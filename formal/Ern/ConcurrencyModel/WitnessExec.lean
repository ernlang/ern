import Ern.ConcurrencyModel.Controller
import Ern.ConcurrencyModel.EventDecide

/-!
# Witness tooling: executions with hand-written graphs (fragment F)

Shared material of the execution witnesses of theorems 12 and 13 (`WitnessHandoff`,
`WitnessLock`): the trace of an `EncapRun` (`trace_of_run`), a correspondence given by lists
(`listK`) with a Boolean check of K1–K4 proved sound (`corresponds_of_check`), with the provenance
of lifecycle roles checked for any correspondence (`roleFromOK`, `roles_of_check`), and a Boolean
form of `FirstCompatible` on a finite range (`firstCompatible_of_check`).
-/

namespace Ern.ConcurrencyModel

open Ern.MemoryModel Ern.MemoryModel.Access Events

variable {pm : ProviderMeta}

/-- An execution with named states is an `EncapsulatedTrace` from its first state to its last
(C51.1). -/
theorem trace_of_run {ks : KShared} {L : MutexLayout} :
    ∀ {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label}, EncapRun pm ks L σ lbls →
      EncapsulatedTrace pm ks L (σ 0) lbls (σ lbls.length)
  | _, [], _ => .nil
  | σ, lbl :: lbls, hr => by
    obtain ⟨he, hs⟩ := hr 0 (by simp)
    have hr' : EncapRun pm ks L (fun k => σ (k + 1)) lbls := fun k hk => by
      have := hr (k + 1) (by simp; omega)
      simpa using this
    have ih := trace_of_run hr'
    exact .cons he hs (by simpa using ih)

/-- An execution with named states from its steps, each read on the label of its list. -/
theorem encapRun_of_steps {ks : KShared} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg}
    {lbls : List Label}
    (h : ∀ i, i < lbls.length → ∀ lbl, lbls[i]? = some lbl →
      EncapStep pm ks L (σ i) lbl (σ (i + 1)) ∧ LStep ks L lbl (σ i) (σ (i + 1))) :
    EncapRun pm ks L σ lbls := fun i hi => h i hi _ (List.getElem?_eq_getElem hi)

/-! ## A correspondence given by lists -/

/-- The value associated with `c` in a list of pairs, the first one. -/
def lookupL {β : Type} (c : Nat) : List (Nat × β) → Option β
  | [] => none
  | (c', b) :: l => if c' = c then some b else lookupL c l

/-- A value found by `lookupL` is in the list. -/
theorem mem_of_lookupL {β : Type} {c : Nat} {b : β} :
    ∀ {l : List (Nat × β)}, lookupL c l = some b → (c, b) ∈ l
  | [], h => by cases h
  | (c', b') :: l, h => by
    unfold lookupL at h
    split at h
    · rename_i e; subst e; cases h; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (mem_of_lookupL h)

/-- The correspondence given by lists (fragment F): the event of step `i` is `evs[i]`, the
`start(c)` and `complete(c)` markers are given by pairs. -/
def listK {n : Nat} (evs : List (Fin n)) (starts completes : List (Nat × Fin n)) :
    StepEvents (Fin n) :=
  ⟨fun i => evs[i]?, fun c => lookupL c starts, fun c => lookupL c completes⟩

/-- The Boolean check of K1–K4 for a list correspondence (C26–C28, C32, C47), given the list
`creates` of the pairs (step, created context). -/
def kcheck {n : Nat} {U V S : Type} (G : ListGraph n Nat U V S) (lbls : List Label)
    (creates : List (Nat × Nat)) (evs : List (Fin n)) (starts completes : List (Nat × Fin n)) :
    Bool :=
  decide evs.Nodup &&
  (List.range lbls.length).all (fun i => match evs[i]?, lbls[i]? with
    | some e, some l => decide ((G.ev e).ctx = l.requester)
    | _, _ => true) &&
  (List.range lbls.length).all (fun i => (List.range lbls.length).all fun j =>
    match evs[i]?, evs[j]?, lbls[i]?, lbls[j]? with
    | some a, some b, some li, some lj =>
        !(decide (i < j) && decide (li.requester = lj.requester)) ||
          decide ((G.ev a).ctx = (G.ev b).ctx ∧ a < b)
    | _, _, _, _ => true) &&
  creates.all (fun p => match evs[p.1]? with
    | some e => decide (G.toGraph.sync? e = some (.spawn p.2))
    | none => true) &&
  starts.all (fun p => decide ((G.ev p.2).ctx = p.1) &&
    decide (G.toGraph.sync? p.2 = some (.start p.1)) &&
    (List.range lbls.length).all fun j => match lbls[j]?, evs[j]? with
      | some l, some d => !(decide (l.requester = p.1)) || decide ((G.ev p.2).ctx = (G.ev d).ctx ∧ p.2 < d)
      | _, _ => true) &&
  completes.all (fun p => decide ((G.ev p.2).ctx = p.1) &&
    decide (G.toGraph.sync? p.2 = some (.complete p.1)) &&
    (List.range lbls.length).all fun j => match lbls[j]?, evs[j]? with
      | some l, some d => !(decide (l.requester = p.1)) || decide ((G.ev d).ctx = (G.ev p.2).ctx ∧ d < p.2)
      | _, _ => true) &&
  (List.range lbls.length).all (fun q => match lbls[q]?, evs[q]? with
    | some (.join _ d), some e => decide (G.toGraph.sync? e = some (.join d))
    | _, _ => true)

/-- The created contexts are listed: every `spawn` or by-value `spawn` step `s` is listed with the
identity of its new context, the length of the context list before it (C4, C5). -/
def createsOK (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) (creates : List (Nat × Nat)) :
    Bool :=
  (List.range lbls.length).all fun s => match lbls[s]? with
    | some (.spawn _ _ _) | some (.spawnVal _ _ _ _) => creates.contains (s, (σ s).1.C.length)
    | _ => true

/-- Step `s` is a `spawn` or a by-value `spawn` that creates `c`, as a Boolean (`Creates`). -/
def createsB (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) (s c : Nat) : Bool :=
  match lbls[s]? with
  | some (.spawn _ _ _) => decide (c = (σ s).1.C.length)
  | some (.spawnVal _ _ _ _) => decide (c = (σ s).1.C.length)
  | _ => false

theorem creates_of_createsB {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} {s c : Nat}
    (h : createsB σ lbls s c = true) : Creates σ lbls s c := by
  unfold createsB at h
  split at h
  · rename_i c' ps ls hs
    obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.1 hs
    exact ⟨hlt, .inl ⟨c', ps, ls, hget⟩, of_decide_eq_true h⟩
  · rename_i c' ps ls vs hs
    obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.1 hs
    exact ⟨hlt, .inr ⟨c', ps, ls, vs, hget⟩, of_decide_eq_true h⟩
  · cases h

/-- Step `t` is `terminate` by `c`, as a Boolean. -/
def termB (lbls : List Label) (t c : Nat) : Bool :=
  match lbls[t]? with
  | some (.terminate c') => decide (c' = c)
  | _ => false

theorem term_of_termB {lbls : List Label} {t c : Nat} (h : termB lbls t c = true) :
    ∃ ht : t < lbls.length, lbls[t] = .terminate c := by
  unfold termB at h
  split at h
  · rename_i c' hs
    obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.1 hs
    have := of_decide_eq_true h
    subst this
    exact ⟨hlt, hget⟩
  · cases h

/-- Step `q` is a `join` of `d`, as a Boolean. -/
def joinB (lbls : List Label) (q d : Nat) : Bool :=
  match lbls[q]? with
  | some (.join _ d') => decide (d' = d)
  | _ => false

theorem join_of_joinB {lbls : List Label} {q d : Nat} (h : joinB lbls q d = true) :
    ∃ hq : q < lbls.length, ∃ c, lbls[q] = .join c d := by
  unfold joinB at h
  split at h
  · rename_i c d' hs
    obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.1 hs
    have := of_decide_eq_true h
    subst this
    exact ⟨hlt, c, hget⟩
  · cases h

/-- The provenance of the lifecycle role of the event `e` (K3 and K4, converse; C28, C32), as a
Boolean: a role `spawn(c)` is carried by the event of a step that creates `c`, a role `start(c)` by
the marker `start(c)` of a created context, a role `complete(c)` by the marker `complete(c)` of a
context that executes `terminate`, a role `join(d)` by the event of a step `join(d)`. -/
def roleFromOK {E : Type} [DecidableEq E] (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label)
    (K : StepEvents E) (e : E) : Option (SyncRole Nat) → Bool
  | some (.spawn c) =>
      (List.range lbls.length).any fun s => createsB σ lbls s c && decide (K.ev s = some e)
  | some (.start c) =>
      decide (K.start c = some e) && (List.range lbls.length).any fun s => createsB σ lbls s c
  | some (.complete c) =>
      decide (K.complete c = some e) && (List.range lbls.length).any fun t => termB lbls t c
  | some (.join d) =>
      (List.range lbls.length).any fun q => joinB lbls q d && decide (K.ev q = some e)
  | _ => true

/-- Soundness of the Boolean check of the provenance of roles: it gives the four provenance fields
of `Corresponds` (K3 and K4, converse), for any correspondence. -/
theorem roles_of_check {E U V S : Type} [DecidableEq E] {G : Events.Graph E Nat U V S}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} {K : StepEvents E}
    (h : ∀ e, roleFromOK σ lbls K e (G.sync? e) = true) :
    (∀ e c, G.sync? e = some (.spawn c) → ∃ s, Creates σ lbls s c ∧ K.ev s = some e) ∧
    (∀ e c, G.sync? e = some (.start c) → K.start c = some e ∧ ∃ s, Creates σ lbls s c) ∧
    (∀ e c, G.sync? e = some (.complete c) →
      K.complete c = some e ∧ ∃ t, ∃ h : t < lbls.length, lbls[t] = .terminate c) ∧
    (∀ e d, G.sync? e = some (.join d) →
      ∃ q, ∃ h : q < lbls.length, ∃ c, lbls[q] = .join c d ∧ K.ev q = some e) := by
  refine ⟨fun e c hs => ?_, fun e c hs => ?_, fun e c hs => ?_, fun e d hs => ?_⟩
  · have := h e
    rw [hs] at this
    simp only [roleFromOK, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
    obtain ⟨s, -, hc, he⟩ := this
    exact ⟨s, creates_of_createsB hc, he⟩
  · have := h e
    rw [hs] at this
    simp only [roleFromOK, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
    obtain ⟨hk, s, -, hc⟩ := this
    exact ⟨hk, s, creates_of_createsB hc⟩
  · have := h e
    rw [hs] at this
    simp only [roleFromOK, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
    obtain ⟨hk, t, -, ht⟩ := this
    exact ⟨hk, t, term_of_termB ht⟩
  · have := h e
    rw [hs] at this
    simp only [roleFromOK, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
    obtain ⟨q, -, hj, he⟩ := this
    obtain ⟨hq, c, hl⟩ := join_of_joinB hj
    exact ⟨q, hq, c, hl, he⟩

/-- In a list without duplicates, an element has one index. -/
theorem nodup_getElem?_inj {α : Type} : ∀ {l : List α}, l.Nodup → ∀ {i j : Nat} {a : α},
    l[i]? = some a → l[j]? = some a → i = j
  | [], _, _, _, _, h, _ => by cases h
  | x :: l, hnd, i, j, a, hi, hj => by
    have hx : x ∉ l := (List.nodup_cons.1 hnd).1
    have hl : l.Nodup := (List.nodup_cons.1 hnd).2
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j =>
        simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at hi hj
        subst hi; exact absurd (List.mem_of_getElem? hj) hx
    | succ i =>
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at hi hj
        subst hj; exact absurd (List.mem_of_getElem? hi) hx
      | succ j =>
        simp only [List.getElem?_cons_succ] at hi hj
        exact congrArg (· + 1) (nodup_getElem?_inj hl hi hj)

/-- Soundness of the Boolean checks: a list correspondence that passes them is a correspondence of
fragment F (K1–K4, with the provenance of roles, `roleFromOK`). -/
theorem corresponds_of_check {n : Nat} {U V S : Type} (G : ListGraph n Nat U V S)
    (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) (creates : List (Nat × Nat))
    (evs : List (Fin n)) (starts completes : List (Nat × Fin n))
    (h : kcheck G lbls creates evs starts completes = true)
    (hc : createsOK σ lbls creates = true)
    (hr : ∀ e, roleFromOK σ lbls (listK evs starts completes) e (G.toGraph.sync? e) = true) :
    Corresponds G.toGraph σ lbls (listK evs starts completes) := by
  obtain ⟨hr1, hr2, hr3, hr4⟩ := roles_of_check hr
  simp only [kcheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hnd, hctx⟩, hpo⟩, hsp⟩, hst⟩, hco⟩, hjo⟩ := h
  refine ⟨fun i hi e he => ?_, fun i j e hi hj => ?_, fun i j hi hj a b hij hreq ha hb => ?_,
    fun s c hcr e he => ?_, fun c x hx => ?_, fun c x hx => ?_, fun q hq c d e hlq he => ?_,
    hr1, hr2, hr3, hr4⟩
  · have := hctx i (List.mem_range.2 hi)
    simp only [listK] at he
    rw [he, List.getElem?_eq_getElem hi] at this
    exact of_decide_eq_true this
  · simp only [listK] at hi hj
    have hi' := (List.getElem?_eq_some_iff.1 hi)
    have hj' := (List.getElem?_eq_some_iff.1 hj)
    exact nodup_getElem?_inj hnd hi hj
  · have := hpo i (List.mem_range.2 hi) j (List.mem_range.2 hj)
    simp only [listK] at ha hb
    rw [ha, hb, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj] at this
    simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
      decide_eq_false_iff_not, decide_eq_true_eq] at this
    rcases this with (h | h) | h
    · exact absurd hij h
    · exact absurd hreq h
    · exact h
  · obtain ⟨hs, hkind, hcl⟩ := hcr
    have hmem : (s, c) ∈ creates := by
      simp only [createsOK, List.all_eq_true] at hc
      have := hc s (List.mem_range.2 hs)
      rw [List.getElem?_eq_getElem hs] at this
      rcases hkind with ⟨_, _, _, e'⟩ | ⟨_, _, _, _, e'⟩ <;> rw [e'] at this <;>
        · rw [hcl]; exact List.contains_iff_mem.1 this
    have := hsp (s, c) hmem
    simp only [listK] at he
    simp only [he] at this
    exact of_decide_eq_true this
  · have hm := mem_of_lookupL hx
    have := hst (c, x) hm
    obtain ⟨⟨h1, h2⟩, h3⟩ := this
    refine ⟨h1, h2, fun j hj d hjc hd => ?_⟩
    have := h3 j (List.mem_range.2 hj)
    simp only [listK] at hd
    rw [List.getElem?_eq_getElem hj, hd] at this
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
      decide_eq_true_eq] at this
    rcases this with h | h
    · exact absurd hjc h
    · exact h
  · have hm := mem_of_lookupL hx
    have := hco (c, x) hm
    obtain ⟨⟨h1, h2⟩, h3⟩ := this
    refine ⟨h1, h2, fun j hj d hjc hd => ?_⟩
    have := h3 j (List.mem_range.2 hj)
    simp only [listK] at hd
    rw [List.getElem?_eq_getElem hj, hd] at this
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
      decide_eq_true_eq] at this
    rcases this with h | h
    · exact absurd hjc h
    · exact h
  · have := hjo q (List.mem_range.2 hq)
    simp only [listK] at he
    rw [List.getElem?_eq_getElem hq, hlq, he] at this
    exact of_decide_eq_true this

/-! ## `FirstCompatible` on a finite range -/

/-- `FirstCompatible` (12d) from a check of its three parts on the states `i` to `r + 1`. -/
theorem firstCompatible_of_check {Inc : Option Mode → Mode → Prop} [∀ v m, Decidable (Inc v m)]
    {σ : Nat → SC × SyncReg × ArenaReg} {i c' l : Nat} {m : Mode} {r : Nat} (hir : i ≤ r)
    (hlast : ¬ Inc (cap (σ (r + 1)).1 (σ (r + 1)).2.1 c' l) m)
    (hrange : (List.range (r + 1 - i)).all
      (fun k => decide (Inc (cap (σ (i + k)).1 (σ (i + k)).2.1 c' l) m)) = true) :
    FirstCompatible Inc σ i c' l m r := by
  refine ⟨hir, hlast, fun k hk1 hk2 => ?_⟩
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hrange
  have := hrange (k - i) (by omega)
  rwa [Nat.add_sub_cancel' hk1] at this

/-! ## Bounded quantifiers -/

/-- A property of every index from `a` to `b`, from a check on that range. -/
theorem forall_between {P : Nat → Prop} [DecidablePred P] {a b : Nat}
    (h : (List.range (b + 1 - a)).all (fun k => decide (P (a + k))) = true) :
    ∀ k, a ≤ k → k ≤ b → P k := by
  intro k hk1 hk2
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  have := h (k - a) (by omega)
  rwa [Nat.add_sub_cancel' hk1] at this

/-! ## Realization R of a list correspondence -/

/-- The Boolean check of realization R for a list correspondence (C13, C27, C31, C48): the event
of each controller step has the access `ctlAcc` and the `sync` attribute `ctlSync`; `mo` is the
trace order between them; every modification of `x` is one of them. -/
def rcheck {n : Nat} {S : Type} (G : ListGraph n Nat Nat Nat S) (L : MutexLayout)
    (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) (evs : List (Fin n)) (i x : Nat)
    (R : CtlOrders) (v₀ v₁ : Nat) : Bool :=
  decide (v₀ ≠ v₁) &&
  (List.range lbls.length).all (fun k => match lbls[k]? with
    | some lbl => !(decide (CtlStep L σ lbls i x k)) || (match evs[k]? with
      | some e => decide (G.toGraph.acc? e = some (ctlAcc x R v₀ v₁ lbl)) &&
          decide (G.toGraph.sync? e = ctlSync lbl)
      | none => false)
    | none => true) &&
  (List.range lbls.length).all (fun k => (List.range lbls.length).all fun k' =>
    match evs[k]?, evs[k']? with
    | some e, some e' => !(decide (CtlStep L σ lbls i x k) && decide (CtlStep L σ lbls i x k')) ||
        decide (G.toGraph.mo e e' ↔ k < k')
    | _, _ => true) &&
  (List.finRange n).all (fun w => !(decide (G.toGraph.ModOn w x)) ||
    (List.range lbls.length).any fun k => decide (CtlStep L σ lbls i x k) && evs[k]? == some w)

/-- Soundness of the check of realization R. -/
theorem realizes_of_check {n : Nat} {S : Type} (G : ListGraph n Nat Nat Nat S) (L : MutexLayout)
    (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) (evs : List (Fin n))
    (starts completes : List (Nat × Fin n)) (i x : Nat) (R : CtlOrders) (v₀ v₁ : Nat)
    (h : rcheck G L σ lbls evs i x R v₀ v₁ = true) :
    Realizes G.toGraph L σ lbls (listK evs starts completes) i x R v₀ v₁ := by
  simp only [rcheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hv, hev⟩, hmo⟩, honly⟩ := h
  have hlt : ∀ k, CtlStep L σ lbls i x k → k < lbls.length := fun k hk => by
    unfold CtlStep at hk; split at hk
    all_goals first
      | (rename_i h; exact (List.getElem?_eq_some_iff.1 h).1)
      | exact hk.elim
  refine ⟨hv, fun k lbl hl hk => ?_, fun k k' e e' hk hk' he he' => ?_, fun w hw => ?_⟩
  · have := hev k (List.mem_range.2 (hlt k hk))
    rw [hl] at this
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at this
    rcases this with h | h
    · exact absurd hk h
    · revert h
      simp only [listK]
      cases evs[k]? with
      | none => simp
      | some e =>
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact fun ⟨h1, h2⟩ => ⟨e, rfl, h1, h2⟩
  · have := hmo k (List.mem_range.2 (hlt k hk)) k' (List.mem_range.2 (hlt k' hk'))
    simp only [listK] at he he'
    rw [he, he'] at this
    simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
      decide_eq_false_iff_not, decide_eq_true_eq] at this
    rcases this with (h | h) | h
    · exact absurd hk h
    · exact absurd hk' h
    · exact h
  · have := honly w (List.mem_finRange w)
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, List.any_eq_true,
      Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    rcases this with h | ⟨k, -, hk, he⟩
    · exact absurd hw h
    · exact ⟨k, hk, he⟩

end Ern.ConcurrencyModel
