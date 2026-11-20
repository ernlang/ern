import Ern.ConcurrencyModel.Controller
import Ern.ConcurrencyModel.EventDecide

/-!
# Witness tooling: executions with hand-written graphs (fragment F)

Shared material of the execution witnesses of theorems 12 and 13 (`WitnessHandoff`,
`WitnessLock`): the trace of an `EncapRun` (`trace_of_run`), a correspondence given by lists
(`listK`) with a Boolean check of K1–K4 proved sound (`corresponds_of_check`), and a Boolean form
of `FirstCompatible` on a finite range (`firstCompatible_of_check`).
-/

namespace Ern.ConcurrencyModel

open Ern.MemoryModel Ern.MemoryModel.Access Events

/-- An execution with named states is an `EncapsulatedTrace` from its first state to its last
(C51.1). -/
theorem trace_of_run {ks : KShared} {L : MutexLayout} :
    ∀ {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label}, EncapRun ks L σ lbls →
      EncapsulatedTrace ks L (σ 0) lbls (σ lbls.length)
  | _, [], _ => .nil
  | σ, lbl :: lbls, hr => by
    obtain ⟨he, hs⟩ := hr 0 (by simp)
    have hr' : EncapRun ks L (fun k => σ (k + 1)) lbls := fun k hk => by
      have := hr (k + 1) (by simp; omega)
      simpa using this
    have ih := trace_of_run hr'
    exact .cons he hs (by simpa using ih)

/-- An execution with named states from its steps, each read on the label of its list. -/
theorem encapRun_of_steps {ks : KShared} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg}
    {lbls : List Label}
    (h : ∀ i, i < lbls.length → ∀ lbl, lbls[i]? = some lbl →
      EncapStep ks L (σ i) lbl (σ (i + 1)) ∧ LStep ks L lbl (σ i) (σ (i + 1))) :
    EncapRun ks L σ lbls := fun i hi => h i hi _ (List.getElem?_eq_getElem hi)

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

/-- Soundness of the Boolean check: a list correspondence that passes it is a correspondence of
fragment F (K1–K4). -/
theorem corresponds_of_check {n : Nat} {U V S : Type} (G : ListGraph n Nat U V S)
    (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) (creates : List (Nat × Nat))
    (evs : List (Fin n)) (starts completes : List (Nat × Fin n))
    (h : kcheck G lbls creates evs starts completes = true)
    (hc : createsOK σ lbls creates = true) :
    Corresponds G.toGraph σ lbls (listK evs starts completes) := by
  simp only [kcheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hnd, hctx⟩, hpo⟩, hsp⟩, hst⟩, hco⟩, hjo⟩ := h
  refine ⟨fun i hi e he => ?_, fun i j e hi hj => ?_, fun i j hi hj a b hij hreq ha hb => ?_,
    fun s c hcr e he => ?_, fun c x hx => ?_, fun c x hx => ?_, fun q hq c d e hlq he => ?_⟩
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

end Ern.ConcurrencyModel
