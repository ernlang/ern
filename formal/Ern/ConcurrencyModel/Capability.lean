import Ern.ConcurrencyModel.Classification
import Ern.ConcurrencyModel.Encapsulation
import Ern.ConcurrencyModel.Outcomes

/-!
# Theorem 12: context capability, its soundness and L2 (C43–C45)

Theorem 12 of `formal/DESIGN.md`, Milestone 4, target theorems, on the authority machine; no event
is involved.

* `cap(s, c, l)` (C43): the greatest effective mode on `l` attributable to `c` through an active
  authority held by a frame of the stack of `c`, or held in a place through a valid holder chain
  that passes through the `guarded` authority of no live entry (`CapAttr`, `cap`). It is defined
  on the pattern of the guard-free exercise of C22.6 (`ExerFree`), with "the current frame"
  replaced by "a frame of the stack of `c`"; it is not `ExercisableAt`.
* The incompatibility of a capability value with a mode used by another context (C43): the
  `Modify` criterion (`IncompatModify`) and the `Confined` criterion (`IncompatConfined`).
* 12a: `cap` covers every access of a step (11e) in the state before the step (`cap_covers`).
* 12b: L2, state form (C45; `OB-C18`): no reached state gives two distinct contexts incompatible
  capabilities on a leaf under the `Modify` criterion (`cap_l2`).

Formalization hypothesis (reading 8 of C43): the live frames of a context are the frames of its
stack; a "suspended" frame is a frame of the stack other than the current one; `cap` covers every
frame of the stack.

Fragment of the trace statements: `DDSound` (Spec 1 §80), well-formed statics (Spec 1 §47), an
`EncapsulatedTrace` (C51.1) from the initial state of Spec 1 §47.
-/

namespace Ern.ConcurrencyModel

open Ern.MemoryModel Ern.MemoryModel.Access

variable {pm : ProviderMeta}

/-! ## The capability of a context (C43) -/

/-- `x` is attributable to context `c` in mode `m` in `s`, under the registry `reg` (C43): `x` is
active, its own mode permits `m`, it is not the `guarded` authority of a live entry, and it is
held by a frame of the stack of `c` (reading 8), or by a place `p` such that an authority itself
attributable to `c` in mode `m` has an effective mode permitting `m` on every leaf of `p` (a valid
holder chain, Spec 1 §43). The constructors are those of `ExerFree` (C22.6) with a frame of the
stack of `c` in place of its current frame. -/
inductive CapAttr (s : SC) (reg : SyncReg) (c : Nat) : Nat → Mode → Prop where
  | base {a : Nat} {m : Mode} {y : Authority} {f : Nat} : NotGuarded s reg a → s.A[a]? = some y →
      y.active = true → m.le y.mode → y.holder = .frame f → f ∈ s.stk c → CapAttr s reg c a m
  | held {a p b : Nat} {m : Mode} {y : Authority} : NotGuarded s reg a → s.A[a]? = some y →
      y.active = true → m.le y.mode → y.holder = .place p → CapAttr s reg c b m →
      (∀ l ∈ footprint s.P p, Allows (effective s.flat b l) m) → CapAttr s reg c a m

/-- One step of `CapAttr · m` read on a Boolean premise (decision procedure for C43, on the
pattern of `exerFreeR`). -/
def capAttrR (s : SC) (reg : SyncReg) (c : Nat) (m : Mode) (E : Nat → Bool) (a : Nat) : Bool :=
  decide (NotGuarded s reg a) && match s.A[a]? with
  | some y => y.active && decide (m.le y.mode) && match y.holder with
    | .frame f => decide (f ∈ s.stk c)
    | .place p => (List.range s.A.length).any fun b =>
        decide (∀ l ∈ footprint s.P p, Allows (effective s.flat b l) m) && E b
  | none => false

/-- `capAttrR` is a bounded monotone rule (decision procedure for C43). -/
theorem capAttrR_rule (s : SC) (reg : SyncReg) (c : Nat) (m : Mode) :
    KRule s.A.length (capAttrR s reg c m) where
  mono p q hpq a h := by
    unfold capAttrR at h ⊢
    simp only [Bool.and_eq_true] at h ⊢
    refine ⟨h.1, ?_⟩
    have h2 := h.2
    split at h2
    · simp only [Bool.and_eq_true] at h2 ⊢
      refine ⟨h2.1, ?_⟩; split at h2
      · simpa using h2.2
      · simp only [Bool.and_eq_true, List.any_eq_true] at h2 ⊢
        obtain ⟨b, hb, hc, he⟩ := h2.2
        exact ⟨b, hb, hc, hpq b he⟩
    · exact h2
  bound p a h := by
    unfold capAttrR at h
    simp only [Bool.and_eq_true] at h
    have h2 := h.2
    split at h2
    · exact lt_of_getElem? ‹_›
    · cases h2
  loc p q hpq a := by
    unfold capAttrR; congr 1; split
    · congr 1; split
      · rfl
      · exact any_congr' fun b hb => by rw [hpq b (List.mem_range.1 hb)]
    · rfl

/-- Soundness of the iteration (decision procedure for C43). -/
theorem capAttr_of_kiter (s : SC) (reg : SyncReg) (c : Nat) (m : Mode) :
    ∀ k a, kiter (capAttrR s reg c m) k a = true → CapAttr s reg c a m
  | 0, _, h => by simp [kiter] at h
  | k + 1, a, h => by
    simp only [kiter, capAttrR, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hg, h⟩ := h
    split at h
    · rename_i y hy
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨ha, hm⟩, h⟩ := h
      split at h
      · rename_i f hf; exact .base hg hy ha hm hf (by simpa using h)
      · rename_i p hp
        simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨b, -, hc, hb⟩ := h
        exact .held hg hy ha hm hp (capAttr_of_kiter s reg c m k b hb) hc
    · cases h

/-- The frame-held case of `capAttrR`. -/
theorem capAttrR_base {s : SC} {reg : SyncReg} {c : Nat} {m : Mode} {E : Nat → Bool} {a f : Nat}
    {y : Authority} (hg : NotGuarded s reg a) (hy : s.A[a]? = some y) (ha : y.active = true)
    (hm : m.le y.mode) (hf : y.holder = .frame f) (hin : f ∈ s.stk c) :
    capAttrR s reg c m E a = true := by
  simp only [capAttrR, hy, ha, hf, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hg, hm, hin⟩

/-- The place-held case of `capAttrR`. -/
theorem capAttrR_held {s : SC} {reg : SyncReg} {c : Nat} {m : Mode} {E : Nat → Bool} {a p b : Nat}
    {y : Authority} (hg : NotGuarded s reg a) (hy : s.A[a]? = some y) (ha : y.active = true)
    (hm : m.le y.mode) (hp : y.holder = .place p) (hb : b < s.A.length)
    (hc : ∀ l ∈ footprint s.P p, Allows (effective s.flat b l) m) (hE : E b = true) :
    capAttrR s reg c m E a = true := by
  simp only [capAttrR, hy, ha, hp, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq,
    List.any_eq_true, List.mem_range]
  exact ⟨hg, hm, b, hb, hc, hE⟩

/-- `CapAttr` is computed by `|A| + 1` steps of `capAttrR` (decision procedure for C43). -/
theorem capAttr_iff {s : SC} {reg : SyncReg} {c a : Nat} {m : Mode} :
    CapAttr s reg c a m ↔ kiter (capAttrR s reg c m) (s.A.length + 1) a = true := by
  refine ⟨fun h => ?_, capAttr_of_kiter s reg c m _ a⟩
  induction h with
  | base hg hy ha hm hf hin => exact capAttrR_base hg hy ha hm hf hin
  | held hg hy ha hm hp _ hc ih =>
    rw [← kiter_fix (capAttrR_rule s reg c _)]
    exact capAttrR_held hg hy ha hm hp (kiter_bound (capAttrR_rule s reg c _) _ _ ih) hc ih

/-- Decidability of `CapAttr` (C43). -/
instance (s : SC) (reg : SyncReg) (c a : Nat) (m : Mode) : Decidable (CapAttr s reg c a m) :=
  decidable_of_iff _ capAttr_iff.symm

/-- Some authority attributable to `c` in mode `m` has an effective mode permitting `m` on the
leaf `l` (C43). -/
def CapAt (s : SC) (reg : SyncReg) (c l : Nat) (m : Mode) : Prop :=
  ∃ x ∈ List.range s.A.length, CapAttr s reg c x m ∧ Allows (effective s.flat x l) m

/-- Decidability of `CapAt` (C43). -/
instance (s : SC) (reg : SyncReg) (c l : Nat) (m : Mode) : Decidable (CapAt s reg c l m) := by
  unfold CapAt; infer_instance

/-- `cap(s, c, l) ∈ {none, Observe, Modify}` (C43; reading 8): the greatest mode `m` such that an
authority attributable to `c` in mode `m` has an effective mode permitting `m` on `l`; `none` if
there is none. -/
def cap (s : SC) (reg : SyncReg) (c l : Nat) : Option Mode :=
  if CapAt s reg c l .modify then some .modify else if CapAt s reg c l .observe then some .observe
  else none

/-- The order of capability values (C43): `none < Observe < Modify`. -/
def capRank : Option Mode → Nat
  | none => 0
  | some .observe => 1
  | some .modify => 2

/-- C43, `Modify` criterion: a present capability value `v` of one context is incompatible with the
mode `m` used by another context on the same leaf when one of the two is `Modify` ("present `cap`
values on a leaf are incompatible when at least one is `Modify`"). -/
def IncompatModify (v : Option Mode) (m : Mode) : Prop :=
  match v with
  | none => False
  | some v => v = .modify ∨ m = .modify

/-- C43, `Confined` criterion: any present capability value of one context is incompatible with
any mode used by another context ("for `Confined`, any two present capabilities are
incompatible"). -/
def IncompatConfined (v : Option Mode) (_m : Mode) : Prop := v ≠ none

instance (v : Option Mode) (m : Mode) : Decidable (IncompatModify v m) := by
  unfold IncompatModify; split <;> infer_instance

instance (v : Option Mode) (m : Mode) : Decidable (IncompatConfined v m) := by
  unfold IncompatConfined; infer_instance

/-! ## Elementary facts -/

/-- An attributable authority with a sufficient effective mode bounds `cap` from below (C43). -/
theorem cap_of {s : SC} {reg : SyncReg} {c l x : Nat} {m : Mode} (hx : CapAttr s reg c x m)
    (he : Allows (effective s.flat x l) m) : Allows (cap s reg c l) m := by
  have hb : x ∈ List.range s.A.length := by
    cases hx with
    | base _ hy => exact List.mem_range.2 (lt_of_getElem? hy)
    | held _ hy => exact List.mem_range.2 (lt_of_getElem? hy)
  cases m with
  | modify =>
    have h1 : CapAt s reg c l .modify := ⟨x, hb, hx, he⟩
    simp only [cap, h1, ↓reduceIte]; exact Or.inr rfl
  | observe =>
    by_cases h : CapAt s reg c l .modify
    · simp only [cap, h, ↓reduceIte]; exact Or.inl rfl
    · have h2 : CapAt s reg c l .observe := ⟨x, hb, hx, he⟩
      simp only [cap, h, h2, ↓reduceIte]; exact Or.inl rfl

/-- `cap` at `Modify` rests on an authority attributable in `Modify` with effective `Modify`. -/
theorem cap_modify {s : SC} {reg : SyncReg} {c l : Nat} (h : cap s reg c l = some .modify) :
    CapAt s reg c l .modify := by
  unfold cap at h
  split at h
  · assumption
  · split at h <;> simp at h

/-- A present `cap` rests on an attributable authority with a sufficient effective mode. -/
theorem cap_present {s : SC} {reg : SyncReg} {c l : Nat} (h : cap s reg c l ≠ none) :
    ∃ m, CapAt s reg c l m := by
  unfold cap at h
  split at h
  · exact ⟨_, ‹_›⟩
  · split at h
    · exact ⟨_, ‹_›⟩
    · exact absurd rfl h

/-- `Allows e Modify` is `e = some Modify` (Spec 1 §43). -/
theorem allows_modify {e : Option Mode} (h : Allows e .modify) : e = some .modify := by
  cases e with
  | none => exact h.elim
  | some e =>
    rcases h with h | h
    · cases h
    · rw [h]

/-- A mode allowed is present (Spec 1 §43). -/
theorem allows_present {e : Option Mode} {m : Mode} (h : Allows e m) : e ≠ none := by
  cases e with
  | none => exact h.elim
  | some _ => exact Option.some_ne_none _

/-- A present effective mode permits `Observe` (Spec 1 §43). -/
theorem allows_observe {e : Option Mode} (h : e ≠ none) : Allows e .observe := by
  cases e with
  | none => exact absurd rfl h
  | some e => exact Or.inl rfl

/-- An attributable authority is not the `guarded` authority of a live entry (C43). -/
theorem CapAttr.notGuarded {s : SC} {reg : SyncReg} {c u : Nat} {m : Mode}
    (h : CapAttr s reg c u m) : NotGuarded s reg u := by
  cases h with
  | base hg => exact hg
  | held hg => exact hg

/-- What the current frame of `c` exercises without passing through a live `guarded` authority
(C22.6) is attributable to `c` (C43; reading 8: the current frame is a frame of the stack), under
the frame structure of C3 (a live context has a nonempty stack, whose top is its current
frame). -/
theorem capAttr_of_exerFree {s : SC} {reg : SyncReg} {c a : Nat} {m : Mode} (hF : FramesC s)
    (h : ExerFree s reg c a m) : CapAttr s reg c a m := by
  by_cases hl : s.Live c
  · obtain ⟨f, r, hfr⟩ := List.exists_cons_of_ne_nil (hF.nonempty c hl)
    have htop : (s.view c).top ∈ s.stk c := by
      rw [SC.view_top hfr, hfr]; exact List.mem_cons_self ..
    induction h with
    | base hg hy ha hm hf => exact .base hg hy ha hm hf htop
    | held hg hy ha hm hp _ hc ih => exact .held hg hy ha hm hp ih hc
  · exfalso
    induction h with
    | base _ hy _ _ hf =>
      rw [SC.view_top_dead hl] at hf; exact SC.noFrame_holder hy hf
    | held _ _ _ _ _ _ _ ih => exact ih

/-! ## L2 on one state (C43, C45) -/

/-- L2 on attributions (C43, C45): under the frame uniqueness of C3, `I1` (Spec 1 §50) and `WF3`
(Spec 1 §49), an authority attributable to `c` in mode `Modify` with effective `Modify` on a leaf
does not coexist with an authority attributable to another context `c'` with an effective mode
permitting its mode on the same leaf: along the holder chain, each holding place has a leaf on
which the authority attributable in `Modify` has effective `Modify`, so the authority of the other
chain is the same (§50), down to a frame of both stacks. -/
theorem capAttr_compat {s : SC} {reg : SyncReg} (hnd : s.frames.Nodup) (hI : I1 s.flat)
    (hw : WF3 s.flat) {c c' : Nat} (hcc : c ≠ c') {x : Nat} {m₀ : Mode}
    (hx : CapAttr s reg c x m₀) (hm₀ : m₀ = .modify) :
    ∀ y l m, effective s.flat x l = some .modify → CapAttr s reg c' y m →
      Allows (effective s.flat y l) m → False := by
  induction hx with
  | @base a m y f _ hy ha hm hf hin =>
    intro y' l m' hel hy' hal
    by_cases hxy : a = y'
    · subst hxy
      cases hy' with
      | base _ hy2 _ _ hf2 hin2 =>
        rw [hy] at hy2; cases hy2; rw [hf] at hf2; cases hf2
        exact hcc (ReparentAux.stk_unique hnd hin hin2)
      | held _ hy2 _ _ hp2 =>
        rw [hy] at hy2; cases hy2; rw [hf] at hp2; cases hp2
    · exact allows_present hal (effective_exclusive hI hxy hel)
  | @held a p b m y _ hy ha hm hp hb hc ih =>
    intro y' l m' hel hy' hal
    by_cases hxy : a = y'
    · subst hxy
      cases hy' with
      | base _ hy2 _ _ hf2 =>
        rw [hy] at hy2; cases hy2; rw [hp] at hf2; cases hf2
      | held _ hy2 _ _ hp2 hb2 hc2 =>
        rw [hy] at hy2; cases hy2; rw [hp] at hp2; cases hp2
        have hu : s.flat.Usable p := by
          have := hw.holders a _ hy ha; rw [hp] at this; exact this
        obtain ⟨l', hl'⟩ := exists_mem_footprint hw (s.flat.P.length - p + 1) p (by omega) hu.lt
        exact ih hm₀ _ l' _ (allows_modify (hm₀ ▸ hc l' hl')) hb2 (hc2 l' hl')
    · exact allows_present hal (effective_exclusive hI hxy hel)

/-- L2 on one state (C43, C45): under the frame uniqueness of C3, `I1` and `WF3`, for `c ≠ c'`,
never `cap c l = Modify` with `cap c' l` present. -/
theorem cap_compat_state {s : SC} {reg : SyncReg} (hnd : s.frames.Nodup) (hI : I1 s.flat)
    (hw : WF3 s.flat) {c c' l : Nat} (hcc : c ≠ c') (hm : cap s reg c l = some .modify) :
    cap s reg c' l = none := by
  cases hc' : cap s reg c' l with
  | none => rfl
  | some m' =>
    exfalso
    obtain ⟨x, -, hx, hex⟩ := cap_modify hm
    obtain ⟨m, y, -, hy, hey⟩ := cap_present (by rw [hc']; exact Option.some_ne_none _)
    exact capAttr_compat hnd hI hw hcc hx rfl y l m (allows_modify hex) hy hey

/-- The invariants of theorem 2 hold at every state reached by an `EncapsulatedTrace` from the
initial state of Spec 1 §47, under `DDSound` (Spec 1 §80) and well-formed statics (§47). -/
theorem encapsulated_inv {ks : KShared} {L : MutexLayout} {statics : Statics} {lbls : List Label}
    {st : SC × SyncReg × ArenaReg} (hdd : DDSound ks.toK) (hst : StaticsOK statics)
    (h : EncapsulatedTrace pm ks L (SC.ofS3 (S3.init statics), [], []) lbls st) :
    KInvCA st.1 ∧ LibInv L st := by
  obtain ⟨hk, hs⟩ := init_inv hdd hst L
  exact trace_inv hdd h.restricted hk hs

/-- **Theorem 12b**, L2, state form (C45: "On an `EncapsulatedTrace`, no state gives two distinct
contexts incompatible `cap` values on the same leaf under the `Modify` criterion of C43";
`OB-C18`): at every state reached by an `EncapsulatedTrace` from the initial state of Spec 1 §47,
under `DDSound` and well-formed statics, a present capability of `c` on `l` is not incompatible,
under the `Modify` criterion, with that of another context `c'`. -/
theorem cap_l2 {ks : KShared} {L : MutexLayout} {statics : Statics} {lbls : List Label}
    {st : SC × SyncReg × ArenaReg} (hdd : DDSound ks.toK) (hst : StaticsOK statics)
    (h : EncapsulatedTrace pm ks L (SC.ofS3 (S3.init statics), [], []) lbls st) {c c' l : Nat}
    {m : Mode} (hcc : c ≠ c') (hm : cap st.1 st.2.1 c l = some m) :
    ¬ IncompatModify (cap st.1 st.2.1 c' l) m := by
  obtain ⟨hk, -⟩ := encapsulated_inv hdd hst h
  have hF : FramesC st.1 := hk.1.1.1
  have hw : WF3 st.1.flat := hk.1.1.2
  have hI : I1 st.1.flat := hk.1.2.1.1.1
  intro hinc
  cases hc' : cap st.1 st.2.1 c' l with
  | none => rw [hc'] at hinc; exact hinc
  | some m' =>
    rw [hc'] at hinc
    rcases hinc with h' | h'
    · subst h'
      have := cap_compat_state hF.nodup hI hw (Ne.symm hcc) hc'
      rw [hm] at this; cases this
    · subst h'
      have := cap_compat_state hF.nodup hI hw hcc hm
      rw [hc'] at this; cases this

/-! ## 12a: `cap` covers the accesses of a step (C43) -/

/-- The required mode of an access is covered by `cap` when an authority attributable in that
mode has a sufficient effective mode on the leaf (C43). -/
theorem cap_covers_of {s : SC} {reg : SyncReg} {c a l : Nat} {m : Mode} (hF : FramesC s)
    (hx : ExerFree s reg c a m) (he : Allows (effective s.flat a l) m) :
    Allows (cap s reg c l) m :=
  cap_of (capAttr_of_exerFree hF hx) he

/-- The accesses of `sharedWrites` are on the leaves of the region, in mode `Observe`. -/
theorem mem_sharedWrites {ks : KShared} {region : List Nat} {ord : Option MemOrder}
    {kind : WriteKind} {x : LeafAccess} (hx : x ∈ sharedWrites ks region ord kind) :
    x.leaf ∈ region ∧ x.mode = .observe := by
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
  by_cases ha : AtomicLeaf ks l <;> simp [ha, hl]

/-- The accesses of `ctlAccess` are on the controller of the entry, in mode `Observe`. -/
theorem mem_ctlAccess {L : MutexLayout} {st : SC × SyncReg × ArenaReg} {i : Nat}
    {k : Events.Kind} {o : MemOrder} {x : LeafAccess} (hx : x ∈ ctlAccess L st i k o) :
    ∃ e, st.2.1[i]? = some e ∧ ControlOf L st.1 e = some x.leaf ∧ x.mode = .observe := by
  unfold ctlAccess at hx
  obtain ⟨ctl, hc, rfl⟩ := List.mem_map.1 hx
  cases he : st.2.1[i]? with
  | none => rw [he] at hc; cases hc
  | some e =>
    rw [he] at hc
    exact ⟨e, rfl, by simpa using hc, rfl⟩

/-- The controller right of C14.3, C17.4 and C18.4 without a live `guarded` authority (C22.6)
covers the controller in `Observe` (C43). -/
theorem cap_covers_ctl {L : MutexLayout} {s : SC} {reg : SyncReg} {e : SyncEntry} {c ctl : Nat}
    (hF : FramesC s) (h : CtrlRightFree L (s, reg) e c) (hctl : ControlOf L s e = some ctl) :
    Allows (cap s reg c ctl) .observe := by
  unfold CtrlRightFree at h
  rw [hctl] at h
  obtain ⟨a, -, hx, he⟩ := h
  exact cap_covers_of hF hx (allows_observe he)

/-- **Theorem 12a** (C43; C22.6): for a step of an `EncapsulatedTrace` (C51.1) from a state
satisfying the frame structure of C3, each access of the step (11e, `classify`) is covered by the
capability of the executing context on its leaf, in the state before the step: `cap` permits the
mode the access requires. The rights the step reads without a live `guarded` authority
(`RightsReadFree`, C22.6) are attributable (`capAttr_of_exerFree`), and the step's own
preconditions give their effective modes (Spec 1 §66.2, §67.1, §68.2; C37.2; C13.11; C14.3, C17.4,
C18.4). -/
theorem cap_covers {ks : KShared} {L : MutexLayout} {R : CtlOrders} {lbl : Label}
    {st st' : SC × SyncReg × ArenaReg} {acc : List LeafAccess} (hF : FramesC st.1)
    (he : EncapStep pm ks L st lbl st') (h : LStep ks L lbl st st')
    (hc : classify ks L R st lbl = some acc) :
    ∀ x ∈ acc, Allows (cap st.1 st.2.1 lbl.requester x.leaf) x.mode := by
  obtain ⟨-, -, hr⟩ := he
  intro x hx
  cases h with
  | @kernel s s' reg ar c op hop =>
    cases op with
    | read a ls =>
      simp only [classify, Option.some.injEq] at hc; subst hc
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
      obtain ⟨o, hR, ho⟩ := hop
      have hR' : Guarded (Read3Pre (s.view c) a ls) (s.view c) o := hR
      cases hR' with
      | ok hp => exact cap_covers_of hF hr (allows_observe (hp.effectivePresent l hl))
      | reject => cases ho
    | write a ls =>
      simp only [classify, Option.some.injEq] at hc; subst hc
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
      obtain ⟨o, hR, ho⟩ := hop
      have hR' : Guarded (Write3Pre (s.view c) a ls) (write3Eff (s.view c) ls) o := hR
      cases hR' with
      | ok hp =>
        refine cap_covers_of hF hr ?_
        show Allows (effective (s.view c) a l) .modify
        rw [hp.effectiveModify l hl]; exact Or.inr rfl
      | reject => cases ho
    | writeShared a ls =>
      simp only [classify] at hc
      split at hc
      · cases hc
        obtain ⟨hl, hm⟩ := mem_sharedWrites hx
        rw [hm]
        obtain ⟨o, hR, ho⟩ := hop
        have hR' : Guarded (WriteSharedPre ks.toK (s.view c) a ls) (write3Eff (s.view c) ls) o :=
          hR
        cases hR' with
        | ok hp => exact cap_covers_of hF hr (allows_observe (hp.effectivePresent _ hl))
        | reject => cases ho
      · cases hc
    | _ => simp only [classify, Option.some.injEq] at hc; subst hc; cases hx
  | @readShared s reg ar c a l v order hs =>
    simp only [classify, Option.some.injEq] at hc; subst hc
    rw [List.mem_singleton.1 hx]
    exact cap_covers_of hF hr (allows_observe ((Guarded.ok_iff.1 hs).1.read.effectivePresent l
      (List.mem_singleton_self _)))
  | @writeShared s s' reg ar c a region ord kind hw =>
    simp only [classify, Option.some.injEq] at hc; subst hc
    obtain ⟨hl, hm⟩ := mem_sharedWrites hx
    rw [hm]
    exact cap_covers_of hF hr (allows_observe ((Guarded.ok_iff.1 hw).1.o11.effectivePresent _ hl))
  | @cas s s' reg ar c a l succ fail br hcas =>
    have hpres : effective s.flat a l ≠ none := by
      rcases hcas with ⟨-, h⟩ | ⟨-, h⟩
      · cases h
      · cases br with
        | success v =>
          exact (Guarded.ok_iff.1 h).1.o11.effectivePresent l (List.mem_singleton_self _)
        | failure v =>
          exact (Guarded.ok_iff.1 h).1.read.effectivePresent l (List.mem_singleton_self _)
    cases br <;>
    · simp only [classify, Option.some.injEq] at hc; subst hc
      rw [List.mem_singleton.1 hx]
      exact cap_covers_of hF hr (allows_observe hpres)
  | @newMutex s reg ar c g st₁ hn =>
    simp only [classify, Option.some.injEq] at hc; subst hc
    obtain ⟨ctl, hctl, rfl⟩ := List.mem_map.1 hx
    have hctl' : ControlOf L s ⟨g, none⟩ = some ctl := by simpa using hctl
    obtain ⟨-, hnr⟩ := hr
    unfold NewMutexRightFree at hnr
    rw [hctl'] at hnr
    obtain ⟨a, -, hxa, hea, -⟩ := hnr
    refine cap_covers_of hF hxa ?_
    show Allows (effective (s.view c) a ctl) .modify
    rw [hea]; exact Or.inr rfl
  | @acquire s reg ar c i st₁ ha =>
    simp only [classify, Option.some.injEq] at hc; subst hc
    obtain ⟨e, hei, hctl, hm⟩ := mem_ctlAccess hx
    rw [hm]
    simp only [RightsReadFree, hei, OptP] at hr
    exact cap_covers_ctl hF hr.1 hctl
  | @unlock s reg ar c i st₁ hu =>
    simp only [classify, Option.some.injEq] at hc; subst hc
    obtain ⟨e, hei, hctl, hm⟩ := mem_ctlAccess hx
    rw [hm]
    simp only [RightsReadFree, hei, OptP] at hr
    revert hr
    cases e.grant with
    | none => exact False.elim
    | some g => exact fun hr => cap_covers_ctl hF hr.2.1 hctl
  | @resetLock s reg ar c i st₁ hrl =>
    simp only [classify, Option.some.injEq] at hc; subst hc
    obtain ⟨e, hei, hctl, hm⟩ := mem_ctlAccess hx
    rw [hm]
    simp only [RightsReadFree, hei, OptP] at hr
    exact cap_covers_ctl hF hr.2 hctl
  | _ => simp only [classify, Option.some.injEq] at hc; subst hc; cases hx

end Ern.ConcurrencyModel
