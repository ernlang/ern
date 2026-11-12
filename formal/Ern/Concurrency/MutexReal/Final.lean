import Ern.Concurrency.MutexReal.Amend

/-!
# The final wording of the amendments

Brief of milestone 4, slice 2, layer R, final pass, task 1 (`formal/reports/spec2-m4-mutexreal.md`,
§ Passe finale). The second version of the **proposed, not validated** amendments
(`ERN_WC5_2_amendements_proposes.md`), encoded beside the existing definitions, which are
unchanged:

* amendment 1, the final C22 item 4: the final footprint (`TouchesF`) is `Touches`, except that
  the owner of an `alloc` counts as the place itself, not by its leaves; the provider still counts
  by its leaves, and the place `result` of a `depend` is not in it. The final restriction
  (`CtlRestrF`) is `CtlRestr` read on `TouchesF`, with the same three exceptions. The final
  encapsulation (`Encap7`) is `Encap5R` and `CtlRestrF`. Executions: `Run7`;
* amendment 3, the proposed C13 item 11: `newMutex` also needs exercisable `Modify` with effective
  `Modify` on the controller, in the form the model uses for O10.1 (Spec 1 §67.1, `Write3Pre`)
  (`NewMutexRight`). The step relation is unchanged: the amended step is a predicate beside it
  (`NewMutexAmOk`);
* a final amended execution (`RunAmF`) is a `Run7` whose `resetLock` steps satisfy the clause of
  the proposed C18 item 4 and whose `newMutex` steps satisfy the clause of the proposed C13
  item 11 (`AmCondF`).

`Run6 → Run7` holds when the controller of every live entry is a leaf (WC5.1 corrigé C21 item 3,
`SyncInv`), in particular on every `Run6` from the initial state (`run7_of_run6_init`).
-/

set_option autoImplicit false

namespace Ern.Concurrency.MutexReal

open Ern.MemoryModel Ern.MemoryModel.Access Ern.Concurrency

/-! ## Amendment 1, final wording -/

/-- The final footprint (brief, final pass, "Empreinte finale"; final C22 item 4, "evaluated against
the leaves actually affected"): `Touches`, except for `alloc`, whose owner counts as the place
itself (the holder of the new root, Spec 1 §71 effect), not by its leaves; the provider (its
metadata, §71.2) counts by its leaves, and the fresh leaves stay. `depend` has an empty footprint,
as in `Touches`. -/
def TouchesF (L : MutexLayout) (st : SC × SyncReg × ArenaReg) : Label → Nat → Prop
  | .kernel _ (.alloc pr ow _), l => l ∈ footprint st.1.P pr ∨ l = ow ∨ st.1.P.length ≤ l
  | lbl, l => Touches L st lbl l

/-- Decidability of `TouchesF`. -/
instance (L : MutexLayout) (st : SC × SyncReg × ArenaReg) (lbl : Label) (l : Nat) :
    Decidable (TouchesF L st lbl l) := by
  unfold TouchesF; split <;> infer_instance

/-- The final restriction of the controller (final C22 item 4; brief, final pass): `CtlRestr` read
on the final footprint. For every entry `i` live before the step from `st` to `st'`, if the final
footprint of the step contains `ControlOf(i)`, then the step is a protocol step of entry `i`, or a
move admitted by C22 item 3, or entry `i` is dead after it. -/
def CtlRestrF (L : MutexLayout) (st : SC × SyncReg × ArenaReg) (lbl : Label)
    (st' : SC × SyncReg × ArenaReg) : Prop :=
  ∀ i ∈ List.range st.2.1.length, OptP (st.2.1[i]?) (fun x => x.Live st.1 →
    OptP (ControlOf L st.1 x) (fun ctl => TouchesF L st lbl ctl →
      ctlOp i lbl ≠ none ∨ C223Move L (st.1, st.2.1) lbl ∨ ¬ x.Live st'.1) True) True

/-- Decidability of `CtlRestrF`. -/
instance (L : MutexLayout) (st : SC × SyncReg × ArenaReg) (lbl : Label)
    (st' : SC × SyncReg × ArenaReg) : Decidable (CtlRestrF L st lbl st') := by
  unfold CtlRestrF; infer_instance

/-- `CtlRestrF` read on one entry. -/
theorem CtlRestrF.apply {L : MutexLayout} {st st' : SC × SyncReg × ArenaReg} {lbl : Label}
    (h : CtlRestrF L st lbl st') {i : Nat} {x : SyncEntry} (hx : st.2.1[i]? = some x)
    (hl : x.Live st.1) {ctl : Nat} (hc : ControlOf L st.1 x = some ctl)
    (ht : TouchesF L st lbl ctl) :
    ctlOp i lbl ≠ none ∨ C223Move L (st.1, st.2.1) lbl ∨ ¬ x.Live st'.1 := by
  have hi := h i (List.mem_range.2 (List.getElem?_eq_some_iff.1 hx).1)
  rw [hx] at hi
  have hi' := hi hl
  rw [hc] at hi'
  exact hi' ht

/-- The final encapsulation of a step from `st` to `st'` (brief, final pass): `Encap5R` and the
final restriction of the controller. -/
def Encap7 (k : K) (L : MutexLayout) (st : SC × SyncReg × ArenaReg) (lbl : Label)
    (st' : SC × SyncReg × ArenaReg) : Prop :=
  Encap5R k L st lbl ∧ CtlRestrF L st lbl st'

/-- `Run7` (brief, final pass): a run with named states every step of which satisfies `Encap7` and
is an `ok` step. -/
def Run7 (k : K) (L : MutexLayout) (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) :
    Prop :=
  ∀ i (h : i < lbls.length), Encap7 k L (σ i) lbls[i] (σ (i + 1)) ∧
    LStep k L lbls[i] (σ i) (σ (i + 1))

/-- Brief, final pass, task 1: every `Run7` is a `Run5R`. -/
theorem run7_run5R {k : K} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg}
    {lbls : List Label} (h : Run7 k L σ lbls) : Run5R k L σ lbls :=
  fun i hi => ⟨(h i hi).1.1, (h i hi).2⟩

/-- A `Run5R` whose steps all satisfy the final restriction is a `Run7`. -/
theorem run7_of_run5R {k : K} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg}
    {lbls : List Label} (h : Run5R k L σ lbls)
    (hc : ∀ i (hi : i < lbls.length), CtlRestrF L (σ i) lbls[i] (σ (i + 1))) : Run7 k L σ lbls :=
  fun i hi => ⟨⟨(h i hi).1, hc i hi⟩, (h i hi).2⟩

/-- A `Run7` satisfies the final restriction at each step. -/
theorem Run7.restr {k : K} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg}
    {lbls : List Label} (h : Run7 k L σ lbls) {i : Nat} (hi : i < lbls.length) :
    CtlRestrF L (σ i) lbls[i] (σ (i + 1)) :=
  (h i hi).1.2

/-! ## Footprints -/

/-- The final footprint is `Touches` on every label other than `alloc`. -/
theorem touchesF_of_not_alloc {L : MutexLayout} {st : SC × SyncReg × ArenaReg} {lbl : Label}
    (h : ∀ c pr ow ls, lbl ≠ .kernel c (.alloc pr ow ls)) (l : Nat) :
    TouchesF L st lbl l ↔ Touches L st lbl l := by
  cases lbl with
  | kernel c op =>
    cases op with
    | alloc pr ow ls => exact absurd rfl (h c pr ow ls)
    | _ => exact Iff.rfl
  | _ => exact Iff.rfl

/-- On a leaf, the final footprint is contained in `Touches`: the owner of an `alloc`, counted as
the place itself, is then its own only leaf (Spec 1 §40). -/
theorem touches_of_touchesF {L : MutexLayout} {st : SC × SyncReg × ArenaReg} {lbl : Label}
    {l : Nat} (h : TouchesF L st lbl l) (hl : isLeaf st.1.P l) (hlt : l < st.1.P.length) :
    Touches L st lbl l := by
  cases lbl with
  | kernel c op =>
    cases op with
    | alloc pr ow ls =>
      rcases h with h | rfl | h
      · exact Or.inl h
      · exact Or.inr (Or.inl ((Arena.mem_footprint_leaf hl hlt).2 rfl))
      · exact Or.inr (Or.inr h)
    | _ => exact h
  | _ => exact h

/-- Brief, final pass, task 1, step form of `Run6 → Run7`: where the controller of every live entry
is a leaf (`SyncInv`, WC5.1 corrigé C21 item 3), the restriction tested in the corrective pass
entails the final restriction. -/
theorem ctlRestrF_of_ctlRestr {L : MutexLayout} {st st' : SC × SyncReg × ArenaReg} {lbl : Label}
    (h : CtlRestr L st lbl st') (hinv : SyncInv L st.1 st.2.1) : CtlRestrF L st lbl st' := by
  intro i hi
  have hi' := h i hi
  cases hx : st.2.1[i]? with
  | none => simp only [OptP]
  | some x =>
    rw [hx] at hi'
    simp only [OptP] at hi' ⊢
    intro hl
    have hctl := hinv.control x (List.mem_of_getElem? hx) hl
    have hi'' := hi' hl
    cases hc : ControlOf L st.1 x with
    | none => trivial
    | some ctl =>
      rw [hc] at hctl hi''
      simp only [OptP] at hctl hi'' ⊢
      exact fun ht => hi'' (Or.inl (touches_of_touchesF ht hctl.2 (ctl_lt hc)))

/-- Brief, final pass, task 1: a `Run6` whose states satisfy `SyncInv` before each step is a
`Run7`. -/
theorem run7_of_run6 {k : K} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg}
    {lbls : List Label} (h : Run6 k L σ lbls)
    (hinv : ∀ i, i < lbls.length → SyncInv L (σ i).1 (σ i).2.1) : Run7 k L σ lbls :=
  run7_of_run5R (run6_run5R h) fun i hi => ctlRestrF_of_ctlRestr (h.restr hi) (hinv i hi)

/-- Brief, final pass, task 1: every `Run6` from the initial state of Spec 1 §47, under `DDSound`
(Spec 1 §80), is a `Run7`; `SyncInv` holds along it (`trace_inv`). -/
theorem run7_of_run6_init {k : K} {L : MutexLayout} {statics : Statics}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} (hdd : DDSound k)
    (hstat : StaticsOK statics) (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], []))
    (h : Run6 k L σ lbls) : Run7 k L σ lbls := by
  refine run7_of_run6 h fun i hi => ?_
  have htr := run5R_prefix (run6_run5R h) (Nat.le_of_lt hi)
  rw [h0] at htr
  obtain ⟨hk₀, hs₀⟩ := init_inv (k := k) hdd hstat L
  exact (trace_inv hdd htr hk₀ hs₀).2.1.1

/-! ## Amendment 3 -/

/-- The clause of the proposed C13 item 11 for `newMutex(g)` executed by `c`: some authority is
exercisable in `Modify` by the current frame of `c` and has effective `Modify` on the controller
`ControlOf(⟨g, none⟩)`; these are the clauses `exercisable` and `effectiveModify` of the
preconditions of O10 (Spec 1 §67.1, `Write3Pre`) on the view of `c`, as for a `write` by `c`. -/
def NewMutexRight (L : MutexLayout) (s : SC) (c g : Nat) : Prop :=
  OptP (ControlOf L s ⟨g, none⟩) (fun ctl => ∃ a ∈ List.range s.A.length,
    (s.view c).ExercisableAt a .modify ∧ effective (s.view c) a ctl = some .modify) False

/-- Decidability of `NewMutexRight`. -/
instance (L : MutexLayout) (s : SC) (c g : Nat) : Decidable (NewMutexRight L s c g) := by
  unfold NewMutexRight; infer_instance

/-- The amended `newMutex(g)` executed by `c` (proposed C13 item 11; brief, final pass): the
preconditions and effect of `NewMutexOk` (WC5.1 corrigé C13) and the clause `NewMutexRight`. -/
def NewMutexAmOk (k : K) (L : MutexLayout) (ar : ArenaReg) (s : SC) (reg : SyncReg) (c g : Nat)
    (st' : SC × SyncReg) : Prop :=
  NewMutexOk k L ar s reg c g st' ∧ NewMutexRight L s c g

/-- Brief, final pass, task 1: an amended `newMutex` that is `ok` is a `newMutex` that is `ok`, with
the same final state. -/
theorem NewMutexAmOk.ok {k : K} {L : MutexLayout} {ar : ArenaReg} {s : SC} {reg : SyncReg}
    {c g : Nat} {st' : SC × SyncReg} (h : NewMutexAmOk k L ar s reg c g st') :
    NewMutexOk k L ar s reg c g st' :=
  h.1

/-! ## Final amended execution -/

/-- The clauses added to a step by the proposed C18 item 4 and C13 item 11: for `resetLock(i)` by
`c`, the controller-access right of the current frame of `c` on entry `i` (`AmCond`); for
`newMutex(g)` by `c`, `NewMutexRight`; no condition on other steps. -/
def AmCondF (L : MutexLayout) (st : SC × SyncReg × ArenaReg) : Label → Prop
  | .resetLock c i => OptP (st.2.1[i]?) (fun e => CtrlRight L st.1 e (st.1.view c).top) False
  | .newMutex c g => NewMutexRight L st.1 c g
  | _ => True

/-- Decidability of `AmCondF`. -/
instance (L : MutexLayout) (st : SC × SyncReg × ArenaReg) (lbl : Label) :
    Decidable (AmCondF L st lbl) := by
  unfold AmCondF; split <;> infer_instance

/-- A final amended execution (brief, final pass): a `Run7` each `resetLock` step of which satisfies
the clause of the proposed C18 item 4 and each `newMutex` step the clause of the proposed C13
item 11. -/
def RunAmF (k : K) (L : MutexLayout) (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) :
    Prop :=
  Run7 k L σ lbls ∧ ∀ i (h : i < lbls.length), AmCondF L (σ i) lbls[i]

/-- `AmCondF` contains `AmCond`. -/
theorem amCond_of_amCondF {L : MutexLayout} {st : SC × SyncReg × ArenaReg} {lbl : Label}
    (h : AmCondF L st lbl) : AmCond L st lbl := by
  cases lbl <;> first | exact h | exact trivial

/-- An `ok` `newMutex` step is a `NewMutexOk` of the registry, the arena registry unchanged. -/
theorem lstep_newMutex {k : K} {L : MutexLayout} {c g : Nat} {st st' : SC × SyncReg × ArenaReg}
    (h : LStep k L (.newMutex c g) st st') :
    NewMutexOk k L st.2.2 st.1 st.2.1 c g (st'.1, st'.2.1) := by
  cases h with
  | newMutex hn => exact hn

/-- In a final amended execution, every `resetLock` step is an amended `resetLock` that is `ok`. -/
theorem RunAmF.resetLock {k : K} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg}
    {lbls : List Label} (h : RunAmF k L σ lbls) {i : Nat} (hi : i < lbls.length) {c j : Nat}
    (hl : lbls[i] = .resetLock c j) :
    ResetLockAmOk L (σ i).1 (σ i).2.1 c j ((σ (i + 1)).1, (σ (i + 1)).2.1) := by
  have hs := (h.1 i hi).2
  have ha := h.2 i hi
  rw [hl] at hs ha
  exact ⟨lstep_resetLock hs, ha⟩

/-- In a final amended execution, every `newMutex` step is an amended `newMutex` that is `ok`. -/
theorem RunAmF.newMutex {k : K} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg}
    {lbls : List Label} (h : RunAmF k L σ lbls) {i : Nat} (hi : i < lbls.length) {c g : Nat}
    (hl : lbls[i] = .newMutex c g) :
    NewMutexAmOk k L (σ i).2.2 (σ i).1 (σ i).2.1 c g ((σ (i + 1)).1, (σ (i + 1)).2.1) := by
  have hs := (h.1 i hi).2
  have ha := h.2 i hi
  rw [hl] at hs ha
  exact ⟨lstep_newMutex hs, ha⟩

end Ern.Concurrency.MutexReal
