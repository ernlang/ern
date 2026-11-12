import Ern.Concurrency.MutexReal.Classify

/-!
# The proposed amendments to C22 item 4 and C18

Brief of milestone 4, slice 2, layer R, corrective pass, task 1
(`formal/reports/spec2-m4-mutexreal.md`, § Passe corrective). Two **proposed, not validated**
amendments to WC5.1 corrigé (`ERN_WC5_2_amendements_proposes.md`), encoded beside the existing
definitions, which are unchanged:

* amendment 1, the new C22 item 4: for every entry live before the step, a step whose enlarged
  footprint (`TouchesX`) contains the controller is refused unless it is a protocol step of that
  entry, a `transfer` or by-value `spawn` admitted by C22 item 3, or a step after which the entry
  is dead (`CtlRestr`). The corrected encapsulation (`Encap6`) is `Encap5R` and `CtlRestr`; it
  reads the state after the step, since the last exception does. Executions: `Run6`;
* amendment 2, the new C18 item 4: `resetLock` also needs the controller-access right, in the form
  the model uses for C14 item 3 and C17 item 4 (`CtrlRight`). The step relation is unchanged: the
  amended step is a predicate beside it (`ResetLockAmOk`), and an amended execution is a `Run6`
  whose `resetLock` steps satisfy it (`RunAm`).
-/

set_option autoImplicit false

namespace Ern.Concurrency.MutexReal

open Ern.MemoryModel.Access Ern.Concurrency

/-! ## Amendment 1 -/

/-- The enlarged footprint (brief, corrective pass, "Empreinte élargie"): `Touches`, plus the place
`result` of a `depend`, whose anchors `D(result)` the step changes (Spec 1 §64 effect), the
"dependency state" of the proposed C22 item 4. The place itself, not its leaves: `depend` changes
`D` of `result` only (`dependEff`). -/
def TouchesX (L : MutexLayout) (st : SC × SyncReg × ArenaReg) (lbl : Label) (l : Nat) : Prop :=
  Touches L st lbl l ∨
    match lbl with
    | .kernel _ (.depend q _) => l = q
    | _ => False

/-- Decidability of `TouchesX`. -/
instance (L : MutexLayout) (st : SC × SyncReg × ArenaReg) (lbl : Label) (l : Nat) :
    Decidable (TouchesX L st lbl l) := by
  unfold TouchesX; split <;> infer_instance

/-- Decidability of `EncapVals` (WC5.1 corrigé C22 item 3 for the by-value composite). -/
instance instDecidableEncapVals (L : MutexLayout) (reg : SyncReg) (c : Nat) :
    (t : SC) → (vs : List (Nat × Nat)) → Decidable (EncapVals L reg c t vs)
  | _, [] => isTrue trivial
  | t, v :: vs =>
    haveI := instDecidableEncapVals L reg c (transferEffC t c v.1 v.2) vs
    inferInstanceAs (Decidable (TransferExcl L (t, reg) v.1 ∧ _))

/-- A `transfer` or a by-value `spawn` admitted by WC5.1 corrigé C22 item 3 (`TransferExcl`,
`EncapVals`): the exception of the proposed C22 item 4 for the legal moves of the mutex value. -/
def C223Move (L : MutexLayout) (st : SC × SyncReg) : Label → Prop
  | .kernel _ (.transfer src _) => TransferExcl L st src
  | .spawnVal c _ ls vs => EncapVals L st.2 c (spawnCreate st.1 c ls) vs
  | _ => False

/-- Decidability of `C223Move`. -/
instance (L : MutexLayout) (st : SC × SyncReg) (lbl : Label) : Decidable (C223Move L st lbl) := by
  unfold C223Move; split <;> infer_instance

/-- The restriction of the controller (proposed C22 item 4; brief, corrective pass): for every
entry `i` live before the step from `st` to `st'`, if the enlarged footprint of the step contains
`ControlOf(i)`, then the step is a protocol step of entry `i`, or a move admitted by C22 item 3, or
entry `i` is dead after it. -/
def CtlRestr (L : MutexLayout) (st : SC × SyncReg × ArenaReg) (lbl : Label)
    (st' : SC × SyncReg × ArenaReg) : Prop :=
  ∀ i ∈ List.range st.2.1.length, OptP (st.2.1[i]?) (fun x => x.Live st.1 →
    OptP (ControlOf L st.1 x) (fun ctl => TouchesX L st lbl ctl →
      ctlOp i lbl ≠ none ∨ C223Move L (st.1, st.2.1) lbl ∨ ¬ x.Live st'.1) True) True

/-- Decidability of `CtlRestr`. -/
instance (L : MutexLayout) (st : SC × SyncReg × ArenaReg) (lbl : Label)
    (st' : SC × SyncReg × ArenaReg) : Decidable (CtlRestr L st lbl st') := by
  unfold CtlRestr; infer_instance

/-- `CtlRestr` read on one entry. -/
theorem CtlRestr.apply {L : MutexLayout} {st st' : SC × SyncReg × ArenaReg} {lbl : Label}
    (h : CtlRestr L st lbl st') {i : Nat} {x : SyncEntry} (hx : st.2.1[i]? = some x)
    (hl : x.Live st.1) {ctl : Nat} (hc : ControlOf L st.1 x = some ctl)
    (ht : TouchesX L st lbl ctl) :
    ctlOp i lbl ≠ none ∨ C223Move L (st.1, st.2.1) lbl ∨ ¬ x.Live st'.1 := by
  have hi := h i (List.mem_range.2 (List.getElem?_eq_some_iff.1 hx).1)
  rw [hx] at hi
  have hi' := hi hl
  rw [hc] at hi'
  exact hi' ht

/-- The corrected encapsulation of a step from `st` to `st'` (brief, corrective pass): `Encap5R`
and the restriction of the controller. -/
def Encap6 (k : K) (L : MutexLayout) (st : SC × SyncReg × ArenaReg) (lbl : Label)
    (st' : SC × SyncReg × ArenaReg) : Prop :=
  Encap5R k L st lbl ∧ CtlRestr L st lbl st'

/-- `Run6` (brief, corrective pass): a run with named states every step of which satisfies
`Encap6` and is an `ok` step. -/
def Run6 (k : K) (L : MutexLayout) (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) :
    Prop :=
  ∀ i (h : i < lbls.length), Encap6 k L (σ i) lbls[i] (σ (i + 1)) ∧
    LStep k L lbls[i] (σ i) (σ (i + 1))

/-- Brief, corrective pass, task 1: every `Run6` is a `Run5R`. -/
theorem run6_run5R {k : K} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg}
    {lbls : List Label} (h : Run6 k L σ lbls) : Run5R k L σ lbls :=
  fun i hi => ⟨(h i hi).1.1, (h i hi).2⟩

/-- A `Run5R` whose steps all satisfy the restriction of the controller is a `Run6`. -/
theorem run6_of_run5R {k : K} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg}
    {lbls : List Label} (h : Run5R k L σ lbls)
    (hc : ∀ i (hi : i < lbls.length), CtlRestr L (σ i) lbls[i] (σ (i + 1))) : Run6 k L σ lbls :=
  fun i hi => ⟨⟨(h i hi).1, hc i hi⟩, (h i hi).2⟩

/-- A `Run6` satisfies the restriction of the controller at each step. -/
theorem Run6.restr {k : K} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg}
    {lbls : List Label} (h : Run6 k L σ lbls) {i : Nat} (hi : i < lbls.length) :
    CtlRestr L (σ i) lbls[i] (σ (i + 1)) :=
  (h i hi).1.2

/-! ## Amendment 2 -/

/-- The amended `resetLock` of entry `i` executed by `c` (proposed C18 item 4; brief, corrective
pass): the preconditions of `ResetLockOk` (WC5.1 corrigé C18.1–C18.3) and the controller-access
right of the acting frame on that entry, `CtrlRight`, the form of C14 item 3 and C17 item 4. -/
def ResetLockAmOk (L : MutexLayout) (s : SC) (reg : SyncReg) (c i : Nat) (st' : SC × SyncReg) :
    Prop :=
  ResetLockOk L s reg c i st' ∧ OptP (reg[i]?) (fun e => CtrlRight L s e (s.view c).top) False

/-- Brief, corrective pass, task 1: an amended `resetLock` that is `ok` is a `resetLock` that is
`ok`. -/
theorem ResetLockAmOk.ok {L : MutexLayout} {s : SC} {reg : SyncReg} {c i : Nat}
    {st' : SC × SyncReg} (h : ResetLockAmOk L s reg c i st') : ResetLockOk L s reg c i st' :=
  h.1

/-- The clause added by the proposed C18 item 4 to a step: for `resetLock(i)` by `c`, the
controller-access right of the current frame of `c` on entry `i`; no condition on other steps. -/
def AmCond (L : MutexLayout) (st : SC × SyncReg × ArenaReg) : Label → Prop
  | .resetLock c i => OptP (st.2.1[i]?) (fun e => CtrlRight L st.1 e (st.1.view c).top) False
  | _ => True

/-- Decidability of `AmCond`. -/
instance (L : MutexLayout) (st : SC × SyncReg × ArenaReg) (lbl : Label) :
    Decidable (AmCond L st lbl) := by
  unfold AmCond; split <;> infer_instance

/-- An amended execution (brief, corrective pass): a `Run6` each `resetLock` step of which
satisfies the clause of the proposed C18 item 4. -/
def RunAm (k : K) (L : MutexLayout) (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) :
    Prop :=
  Run6 k L σ lbls ∧ ∀ i (h : i < lbls.length), AmCond L (σ i) lbls[i]

/-- An `ok` `resetLock` step is a `ResetLockOk` of the registry. -/
theorem lstep_resetLock {k : K} {L : MutexLayout} {c i : Nat} {st st' : SC × SyncReg × ArenaReg}
    (h : LStep k L (.resetLock c i) st st') :
    ResetLockOk L st.1 st.2.1 c i (st'.1, st'.2.1) := by
  cases h with
  | resetLock hr => exact hr

/-- In an amended execution, every `resetLock` step is an amended `resetLock` that is `ok`. -/
theorem RunAm.resetLock {k : K} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg}
    {lbls : List Label} (h : RunAm k L σ lbls) {i : Nat} (hi : i < lbls.length) {c j : Nat}
    (hl : lbls[i] = .resetLock c j) :
    ResetLockAmOk L (σ i).1 (σ i).2.1 c j ((σ (i + 1)).1, (σ (i + 1)).2.1) := by
  have hs := (h.1 i hi).2
  have ha := h.2 i hi
  rw [hl] at hs ha
  exact ⟨lstep_resetLock hs, ha⟩

end Ern.Concurrency.MutexReal
