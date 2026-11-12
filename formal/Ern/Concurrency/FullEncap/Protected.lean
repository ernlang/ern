import Ern.Concurrency.FullEncap.Witness

/-!
# Protected data

Brief of milestone 4, slice 3, task 5. The target corollary: on a `RunFull` from the initial
state, a step whose final footprint contains a leaf protected by an entry live before and after
the step (a leaf of `footprint(guarded)`, WC5.2 C13, C21) is made by a context whose capacity on
that leaf comes from the subtree of the registered grant of that entry (WC5.2 C21 item 5,
`GrantSubtree`; C22, `GrantDiscipline`).

* `ProtectedOK` states it for one step, decidably; `CapFromGrant` reads "the capacity of `c` on
  `l` comes from the subtree of the grant": `cap5(c, l)` is present and attained by the grant or
  one of its active descendants, attributable to `c`.
* On `Run7`, W-GI refutes it (`protected_run7_refuted`).
* On `RunFull`, an abandoned grant refutes it (`protected_runFull_refuted`): a derivative of the
  grant yielded to a child context survives the exit of the frame holding the grant and is
  reanchored to `guarded` (Spec 1 §73, `exitG`); the grant stays recorded and inactive (WC5.2
  C18: "A grant may become inactive through ... frame exit"), and C21 item 5 says nothing of an
  inactive grant.
-/

set_option autoImplicit false

namespace Ern.Concurrency.FullEncap.Protected

open Ern.MemoryModel Ern.MemoryModel.Access Ern.Concurrency Ern.Concurrency.MutexReal
open Ern.Concurrency.Corpus Ern.Concurrency.FullEncap.Witness
open Ern.Concurrency.Traces (L0)

/-- The capacity of `c` on leaf `l` comes from the subtree of the registered grant of entry `e`
(brief of slice 3, task 5): `cap5(c, l)` (WC5.2 C43) is present, and the grant or one of its
descendants (Spec 1 §42, origin chain) is attributable to `c` without a live `guarded` with an
effective mode on `l` at least that capacity. False when no grant is recorded. -/
def CapFromGrant (s : SC) (reg : SyncReg) (c : Nat) (e : SyncEntry) (l : Nat) : Prop :=
  OptP e.grant (fun g => ∃ x ∈ List.range s.A.length, (x = g ∨ g ∈ s.flat.ancs x) ∧
    OptP (cap5 s reg c l) (fun m => Attr5 s reg c x m ∧ Allows (effective s.flat x l) m) False)
    False

/-- Decidability of `CapFromGrant`. -/
instance (s : SC) (reg : SyncReg) (c : Nat) (e : SyncEntry) (l : Nat) :
    Decidable (CapFromGrant s reg c e l) := by
  unfold CapFromGrant; infer_instance

/-- The corollary of task 5 for one step from `st` to `st'` (brief of slice 3, task 5): for every
entry live before and after the step and every leaf of `footprint(guarded)` in the final footprint
of the step, the capacity of the acting context on that leaf comes from the subtree of the grant
recorded before the step. -/
def ProtectedOK (L : MutexLayout) (st : SC × SyncReg × ArenaReg) (lbl : Label)
    (st' : SC × SyncReg × ArenaReg) : Prop :=
  ∀ e ∈ st.2.1, e.Live st.1 → e.Live st'.1 → ∀ l ∈ st.1.flat.afp e.guarded,
    TouchesF L st lbl l → CapFromGrant st.1 st.2.1 lbl.ctx e l

/-- Decidability of `ProtectedOK`. -/
instance (L : MutexLayout) (st : SC × SyncReg × ArenaReg) (lbl : Label)
    (st' : SC × SyncReg × ArenaReg) : Decidable (ProtectedOK L st lbl st') := by
  unfold ProtectedOK; infer_instance

/-! ## On `Run7`: W-GI -/

/-- Brief of slice 3, task 5, "faux sur `Run7`": W-GI is a final amended execution (`Run7`) from
the initial state whose step 1, `c0 : issue(arena0, R1, t)`, touches the protected leaf `t` of the
live entry `e` without the lock: no grant is recorded and `c0` has no `cap5` on `t`. On the twin,
under the grant of `c0`, the same step satisfies the corollary. -/
theorem protected_run7_refuted : Run7 KM L0 giσ giLbls ∧
    ¬ ProtectedOK L0 (giσ 8) (.issue 0 0 [5] 3) (giσ 9) ∧ cap5 gi6 giReg 0 3 = none ∧
    ProtectedOK L0 (gtσ 9) (.issue 0 0 [5] 3) (gtσ 10) :=
  ⟨W_GI_current.2.1, by decide, by decide, by decide⟩

/-! ## On `RunFull`: an abandoned grant -/

/-- `o := derive(root_M, Observe, {lock})`, authority 4 (O1). -/
def ab3 : SC := x2.set (deriveEff (x2.view 0) 0 [2] .observe)
/-- `c0 : enterFrame([o], [])` (O6): frame 1 holds `o`. -/
def ab4 : SC := enterEffC ab3 0 [4] []
/-- `c0 : acquire(e)`: grant `g`, authority 5, held by frame 1 (WC5.2 C16). -/
def ab5 : SC := deriveSyncEff ab4 0 3
/-- The registry with `g` recorded. -/
def abReg : SyncReg := [⟨3, some 5⟩]
/-- `x := derive(g, Modify, {T})`, authority 6, held by frame 1 (O1). -/
def ab6 : SC := ab5.set (deriveEff (ab5.view 0) 5 [3] .modify)
/-- `c0 : spawn([x])` (WC5.2 C4): context 1, initial frame 2 holds `x`. -/
def ab7 : SC := spawnEff ab6 0 [6] []
/-- `c0 : exitFrame` (O7; WC5.2 C6): frame 1 ends; `g` and `o` are released, `x` survives in
context 1 and is reanchored to `guarded`. -/
def ab8 : SC := exitEffC ab7 0
/-- `c1 : write3(T)` via `x` (O10). -/
def ab9 : SC := ab8.set (write3Eff (ab8.view 1) [3])

/-- The labels of the abandoned-grant trace. -/
def abLbls : List Label :=
  ClassifyWitness.mx3Lbls ++ [.kernel 0 (.derive 0 [2] .observe), .kernel 0 (.enter [4] []),
    .acquire 0 0, .kernel 0 (.derive 5 [3] .modify), .spawn 0 [6] [], .kernel 0 .exit,
    .kernel 1 (.write 6 [3])]

/-- The named states of the abandoned-grant trace. -/
def abσ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(x0, [], []), (x1, [], []), (x2, [], []), (x2, regX, []), (ab3, regX, []), (ab4, regX, []),
    (ab5, abReg, []), (ab6, abReg, []), (ab7, abReg, []), (ab8, abReg, []),
    (ab9, abReg, [])].getD i (ab9, abReg, [])

/-- Brief of slice 3, task 5, on `RunFull`: refuted. From `MX₃`, `c0` enters a frame with the
controller right `o`, acquires `e` (grant `g` held by that frame), derives `x` from `g`, yields `x`
to a new context `c1`, and exits the frame without `unlock` (WC5.2 C18: the grant becomes inactive
by frame exit; `x` survives in `c1` and its origin becomes `guarded`, Spec 1 §73). Then
`c1 : write3(T)` via `x` touches the protected leaf `T` of entry `e`, live before and after, whose
recorded grant `g` is inactive and has no descendant: the capacity of `c1` comes from `x`, outside
the subtree of `g`. Every step is admitted by the complete encapsulation: the trace is a `RunFull`
from the initial state. -/
theorem protected_runFull_refuted : abσ 0 = (SC.ofS3 (S3.init mxst), [], []) ∧
    RunFull KM L0 abσ abLbls ∧ ¬ ProtectedOK L0 (abσ 9) (.kernel 1 (.write 6 [3])) (abσ 10) ∧
    ¬ ab8.flat.Active 5 ∧ ab8.flat.ancs 6 = [3, 1] ∧ cap5 ab8 abReg 1 3 = some .modify ∧
    (⟨3, some 5⟩ : SyncEntry).Live ab8 ∧ (⟨3, some 5⟩ : SyncEntry).Live ab9 := by
  have h : Steps5R KM L0 [(x2, regX, []), (ab3, regX, []), (ab4, regX, []), (ab5, abReg, []),
      (ab6, abReg, []), (ab7, abReg, []), (ab8, abReg, []), (ab9, abReg, [])]
      [.kernel 0 (.derive 0 [2] .observe), .kernel 0 (.enter [4] []), .acquire 0 0,
        .kernel 0 (.derive 5 [3] .modify), .spawn 0 [6] [], .kernel 0 .exit,
        .kernel 1 (.write 6 [3])] :=
    .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons (by decide) (.kernel ⟨by decide, .ok (by decide)⟩) <|
    .cons (by decide) (.acquire ⟨by decide, ⟨3, none⟩, rfl, by decide, by decide, rfl⟩) <|
    .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons (by decide) (.spawn ⟨by decide, .ok (by decide)⟩) <|
    .cons (by decide) (.kernel ⟨by decide, .ok (by decide)⟩) <|
    .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) .nil
  exact ⟨rfl, runFull_of_run7 (run7_of_run5R ((ClassifyWitness.mx3_steps h).run _) (by decide))
    (by decide), by decide, by decide, by decide, by decide, by decide, by decide⟩

end Ern.Concurrency.FullEncap.Protected
