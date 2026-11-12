import Ern.Concurrency.MutexReal.Amend
import Ern.Concurrency.Corpus.ResetLockRight

/-!
# W-NC: `newMutex` without a right on the controller

`corpus-spec2-m3.md` v11 §2 decies, witness W-NC and its twin, at the level of the authority
machine, from steps 1 and 2 of block MX (`guarded` derived and stored in `slot`, `lock` `Init`, no
entry). WC5.1 corrigé C14 item 3 and C17 item 4 require a right of access to the controller; C13
has none. Verdicts written from the corpus, preconditions by `decide`, contract `KM`. No amendment
of C13 is tested.
-/

set_option autoImplicit false

namespace Ern.Concurrency.Corpus.NewMutexRight

open Ern.MemoryModel.Access Ern.Concurrency Ern.Concurrency.Corpus
open Ern.Concurrency.Corpus.ResetLockRight (rc1 rc2 W_RC_1_ok W_RC_2_ok W_RC_no_ctl_mode)
open Ern.Concurrency.Traces (L0)

/-- `corpus-spec2-m3.md` v11 §2 decies W-NC, steps 1 and 2, `ok`: `c0 : s := derive(root_M, Modify,
{slot})` (O1), then `c0 : enterFrame f1` yielding `s` (O6); the states are those of W-RC with an
empty registry. Before step 3, no authority exercisable from `f1`, in either mode, has a present
effective mode on `lock` (place 2). -/
theorem W_NC_12_ok : opStepC KM (.derive 0 [1] .modify) 0 x2 (.ok rc1) ∧
    opStepC KM (.enter [4] []) 0 rc1 (.ok rc2) ∧ (rc2.view 0).top = 1 ∧
    ∀ a ∈ List.range rc2.A.length, ∀ m ∈ [Mode.observe, Mode.modify],
      (rc2.view 0).ExercisableAt a m → effective rc2.flat a 2 = none :=
  ⟨W_RC_1_ok.1, W_RC_2_ok.1, W_RC_2_ok.2, W_RC_no_ctl_mode⟩

/-- `corpus-spec2-m3.md` v11 §2 decies W-NC, step 3, `c0 (f1) : newMutex(guarded)`, `ok`: WC5.1
corrigé C13.1 (`guarded` active, of mode `Modify`, held by the usable `slot`), C13.2 (`Modify`
exercisable over `guarded` by the third clause of Spec 1 §43, through `s`), C13.3, C13.4, C13.6 to
C13.9, C13.10 (the leaves of `M` are `Init`). No precondition of C13 reads a right on the
controller. -/
theorem W_NC_3_ok : NewMutexOk KM L0 [] rc2 [] 0 3 (rc2, regX) ∧
    (rc2.view 0).ExercisableAt 3 .modify :=
  ⟨⟨by decide, by decide, rfl⟩, by decide⟩

/-- `corpus-spec2-m3.md` v11 §2 decies, twin of W-NC: step 3 of block MX, `c0 (f0) :
newMutex(guarded)`, is `ok`. -/
theorem W_NC_twin_ok : NewMutexOk KM L0 [] x2 [] 0 3 (x2, regX) := mx_steps.2.2.1

/-- The labels of W-NC. -/
def ncLbls : List Label :=
  [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 3 1), .kernel 0 (.derive 0 [1] .modify),
   .kernel 0 (.enter [4] []), .newMutex 0 3]

/-- The named states of W-NC. -/
def ncσ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(x0, [], []), (x1, [], []), (x2, [], []), (rc1, [], []), (rc2, [], []), (rc2, regX, [])].getD i
    (rc2, regX, [])

/-- `corpus-spec2-m3.md` v11 §2 decies W-NC: the trace is a `Run5R` from the initial state, and a
`Run6` (no entry is live before the `newMutex`). -/
theorem W_NC_run : ncσ 0 = (SC.ofS3 (S3.init mxst), [], []) ∧ Run5R KM L0 ncσ ncLbls ∧
    MutexReal.Run6 KM L0 ncσ ncLbls := by
  have h : Steps5R KM L0 [(x0, [], []), (x1, [], []), (x2, [], []), (rc1, [], []), (rc2, [], []),
      (rc2, regX, [])] ncLbls :=
    .cons ⟨⟨(fun e he => by cases he), by decide, trivial⟩, trivial⟩ (.kernel mx_steps.1) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, by decide⟩ (.kernel mx_steps.2.1) <|
    .cons ⟨⟨(fun e he => by cases he), by decide, trivial⟩, trivial⟩ (.kernel W_RC_1_ok.1) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, trivial⟩ (.kernel W_RC_2_ok.1) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, trivial⟩ (.newMutex W_NC_3_ok.1) .nil
  have hr := h.run (rc2, regX, [])
  exact ⟨rfl, hr, MutexReal.run6_of_run5R hr (by decide)⟩

end Ern.Concurrency.Corpus.NewMutexRight
