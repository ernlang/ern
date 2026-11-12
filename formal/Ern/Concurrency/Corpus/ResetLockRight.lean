import Ern.Concurrency.Events
import Ern.Concurrency.Corpus.MX

/-!
# W-RC: `resetLock` without a right on the controller

`corpus-spec2-m3.md` v10 §2 nonies, witness W-RC and its twin, at the level of the authority
machine, from `MX₃`. WC5.1 corrigé C17 item 4 requires for `unlock` a right of access to the
controller; C18 has no equivalent clause. Verdicts written from the corpus, preconditions by
`decide`, contract `KM`. The trace of the `ok` steps is a `Run5R` from the initial state of Spec 1
§47.
-/

set_option autoImplicit false

namespace Ern.Concurrency.Corpus.ResetLockRight

open Ern.MemoryModel.Access Ern.Concurrency Ern.Concurrency.Corpus
open Ern.Concurrency.Traces (L0)

/-- W-RC step 1, `c0 : s := derive(root_M, Modify, {slot})`: authority 4 (O1). -/
def rc1 : SC := x2.set (deriveEff (x2.view 0) 0 [1] .modify)
/-- W-RC step 2, `c0 : enterFrame f1` yielding `s` (O6): frame 1. -/
def rc2 : SC := enterEffC rc1 0 [4] []

/-- `corpus-spec2-m3.md` v10 §2 nonies W-RC, step 1, `ok` (O1): `root_M` is held by `f0` with
effective `Modify` on `slot`. After the step, `root_M` has no effective mode on `slot` (Spec 1
§43.3) and keeps effective `Modify` on `lock`. -/
theorem W_RC_1_ok : opStepC KM (.derive 0 [1] .modify) 0 x2 (.ok rc1) ∧
    effective rc1.flat 0 1 = none ∧ effective rc1.flat 0 2 = some .modify :=
  ⟨⟨by decide, _, .ok (by decide), rfl⟩, by decide, by decide⟩

/-- `corpus-spec2-m3.md` v10 §2 nonies W-RC, step 2, `ok` (O6): `enterFrame f1` yielding `s`, a
derived active authority held by the calling frame. The current frame of context 0 is then `f1`
(frame 1). -/
theorem W_RC_2_ok : opStepC KM (.enter [4] []) 0 rc1 (.ok rc2) ∧ (rc2.view 0).top = 1 :=
  ⟨⟨by decide, .ok (by decide)⟩, by decide⟩

/-- `corpus-spec2-m3.md` v10 §2 nonies W-RC, before step 4: no authority exercisable from `f1`, in
either mode, has a present effective mode on `lock` (place 2). -/
theorem W_RC_no_ctl_mode : ∀ a ∈ List.range rc2.A.length, ∀ m ∈ [Mode.observe, Mode.modify],
    (rc2.view 0).ExercisableAt a m → effective rc2.flat a 2 = none := by
  decide

/-- `corpus-spec2-m3.md` v10 §2 nonies W-RC, step 3, `c0 (f1) : acquire(e)`: no `ok` outcome; the
failing clause is WC5.1 corrigé C14.3 (no right of access to the controller), C14.1 (live entry)
and C14.2 (`grant = none`) holding. Under the criterion of the corpus §0: `reject`. -/
theorem W_RC_3_reject : (∀ st', ¬ AcquireOk KM L0 rc2 regX 0 0 st') ∧
    (⟨3, none⟩ : SyncEntry).Live rc2 ∧ (⟨3, none⟩ : SyncEntry).grant = none ∧
    ¬ CtrlRight L0 rc2 ⟨3, none⟩ (rc2.view 0).top := by
  have hc : ¬ CtrlRight L0 rc2 ⟨3, none⟩ (rc2.view 0).top := by decide
  refine ⟨?_, by decide, rfl, hc⟩
  rintro st' ⟨-, e, he, ⟨-, -, hcr⟩, -⟩
  simp only [regX, List.getElem?_cons_zero, Option.some.injEq] at he
  subst he
  exact hc hcr

/-- `corpus-spec2-m3.md` v10 §2 nonies W-RC, step 4, `c0 (f1) : resetLock(e)`, `ok`: WC5.1 corrigé
C18.1, `ExercisableAt(guarded, Modify)` by the third clause of Spec 1 §43 (`guarded` held by
`slot`, on whose leaves `s`, exercisable from `f1`, has effective `Modify`); C18.2, no active
descendant of `guarded`; C18.3, the controller is a usable leaf. No precondition of C18 reads a
right on `lock`. -/
theorem W_RC_4_ok : ResetLockOk L0 rc2 regX 0 0 (rc2, regX) :=
  ⟨by decide, ⟨3, none⟩, rfl, by decide, by decide, by decide, rfl⟩

/-- `corpus-spec2-m3.md` v10 §2 nonies, twin of W-RC: from `MX₃`, `c0 (f0) : resetLock(e)` is `ok`,
`f0` having effective `Modify` on `slot` and on `lock`. -/
theorem W_RC_twin_ok : ResetLockOk L0 x2 regX 0 0 (x2, regX) ∧
    effective x2.flat 0 1 = some .modify ∧ effective x2.flat 0 2 = some .modify :=
  ⟨⟨by decide, ⟨3, none⟩, rfl, by decide, by decide, by decide, rfl⟩, by decide, by decide⟩

/-- The labels of the `ok` steps of W-RC: block MX up to `MX₃`, then steps 1, 2 and 4. -/
def rcLbls : List Label :=
  [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 3 1), .newMutex 0 3,
   .kernel 0 (.derive 0 [1] .modify), .kernel 0 (.enter [4] []), .resetLock 0 0]

/-- The named states of W-RC. -/
def rcσ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(x0, [], []), (x1, [], []), (x2, [], []), (x2, regX, []), (rc1, regX, []), (rc2, regX, []),
    (rc2, regX, [])].getD i (rc2, regX, [])

/-- `corpus-spec2-m3.md` v10 §2 nonies W-RC: the `ok` steps form a `Run5R` from the initial state;
`Encap5R` admits each of them, the `resetLock` of step 4 included. -/
theorem W_RC_run : rcσ 0 = (SC.ofS3 (S3.init mxst), [], []) ∧ Run5R KM L0 rcσ rcLbls := by
  have h : Steps5R KM L0 [(x0, [], []), (x1, [], []), (x2, [], []), (x2, regX, []),
      (rc1, regX, []), (rc2, regX, []), (rc2, regX, [])] rcLbls :=
    .cons ⟨⟨(fun e he => by cases he), by decide, trivial⟩, trivial⟩ (.kernel mx_steps.1) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, by decide⟩ (.kernel mx_steps.2.1) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, trivial⟩ (.newMutex mx_steps.2.2.1) <|
    .cons ⟨⟨(by decide : ∀ e ∈ regX, e.Live x2 → 0 ≠ e.guarded), by decide, trivial⟩, trivial⟩
      (.kernel W_RC_1_ok.1) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, trivial⟩ (.kernel W_RC_2_ok.1) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, trivial⟩ (.resetLock W_RC_4_ok) .nil
  exact ⟨rfl, h.run _⟩

end Ern.Concurrency.Corpus.ResetLockRight
