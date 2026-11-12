import Ern.Concurrency.MutexReal.Final
import Ern.Concurrency.MutexReal.AmendWitness
import Ern.Concurrency.Corpus.NewMutexRight

/-!
# Witnesses of the final wording of the amendments

Brief of milestone 4, slice 2, layer R, final pass, task 2 (`corpus-spec2-m3.md` v12 §2 undecies):
under the final restriction (`CtlRestrF`), the last steps of `store_cex`, `issue_cex` and
`alloc_cex` stay refused; `alloc(provider = slot, owner = M)` and `depend(lock, a)` are admitted;
`alloc(provider = M, owner = lock′)` is an `ok` kernel step refused by the final restriction. Under
the proposed C13 item 11, step 3 of W-NC has no `ok` outcome and its twin is `ok`. Verdicts and
facts are written from the corpus, checked by `decide`.
-/

set_option autoImplicit false

namespace Ern.Concurrency.MutexReal.FinalWitness

open Ern.MemoryModel Ern.MemoryModel.Access Ern.Concurrency Ern.Concurrency.MutexReal
open Ern.Concurrency.Corpus Ern.Concurrency.MutexReal.ClassifyWitness
open Ern.Concurrency.MutexReal.AmendWitness
open Ern.Concurrency.Corpus.ResetLockRight (rc2)
open Ern.Concurrency.Corpus.NewMutexRight (ncσ ncLbls W_NC_3_ok W_NC_run)
open Ern.Concurrency.Traces (L0)

/-! ## The three counter-examples stay refused -/

/-- `corpus-spec2-m3.md` v12 §2 undecies, `store`: the last step of `store_cex`,
`c0 : store(z, lock)`, is refused by the final restriction (final C22 item 4: `store` targeting
the controller leaf); the trace is no `Run7`. -/
theorem store_refusedF : ¬ CtlRestrF L0 (csσ 4) (.kernel 0 (.store 4 2)) (csσ 5) ∧
    ¬ Run7 KM L0 csσ csLbls := by
  have h : ¬ CtlRestrF L0 (csσ 4) (.kernel 0 (.store 4 2)) (csσ 5) := by decide
  exact ⟨h, fun hr => h (hr.restr (i := 4) (by decide))⟩

/-- `corpus-spec2-m3.md` v12 §2 undecies, `issue`: the last step of `issue_cex`,
`c0 : issue(arena, R1, lock2)`, is refused by the final restriction (`issue` using the controller
leaf as its destination); the trace is no `Run7`. -/
theorem issue_refusedF : ¬ CtlRestrF L0 (ciσ 7) (.issue 0 0 [5] 2) (ciσ 8) ∧
    ¬ Run7 KA L0 ciσ ciLbls := by
  have h : ¬ CtlRestrF L0 (ciσ 7) (.issue 0 0 [5] 2) (ciσ 8) := by decide
  exact ⟨h, fun hr => h (hr.restr (i := 7) (by decide))⟩

/-- `corpus-spec2-m3.md` v12 §2 undecies, `alloc`, owner = controller: the last step of
`alloc_cex`, `c0 : alloc(provider = slot, owner = lock)`, is refused by the final restriction
(`alloc` using the controller leaf itself as owner); the trace is no `Run7`. -/
theorem alloc_refusedF :
    ¬ CtlRestrF L0 (caσ 3) (.kernel 0 (.alloc 1 2 [(none, 0)])) (caσ 4) ∧
    ¬ Run7 KM L0 caσ caLbls := by
  have h : ¬ CtlRestrF L0 (caσ 3) (.kernel 0 (.alloc 1 2 [(none, 0)])) (caσ 4) := by decide
  exact ⟨h, fun hr => h (hr.restr (i := 3) (by decide))⟩

/-! ## `alloc`, owner = the whole mutex -/

/-- The labels of `alloc(provider = slot, owner = M)` from `MX₃`. -/
def amLbls : List Label := mx3Lbls ++ [.kernel 0 (.alloc 1 0 [(none, 0)])]

/-- The named states of `alloc(provider = slot, owner = M)` from `MX₃`. -/
def amσ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(x0, [], []), (x1, [], []), (x2, [], []), (x2, regX, []), (tam1, regX, [])].getD i
    (tam1, regX, [])

/-- `corpus-spec2-m3.md` v12 §2 undecies, `alloc`, owner = the whole mutex:
`c0 : alloc(provider = slot, owner = M)` is `ok` (obtained in the corrective pass,
`alloc_owner_M_refused`) and admitted: the trace from the initial state is a `Run7` (final C22
item 4: naming a structural place that contains the controller does not touch it; C13.5). -/
theorem alloc_owner_M_admitted : amσ 0 = (SC.ofS3 (S3.init mxst), [], []) ∧
    Run7 KM L0 amσ amLbls := by
  have h : Steps5R KM L0 [(x2, regX, []), (tam1, regX, [])]
      [.kernel 0 (.alloc 1 0 [(none, 0)])] :=
    .cons alloc_owner_M_refused.2.1 (.kernel alloc_owner_M_refused.1) .nil
  exact ⟨rfl, run7_of_run5R ((mx3_steps h).run _) (by decide)⟩

/-! ## `alloc`, provider containing the controller -/

/-- `c0 : alloc(provider = M, owner = lock′)` (O14). The effect `allocEff` does not read the
provider (its metadata is not represented), so the state is that of the twin of `alloc_cex`. -/
def pm1 : SC := x2.set (allocEff (x2.view 0) 6 [(none, 0)])

/-- The labels of `alloc(provider = M, owner = lock′)` from `MX₃`. -/
def pmLbls : List Label := mx3Lbls ++ [.kernel 0 (.alloc 0 6 [(none, 0)])]

/-- The named states of `alloc(provider = M, owner = lock′)` from `MX₃`. -/
def pmσ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(x0, [], []), (x1, [], []), (x2, [], []), (x2, regX, []), (pm1, regX, [])].getD i
    (pm1, regX, [])

/-- `corpus-spec2-m3.md` v12 §2 undecies, `alloc`, provider containing the controller: from `MX₃`,
`c0 : alloc(provider = M, owner = lock′)` is an `ok` kernel step, as expected (Spec 1 §71.2: the
leaves of `M` are `Init`, `Modify` exercisable through `root_M`; §71.3), admitted by `Encap5R`, and
the trace is a `Run5R` from the initial state; entry `e` stays live. The final restriction refuses
it (the provider metadata accesses may write the controller leaf: the provider counts by its
leaves, `lock` among them); the trace is no `Run7`. -/
theorem alloc_provider_M_refused : pmσ 0 = (SC.ofS3 (S3.init mxst), [], []) ∧
    opStepC KM (.alloc 0 6 [(none, 0)]) 0 x2 (.ok pm1) ∧ Run5R KM L0 pmσ pmLbls ∧
    (⟨3, none⟩ : SyncEntry).Live pm1 ∧ TouchesF L0 (pmσ 3) (.kernel 0 (.alloc 0 6 [(none, 0)])) 2 ∧
    ¬ CtlRestrF L0 (pmσ 3) (.kernel 0 (.alloc 0 6 [(none, 0)])) (pmσ 4) ∧
    ¬ Run7 KM L0 pmσ pmLbls := by
  have ha : opStepC KM (.alloc 0 6 [(none, 0)]) 0 x2 (.ok pm1) :=
    ⟨by decide, _, .ok (by decide) trivial, rfl⟩
  have h : Steps5R KM L0 [(x2, regX, []), (pm1, regX, [])] [.kernel 0 (.alloc 0 6 [(none, 0)])] :=
    .cons ⟨⟨trivial, trivial, trivial⟩, by decide⟩ (.kernel ha) .nil
  have hc : ¬ CtlRestrF L0 (pmσ 3) (.kernel 0 (.alloc 0 6 [(none, 0)])) (pmσ 4) := by decide
  exact ⟨rfl, ha, (mx3_steps h).run _, by decide, by decide, hc,
    fun hr => hc (hr.restr (i := 3) (by decide))⟩

/-! ## `depend` -/

/-- `corpus-spec2-m3.md` v12 §2 undecies, `depend`: `c0 : depend(lock, a)` is `ok` (obtained in
the corrective pass, `depend_refused`) and admitted: the trace from the initial state is a `Run7`
(final C22 item 4: a change solely to a dependency relation is not excluded). -/
theorem depend_admitted : Run7 KM L0 tdσ tdLbls :=
  run7_of_run5R depend_refused.2.1 (by decide)

/-! ## Positive twins -/

/-- `corpus-spec2-m3.md` v12 §2 undecies, positive twins, unchanged: `store(z, lock′)`,
`issue(arena, R1, d0)`, `alloc(provider = slot, owner = lock′)`, `depend(lock′, a)` are `Run7`
traces, by the inclusion of task 1 from the initial state. -/
theorem twins_run7 : Run7 KM L0 tsσ tsLbls ∧ Run7 KA L0 tiσ tiLbls ∧ Run7 KM L0 taσ taLbls ∧
    Run7 KM L0 tdtσ tdtLbls :=
  ⟨run7_of_run6_init (ddKC [2]) mxst_ok store_twin.1 store_twin.2,
    run7_of_run6_init (ddKC [2]) arst_ok issue_twin.1 issue_twin.2,
    run7_of_run6_init (ddKC [2]) mxst_ok alloc_twin.1 alloc_twin.2,
    run7_of_run6_init (ddKC [2]) mxst_ok depend_twin.1 depend_twin.2⟩

/-! ## `newMutex` under the proposed C13 item 11 -/

/-- `corpus-spec2-m3.md` v12 §2 undecies, W-NC step 3, `c0 (f1) : newMutex(guarded)`, under the
proposed C13 item 11: no `ok` outcome; the failing clause is item 11 (no authority exercisable in
`Modify` by `f1` has effective `Modify` on `lock`), the preconditions of WC5.1 corrigé C13 holding
(`NewMutexOk`). Under the criterion of the corpus §0: `reject`. -/
theorem W_NC_3_amended_reject : (∀ st', ¬ NewMutexAmOk KM L0 [] rc2 [] 0 3 st') ∧
    NewMutexOk KM L0 [] rc2 [] 0 3 (rc2, regX) ∧ ¬ NewMutexRight L0 rc2 0 3 := by
  have hc : ¬ NewMutexRight L0 rc2 0 3 := by decide
  exact ⟨fun _ h => hc h.2, W_NC_3_ok.1, hc⟩

/-- `corpus-spec2-m3.md` v12 §2 undecies, twin of W-NC: step 3 of block MX, `c0 (f0) :
newMutex(guarded)`, is `ok` under the amended form (`root_M` has effective `Modify` on `lock`). -/
theorem W_NC_twin_amended_ok : NewMutexAmOk KM L0 [] x2 [] 0 3 (x2, regX) :=
  ⟨mx_steps.2.2.1, by decide⟩

/-- W-NC is a `Run7` from the initial state and no final amended execution: trace step 4 (step 3
of the corpus) is the `newMutex` without effective `Modify` on the controller. -/
theorem W_NC_not_amendedF : Run7 KM L0 ncσ ncLbls ∧ ¬ RunAmF KM L0 ncσ ncLbls := by
  refine ⟨run7_of_run6_init (ddKC [2]) mxst_ok W_NC_run.1 W_NC_run.2.2, fun h => ?_⟩
  have := h.2 4 (by decide)
  revert this
  decide

end Ern.Concurrency.MutexReal.FinalWitness
