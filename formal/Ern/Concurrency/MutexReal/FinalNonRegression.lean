import Ern.Concurrency.MutexReal.FinalWitness
import Ern.Concurrency.MutexReal.NonRegression
import Ern.Concurrency.MutexReal.ResetAmend
import Ern.Concurrency.Corpus.GuardedStore
import Ern.Concurrency.EncapTraces
import Ern.Concurrency.Corpus.Witness

/-!
# Non-regression under the final wording

Brief of milestone 4, slice 2, layer R, final pass, task 3 (`corpus-spec2-m3.md` v12 §2 undecies,
"Non-régression"):

* the `Run6` traces of the repository are `Run7` traces by the inclusion of task 1 from the
  initial state (`run7_of_run6_init`), not replayed step by step;
* every `newMutex` step of the existing traces satisfies the clause of the proposed C13 item 11
  (`newMutex_steps_C13_11`, one conjunct per distinct step);
* every `Run6` trace of the repository other than W-RC and W-NC, in particular the amended
  executions W-RL and W-RL-J (`amended_runs`), is a final amended execution (`runAmF_traces`).
-/

set_option autoImplicit false

namespace Ern.Concurrency.MutexReal.FinalNonRegression

open Ern.MemoryModel Ern.MemoryModel.Access Ern.Concurrency Ern.Concurrency.MutexReal
open Ern.Concurrency.Corpus Ern.Concurrency.Corpus.HandoffEvents Ern.Concurrency.Corpus.MutexEdge
open Ern.Concurrency.Corpus.ResetLockRight Ern.Concurrency.MutexReal.ClassifyWitness
open Ern.Concurrency.MutexReal.NonRegression
open Ern.Concurrency.MutexReal.Witness (s11σ s11Lbls)
open Ern.Concurrency.Corpus.GuardedChainC (lcLbls)
open Ern.Concurrency.Corpus.GuardedChain (gc4 zst_ok)
open Ern.Concurrency.Corpus.GuardedStore (gs2)
open Ern.Concurrency.EncapTraces (e2 z0 u0 m0)
open Ern.Concurrency.Traces (L0)

/-! ## `Run6` traces are `Run7` traces -/

/-- Brief, final pass, task 3: the `Run6` traces of the repository (`NonRegression`) are `Run7`
traces, by `run7_of_run6_init` from their initial states (S13, S14 of `corpus-spec2-m3.md` §1 for
W-HO; block MX; the state of W-GC for `lc_trace` and W-GS; block AR for S3). The twins of the
counter-examples and W-NC are in `FinalWitness` (`twins_run7`, `W_NC_not_amendedF`). -/
theorem run6_traces_run7 :
    Run7 KF L0 hoσ hoLbls ∧ Run7 KF L0 ho2σ ho2Lbls ∧ Run7 KF L0 ho3σ ho3Lbls ∧
    Run7 KF L0 hojσ hojLbls ∧ Run7 KF L0 ho3jσ ho3jLbls ∧ Run7 KM L0 lcσ lcLbls ∧
    Run7 KM L0 rl0σ rl0Lbls ∧ Run7 KM L0 rlσ rlLbls ∧ Run7 KM L0 rljσ rljLbls ∧
    Run7 KM L0 trσ trLbls ∧ Run7 KM L0 trjσ trjLbls ∧ Run7 KM L0 rcσ rcLbls ∧
    Run7 KM L0 s11σ s11Lbls ∧ Run7 KM L0 cvσ cvLbls ∧ Run7 KM L0 ceσ ceLbls ∧
    Run7 KM L0 crσ crLbls ∧ Run7 KM L0 gsTwinσ gsTwinLbls ∧ Run7 KA L0 s3σ s3Lbls ∧
    Run7 KM L0 s10σ s10Lbls := by
  have hx : StaticsOK xst := by decide
  have hy : StaticsOK yst := by decide
  exact ⟨run7_of_run6_init (ddKC []) hx W_HO_run.1 W_HO_run6,
    run7_of_run6_init (ddKC []) hy W_HO2_run.1 W_HO2_run6,
    run7_of_run6_init (ddKC []) hy W_HO3_run.1 W_HO3_run6,
    run7_of_run6_init (ddKC []) hx W_HOJ_run.1 W_HOJ_run6,
    run7_of_run6_init (ddKC []) hy W_HO3J_run.1 W_HO3J_run6,
    run7_of_run6_init (ddKC [2]) zst_ok lc_run.1 lc_run6,
    run7_of_run6_init (ddKC [2]) mxst_ok W_RL0_run.1 W_RL0_run6,
    run7_of_run6_init (ddKC [2]) mxst_ok W_RL_run.1 W_RL_run6,
    run7_of_run6_init (ddKC [2]) mxst_ok W_RLJ_run.1 W_RLJ_run6,
    run7_of_run6_init (ddKC [2]) mxst_ok W_TR_run.1 W_TR_run6,
    run7_of_run6_init (ddKC [2]) mxst_ok W_TRJ_run.1 W_TRJ_run6,
    run7_of_run6_init (ddKC [2]) mxst_ok W_RC_run.1 W_RC_run6,
    run7_of_run6_init (ddKC [2]) mxst_ok rfl s11_run6,
    run7_of_run6_init (ddKC [2]) mxst_ok spawnVal_moves.1 spawnVal_moves_run6,
    run7_of_run6_init (ddKC [2]) mxst_ok endUse_ends.1 endUse_ends_run6,
    run7_of_run6_init (ddKC [2]) mxst_ok release_ends.1 release_ends_run6,
    run7_of_run6_init (ddKC [2]) zst_ok gs_twin_run6.1 gs_twin_run6.2,
    run7_of_run6_init (ddKC [2]) arst_ok s3_run6.1 s3_run6.2,
    run7_of_run6_init (ddKC [2]) mxst_ok s10_run6.1 s10_run6.2⟩

/-! ## `newMutex` steps -/

/-- Brief, final pass, task 3; `corpus-spec2-m3.md` v12 §2 undecies: every `newMutex` step of the
existing traces satisfies the clause of the proposed C13 item 11 (it reads the state, the context
and `guarded`, not the registry). One conjunct per distinct step, layout `L0`:
block MX, `newMutex(3)` from `x2` (all traces from `MX₃`); block AR, `newMutex(5)` from `a4`;
W-GC and `lc_trace`, `newMutex(4)` from `gc4`; W-GS, `newMutex(3)` from `gs2`; S9, `newMutex(4)`
and `newMutex(5)` from `n4`; W-C22.3b, `newMutex(1)` from `w0`; the traces of WC4
(`EncapTraces`): `newMutex(4)` from `e2`, `newMutex(1)` from `z0`, `newMutex(2)` and
`newMutex(3)` from `u0`, `newMutex(1)` from `m0`. W-NC step 3 (`rc2`) is the exception
(`W_NC_3_amended_reject`). -/
theorem newMutex_steps_C13_11 :
    NewMutexRight L0 x2 0 3 ∧ NewMutexRight L0 a4 0 5 ∧ NewMutexRight L0 gc4 0 4 ∧
    NewMutexRight L0 gs2 0 3 ∧ NewMutexRight L0 n4 0 4 ∧ NewMutexRight L0 n4 0 5 ∧
    NewMutexRight L0 w0 0 1 ∧ NewMutexRight L0 e2 0 4 ∧ NewMutexRight L0 z0 0 1 ∧
    NewMutexRight L0 u0 0 2 ∧ NewMutexRight L0 u0 0 3 ∧ NewMutexRight L0 m0 0 1 := by
  decide

/-! ## Final amended executions -/

/-- Brief, final pass, task 3: every `Run6` trace of the repository other than W-RC (whose
`resetLock` has no controller-access right, `amended_runs`) and W-NC (`W_NC_not_amendedF`) is a
final amended execution; in particular the amended executions W-RL and W-RL-J (`amended_runs`)
stay amended under the final wording. The clauses of the proposed C18 item 4 and C13 item 11 are
checked by `decide` at each step. -/
theorem runAmF_traces :
    RunAmF KF L0 hoσ hoLbls ∧ RunAmF KF L0 ho2σ ho2Lbls ∧ RunAmF KF L0 ho3σ ho3Lbls ∧
    RunAmF KF L0 hojσ hojLbls ∧ RunAmF KF L0 ho3jσ ho3jLbls ∧ RunAmF KM L0 lcσ lcLbls ∧
    RunAmF KM L0 rl0σ rl0Lbls ∧ RunAmF KM L0 rlσ rlLbls ∧ RunAmF KM L0 rljσ rljLbls ∧
    RunAmF KM L0 trσ trLbls ∧ RunAmF KM L0 trjσ trjLbls ∧ RunAmF KM L0 s11σ s11Lbls ∧
    RunAmF KM L0 cvσ cvLbls ∧ RunAmF KM L0 ceσ ceLbls ∧ RunAmF KM L0 crσ crLbls ∧
    RunAmF KM L0 gsTwinσ gsTwinLbls ∧ RunAmF KA L0 s3σ s3Lbls ∧ RunAmF KM L0 s10σ s10Lbls := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, -, h13, h14, h15, h16, h17, h18, h19⟩ :=
    run6_traces_run7
  exact ⟨⟨h1, by decide⟩, ⟨h2, by decide⟩, ⟨h3, by decide⟩, ⟨h4, by decide⟩, ⟨h5, by decide⟩,
    ⟨h6, by decide⟩, ⟨h7, by decide⟩, ⟨h8, by decide⟩, ⟨h9, by decide⟩, ⟨h10, by decide⟩,
    ⟨h11, by decide⟩, ⟨h13, by decide⟩, ⟨h14, by decide⟩, ⟨h15, by decide⟩, ⟨h16, by decide⟩,
    ⟨h17, by decide⟩, ⟨h18, by decide⟩, ⟨h19, by decide⟩⟩

/-- The twins of the counter-examples are final amended executions. -/
theorem twins_runAmF : RunAmF KM L0 AmendWitness.tsσ AmendWitness.tsLbls ∧
    RunAmF KA L0 AmendWitness.tiσ AmendWitness.tiLbls ∧
    RunAmF KM L0 AmendWitness.taσ AmendWitness.taLbls ∧
    RunAmF KM L0 AmendWitness.tdtσ AmendWitness.tdtLbls := by
  obtain ⟨h1, h2, h3, h4⟩ := FinalWitness.twins_run7
  exact ⟨⟨h1, by decide⟩, ⟨h2, by decide⟩, ⟨h3, by decide⟩, ⟨h4, by decide⟩⟩

end Ern.Concurrency.MutexReal.FinalNonRegression
