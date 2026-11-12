import Ern.Concurrency.MutexReal.AmendWitness
import Ern.Concurrency.Corpus.HandoffEvents
import Ern.Concurrency.Corpus.ResetLockRight
import Ern.Concurrency.Corpus.PlaceExclWitness
import Ern.Concurrency.MutexReal.Witness

/-!
# Non-regression under the proposed C22 item 4

Brief of milestone 4, slice 2, layer R, corrective pass, task 3 (`corpus-spec2-m3.md` v11 §2
decies, "Non-régression"): every `Run5R` trace of the repository other than the three
counter-examples of the classification is a `Run6`, by `decide` on the restriction of the
controller at each step. The traces that the corpus names and that the repository has only as
`EncapsulatedTrace5R` (the twin of W-GS, S3 up to `issue`, S10) are restated with named states and
checked the same way.
-/

set_option autoImplicit false

namespace Ern.Concurrency.MutexReal.NonRegression

open Ern.MemoryModel Ern.MemoryModel.Access Ern.Concurrency Ern.Concurrency.MutexReal
open Ern.Concurrency.Corpus Ern.Concurrency.Corpus.HandoffEvents Ern.Concurrency.Corpus.MutexEdge
open Ern.Concurrency.Corpus.ResetLockRight Ern.Concurrency.MutexReal.ClassifyWitness
open Ern.Concurrency.MutexReal.Witness (s11σ s11Lbls s11_abandoned)
open Ern.Concurrency.Corpus.GuardedChainC (lcLbls)
open Ern.Concurrency.Traces (L0)

/-! ## The `Run5R` traces of the repository -/

/-- W-HO (`corpus-spec2-m3.md` §2 bis) is a `Run6`. -/
theorem W_HO_run6 : Run6 KF L0 hoσ hoLbls := run6_of_run5R W_HO_run.2 (by decide)
/-- W-HO′ is a `Run6`. -/
theorem W_HO2_run6 : Run6 KF L0 ho2σ ho2Lbls := run6_of_run5R W_HO2_run.2 (by decide)
/-- W-HO″ is a `Run6`. -/
theorem W_HO3_run6 : Run6 KF L0 ho3σ ho3Lbls := run6_of_run5R W_HO3_run.2 (by decide)
/-- W-HO-J (§2 septies) is a `Run6`. -/
theorem W_HOJ_run6 : Run6 KF L0 hojσ hojLbls := run6_of_run5R W_HOJ_run.2 (by decide)
/-- W-HO″-J is a `Run6`. -/
theorem W_HO3J_run6 : Run6 KF L0 ho3jσ ho3jLbls := run6_of_run5R W_HO3J_run.2 (by decide)
/-- `lc_trace` (§2 septies) is a `Run6`. -/
theorem lc_run6 : Run6 KM L0 lcσ lcLbls := run6_of_run5R lc_run.2 (by decide)
/-- W-RL₀ (§2 octies) is a `Run6`. -/
theorem W_RL0_run6 : Run6 KM L0 rl0σ rl0Lbls := run6_of_run5R W_RL0_run.2 (by decide)
/-- W-RL is a `Run6`. -/
theorem W_RL_run6 : Run6 KM L0 rlσ rlLbls := run6_of_run5R W_RL_run.2 (by decide)
/-- W-RL-J is a `Run6`. -/
theorem W_RLJ_run6 : Run6 KM L0 rljσ rljLbls := run6_of_run5R W_RLJ_run.2 (by decide)
/-- W-TR is a `Run6`: its `transfer(M, M′)` is a move admitted by C22 item 3. -/
theorem W_TR_run6 : Run6 KM L0 trσ trLbls := run6_of_run5R W_TR_run.2 (by decide)
/-- W-TR-J is a `Run6`. -/
theorem W_TRJ_run6 : Run6 KM L0 trjσ trjLbls := run6_of_run5R W_TRJ_run.2 (by decide)
/-- W-RC (§2 nonies) is a `Run6`: its `resetLock` is a protocol step of the entry. -/
theorem W_RC_run6 : Run6 KM L0 rcσ rcLbls := run6_of_run5R W_RC_run.2 (by decide)
/-- S11 with its abandoned grant is a `Run6`. -/
theorem s11_run6 : Run6 KM L0 s11σ s11Lbls := run6_of_run5R s11_abandoned.1 (by decide)
/-- The by-value `spawn` moving the mutex (`spawnVal_moves`) is a `Run6`: a move admitted by C22
item 3. -/
theorem spawnVal_moves_run6 : Run6 KM L0 cvσ cvLbls :=
  run6_of_run5R spawnVal_moves.2.1 (by decide)
/-- `endUse(M)` (`endUse_ends`) is a `Run6`: the entry is dead after the step. -/
theorem endUse_ends_run6 : Run6 KM L0 ceσ ceLbls := run6_of_run5R endUse_ends.2.1 (by decide)
/-- `release(guarded)` (`release_ends`) is a `Run6`. -/
theorem release_ends_run6 : Run6 KM L0 crσ crLbls := run6_of_run5R release_ends.2.1 (by decide)

/-! ## Traces named by the corpus, restated with named states -/

section GS

open Ern.Concurrency.Corpus.GuardedStore

/-- The named states of the twin of W-GS (`W_GS_twin_trace5R`). -/
def gsTwinσ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(gs0, [], []), (gs1, [], []), (gs2, [], []), (gs2, sreg, []), (gs3, sreg, []), (gs4, sreg, []),
    (gs5, sreg, []), (gt6, sregG, []), (gt7, sregG, []),
    (Ern.Concurrency.Corpus.PlaceExclWitness.gt8, sreg, [])].getD i
    (Ern.Concurrency.Corpus.PlaceExclWitness.gt8, sreg, [])

/-- The labels of the twin of W-GS. -/
def gsTwinLbls : List Label := setupLbls ++ [.acquire 0 0] ++ [.kernel 0 (.store 4 3)] ++
  [.unlock 0 0]

/-- `corpus-spec2-m3.md` v6 §2 sexies, twin of W-GS (`acquire(e)`, `store(z2, T)` under the grant,
`unlock(e)`), restated with named states, is a `Run6` from the initial state. -/
theorem gs_twin_run6 : gsTwinσ 0 = (gs0, [], []) ∧ Run6 KM L0 gsTwinσ gsTwinLbls := by
  have h : Steps5R KM L0 [(gs0, [], []), (gs1, [], []), (gs2, [], []), (gs2, sreg, []),
      (gs3, sreg, []), (gs4, sreg, []), (gs5, sreg, []), (gt6, sregG, []), (gt7, sregG, []),
      (Ern.Concurrency.Corpus.PlaceExclWitness.gt8, sreg, [])] gsTwinLbls :=
    .cons ⟨⟨(fun e he => by cases he), by decide, trivial⟩, trivial⟩
      (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, by decide⟩ (.kernel ⟨by decide, .ok (by decide)⟩) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, trivial⟩ (.newMutex ⟨by decide, by decide, rfl⟩) <|
    .cons ⟨⟨(by decide : ∀ e ∈ sreg, e.Live gs2 → 2 ≠ e.guarded), by decide, trivial⟩, trivial⟩
      (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons ⟨⟨(by decide : ∀ e ∈ sreg, e.Live gs3 → 0 ≠ e.guarded), by decide, trivial⟩, trivial⟩
      (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, trivial⟩ (.spawn ⟨by decide, .ok (by decide)⟩) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, by decide⟩ (.acquire W_GS_twin_ok.1) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, by decide⟩ (.kernel W_GS_twin_ok.2) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, trivial⟩
      (.unlock ⟨by decide, ⟨3, some 6⟩, 6, rfl, by decide, rfl, by decide, by decide, rfl⟩) .nil
  exact ⟨rfl, run6_of_run5R (h.run _) (by decide)⟩

end GS

/-- The named states of S3 up to `issue` (`s3_trace5R`). -/
def s3σ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(a0, [], []), (a1, [], []), (a2, [], []), (a2, [], arA), (a3, [], arA), (a4, [], arA),
    (a4, regA, arA), (a5, regA, arA), (a6, regA, arA), (a7, regA8, arA),
    (a8, regA8, arA1)].getD i (a8, regA8, arA1)

/-- The labels of S3 up to `issue`. -/
def s3Lbls : List Label :=
  [.kernel 0 (.derive 2 [5, 6] .modify), .kernel 0 (.store 4 3), .newArena 0 4 4,
   .kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 5 1), .newMutex 0 5,
   .kernel 0 (.derive 0 [1, 2] .observe), .spawn 0 [6] [(none, 0)], .acquire 1 0,
   .issue 1 0 [5] 8]

/-- `corpus-spec2-m3.md` §1 S3 up to step 3, the arena administered through the mutex grant,
restated with named states, is a `Run6` from the initial state. -/
theorem s3_run6 : s3σ 0 = (SC.ofS3 (S3.init arst), [], []) ∧ Run6 KA L0 s3σ s3Lbls := by
  have hn : NewMutexOk KA L0 arA a4 [] 0 5 (a4, regA) := ⟨by decide, by decide, rfl⟩
  have ha : NewArenaStepC a2 [] [] 0 4 4 (.ok (a2, arA)) := ⟨by decide, .ok (by decide)⟩
  have h : Steps5R KA L0 [(a0, [], []), (a1, [], []), (a2, [], []), (a2, [], arA), (a3, [], arA),
      (a4, [], arA), (a4, regA, arA), (a5, regA, arA), (a6, regA, arA), (a7, regA8, arA),
      (a8, regA8, arA1)] s3Lbls :=
    .cons ⟨⟨(fun e he => by cases he), by decide, trivial⟩, trivial⟩
      (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, by decide⟩ (.kernel ⟨by decide, .ok (by decide)⟩) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, trivial⟩ (.newArena ha) <|
    .cons ⟨⟨(fun e he => by cases he), by decide, trivial⟩, trivial⟩
      (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, by decide⟩ (.kernel ⟨by decide, .ok (by decide)⟩) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, trivial⟩ (.newMutex hn) <|
    .cons ⟨⟨(by decide : ∀ e ∈ regA, e.Live a4 → 0 ≠ e.guarded), by decide, trivial⟩, trivial⟩
      (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, trivial⟩ (.spawn ⟨by decide, .ok (by decide)⟩) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, by decide⟩ (.acquire S3_2_ok) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, by decide⟩ (.issue S3_3_ok) .nil
  exact ⟨rfl, run6_of_run5R (h.run _) (by decide)⟩

/-- The named states of S10 (`s10_trace5R`). -/
def s10σ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(x0, [], []), (x1, [], []), (x2, [], []), (x2, regX, []), (r1, [⟨3, some 4⟩], []),
    (r2, [⟨3, some 4⟩], []), (r3, [⟨3, some 4⟩], []), (r4, [⟨3, some 4⟩], []),
    (r5, [⟨3, some 4⟩], [])].getD i (r5, [⟨3, some 4⟩], [])

/-- The labels of S10. -/
def s10Lbls : List Label :=
  [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 3 1), .newMutex 0 3, .acquire 0 0,
   .kernel 0 (.derive 0 [1, 2] .modify),
   .kernel 0 (.enter [5] [(none, 0), (some 7, 0), (some 7, 0)]),
   .kernel 0 (.transfer 0 7), .kernel 0 (.transfer 7 0)]

/-- `corpus-spec2-m3.md` §1 S10, the whole mutex moved and moved back while its grant is active,
restated with named states, is a `Run6` from the initial state: both transfers are moves admitted
by C22 item 3. -/
theorem s10_run6 : s10σ 0 = (SC.ofS3 (S3.init mxst), [], []) ∧ Run6 KM L0 s10σ s10Lbls := by
  have h : Steps5R KM L0 [(x0, [], []), (x1, [], []), (x2, [], []), (x2, regX, []),
      (r1, [⟨3, some 4⟩], []), (r2, [⟨3, some 4⟩], []), (r3, [⟨3, some 4⟩], []),
      (r4, [⟨3, some 4⟩], []), (r5, [⟨3, some 4⟩], [])] s10Lbls :=
    .cons ⟨⟨(fun e he => by cases he), by decide, trivial⟩, trivial⟩ (.kernel mx_steps.1) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, by decide⟩ (.kernel mx_steps.2.1) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, trivial⟩ (.newMutex mx_steps.2.2.1) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, by decide⟩ (.acquire s10_setup.1) <|
    .cons ⟨⟨(by decide : ∀ e ∈ ([⟨3, some 4⟩] : SyncReg), e.Live r1 → 0 ≠ e.guarded), by decide,
        trivial⟩, trivial⟩ (.kernel s10_setup.2.1) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, trivial⟩ (.kernel s10_setup.2.2) <|
    .cons ⟨⟨S10_1_ok.2.1, trivial, trivial⟩, by decide⟩ (.kernel S10_1_ok.1) <|
    .cons ⟨⟨S10_2_ok.2, trivial, trivial⟩, by decide⟩ (.kernel S10_2_ok.1) .nil
  exact ⟨rfl, run6_of_run5R (h.run _) (by decide)⟩

end Ern.Concurrency.MutexReal.NonRegression
