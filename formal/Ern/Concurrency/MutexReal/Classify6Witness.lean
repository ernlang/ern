import Ern.Concurrency.MutexReal.Classify6
import Ern.Concurrency.MutexReal.NonRegression

/-!
# Witnesses of the replayed classification

Brief of milestone 4, slice 2, layer R, corrective pass, task 4: the statuses `déplacement` and
`fin de vie` are existential; their witnesses of the previous pass are `Run6` traces
(`Ern.Concurrency.MutexReal.NonRegression`). `completeness6_run` is instantiated on `lc_trace`.
-/

set_option autoImplicit false

namespace Ern.Concurrency.MutexReal.Classify6Witness

open Ern.MemoryModel.Access Ern.Concurrency Ern.Concurrency.MutexReal
open Ern.Concurrency.Corpus Ern.Concurrency.Corpus.MutexEdge
open Ern.Concurrency.MutexReal.ClassifyWitness Ern.Concurrency.MutexReal.NonRegression
open Ern.Concurrency.Corpus.HandoffEvents (lcσ lc_run)
open Ern.Concurrency.Corpus.GuardedChainC (lcLbls)
open Ern.Concurrency.Traces (L0)

/-- Brief, corrective pass, task 4, status `déplacement` on `Run6`: W-TR is a `Run6` whose step 9,
`transfer(M, M′)`, keeps entry `e` live and moves its controller from `lock` to `lock′`; the
by-value `spawn` of `spawnVal_moves` is a `Run6` whose step moves the controller from `lock` to the
child's place 9. -/
theorem moves_run6 : Run6 KM L0 trσ trLbls ∧ ControlOf L0 (trσ 9).1 ⟨3, none⟩ = some 2 ∧
    ControlOf L0 (trσ 10).1 ⟨3, none⟩ = some 6 ∧ (⟨3, none⟩ : SyncEntry).Live (trσ 10).1 ∧
    Run6 KM L0 cvσ cvLbls ∧ ControlOf L0 (cvσ 3).1 ⟨3, none⟩ = some 2 ∧
    ControlOf L0 (cvσ 4).1 ⟨3, none⟩ = some 9 ∧ (⟨3, none⟩ : SyncEntry).Live (cvσ 4).1 :=
  ⟨W_TR_run6, by decide, by decide, by decide, spawnVal_moves_run6, by decide, by decide,
    by decide⟩

/-- Brief, corrective pass, task 4, status `fin de vie` on `Run6`: `endUse(M)` touches `lock` in its
enlarged footprint and ends entry `e`; `release(guarded)` ends it; both traces are `Run6`. -/
theorem ends_run6 : Run6 KM L0 ceσ ceLbls ∧ TouchesX L0 (ceσ 3) (.kernel 0 (.endUse 0)) 2 ∧
    ¬ (⟨3, none⟩ : SyncEntry).Live (ceσ 4).1 ∧ Run6 KM L0 crσ crLbls ∧
    ¬ (⟨3, none⟩ : SyncEntry).Live (crσ 4).1 :=
  ⟨endUse_ends_run6, by decide, by decide, release_ends_run6, by decide⟩

/-- `completeness6_run` on `lc_trace`: its `Run6` (`lc_run6`), hypothesis 3 (`lc_bridge`), and the
`unlock(e)` of step 9, which touches `lock`, give the event 2 of the controller graph. -/
theorem lc_complete6 : ∃ c op, ctlOp 0 lcLbls[9] = some (c, op) ∧
    (ctlGraph refOrds 0 lcLbls).ev? (ctlIdx 0 lcLbls 9) = some ⟨c, op.kind refOrds⟩ :=
  completeness6_run (ddKC [2]) Ern.Concurrency.Corpus.GuardedChain.zst_ok lc_run.1 lc_run6
    Ern.Concurrency.MutexReal.Witness.lc_bridge.1 (i := 9) (by decide) (x := ⟨4, some 6⟩) rfl
    (by decide) (by decide) (ctl := 2) (by decide) (by decide) refOrds

end Ern.Concurrency.MutexReal.Classify6Witness
