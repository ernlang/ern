import Ern.Concurrency.MutexReal.Classify7
import Ern.Concurrency.MutexReal.Classify6Witness
import Ern.Concurrency.MutexReal.FinalNonRegression

/-!
# Witnesses of the classification under the final footprint

Brief of milestone 4, slice 2, layer R, final pass, task 4: the statuses `déplacement` and
`fin de vie` on `Run7` traces; `completeness7_run` instantiated on `lc_trace`; the footprint gap
on `alloc(provider = slot, owner = M)`.
-/

set_option autoImplicit false

namespace Ern.Concurrency.MutexReal.Classify7Witness

open Ern.MemoryModel Ern.MemoryModel.Access Ern.Concurrency Ern.Concurrency.MutexReal
open Ern.Concurrency.Corpus Ern.Concurrency.Corpus.MutexEdge
open Ern.Concurrency.MutexReal.ClassifyWitness Ern.Concurrency.MutexReal.AmendWitness
open Ern.Concurrency.MutexReal.FinalNonRegression (run6_traces_run7)
open Ern.Concurrency.Corpus.HandoffEvents (lcσ)
open Ern.Concurrency.Corpus.GuardedChainC (lcLbls)
open Ern.Concurrency.Traces (L0)

/-- Brief, final pass, task 4, status `déplacement` on `Run7`: W-TR is a `Run7` whose step 9,
`transfer(M, M′)`, keeps entry `e` live and moves its controller from `lock` to `lock′`; the
by-value `spawn` of `spawnVal_moves` is a `Run7` whose step moves the controller from `lock` to
the child's place 9. -/
theorem moves_run7 : Run7 KM L0 trσ trLbls ∧ ControlOf L0 (trσ 9).1 ⟨3, none⟩ = some 2 ∧
    ControlOf L0 (trσ 10).1 ⟨3, none⟩ = some 6 ∧ (⟨3, none⟩ : SyncEntry).Live (trσ 10).1 ∧
    Run7 KM L0 cvσ cvLbls ∧ ControlOf L0 (cvσ 3).1 ⟨3, none⟩ = some 2 ∧
    ControlOf L0 (cvσ 4).1 ⟨3, none⟩ = some 9 ∧ (⟨3, none⟩ : SyncEntry).Live (cvσ 4).1 :=
  ⟨run6_traces_run7.2.2.2.2.2.2.2.2.2.1, by decide, by decide, by decide,
    run6_traces_run7.2.2.2.2.2.2.2.2.2.2.2.2.2.1, by decide, by decide, by decide⟩

/-- Brief, final pass, task 4, status `fin de vie` on `Run7`: `endUse(M)` has `lock` in its final
footprint and ends entry `e`; `release(guarded)` ends it; both traces are `Run7`. -/
theorem ends_run7 : Run7 KM L0 ceσ ceLbls ∧ TouchesF L0 (ceσ 3) (.kernel 0 (.endUse 0)) 2 ∧
    ¬ (⟨3, none⟩ : SyncEntry).Live (ceσ 4).1 ∧ Run7 KM L0 crσ crLbls ∧
    ¬ (⟨3, none⟩ : SyncEntry).Live (crσ 4).1 :=
  ⟨run6_traces_run7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, by decide, by decide,
    run6_traces_run7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, by decide⟩

/-- `completeness7_run` on `lc_trace`: its `Run7`, hypothesis 3 (`lc_bridge`), and the `unlock(e)`
of step 9, whose final footprint contains `lock`, give the event 2 of the controller graph. -/
theorem lc_complete7 : ∃ c op, ctlOp 0 lcLbls[9] = some (c, op) ∧
    (ctlGraph refOrds 0 lcLbls).ev? (ctlIdx 0 lcLbls 9) = some ⟨c, op.kind refOrds⟩ :=
  completeness7_run (ddKC [2]) Ern.Concurrency.Corpus.GuardedChain.zst_ok
    Ern.Concurrency.Corpus.HandoffEvents.lc_run.1 run6_traces_run7.2.2.2.2.2.1
    Ern.Concurrency.MutexReal.Witness.lc_bridge.1 (i := 9) (by decide) (x := ⟨4, some 6⟩) rfl
    (by decide) (by decide) (ctl := 2) (by decide) (by decide) refOrds

/-! ## The footprint gap -/

/-- Brief, final pass, task 4, "Écart d'empreinte", on `c0 : alloc(provider = slot, owner = M)`
from `MX₃`: `lock` (place 2), a leaf of the owner `M`, is in `Touches` and not in the final
footprint; `M` (place 0), no leaf, is in the final footprint and not in `Touches`. The step changes
neither the initialization state of `lock` (`Init` before and after), nor its holder relations
(no authority is held by `lock`, and no place is owned by `lock`, after the step; the new root
authority, of index 4, is held by `M`, its new root place 7 owned by `M`; the place record of
`lock` is unchanged), nor `ControlOf(e)`, which stays `lock`. Contrast with `alloc_cex`, where
`lock` becomes the holder of the new root. -/
theorem alloc_owner_M_gap :
    Touches L0 (x2, regX, []) (.kernel 0 (.alloc 1 0 [(none, 0)])) 2 ∧
    ¬ TouchesF L0 (x2, regX, []) (.kernel 0 (.alloc 1 0 [(none, 0)])) 2 ∧
    TouchesF L0 (x2, regX, []) (.kernel 0 (.alloc 1 0 [(none, 0)])) 0 ∧
    ¬ Touches L0 (x2, regX, []) (.kernel 0 (.alloc 1 0 [(none, 0)])) 0 ∧
    x2.I 2 = .init ∧ tam1.I 2 = .init ∧
    (∀ a ∈ List.range tam1.A.length, (tam1.A[a]?).map (·.holder) ≠ some (.place 2)) ∧
    (∀ q ∈ List.range tam1.P.length, (tam1.P[q]?).map (·.owner) ≠ some (.place 2)) ∧
    (tam1.A[4]?).map (·.holder) = some (.place 0) ∧ (tam1.P[7]?).map (·.owner) = some (.place 0) ∧
    tam1.P[2]? = x2.P[2]? ∧
    ControlOf L0 x2 ⟨3, none⟩ = some 2 ∧ ControlOf L0 tam1 ⟨3, none⟩ = some 2 := by
  decide

end Ern.Concurrency.MutexReal.Classify7Witness
