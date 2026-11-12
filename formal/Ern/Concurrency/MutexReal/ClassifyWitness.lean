import Ern.Concurrency.MutexReal.Classify
import Ern.Concurrency.Corpus.MutexEdge
import Ern.Concurrency.Corpus.AR

/-!
# Witnesses of the classification

Brief of milestone 4, slice 2, layer R, task 4 (`formal/reports/spec2-m4-mutexreal.md`): the traces
behind the statuses `contre-exemple` (`store`, `alloc`, `issue`), `déplacement` (`transfer`,
by-value `spawn`) and `fin de vie` (`endUse`, `release`), each a `Run5R` from the initial state of
Spec 1 §47, checked by `decide`. Block MX and block AR of `corpus-spec2-m3.md` §0; contracts `KM`
and `KA`.
-/

set_option autoImplicit false

namespace Ern.Concurrency.MutexReal.ClassifyWitness

open Ern.MemoryModel Ern.MemoryModel.Access Ern.Concurrency Ern.Concurrency.MutexReal
open Ern.Concurrency.Corpus
open Ern.Concurrency.Traces (L0)

/-- The labels of block MX up to `MX₃` (`corpus-spec2-m3.md` §0). -/
def mx3Lbls : List Label :=
  [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 3 1), .newMutex 0 3]

/-- The setup of `MX₃` from the initial state, each step admitted by `Encap5R`, followed by any run
from `MX₃`. -/
theorem mx3_steps {sts : List (SC × SyncReg × ArenaReg)} {lbls : List Label}
    (h : Steps5R KM L0 ((x2, regX, []) :: sts) lbls) :
    Steps5R KM L0 ((x0, [], []) :: (x1, [], []) :: (x2, [], []) :: (x2, regX, []) :: sts)
      (mx3Lbls ++ lbls) :=
  .cons ⟨⟨(fun e he => by cases he), by decide, trivial⟩, trivial⟩ (.kernel mx_steps.1) <|
  .cons ⟨⟨trivial, trivial, trivial⟩, by decide⟩ (.kernel mx_steps.2.1) <|
  .cons ⟨⟨trivial, trivial, trivial⟩, trivial⟩ (.newMutex mx_steps.2.2.1) h

/-! ## `store`: counter-example -/

/-- `c0 : z := derive(root_M′, Observe, {slot′})`, authority 4 (O1). -/
def cs1 : SC := x2.set (deriveEff (x2.view 0) 2 [5] .observe)
/-- `c0 : store(z, lock)` (O8). -/
def cs2 : SC := storeEffC cs1 0 4 2

/-- The labels of the `store` counter-example. -/
def csLbls : List Label :=
  mx3Lbls ++ [.kernel 0 (.derive 2 [5] .observe), .kernel 0 (.store 4 2)]

/-- The named states of the `store` counter-example. -/
def csσ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(x0, [], []), (x1, [], []), (x2, [], []), (x2, regX, []), (cs1, regX, []),
    (cs2, regX, [])].getD i (cs2, regX, [])

/-- Brief, task 4, `store`, status `contre-exemple`: from `MX₃`, `c0 : z := derive(root_M′, Observe,
{slot′})` then `c0 : store(z, lock)` form a `Run5R` from the initial state. Entry `e` is live
before and after the `store`, its controller is `lock` (place 2) in both states; the `store`
writes `lock` (Spec 1 §59, `KernelOp.Writes`) and makes it the holder of `z`; it is not a protocol
step on `e`, so it is no event of the controller graph. No conjunct of `Encap5R` reads the target
of a `store` other than its right premises (`PlaceExcl`), which `root_M` satisfies. -/
theorem store_cex : csσ 0 = (SC.ofS3 (S3.init mxst), [], []) ∧ Run5R KM L0 csσ csLbls ∧
    csLbls[4]? = some (.kernel 0 (.store 4 2)) ∧
    (⟨3, none⟩ : SyncEntry).Live cs1 ∧ (⟨3, none⟩ : SyncEntry).Live cs2 ∧
    ControlOf L0 cs1 ⟨3, none⟩ = some 2 ∧ ControlOf L0 cs2 ⟨3, none⟩ = some 2 ∧
    Touches L0 (cs1, regX, []) (.kernel 0 (.store 4 2)) 2 ∧
    KernelOp.Writes cs1.flat 2 (.store 4 2) ∧ (cs2.A[4]?).map (·.holder) = some (.place 2) ∧
    ctlOp 0 (.kernel 0 (.store 4 2)) = none := by
  have h : Steps5R KM L0 [(x2, regX, []), (cs1, regX, []), (cs2, regX, [])]
      [.kernel 0 (.derive 2 [5] .observe), .kernel 0 (.store 4 2)] :=
    .cons ⟨⟨(by decide : ∀ e ∈ regX, e.Live x2 → 2 ≠ e.guarded), by decide, trivial⟩, trivial⟩
      (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, by decide⟩ (.kernel ⟨by decide, .ok (by decide)⟩) .nil
  exact ⟨rfl, (mx3_steps h).run _, rfl, by decide, by decide, by decide, by decide, rfl, rfl,
    by decide, rfl⟩

/-! ## `alloc`: counter-example -/

/-- `c0 : alloc(provider = slot, owner = lock, one leaf)` (O14): the new root authority, 4, is held
by `lock`. -/
def ca1 : SC := x2.set (allocEff (x2.view 0) 2 [(none, 0)])

/-- The labels of the `alloc` counter-example. -/
def caLbls : List Label := mx3Lbls ++ [.kernel 0 (.alloc 1 2 [(none, 0)])]

/-- The named states of the `alloc` counter-example. -/
def caσ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(x0, [], []), (x1, [], []), (x2, [], []), (x2, regX, []), (ca1, regX, [])].getD i
    (ca1, regX, [])

/-- Brief, task 4, `alloc`, status `contre-exemple`: from `MX₃`, `c0 : alloc(provider = slot,
owner = lock)` is an `ok` step admitted by `Encap5R` (its right premises, `PlaceExcl`, hold through
`root_M`); the trace is a `Run5R` from the initial state. Entry `e` stays live with controller
`lock`, which becomes the holder of the new root authority (Spec 1 §71 effect); the step is not a
protocol step on `e`. -/
theorem alloc_cex : caσ 0 = (SC.ofS3 (S3.init mxst), [], []) ∧ Run5R KM L0 caσ caLbls ∧
    caLbls[3]? = some (.kernel 0 (.alloc 1 2 [(none, 0)])) ∧
    (⟨3, none⟩ : SyncEntry).Live x2 ∧ (⟨3, none⟩ : SyncEntry).Live ca1 ∧
    ControlOf L0 x2 ⟨3, none⟩ = some 2 ∧ ControlOf L0 ca1 ⟨3, none⟩ = some 2 ∧
    Touches L0 (x2, regX, []) (.kernel 0 (.alloc 1 2 [(none, 0)])) 2 ∧
    (ca1.A[4]?).map (·.holder) = some (.place 2) ∧
    ctlOp 0 (.kernel 0 (.alloc 1 2 [(none, 0)])) = none := by
  have h : Steps5R KM L0 [(x2, regX, []), (ca1, regX, [])] [.kernel 0 (.alloc 1 2 [(none, 0)])] :=
    .cons ⟨⟨trivial, trivial, trivial⟩, by decide⟩
      (.kernel ⟨by decide, _, .ok (by decide) trivial, rfl⟩) .nil
  exact ⟨rfl, (mx3_steps h).run _, rfl, by decide, by decide, by decide, by decide, by decide,
    by decide, rfl⟩

/-! ## `issue`: counter-example -/

/-- `c0 : acquire(e2)`: grant, authority 6, held by frame 0 (WC5.1 corrigé C16). -/
def ci1 : SC := deriveSyncEff a4 0 5
/-- The registry with the grant recorded. -/
def regI : SyncReg := [⟨5, some 6⟩]
/-- `split(internal, [R1])` by context 0: the block, authority 7 (O2). -/
def ci2s : SC := ci1.set (splitEff (ci1.view 0) 4 [[5]])
/-- `store(block, lock2)` by context 0 (O8). -/
def ci2 : SC := storeEffC ci2s 0 ci1.A.length 2
/-- The arena registry after the issue of `R1` (Spec 1 §77 effect). -/
def arI : ArenaReg := arA.set 0 (Arena.issueMeta ci1.flat ⟨4, 4, [5, 6], []⟩ [5])

/-- The labels of the `issue` counter-example: block AR up to `newMutex(guarded2)`, then
`c0 : acquire(e2)` and `c0 : issue(arena, R1, lock2)`. -/
def ciLbls : List Label :=
  [.kernel 0 (.derive 2 [5, 6] .modify), .kernel 0 (.store 4 3), .newArena 0 4 4,
   .kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 5 1), .newMutex 0 5, .acquire 0 0,
   .issue 0 0 [5] 2]

/-- The named states of the `issue` counter-example. -/
def ciσ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(a0, [], []), (a1, [], []), (a2, [], []), (a2, [], arA), (a3, [], arA), (a4, [], arA),
    (a4, regA, arA), (ci1, regI, arA), (ci2, regI, arI)].getD i (ci2, regI, arI)

/-- Brief, task 4, `issue`, status `contre-exemple`: in block AR before the sharing of `M2`,
`c0 : acquire(e2)` then `c0 : issue(arena, R1, lock2)` are `ok` steps admitted by `Encap5R` (the
`MetaRight` premise of `PlaceExcl` holds through the grant); the trace is a `Run5R` from the initial
state. Entry `e2` stays live with controller `lock2` (place 2), into which the block is stored
(Spec 1 §77, §65); the `issue` is not a protocol step on `e2`. -/
theorem issue_cex : ciσ 0 = (SC.ofS3 (S3.init arst), [], []) ∧ Run5R KA L0 ciσ ciLbls ∧
    ciLbls[7]? = some (.issue 0 0 [5] 2) ∧
    (⟨5, none⟩ : SyncEntry).Live ci1 ∧ (⟨5, none⟩ : SyncEntry).Live ci2 ∧
    ControlOf L0 ci1 ⟨5, none⟩ = some 2 ∧ ControlOf L0 ci2 ⟨5, none⟩ = some 2 ∧
    Touches L0 (ci1, regI, arA) (.issue 0 0 [5] 2) 2 ∧
    (ci2.A[7]?).map (·.holder) = some (.place 2) ∧ ctlOp 0 (.issue 0 0 [5] 2) = none := by
  have h : Steps5R KA L0 [(a0, [], []), (a1, [], []), (a2, [], []), (a2, [], arA), (a3, [], arA),
      (a4, [], arA), (a4, regA, arA), (ci1, regI, arA), (ci2, regI, arI)] ciLbls :=
    .cons ⟨⟨(fun e he => by cases he), by decide, trivial⟩, trivial⟩
      (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, by decide⟩ (.kernel ⟨by decide, .ok (by decide)⟩) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, trivial⟩ (.newArena ⟨by decide, .ok (by decide)⟩) <|
    .cons ⟨⟨(fun e he => by cases he), by decide, trivial⟩, trivial⟩
      (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, by decide⟩ (.kernel ⟨by decide, .ok (by decide)⟩) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, trivial⟩ (.newMutex ⟨by decide, by decide, rfl⟩) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, by decide⟩
      (.acquire ⟨by decide, ⟨5, none⟩, rfl, by decide, by decide, rfl⟩) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, by decide⟩
      (.issue (.ok (E := ⟨4, 4, [5, 6], []⟩) rfl (by decide) (by decide)
        ⟨by decide, _, .ok (by decide), rfl⟩ ⟨by decide, .ok (by decide)⟩)) .nil
  exact ⟨rfl, h.run _, rfl, by decide, by decide, by decide, by decide, rfl, by decide, rfl⟩

/-! ## `déplacement` -/

open Ern.Concurrency.Corpus.MutexEdge in
/-- Brief, task 4, `transfer`, status `déplacement` (`corpus-spec2-m3.md` S7, v9 §2 octies W-TR):
in the `Run5R` W-TR, step 9, `c0 : transfer(M, M′)`, keeps entry `e` live and moves its
controller from `lock` (place 2) to `lock′` (place 6). -/
theorem transfer_moves : Run5R KM L0 trσ trLbls ∧ trLbls[9]? = some (.kernel 0 (.transfer 0 4)) ∧
    (⟨3, none⟩ : SyncEntry).Live (trσ 9).1 ∧ (⟨3, none⟩ : SyncEntry).Live (trσ 10).1 ∧
    ControlOf L0 (trσ 9).1 ⟨3, none⟩ = some 2 ∧ ControlOf L0 (trσ 10).1 ⟨3, none⟩ = some 6 :=
  ⟨W_TR_run.2, rfl, by decide, by decide, by decide, by decide⟩

/-- The locals of the child: a copy of the shape of the mutex value, root `7`, fields `8`, `9`. -/
def mLocals : LocalShape := [(none, 0), (some 7, 0), (some 7, 0)]
/-- `c0 : spawn` by value moving `M` into the root local `7` of the child (WC5.1 corrigé C5). -/
def cv1 : SC := spawnValEff x2 0 [] mLocals [(0, 7)]

/-- The labels of the by-value `spawn` that moves the mutex. -/
def cvLbls : List Label := mx3Lbls ++ [.spawnVal 0 [] mLocals [(0, 7)]]

/-- The named states of the by-value `spawn` that moves the mutex. -/
def cvσ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(x0, [], []), (x1, [], []), (x2, [], []), (x2, regX, []), (cv1, regX, [])].getD i
    (cv1, regX, [])

/-- Brief, task 4, by-value `spawn`, status `déplacement`: from `MX₃`, a by-value `spawn` whose
transfer moves the whole mutex value `M` into a local of the child (WC5.1 corrigé C12, C22 item 3:
the source is neither `slot`, a strict part of `slot`, nor the controller) is an `ok` step admitted
by `Encap5R`; the trace is a `Run5R` from the initial state. Entry `e` stays live and its controller
moves from `lock` (place 2) to the child's place 9; the step touches `lock`. -/
theorem spawnVal_moves : cvσ 0 = (SC.ofS3 (S3.init mxst), [], []) ∧ Run5R KM L0 cvσ cvLbls ∧
    (⟨3, none⟩ : SyncEntry).Live x2 ∧ (⟨3, none⟩ : SyncEntry).Live cv1 ∧
    ControlOf L0 x2 ⟨3, none⟩ = some 2 ∧ ControlOf L0 cv1 ⟨3, none⟩ = some 9 ∧
    Touches L0 (x2, regX, []) (.spawnVal 0 [] mLocals [(0, 7)]) 2 := by
  have h : Steps5R KM L0 [(x2, regX, []), (cv1, regX, [])] [.spawnVal 0 [] mLocals [(0, 7)]] :=
    .cons ⟨⟨⟨by decide, trivial⟩, trivial, trivial⟩, by decide⟩
      (.spawnVal ⟨by decide, .ok (by decide)⟩) .nil
  exact ⟨rfl, (mx3_steps h).run _, by decide, by decide, by decide, by decide, by decide⟩

/-! ## `fin de vie` -/

/-- `c0 : endUse(M)` (O12). -/
def ce1 : SC := x2.set (endUseEff (x2.view 0) 0)

/-- The labels of the `endUse(M)` trace. -/
def ceLbls : List Label := mx3Lbls ++ [.kernel 0 (.endUse 0)]

/-- The named states of the `endUse(M)` trace. -/
def ceσ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(x0, [], []), (x1, [], []), (x2, [], []), (x2, regX, []), (ce1, regX, [])].getD i
    (ce1, regX, [])

/-- Brief, task 4, `endUse`, status `fin de vie` (`corpus-spec2-m3.md` S17a twin; WC5.1 corrigé
C22 item 5): from `MX₃`, `c0 : endUse(M)` is an `ok` step admitted by `Encap5R`; it touches `lock`
and entry `e` is dead after it. -/
theorem endUse_ends : ceσ 0 = (SC.ofS3 (S3.init mxst), [], []) ∧ Run5R KM L0 ceσ ceLbls ∧
    (⟨3, none⟩ : SyncEntry).Live x2 ∧ ¬ (⟨3, none⟩ : SyncEntry).Live ce1 ∧
    Touches L0 (x2, regX, []) (.kernel 0 (.endUse 0)) 2 := by
  have h : Steps5R KM L0 [(x2, regX, []), (ce1, regX, [])] [.kernel 0 (.endUse 0)] :=
    .cons ⟨⟨(by decide : ∀ e ∈ regX, e.Live x2 → ControlOf L0 x2 e ≠ some 0 ∧
        OptP (slotOf x2 e.guarded) (fun q => partOf x2.P 0 q → 0 = q) True), trivial, trivial⟩,
        by decide⟩
      (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) .nil
  exact ⟨rfl, (mx3_steps h).run _, by decide, by decide, by decide⟩

/-- `c0 : release(guarded)` (O3). -/
def cr1 : SC := x2.set (releaseEff (x2.view 0) 3)

/-- The labels of the `release(guarded)` trace. -/
def crLbls : List Label := mx3Lbls ++ [.kernel 0 (.release 3)]

/-- The named states of the `release(guarded)` trace. -/
def crσ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(x0, [], []), (x1, [], []), (x2, [], []), (x2, regX, []), (cr1, regX, [])].getD i
    (cr1, regX, [])

/-- Brief, task 4, `release`, status `fin de vie`: from `MX₃`, `c0 : release(guarded)` is an `ok`
step admitted by `Encap5R` (Spec 1 §62: `guarded` is derived, held by `slot`, on which `root_M`
gives exercisable `Modify`; WC5.1 corrigé C22 excludes `derive` and `split` from `guarded`, not its
`release`); entry `e` is dead after it. The step touches no leaf. -/
theorem release_ends : crσ 0 = (SC.ofS3 (S3.init mxst), [], []) ∧ Run5R KM L0 crσ crLbls ∧
    (⟨3, none⟩ : SyncEntry).Live x2 ∧ ¬ (⟨3, none⟩ : SyncEntry).Live cr1 := by
  have h : Steps5R KM L0 [(x2, regX, []), (cr1, regX, [])] [.kernel 0 (.release 3)] :=
    .cons ⟨⟨trivial, trivial, trivial⟩, by decide⟩
      (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) .nil
  exact ⟨rfl, (mx3_steps h).run _, by decide, by decide⟩

end Ern.Concurrency.MutexReal.ClassifyWitness
