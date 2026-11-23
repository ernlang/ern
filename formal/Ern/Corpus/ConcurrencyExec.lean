import Ern.ConcurrencyModel.WitnessSafe
import Ern.Corpus.ConcurrencyFrames
import Ern.Corpus.ConcurrencyMutex

/-!
# Corpus of the concurrency model: executions and the safe trace (test module)

Cases `R46`–`R48` of the concurrency model
(`specs/ERN_Concurrency_Model_Specification_v0.md`):
each execution is an `EncapsulatedTrace` with named states from the initial state of Spec 1 §47
(`EncapRun`), with a hand-written graph of fragment F, its correspondence (K1–K4) and the data of
reading 9 (storage identities of type `Unit`, no initial write: `unitData`). A trace that is not
safe states the condition of `SafeConcurrentTrace` that fails, every other condition, the
correspondence premises Q1–Q3 (C52), the hypothesis of reading 12 (`CtlAtomic`) and the race
(C33). A safe trace states `SafeConcurrentTrace`, Q1–Q3, reading 12, and applies 14d (`no_race`).
Each docstring gives the expected verdict with its clause, the obtained verdict and the twin. The
expected order of the loss marker and the expected races are those of C45, C46 and C33. This is a
test module: no model module imports it.

Events: `write3` carries a non-atomic access of the range of the written place; the controller
events follow realization R (`nmEv`, `acqEv`, `pubEv` of `WitnessLock`); the other steps are pure
authority markers, except the lifecycle events (`lifeEv`).
-/

namespace Ern.Corpus.Concurrency

open Ern.MemoryModel Ern.MemoryModel.Access Ern.ConcurrencyModel Events

variable {pm : ProviderMeta}

set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

/-! ## R46: restitution by a `release` after the `spawn` -/

/-- Step 6 of `R46`: `write3(X)` by context 1 through `a` (O10). -/
def r46s7 : SC := r07s6.set (write3Eff (r07s6.view 1) [0])

/-- The labels of `R46`: `X` initialized; `a := derive(root_X, Modify)`; `b := derive(a,
Modify)`; the `spawn` of context 1 yielding `a`; `c0 : write3(X)` by `b`; `c0 : release(b)`;
`c1 : write3(X)` by `a`. -/
def r46L : List Label :=
  [.kernel 0 (.write 0 [0]), .kernel 0 (.derive 0 [0] .modify), .kernel 0 (.derive 1 [0] .modify),
   .spawn 0 [1] [], .kernel 0 (.write 2 [0]), .kernel 0 (.release 2), .kernel 1 (.write 1 [0])]

/-- The states of `R46`. -/
def r46σ : Nat → SC × SyncReg × ArenaReg
  | 0 => (SC.ofS3 (S3.init oneLocal), [], []) | 1 => (r07s1, [], []) | 2 => (r07s2, [], [])
  | 3 => (r07s3, [], []) | 4 => (r07s4, [], []) | 5 => (r07s5, [], []) | 6 => (r07s6, [], [])
  | _ => (r46s7, [], [])

/-- `R46` is an `EncapsulatedTrace` with named states from the initial state (C51.1). -/
theorem r46_run : EncapRun pm kX mutexLayout r46σ r46L := by
  refine encapRun_of_steps fun i hi lbl hl => ?_
  match i, hi with
  | 0, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 1, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 2, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 3, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .spawn (.ok (by decide))⟩
  | 4, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 5, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 6, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩

/-- The graph of `R46`: the initializing write of `c0`, the two derivations, `spawn(c1)`,
`start(c1)`, the write of `c0` through `b`, `release(b)`, the write of `c1` through `a`. -/
def r46G : ListGraph 8 Nat Nat Nat Unit where
  ev i := match i.val with
    | 0 => wrEv 0 0 rX | 1 => pureEv 0 1 | 2 => pureEv 0 2 | 3 => lifeEv 0 3 0 (.spawn 1)
    | 4 => lifeEv 1 3 1 (.start 1) | 5 => wrEv 0 4 rX | 6 => pureEv 0 5 | _ => wrEv 1 6 rX
  uRange _ := ⟨0, 0⟩
  rf := []
  mo := []

/-- The correspondence of `R46`. -/
def r46K : StepEvents (Fin 8) := listK [0, 1, 2, 3, 5, 6, 7] [(1, 4)] []

/-- **R46** (not safe: `HandoffOrdered` alone fails; race). The base frame has a local `X`,
initialized; `a := derive(root_X, Modify)`; `b := derive(a, Modify)`; context 0 spawns context 1
yielding `a`; context 0 writes `X` through `b`, then releases `b`; context 1 writes `X` through
`a`. Expected (C45, C46, C51 item 2(f); C33): `HandoffOrdered` alone fails: the loss marker is
`release(b)`, later than the `spawn`; the write of `c0` through `b` and that of `c1` race.
Obtained: the execution is an `EncapsulatedTrace`; the loss marker of the pair of the write of
`c0` (step 4) and that of `c1` (step 6) is `release(b)` (step 5, `FirstCompatible`);
`HandoffOrdered` fails for that pair; every other condition of the safe trace holds, and Q1–Q3
and reading 12 hold; the two writes (events 5 and 7) race. Twin: `R46_twin`. -/
theorem R46 :
    r46σ 0 = (SC.ofS3 (S3.init oneLocal), [], []) ∧ EncapRun pm kX mutexLayout r46σ r46L ∧
    Corresponds r46G.toGraph r46σ r46L r46K ∧ r46G.toGraph.EventConsistent ∧
    r46G.toGraph.FiniteCausalPast ∧ OrdinaryAtomicOK kX r46σ r46L ∧
    r46G.toGraph.OrderLegal ∧ StepOrders kX mutexLayout refOrders r46σ r46L r46G.toGraph r46K ∧
    UnitLeaf kX mutexLayout refOrders r46σ r46L r46G.toGraph r46K ∧
    ConfinedExcl kX r46σ r46L ∧
    ConfinedHandoff kX mutexLayout refOrders r46σ r46L r46G.toGraph r46K ∧
    SyncOrdered kX mutexLayout refOrders r46σ r46L r46G.toGraph r46K ∧ InheritedLegal kX r46L ∧
    ¬ HandoffOrdered kX mutexLayout refOrders r46σ r46L r46G.toGraph r46K ∧
    LifetimeOrdered r46G.toGraph (unitData (lbls := r46L) (K := r46K)) ∧
    LifecycleOK r46G.toGraph r46σ r46L r46K ∧ LockEdge r46G.toGraph r46L r46K ∧
    CorrQ1 r46G.toGraph r46L r46K unitData ∧
    CorrQ2 kX mutexLayout refOrders r46σ r46L r46G.toGraph r46K unitData ∧
    CorrQ3 (unitData (G := r46G.toGraph) (lbls := r46L) (K := r46K)) ∧
    CorrQ4 kX mutexLayout refOrders r46σ r46L r46K ∧
    CtlAtomic kX mutexLayout r46σ r46L ∧
    FirstCompatible IncompatModify r46σ 4 0 0 .modify 5 ∧
    r46L[5]? = some (.kernel 0 (.release 2)) ∧ r46G.toGraph.Race 5 7 ∧
    ¬ SafeConcurrentTrace pm kX mutexLayout refOrders r46σ r46L r46G.toGraph r46K unitData := by
  have hK : Corresponds r46G.toGraph r46σ r46L r46K :=
    corresponds_of_check _ _ _ [(3, 1)] _ _ _ (by decide +kernel) (by decide) (by decide +kernel)
  have hno : ¬ HandoffOrdered kX mutexLayout refOrders r46σ r46L r46G.toGraph r46K := fun h =>
    absurd (h 4 6 ⟨0, .write, none, .modify⟩ ⟨0, .write, none, .modify⟩
      (conflictPair_of (by decide) (by decide) (by decide) rfl (by decide) (by decide)
        (by decide))
      (by decide) (kX_noConf 0)) (by decide +kernel)
  exact ⟨rfl, r46_run, hK, by decide +kernel, finitePast_fin _, by decide,
    orderLegal_of_check (by decide +kernel),
    stepOrders_of_check (listK_none (by decide)) (by decide +kernel),
    unitLeaf_of_check (listK_none (by decide)) (by decide +kernel) (by decide +kernel)
      (by decide +kernel),
    confinedExcl_none kX_noConf, confinedHandoff_of_check (by decide +kernel),
    syncOrdered_of_check (by decide +kernel), by decide, hno,
    ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩, hK.lifecycle,
    lockEdge_none (by decide), by unfold CorrQ1; decide +kernel,
    corrQ2_of_check (listK_none (by decide)) (by decide +kernel),
    by unfold CorrQ3; decide +kernel, corrQ4_of_check (by decide +kernel),
    ctlAtomic_of_check (by decide),
    firstCompatible_of_check (by decide) (by decide) (by decide), rfl, by decide +kernel,
    fun h => hno h.handoff⟩

/-- Twin of `R46`: `c0 : write3(X)` by `b`, before the `spawn` (O10). -/
def r46t4 : SC := r07s3.set (write3Eff (r07s3.view 0) [0])
/-- Twin of `R46`: `c0 : release(b)` (O3). -/
def r46t5 : SC := r46t4.set (releaseEff (r46t4.view 0) 2)
/-- Twin of `R46`: the `spawn` of context 1 yielding `a` (C4). -/
def r46t6 : SC := spawnEff r46t5 0 [1] []
/-- Twin of `R46`: `c1 : write3(X)` by `a` (O10). -/
def r46t7 : SC := r46t6.set (write3Eff (r46t6.view 1) [0])

/-- The labels of the twin of `R46`. -/
def r46TL : List Label :=
  [.kernel 0 (.write 0 [0]), .kernel 0 (.derive 0 [0] .modify), .kernel 0 (.derive 1 [0] .modify),
   .kernel 0 (.write 2 [0]), .kernel 0 (.release 2), .spawn 0 [1] [], .kernel 1 (.write 1 [0])]

/-- The states of the twin of `R46`. -/
def r46Tσ : Nat → SC × SyncReg × ArenaReg
  | 0 => (SC.ofS3 (S3.init oneLocal), [], []) | 1 => (r07s1, [], []) | 2 => (r07s2, [], [])
  | 3 => (r07s3, [], []) | 4 => (r46t4, [], []) | 5 => (r46t5, [], []) | 6 => (r46t6, [], [])
  | _ => (r46t7, [], [])

/-- The twin of `R46` is an `EncapsulatedTrace` with named states from the initial state. -/
theorem r46T_run : EncapRun pm kX mutexLayout r46Tσ r46TL := by
  refine encapRun_of_steps fun i hi lbl hl => ?_
  match i, hi with
  | 0, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 1, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 2, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 3, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 4, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 5, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .spawn (.ok (by decide))⟩
  | 6, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩

/-- The graph of the twin of `R46`. -/
def r46TG : ListGraph 8 Nat Nat Nat Unit where
  ev i := match i.val with
    | 0 => wrEv 0 0 rX | 1 => pureEv 0 1 | 2 => pureEv 0 2 | 3 => wrEv 0 3 rX | 4 => pureEv 0 4
    | 5 => lifeEv 0 5 0 (.spawn 1) | 6 => lifeEv 1 5 1 (.start 1) | _ => wrEv 1 6 rX
  uRange _ := ⟨0, 0⟩
  rf := []
  mo := []

/-- The correspondence of the twin of `R46`. -/
def r46TK : StepEvents (Fin 8) := listK [0, 1, 2, 3, 4, 5, 7] [(1, 6)] []

/-- **R46, twin** (safe). The write of `c0` through `b` and `release(b)` before the `spawn`.
Expected: a safe trace; the loss marker is the `spawn`, ordered by the creation edge (C47).
Obtained: `SafeConcurrentTrace`, Q1–Q3 and reading 12 hold; the loss marker of the pair of the
write of `c0` through `b` (step 3) and that of `c1` (step 6) is the `spawn` (step 5); 14d applies:
no pair of events races. -/
theorem R46_twin :
    SafeConcurrentTrace pm kX mutexLayout refOrders r46Tσ r46TL r46TG.toGraph r46TK unitData ∧
    CorrQ1 r46TG.toGraph r46TL r46TK unitData ∧
    CorrQ2 kX mutexLayout refOrders r46Tσ r46TL r46TG.toGraph r46TK unitData ∧
    CorrQ3 (unitData (G := r46TG.toGraph) (lbls := r46TL) (K := r46TK)) ∧
    CorrQ4 kX mutexLayout refOrders r46Tσ r46TL r46TK ∧
    CtlAtomic kX mutexLayout r46Tσ r46TL ∧
    FirstCompatible IncompatModify r46Tσ 3 0 0 .modify 5 ∧ ∀ a b, ¬ r46TG.toGraph.Race a b := by
  have hK : Corresponds r46TG.toGraph r46Tσ r46TL r46TK :=
    corresponds_of_check _ _ _ [(5, 1)] _ _ _ (by decide +kernel) (by decide) (by decide +kernel)
  have hS : SafeConcurrentTrace pm kX mutexLayout refOrders r46Tσ r46TL r46TG.toGraph r46TK
      unitData :=
    ⟨r46T_run, by decide +kernel, finitePast_fin _, by decide,
      orderLegal_of_check (by decide +kernel),
      stepOrders_of_check (listK_none (by decide)) (by decide +kernel),
      unitLeaf_of_check (listK_none (by decide)) (by decide +kernel) (by decide +kernel)
        (by decide +kernel),
      confinedExcl_none kX_noConf,
      confinedHandoff_of_check (by decide +kernel), syncOrdered_of_check (by decide +kernel),
      by decide, handoffOrdered_of_check (by decide +kernel),
      ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩, hK.lifecycle,
      lockEdge_none (by decide)⟩
  have hq1 : CorrQ1 r46TG.toGraph r46TL r46TK unitData := by unfold CorrQ1; decide +kernel
  have hq2 : CorrQ2 kX mutexLayout refOrders r46Tσ r46TL r46TG.toGraph r46TK unitData :=
    corrQ2_of_check (listK_none (by decide)) (by decide +kernel)
  have hq3 : CorrQ3 (unitData (G := r46TG.toGraph) (lbls := r46TL) (K := r46TK)) := by
    unfold CorrQ3; decide +kernel
  have h12 : CtlAtomic kX mutexLayout r46Tσ r46TL := ctlAtomic_of_check (by decide)
  exact ⟨hS, hq1, hq2, hq3, corrQ4_of_check (by decide +kernel), h12,
    firstCompatible_of_check (by decide) (by decide) (by decide),
    no_race (testKS_dd _ _ _) (by decide : StaticsOK oneLocal) rfl hK hS hq1 hq2 hq3 h12⟩

/-! ## R47: a relay through an intermediate context, joined alone -/

/-- Step 10 of `R47`: `write3(X)` by context 0 through `root_X` (O10). -/
def r47s11 : SC := r08s9.set (write3Eff (r08s9.view 0) [0])

/-- The labels of `R47`: the setup and steps 1–6 of `R08`. -/
def r47L : List Label :=
  [.kernel 0 (.write 0 [0]), .kernel 0 (.derive 0 [0] .modify), .spawn 0 [1] [],
   .kernel 1 (.derive 1 [0] .modify), .spawn 1 [2] [], .kernel 2 (.write 2 [0]),
   .kernel 2 (.release 2), .kernel 1 (.release 1), .terminate 1, .join 0 1,
   .kernel 0 (.write 0 [0])]

/-- The states of `R47`. -/
def r47σ : Nat → SC × SyncReg × ArenaReg
  | 0 => (SC.ofS3 (S3.init oneLocal), [], []) | 1 => (r05s1, [], []) | 2 => (r08s2, [], [])
  | 3 => (r08s3, [], []) | 4 => (r08s4, [], []) | 5 => (r08s5, [], []) | 6 => (r08s6, [], [])
  | 7 => (r08s7, [], []) | 8 => (r08s8, [], []) | 9 => (r08s9, [], []) | 10 => (r08s9, [], [])
  | _ => (r47s11, [], [])

/-- `R47` is an `EncapsulatedTrace` with named states from the initial state (C51.1). -/
theorem r47_run : EncapRun pm kX mutexLayout r47σ r47L := by
  refine encapRun_of_steps fun i hi lbl hl => ?_
  match i, hi with
  | 0, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 1, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 2, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .spawn (.ok (by decide))⟩
  | 3, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 4, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .spawn (.ok (by decide))⟩
  | 5, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 6, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 7, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 8, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .terminate (.ok (by decide))⟩
  | 9, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .join (.ok (by decide) (by decide))⟩
  | 10, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩

/-- The graph of `R47`. -/
def r47G : ListGraph 14 Nat Nat Nat Unit where
  ev i := match i.val with
    | 0 => wrEv 0 0 rX | 1 => pureEv 0 1 | 2 => lifeEv 0 2 0 (.spawn 1)
    | 3 => lifeEv 1 2 1 (.start 1) | 4 => pureEv 1 3 | 5 => lifeEv 1 4 0 (.spawn 2)
    | 6 => lifeEv 2 4 1 (.start 2) | 7 => wrEv 2 5 rX | 8 => pureEv 2 6 | 9 => pureEv 1 7
    | 10 => pureEv 1 8 | 11 => lifeEv 1 8 1 (.complete 1) | 12 => lifeEv 0 9 0 (.join 1)
    | _ => wrEv 0 10 rX
  uRange _ := ⟨0, 0⟩
  rf := []
  mo := []

/-- The correspondence of `R47`. -/
def r47K : StepEvents (Fin 14) :=
  listK [0, 1, 2, 4, 5, 7, 8, 9, 10, 12, 13] [(1, 3), (2, 6)] [(1, 11)]

/-- **R47** (not safe: `HandoffOrdered` alone fails; race). The execution of `R08`, steps 1–6:
`X` initialized; `a := derive(root_X, Modify)`; context 0 spawns context 1 yielding `a`; context
1 derives `a₂ := derive(a, Modify)` and spawns context 2 yielding `a₂`; context 2 writes `X`
through `a₂` and releases `a₂`; context 1 releases `a` and terminates; context 0 joins context 1,
then writes `X` through `root_X`. Expected (C45, C46, C47, C51 item 2(f); C33): `HandoffOrdered`
alone fails, for the pair of the write of `c2` and the final write of `c0`, despite `join(c1)`;
these two writes race. Obtained: the execution is an `EncapsulatedTrace`; the loss marker of that
pair (steps 5 and 10) is `release(a₂)` (step 6, `FirstCompatible`); `HandoffOrdered` fails for it;
every other condition of the safe trace holds, and Q1–Q3 and reading 12 hold; the two writes
(events 7 and 13) race. Twin: `R47_twin`. -/
theorem R47 :
    r47σ 0 = (SC.ofS3 (S3.init oneLocal), [], []) ∧ EncapRun pm kX mutexLayout r47σ r47L ∧
    Corresponds r47G.toGraph r47σ r47L r47K ∧ r47G.toGraph.EventConsistent ∧
    r47G.toGraph.FiniteCausalPast ∧ OrdinaryAtomicOK kX r47σ r47L ∧
    r47G.toGraph.OrderLegal ∧ StepOrders kX mutexLayout refOrders r47σ r47L r47G.toGraph r47K ∧
    UnitLeaf kX mutexLayout refOrders r47σ r47L r47G.toGraph r47K ∧
    ConfinedExcl kX r47σ r47L ∧
    ConfinedHandoff kX mutexLayout refOrders r47σ r47L r47G.toGraph r47K ∧
    SyncOrdered kX mutexLayout refOrders r47σ r47L r47G.toGraph r47K ∧ InheritedLegal kX r47L ∧
    ¬ HandoffOrdered kX mutexLayout refOrders r47σ r47L r47G.toGraph r47K ∧
    LifetimeOrdered r47G.toGraph (unitData (lbls := r47L) (K := r47K)) ∧
    LifecycleOK r47G.toGraph r47σ r47L r47K ∧ LockEdge r47G.toGraph r47L r47K ∧
    CorrQ1 r47G.toGraph r47L r47K unitData ∧
    CorrQ2 kX mutexLayout refOrders r47σ r47L r47G.toGraph r47K unitData ∧
    CorrQ3 (unitData (G := r47G.toGraph) (lbls := r47L) (K := r47K)) ∧
    CorrQ4 kX mutexLayout refOrders r47σ r47L r47K ∧
    CtlAtomic kX mutexLayout r47σ r47L ∧
    FirstCompatible IncompatModify r47σ 5 2 0 .modify 6 ∧
    r47L[6]? = some (.kernel 2 (.release 2)) ∧ r47G.toGraph.Race 7 13 ∧
    ¬ SafeConcurrentTrace pm kX mutexLayout refOrders r47σ r47L r47G.toGraph r47K unitData := by
  have hK : Corresponds r47G.toGraph r47σ r47L r47K :=
    corresponds_of_check _ _ _ [(2, 1), (4, 2)] _ _ _ (by decide +kernel) (by decide)
      (by decide +kernel)
  have hno : ¬ HandoffOrdered kX mutexLayout refOrders r47σ r47L r47G.toGraph r47K := fun h =>
    absurd (h 5 10 ⟨0, .write, none, .modify⟩ ⟨0, .write, none, .modify⟩
      (conflictPair_of (by decide) (by decide) (by decide) rfl (by decide) (by decide)
        (by decide))
      (by decide) (kX_noConf 0)) (by decide +kernel)
  exact ⟨rfl, r47_run, hK, by decide +kernel, finitePast_fin _, by decide,
    orderLegal_of_check (by decide +kernel),
    stepOrders_of_check (listK_none (by decide)) (by decide +kernel),
    unitLeaf_of_check (listK_none (by decide)) (by decide +kernel) (by decide +kernel)
      (by decide +kernel),
    confinedExcl_none kX_noConf, confinedHandoff_of_check (by decide +kernel),
    syncOrdered_of_check (by decide +kernel), by decide, hno,
    ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩, hK.lifecycle,
    lockEdge_none (by decide), by unfold CorrQ1; decide +kernel,
    corrQ2_of_check (listK_none (by decide)) (by decide +kernel),
    by unfold CorrQ3; decide +kernel, corrQ4_of_check (by decide +kernel),
    ctlAtomic_of_check (by decide),
    firstCompatible_of_check (by decide) (by decide) (by decide), rfl, by decide +kernel,
    fun h => hno h.handoff⟩

/-- Twin of `R47`: `c2 : terminate` after its `release` (C7). -/
def r47t8 : SC := termEffC r08s7 2
/-- Twin of `R47`: `c1 : release(a)`, after `c1 : join(c2)` (O3). -/
def r47t10 : SC := r47t8.set (releaseEff (r47t8.view 1) 1)
/-- Twin of `R47`: `c1 : terminate` (C7). -/
def r47t11 : SC := termEffC r47t10 1
/-- Twin of `R47`: `c0 : write3(X)` through `root_X`, after `c0 : join(c1)` (O10). -/
def r47t13 : SC := r47t11.set (write3Eff (r47t11.view 0) [0])

/-- The labels of the twin of `R47`. -/
def r47TL : List Label :=
  [.kernel 0 (.write 0 [0]), .kernel 0 (.derive 0 [0] .modify), .spawn 0 [1] [],
   .kernel 1 (.derive 1 [0] .modify), .spawn 1 [2] [], .kernel 2 (.write 2 [0]),
   .kernel 2 (.release 2), .terminate 2, .join 1 2, .kernel 1 (.release 1), .terminate 1,
   .join 0 1, .kernel 0 (.write 0 [0])]

/-- The states of the twin of `R47`. -/
def r47Tσ : Nat → SC × SyncReg × ArenaReg
  | 0 => (SC.ofS3 (S3.init oneLocal), [], []) | 1 => (r05s1, [], []) | 2 => (r08s2, [], [])
  | 3 => (r08s3, [], []) | 4 => (r08s4, [], []) | 5 => (r08s5, [], []) | 6 => (r08s6, [], [])
  | 7 => (r08s7, [], []) | 8 => (r47t8, [], []) | 9 => (r47t8, [], []) | 10 => (r47t10, [], [])
  | 11 => (r47t11, [], []) | 12 => (r47t11, [], []) | _ => (r47t13, [], [])

/-- The twin of `R47` is an `EncapsulatedTrace` with named states from the initial state. -/
theorem r47T_run : EncapRun pm kX mutexLayout r47Tσ r47TL := by
  refine encapRun_of_steps fun i hi lbl hl => ?_
  match i, hi with
  | 0, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 1, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 2, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .spawn (.ok (by decide))⟩
  | 3, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 4, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .spawn (.ok (by decide))⟩
  | 5, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 6, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 7, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .terminate (.ok (by decide))⟩
  | 8, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .join (.ok (by decide) (by decide))⟩
  | 9, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 10, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .terminate (.ok (by decide))⟩
  | 11, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .join (.ok (by decide) (by decide))⟩
  | 12, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩

/-- The graph of the twin of `R47`. -/
def r47TG : ListGraph 17 Nat Nat Nat Unit where
  ev i := match i.val with
    | 0 => wrEv 0 0 rX | 1 => pureEv 0 1 | 2 => lifeEv 0 2 0 (.spawn 1)
    | 3 => lifeEv 1 2 1 (.start 1) | 4 => pureEv 1 3 | 5 => lifeEv 1 4 0 (.spawn 2)
    | 6 => lifeEv 2 4 1 (.start 2) | 7 => wrEv 2 5 rX | 8 => pureEv 2 6 | 9 => pureEv 2 7
    | 10 => lifeEv 2 7 1 (.complete 2) | 11 => lifeEv 1 8 0 (.join 2) | 12 => pureEv 1 9
    | 13 => pureEv 1 10 | 14 => lifeEv 1 10 1 (.complete 1) | 15 => lifeEv 0 11 0 (.join 1)
    | _ => wrEv 0 12 rX
  uRange _ := ⟨0, 0⟩
  rf := []
  mo := []

/-- The correspondence of the twin of `R47`. -/
def r47TK : StepEvents (Fin 17) :=
  listK [0, 1, 2, 4, 5, 7, 8, 9, 11, 12, 13, 15, 16] [(1, 3), (2, 6)] [(2, 10), (1, 14)]

set_option maxHeartbeats 400000 in
/-- **R47, twin** (safe). Context 2 terminates after its `release`; context 1 joins context 2
before its own `release`; then the rest of `R47`. Expected: a safe trace. Obtained:
`SafeConcurrentTrace`, Q1–Q3 and reading 12 hold; 14d applies: no pair of events races. -/
theorem R47_twin :
    SafeConcurrentTrace pm kX mutexLayout refOrders r47Tσ r47TL r47TG.toGraph r47TK unitData ∧
    CorrQ1 r47TG.toGraph r47TL r47TK unitData ∧
    CorrQ2 kX mutexLayout refOrders r47Tσ r47TL r47TG.toGraph r47TK unitData ∧
    CorrQ3 (unitData (G := r47TG.toGraph) (lbls := r47TL) (K := r47TK)) ∧
    CorrQ4 kX mutexLayout refOrders r47Tσ r47TL r47TK ∧
    CtlAtomic kX mutexLayout r47Tσ r47TL ∧ ∀ a b, ¬ r47TG.toGraph.Race a b := by
  have hK : Corresponds r47TG.toGraph r47Tσ r47TL r47TK :=
    corresponds_of_check _ _ _ [(2, 1), (4, 2)] _ _ _ (by decide +kernel) (by decide)
      (by decide +kernel)
  have hS : SafeConcurrentTrace pm kX mutexLayout refOrders r47Tσ r47TL r47TG.toGraph r47TK
      unitData :=
    ⟨r47T_run, by decide +kernel, finitePast_fin _, by decide,
      orderLegal_of_check (by decide +kernel),
      stepOrders_of_check (listK_none (by decide)) (by decide +kernel),
      unitLeaf_of_check (listK_none (by decide)) (by decide +kernel) (by decide +kernel)
        (by decide +kernel),
      confinedExcl_none kX_noConf,
      confinedHandoff_of_check (by decide +kernel), syncOrdered_of_check (by decide +kernel),
      by decide, handoffOrdered_of_check (by decide +kernel),
      ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩, hK.lifecycle,
      lockEdge_none (by decide)⟩
  have hq1 : CorrQ1 r47TG.toGraph r47TL r47TK unitData := by unfold CorrQ1; decide +kernel
  have hq2 : CorrQ2 kX mutexLayout refOrders r47Tσ r47TL r47TG.toGraph r47TK unitData :=
    corrQ2_of_check (listK_none (by decide)) (by decide +kernel)
  have hq3 : CorrQ3 (unitData (G := r47TG.toGraph) (lbls := r47TL) (K := r47TK)) := by
    unfold CorrQ3; decide +kernel
  have h12 : CtlAtomic kX mutexLayout r47Tσ r47TL := ctlAtomic_of_check (by decide)
  exact ⟨hS, hq1, hq2, hq3, corrQ4_of_check (by decide +kernel), h12,
    no_race (testKS_dd _ _ _) (by decide : StaticsOK oneLocal) rfl hK hS hq1 hq2 hq3 h12⟩

/-! ## R48: a grant abandoned by a frame exit, then recovered -/

/-- The labels of `R48`: the construction of the reference mutex and steps 1–11 of `R22`. -/
def r48L : List Label := refMutexL ++ r22L ++ r22L'

/-- The states of `R48`. -/
def r48σ : Nat → SC × SyncReg × ArenaReg
  | 0 => (m0, [], []) | 1 => (m1, [], []) | 2 => (m2, [], []) | 3 => (m2, regFree, [])
  | 4 => (n3, regFree, []) | 5 => (r22s2, regFree, []) | 6 => (r22s3, regTaken, [])
  | 7 => (r22s4, regTaken, []) | 8 => (r22s5, regTaken, []) | 9 => (r22s6, regTaken, [])
  | 10 => (r22s7, regTaken, []) | 11 => (r22s8, regTaken, []) | 12 => (r22s8, regFree, [])
  | 13 => (r22s10, r22reg, []) | _ => (r22s11, r22reg, [])

/-- `R48` is an `EncapsulatedTrace` with named states from the initial state (C51.1). -/
theorem r48_run : EncapRun pm kMutex mutexLayout r48σ r48L := by
  refine encapRun_of_steps fun i hi lbl hl => ?_
  match i, hi with
  | 0, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel mutex_steps.1⟩
  | 1, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel mutex_steps.2.1⟩
  | 2, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .newMutex (st' := (m2, regFree)) mutex_steps.2.2.1⟩
  | 3, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 4, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel (.ok (by decide))⟩
  | 5, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .acquire (st' := (r22s3, regTaken)) ⟨⟨2, none⟩, rfl, by decide, by decide, rfl⟩⟩
  | 6, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 7, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .spawn (.ok (by decide))⟩
  | 8, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel (.ok (by decide))⟩
  | 9, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 10, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 11, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .resetLock (st' := (r22s8, regFree))
        ⟨⟨2, some 4⟩, rfl, by decide, by decide, by decide, by decide, rfl⟩⟩
  | 12, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .acquire (st' := (r22s10, r22reg)) ⟨⟨2, none⟩, rfl, by decide, by decide, rfl⟩⟩
  | 13, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩

/-- The graph of `R48` under the orders `R`: the controller write of `newMutex`, the `acquire` of
step 3 (step 5 of the trace), the `spawn` of context 1 and its `start`, the write of `T` by
context 1, the `resetLock`, the `acquire` of step 10, the write of `T` by context 0. -/
def r48G (R : CtlOrders) : ListGraph 15 Nat Nat Nat Unit where
  ev i := match i.val with
    | 0 => pureEv 0 0 | 1 => pureEv 0 1 | 2 => nmEv 0 2 | 3 => pureEv 0 3 | 4 => pureEv 0 4
    | 5 => acqEv 0 5 R.acq | 6 => pureEv 0 6 | 7 => lifeEv 0 7 0 (.spawn 1)
    | 8 => lifeEv 1 7 1 (.start 1) | 9 => pureEv 0 8 | 10 => wrEv 1 9 rT | 11 => pureEv 1 10
    | 12 => pubEv 0 11 R.reset | 13 => acqEv 0 12 R.acq | _ => wrEv 0 13 rT
  uRange _ := ⟨8, 8⟩
  rf := [(2, 5), (12, 13)]
  mo := [(2, 5), (2, 12), (2, 13), (5, 12), (5, 13), (12, 13)]

/-- The correspondence of `R48`. -/
def r48K : StepEvents (Fin 15) := listK [0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 14] [(1, 8)] []

set_option maxHeartbeats 400000 in
/-- **R48** (not safe: `HandoffOrdered` alone fails; race). The execution of `R22`, steps 1–11,
after the construction of the reference mutex, under the reference triple. Expected (C45, C46,
C48, C49, C51 item 2(f); C33): `HandoffOrdered` alone fails, for the write of `T` by `c1` (step 7)
and that of `c0` (step 11): the loss marker is `release(x)`; the edge of `LockOrder` holds (the
`acquire` of step 10 reads the `resetLock` of the same context); the two writes race. Obtained:
the execution is an `EncapsulatedTrace` with realization R; the loss marker of that pair (steps 9
and 13 of the trace) is `release(x)` (step 10 of the trace, `FirstCompatible`); `HandoffOrdered`
fails for it; the `acquire` of step 10 reads by `rf` the `resetLock` (events 12, 13) and the edge
of `LockOrder` holds by 14e; every other condition of the safe trace holds, and Q1–Q3 and reading
12 hold; the two writes (events 10 and 14) race. Twin: `R48_twin`. -/
theorem R48 :
    r48σ 0 = (SC.ofS3 (S3.init mutexStatics), [], []) ∧ EncapRun pm kMutex mutexLayout r48σ r48L ∧
    Corresponds (r48G refOrders).toGraph r48σ r48L r48K ∧
    (r48G refOrders).toGraph.EventConsistent ∧
    Realizes (r48G refOrders).toGraph mutexLayout r48σ r48L r48K 0 2 refOrders 0 1 ∧
    (r48G refOrders).toGraph.FiniteCausalPast ∧ OrdinaryAtomicOK kMutex r48σ r48L ∧
    (r48G refOrders).toGraph.OrderLegal ∧
    StepOrders kMutex mutexLayout refOrders r48σ r48L (r48G refOrders).toGraph r48K ∧
    UnitLeaf kMutex mutexLayout refOrders r48σ r48L (r48G refOrders).toGraph r48K ∧
    ConfinedExcl kMutex r48σ r48L ∧
    ConfinedHandoff kMutex mutexLayout refOrders r48σ r48L (r48G refOrders).toGraph r48K ∧
    SyncOrdered kMutex mutexLayout refOrders r48σ r48L (r48G refOrders).toGraph r48K ∧
    InheritedLegal kMutex r48L ∧
    ¬ HandoffOrdered kMutex mutexLayout refOrders r48σ r48L (r48G refOrders).toGraph r48K ∧
    LifetimeOrdered (r48G refOrders).toGraph (unitData (lbls := r48L) (K := r48K)) ∧
    LifecycleOK (r48G refOrders).toGraph r48σ r48L r48K ∧
    (r48G refOrders).toGraph.rf 12 13 ∧ LockEdge (r48G refOrders).toGraph r48L r48K ∧
    CorrQ1 (r48G refOrders).toGraph r48L r48K unitData ∧
    CorrQ2 kMutex mutexLayout refOrders r48σ r48L (r48G refOrders).toGraph r48K unitData ∧
    CorrQ3 (unitData (G := (r48G refOrders).toGraph) (lbls := r48L) (K := r48K)) ∧
    CorrQ4 kMutex mutexLayout refOrders r48σ r48L r48K ∧
    CtlAtomic kMutex mutexLayout r48σ r48L ∧
    FirstCompatible IncompatModify r48σ 9 1 3 .modify 10 ∧
    r48L[10]? = some (.kernel 1 (.release 5)) ∧ (r48G refOrders).toGraph.Race 10 14 ∧
    ¬ SafeConcurrentTrace pm kMutex mutexLayout refOrders r48σ r48L (r48G refOrders).toGraph r48K
      unitData := by
  have hK : Corresponds (r48G refOrders).toGraph r48σ r48L r48K :=
    corresponds_of_check _ _ _ [(7, 1)] _ _ _ (by decide +kernel) (by decide) (by decide +kernel)
  have hR : Realizes (r48G refOrders).toGraph mutexLayout r48σ r48L r48K 0 2 refOrders 0 1 :=
    realizes_of_check _ _ _ _ _ _ _ _ _ _ _ _ (by decide +kernel)
  have hno : ¬ HandoffOrdered kMutex mutexLayout refOrders r48σ r48L (r48G refOrders).toGraph
      r48K := fun h =>
    absurd (h 9 13 ⟨3, .write, none, .modify⟩ ⟨3, .write, none, .modify⟩
      (conflictPair_of (by decide) (by decide) (by decide) rfl (by decide) (by decide)
        (by decide))
      (by decide) (kMutex_noConf 3)) (by decide +kernel)
  exact ⟨rfl, r48_run, hK, by decide +kernel, hR, finitePast_fin _, by decide,
    orderLegal_of_check (by decide +kernel),
    stepOrders_of_check (listK_none (by decide)) (by decide +kernel),
    unitLeaf_of_check (listK_none (by decide)) (by decide +kernel) (by decide +kernel)
      (by decide +kernel),
    confinedExcl_none kMutex_noConf, confinedHandoff_of_check (by decide +kernel),
    syncOrdered_of_check (by decide +kernel), by decide, hno,
    ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩, hK.lifecycle, by decide +kernel,
    mutex_lockEdge hR (by decide) (by decide), by unfold CorrQ1; decide +kernel,
    corrQ2_of_check (listK_none (by decide)) (by decide +kernel),
    by unfold CorrQ3; decide +kernel, corrQ4_of_check (by decide +kernel),
    ctlAtomic_of_check (by decide),
    firstCompatible_of_check (by decide) (by decide) (by decide), rfl, by decide +kernel,
    fun h => hno h.handoff⟩

/-- Twin of `R48`: `c1 : terminate` after `release(x)` (C7). -/
def r48t11 : SC := termEffC r22s8 1
/-- Twin of `R48`: `c0 : acquire(e)` after `join(c1)` and `resetLock(e)`: the grant 6 (C16). -/
def r48t14 : SC := deriveSyncEff r48t11 0 2
/-- Twin of `R48`: `c0 : write3(T)` through the grant 6 (O10). -/
def r48t15 : SC := r48t14.set (write3Eff (r48t14.view 0) [3])

/-- The labels of the twin of `R48`: `R48` with `c1 : terminate` and `c0 : join(c1)` after step 8
of `R22`. -/
def r48TL : List Label := refMutexL ++ r22L ++ [.terminate 1, .join 0 1] ++ r22L'

/-- The states of the twin of `R48`. -/
def r48Tσ : Nat → SC × SyncReg × ArenaReg
  | 0 => (m0, [], []) | 1 => (m1, [], []) | 2 => (m2, [], []) | 3 => (m2, regFree, [])
  | 4 => (n3, regFree, []) | 5 => (r22s2, regFree, []) | 6 => (r22s3, regTaken, [])
  | 7 => (r22s4, regTaken, []) | 8 => (r22s5, regTaken, []) | 9 => (r22s6, regTaken, [])
  | 10 => (r22s7, regTaken, []) | 11 => (r22s8, regTaken, []) | 12 => (r48t11, regTaken, [])
  | 13 => (r48t11, regTaken, []) | 14 => (r48t11, regFree, []) | 15 => (r48t14, r22reg, [])
  | _ => (r48t15, r22reg, [])

/-- The twin of `R48` is an `EncapsulatedTrace` with named states from the initial state. -/
theorem r48T_run : EncapRun pm kMutex mutexLayout r48Tσ r48TL := by
  refine encapRun_of_steps fun i hi lbl hl => ?_
  match i, hi with
  | 0, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel mutex_steps.1⟩
  | 1, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel mutex_steps.2.1⟩
  | 2, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .newMutex (st' := (m2, regFree)) mutex_steps.2.2.1⟩
  | 3, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 4, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel (.ok (by decide))⟩
  | 5, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .acquire (st' := (r22s3, regTaken)) ⟨⟨2, none⟩, rfl, by decide, by decide, rfl⟩⟩
  | 6, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 7, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .spawn (.ok (by decide))⟩
  | 8, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel (.ok (by decide))⟩
  | 9, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 10, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 11, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .terminate (.ok (by decide))⟩
  | 12, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .join (.ok (by decide) (by decide))⟩
  | 13, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .resetLock (st' := (r48t11, regFree))
        ⟨⟨2, some 4⟩, rfl, by decide, by decide, by decide, by decide, rfl⟩⟩
  | 14, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .acquire (st' := (r48t14, r22reg)) ⟨⟨2, none⟩, rfl, by decide, by decide, rfl⟩⟩
  | 15, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩

/-- The graph of the twin of `R48`. -/
def r48TG : ListGraph 18 Nat Nat Nat Unit where
  ev i := match i.val with
    | 0 => pureEv 0 0 | 1 => pureEv 0 1 | 2 => nmEv 0 2 | 3 => pureEv 0 3 | 4 => pureEv 0 4
    | 5 => acqEv 0 5 .acquire | 6 => pureEv 0 6 | 7 => lifeEv 0 7 0 (.spawn 1)
    | 8 => lifeEv 1 7 1 (.start 1) | 9 => pureEv 0 8 | 10 => wrEv 1 9 rT | 11 => pureEv 1 10
    | 12 => pureEv 1 11 | 13 => lifeEv 1 11 1 (.complete 1) | 14 => lifeEv 0 12 0 (.join 1)
    | 15 => pubEv 0 13 .release | 16 => acqEv 0 14 .acquire | _ => wrEv 0 15 rT
  uRange _ := ⟨8, 8⟩
  rf := [(2, 5), (15, 16)]
  mo := [(2, 5), (2, 15), (2, 16), (5, 15), (5, 16), (15, 16)]

/-- The correspondence of the twin of `R48`. -/
def r48TK : StepEvents (Fin 18) :=
  listK [0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 14, 15, 16, 17] [(1, 8)] [(1, 13)]

/-- The correspondence of the twin of `R48` (K1–K4). -/
theorem r48T_corr : Corresponds r48TG.toGraph r48Tσ r48TL r48TK :=
  corresponds_of_check _ _ _ [(7, 1)] _ _ _ (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- Realization R in the twin of `R48` (C48). -/
theorem r48T_realizes : Realizes r48TG.toGraph mutexLayout r48Tσ r48TL r48TK 0 2 refOrders 0 1 :=
  realizes_of_check _ _ _ _ _ _ _ _ _ _ _ _ (by decide +kernel)

/-- The graph of the twin of `R48` is `EventConsistent` (C34). -/
theorem r48T_consistent : r48TG.toGraph.EventConsistent := by decide +kernel

/-- `ConfinedHandoff` in the twin of `R48` (C51 item 2(c)). -/
theorem r48T_confined : ConfinedHandoff kMutex mutexLayout refOrders r48Tσ r48TL r48TG.toGraph r48TK :=
  confinedHandoff_of_check (by decide +kernel)

/-- `SyncOrdered` in the twin of `R48` (C51 item 2(d)). -/
theorem r48T_sync : SyncOrdered kMutex mutexLayout refOrders r48Tσ r48TL r48TG.toGraph r48TK :=
  syncOrdered_of_check (by decide +kernel)

/-- `HandoffOrdered` in the twin of `R48` (C46; C51 item 2(f)). -/
theorem r48T_handoff : HandoffOrdered kMutex mutexLayout refOrders r48Tσ r48TL r48TG.toGraph r48TK :=
  handoffOrdered_of_check (by decide +kernel)

/-- `LifetimeOrdered` in the twin of `R48` (C51). -/
theorem r48T_lifetime : LifetimeOrdered r48TG.toGraph (unitData (lbls := r48TL) (K := r48TK)) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- Q1 in the twin of `R48` (C52). -/
theorem r48T_q1 : CorrQ1 r48TG.toGraph r48TL r48TK unitData := by unfold CorrQ1; decide +kernel

/-- Q2 in the twin of `R48` (C52). -/
theorem r48T_q2 : CorrQ2 kMutex mutexLayout refOrders r48Tσ r48TL r48TG.toGraph r48TK unitData :=
  corrQ2_of_check (listK_none (by decide +kernel)) (by decide +kernel)

/-- Q3 in the twin of `R48` (C52). -/
theorem r48T_q3 : CorrQ3 (unitData (G := r48TG.toGraph) (lbls := r48TL) (K := r48TK)) := by
  unfold CorrQ3; decide +kernel

/-- Reading 12 in the twin of `R48`. -/
theorem r48T_ctl : CtlAtomic kMutex mutexLayout r48Tσ r48TL := ctlAtomic_of_check (by decide +kernel)

/-- The edge of `LockOrder` in the twin of `R48`, by 14e (C49; C51 item 2(f)). -/
theorem r48T_lock : LockEdge r48TG.toGraph r48TL r48TK :=
  mutex_lockEdge r48T_realizes (by decide +kernel) (by decide +kernel)

/-- The twin of `R48` is a `SafeConcurrentTrace` (C51). -/
theorem r48T_safe :
    SafeConcurrentTrace pm kMutex mutexLayout refOrders r48Tσ r48TL r48TG.toGraph r48TK unitData :=
  ⟨r48T_run, r48T_consistent, finitePast_fin _, by decide +kernel,
      orderLegal_of_check (by decide +kernel),
      stepOrders_of_check (listK_none (by decide)) (by decide +kernel),
      unitLeaf_of_check (listK_none (by decide)) (by decide +kernel) (by decide +kernel)
        (by decide +kernel),
      confinedExcl_none kMutex_noConf,
    r48T_confined, r48T_sync, by decide +kernel, r48T_handoff, r48T_lifetime,
    r48T_corr.lifecycle, r48T_lock⟩

/-- **R48, twin** (safe). After step 8 of `R22`: context 1 terminates; context 0 joins it; then
steps 9–11. Expected: a safe trace. Obtained: `SafeConcurrentTrace` (the edge of `LockOrder` by
14e), Q1–Q3 and reading 12 hold; 14d applies: no pair of events races. -/
theorem R48_twin :
    SafeConcurrentTrace pm kMutex mutexLayout refOrders r48Tσ r48TL r48TG.toGraph r48TK unitData ∧
    CorrQ1 r48TG.toGraph r48TL r48TK unitData ∧
    CorrQ2 kMutex mutexLayout refOrders r48Tσ r48TL r48TG.toGraph r48TK unitData ∧
    CorrQ3 (unitData (G := r48TG.toGraph) (lbls := r48TL) (K := r48TK)) ∧
    CorrQ4 kMutex mutexLayout refOrders r48Tσ r48TL r48TK ∧
    CtlAtomic kMutex mutexLayout r48Tσ r48TL ∧ ∀ a b, ¬ r48TG.toGraph.Race a b :=
  ⟨r48T_safe, r48T_q1, r48T_q2, r48T_q3, corrQ4_of_check (by decide +kernel), r48T_ctl,
    no_race (testKS_dd _ _ _) mutexStatics_ok rfl r48T_corr (r48T_safe (pm := pm)) r48T_q1 r48T_q2 r48T_q3
      r48T_ctl⟩

end Ern.Corpus.Concurrency
