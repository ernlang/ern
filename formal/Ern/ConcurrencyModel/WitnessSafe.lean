import Ern.ConcurrencyModel.WitnessSafeExec
import Ern.ConcurrencyModel.WitnessLock

/-!
# Witnesses S1–S3: safe traces on the executions of theorems 12 and 13 (C46, C49, C51, C52)

The executions, graphs and correspondences of W1, W2 and W7–W10 (`WitnessHandoff`, `WitnessLock`),
unchanged, with the data of reading 9: those graphs have no validity event and no initial write, and
their storage identities are of type `Unit`, one identity for every access, so Q3 is vacuous and Q2
covers every conflicting pair of step events. For each execution: the conditions of
`SafeConcurrentTrace` (C51 item 2), the correspondence premises Q1–Q3 (C52) and Q4 (C26), and the
premise of reading 12 (`CtlAtomic`). A safe trace applies 14d; a trace that is not safe states
the condition that fails, every other condition, and the race.

The contract `kMutex` classes the controller `lock` (leaf 2) `Atomic(4, 4)`: reading 12 holds for
W7–W10 without replaying them under another contract.
-/

namespace Ern.ConcurrencyModel

open Ern.MemoryModel Ern.MemoryModel.Access Events

variable {pm : ProviderMeta}

set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

/-- The contract of block X has no `Confined` leaf (C35). -/
theorem kX_noConf : ∀ l, ¬ ConfinedLeaf kX l := fun _ h => by cases h

/-- The contract of the mutex witnesses has no `Confined` leaf (C35). -/
theorem kMutex_noConf : ∀ l, ¬ ConfinedLeaf kMutex l := fun _ h => by
  unfold ConfinedLeaf at h; simp only [testKS] at h; split at h <;> cases h

/-- The data of reading 9 of a graph of storage type `Unit`: one identity, no initial write. -/
abbrev unitData {E U V : Type} {G : Events.Graph E Nat U V Unit} {lbls : List Label}
    {K : StepEvents E} : AccessData G lbls K :=
  noInit fun _ => ()

/-! ## S1: W1, restitution without `join` -/

/-- **Witness S1** (C46; C51 item 2(f)): W1 (`witness_w1`), restitution of `a` without `join`. All
steps are `ok` and the execution is an `EncapsulatedTrace`; `HandoffOrdered` fails for the pair of
the `write3` of `c1` (step 2) and that of `c0` (step 4) on `X`: their loss marker is `release(a)`,
and its event is not `hb`-before the write of `c0`. Every other condition of the safe trace holds,
and Q1–Q4 and reading 12 hold. The two writes race. -/
theorem witness_s1 :
    EncapRun pm kX mutexLayout w1σ w1L ∧ w1G.toGraph.EventConsistent ∧
    w1G.toGraph.FiniteCausalPast ∧ OrdinaryAtomicOK kX w1σ w1L ∧
    w1G.toGraph.OrderLegal ∧ StepOrders kX mutexLayout refOrders w1σ w1L w1G.toGraph w1K ∧
    UnitLeaf kX mutexLayout refOrders w1σ w1L w1G.toGraph w1K ∧
    ConfinedExcl kX w1σ w1L ∧
    ConfinedHandoff kX mutexLayout refOrders w1σ w1L w1G.toGraph w1K ∧
    SyncOrdered kX mutexLayout refOrders w1σ w1L w1G.toGraph w1K ∧ InheritedLegal kX w1L ∧
    ¬ HandoffOrdered kX mutexLayout refOrders w1σ w1L w1G.toGraph w1K ∧
    LifetimeOrdered w1G.toGraph (unitData (lbls := w1L) (K := w1K)) ∧
    LifecycleOK w1G.toGraph w1σ w1L w1K ∧ LockEdge w1G.toGraph w1L w1K ∧
    CorrQ1 w1G.toGraph w1L w1K unitData ∧
    CorrQ2 kX mutexLayout refOrders w1σ w1L w1G.toGraph w1K unitData ∧
    CorrQ3 (unitData (G := w1G.toGraph) (lbls := w1L) (K := w1K)) ∧
    CorrQ4 kX mutexLayout refOrders w1σ w1L w1K ∧
    CtlAtomic kX mutexLayout w1σ w1L ∧ w1G.toGraph.Race 3 5 ∧
    ¬ SafeConcurrentTrace pm kX mutexLayout refOrders w1σ w1L w1G.toGraph w1K unitData := by
  have hw := witness_w1 (pm := pm)
  have hno : ¬ HandoffOrdered kX mutexLayout refOrders w1σ w1L w1G.toGraph w1K := fun h =>
    absurd (h 2 4 ⟨0, .write, none, .modify⟩ ⟨0, .write, none, .modify⟩
      (conflictPair_of (by decide) (by decide) (by decide) rfl (by decide) (by decide)
        (by decide))
      (by decide) (kX_noConf 0)) (by decide +kernel)
  exact ⟨hw.2.1, hw.2.2.2.1, finitePast_fin _, by decide,
    orderLegal_of_check (by decide +kernel),
    stepOrders_of_check (listK_none (by decide)) (by decide +kernel),
    unitLeaf_of_check (listK_none (by decide)) (by decide +kernel) (by decide +kernel)
      (by decide +kernel),
    confinedExcl_none kX_noConf,
    confinedHandoff_of_check (by decide +kernel), syncOrdered_of_check (by decide +kernel),
    by decide, hno, ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩,
    hw.2.2.1.lifecycle, lockEdge_none (by decide), by unfold CorrQ1; decide +kernel,
    corrQ2_of_check (listK_none (by decide)) (by decide +kernel),
    by unfold CorrQ3; decide +kernel, corrQ4_of_check (by decide +kernel),
    ctlAtomic_of_check (by decide), by decide +kernel,
    fun h => hno h.handoff⟩

/-! ## S2: W2 and W7 -/

/-- **Witness S2**, W2 (C46, C47; C51, C52): W2 (`witness_w2`), restitution of `a` with `c1 :
terminate` and `c0 : join(c1)`, is a `SafeConcurrentTrace` from the initial state; Q1–Q4 and
reading 12 hold; 14d applies: no pair of events races. -/
theorem witness_s2_w2 :
    SafeConcurrentTrace pm kX mutexLayout refOrders w2σ w2L w2G.toGraph w2K unitData ∧
    CorrQ1 w2G.toGraph w2L w2K unitData ∧
    CorrQ2 kX mutexLayout refOrders w2σ w2L w2G.toGraph w2K unitData ∧
    CorrQ3 (unitData (G := w2G.toGraph) (lbls := w2L) (K := w2K)) ∧
    CorrQ4 kX mutexLayout refOrders w2σ w2L w2K ∧
    CtlAtomic kX mutexLayout w2σ w2L ∧ ∀ a b, ¬ w2G.toGraph.Race a b := by
  have hw := witness_w2 (pm := pm)
  have hS : SafeConcurrentTrace pm kX mutexLayout refOrders w2σ w2L w2G.toGraph w2K unitData :=
    ⟨hw.2.1, hw.2.2.2.1, finitePast_fin _, by decide,
      orderLegal_of_check (by decide +kernel),
      stepOrders_of_check (listK_none (by decide)) (by decide +kernel),
      unitLeaf_of_check (listK_none (by decide)) (by decide +kernel) (by decide +kernel)
        (by decide +kernel),
      confinedExcl_none kX_noConf,
      confinedHandoff_of_check (by decide +kernel), syncOrdered_of_check (by decide +kernel),
      by decide, handoffOrdered_of_check (by decide +kernel),
      ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩, hw.2.2.1.lifecycle,
      lockEdge_none (by decide)⟩
  have hq1 : CorrQ1 w2G.toGraph w2L w2K unitData := by unfold CorrQ1; decide +kernel
  have hq2 : CorrQ2 kX mutexLayout refOrders w2σ w2L w2G.toGraph w2K unitData :=
    corrQ2_of_check (listK_none (by decide)) (by decide +kernel)
  have hq3 : CorrQ3 (unitData (G := w2G.toGraph) (lbls := w2L) (K := w2K)) := by
    unfold CorrQ3; decide +kernel
  have h12 : CtlAtomic kX mutexLayout w2σ w2L := ctlAtomic_of_check (by decide)
  exact ⟨hS, hq1, hq2, hq3, corrQ4_of_check (by decide +kernel), h12,
    no_race (testKS_dd _ _ _) xStatics_ok hw.1 hw.2.2.1 hS hq1 hq2 hq3 h12⟩

/-- The edge of `LockOrder` for an execution of the mutex block whose `acquire` steps are all on
entry `0`, whose protocol steps on `0` have the controller `lock` (leaf 2), with realization R under
the reference triple: by 14e (`lock_edge_entry`). -/
theorem mutex_lockEdge {E S : Type} {G : Events.Graph E Nat Nat Nat S}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} {K : StepEvents E}
    (hR : Realizes G mutexLayout σ lbls K 0 2 refOrders 0 1)
    (hacq : ∀ k (hk : k < lbls.length), AcqEntry 0 lbls[k] = true)
    (hstab : ∀ k, k < lbls.length → ProtoOn lbls 0 k → ctlOf mutexLayout (σ k) 0 = some 2) :
    LockEdge G lbls K :=
  lockEdge_single 0 hacq
    (lock_edge_entry hR (.inl rfl) (.inl rfl) (.inl rfl) (stab_of_check hstab))

/-- **Witness S2**, W7 (C48, C49; C51, C52): W7 (`witness_w7`), the mutex handoff under the
reference triple, is a `SafeConcurrentTrace` from the initial state; its edge of `LockOrder` holds
by 14e; Q1–Q4 and reading 12 hold (the contract classes `lock` `Atomic(4, 4)`); 14d applies: no
pair of events races. -/
theorem witness_s2_w7 :
    SafeConcurrentTrace pm kMutex mutexLayout refOrders w7σ w7L (w7G refOrders).toGraph w7K
      unitData ∧
    CorrQ1 (w7G refOrders).toGraph w7L w7K unitData ∧
    CorrQ2 kMutex mutexLayout refOrders w7σ w7L (w7G refOrders).toGraph w7K unitData ∧
    CorrQ3 (unitData (G := (w7G refOrders).toGraph) (lbls := w7L) (K := w7K)) ∧
    CorrQ4 kMutex mutexLayout refOrders w7σ w7L w7K ∧
    CtlAtomic kMutex mutexLayout w7σ w7L ∧ ∀ a b, ¬ (w7G refOrders).toGraph.Race a b := by
  have hw := witness_w7 (pm := pm)
  have hS : SafeConcurrentTrace pm kMutex mutexLayout refOrders w7σ w7L (w7G refOrders).toGraph w7K
      unitData :=
    ⟨hw.2.1, hw.2.2.2.1, finitePast_fin _, by decide,
      orderLegal_of_check (by decide +kernel),
      stepOrders_of_check (listK_none (by decide)) (by decide +kernel),
      unitLeaf_of_check (listK_none (by decide)) (by decide +kernel) (by decide +kernel)
        (by decide +kernel),
      confinedExcl_none kMutex_noConf,
      confinedHandoff_of_check (by decide +kernel), syncOrdered_of_check (by decide +kernel),
      by decide, handoffOrdered_of_check (by decide +kernel),
      ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩, hw.2.2.1.lifecycle,
      mutex_lockEdge hw.2.2.2.2.1 (by decide) (by decide)⟩
  have hq1 : CorrQ1 (w7G refOrders).toGraph w7L w7K unitData := by unfold CorrQ1; decide +kernel
  have hq2 : CorrQ2 kMutex mutexLayout refOrders w7σ w7L (w7G refOrders).toGraph w7K unitData :=
    corrQ2_of_check (listK_none (by decide)) (by decide +kernel)
  have hq3 : CorrQ3 (unitData (G := (w7G refOrders).toGraph) (lbls := w7L) (K := w7K)) := by
    unfold CorrQ3; decide +kernel
  have h12 : CtlAtomic kMutex mutexLayout w7σ w7L := ctlAtomic_of_check (by decide)
  exact ⟨hS, hq1, hq2, hq3, corrQ4_of_check (by decide +kernel), h12,
    no_race (testKS_dd _ _ _) mutexStatics_ok hw.1 hw.2.2.1 hS hq1 hq2 hq3 h12⟩

/-! ## S3: W8 and W10, and the twin W9 -/

/-- **Witness S3**, W8 (C49; C51 item 2(f)): W8 (`witness_w8`), recovery without `join`. All steps
are `ok`; `HandoffOrdered` fails for the pair of the `write3` of `T` of `c1` (step 6) and that of
`c0` (step 11): their loss marker is `unlock(e)`, whose event is not `hb`-before the write of `c0`.
Every other condition holds, the edge of `LockOrder` by 14e; Q1–Q4 and reading 12 hold. The two
writes race. Admitted twin: W9 (`witness_s3_w9`). -/
theorem witness_s3_w8 :
    EncapRun pm kMutex mutexLayout w8σ w8L ∧ (w8G refOrders).toGraph.EventConsistent ∧
    (w8G refOrders).toGraph.FiniteCausalPast ∧ OrdinaryAtomicOK kMutex w8σ w8L ∧
    (w8G refOrders).toGraph.OrderLegal ∧
    StepOrders kMutex mutexLayout refOrders w8σ w8L (w8G refOrders).toGraph w8K ∧
    UnitLeaf kMutex mutexLayout refOrders w8σ w8L (w8G refOrders).toGraph w8K ∧
    ConfinedExcl kMutex w8σ w8L ∧
    ConfinedHandoff kMutex mutexLayout refOrders w8σ w8L (w8G refOrders).toGraph w8K ∧
    SyncOrdered kMutex mutexLayout refOrders w8σ w8L (w8G refOrders).toGraph w8K ∧
    InheritedLegal kMutex w8L ∧
    ¬ HandoffOrdered kMutex mutexLayout refOrders w8σ w8L (w8G refOrders).toGraph w8K ∧
    LifetimeOrdered (w8G refOrders).toGraph (unitData (lbls := w8L) (K := w8K)) ∧
    LifecycleOK (w8G refOrders).toGraph w8σ w8L w8K ∧ LockEdge (w8G refOrders).toGraph w8L w8K ∧
    CorrQ1 (w8G refOrders).toGraph w8L w8K unitData ∧
    CorrQ2 kMutex mutexLayout refOrders w8σ w8L (w8G refOrders).toGraph w8K unitData ∧
    CorrQ3 (unitData (G := (w8G refOrders).toGraph) (lbls := w8L) (K := w8K)) ∧
    CorrQ4 kMutex mutexLayout refOrders w8σ w8L w8K ∧
    CtlAtomic kMutex mutexLayout w8σ w8L ∧ (w8G refOrders).toGraph.Race 7 12 ∧
    ¬ SafeConcurrentTrace pm kMutex mutexLayout refOrders w8σ w8L (w8G refOrders).toGraph w8K
      unitData := by
  have hw := witness_w8 (pm := pm)
  have hno : ¬ HandoffOrdered kMutex mutexLayout refOrders w8σ w8L (w8G refOrders).toGraph w8K :=
    fun h => absurd (h 6 11 ⟨3, .write, none, .modify⟩ ⟨3, .write, none, .modify⟩
      (conflictPair_of (by decide) (by decide) (by decide) rfl (by decide) (by decide)
        (by decide))
      (by decide) (kMutex_noConf 3)) (by decide +kernel)
  exact ⟨hw.2.1, hw.2.2.2.1, finitePast_fin _, by decide,
    orderLegal_of_check (by decide +kernel),
    stepOrders_of_check (listK_none (by decide)) (by decide +kernel),
    unitLeaf_of_check (listK_none (by decide)) (by decide +kernel) (by decide +kernel)
      (by decide +kernel),
    confinedExcl_none kMutex_noConf,
    confinedHandoff_of_check (by decide +kernel), syncOrdered_of_check (by decide +kernel),
    by decide, hno, ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩,
    hw.2.2.1.lifecycle, mutex_lockEdge hw.2.2.2.2.1 (by decide) (by decide),
    by unfold CorrQ1; decide +kernel,
    corrQ2_of_check (listK_none (by decide)) (by decide +kernel),
    by unfold CorrQ3; decide +kernel, corrQ4_of_check (by decide +kernel),
    ctlAtomic_of_check (by decide), by decide +kernel,
    fun h => hno h.handoff⟩

/-- **Witness S3**, twin W9 (C47, C49; C51, C52): W9 (`witness_w9`), W8 with `c1 : terminate` and
`c0 : join(c1)` before the `resetLock`, is a `SafeConcurrentTrace`; Q1–Q4 and reading 12 hold; 14d
applies: no pair of events races. -/
theorem witness_s3_w9 :
    SafeConcurrentTrace pm kMutex mutexLayout refOrders w9σ w9L w9G.toGraph w9K unitData ∧
    CorrQ1 w9G.toGraph w9L w9K unitData ∧
    CorrQ2 kMutex mutexLayout refOrders w9σ w9L w9G.toGraph w9K unitData ∧
    CorrQ3 (unitData (G := w9G.toGraph) (lbls := w9L) (K := w9K)) ∧
    CorrQ4 kMutex mutexLayout refOrders w9σ w9L w9K ∧
    CtlAtomic kMutex mutexLayout w9σ w9L ∧ ∀ a b, ¬ w9G.toGraph.Race a b := by
  have hw := witness_w9 (pm := pm)
  have hS : SafeConcurrentTrace pm kMutex mutexLayout refOrders w9σ w9L w9G.toGraph w9K unitData :=
    ⟨hw.2.1, hw.2.2.2.1, finitePast_fin _, by decide,
      orderLegal_of_check (by decide +kernel),
      stepOrders_of_check (listK_none (by decide)) (by decide +kernel),
      unitLeaf_of_check (listK_none (by decide)) (by decide +kernel) (by decide +kernel)
        (by decide +kernel),
      confinedExcl_none kMutex_noConf,
      confinedHandoff_of_check (by decide +kernel), syncOrdered_of_check (by decide +kernel),
      by decide, handoffOrdered_of_check (by decide +kernel),
      ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩, hw.2.2.1.lifecycle,
      mutex_lockEdge hw.2.2.2.2.1 (by decide) (by decide)⟩
  have hq1 : CorrQ1 w9G.toGraph w9L w9K unitData := by unfold CorrQ1; decide +kernel
  have hq2 : CorrQ2 kMutex mutexLayout refOrders w9σ w9L w9G.toGraph w9K unitData :=
    corrQ2_of_check (listK_none (by decide)) (by decide +kernel)
  have hq3 : CorrQ3 (unitData (G := w9G.toGraph) (lbls := w9L) (K := w9K)) := by
    unfold CorrQ3; decide +kernel
  have h12 : CtlAtomic kMutex mutexLayout w9σ w9L := ctlAtomic_of_check (by decide)
  exact ⟨hS, hq1, hq2, hq3, corrQ4_of_check (by decide +kernel), h12,
    no_race (testKS_dd _ _ _) mutexStatics_ok hw.1 hw.2.2.1 hS hq1 hq2 hq3 h12⟩

/-- **Witness S3**, W10 (C32.1, C40, C48; C51 item 2(f)): the execution and graph of W7 with the
relaxed triple (`witness_w10`): all steps are `ok`; `HandoffOrdered` fails for the pair of the
`write3` of `T` of `c1` (step 6) and that of `c0` (step 10), whose marker `unlock(e)` has no `hb` to
the write of `c0`; the edge of `LockOrder` fails: the `acquire` of `c0` (step 9) reads by `rf` the
`unlock` of `c1` (step 7), which is not `hb`-before it. Every other condition holds; Q1–Q4 and
reading 12 hold. The two writes race. Admitted twin: W7 (`witness_s2_w7`). -/
theorem witness_s3_w10 :
    EncapRun pm kMutex mutexLayout w7σ w7L ∧ (w7G rlxOrders).toGraph.EventConsistent ∧
    (w7G rlxOrders).toGraph.FiniteCausalPast ∧ OrdinaryAtomicOK kMutex w7σ w7L ∧
    (w7G rlxOrders).toGraph.OrderLegal ∧
    StepOrders kMutex mutexLayout rlxOrders w7σ w7L (w7G rlxOrders).toGraph w7K ∧
    UnitLeaf kMutex mutexLayout rlxOrders w7σ w7L (w7G rlxOrders).toGraph w7K ∧
    ConfinedExcl kMutex w7σ w7L ∧
    ConfinedHandoff kMutex mutexLayout rlxOrders w7σ w7L (w7G rlxOrders).toGraph w7K ∧
    SyncOrdered kMutex mutexLayout rlxOrders w7σ w7L (w7G rlxOrders).toGraph w7K ∧
    InheritedLegal kMutex w7L ∧
    ¬ HandoffOrdered kMutex mutexLayout rlxOrders w7σ w7L (w7G rlxOrders).toGraph w7K ∧
    LifetimeOrdered (w7G rlxOrders).toGraph (unitData (lbls := w7L) (K := w7K)) ∧
    LifecycleOK (w7G rlxOrders).toGraph w7σ w7L w7K ∧
    ¬ LockEdge (w7G rlxOrders).toGraph w7L w7K ∧
    CorrQ1 (w7G rlxOrders).toGraph w7L w7K unitData ∧
    CorrQ2 kMutex mutexLayout rlxOrders w7σ w7L (w7G rlxOrders).toGraph w7K unitData ∧
    CorrQ3 (unitData (G := (w7G rlxOrders).toGraph) (lbls := w7L) (K := w7K)) ∧
    CorrQ4 kMutex mutexLayout rlxOrders w7σ w7L w7K ∧
    CtlAtomic kMutex mutexLayout w7σ w7L ∧ (w7G rlxOrders).toGraph.Race 7 11 ∧
    ¬ SafeConcurrentTrace pm kMutex mutexLayout rlxOrders w7σ w7L (w7G rlxOrders).toGraph w7K
      unitData := by
  have hw := witness_w10.1
  have hno : ¬ HandoffOrdered kMutex mutexLayout rlxOrders w7σ w7L (w7G rlxOrders).toGraph w7K :=
    fun h => absurd (h 6 10 ⟨3, .write, none, .modify⟩ ⟨3, .write, none, .modify⟩
      (conflictPair_of (by decide) (by decide) (by decide) rfl (by decide) (by decide)
        (by decide))
      (by decide) (kMutex_noConf 3)) (by decide +kernel)
  have hle : ¬ LockEdge (w7G rlxOrders).toGraph w7L w7K := fun h =>
    absurd (h 0 7 9 ⟨1, .inl rfl⟩ ⟨0, rfl⟩ 8 10 rfl rfl (by decide +kernel)) (by decide +kernel)
  exact ⟨w7_run, hw.1, finitePast_fin _, by decide,
    orderLegal_of_check (by decide +kernel),
    stepOrders_of_check (listK_none (by decide)) (by decide +kernel),
    unitLeaf_of_check (listK_none (by decide)) (by decide +kernel) (by decide +kernel)
      (by decide +kernel),
    confinedExcl_none kMutex_noConf,
    confinedHandoff_of_check (by decide +kernel), syncOrdered_of_check (by decide +kernel),
    by decide, hno, ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩,
    hw.2.1.lifecycle, hle, by unfold CorrQ1; decide +kernel,
    corrQ2_of_check (listK_none (by decide)) (by decide +kernel),
    by unfold CorrQ3; decide +kernel, corrQ4_of_check (by decide +kernel),
    ctlAtomic_of_check (by decide), by decide +kernel,
    fun h => hno h.handoff⟩

end Ern.ConcurrencyModel
