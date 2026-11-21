import Ern.ConcurrencyModel.WitnessSafe
import Ern.ConcurrencyModel.WitnessAtomic

/-!
# Witnesses S4–S8: shared-mutation disciplines and storage reuse (C35, C42, C51, C52)

Executions from the initial state of Spec 1 §47 under the test contract of the atomic witnesses
(`WitnessAtomic`): the value `V` with the leaves `A` (place 1, `Atomic(4, 4)`), `S` (place 3,
`Synchronized`), `C` (place 4, `Confined`) and `U` (place 5, `SharedMutable` without class);
`root` (authority 0) is the root authority of `V`, held by the base frame of `c0`. Each step is an
`ok` step; each execution is an `EncapsulatedTrace` with a hand-written graph, its correspondence
K1–K4 and the data of reading 9 (storage identities: the place of the accessed storage; no initial
write). A trace that is not safe states the condition that fails, every other condition, Q1–Q3
(unless stated) and the race; each has an admitted twin, a `SafeConcurrentTrace` to which 14d
applies.

Graphs: an access of a leaf `l` carries the range `⟨8 l, 8⟩`; the atomic unit of a leaf is the leaf
itself. The other steps are pure authority markers, except the lifecycle events and, in S8, the
validity events of `enterFrame` and `exitFrame` (complement of fragment F).
-/

namespace Ern.ConcurrencyModel

open Ern.MemoryModel Ern.MemoryModel.Access Events

variable {pm : ProviderMeta}

set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

/-! ## Material -/

/-- The only `Confined` leaf of the test contract is `C` (C35). -/
theorem kAtomic_conf : ∀ l, ConfinedLeaf kAtomic l → l ∈ [4] := fun l h => by
  unfold ConfinedLeaf at h; simp only [testKS, atomicDisc] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · rename_i e; simp [e]
      · split at h <;> cases h

/-- The range of the leaf `l`. -/
def rLeaf (l : Nat) : Range := ⟨8 * l, 8⟩

/-- A pure authority event of context `c` at step `k`. -/
def pEv (c k : Nat) : Event Nat Nat Nat Nat := ⟨c, ⟨k, 0⟩, .marks none none⟩
/-- A lifecycle event of context `c` at step `k`, position `p`. -/
def lEv (c k p : Nat) (r : SyncRole Nat) : Event Nat Nat Nat Nat :=
  ⟨c, ⟨k, p⟩, .marks none (some r)⟩
/-- An access event of context `c` at step `k`. -/
def accEv (c k : Nat) (a : Acc Nat Nat) : Event Nat Nat Nat Nat :=
  ⟨c, ⟨k, 0⟩, .marks (some a) none⟩
/-- A validity event of context `c` at step `k`: begin (`true`) or end of the storage `x`. -/
def valEv (c k : Nat) (b : Bool) (x : Nat) : Event Nat Nat Nat Nat := ⟨c, ⟨k, 0⟩, .validity ⟨b, x⟩⟩

/-- `c0 : derive(root, m, {l})`, authority 1 (O1). -/
def shD (l : Nat) (m : Mode) : SC := v0.set (deriveEff (v0.view 0) 0 [l] m)
/-- `spawn c1` yielding authority 1 (C4). -/
def shS (l : Nat) (m : Mode) : SC := spawnEff (shD l m) 0 [1] []
/-- `c : write3` or `writeShared` of `{l}` (O10, O11, C39). -/
def wrS (s : SC) (c l : Nat) : SC := s.set (write3Eff (s.view c) [l])
/-- `c : read3` (O9). -/
def rdS (s : SC) (c : Nat) : SC := s.set (s.view c)
/-- `c : release(a)` (O3). -/
def relS (s : SC) (c a : Nat) : SC := s.set (releaseEff (s.view c) a)

/-- The graph of a two-access execution: `derive`, `spawn(c1)`, `start(c1)`, the access `xa` of
context `ca` (step 2), the access `xb` of context `cb` (step 3). -/
def pairG (ca cb : Nat) (xa xb : Acc Nat Nat) (rf : List (Fin 5 × Fin 5)) :
    ListGraph 5 Nat Nat Nat Nat where
  ev i := match i.val with
    | 0 => pEv 0 0 | 1 => lEv 0 1 0 (.spawn 1) | 2 => lEv 1 1 1 (.start 1)
    | 3 => accEv ca 2 xa | _ => accEv cb 3 xb
  uRange := rLeaf
  rf := rf
  mo := []

/-- The correspondence of a two-access execution. -/
def pairK : StepEvents (Fin 5) := listK [0, 1, 3, 4] [(1, 2)] []

/-- The graph of a joined execution: `derive`, `spawn(c1)`, `start(c1)`, the access `xa` of `c1`
(step 2), `release`, `terminate`, `complete(c1)`, `join(c1)`, the access `xb` of `c0` (step 6). -/
def joinG (xa xb : Acc Nat Nat) : ListGraph 9 Nat Nat Nat Nat where
  ev i := match i.val with
    | 0 => pEv 0 0 | 1 => lEv 0 1 0 (.spawn 1) | 2 => lEv 1 1 1 (.start 1) | 3 => accEv 1 2 xa
    | 4 => pEv 1 3 | 5 => pEv 1 4 | 6 => lEv 1 4 1 (.complete 1) | 7 => lEv 0 5 0 (.join 1)
    | _ => accEv 0 6 xb
  uRange := rLeaf
  rf := []
  mo := []

/-- The correspondence of a joined execution. -/
def joinK : StepEvents (Fin 9) := listK [0, 1, 3, 4, 5, 7, 8] [(1, 2)] [(1, 6)]

/-- The data of reading 9 of a single storage `x`: every access has the identity `x`. -/
abbrev leafData {n : Nat} {G : Events.Graph (Fin n) Nat Nat Nat Nat} {lbls : List Label}
    {K : StepEvents (Fin n)} (x : Nat) : AccessData G lbls K :=
  noInit fun _ => x

/-! ## S4: inherited `writeShared` on an unclassified leaf -/

/-- The labels of S4. -/
def s4L : List Label :=
  [.kernel 0 (.derive 0 [5] .observe), .spawn 0 [1] [], .kernel 1 (.writeShared 1 [5]),
   .kernel 0 (.writeShared 0 [5])]

/-- The states of S4. -/
def s4σ : Nat → SC × SyncReg × ArenaReg
  | 0 => (v0, [], []) | 1 => (shD 5 .observe, [], []) | 2 => (shS 5 .observe, [], [])
  | 3 => (wrS (shS 5 .observe) 1 5, [], []) | _ => (wrS (wrS (shS 5 .observe) 1 5) 0 5, [], [])

/-- The graph of S4: the two non-atomic writes of `U`. -/
def s4G : ListGraph 5 Nat Nat Nat Nat :=
  pairG 1 0 (.plain (rLeaf 5) .write) (.plain (rLeaf 5) .write) []

/-- S4 is an `EncapsulatedTrace` with named states from the initial state (C51.1). -/
theorem s4_run : EncapRun pm kAtomic mutexLayout s4σ s4L := by
  refine encapRun_of_steps fun i hi lbl hl => ?_
  match i, hi with
  | 0, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 1, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .spawn (.ok (by decide))⟩
  | 2, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 3, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩

/-- **Witness S4** (C35: "concurrent evaluation of `writeShared` over a nonempty region is `reject`
if any targeted leaf lacks a selected `K_C.SharedDiscipline` class"; C51 item 2(e)):
`o := derive(root, Observe, {U})`; `spawn c1` yielding `o`; `c1` and then `c0` run the inherited
`writeShared` on `{U}`, through `o` and through `root`. All steps are `ok` in the kernel; (e) fails
for both writes; every other condition of the safe trace holds; Q1, Q3 and reading 12 hold; Q2
fails: an inherited `writeShared` outside the table has no access in 11e. The two writes race.
Admitted twin: `witness_s4_twin`. -/
theorem witness_s4 :
    EncapRun pm kAtomic mutexLayout s4σ s4L ∧ s4G.toGraph.EventConsistent ∧
    s4G.toGraph.FiniteCausalPast ∧ OrdinaryAtomicOK kAtomic s4σ s4L ∧
    ConfinedExcl kAtomic s4σ s4L ∧
    ConfinedHandoff kAtomic mutexLayout refOrders s4σ s4L s4G.toGraph pairK ∧
    SyncOrdered kAtomic mutexLayout refOrders s4σ s4L s4G.toGraph pairK ∧
    ¬ InheritedLegal kAtomic s4L ∧
    HandoffOrdered kAtomic mutexLayout refOrders s4σ s4L s4G.toGraph pairK ∧
    LifetimeOrdered s4G.toGraph (leafData (lbls := s4L) (K := pairK) 5) ∧
    LifecycleOK s4G.toGraph s4σ s4L pairK ∧ LockEdge s4G.toGraph s4L pairK ∧
    CorrQ1 s4G.toGraph s4L pairK (leafData 5) ∧
    ¬ CorrQ2 kAtomic mutexLayout refOrders s4σ s4L s4G.toGraph pairK (leafData 5) ∧
    CorrQ3 (leafData (G := s4G.toGraph) (lbls := s4L) (K := pairK) 5) ∧
    CtlAtomic kAtomic mutexLayout s4σ s4L ∧ s4G.toGraph.Race 3 4 ∧
    ¬ SafeConcurrentTrace pm kAtomic mutexLayout refOrders s4σ s4L s4G.toGraph pairK
      (leafData 5) := by
  have hK : Corresponds s4G.toGraph s4σ s4L pairK :=
    corresponds_of_check _ _ _ [(1, 1)] _ _ _ (by decide +kernel) (by decide)
  have hne : ¬ InheritedLegal kAtomic s4L := fun h => absurd (h 2 (by decide)) (by decide)
  have hq2 : ¬ CorrQ2 kAtomic mutexLayout refOrders s4σ s4L s4G.toGraph pairK (leafData 5) :=
    fun h => by
      obtain ⟨x, y, hx, -, -, -, -⟩ := h 2 3 3 4 rfl rfl (by decide +kernel) rfl
      have hm := mem_stepAcc hx
      have h2 : stepAcc kAtomic mutexLayout refOrders s4σ s4L 2 = [] := by decide
      rw [h2] at hm; cases hm
  exact ⟨s4_run, by decide +kernel, finitePast_fin _, by decide,
    confinedExcl_of_check [4] 2 kAtomic_conf (by decide) (by decide +kernel),
    confinedHandoff_of_check (by decide +kernel), syncOrdered_of_check (by decide +kernel), hne,
    handoffOrdered_of_check (by decide +kernel),
    ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩, hK.lifecycle,
    lockEdge_none (by decide), by unfold CorrQ1; decide +kernel, hq2,
    by unfold CorrQ3; decide +kernel, ctlAtomic_of_check (by decide), by decide +kernel,
    fun h => hne h.inherited⟩

/-! ## The joined executions on one leaf -/

/-- The states of a joined execution on the leaf `l` with the derived mode `m`: the access of `c1`
(effect `e1`), `release`, `terminate`, `join`, the access of `c0` (effect `e0`). -/
def joinσ (l : Nat) (m : Mode) (e1 : SC → SC) (e0 : SC → SC) : Nat → SC × SyncReg × ArenaReg
  | 0 => (v0, [], []) | 1 => (shD l m, [], []) | 2 => (shS l m, [], [])
  | 3 => (e1 (shS l m), [], []) | 4 => (relS (e1 (shS l m)) 1 1, [], [])
  | 5 => (termEffC (relS (e1 (shS l m)) 1 1) 1, [], [])
  | 6 => (termEffC (relS (e1 (shS l m)) 1 1) 1, [], [])
  | _ => (e0 (termEffC (relS (e1 (shS l m)) 1 1) 1), [], [])

/-- The labels of S4's twin: S4 on `S` with `release`, `terminate` and `join` before the write of
`c0`. -/
def s4tL : List Label :=
  [.kernel 0 (.derive 0 [3] .observe), .spawn 0 [1] [], .kernel 1 (.writeShared 1 [3]),
   .kernel 1 (.release 1), .terminate 1, .join 0 1, .kernel 0 (.writeShared 0 [3])]

/-- The states of S4's twin. -/
def s4tσ : Nat → SC × SyncReg × ArenaReg :=
  joinσ 3 .observe (fun s => wrS s 1 3) (fun s => wrS s 0 3)

/-- The graph of S4's twin. -/
def s4tG : ListGraph 9 Nat Nat Nat Nat := joinG (.plain (rLeaf 3) .write) (.plain (rLeaf 3) .write)

/-- S4's twin is an `EncapsulatedTrace` with named states from the initial state (C51.1). -/
theorem s4t_run : EncapRun pm kAtomic mutexLayout s4tσ s4tL := by
  refine encapRun_of_steps fun i hi lbl hl => ?_
  match i, hi with
  | 0, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 1, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .spawn (.ok (by decide))⟩
  | 2, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 3, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 4, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .terminate (.ok (by decide))⟩
  | 5, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .join (.ok (by decide) (by decide))⟩
  | 6, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩

/-- **Witness S4**, admitted twin (C35–C38; C51, C52): the inherited `writeShared` of S4 on the
`Synchronized` leaf `S`, `c1` releasing `o` and terminating, `c0` joining `c1` before its write:
the inherited steps satisfy the table (e); the execution is a `SafeConcurrentTrace`; Q1–Q3 and
reading 12 hold; 14d applies: no pair of events races. -/
theorem witness_s4_twin :
    SafeConcurrentTrace pm kAtomic mutexLayout refOrders s4tσ s4tL s4tG.toGraph joinK
      (leafData 3) ∧
    CorrQ1 s4tG.toGraph s4tL joinK (leafData 3) ∧
    CorrQ2 kAtomic mutexLayout refOrders s4tσ s4tL s4tG.toGraph joinK (leafData 3) ∧
    CorrQ3 (leafData (G := s4tG.toGraph) (lbls := s4tL) (K := joinK) 3) ∧
    CtlAtomic kAtomic mutexLayout s4tσ s4tL ∧ ∀ a b, ¬ s4tG.toGraph.Race a b := by
  have hK : Corresponds s4tG.toGraph s4tσ s4tL joinK :=
    corresponds_of_check _ _ _ [(1, 1)] _ _ _ (by decide +kernel) (by decide)
  have hS : SafeConcurrentTrace pm kAtomic mutexLayout refOrders s4tσ s4tL s4tG.toGraph joinK
      (leafData 3) :=
    ⟨s4t_run, by decide +kernel, finitePast_fin _, by decide,
      confinedExcl_of_check [4] 2 kAtomic_conf (by decide) (by decide +kernel),
      confinedHandoff_of_check (by decide +kernel), syncOrdered_of_check (by decide +kernel),
      by decide, handoffOrdered_of_check (by decide +kernel),
      ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩, hK.lifecycle,
      lockEdge_none (by decide)⟩
  have hq1 : CorrQ1 s4tG.toGraph s4tL joinK (leafData 3) := by unfold CorrQ1; decide +kernel
  have hq2 : CorrQ2 kAtomic mutexLayout refOrders s4tσ s4tL s4tG.toGraph joinK (leafData 3) :=
    corrQ2_of_check (listK_none (by decide)) (by decide +kernel)
  have hq3 : CorrQ3 (leafData (G := s4tG.toGraph) (lbls := s4tL) (K := joinK) 3) := by
    unfold CorrQ3; decide +kernel
  have h12 : CtlAtomic kAtomic mutexLayout s4tσ s4tL := ctlAtomic_of_check (by decide)
  exact ⟨hS, hq1, hq2, hq3, h12,
    no_race (testKS_dd _ _ _) atomicStatics_ok rfl hK hS hq1 hq2 hq3 h12⟩

/-! ## S5: concurrent `writeShared` on `Synchronized` storage -/

/-- The labels of S5. -/
def s5L : List Label :=
  [.kernel 0 (.derive 0 [3] .observe), .spawn 0 [1] [], .writeShared 1 1 [3] none .store,
   .writeShared 0 0 [3] none .store]

/-- The states of S5. -/
def s5σ : Nat → SC × SyncReg × ArenaReg
  | 0 => (v0, [], []) | 1 => (shD 3 .observe, [], []) | 2 => (shS 3 .observe, [], [])
  | 3 => (wrS (shS 3 .observe) 1 3, [], []) | _ => (wrS (wrS (shS 3 .observe) 1 3) 0 3, [], [])

/-- The graph of S5: the two non-atomic writes of `S`. -/
def s5G : ListGraph 5 Nat Nat Nat Nat :=
  pairG 1 0 (.plain (rLeaf 3) .write) (.plain (rLeaf 3) .write) []

/-- S5 is an `EncapsulatedTrace` with named states from the initial state (C51.1). -/
theorem s5_run : EncapRun pm kAtomic mutexLayout s5σ s5L := by
  refine encapRun_of_steps fun i hi lbl hl => ?_
  match i, hi with
  | 0, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 1, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .spawn (.ok (by decide))⟩
  | 2, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .writeShared (.ok ⟨by decide, by decide, fun h => absurd rfl h⟩)⟩
  | 3, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .writeShared (.ok ⟨by decide, by decide, fun h => absurd rfl h⟩)⟩

/-- **Witness S5** (C44: "Conflicting **non-atomic** `writeShared` operations on `Synchronized`
storage performed under shared compatible `Observe` rights are **not** covered by the
exclusive-handoff premise"; C51 item 2(d); C52): `o := derive(root, Observe, {S})`; `spawn c1`
yielding `o`; `c1` and then `c0` run the concurrent `writeShared` of kind `store` without
annotation on `{S}`, through `o` and through `root`. (d) fails: the two writes form a
non-exclusive pair in conflict on `S` not ordered by `hb`. Every other condition holds; Q1–Q3 and
reading 12 hold. The two writes race. Admitted twin: `witness_s5_twin`. -/
theorem witness_s5 :
    EncapRun pm kAtomic mutexLayout s5σ s5L ∧ s5G.toGraph.EventConsistent ∧
    s5G.toGraph.FiniteCausalPast ∧ OrdinaryAtomicOK kAtomic s5σ s5L ∧
    ConfinedExcl kAtomic s5σ s5L ∧
    ConfinedHandoff kAtomic mutexLayout refOrders s5σ s5L s5G.toGraph pairK ∧
    ¬ SyncOrdered kAtomic mutexLayout refOrders s5σ s5L s5G.toGraph pairK ∧
    InheritedLegal kAtomic s5L ∧
    HandoffOrdered kAtomic mutexLayout refOrders s5σ s5L s5G.toGraph pairK ∧
    LifetimeOrdered s5G.toGraph (leafData (lbls := s5L) (K := pairK) 3) ∧
    LifecycleOK s5G.toGraph s5σ s5L pairK ∧ LockEdge s5G.toGraph s5L pairK ∧
    CorrQ1 s5G.toGraph s5L pairK (leafData 3) ∧
    CorrQ2 kAtomic mutexLayout refOrders s5σ s5L s5G.toGraph pairK (leafData 3) ∧
    CorrQ3 (leafData (G := s5G.toGraph) (lbls := s5L) (K := pairK) 3) ∧
    CtlAtomic kAtomic mutexLayout s5σ s5L ∧ s5G.toGraph.Race 3 4 ∧
    ¬ SafeConcurrentTrace pm kAtomic mutexLayout refOrders s5σ s5L s5G.toGraph pairK
      (leafData 3) := by
  have hK : Corresponds s5G.toGraph s5σ s5L pairK :=
    corresponds_of_check _ _ _ [(1, 1)] _ _ _ (by decide +kernel) (by decide)
  have hno : ¬ SyncOrdered kAtomic mutexLayout refOrders s5σ s5L s5G.toGraph pairK := fun h =>
    absurd (h 2 3 ⟨3, .write, none, .observe⟩ ⟨3, .write, none, .observe⟩
      (conflictPair_of (by decide) (by decide) (by decide) rfl (by decide) (by decide)
        (by decide))
      (by decide) (by decide) 3 4 rfl rfl) (by decide +kernel)
  exact ⟨s5_run, by decide +kernel, finitePast_fin _, by decide,
    confinedExcl_of_check [4] 2 kAtomic_conf (by decide) (by decide +kernel),
    confinedHandoff_of_check (by decide +kernel), hno, by decide,
    handoffOrdered_of_check (by decide +kernel),
    ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩, hK.lifecycle,
    lockEdge_none (by decide), by unfold CorrQ1; decide +kernel,
    corrQ2_of_check (listK_none (by decide)) (by decide +kernel),
    by unfold CorrQ3; decide +kernel, ctlAtomic_of_check (by decide), by decide +kernel,
    fun h => hno h.synchronized⟩

/-- The labels of S5's twin: `c1` writes, releases `o` and terminates; `c0` joins `c1` and
writes. -/
def s5tL : List Label :=
  [.kernel 0 (.derive 0 [3] .observe), .spawn 0 [1] [], .writeShared 1 1 [3] none .store,
   .kernel 1 (.release 1), .terminate 1, .join 0 1, .writeShared 0 0 [3] none .store]

/-- The states of S5's twin. -/
def s5tσ : Nat → SC × SyncReg × ArenaReg :=
  joinσ 3 .observe (fun s => wrS s 1 3) (fun s => wrS s 0 3)

/-- S5's twin is an `EncapsulatedTrace` with named states from the initial state (C51.1). -/
theorem s5t_run : EncapRun pm kAtomic mutexLayout s5tσ s5tL := by
  refine encapRun_of_steps fun i hi lbl hl => ?_
  match i, hi with
  | 0, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 1, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .spawn (.ok (by decide))⟩
  | 2, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .writeShared (.ok ⟨by decide, by decide, fun h => absurd rfl h⟩)⟩
  | 3, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 4, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .terminate (.ok (by decide))⟩
  | 5, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .join (.ok (by decide) (by decide))⟩
  | 6, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .writeShared (.ok ⟨by decide, by decide, fun h => absurd rfl h⟩)⟩

/-- **Witness S5**, admitted twin (C47, C51 item 2(d), C52): with `c1 : terminate` and `c0 :
join(c1)` before the write of `c0`, the two writes of `S` are ordered by `hb`; the execution is a
`SafeConcurrentTrace`; Q1–Q3 and reading 12 hold; 14d applies: no pair of events races. -/
theorem witness_s5_twin :
    SafeConcurrentTrace pm kAtomic mutexLayout refOrders s5tσ s5tL s4tG.toGraph joinK
      (leafData 3) ∧
    CorrQ1 s4tG.toGraph s5tL joinK (leafData 3) ∧
    CorrQ2 kAtomic mutexLayout refOrders s5tσ s5tL s4tG.toGraph joinK (leafData 3) ∧
    CorrQ3 (leafData (G := s4tG.toGraph) (lbls := s5tL) (K := joinK) 3) ∧
    CtlAtomic kAtomic mutexLayout s5tσ s5tL ∧ ∀ a b, ¬ s4tG.toGraph.Race a b := by
  have hK : Corresponds s4tG.toGraph s5tσ s5tL joinK :=
    corresponds_of_check _ _ _ [(1, 1)] _ _ _ (by decide +kernel) (by decide)
  have hS : SafeConcurrentTrace pm kAtomic mutexLayout refOrders s5tσ s5tL s4tG.toGraph joinK
      (leafData 3) :=
    ⟨s5t_run, by decide +kernel, finitePast_fin _, by decide,
      confinedExcl_of_check [4] 2 kAtomic_conf (by decide) (by decide +kernel),
      confinedHandoff_of_check (by decide +kernel), syncOrdered_of_check (by decide +kernel),
      by decide, handoffOrdered_of_check (by decide +kernel),
      ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩, hK.lifecycle,
      lockEdge_none (by decide)⟩
  have hq1 : CorrQ1 s4tG.toGraph s5tL joinK (leafData 3) := by unfold CorrQ1; decide +kernel
  have hq2 : CorrQ2 kAtomic mutexLayout refOrders s5tσ s5tL s4tG.toGraph joinK (leafData 3) :=
    corrQ2_of_check (listK_none (by decide)) (by decide +kernel)
  have hq3 : CorrQ3 (leafData (G := s4tG.toGraph) (lbls := s5tL) (K := joinK) 3) := by
    unfold CorrQ3; decide +kernel
  have h12 : CtlAtomic kAtomic mutexLayout s5tσ s5tL := ctlAtomic_of_check (by decide)
  exact ⟨hS, hq1, hq2, hq3, h12,
    no_race (testKS_dd _ _ _) atomicStatics_ok rfl hK hS hq1 hq2 hq3 h12⟩

/-! ## S6: ordinary read of `Atomic` storage under `Observe` -/

/-- The labels of S6. -/
def s6L : List Label :=
  [.kernel 0 (.derive 0 [1] .observe), .spawn 0 [1] [], .writeShared 0 0 [1] (some .release) .store,
   .kernel 1 (.read 1 [1])]

/-- The states of S6. -/
def s6σ : Nat → SC × SyncReg × ArenaReg
  | 0 => (v0, [], []) | 1 => (shD 1 .observe, [], []) | 2 => (shS 1 .observe, [], [])
  | 3 => (wrS (shS 1 .observe) 0 1, [], []) | _ => (rdS (wrS (shS 1 .observe) 0 1) 1, [], [])

/-- The graph of S6: the atomic `release` write of `A` by `c0`, the non-atomic read of `A` by
`c1`, which reads it by `rf`. -/
def s6G : ListGraph 5 Nat Nat Nat Nat :=
  pairG 0 1 (.atomic 1 .release (.write 1)) (.unit 1 (.read 1)) [(3, 4)]

/-- S6 is an `EncapsulatedTrace` with named states from the initial state (C51.1). -/
theorem s6_run : EncapRun pm kAtomic mutexLayout s6σ s6L := by
  refine encapRun_of_steps fun i hi lbl hl => ?_
  match i, hi with
  | 0, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 1, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .spawn (.ok (by decide))⟩
  | 2, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .writeShared (.ok ⟨by decide, by decide, fun h => absurd rfl h⟩)⟩
  | 3, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩

/-- **Witness S6** (C42: "an ordinary `read3` or `write3` on an `Atomic` leaf requires an
**effective and exercisable `Modify`** capability for that leaf"; C51 item 2(b)): `o :=
derive(root, Observe, {A})`; `spawn c1` yielding `o`; `c0 : writeShared` of kind `store` on `{A}`
with `release`; `c1 : read3(A)` through `o`, whose event reads the write of `c0` by `rf`. All steps
are `ok`; (b) fails at the `read3`; every other condition holds; Q1–Q3 and reading 12 hold. The
atomic write and the non-atomic read race. Admitted twin: `witness_s6_twin`. -/
theorem witness_s6 :
    EncapRun pm kAtomic mutexLayout s6σ s6L ∧ s6G.toGraph.EventConsistent ∧
    s6G.toGraph.FiniteCausalPast ∧ ¬ OrdinaryAtomicOK kAtomic s6σ s6L ∧
    ConfinedExcl kAtomic s6σ s6L ∧
    ConfinedHandoff kAtomic mutexLayout refOrders s6σ s6L s6G.toGraph pairK ∧
    SyncOrdered kAtomic mutexLayout refOrders s6σ s6L s6G.toGraph pairK ∧
    InheritedLegal kAtomic s6L ∧
    HandoffOrdered kAtomic mutexLayout refOrders s6σ s6L s6G.toGraph pairK ∧
    LifetimeOrdered s6G.toGraph (leafData (lbls := s6L) (K := pairK) 1) ∧
    LifecycleOK s6G.toGraph s6σ s6L pairK ∧ LockEdge s6G.toGraph s6L pairK ∧
    CorrQ1 s6G.toGraph s6L pairK (leafData 1) ∧
    CorrQ2 kAtomic mutexLayout refOrders s6σ s6L s6G.toGraph pairK (leafData 1) ∧
    CorrQ3 (leafData (G := s6G.toGraph) (lbls := s6L) (K := pairK) 1) ∧
    CtlAtomic kAtomic mutexLayout s6σ s6L ∧ s6G.toGraph.rf 3 4 ∧ s6G.toGraph.Race 3 4 ∧
    ¬ SafeConcurrentTrace pm kAtomic mutexLayout refOrders s6σ s6L s6G.toGraph pairK
      (leafData 1) := by
  have hK : Corresponds s6G.toGraph s6σ s6L pairK :=
    corresponds_of_check _ _ _ [(1, 1)] _ _ _ (by decide +kernel) (by decide)
  have hno : ¬ OrdinaryAtomicOK kAtomic s6σ s6L := fun h => absurd (h 3 (by decide)) (by decide)
  exact ⟨s6_run, by decide +kernel, finitePast_fin _, hno,
    confinedExcl_of_check [4] 2 kAtomic_conf (by decide) (by decide +kernel),
    confinedHandoff_of_check (by decide +kernel), syncOrdered_of_check (by decide +kernel),
    by decide, handoffOrdered_of_check (by decide +kernel),
    ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩, hK.lifecycle,
    lockEdge_none (by decide), by unfold CorrQ1; decide +kernel,
    corrQ2_of_check (listK_none (by decide)) (by decide +kernel),
    by unfold CorrQ3; decide +kernel, ctlAtomic_of_check (by decide), by decide +kernel,
    by decide +kernel, fun h => hno h.ordinary⟩

/-- The labels of S6's twin: the read of `c1` is `readShared(A)` with `acquire`. -/
def s6tL : List Label :=
  [.kernel 0 (.derive 0 [1] .observe), .spawn 0 [1] [], .writeShared 0 0 [1] (some .release) .store,
   .readShared 1 1 1 .acquire 1]

/-- The states of S6's twin. -/
def s6tσ : Nat → SC × SyncReg × ArenaReg
  | 0 => (v0, [], []) | 1 => (shD 1 .observe, [], []) | 2 => (shS 1 .observe, [], [])
  | _ => (wrS (shS 1 .observe) 0 1, [], [])

/-- The graph of S6's twin: the `acquire` read of `A` by `c1` reads the `release` write by `rf`. -/
def s6tG : ListGraph 5 Nat Nat Nat Nat :=
  pairG 0 1 (.atomic 1 .release (.write 1)) (.atomic 1 .acquire (.read 1)) [(3, 4)]

/-- S6's twin is an `EncapsulatedTrace` with named states from the initial state (C51.1). -/
theorem s6t_run : EncapRun pm kAtomic mutexLayout s6tσ s6tL := by
  refine encapRun_of_steps fun i hi lbl hl => ?_
  match i, hi with
  | 0, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 1, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .spawn (.ok (by decide))⟩
  | 2, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .writeShared (.ok ⟨by decide, by decide, fun h => absurd rfl h⟩)⟩
  | 3, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .readShared (.ok ⟨by decide, by decide, ⟨4, 4, rfl⟩, by decide, by decide⟩)⟩

/-- **Witness S6**, admitted twin (C37, C32.1, C42; C51, C52): with `readShared(A)` in `acquire`
instead of `read3`, `sw` relates the write to the read; the execution is a
`SafeConcurrentTrace`; Q1–Q3 and reading 12 hold; 14d applies: no pair of events races. -/
theorem witness_s6_twin :
    SafeConcurrentTrace pm kAtomic mutexLayout refOrders s6tσ s6tL s6tG.toGraph pairK
      (leafData 1) ∧
    CorrQ1 s6tG.toGraph s6tL pairK (leafData 1) ∧
    CorrQ2 kAtomic mutexLayout refOrders s6tσ s6tL s6tG.toGraph pairK (leafData 1) ∧
    CorrQ3 (leafData (G := s6tG.toGraph) (lbls := s6tL) (K := pairK) 1) ∧
    CtlAtomic kAtomic mutexLayout s6tσ s6tL ∧ s6tG.toGraph.SW 3 4 ∧
    ∀ a b, ¬ s6tG.toGraph.Race a b := by
  have hK : Corresponds s6tG.toGraph s6tσ s6tL pairK :=
    corresponds_of_check _ _ _ [(1, 1)] _ _ _ (by decide +kernel) (by decide)
  have hS : SafeConcurrentTrace pm kAtomic mutexLayout refOrders s6tσ s6tL s6tG.toGraph pairK
      (leafData 1) :=
    ⟨s6t_run, by decide +kernel, finitePast_fin _, by decide,
      confinedExcl_of_check [4] 2 kAtomic_conf (by decide) (by decide +kernel),
      confinedHandoff_of_check (by decide +kernel), syncOrdered_of_check (by decide +kernel),
      by decide, handoffOrdered_of_check (by decide +kernel),
      ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩, hK.lifecycle,
      lockEdge_none (by decide)⟩
  have hq1 : CorrQ1 s6tG.toGraph s6tL pairK (leafData 1) := by unfold CorrQ1; decide +kernel
  have hq2 : CorrQ2 kAtomic mutexLayout refOrders s6tσ s6tL s6tG.toGraph pairK (leafData 1) :=
    corrQ2_of_check (listK_none (by decide)) (by decide +kernel)
  have hq3 : CorrQ3 (leafData (G := s6tG.toGraph) (lbls := s6tL) (K := pairK) 1) := by
    unfold CorrQ3; decide +kernel
  have h12 : CtlAtomic kAtomic mutexLayout s6tσ s6tL := ctlAtomic_of_check (by decide)
  exact ⟨hS, hq1, hq2, hq3, h12, by decide +kernel,
    no_race (testKS_dd _ _ _) atomicStatics_ok rfl hK hS hq1 hq2 hq3 h12⟩

/-! ## S7: two contexts with a capability on `Confined` storage -/

/-- The labels of S7. -/
def s7L : List Label :=
  [.kernel 0 (.derive 0 [4] .observe), .spawn 0 [1] [], .writeShared 1 1 [4] none .store,
   .kernel 0 (.read 0 [4])]

/-- The states of S7. -/
def s7σ : Nat → SC × SyncReg × ArenaReg
  | 0 => (v0, [], []) | 1 => (shD 4 .observe, [], []) | 2 => (shS 4 .observe, [], [])
  | 3 => (wrS (shS 4 .observe) 1 4, [], []) | _ => (rdS (wrS (shS 4 .observe) 1 4) 0, [], [])

/-- The graph of S7: the non-atomic write of `C` by `c1`, the non-atomic read of `C` by `c0`. -/
def s7G : ListGraph 5 Nat Nat Nat Nat :=
  pairG 1 0 (.plain (rLeaf 4) .write) (.plain (rLeaf 4) .read) []

/-- S7 is an `EncapsulatedTrace` with named states from the initial state (C51.1). -/
theorem s7_run : EncapRun pm kAtomic mutexLayout s7σ s7L := by
  refine encapRun_of_steps fun i hi lbl hl => ?_
  match i, hi with
  | 0, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 1, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .spawn (.ok (by decide))⟩
  | 2, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .writeShared (.ok ⟨by decide, by decide, fun h => absurd rfl h⟩)⟩
  | 3, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩

/-- **Witness S7** (C35: "On a `Confined` leaf, simultaneous `Observe` capabilities in two contexts
are forbidden by that safe contract"; C51 item 2(c)): `o := derive(root, Observe, {C})`; `spawn c1`
yielding `o`; `c1 : writeShared` of kind `store` without annotation on `{C}`; `c0 : read3(C)`
through `root`. All steps are `ok`; (c) fails: after the `spawn`, `c0` and `c1` both have a present
capability on `C`, and the pair of the write of `c1` and the read of `c0` has no ordered handoff
under the `Confined` criterion (the capability of `c1` never becomes `none`). Every other condition
holds; Q1–Q3 and reading 12 hold. The write and the read race. Admitted twin:
`witness_s7_twin`. -/
theorem witness_s7 :
    EncapRun pm kAtomic mutexLayout s7σ s7L ∧ s7G.toGraph.EventConsistent ∧
    s7G.toGraph.FiniteCausalPast ∧ OrdinaryAtomicOK kAtomic s7σ s7L ∧
    ¬ ConfinedExcl kAtomic s7σ s7L ∧
    ¬ ConfinedHandoff kAtomic mutexLayout refOrders s7σ s7L s7G.toGraph pairK ∧
    SyncOrdered kAtomic mutexLayout refOrders s7σ s7L s7G.toGraph pairK ∧
    InheritedLegal kAtomic s7L ∧
    HandoffOrdered kAtomic mutexLayout refOrders s7σ s7L s7G.toGraph pairK ∧
    LifetimeOrdered s7G.toGraph (leafData (lbls := s7L) (K := pairK) 4) ∧
    LifecycleOK s7G.toGraph s7σ s7L pairK ∧ LockEdge s7G.toGraph s7L pairK ∧
    CorrQ1 s7G.toGraph s7L pairK (leafData 4) ∧
    CorrQ2 kAtomic mutexLayout refOrders s7σ s7L s7G.toGraph pairK (leafData 4) ∧
    CorrQ3 (leafData (G := s7G.toGraph) (lbls := s7L) (K := pairK) 4) ∧
    CtlAtomic kAtomic mutexLayout s7σ s7L ∧ s7G.toGraph.Race 3 4 ∧
    ¬ SafeConcurrentTrace pm kAtomic mutexLayout refOrders s7σ s7L s7G.toGraph pairK
      (leafData 4) := by
  have hK : Corresponds s7G.toGraph s7σ s7L pairK :=
    corresponds_of_check _ _ _ [(1, 1)] _ _ _ (by decide +kernel) (by decide)
  have hne : ¬ ConfinedExcl kAtomic s7σ s7L := fun h =>
    absurd (h 2 (by decide) 4 (by decide) 0 1 (by decide) (by decide)) (by decide)
  have hnh : ¬ ConfinedHandoff kAtomic mutexLayout refOrders s7σ s7L s7G.toGraph pairK := fun h =>
    absurd (h 2 3 ⟨4, .write, none, .observe⟩ ⟨4, .read, none, .observe⟩
      (conflictPair_of (by decide) (by decide) (by decide) rfl (by decide) (by decide)
        (by decide))
      (by decide)) (by decide +kernel)
  exact ⟨s7_run, by decide +kernel, finitePast_fin _, by decide, hne, hnh,
    syncOrdered_of_check (by decide +kernel), by decide,
    handoffOrdered_of_check (by decide +kernel),
    ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩, hK.lifecycle,
    lockEdge_none (by decide), by unfold CorrQ1; decide +kernel,
    corrQ2_of_check (listK_none (by decide)) (by decide +kernel),
    by unfold CorrQ3; decide +kernel, ctlAtomic_of_check (by decide), by decide +kernel,
    fun h => hne h.confinedExcl⟩

/-- The labels of S7's twin: `m := derive(root, Modify, {C})`; `spawn c1` yielding `m`; `c1`
writes, releases `m` and terminates; `c0` joins `c1` and reads. -/
def s7tL : List Label :=
  [.kernel 0 (.derive 0 [4] .modify), .spawn 0 [1] [], .writeShared 1 1 [4] none .store,
   .kernel 1 (.release 1), .terminate 1, .join 0 1, .kernel 0 (.read 0 [4])]

/-- The states of S7's twin. -/
def s7tσ : Nat → SC × SyncReg × ArenaReg :=
  joinσ 4 .modify (fun s => wrS s 1 4) (fun s => rdS s 0)

/-- The graph of S7's twin. -/
def s7tG : ListGraph 9 Nat Nat Nat Nat := joinG (.plain (rLeaf 4) .write) (.plain (rLeaf 4) .read)

/-- S7's twin is an `EncapsulatedTrace` with named states from the initial state (C51.1). -/
theorem s7t_run : EncapRun pm kAtomic mutexLayout s7tσ s7tL := by
  refine encapRun_of_steps fun i hi lbl hl => ?_
  match i, hi with
  | 0, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 1, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .spawn (.ok (by decide))⟩
  | 2, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .writeShared (.ok ⟨by decide, by decide, fun h => absurd rfl h⟩)⟩
  | 3, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 4, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .terminate (.ok (by decide))⟩
  | 5, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .join (.ok (by decide) (by decide))⟩
  | 6, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩

/-- **Witness S7**, admitted twin (C35, C43, C46, C47; C51, C52): with `m := derive(root, Modify,
{C})` yielded to `c1`, which writes, releases `m` and terminates, and `c0` joining `c1` before its
read, at most one context has a capability on `C` at every state; the loss marker of the pair is
`release(m)`, step 3 of `c1` (`FirstCompatible`, `Confined` criterion), and its event is
`hb`-before the read; the execution is a `SafeConcurrentTrace`; Q1–Q3 and reading 12 hold; 14d
applies: no pair of events races. -/
theorem witness_s7_twin :
    SafeConcurrentTrace pm kAtomic mutexLayout refOrders s7tσ s7tL s7tG.toGraph joinK
      (leafData 4) ∧
    CorrQ1 s7tG.toGraph s7tL joinK (leafData 4) ∧
    CorrQ2 kAtomic mutexLayout refOrders s7tσ s7tL s7tG.toGraph joinK (leafData 4) ∧
    CorrQ3 (leafData (G := s7tG.toGraph) (lbls := s7tL) (K := joinK) 4) ∧
    CtlAtomic kAtomic mutexLayout s7tσ s7tL ∧
    FirstCompatible IncompatConfined s7tσ 2 1 4 .observe 3 ∧
    s7tL[3]? = some (.kernel 1 (.release 1)) ∧ s7tG.toGraph.HB 4 8 ∧
    ∀ a b, ¬ s7tG.toGraph.Race a b := by
  have hK : Corresponds s7tG.toGraph s7tσ s7tL joinK :=
    corresponds_of_check _ _ _ [(1, 1)] _ _ _ (by decide +kernel) (by decide)
  have hS : SafeConcurrentTrace pm kAtomic mutexLayout refOrders s7tσ s7tL s7tG.toGraph joinK
      (leafData 4) :=
    ⟨s7t_run, by decide +kernel, finitePast_fin _, by decide,
      confinedExcl_of_check [4] 2 kAtomic_conf (by decide) (by decide +kernel),
      confinedHandoff_of_check (by decide +kernel), syncOrdered_of_check (by decide +kernel),
      by decide, handoffOrdered_of_check (by decide +kernel),
      ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩, hK.lifecycle,
      lockEdge_none (by decide)⟩
  have hq1 : CorrQ1 s7tG.toGraph s7tL joinK (leafData 4) := by unfold CorrQ1; decide +kernel
  have hq2 : CorrQ2 kAtomic mutexLayout refOrders s7tσ s7tL s7tG.toGraph joinK (leafData 4) :=
    corrQ2_of_check (listK_none (by decide)) (by decide +kernel)
  have hq3 : CorrQ3 (leafData (G := s7tG.toGraph) (lbls := s7tL) (K := joinK) 4) := by
    unfold CorrQ3; decide +kernel
  have h12 : CtlAtomic kAtomic mutexLayout s7tσ s7tL := ctlAtomic_of_check (by decide)
  exact ⟨hS, hq1, hq2, hq3, h12, by decide, rfl, by decide +kernel,
    no_race (testKS_dd _ _ _) atomicStatics_ok rfl hK hS hq1 hq2 hq3 h12⟩

/-! ## S8: reuse of bytes by a distinct storage identity -/

/-- The range shared by the locals `X` and `Y`. -/
def rXY : Range := rLeaf 7

/-- `c0 : enterFrame` with one local (O6): `X`, place 7, root authority 1. -/
def s8a : SC := enterEffC v0 0 [] [(none, 0)]
/-- `a := derive(root_X, Modify)`, authority 2. -/
def s8b : SC := s8a.set (deriveEff (s8a.view 0) 1 [7] .modify)
/-- `spawn c1` yielding `a`. -/
def s8c : SC := spawnEff s8b 0 [2] []
/-- `c1 : write3(X)` by `a`, then `c1 : release(a)`. -/
def s8e : SC := relS (wrS s8c 1 7) 1 2
/-- `c0 : exitFrame`, then `c0 : enterFrame` with one local `Y` (place 8, root authority 3). -/
def s8g (s : SC) : SC := enterEffC (exitEffC s 0) 0 [] [(none, 0)]

/-- The labels of S8. -/
def s8L : List Label :=
  [.kernel 0 (.enter [] [(none, 0)]), .kernel 0 (.derive 1 [7] .modify), .spawn 0 [2] [],
   .kernel 1 (.write 2 [7]), .kernel 1 (.release 2), .kernel 0 .exit,
   .kernel 0 (.enter [] [(none, 0)]), .kernel 0 (.write 3 [8])]

/-- The states of S8. -/
def s8σ : Nat → SC × SyncReg × ArenaReg
  | 0 => (v0, [], []) | 1 => (s8a, [], []) | 2 => (s8b, [], []) | 3 => (s8c, [], [])
  | 4 => (wrS s8c 1 7, [], []) | 5 => (s8e, [], []) | 6 => (exitEffC s8e 0, [], [])
  | 7 => (s8g s8e, [], []) | _ => (wrS (s8g s8e) 0 8, [], [])

/-- The graph of S8: begin of `X`, `derive`, `spawn(c1)`, `start(c1)`, the write of `X` by `c1`,
`release(a)`, end of `X`, begin of `Y`, the write of `Y` by `c0`, on the same bytes. -/
def s8G : ListGraph 9 Nat Nat Nat Nat where
  ev i := match i.val with
    | 0 => valEv 0 0 true 7 | 1 => pEv 0 1 | 2 => lEv 0 2 0 (.spawn 1) | 3 => lEv 1 2 1 (.start 1)
    | 4 => accEv 1 3 (.plain rXY .write) | 5 => pEv 1 4 | 6 => valEv 0 5 false 7
    | 7 => valEv 0 6 true 8 | _ => accEv 0 7 (.plain rXY .write)
  uRange := rLeaf
  rf := []
  mo := []

/-- The correspondence of S8. -/
def s8K : StepEvents (Fin 9) := listK [0, 1, 2, 4, 5, 6, 7, 8] [(1, 3)] []

/-- The storage identities of S8: `X` (7) for the write of `c1`, `Y` (8) for that of `c0`. -/
def s8D : AccessData s8G.toGraph s8L s8K := noInit fun e => if e.val = 4 then 7 else 8

/-- S8 is an `EncapsulatedTrace` with named states from the initial state (C51.1). -/
theorem s8_run : EncapRun pm kAtomic mutexLayout s8σ s8L := by
  refine encapRun_of_steps fun i hi lbl hl => ?_
  match i, hi with
  | 0, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel (.ok (by decide))⟩
  | 1, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 2, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .spawn (.ok (by decide))⟩
  | 3, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 4, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 5, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel (.ok (by decide))⟩
  | 6, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel (.ok (by decide))⟩
  | 7, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩

/-- **Witness S8** (C51, `LifetimeOrdered`: "If bytes are reused for a distinct logical storage
identity, the prior identity's relevant accesses and end-validity must be ordered before new
accesses"; C6: "There is no implicit wait"; C27): `c0 : enterFrame` with a local `X`; `a :=
derive(root_X, Modify)`; `spawn c1` yielding `a`; `c1 : write3(X)` by `a`; `c1 : release(a)`;
`c0 : exitFrame`; `c0 : enterFrame` with a local `Y`; `c0 : write3(Y)`. `X` and `Y` have the same
bytes and distinct identities; the events of the `enterFrame` and `exitFrame` steps are the begin
and end of validity of `X` and the begin of validity of `Y`. All steps are `ok`; `LifetimeOrdered`
fails by L2: the write of `c1` is not `hb`-before the end of validity of `X`. Every other
condition holds; Q1–Q3 and reading 12 hold. The two writes race. Admitted twin:
`witness_s8_twin`. -/
theorem witness_s8 :
    EncapRun pm kAtomic mutexLayout s8σ s8L ∧ s8G.toGraph.EventConsistent ∧
    s8G.toGraph.FiniteCausalPast ∧ OrdinaryAtomicOK kAtomic s8σ s8L ∧
    ConfinedExcl kAtomic s8σ s8L ∧
    ConfinedHandoff kAtomic mutexLayout refOrders s8σ s8L s8G.toGraph s8K ∧
    SyncOrdered kAtomic mutexLayout refOrders s8σ s8L s8G.toGraph s8K ∧
    InheritedLegal kAtomic s8L ∧
    HandoffOrdered kAtomic mutexLayout refOrders s8σ s8L s8G.toGraph s8K ∧
    ¬ LifetimeOrdered s8G.toGraph s8D ∧ ¬ s8G.toGraph.HB 4 6 ∧
    LifecycleOK s8G.toGraph s8σ s8L s8K ∧ LockEdge s8G.toGraph s8L s8K ∧
    CorrQ1 s8G.toGraph s8L s8K s8D ∧
    CorrQ2 kAtomic mutexLayout refOrders s8σ s8L s8G.toGraph s8K s8D ∧ CorrQ3 s8D ∧
    CtlAtomic kAtomic mutexLayout s8σ s8L ∧ s8G.toGraph.Race 4 8 ∧
    ¬ SafeConcurrentTrace pm kAtomic mutexLayout refOrders s8σ s8L s8G.toGraph s8K s8D := by
  have hK : Corresponds s8G.toGraph s8σ s8L s8K :=
    corresponds_of_check _ _ _ [(2, 1)] _ _ _ (by decide +kernel) (by decide)
  have hno : ¬ LifetimeOrdered s8G.toGraph s8D := fun h =>
    absurd (h.before_end 4 6 (by decide) (by decide)) (by decide +kernel)
  exact ⟨s8_run, by decide +kernel, finitePast_fin _, by decide,
    confinedExcl_of_check [4] 2 kAtomic_conf (by decide) (by decide +kernel),
    confinedHandoff_of_check (by decide +kernel), syncOrdered_of_check (by decide +kernel),
    by decide, handoffOrdered_of_check (by decide +kernel), hno, by decide +kernel,
    hK.lifecycle, lockEdge_none (by decide), by unfold CorrQ1; decide +kernel,
    corrQ2_of_check (listK_none (by decide)) (by decide +kernel),
    by unfold CorrQ3; decide +kernel, ctlAtomic_of_check (by decide), by decide +kernel,
    fun h => hno h.lifetime⟩

/-- The labels of S8's twin: `c1` terminates after its `release`, and `c0` joins `c1` before its
`exitFrame`. -/
def s8tL : List Label :=
  [.kernel 0 (.enter [] [(none, 0)]), .kernel 0 (.derive 1 [7] .modify), .spawn 0 [2] [],
   .kernel 1 (.write 2 [7]), .kernel 1 (.release 2), .terminate 1, .join 0 1, .kernel 0 .exit,
   .kernel 0 (.enter [] [(none, 0)]), .kernel 0 (.write 3 [8])]

/-- The states of S8's twin. -/
def s8tσ : Nat → SC × SyncReg × ArenaReg
  | 0 => (v0, [], []) | 1 => (s8a, [], []) | 2 => (s8b, [], []) | 3 => (s8c, [], [])
  | 4 => (wrS s8c 1 7, [], []) | 5 => (s8e, [], []) | 6 => (termEffC s8e 1, [], [])
  | 7 => (termEffC s8e 1, [], []) | 8 => (exitEffC (termEffC s8e 1) 0, [], [])
  | 9 => (s8g (termEffC s8e 1), [], []) | _ => (wrS (s8g (termEffC s8e 1)) 0 8, [], [])

/-- The graph of S8's twin: S8's events with `terminate`, `complete(c1)` and `join(c1)` before the
end of validity of `X`. -/
def s8tG : ListGraph 12 Nat Nat Nat Nat where
  ev i := match i.val with
    | 0 => valEv 0 0 true 7 | 1 => pEv 0 1 | 2 => lEv 0 2 0 (.spawn 1) | 3 => lEv 1 2 1 (.start 1)
    | 4 => accEv 1 3 (.plain rXY .write) | 5 => pEv 1 4 | 6 => pEv 1 5
    | 7 => lEv 1 5 1 (.complete 1) | 8 => lEv 0 6 0 (.join 1) | 9 => valEv 0 7 false 7
    | 10 => valEv 0 8 true 8 | _ => accEv 0 9 (.plain rXY .write)
  uRange := rLeaf
  rf := []
  mo := []

/-- The correspondence of S8's twin. -/
def s8tK : StepEvents (Fin 12) := listK [0, 1, 2, 4, 5, 6, 8, 9, 10, 11] [(1, 3)] [(1, 7)]

/-- The storage identities of S8's twin: `X` (7) for the write of `c1`, `Y` (8) for that of `c0`. -/
def s8tD : AccessData s8tG.toGraph s8tL s8tK := noInit fun e => if e.val = 4 then 7 else 8

/-- S8's twin is an `EncapsulatedTrace` with named states from the initial state (C51.1). -/
theorem s8t_run : EncapRun pm kAtomic mutexLayout s8tσ s8tL := by
  refine encapRun_of_steps fun i hi lbl hl => ?_
  match i, hi with
  | 0, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel (.ok (by decide))⟩
  | 1, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 2, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .spawn (.ok (by decide))⟩
  | 3, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 4, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 5, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .terminate (.ok (by decide))⟩
  | 6, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .join (.ok (by decide) (by decide))⟩
  | 7, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel (.ok (by decide))⟩
  | 8, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel (.ok (by decide))⟩
  | 9, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩

/-- **Witness S8**, admitted twin (C47, C51, C52): with `c1 : terminate` after its `release` and
`c0 : join(c1)` before the `exitFrame`, the write of `X` is `hb`-before the end of validity of `X`,
which is `hb`-before the begin of validity of `Y`; the two writes are ordered by 14a.2; the
execution is a `SafeConcurrentTrace`; Q1–Q3 and reading 12 hold; 14d applies: no pair of events
races. -/
theorem witness_s8_twin :
    SafeConcurrentTrace pm kAtomic mutexLayout refOrders s8tσ s8tL s8tG.toGraph s8tK s8tD ∧
    CorrQ1 s8tG.toGraph s8tL s8tK s8tD ∧
    CorrQ2 kAtomic mutexLayout refOrders s8tσ s8tL s8tG.toGraph s8tK s8tD ∧ CorrQ3 s8tD ∧
    CtlAtomic kAtomic mutexLayout s8tσ s8tL ∧ s8tG.toGraph.HB 4 11 ∧
    ∀ a b, ¬ s8tG.toGraph.Race a b := by
  have hK : Corresponds s8tG.toGraph s8tσ s8tL s8tK :=
    corresponds_of_check _ _ _ [(2, 1)] _ _ _ (by decide +kernel) (by decide)
  have hL : LifetimeOrdered s8tG.toGraph s8tD :=
    ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩
  have hS : SafeConcurrentTrace pm kAtomic mutexLayout refOrders s8tσ s8tL s8tG.toGraph s8tK s8tD :=
    ⟨s8t_run, by decide +kernel, finitePast_fin _, by decide,
      confinedExcl_of_check [4] 2 kAtomic_conf (by decide) (by decide +kernel),
      confinedHandoff_of_check (by decide +kernel), syncOrdered_of_check (by decide +kernel),
      by decide, handoffOrdered_of_check (by decide +kernel), hL, hK.lifecycle,
      lockEdge_none (by decide)⟩
  have hq1 : CorrQ1 s8tG.toGraph s8tL s8tK s8tD := by unfold CorrQ1; decide +kernel
  have hq2 : CorrQ2 kAtomic mutexLayout refOrders s8tσ s8tL s8tG.toGraph s8tK s8tD :=
    corrQ2_of_check (listK_none (by decide)) (by decide +kernel)
  have hq3 : CorrQ3 s8tD := by unfold CorrQ3; decide +kernel
  have h12 : CtlAtomic kAtomic mutexLayout s8tσ s8tL := ctlAtomic_of_check (by decide)
  have hord : s8tG.toGraph.HB 4 11 :=
    lifetime_reuse hL (v := 9) (w := 10) (x := 7) (y := 8) (by decide) (by decide)
      (by decide +kernel) (by decide) rfl (by decide) rfl
  exact ⟨hS, hq1, hq2, hq3, h12, hord,
    no_race (testKS_dd _ _ _) atomicStatics_ok rfl hK hS hq1 hq2 hq3 h12⟩

end Ern.ConcurrencyModel
