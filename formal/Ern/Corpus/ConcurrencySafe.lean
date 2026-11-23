import Ern.ConcurrencyModel.WitnessSafeShared

/-!
# Corpus of the concurrency model: the conditions of the safe trace (test module)

Cases `R49`–`R51` of the concurrency model
(`specs/ERN_Concurrency_Model_Specification_v0.md`), in the form of `Ern.Corpus.ConcurrencyExec`:
each execution is an `EncapsulatedTrace` with named states from the initial state of Spec 1 §47
(`EncapRun`), with a hand-written graph of fragment F, its correspondence (K1–K4) and the data of
reading 9. A trace that is not safe states every condition of `SafeConcurrentTrace`, the one that
fails being negated, the correspondence premises Q1–Q3 (C52), the hypothesis of reading 12
(`CtlAtomic`), and that no pair of events races (C33): each case isolates one condition. A safe
trace states `SafeConcurrentTrace`, Q1–Q3, reading 12, and applies 14d (`no_race`). Each docstring
gives the expected verdict with its clause, the obtained verdict and the twin. This is a test
module: no model module imports it.

What differs from `Ern.Corpus.ConcurrencyExec`:

* the test contract is that of the atomic witnesses (`kAtomic`, `WitnessSafeShared`): `A` is the
  leaf 1 (`Atomic(4, 4)`), `S` the leaf 3 (`Synchronized`), `root` the authority 0, the root
  authority of the value, held by the base frame of `c0`; the executions start from the initial
  state of `atomicStatics`;
* the storage identities of reading 9 are the places of the accessed storage (`leafData`,
  `noInit`), not `Unit`;
* in `R50`, the data of reading 9 mark an initial write: an atomic write of `A` that is the event
  of no step.

Graphs: an access of a leaf `l` carries the range `⟨8 l, 8⟩`; the atomic unit of a leaf is the leaf
itself; the other steps are pure authority markers, except the lifecycle events. Steps are numbered
from 0.
-/

namespace Ern.Corpus.Concurrency

open Ern.MemoryModel Ern.MemoryModel.Access Ern.ConcurrencyModel Events

variable {pm : ProviderMeta}

set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

/-! ## R49: the scope of `HandoffOrdered` (C43–C46; C51 item 2(f)) -/

/-- `c0 : writeShared({S})` of kind `store` without annotation, through `root`, which has the
effective mode `Modify` on `S`; `c0 : derive(root, Observe, {S})`, authority 1; `spawn c1` yielding
authority 1; `c1 : writeShared({S})` of kind `store` without annotation, through authority 1. -/
def r49L : List Label :=
  [.writeShared 0 0 [3] none .store, .kernel 0 (.derive 0 [3] .observe), .spawn 0 [1] [],
   .writeShared 1 1 [3] none .store]

/-- The state after the `derive` of `R49`. -/
def r49s1 : SC := (wrS v0 0 3).set (deriveEff ((wrS v0 0 3).view 0) 0 [3] .observe)

/-- The states of `R49`. -/
def r49σ : Nat → SC × SyncReg × ArenaReg
  | 0 => (v0, [], []) | 1 => (wrS v0 0 3, [], []) | 2 => (r49s1, [], [])
  | 3 => (spawnEff r49s1 0 [1] [], [], []) | _ => (wrS (spawnEff r49s1 0 [1] []) 1 3, [], [])

/-- `R49` is an `EncapsulatedTrace` with named states from the initial state (C51.1). -/
theorem r49_run : EncapRun pm kAtomic mutexLayout r49σ r49L := by
  refine encapRun_of_steps fun i hi lbl hl => ?_
  match i, hi with
  | 0, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .writeShared (.ok ⟨by decide, by decide, fun h => absurd rfl h⟩)⟩
  | 1, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 2, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .spawn (.ok (by decide))⟩
  | 3, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .writeShared (.ok ⟨by decide, by decide, fun h => absurd rfl h⟩)⟩

/-- The accesses of `S` of the two writes: non-atomic writes under `Observe` (11e). -/
abbrev r49w : LeafAccess := ⟨3, .write, none, .observe⟩

/-- The graph of the twin of `R49`: the `derive` has a pure authority marker. -/
def r49TG : ListGraph 5 Nat Nat Nat Nat where
  ev i := match i.val with
    | 0 => accEv 0 0 (.plain (rLeaf 3) .write) | 1 => pEv 0 1 | 2 => lEv 0 2 0 (.spawn 1)
    | 3 => lEv 1 2 1 (.start 1) | _ => accEv 1 3 (.plain (rLeaf 3) .write)
  uRange := rLeaf
  rf := []
  mo := []

/-- The correspondence of the twin of `R49`. -/
def r49TK : StepEvents (Fin 5) := listK [0, 1, 2, 4] [(1, 3)] []

/-- **R49, twin** (safe). The steps of `R49`; the `derive` (step 1) has a pure authority marker.
Expected: a safe trace; the loss marker is the `derive`, `po`-before the `spawn` and so `hb`-before
the write of `c1` (C46, C47). Obtained: the pair of the writes of steps 0 and 3 is exclusive
(reading 13: at step 0, the capability of `c0` on `S` is `Modify`, the access of step 3 uses
`Observe`); its loss marker is the `derive` (step 1, `FirstCompatible`); `SafeConcurrentTrace`,
Q1–Q3 and reading 12 hold; 14d applies: no pair of events races. -/
theorem R49_twin :
    SafeConcurrentTrace pm kAtomic mutexLayout refOrders r49σ r49L r49TG.toGraph r49TK
      (leafData 3) ∧
    CorrQ1 r49TG.toGraph r49L r49TK (leafData 3) ∧
    CorrQ2 kAtomic mutexLayout refOrders r49σ r49L r49TG.toGraph r49TK (leafData 3) ∧
    CorrQ3 (leafData (G := r49TG.toGraph) (lbls := r49L) (K := r49TK) 3) ∧
    CtlAtomic kAtomic mutexLayout r49σ r49L ∧
    ExclusivePair kAtomic r49σ r49L 0 3 r49w r49w ∧
    FirstCompatible IncompatModify r49σ 0 0 3 .observe 1 ∧ ∀ a b, ¬ r49TG.toGraph.Race a b := by
  have hK : Corresponds r49TG.toGraph r49σ r49L r49TK :=
    corresponds_of_check _ _ _ [(2, 1)] _ _ _ (by decide +kernel) (by decide) (by decide +kernel)
  have hS : SafeConcurrentTrace pm kAtomic mutexLayout refOrders r49σ r49L r49TG.toGraph r49TK
      (leafData 3) :=
    ⟨r49_run, by decide +kernel, finitePast_fin _, by decide,
      orderLegal_of_check (by decide +kernel),
      stepOrders_of_check (listK_none (by decide)) (by decide +kernel),
      confinedExcl_of_check [4] 2 kAtomic_conf (by decide) (by decide +kernel),
      confinedHandoff_of_check (by decide +kernel), syncOrdered_of_check (by decide +kernel),
      by decide, handoffOrdered_of_check (by decide +kernel),
      ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩, hK.lifecycle,
      lockEdge_none (by decide)⟩
  have hq1 : CorrQ1 r49TG.toGraph r49L r49TK (leafData 3) := by unfold CorrQ1; decide +kernel
  have hq2 : CorrQ2 kAtomic mutexLayout refOrders r49σ r49L r49TG.toGraph r49TK (leafData 3) :=
    corrQ2_of_check (listK_none (by decide)) (by decide +kernel)
  have hq3 : CorrQ3 (leafData (G := r49TG.toGraph) (lbls := r49L) (K := r49TK) 3) := by
    unfold CorrQ3; decide +kernel
  have h12 : CtlAtomic kAtomic mutexLayout r49σ r49L := ctlAtomic_of_check (by decide)
  exact ⟨hS, hq1, hq2, hq3, h12, by decide +kernel, by decide +kernel,
    no_race (testKS_dd _ _ _) atomicStatics_ok rfl hK hS hq1 hq2 hq3 h12⟩

/-- The graph of `R49`: the `derive` has no event. -/
def r49G : ListGraph 4 Nat Nat Nat Nat where
  ev i := match i.val with
    | 0 => accEv 0 0 (.plain (rLeaf 3) .write) | 1 => lEv 0 2 0 (.spawn 1)
    | 2 => lEv 1 2 1 (.start 1) | _ => accEv 1 3 (.plain (rLeaf 3) .write)
  uRange := rLeaf
  rf := []
  mo := []

/-- The correspondence of `R49`: steps 0, 2, 3 have the events 0, 1, 3; step 1 (the `derive`) has
no event; `start(c1)` is the event 2. -/
def r49K : StepEvents (Fin 4) where
  ev i := if i = 0 then some 0 else if i = 2 then some 1 else if i = 3 then some 3 else none
  start c := if c = 1 then some 2 else none
  complete _ := none

/-- The correspondence of `R49` gives no event past the end of the trace. -/
theorem r49K_none : ∀ i, r49L.length ≤ i → r49K.ev i = none := by
  intro i hi
  have h4 : 4 ≤ i := hi
  simp only [r49K]
  simp only [show ¬ i = 0 by omega, show ¬ i = 2 by omega, show ¬ i = 3 by omega, ite_false]

/-- A step with an event in `R49` is a step of the trace. -/
theorem r49K_lt {i : Nat} {e : Fin 4} (h : r49K.ev i = some e) : i < r49L.length := by
  rcases Nat.lt_or_ge i r49L.length with h4 | h4
  · exact h4
  · rw [r49K_none i h4] at h; cases h

/-- The check of the provenance of the lifecycle roles of `R49` (`roleFromOK`). -/
theorem r49_roles : ∀ e, roleFromOK r49σ r49L r49K e (r49G.toGraph.sync? e) = true := by
  decide +kernel

/-- The correspondence K1–K4 of `R49` (C26–C28, C32.2, C47). -/
theorem r49_corr : Corresponds r49G.toGraph r49σ r49L r49K where
  ctx := fun i h e he =>
    (by decide +kernel : ∀ i (h : i < r49L.length) (e : Fin 4), r49K.ev i = some e →
      r49G.toGraph.ctx e = r49L[i].requester) i h e he
  inj := fun i j e hi hj =>
    (by decide +kernel : ∀ i, i < r49L.length → ∀ j, j < r49L.length → ∀ e : Fin 4,
      r49K.ev i = some e → r49K.ev j = some e → i = j) i (r49K_lt hi) j (r49K_lt hj) e hi hj
  po := fun i j hi hj a b hij hr ha hb =>
    (by decide +kernel : ∀ i (hi : i < r49L.length) j (hj : j < r49L.length) (a b : Fin 4),
      i < j → r49L[i].requester = r49L[j].requester → r49K.ev i = some a →
      r49K.ev j = some b → r49G.toGraph.po a b) i hi j hj a b hij hr ha hb
  spawnRole := by
    rintro s c ⟨h, hs, rfl⟩ e he
    match s, h with
    | 0, _ => rcases hs with ⟨_, _, _, h⟩ | ⟨_, _, _, _, h⟩ <;> cases h
    | 1, _ => rcases hs with ⟨_, _, _, h⟩ | ⟨_, _, _, _, h⟩ <;> cases h
    | 2, _ => revert e; decide +kernel
    | 3, _ => rcases hs with ⟨_, _, _, h⟩ | ⟨_, _, _, _, h⟩ <;> cases h
  start := by
    intro c x hx
    simp only [r49K] at hx
    split at hx
    · rename_i hc; subst hc; cases hx; exact ⟨by decide +kernel, by decide +kernel,
        by decide +kernel⟩
    · cases hx
  complete := fun c x hx => by cases hx
  joinRole := by
    intro q h c d e hl
    match q, h with
    | 0, _ | 1, _ | 2, _ | 3, _ => cases hl
  spawnFrom := (roles_of_check r49_roles).1
  startFrom := (roles_of_check r49_roles).2.1
  completeFrom := (roles_of_check r49_roles).2.2.1
  joinFrom := (roles_of_check r49_roles).2.2.2

/-- **R49** (not safe: `HandoffOrdered` alone fails; no race). The base frame of `c0` holds
`root`; `c0` writes `S` by the concurrent `writeShared` of kind `store` without annotation;
`c0 : derive(root, Observe, {S})`; `spawn c1` yielding the derived authority; `c1` writes `S` in
the same way through it. The `derive` has no event. Expected (C43; C44; C45: "the period
containing `e1` during which `cap(·,c′,l)` is incompatible with the capability used by `e2`"; C46:
"not permission to assume a hidden marker"; C47): `HandoffOrdered` alone fails; no race. The pair
of the writes of steps 0 and 3 is exclusive: at step 0 the capability of `c0` on `S` is `Modify`,
and the access of step 3 uses `Observe`; its loss marker is the `derive` (step 1), which has no
event; the two writes are ordered by the creation edge. Obtained: the execution is an
`EncapsulatedTrace`; the pair is an `ExclusivePair` (reading 13); its loss marker is step 1
(`FirstCompatible`), which has no event; `HandoffOrdered` fails for that pair; every other condition
of the safe trace holds, and Q1–Q3 and reading 12 hold; no pair of events races. Twin:
`R49_twin`. -/
theorem R49 :
    r49σ 0 = (SC.ofS3 (S3.init atomicStatics), [], []) ∧
    EncapRun pm kAtomic mutexLayout r49σ r49L ∧ Corresponds r49G.toGraph r49σ r49L r49K ∧
    r49G.toGraph.EventConsistent ∧ r49G.toGraph.FiniteCausalPast ∧
    OrdinaryAtomicOK kAtomic r49σ r49L ∧ r49G.toGraph.OrderLegal ∧
    StepOrders kAtomic mutexLayout refOrders r49σ r49L r49G.toGraph r49K ∧
    ConfinedExcl kAtomic r49σ r49L ∧
    ConfinedHandoff kAtomic mutexLayout refOrders r49σ r49L r49G.toGraph r49K ∧
    SyncOrdered kAtomic mutexLayout refOrders r49σ r49L r49G.toGraph r49K ∧
    InheritedLegal kAtomic r49L ∧
    ¬ HandoffOrdered kAtomic mutexLayout refOrders r49σ r49L r49G.toGraph r49K ∧
    LifetimeOrdered r49G.toGraph (leafData (lbls := r49L) (K := r49K) 3) ∧
    LifecycleOK r49G.toGraph r49σ r49L r49K ∧ LockEdge r49G.toGraph r49L r49K ∧
    CorrQ1 r49G.toGraph r49L r49K (leafData 3) ∧
    CorrQ2 kAtomic mutexLayout refOrders r49σ r49L r49G.toGraph r49K (leafData 3) ∧
    CorrQ3 (leafData (G := r49G.toGraph) (lbls := r49L) (K := r49K) 3) ∧
    CtlAtomic kAtomic mutexLayout r49σ r49L ∧
    ExclusivePair kAtomic r49σ r49L 0 3 r49w r49w ∧
    FirstCompatible IncompatModify r49σ 0 0 3 .observe 1 ∧ r49K.ev 1 = none ∧
    (∀ a b, ¬ r49G.toGraph.Race a b) ∧
    ¬ SafeConcurrentTrace pm kAtomic mutexLayout refOrders r49σ r49L r49G.toGraph r49K
      (leafData 3) := by
  have hK := r49_corr
  have hno : ¬ HandoffOrdered kAtomic mutexLayout refOrders r49σ r49L r49G.toGraph r49K :=
    fun h => absurd (h 0 3 r49w r49w
      (conflictPair_of (by decide) (by decide) (by decide) rfl (by decide) (by decide)
        (by decide))
      (by decide +kernel) (by decide)) (by decide +kernel)
  exact ⟨rfl, r49_run, hK, by decide +kernel, finitePast_fin _, by decide,
    orderLegal_of_check (by decide +kernel), stepOrders_of_check r49K_none (by decide +kernel),
    confinedExcl_of_check [4] 2 kAtomic_conf (by decide) (by decide +kernel),
    confinedHandoff_of_check (by decide +kernel), syncOrdered_of_check (by decide +kernel),
    by decide, hno,
    ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩, hK.lifecycle,
    lockEdge_none (by decide), by unfold CorrQ1; decide +kernel,
    corrQ2_of_check r49K_none (by decide +kernel), by unfold CorrQ3; decide +kernel,
    ctlAtomic_of_check (by decide), by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, fun h => hno h.handoff⟩

/-! ## R50: the legality of the memory orders of the events (C34, C40; C51 item 2(b)) -/

/-- The graph of the twin of S6 (`writeShared({A})` of kind `store` with `release` by `c0`,
`readShared(A, acquire)` by `c1`, which reads it by `rf`), preceded by an atomic write of `A` with
the order `oi`: an event of `c0` that is the event of no step, first in `mo`. Its origin (C27) is
that of no step of the trace, which has the steps 0 to 3. -/
def r50G (oi : MemOrder) : ListGraph 6 Nat Nat Nat Nat where
  ev i := match i.val with
    | 0 => ⟨0, ⟨4, 0⟩, .marks (some (.atomic 1 oi (.write 0))) none⟩
    | 1 => pEv 0 0 | 2 => lEv 0 1 0 (.spawn 1) | 3 => lEv 1 1 1 (.start 1)
    | 4 => accEv 0 2 (.atomic 1 .release (.write 1))
    | _ => accEv 1 3 (.atomic 1 .acquire (.read 1))
  uRange := rLeaf
  rf := [(4, 5)]
  mo := [(0, 4)]

/-- The correspondence of `R50` and of its twin. -/
def r50K : StepEvents (Fin 6) := listK [1, 2, 4, 5] [(1, 3)] []

/-- The data of reading 9 of `R50`: one storage identity; the event 0 is an initial write. -/
def r50D : AccessData (r50G .acquire).toGraph s6tL r50K :=
  ⟨fun _ => 1, fun e => decide (e.val = 0), by decide +kernel, by decide +kernel⟩

/-- The data of reading 9 of the twin of `R50`. -/
def r50TD : AccessData (r50G .relaxed).toGraph s6tL r50K :=
  ⟨fun _ => 1, fun e => decide (e.val = 0), by decide +kernel, by decide +kernel⟩

/-- **R50** (not safe: the legality of the memory orders alone fails; no race). The steps of the
twin of S6: `o := derive(root, Observe, {A})`; `spawn c1` yielding `o`; `c0 : writeShared({A})` of
kind `store` with `release`; `c1 : readShared(o, A, acquire)`, which reads that write by `rf`. The
graph starts with an atomic write of `A` by `c0` with the order `acquire`, which is the event of no
step: an initial write of the data of reading 9, first in `mo` (C31). Expected (C40; C34: "Legality
of memory-order annotations (C40) is a typing condition on events, separate from these conjuncts";
C51 item 2(b)): the legality of the orders alone fails; no race: `acquire` is not in the row of the
atomic store. Obtained: `OrderLegal` fails; every other condition of the safe trace holds,
`StepOrders` included, and Q1–Q3 and reading 12 hold; no pair of events races. A witness of the
typing of an atomic initial event: it does not say that an initialization is atomic (C31:
"Non-atomic initialization and exclusive writes remain **non-atomic** events"); the value of that
write is free. The event is the event of no step because the order of an `ok` `readShared`,
`writeShared` or compare-and-exchange is legal (`atomic_steps_legal`, `writeShared_legal`): an
illegal order on its event would also make `StepOrders` fail. Twin: `R50_twin`. -/
theorem R50 :
    s6tσ 0 = (SC.ofS3 (S3.init atomicStatics), [], []) ∧
    EncapRun pm kAtomic mutexLayout s6tσ s6tL ∧
    Corresponds (r50G .acquire).toGraph s6tσ s6tL r50K ∧
    (r50G .acquire).toGraph.EventConsistent ∧
    (r50G .acquire).toGraph.FiniteCausalPast ∧ OrdinaryAtomicOK kAtomic s6tσ s6tL ∧
    ¬ (r50G .acquire).toGraph.OrderLegal ∧
    StepOrders kAtomic mutexLayout refOrders s6tσ s6tL (r50G .acquire).toGraph r50K ∧
    ConfinedExcl kAtomic s6tσ s6tL ∧
    ConfinedHandoff kAtomic mutexLayout refOrders s6tσ s6tL (r50G .acquire).toGraph r50K ∧
    SyncOrdered kAtomic mutexLayout refOrders s6tσ s6tL (r50G .acquire).toGraph r50K ∧
    InheritedLegal kAtomic s6tL ∧
    HandoffOrdered kAtomic mutexLayout refOrders s6tσ s6tL (r50G .acquire).toGraph r50K ∧
    LifetimeOrdered (r50G .acquire).toGraph r50D ∧
    LifecycleOK (r50G .acquire).toGraph s6tσ s6tL r50K ∧
    LockEdge (r50G .acquire).toGraph s6tL r50K ∧
    CorrQ1 (r50G .acquire).toGraph s6tL r50K r50D ∧
    CorrQ2 kAtomic mutexLayout refOrders s6tσ s6tL (r50G .acquire).toGraph r50K r50D ∧
    CorrQ3 r50D ∧ CtlAtomic kAtomic mutexLayout s6tσ s6tL ∧
    r50D.init 0 = true ∧ (∀ a b, ¬ (r50G .acquire).toGraph.Race a b) ∧
    ¬ SafeConcurrentTrace pm kAtomic mutexLayout refOrders s6tσ s6tL (r50G .acquire).toGraph
      r50K r50D := by
  have hK : Corresponds (r50G .acquire).toGraph s6tσ s6tL r50K :=
    corresponds_of_check _ _ _ [(1, 1)] _ _ _ (by decide +kernel) (by decide) (by decide +kernel)
  have hno : ¬ (r50G .acquire).toGraph.OrderLegal := fun h => by
    have h3 : Graph.OrderOK Kind.write MemOrder.acquire :=
      h 0 1 .acquire (.write 0) (by decide +kernel)
    rcases h3 with h3 | h3 | h3 <;> cases h3
  exact ⟨rfl, s6t_run, hK, by decide +kernel, finitePast_fin _, by decide, hno,
    stepOrders_of_check (listK_none (by decide)) (by decide +kernel),
    confinedExcl_of_check [4] 2 kAtomic_conf (by decide) (by decide +kernel),
    confinedHandoff_of_check (by decide +kernel), syncOrdered_of_check (by decide +kernel),
    by decide, handoffOrdered_of_check (by decide +kernel),
    ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩, hK.lifecycle,
    lockEdge_none (by decide), by unfold CorrQ1; decide +kernel,
    corrQ2_of_check (listK_none (by decide)) (by decide +kernel),
    by unfold CorrQ3; decide +kernel, ctlAtomic_of_check (by decide), rfl, by decide +kernel,
    fun h => hno h.orderLegal⟩

/-- **R50, twin** (safe). The same initial write of `A`, with the order `relaxed`. Expected: a safe
trace. Obtained: `SafeConcurrentTrace`, Q1–Q3 and reading 12 hold; the event 0 is an initial write
of the data of reading 9; 14d applies: no pair of events races. -/
theorem R50_twin :
    SafeConcurrentTrace pm kAtomic mutexLayout refOrders s6tσ s6tL (r50G .relaxed).toGraph r50K
      r50TD ∧
    CorrQ1 (r50G .relaxed).toGraph s6tL r50K r50TD ∧
    CorrQ2 kAtomic mutexLayout refOrders s6tσ s6tL (r50G .relaxed).toGraph r50K r50TD ∧
    CorrQ3 r50TD ∧ CtlAtomic kAtomic mutexLayout s6tσ s6tL ∧
    r50TD.init 0 = true ∧ ∀ a b, ¬ (r50G .relaxed).toGraph.Race a b := by
  have hK : Corresponds (r50G .relaxed).toGraph s6tσ s6tL r50K :=
    corresponds_of_check _ _ _ [(1, 1)] _ _ _ (by decide +kernel) (by decide) (by decide +kernel)
  have hS : SafeConcurrentTrace pm kAtomic mutexLayout refOrders s6tσ s6tL
      (r50G .relaxed).toGraph r50K r50TD :=
    ⟨s6t_run, by decide +kernel, finitePast_fin _, by decide,
      orderLegal_of_check (by decide +kernel),
      stepOrders_of_check (listK_none (by decide)) (by decide +kernel),
      confinedExcl_of_check [4] 2 kAtomic_conf (by decide) (by decide +kernel),
      confinedHandoff_of_check (by decide +kernel), syncOrdered_of_check (by decide +kernel),
      by decide, handoffOrdered_of_check (by decide +kernel),
      ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩, hK.lifecycle,
      lockEdge_none (by decide)⟩
  have hq1 : CorrQ1 (r50G .relaxed).toGraph s6tL r50K r50TD := by unfold CorrQ1; decide +kernel
  have hq2 : CorrQ2 kAtomic mutexLayout refOrders s6tσ s6tL (r50G .relaxed).toGraph r50K r50TD :=
    corrQ2_of_check (listK_none (by decide)) (by decide +kernel)
  have hq3 : CorrQ3 r50TD := by unfold CorrQ3; decide +kernel
  have h12 : CtlAtomic kAtomic mutexLayout s6tσ s6tL := ctlAtomic_of_check (by decide)
  exact ⟨hS, hq1, hq2, hq3, h12, rfl,
    no_race (testKS_dd _ _ _) atomicStatics_ok rfl hK hS hq1 hq2 hq3 h12⟩

/-! ## R51: the atomic event of a step agrees with its step (C37, C39, C40; C51 item 2(b)) -/

/-- `o := derive(root, Observe, {A, S})`; `spawn c1` yielding `o`; `c0 : writeShared({S})` of kind
`store` without annotation; `c0 : writeShared({A})` of kind `store` with `relaxed`;
`c1 : readShared(o, A, relaxed)`; `c1 : writeShared({S})` of kind `store` without annotation. -/
def r51L : List Label :=
  [.kernel 0 (.derive 0 [1, 3] .observe), .spawn 0 [1] [], .writeShared 0 0 [3] none .store,
   .writeShared 0 0 [1] (some .relaxed) .store, .readShared 1 1 1 .relaxed 1,
   .writeShared 1 1 [3] none .store]

/-- The state after the `derive` of `R51`. -/
def r51s1 : SC := v0.set (deriveEff (v0.view 0) 0 [1, 3] .observe)
/-- The state after the `spawn` of `R51`. -/
def r51s2 : SC := spawnEff r51s1 0 [1] []

/-- The states of `R51` and of its twin. -/
def r51σ : Nat → SC × SyncReg × ArenaReg
  | 0 => (v0, [], []) | 1 => (r51s1, [], []) | 2 => (r51s2, [], []) | 3 => (wrS r51s2 0 3, [], [])
  | 4 => (wrS (wrS r51s2 0 3) 0 1, [], []) | 5 => (wrS (wrS r51s2 0 3) 0 1, [], [])
  | _ => (wrS (wrS (wrS r51s2 0 3) 0 1) 1 3, [], [])

/-- `R51` is an `EncapsulatedTrace` with named states from the initial state (C51.1). -/
theorem r51_run : EncapRun pm kAtomic mutexLayout r51σ r51L := by
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
  | 4, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .readShared (.ok ⟨by decide, by decide, ⟨4, 4, rfl⟩, by decide, by decide⟩)⟩
  | 5, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .writeShared (.ok ⟨by decide, by decide, fun h => absurd rfl h⟩)⟩

/-- The graph of `R51` and of its twin; `ow` and `or` are the orders carried by the atomic write of
step 3 and the atomic read of step 4, which reads it by `rf`. -/
def r51G (ow or : MemOrder) : ListGraph 7 Nat Nat Nat Nat where
  ev i := match i.val with
    | 0 => pEv 0 0 | 1 => lEv 0 1 0 (.spawn 1) | 2 => lEv 1 1 1 (.start 1)
    | 3 => accEv 0 2 (.plain (rLeaf 3) .write) | 4 => accEv 0 3 (.atomic 1 ow (.write 1))
    | 5 => accEv 1 4 (.atomic 1 or (.read 1)) | _ => accEv 1 5 (.plain (rLeaf 3) .write)
  uRange := rLeaf
  rf := [(4, 5)]
  mo := []

/-- The correspondence of `R51` and of its twin. -/
def r51K : StepEvents (Fin 7) := listK [0, 1, 3, 4, 5, 6] [(1, 2)] []

/-- The data of reading 9 of `R51`: the place of the accessed storage, no initial write. -/
abbrev r51D {G : Events.Graph (Fin 7) Nat Nat Nat Nat} : AccessData G r51L r51K :=
  noInit fun e => if e.val = 4 ∨ e.val = 5 then 1 else 3

/-- The steps of the twin of `R51`: those of `R51` with `release` on the atomic write and `acquire`
on the atomic read. -/
def r51TL : List Label :=
  [.kernel 0 (.derive 0 [1, 3] .observe), .spawn 0 [1] [], .writeShared 0 0 [3] none .store,
   .writeShared 0 0 [1] (some .release) .store, .readShared 1 1 1 .acquire 1,
   .writeShared 1 1 [3] none .store]

/-- The twin of `R51` is an `EncapsulatedTrace` with named states from the initial state
(C51.1). -/
theorem r51T_run : EncapRun pm kAtomic mutexLayout r51σ r51TL := by
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
  | 4, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .readShared (.ok ⟨by decide, by decide, ⟨4, 4, rfl⟩, by decide, by decide⟩)⟩
  | 5, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .writeShared (.ok ⟨by decide, by decide, fun h => absurd rfl h⟩)⟩

/-- The data of reading 9 of the twin of `R51`. -/
abbrev r51TD {G : Events.Graph (Fin 7) Nat Nat Nat Nat} : AccessData G r51TL r51K :=
  noInit fun e => if e.val = 4 ∨ e.val = 5 then 1 else 3

/-- **R51** (not safe: the agreement of the atomic events with their steps alone fails; no race).
`o := derive(root, Observe, {A, S})`; `spawn c1` yielding `o`; `c0` writes `S` by the concurrent
`writeShared` of kind `store` without annotation; `c0 : writeShared({A})` of kind `store` with
`relaxed`; `c1 : readShared(o, A, relaxed)`, which reads that write by `rf`; `c1` writes `S` as `c0`
did. In the graph, the event of step 3 carries `release` and that of step 4 carries `acquire`.
Expected (C39: "That annotation applies **only** to the atomic event on that leaf"; C37; C40): the
agreement of the atomic events with their steps alone fails; no race in this graph: the two orders
of the graph are legal for their kinds, and the `sw` edge they give (C32.1) orders the two writes of
`S`, while no step justifies it. Obtained: `StepOrders` fails at step 3; every other condition of
the safe trace holds, `OrderLegal` included, and Q1–Q3 and reading 12 hold; `sw` relates the event
of step 3 to that of step 4; no pair of events races. Twin: `R51_twin`. -/
theorem R51 :
    r51σ 0 = (SC.ofS3 (S3.init atomicStatics), [], []) ∧
    EncapRun pm kAtomic mutexLayout r51σ r51L ∧
    Corresponds (r51G .release .acquire).toGraph r51σ r51L r51K ∧
    (r51G .release .acquire).toGraph.EventConsistent ∧
    (r51G .release .acquire).toGraph.FiniteCausalPast ∧ OrdinaryAtomicOK kAtomic r51σ r51L ∧
    (r51G .release .acquire).toGraph.OrderLegal ∧
    ¬ StepOrders kAtomic mutexLayout refOrders r51σ r51L (r51G .release .acquire).toGraph r51K ∧
    ConfinedExcl kAtomic r51σ r51L ∧
    ConfinedHandoff kAtomic mutexLayout refOrders r51σ r51L (r51G .release .acquire).toGraph r51K ∧
    SyncOrdered kAtomic mutexLayout refOrders r51σ r51L (r51G .release .acquire).toGraph r51K ∧
    InheritedLegal kAtomic r51L ∧
    HandoffOrdered kAtomic mutexLayout refOrders r51σ r51L (r51G .release .acquire).toGraph r51K ∧
    LifetimeOrdered (r51G .release .acquire).toGraph r51D ∧
    LifecycleOK (r51G .release .acquire).toGraph r51σ r51L r51K ∧
    LockEdge (r51G .release .acquire).toGraph r51L r51K ∧
    CorrQ1 (r51G .release .acquire).toGraph r51L r51K r51D ∧
    CorrQ2 kAtomic mutexLayout refOrders r51σ r51L (r51G .release .acquire).toGraph r51K r51D ∧
    CorrQ3 (r51D (G := (r51G .release .acquire).toGraph)) ∧
    CtlAtomic kAtomic mutexLayout r51σ r51L ∧
    (r51G .release .acquire).toGraph.SW 4 5 ∧
    (∀ a b, ¬ (r51G .release .acquire).toGraph.Race a b) ∧
    ¬ SafeConcurrentTrace pm kAtomic mutexLayout refOrders r51σ r51L
      (r51G .release .acquire).toGraph r51K r51D := by
  have hK : Corresponds (r51G .release .acquire).toGraph r51σ r51L r51K :=
    corresponds_of_check _ _ _ [(1, 1)] _ _ _ (by decide +kernel) (by decide) (by decide +kernel)
  have hno : ¬ StepOrders kAtomic mutexLayout refOrders r51σ r51L
      (r51G .release .acquire).toGraph r51K := fun h => by
    obtain ⟨x, hx, ho, -⟩ := h 3 4 (by decide +kernel) 1 .release (.write 1) (by decide +kernel)
    exact (by decide +kernel : ∀ x ∈ stepAcc kAtomic mutexLayout refOrders r51σ r51L 3,
      x.order ≠ some MemOrder.release) x (mem_stepAcc hx) ho
  exact ⟨rfl, r51_run, hK, by decide +kernel, finitePast_fin _, by decide,
    orderLegal_of_check (by decide +kernel), hno,
    confinedExcl_of_check [4] 2 kAtomic_conf (by decide) (by decide +kernel),
    confinedHandoff_of_check (by decide +kernel), syncOrdered_of_check (by decide +kernel),
    by decide, handoffOrdered_of_check (by decide +kernel),
    ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩, hK.lifecycle,
    lockEdge_none (by decide), by unfold CorrQ1; decide +kernel,
    corrQ2_of_check (listK_none (by decide)) (by decide +kernel),
    by unfold CorrQ3; decide +kernel, ctlAtomic_of_check (by decide), by decide +kernel,
    by decide +kernel, fun h => hno h.stepOrders⟩

/-- **R51, twin** (safe). The same steps with `release` on the atomic write of step 3 and `acquire`
on the atomic read of step 4, as their events: the twin changes the annotations of the steps, not
only those of the graph. Expected: a safe trace; `sw` relates the write to the read (C32.1).
Obtained: `SafeConcurrentTrace`, Q1–Q3 and reading 12 hold; `sw` relates the event of step 3 to
that of step 4; 14d applies: no pair of events races. -/
theorem R51_twin :
    SafeConcurrentTrace pm kAtomic mutexLayout refOrders r51σ r51TL
      (r51G .release .acquire).toGraph r51K r51TD ∧
    CorrQ1 (r51G .release .acquire).toGraph r51TL r51K r51TD ∧
    CorrQ2 kAtomic mutexLayout refOrders r51σ r51TL (r51G .release .acquire).toGraph r51K r51TD ∧
    CorrQ3 (r51TD (G := (r51G .release .acquire).toGraph)) ∧
    CtlAtomic kAtomic mutexLayout r51σ r51TL ∧
    (r51G .release .acquire).toGraph.SW 4 5 ∧
    ∀ a b, ¬ (r51G .release .acquire).toGraph.Race a b := by
  have hK : Corresponds (r51G .release .acquire).toGraph r51σ r51TL r51K :=
    corresponds_of_check _ _ _ [(1, 1)] _ _ _ (by decide +kernel) (by decide) (by decide +kernel)
  have hS : SafeConcurrentTrace pm kAtomic mutexLayout refOrders r51σ r51TL
      (r51G .release .acquire).toGraph r51K r51TD :=
    ⟨r51T_run, by decide +kernel, finitePast_fin _, by decide,
      orderLegal_of_check (by decide +kernel),
      stepOrders_of_check (listK_none (by decide)) (by decide +kernel),
      confinedExcl_of_check [4] 2 kAtomic_conf (by decide) (by decide +kernel),
      confinedHandoff_of_check (by decide +kernel), syncOrdered_of_check (by decide +kernel),
      by decide, handoffOrdered_of_check (by decide +kernel),
      ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩, hK.lifecycle,
      lockEdge_none (by decide)⟩
  have hq1 : CorrQ1 (r51G .release .acquire).toGraph r51TL r51K r51TD := by
    unfold CorrQ1; decide +kernel
  have hq2 : CorrQ2 kAtomic mutexLayout refOrders r51σ r51TL (r51G .release .acquire).toGraph
      r51K r51TD := corrQ2_of_check (listK_none (by decide)) (by decide +kernel)
  have hq3 : CorrQ3 (r51TD (G := (r51G .release .acquire).toGraph)) := by
    unfold CorrQ3; decide +kernel
  have h12 : CtlAtomic kAtomic mutexLayout r51σ r51TL := ctlAtomic_of_check (by decide)
  exact ⟨hS, hq1, hq2, hq3, h12, by decide +kernel,
    no_race (testKS_dd _ _ _) atomicStatics_ok rfl hK hS hq1 hq2 hq3 h12⟩

end Ern.Corpus.Concurrency
