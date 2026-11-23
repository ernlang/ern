import Ern.ConcurrencyModel.WitnessSafeShared

/-!
# Corpus of the concurrency model: the conditions of the safe trace (test module)

Cases `R49`–`R58` of the concurrency model
(`specs/ERN_Concurrency_Model_Specification_v0.md`), in the form of `Ern.Corpus.ConcurrencyExec`:
each execution is an `EncapsulatedTrace` with named states from the initial state of Spec 1 §47
(`EncapRun`), with a hand-written graph of fragment F, its correspondence (K1–K4) and the data of
reading 9. A trace that is not safe states every condition of `SafeConcurrentTrace`, the one that
fails being negated, the correspondence premises Q1–Q4 (C52), the hypothesis of reading 12
(`CtlAtomic`), and that no pair of events races (C33): each case isolates one condition. A safe
trace states `SafeConcurrentTrace`, Q1–Q4, reading 12, and applies 14d (`no_race`). Each docstring
gives the expected verdict with its clause, the obtained verdict and the twin. This is a test
module: no model module imports it.

In `R52` and `R55` the condition that fails is a correspondence premise, Q4 and Q1; in `R53` and
`R54` it is the provenance of lifecycle roles, a part of the correspondence itself (K3, K4): these
two cases state K1–K4 in the direction of the steps one by one (`corresponds_fwd_of_check`), 14d
does not apply to them, and the absence of a race is checked on the graph.

What differs from `Ern.Corpus.ConcurrencyExec`:

* the test contract is that of the atomic witnesses (`kAtomic`, `WitnessSafeShared`): `A` is the
  leaf 1 (`Atomic(4, 4)`), `S` the leaf 3 (`Synchronized`), `root` the authority 0, the root
  authority of the value, held by the base frame of `c0`; the executions start from the initial
  state of `atomicStatics`;
* the storage identities of reading 9 are the places of the accessed storage (`leafData`,
  `noInit`), not `Unit`;
* in `R50`, the data of reading 9 mark an initial write: an atomic write of `A` that is the event
  of no step; in `R57`, a non-atomic one.

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
Q1–Q4 and reading 12 hold; 14d applies: no pair of events races. -/
theorem R49_twin :
    SafeConcurrentTrace pm kAtomic mutexLayout refOrders r49σ r49L r49TG.toGraph r49TK
      (leafData 3) ∧
    CorrQ1 r49TG.toGraph r49L r49TK (leafData 3) ∧
    CorrQ2 kAtomic mutexLayout refOrders r49σ r49L r49TG.toGraph r49TK (leafData 3) ∧
    CorrQ3 (leafData (G := r49TG.toGraph) (lbls := r49L) (K := r49TK) 3) ∧
    CorrQ4 kAtomic mutexLayout refOrders r49σ r49L r49TK ∧
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
      unitLeaf_of_check (listK_none (by decide)) (by decide +kernel) (by decide +kernel)
        (by decide +kernel),
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
  exact ⟨hS, hq1, hq2, hq3, corrQ4_of_check (by decide +kernel), h12, by decide +kernel,
    by decide +kernel,
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
of the safe trace holds, and Q1–Q4 and reading 12 hold; no pair of events races. Twin:
`R49_twin`. -/
theorem R49 :
    r49σ 0 = (SC.ofS3 (S3.init atomicStatics), [], []) ∧
    EncapRun pm kAtomic mutexLayout r49σ r49L ∧ Corresponds r49G.toGraph r49σ r49L r49K ∧
    r49G.toGraph.EventConsistent ∧ r49G.toGraph.FiniteCausalPast ∧
    OrdinaryAtomicOK kAtomic r49σ r49L ∧ r49G.toGraph.OrderLegal ∧
    StepOrders kAtomic mutexLayout refOrders r49σ r49L r49G.toGraph r49K ∧
    UnitLeaf kAtomic mutexLayout refOrders r49σ r49L r49G.toGraph r49K ∧
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
    CorrQ4 kAtomic mutexLayout refOrders r49σ r49L r49K ∧
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
    unitLeaf_of_check r49K_none (by decide +kernel) (by decide +kernel)
      (by decide +kernel),
    confinedExcl_of_check [4] 2 kAtomic_conf (by decide) (by decide +kernel),
    confinedHandoff_of_check (by decide +kernel), syncOrdered_of_check (by decide +kernel),
    by decide, hno,
    ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩, hK.lifecycle,
    lockEdge_none (by decide), by unfold CorrQ1; decide +kernel,
    corrQ2_of_check r49K_none (by decide +kernel), by unfold CorrQ3; decide +kernel,
    corrQ4_of_check (by decide +kernel),
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
  ⟨fun _ => 1, fun e => decide (e.val = 0), by decide +kernel, by decide +kernel,
    initOrigin_of_check (lbls := s6tL) (listK_none (by decide)) (by decide +kernel)⟩

/-- The data of reading 9 of the twin of `R50`. -/
def r50TD : AccessData (r50G .relaxed).toGraph s6tL r50K :=
  ⟨fun _ => 1, fun e => decide (e.val = 0), by decide +kernel, by decide +kernel,
    initOrigin_of_check (lbls := s6tL) (listK_none (by decide)) (by decide +kernel)⟩

/-- **R50** (not safe: the legality of the memory orders alone fails; no race). The steps of the
twin of S6: `o := derive(root, Observe, {A})`; `spawn c1` yielding `o`; `c0 : writeShared({A})` of
kind `store` with `release`; `c1 : readShared(o, A, acquire)`, which reads that write by `rf`. The
graph starts with an atomic write of `A` by `c0` with the order `acquire`, which is the event of no
step: an initial write of the data of reading 9, first in `mo` (C31). Expected (C40; C34: "Legality
of memory-order annotations (C40) is a typing condition on events, separate from these conjuncts";
C51 item 2(b)): the legality of the orders alone fails; no race: `acquire` is not in the row of the
atomic store. Obtained: `OrderLegal` fails; every other condition of the safe trace holds,
`StepOrders` included, and Q1–Q4 and reading 12 hold; no pair of events races. An abstract
witness, admissible under the condition of the fragment on initial writes (reading 14): no event of
a step is `hb`-before its atomic initial write; the case does not say that an initialization is
atomic, nor that this event is the physical initial contents of `A`. The event is the event of no
step because the order of an `ok` `readShared`,
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
    UnitLeaf kAtomic mutexLayout refOrders s6tσ s6tL (r50G .acquire).toGraph r50K ∧
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
    CorrQ3 r50D ∧ CorrQ4 kAtomic mutexLayout refOrders s6tσ s6tL r50K ∧
    CtlAtomic kAtomic mutexLayout s6tσ s6tL ∧
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
    unitLeaf_of_check (listK_none (by decide)) (by decide +kernel) (by decide +kernel)
      (by decide +kernel),
    confinedExcl_of_check [4] 2 kAtomic_conf (by decide) (by decide +kernel),
    confinedHandoff_of_check (by decide +kernel), syncOrdered_of_check (by decide +kernel),
    by decide, handoffOrdered_of_check (by decide +kernel),
    ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩, hK.lifecycle,
    lockEdge_none (by decide), by unfold CorrQ1; decide +kernel,
    corrQ2_of_check (listK_none (by decide)) (by decide +kernel),
    by unfold CorrQ3; decide +kernel, corrQ4_of_check (by decide +kernel),
    ctlAtomic_of_check (by decide), rfl, by decide +kernel,
    fun h => hno h.orderLegal⟩

/-- **R50, twin** (safe). The same initial write of `A`, with the order `relaxed`. Expected: a safe
trace. Obtained: `SafeConcurrentTrace`, Q1–Q4 and reading 12 hold; the event 0 is an initial write
of the data of reading 9; 14d applies: no pair of events races. -/
theorem R50_twin :
    SafeConcurrentTrace pm kAtomic mutexLayout refOrders s6tσ s6tL (r50G .relaxed).toGraph r50K
      r50TD ∧
    CorrQ1 (r50G .relaxed).toGraph s6tL r50K r50TD ∧
    CorrQ2 kAtomic mutexLayout refOrders s6tσ s6tL (r50G .relaxed).toGraph r50K r50TD ∧
    CorrQ3 r50TD ∧ CorrQ4 kAtomic mutexLayout refOrders s6tσ s6tL r50K ∧
    CtlAtomic kAtomic mutexLayout s6tσ s6tL ∧
    r50TD.init 0 = true ∧ ∀ a b, ¬ (r50G .relaxed).toGraph.Race a b := by
  have hK : Corresponds (r50G .relaxed).toGraph s6tσ s6tL r50K :=
    corresponds_of_check _ _ _ [(1, 1)] _ _ _ (by decide +kernel) (by decide) (by decide +kernel)
  have hS : SafeConcurrentTrace pm kAtomic mutexLayout refOrders s6tσ s6tL
      (r50G .relaxed).toGraph r50K r50TD :=
    ⟨s6t_run, by decide +kernel, finitePast_fin _, by decide,
      orderLegal_of_check (by decide +kernel),
      stepOrders_of_check (listK_none (by decide)) (by decide +kernel),
      unitLeaf_of_check (listK_none (by decide)) (by decide +kernel) (by decide +kernel)
        (by decide +kernel),
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
  exact ⟨hS, hq1, hq2, hq3, corrQ4_of_check (by decide +kernel), h12, rfl,
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
the safe trace holds, `OrderLegal` included, and Q1–Q4 and reading 12 hold; `sw` relates the event
of step 3 to that of step 4; no pair of events races. Twin: `R51_twin`. -/
theorem R51 :
    r51σ 0 = (SC.ofS3 (S3.init atomicStatics), [], []) ∧
    EncapRun pm kAtomic mutexLayout r51σ r51L ∧
    Corresponds (r51G .release .acquire).toGraph r51σ r51L r51K ∧
    (r51G .release .acquire).toGraph.EventConsistent ∧
    (r51G .release .acquire).toGraph.FiniteCausalPast ∧ OrdinaryAtomicOK kAtomic r51σ r51L ∧
    (r51G .release .acquire).toGraph.OrderLegal ∧
    ¬ StepOrders kAtomic mutexLayout refOrders r51σ r51L (r51G .release .acquire).toGraph r51K ∧
    UnitLeaf kAtomic mutexLayout refOrders r51σ r51L (r51G .release .acquire).toGraph r51K ∧
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
    CorrQ4 kAtomic mutexLayout refOrders r51σ r51L r51K ∧
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
    unitLeaf_of_check (listK_none (by decide)) (by decide +kernel) (by decide +kernel)
      (by decide +kernel),
    confinedExcl_of_check [4] 2 kAtomic_conf (by decide) (by decide +kernel),
    confinedHandoff_of_check (by decide +kernel), syncOrdered_of_check (by decide +kernel),
    by decide, handoffOrdered_of_check (by decide +kernel),
    ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩, hK.lifecycle,
    lockEdge_none (by decide), by unfold CorrQ1; decide +kernel,
    corrQ2_of_check (listK_none (by decide)) (by decide +kernel),
    by unfold CorrQ3; decide +kernel, corrQ4_of_check (by decide +kernel),
    ctlAtomic_of_check (by decide), by decide +kernel,
    by decide +kernel, fun h => hno h.stepOrders⟩

/-- **R51, twin** (safe). The same steps with `release` on the atomic write of step 3 and `acquire`
on the atomic read of step 4, as their events: the twin changes the annotations of the steps, not
only those of the graph. Expected: a safe trace; `sw` relates the write to the read (C32.1).
Obtained: `SafeConcurrentTrace`, Q1–Q4 and reading 12 hold; `sw` relates the event of step 3 to
that of step 4; 14d applies: no pair of events races. -/
theorem R51_twin :
    SafeConcurrentTrace pm kAtomic mutexLayout refOrders r51σ r51TL
      (r51G .release .acquire).toGraph r51K r51TD ∧
    CorrQ1 (r51G .release .acquire).toGraph r51TL r51K r51TD ∧
    CorrQ2 kAtomic mutexLayout refOrders r51σ r51TL (r51G .release .acquire).toGraph r51K r51TD ∧
    CorrQ3 (r51TD (G := (r51G .release .acquire).toGraph)) ∧
    CorrQ4 kAtomic mutexLayout refOrders r51σ r51TL r51K ∧
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
      unitLeaf_of_check (listK_none (by decide)) (by decide +kernel) (by decide +kernel)
        (by decide +kernel),
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
  exact ⟨hS, hq1, hq2, hq3, corrQ4_of_check (by decide +kernel), h12, by decide +kernel,
    no_race (testKS_dd _ _ _) atomicStatics_ok rfl hK hS hq1 hq2 hq3 h12⟩

/-! ## R52: the presence of an event (Q4; C26) -/

/-- The graph of `R52`: the graph of S5 (`witness_s5`) without the event of the write of `c0`
(step 3). -/
def r52G : ListGraph 4 Nat Nat Nat Nat where
  ev i := match i.val with
    | 0 => pEv 0 0 | 1 => lEv 0 1 0 (.spawn 1) | 2 => lEv 1 1 1 (.start 1)
    | _ => accEv 1 2 (.plain (rLeaf 3) .write)
  uRange := rLeaf
  rf := []
  mo := []

/-- The correspondence of `R52`: steps 0, 1, 2 have the events 0, 1, 3; step 3 has no event. -/
def r52K : StepEvents (Fin 4) := listK [0, 1, 3] [(1, 2)] []

/-- The accesses of `S` of the two writes of S5: non-atomic writes under `Observe` (11e). -/
abbrev r52w : LeafAccess := ⟨3, .write, none, .observe⟩

/-- **R52** (not safe: the presence of an event alone fails; no race). The steps of S5:
`o := derive(root, Observe, {S})`; `spawn c1` yielding `o`; `c1` writes `S` by the concurrent
`writeShared` of kind `store` without annotation, through `o`; `c0` writes `S` in the same way,
through `root`. The write of `c0` (step 3) has no event. Expected (C26: "Each successful
transition has a defined association with one or more semantic events"; C29: "Every actual byte
access performed by a step realization must have a corresponding `acc` event"): the presence of an
event (Q4) alone fails; no race in this graph. The conditions of the safe trace that bear on the
events of two steps say nothing of the pair of steps 2 and 3; with the event of step 3, the two
writes would race. Obtained: the execution is an `EncapsulatedTrace`; every condition of the safe
trace holds, and the correspondence K1–K4, Q1–Q3 and reading 12 hold: every premise of 14d holds
and 14d applies, no pair of events races. What the case rejects is Q4, which is not a premise of
14d: step 3 has no event and forms a pair in conflict with step 2. Twin: `witness_s5_twin`. -/
theorem R52 :
    s5σ 0 = (SC.ofS3 (S3.init atomicStatics), [], []) ∧
    EncapRun pm kAtomic mutexLayout s5σ s5L ∧ Corresponds r52G.toGraph s5σ s5L r52K ∧
    r52G.toGraph.EventConsistent ∧ r52G.toGraph.FiniteCausalPast ∧
    OrdinaryAtomicOK kAtomic s5σ s5L ∧ r52G.toGraph.OrderLegal ∧
    StepOrders kAtomic mutexLayout refOrders s5σ s5L r52G.toGraph r52K ∧
    UnitLeaf kAtomic mutexLayout refOrders s5σ s5L r52G.toGraph r52K ∧
    ConfinedExcl kAtomic s5σ s5L ∧
    ConfinedHandoff kAtomic mutexLayout refOrders s5σ s5L r52G.toGraph r52K ∧
    SyncOrdered kAtomic mutexLayout refOrders s5σ s5L r52G.toGraph r52K ∧
    InheritedLegal kAtomic s5L ∧
    HandoffOrdered kAtomic mutexLayout refOrders s5σ s5L r52G.toGraph r52K ∧
    LifetimeOrdered r52G.toGraph (leafData (lbls := s5L) (K := r52K) 3) ∧
    LifecycleOK r52G.toGraph s5σ s5L r52K ∧ LockEdge r52G.toGraph s5L r52K ∧
    CorrQ1 r52G.toGraph s5L r52K (leafData 3) ∧
    CorrQ2 kAtomic mutexLayout refOrders s5σ s5L r52G.toGraph r52K (leafData 3) ∧
    CorrQ3 (leafData (G := r52G.toGraph) (lbls := s5L) (K := r52K) 3) ∧
    ¬ CorrQ4 kAtomic mutexLayout refOrders s5σ s5L r52K ∧
    CtlAtomic kAtomic mutexLayout s5σ s5L ∧
    ConflictPair kAtomic mutexLayout refOrders s5σ s5L 2 3 r52w r52w ∧ r52K.ev 3 = none ∧
    ∀ a b, ¬ r52G.toGraph.Race a b := by
  have hK : Corresponds r52G.toGraph s5σ s5L r52K :=
    corresponds_of_check _ _ _ [(1, 1)] _ _ _ (by decide +kernel) (by decide) (by decide +kernel)
  have hS : SafeConcurrentTrace pm kAtomic mutexLayout refOrders s5σ s5L r52G.toGraph r52K
      (leafData 3) :=
    ⟨s5_run, by decide +kernel, finitePast_fin _, by decide,
      orderLegal_of_check (by decide +kernel),
      stepOrders_of_check (listK_none (by decide)) (by decide +kernel),
      unitLeaf_of_check (listK_none (by decide)) (by decide +kernel) (by decide +kernel)
        (by decide +kernel),
      confinedExcl_of_check [4] 2 kAtomic_conf (by decide) (by decide +kernel),
      confinedHandoff_of_check (by decide +kernel), syncOrdered_of_check (by decide +kernel),
      by decide, handoffOrdered_of_check (by decide +kernel),
      ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩, hK.lifecycle,
      lockEdge_none (by decide)⟩
  have hq1 : CorrQ1 r52G.toGraph s5L r52K (leafData 3) := by unfold CorrQ1; decide +kernel
  have hq2 : CorrQ2 kAtomic mutexLayout refOrders s5σ s5L r52G.toGraph r52K (leafData 3) :=
    corrQ2_of_check (listK_none (by decide)) (by decide +kernel)
  have hq3 : CorrQ3 (leafData (G := r52G.toGraph) (lbls := s5L) (K := r52K) 3) := by
    unfold CorrQ3; decide +kernel
  have h12 : CtlAtomic kAtomic mutexLayout s5σ s5L := ctlAtomic_of_check (by decide)
  have h3 : r52K.ev 3 = none := by decide +kernel
  have hno : ¬ CorrQ4 kAtomic mutexLayout refOrders s5σ s5L r52K := fun h => by
    obtain ⟨e, he⟩ := h 3 r52w (stepAccess_of_mem (by decide))
    rw [h3] at he
    cases he
  exact ⟨rfl, s5_run, hK, hS.consistent, hS.finitePast, hS.ordinary, hS.orderLegal,
    hS.stepOrders, hS.unitLeaf, hS.confinedExcl, hS.confinedHandoff, hS.synchronized,
    hS.inherited, hS.handoff, hS.lifetime, hS.lifecycle, hS.lockOrder, hq1, hq2, hq3, hno, h12,
    conflictPair_of (by decide) (by decide) (by decide) rfl (by decide) (.inl (by decide))
      (.inl rfl), h3,
    no_race (testKS_dd _ _ _) atomicStatics_ok rfl hK hS hq1 hq2 hq3 h12⟩

/-! ## R53: the provenance of the roles `complete` and `join` (C28; C32 item 3) -/

/-- The graph of `R53`: the graph of S5, one event per step, where the write of `c1` (step 2)
also carries the role `complete(c1)` and the write of `c0` (step 3) the role `join(c1)`. -/
def r53G : ListGraph 5 Nat Nat Nat Nat where
  ev i := match i.val with
    | 0 => pEv 0 0 | 1 => lEv 0 1 0 (.spawn 1) | 2 => lEv 1 1 1 (.start 1)
    | 3 => ⟨1, ⟨2, 0⟩, .marks (some (.plain (rLeaf 3) .write)) (some (.complete 1))⟩
    | _ => ⟨0, ⟨3, 0⟩, .marks (some (.plain (rLeaf 3) .write)) (some (.join 1))⟩
  uRange := rLeaf
  rf := []
  mo := []

set_option maxHeartbeats 400000 in
/-- **R53** (not safe: the provenance of the lifecycle roles alone fails; no race). The execution
of `R52`; one event per step; the event of the write of `c1` (step 2) also carries the role
`complete(c1)`, that of the write of `c0` (step 3) the role `join(c1)`. Expected (C28: "a context
that successfully executes `terminate` emits a `complete(c)` synchronization marker"; "a successful
`join(c)` creates a synchronization event in the joining context"; C32 item 3): the provenance of
the lifecycle roles alone fails; no race in this graph. No step is a `terminate` or a `join`; the
`sw` edge that these roles give orders the two writes of `S`, and no step justifies it. Obtained:
the execution is an `EncapsulatedTrace`; K1–K4 hold in the direction of the steps; the provenance
of roles fails for the roles `complete(c1)` and `join(c1)` and holds for the roles of every other
event (`roleFromOK`), so that `Corresponds` and `LifecycleOK` fail; every other condition of the
safe trace holds, and Q1–Q4 and reading 12 hold; `sw` relates the events of steps 2 and 3; no pair
of events races. Twin: `witness_s5_twin`. -/
theorem R53 :
    s5σ 0 = (SC.ofS3 (S3.init atomicStatics), [], []) ∧
    EncapRun pm kAtomic mutexLayout s5σ s5L ∧
    (∀ i (h : i < s5L.length) e, pairK.ev i = some e → r53G.toGraph.ctx e = s5L[i].requester) ∧
    (∀ i j e, pairK.ev i = some e → pairK.ev j = some e → i = j) ∧
    (∀ i j (hi : i < s5L.length) (hj : j < s5L.length) a b, i < j →
      s5L[i].requester = s5L[j].requester → pairK.ev i = some a → pairK.ev j = some b →
      r53G.toGraph.po a b) ∧
    (∀ s c, Creates s5σ s5L s c → ∀ e, pairK.ev s = some e →
      r53G.toGraph.sync? e = some (.spawn c)) ∧
    (∀ c x, pairK.start c = some x → r53G.toGraph.ctx x = c ∧
      r53G.toGraph.sync? x = some (.start c) ∧ ∀ j (h : j < s5L.length) d,
        s5L[j].requester = c → pairK.ev j = some d → r53G.toGraph.po x d) ∧
    (∀ c x, pairK.complete c = some x → r53G.toGraph.ctx x = c ∧
      r53G.toGraph.sync? x = some (.complete c) ∧ ∀ j (h : j < s5L.length) d,
        s5L[j].requester = c → pairK.ev j = some d → r53G.toGraph.po d x) ∧
    (∀ q (h : q < s5L.length) c d e, s5L[q] = .join c d → pairK.ev q = some e →
      r53G.toGraph.sync? e = some (.join d)) ∧
    ¬ (∀ e c, r53G.toGraph.sync? e = some (.complete c) →
      pairK.complete c = some e ∧ ∃ t, ∃ h : t < s5L.length, s5L[t] = .terminate c) ∧
    ¬ (∀ e d, r53G.toGraph.sync? e = some (.join d) →
      ∃ q, ∃ h : q < s5L.length, ∃ c, s5L[q] = .join c d ∧ pairK.ev q = some e) ∧
    (∀ e, e ≠ 3 → e ≠ 4 → roleFromOK s5σ s5L pairK e (r53G.toGraph.sync? e) = true) ∧
    ¬ Corresponds r53G.toGraph s5σ s5L pairK ∧
    r53G.toGraph.EventConsistent ∧ r53G.toGraph.FiniteCausalPast ∧
    OrdinaryAtomicOK kAtomic s5σ s5L ∧ r53G.toGraph.OrderLegal ∧
    StepOrders kAtomic mutexLayout refOrders s5σ s5L r53G.toGraph pairK ∧
    UnitLeaf kAtomic mutexLayout refOrders s5σ s5L r53G.toGraph pairK ∧
    ConfinedExcl kAtomic s5σ s5L ∧
    ConfinedHandoff kAtomic mutexLayout refOrders s5σ s5L r53G.toGraph pairK ∧
    SyncOrdered kAtomic mutexLayout refOrders s5σ s5L r53G.toGraph pairK ∧
    InheritedLegal kAtomic s5L ∧
    HandoffOrdered kAtomic mutexLayout refOrders s5σ s5L r53G.toGraph pairK ∧
    LifetimeOrdered r53G.toGraph (leafData (lbls := s5L) (K := pairK) 3) ∧
    ¬ LifecycleOK r53G.toGraph s5σ s5L pairK ∧ LockEdge r53G.toGraph s5L pairK ∧
    CorrQ1 r53G.toGraph s5L pairK (leafData 3) ∧
    CorrQ2 kAtomic mutexLayout refOrders s5σ s5L r53G.toGraph pairK (leafData 3) ∧
    CorrQ3 (leafData (G := r53G.toGraph) (lbls := s5L) (K := pairK) 3) ∧
    CorrQ4 kAtomic mutexLayout refOrders s5σ s5L pairK ∧
    CtlAtomic kAtomic mutexLayout s5σ s5L ∧
    (∀ i (h : i < s5L.length), ∀ c d, s5L[i] ≠ .join c d ∧ s5L[i] ≠ .terminate c) ∧
    r53G.toGraph.SW 3 4 ∧ (∀ a b, ¬ r53G.toGraph.Race a b) ∧
    ¬ SafeConcurrentTrace pm kAtomic mutexLayout refOrders s5σ s5L r53G.toGraph pairK
      (leafData 3) := by
  have hnc : ¬ (∀ e c, r53G.toGraph.sync? e = some (.complete c) →
      pairK.complete c = some e ∧ ∃ t, ∃ h : t < s5L.length, s5L[t] = .terminate c) := fun h =>
    absurd (h 3 1 (by decide +kernel)).1 (by decide +kernel)
  have hnj : ¬ (∀ e d, r53G.toGraph.sync? e = some (.join d) →
      ∃ q, ∃ h : q < s5L.length, ∃ c, s5L[q] = .join c d ∧ pairK.ev q = some e) := fun h => by
    obtain ⟨q, hq, c, hl, -⟩ := h 4 1 (by decide +kernel)
    match q, hq with
    | 0, _ | 1, _ | 2, _ | 3, _ => cases hl
  have hnl : ¬ LifecycleOK r53G.toGraph s5σ s5L pairK := fun h => hnc h.completeFrom
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := corresponds_fwd_of_check r53G s5σ s5L [(1, 1)]
    [0, 1, 3, 4] [(1, 2)] [] (by decide +kernel) (by decide)
  refine ⟨rfl, s5_run,
    f1, f2, f3, f4, f5, f6, f7, hnc, hnj,
    by decide +kernel, fun h => hnc h.completeFrom, by decide +kernel, finitePast_fin _,
    by decide, orderLegal_of_check (by decide +kernel),
    stepOrders_of_check (listK_none (by decide)) (by decide +kernel),
    unitLeaf_of_check (listK_none (by decide)) (by decide +kernel) (by decide +kernel)
      (by decide +kernel),
    confinedExcl_of_check [4] 2 kAtomic_conf (by decide) (by decide +kernel),
    confinedHandoff_of_check (by decide +kernel), syncOrdered_of_check (by decide +kernel),
    by decide, handoffOrdered_of_check (by decide +kernel),
    ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩, hnl, lockEdge_none (by decide),
    by unfold CorrQ1; decide +kernel, corrQ2_of_check (listK_none (by decide)) (by decide +kernel),
    by unfold CorrQ3; decide +kernel, corrQ4_of_check (by decide +kernel),
    ctlAtomic_of_check (by decide), ?_, by decide +kernel, by decide +kernel,
    fun h => hnl h.lifecycle⟩
  intro i h c d
  match i, h with
  | 0, _ | 1, _ | 2, _ | 3, _ => exact ⟨(fun h => by cases h), (fun h => by cases h)⟩

/-! ## R54: the provenance of the roles `spawn` and `start` (C28; C32 item 2) -/

/-- The graph of `R54`: the graph of S5, one event per step, where the write of `c1` (step 2)
also carries the role `spawn(7)` and the write of `c0` (step 3) the role `start(7)`. -/
def r54G : ListGraph 5 Nat Nat Nat Nat where
  ev i := match i.val with
    | 0 => pEv 0 0 | 1 => lEv 0 1 0 (.spawn 1) | 2 => lEv 1 1 1 (.start 1)
    | 3 => ⟨1, ⟨2, 0⟩, .marks (some (.plain (rLeaf 3) .write)) (some (.spawn 7))⟩
    | _ => ⟨0, ⟨3, 0⟩, .marks (some (.plain (rLeaf 3) .write)) (some (.start 7))⟩
  uRange := rLeaf
  rf := []
  mo := []

/-- No step of the execution of S5 creates the context 7. -/
theorem s5_not_creates7 : ∀ s, ¬ Creates s5σ s5L s 7 := by
  intro s hc
  obtain ⟨hs, -, hc7⟩ := hc
  match s, hs with
  | 0, _ | 1, _ | 2, _ | 3, _ => exact absurd hc7 (by decide +kernel)

set_option maxHeartbeats 400000 in
/-- **R54** (not safe: the provenance of the lifecycle roles alone fails; no race). The execution
of `R52`; one event per step; the event of the write of `c1` (step 2) also carries the role
`spawn(c7)`, that of the write of `c0` (step 3) the role `start(c7)`. Expected (C28: "the parent
emits a `spawn` synchronization event"; "the new child emits a distinguished `start(c)`
synchronization marker, generated by the `spawn` protocol"; C32 item 2): the provenance of the
lifecycle roles alone fails; no race in this graph. No step creates a context `c7`; the `sw` edge
that these roles give orders the two writes of `S`, and no step justifies it. Obtained: the
execution is an `EncapsulatedTrace`; K1–K4 hold in the direction of the steps; the provenance of
roles fails for the roles `spawn(7)` and `start(7)` and holds for the roles of every other event
(`roleFromOK`), so that `Corresponds` and `LifecycleOK` fail; every other condition of the safe
trace holds, and Q1–Q4 and reading 12 hold; `sw` relates the events of steps 2 and 3; no pair of
events races. Twin: `R49_twin`. -/
theorem R54 :
    s5σ 0 = (SC.ofS3 (S3.init atomicStatics), [], []) ∧
    EncapRun pm kAtomic mutexLayout s5σ s5L ∧
    (∀ i (h : i < s5L.length) e, pairK.ev i = some e → r54G.toGraph.ctx e = s5L[i].requester) ∧
    (∀ i j e, pairK.ev i = some e → pairK.ev j = some e → i = j) ∧
    (∀ i j (hi : i < s5L.length) (hj : j < s5L.length) a b, i < j →
      s5L[i].requester = s5L[j].requester → pairK.ev i = some a → pairK.ev j = some b →
      r54G.toGraph.po a b) ∧
    (∀ s c, Creates s5σ s5L s c → ∀ e, pairK.ev s = some e →
      r54G.toGraph.sync? e = some (.spawn c)) ∧
    (∀ c x, pairK.start c = some x → r54G.toGraph.ctx x = c ∧
      r54G.toGraph.sync? x = some (.start c) ∧ ∀ j (h : j < s5L.length) d,
        s5L[j].requester = c → pairK.ev j = some d → r54G.toGraph.po x d) ∧
    (∀ c x, pairK.complete c = some x → r54G.toGraph.ctx x = c ∧
      r54G.toGraph.sync? x = some (.complete c) ∧ ∀ j (h : j < s5L.length) d,
        s5L[j].requester = c → pairK.ev j = some d → r54G.toGraph.po d x) ∧
    (∀ q (h : q < s5L.length) c d e, s5L[q] = .join c d → pairK.ev q = some e →
      r54G.toGraph.sync? e = some (.join d)) ∧
    ¬ (∀ e c, r54G.toGraph.sync? e = some (.spawn c) →
      ∃ s, Creates s5σ s5L s c ∧ pairK.ev s = some e) ∧
    ¬ (∀ e c, r54G.toGraph.sync? e = some (.start c) →
      pairK.start c = some e ∧ ∃ s, Creates s5σ s5L s c) ∧
    (∀ e, e ≠ 3 → e ≠ 4 → roleFromOK s5σ s5L pairK e (r54G.toGraph.sync? e) = true) ∧
    ¬ Corresponds r54G.toGraph s5σ s5L pairK ∧
    r54G.toGraph.EventConsistent ∧ r54G.toGraph.FiniteCausalPast ∧
    OrdinaryAtomicOK kAtomic s5σ s5L ∧ r54G.toGraph.OrderLegal ∧
    StepOrders kAtomic mutexLayout refOrders s5σ s5L r54G.toGraph pairK ∧
    UnitLeaf kAtomic mutexLayout refOrders s5σ s5L r54G.toGraph pairK ∧
    ConfinedExcl kAtomic s5σ s5L ∧
    ConfinedHandoff kAtomic mutexLayout refOrders s5σ s5L r54G.toGraph pairK ∧
    SyncOrdered kAtomic mutexLayout refOrders s5σ s5L r54G.toGraph pairK ∧
    InheritedLegal kAtomic s5L ∧
    HandoffOrdered kAtomic mutexLayout refOrders s5σ s5L r54G.toGraph pairK ∧
    LifetimeOrdered r54G.toGraph (leafData (lbls := s5L) (K := pairK) 3) ∧
    ¬ LifecycleOK r54G.toGraph s5σ s5L pairK ∧ LockEdge r54G.toGraph s5L pairK ∧
    CorrQ1 r54G.toGraph s5L pairK (leafData 3) ∧
    CorrQ2 kAtomic mutexLayout refOrders s5σ s5L r54G.toGraph pairK (leafData 3) ∧
    CorrQ3 (leafData (G := r54G.toGraph) (lbls := s5L) (K := pairK) 3) ∧
    CorrQ4 kAtomic mutexLayout refOrders s5σ s5L pairK ∧
    CtlAtomic kAtomic mutexLayout s5σ s5L ∧ (∀ s, ¬ Creates s5σ s5L s 7) ∧
    r54G.toGraph.SW 3 4 ∧ (∀ a b, ¬ r54G.toGraph.Race a b) ∧
    ¬ SafeConcurrentTrace pm kAtomic mutexLayout refOrders s5σ s5L r54G.toGraph pairK
      (leafData 3) := by
  have hns : ¬ (∀ e c, r54G.toGraph.sync? e = some (.spawn c) →
      ∃ s, Creates s5σ s5L s c ∧ pairK.ev s = some e) := fun h => by
    obtain ⟨s, hc, -⟩ := h 3 7 (by decide +kernel)
    exact s5_not_creates7 s hc
  have hnt : ¬ (∀ e c, r54G.toGraph.sync? e = some (.start c) →
      pairK.start c = some e ∧ ∃ s, Creates s5σ s5L s c) := fun h =>
    absurd (h 4 7 (by decide +kernel)).1 (by decide +kernel)
  have hnl : ¬ LifecycleOK r54G.toGraph s5σ s5L pairK := fun h => hns h.spawnFrom
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := corresponds_fwd_of_check r54G s5σ s5L [(1, 1)]
    [0, 1, 3, 4] [(1, 2)] [] (by decide +kernel) (by decide)
  exact ⟨rfl, s5_run,
    f1, f2, f3, f4, f5, f6, f7, hns, hnt,
    by decide +kernel, fun h => hns h.spawnFrom, by decide +kernel, finitePast_fin _,
    by decide, orderLegal_of_check (by decide +kernel),
    stepOrders_of_check (listK_none (by decide)) (by decide +kernel),
    unitLeaf_of_check (listK_none (by decide)) (by decide +kernel) (by decide +kernel)
      (by decide +kernel),
    confinedExcl_of_check [4] 2 kAtomic_conf (by decide) (by decide +kernel),
    confinedHandoff_of_check (by decide +kernel), syncOrdered_of_check (by decide +kernel),
    by decide, handoffOrdered_of_check (by decide +kernel),
    ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩, hnl, lockEdge_none (by decide),
    by unfold CorrQ1; decide +kernel, corrQ2_of_check (listK_none (by decide)) (by decide +kernel),
    by unfold CorrQ3; decide +kernel, corrQ4_of_check (by decide +kernel),
    ctlAtomic_of_check (by decide), s5_not_creates7, by decide +kernel, by decide +kernel,
    fun h => hnl h.lifecycle⟩

/-! ## R55: the provenance of initial writes (C31; reading 14) -/

/-- `o := derive(root, Observe, {A, S})`; `spawn c1` yielding `o`; `c1` writes `S` (non-atomic);
`c0 : readShared(root, A, acquire)`; `c0` writes `S` (non-atomic). No step writes `A`. -/
def r55L : List Label :=
  [.kernel 0 (.derive 0 [1, 3] .observe), .spawn 0 [1] [], .writeShared 1 1 [3] none .store,
   .readShared 0 0 1 .acquire 7, .writeShared 0 0 [3] none .store]

/-- The states of `R55` (the `derive` and the `spawn` of `R51`). -/
def r55σ : Nat → SC × SyncReg × ArenaReg
  | 0 => (v0, [], []) | 1 => (r51s1, [], []) | 2 => (r51s2, [], []) | 3 => (wrS r51s2 1 3, [], [])
  | 4 => (wrS r51s2 1 3, [], []) | _ => (wrS (wrS r51s2 1 3) 0 3, [], [])

/-- `R55` is an `EncapsulatedTrace` with named states from the initial state (C51.1). -/
theorem r55_run : EncapRun pm kAtomic mutexLayout r55σ r55L := by
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
  | 4, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .writeShared (.ok ⟨by decide, by decide, fun h => absurd rfl h⟩)⟩

/-- The graph of `R55`: one event per step, and one more event, an atomic write of `A` with the
order `release`, an event of `c1` placed after its write of `S` (event 4), that is the event of no
step; the read of `c0` reads it by `rf`. -/
def r55G : ListGraph 7 Nat Nat Nat Nat where
  ev i := match i.val with
    | 0 => pEv 0 0 | 1 => lEv 0 1 0 (.spawn 1) | 2 => lEv 1 1 1 (.start 1)
    | 3 => accEv 1 2 (.plain (rLeaf 3) .write)
    | 4 => ⟨1, ⟨5, 0⟩, .marks (some (.atomic 1 .release (.write 7))) none⟩
    | 5 => accEv 0 3 (.atomic 1 .acquire (.read 7))
    | _ => accEv 0 4 (.plain (rLeaf 3) .write)
  uRange := rLeaf
  rf := [(4, 5)]
  mo := []

/-- The correspondence of `R55`. -/
def r55K : StepEvents (Fin 7) := listK [0, 1, 3, 5, 6] [(1, 2)] []

/-- The data of reading 9 of `R55`: the place of the accessed storage, no initial write. -/
abbrev r55D {G : Events.Graph (Fin 7) Nat Nat Nat Nat} : AccessData G r55L r55K :=
  noInit fun e => if e.val = 4 ∨ e.val = 5 then 1 else 3

/-- The same execution, with a non-atomic initial write of `A` by `c0` before every step (event 0)
in place of the event 4 of `R55`. -/
def r55hG : ListGraph 7 Nat Nat Nat Nat where
  ev i := match i.val with
    | 0 => ⟨0, ⟨5, 0⟩, .marks (some (.unit 1 (.write 7))) none⟩
    | 1 => pEv 0 0 | 2 => lEv 0 1 0 (.spawn 1) | 3 => lEv 1 1 1 (.start 1)
    | 4 => accEv 1 2 (.plain (rLeaf 3) .write)
    | 5 => accEv 0 3 (.atomic 1 .acquire (.read 7))
    | _ => accEv 0 4 (.plain (rLeaf 3) .write)
  uRange := rLeaf
  rf := [(0, 5)]
  mo := []

set_option maxHeartbeats 400000 in
/-- **R55** (not safe: the provenance of initial writes alone fails; no race).
`o := derive(root, Observe, {A, S})`; `spawn c1` yielding `o`; `c1` writes `S` by the concurrent
`writeShared` of kind `store` without annotation; `c0 : readShared(root, A, acquire)`; `c0` writes
`S` in the same way. No step writes `A`. The graph has one event per step and one more event: an
atomic write of `A` with the order `release`, an event of `c1` placed after the event of its write
of `S`, that is the event of no step; the read of step 3 reads it by `rf`. Expected (C31: "Initial
writes or initialized storage must have an explicitly represented source"; reading 14): the
condition of the fragment on initial writes alone fails; no race in this graph. An access event
that is the event of no step is an initial write (Q1); the event of step 2 is `hb`-before it, and
it is atomic, while fragment F represents no atomic access outside the steps. The `sw` edge it
gives orders the two writes of `S`. Obtained: the execution is an `EncapsulatedTrace`; with the
data without initial write, every condition of the safe trace holds, and the correspondence K1–K4,
Q2–Q4 and reading 12 hold, and Q1 fails; no data of reading 9 makes Q1 true, since their field
`init_origin` excludes that event as an initial write; `sw` relates the event 4 to the read; no
pair of events races. With a non-atomic initial write of `A` before every step instead, the two
writes of `S` race (`r55hG`). Twin: `R55_twin`. -/
theorem R55 :
    r55σ 0 = (SC.ofS3 (S3.init atomicStatics), [], []) ∧
    EncapRun pm kAtomic mutexLayout r55σ r55L ∧ Corresponds r55G.toGraph r55σ r55L r55K ∧
    r55G.toGraph.EventConsistent ∧ r55G.toGraph.FiniteCausalPast ∧
    OrdinaryAtomicOK kAtomic r55σ r55L ∧ r55G.toGraph.OrderLegal ∧
    StepOrders kAtomic mutexLayout refOrders r55σ r55L r55G.toGraph r55K ∧
    UnitLeaf kAtomic mutexLayout refOrders r55σ r55L r55G.toGraph r55K ∧
    ConfinedExcl kAtomic r55σ r55L ∧
    ConfinedHandoff kAtomic mutexLayout refOrders r55σ r55L r55G.toGraph r55K ∧
    SyncOrdered kAtomic mutexLayout refOrders r55σ r55L r55G.toGraph r55K ∧
    InheritedLegal kAtomic r55L ∧
    HandoffOrdered kAtomic mutexLayout refOrders r55σ r55L r55G.toGraph r55K ∧
    LifetimeOrdered r55G.toGraph (r55D (G := r55G.toGraph)) ∧
    LifecycleOK r55G.toGraph r55σ r55L r55K ∧ LockEdge r55G.toGraph r55L r55K ∧
    ¬ CorrQ1 r55G.toGraph r55L r55K r55D ∧
    CorrQ2 kAtomic mutexLayout refOrders r55σ r55L r55G.toGraph r55K r55D ∧
    CorrQ3 (r55D (G := r55G.toGraph)) ∧ CorrQ4 kAtomic mutexLayout refOrders r55σ r55L r55K ∧
    CtlAtomic kAtomic mutexLayout r55σ r55L ∧
    (∀ D : AccessData r55G.toGraph r55L r55K, ¬ CorrQ1 r55G.toGraph r55L r55K D) ∧
    (∀ i, i < r55L.length → r55K.ev i ≠ some 4) ∧ r55G.toGraph.Atomic 4 ∧
    r55K.ev 2 = some 3 ∧ r55G.toGraph.HB 3 4 ∧ r55G.toGraph.SW 4 5 ∧
    (∀ a b, ¬ r55G.toGraph.Race a b) ∧
    r55hG.toGraph.EventConsistent ∧ r55hG.toGraph.Race 4 6 := by
  have hK : Corresponds r55G.toGraph r55σ r55L r55K :=
    corresponds_of_check _ _ _ [(1, 1)] _ _ _ (by decide +kernel) (by decide) (by decide +kernel)
  -- no data of reading 9 declares the event 4 an initial write
  have h4 : ∀ D : AccessData r55G.toGraph r55L r55K, D.init 4 ≠ true := fun D hi => by
    rcases D.init_origin 4 hi with h | h
    · exact h 2 3 (by decide +kernel) (by decide +kernel)
    · exact h (by decide +kernel)
  have hq1 : ∀ D : AccessData r55G.toGraph r55L r55K, ¬ CorrQ1 r55G.toGraph r55L r55K D :=
    fun D hq => by
      rcases hq 4 (by decide +kernel) with ⟨i, hi, he⟩ | hi
      · have hi' : i < 5 := hi
        match i, hi' with
        | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => exact absurd he (by decide +kernel)
      · exact h4 D hi
  exact ⟨rfl, r55_run, hK, by decide +kernel, finitePast_fin _, by decide,
    orderLegal_of_check (by decide +kernel),
    stepOrders_of_check (listK_none (by decide)) (by decide +kernel),
    unitLeaf_of_check (listK_none (by decide)) (by decide +kernel) (by decide +kernel)
      (by decide +kernel),
    confinedExcl_of_check [4] 2 kAtomic_conf (by decide) (by decide +kernel),
    confinedHandoff_of_check (by decide +kernel), syncOrdered_of_check (by decide +kernel),
    by decide, handoffOrdered_of_check (by decide +kernel),
    ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩, hK.lifecycle,
    lockEdge_none (by decide), hq1 _,
    corrQ2_of_check (listK_none (by decide)) (by decide +kernel),
    by unfold CorrQ3; decide +kernel, corrQ4_of_check (by decide +kernel),
    ctlAtomic_of_check (by decide), hq1, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

/-- The steps of the twin of `R55` and `R56`: those of `R55` with, between the write of `S` by
`c1` and the read of `A` by `c0`, a step `c1 : writeShared({A})` of kind `store` with `release`,
through `o`. -/
def r55TL : List Label :=
  [.kernel 0 (.derive 0 [1, 3] .observe), .spawn 0 [1] [], .writeShared 1 1 [3] none .store,
   .writeShared 1 1 [1] (some .release) .store, .readShared 0 0 1 .acquire 7,
   .writeShared 0 0 [3] none .store]

/-- The states of the twin of `R55`. -/
def r55Tσ : Nat → SC × SyncReg × ArenaReg
  | 0 => (v0, [], []) | 1 => (r51s1, [], []) | 2 => (r51s2, [], []) | 3 => (wrS r51s2 1 3, [], [])
  | 4 => (wrS (wrS r51s2 1 3) 1 1, [], []) | 5 => (wrS (wrS r51s2 1 3) 1 1, [], [])
  | _ => (wrS (wrS (wrS r51s2 1 3) 1 1) 0 3, [], [])

/-- The twin of `R55` is an `EncapsulatedTrace` with named states from the initial state
(C51.1). -/
theorem r55T_run : EncapRun pm kAtomic mutexLayout r55Tσ r55TL := by
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

/-- The graph of the twin of `R55`: one event per step, with the kinds and orders of the steps;
the read of `A` reads by `rf` the write of `A` of step 3. -/
def r55TG : ListGraph 7 Nat Nat Nat Nat where
  ev i := match i.val with
    | 0 => pEv 0 0 | 1 => lEv 0 1 0 (.spawn 1) | 2 => lEv 1 1 1 (.start 1)
    | 3 => accEv 1 2 (.plain (rLeaf 3) .write)
    | 4 => accEv 1 3 (.atomic 1 .release (.write 7))
    | 5 => accEv 0 4 (.atomic 1 .acquire (.read 7))
    | _ => accEv 0 5 (.plain (rLeaf 3) .write)
  uRange := rLeaf
  rf := [(4, 5)]
  mo := []

/-- The correspondence of the twin of `R55`. -/
def r55TK : StepEvents (Fin 7) := listK [0, 1, 3, 4, 5, 6] [(1, 2)] []

/-- The data of reading 9 of the twin of `R55`. -/
abbrev r55TD {G : Events.Graph (Fin 7) Nat Nat Nat Nat} : AccessData G r55TL r55TK :=
  noInit fun e => if e.val = 4 ∨ e.val = 5 then 1 else 3

/-- **R55, twin** (safe), also the twin of `R56`. The steps of `R55` with, between the write of
`S` by `c1` and the read of `A` by `c0`, a step `c1 : writeShared({A})` of kind `store` with
`release`, through `o`, that the `readShared` reads. Expected: a safe trace; `sw` relates the
write to the read (C32 item 1). Obtained: `SafeConcurrentTrace`, Q1–Q4 and reading 12 hold; `sw`
relates the events of steps 3 and 4, and the event of the write of `S` by `c1` is `hb`-before that
of `c0`; the atomic store of `A` (step 3) has an event that designates a unit of nonempty byte
range (`atomic_covered`); 14d applies: no pair of events races. -/
theorem R55_twin :
    SafeConcurrentTrace pm kAtomic mutexLayout refOrders r55Tσ r55TL r55TG.toGraph r55TK
      r55TD ∧
    CorrQ1 r55TG.toGraph r55TL r55TK r55TD ∧
    CorrQ2 kAtomic mutexLayout refOrders r55Tσ r55TL r55TG.toGraph r55TK r55TD ∧
    CorrQ3 (r55TD (G := r55TG.toGraph)) ∧
    CorrQ4 kAtomic mutexLayout refOrders r55Tσ r55TL r55TK ∧
    CtlAtomic kAtomic mutexLayout r55Tσ r55TL ∧
    r55TG.toGraph.SW 4 5 ∧ r55TG.toGraph.HB 3 6 ∧
    (∃ e u, r55TK.ev 3 = some e ∧ r55TG.toGraph.unitOf e = some u ∧
      (r55TG.toGraph.uRange u).len ≠ 0) ∧
    ∀ a b, ¬ r55TG.toGraph.Race a b := by
  have hK : Corresponds r55TG.toGraph r55Tσ r55TL r55TK :=
    corresponds_of_check _ _ _ [(1, 1)] _ _ _ (by decide +kernel) (by decide) (by decide +kernel)
  have hS : SafeConcurrentTrace pm kAtomic mutexLayout refOrders r55Tσ r55TL r55TG.toGraph r55TK
      r55TD :=
    ⟨r55T_run, by decide +kernel, finitePast_fin _, by decide,
      orderLegal_of_check (by decide +kernel),
      stepOrders_of_check (listK_none (by decide)) (by decide +kernel),
      unitLeaf_of_check (listK_none (by decide)) (by decide +kernel) (by decide +kernel)
        (by decide +kernel),
      confinedExcl_of_check [4] 2 kAtomic_conf (by decide) (by decide +kernel),
      confinedHandoff_of_check (by decide +kernel), syncOrdered_of_check (by decide +kernel),
      by decide, handoffOrdered_of_check (by decide +kernel),
      ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩, hK.lifecycle,
      lockEdge_none (by decide)⟩
  have hq1 : CorrQ1 r55TG.toGraph r55TL r55TK r55TD := by unfold CorrQ1; decide +kernel
  have hq2 : CorrQ2 kAtomic mutexLayout refOrders r55Tσ r55TL r55TG.toGraph r55TK r55TD :=
    corrQ2_of_check (listK_none (by decide)) (by decide +kernel)
  have hq3 : CorrQ3 (r55TD (G := r55TG.toGraph)) := by unfold CorrQ3; decide +kernel
  have hq4 : CorrQ4 kAtomic mutexLayout refOrders r55Tσ r55TL r55TK :=
    corrQ4_of_check (by decide +kernel)
  have h12 : CtlAtomic kAtomic mutexLayout r55Tσ r55TL := ctlAtomic_of_check (by decide)
  have hx : StepAccess kAtomic mutexLayout refOrders r55Tσ r55TL 3
      ⟨1, .write, some .release, .observe⟩ := stepAccess_of_mem (by decide)
  exact ⟨hS, hq1, hq2, hq3, hq4, h12, by decide +kernel, by decide +kernel,
    atomic_covered hq4 hS.unitLeaf hx (by decide) (by decide),
    no_race (testKS_dd _ _ _) atomicStatics_ok rfl hK hS hq1 hq2 hq3 h12⟩

/-! ## R56–R58: the units of the events of steps (C38; C51 item 2(b)) -/

/-- `o := derive(root, Observe, {A, B, S})`; `spawn c1` yielding `o`; `c1` writes `S`
(non-atomic); `c1 : writeShared({B})` of kind `store` with `release`; `c0 : readShared(root, A,
acquire)`; `c0` writes `S` (non-atomic). `A` is the leaf 1, `B` the leaf 2, `S` the leaf 3. -/
def r56L : List Label :=
  [.kernel 0 (.derive 0 [1, 2, 3] .observe), .spawn 0 [1] [], .writeShared 1 1 [3] none .store,
   .writeShared 1 1 [2] (some .release) .store, .readShared 0 0 1 .acquire 7,
   .writeShared 0 0 [3] none .store]

/-- The state after the `derive` of `R56`. -/
def r56s1 : SC := v0.set (deriveEff (v0.view 0) 0 [1, 2, 3] .observe)
/-- The state after the `spawn` of `R56`. -/
def r56s2 : SC := spawnEff r56s1 0 [1] []

/-- The states of `R56`. -/
def r56σ : Nat → SC × SyncReg × ArenaReg
  | 0 => (v0, [], []) | 1 => (r56s1, [], []) | 2 => (r56s2, [], []) | 3 => (wrS r56s2 1 3, [], [])
  | 4 => (wrS (wrS r56s2 1 3) 1 2, [], []) | 5 => (wrS (wrS r56s2 1 3) 1 2, [], [])
  | _ => (wrS (wrS (wrS r56s2 1 3) 1 2) 0 3, [], [])

/-- `R56` is an `EncapsulatedTrace` with named states from the initial state (C51.1). -/
theorem r56_run : EncapRun pm kAtomic mutexLayout r56σ r56L := by
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

/-- The graph of `R56`: one event per step, with the kinds and orders of the steps; the event of
the atomic store of `B` and that of the atomic read of `A` both designate the unit 9, whose byte
range is empty; the read reads the store by `rf`. -/
def r56G : ListGraph 7 Nat Nat Nat Nat where
  ev i := match i.val with
    | 0 => pEv 0 0 | 1 => lEv 0 1 0 (.spawn 1) | 2 => lEv 1 1 1 (.start 1)
    | 3 => accEv 1 2 (.plain (rLeaf 3) .write)
    | 4 => accEv 1 3 (.atomic 9 .release (.write 7))
    | 5 => accEv 0 4 (.atomic 9 .acquire (.read 7))
    | _ => accEv 0 5 (.plain (rLeaf 3) .write)
  uRange u := if u = 9 then ⟨0, 0⟩ else rLeaf u
  rf := [(4, 5)]
  mo := []

/-- The correspondence of `R56`. -/
def r56K : StepEvents (Fin 7) := listK [0, 1, 3, 4, 5, 6] [(1, 2)] []

/-- The data of reading 9 of `R56`: no initial write. -/
abbrev r56D {G : Events.Graph (Fin 7) Nat Nat Nat Nat} : AccessData G r56L r56K :=
  noInit fun e => if e.val = 4 ∨ e.val = 5 then 9 else 3

/-- The same execution with a graph that designates each leaf by its own unit: a non-atomic
initial write of `A` by `c0` before every step supplies the value read. -/
def r56hG : ListGraph 8 Nat Nat Nat Nat where
  ev i := match i.val with
    | 0 => ⟨0, ⟨6, 0⟩, .marks (some (.unit 1 (.write 7))) none⟩
    | 1 => pEv 0 0 | 2 => lEv 0 1 0 (.spawn 1) | 3 => lEv 1 1 1 (.start 1)
    | 4 => accEv 1 2 (.plain (rLeaf 3) .write)
    | 5 => accEv 1 3 (.atomic 2 .release (.write 7))
    | 6 => accEv 0 4 (.atomic 1 .acquire (.read 7))
    | _ => accEv 0 5 (.plain (rLeaf 3) .write)
  uRange := rLeaf
  rf := [(0, 6)]
  mo := []

set_option maxHeartbeats 400000 in
/-- **R56** (not safe: the units of the events of steps alone fail; no race).
`o := derive(root, Observe, {A, B, S})`; `spawn c1` yielding `o`; `c1` writes `S` by the
concurrent `writeShared` of kind `store` without annotation; `c1 : writeShared({B})` of kind
`store` with `release`; `c0 : readShared(root, A, acquire)`; `c0` writes `S` as `c1` did. The
events of steps 3 and 4 designate one unit, of empty byte range, and the read of step 4 reads by
`rf` the write of step 3. Expected (C38: "One `Atomic(size, align)` unit is **one logical leaf**";
C32 item 1: "on the same atomic unit"): the agreement of the units alone fails; no race in this
graph. Steps 3 and 4 access two different leaves; the `sw` edge orders the two writes of `S`, and
no step justifies it. Obtained: the execution is an `EncapsulatedTrace`; `UnitLeaf` fails; every
other condition of the safe trace holds, and the correspondence K1–K4, Q1–Q4 and reading 12 hold;
step 3 accesses `B` and step 4 accesses `A`, and their events designate the unit 9; `sw` relates
the two events; no pair of events races. With one unit per leaf, the two writes of `S` race
(`r56hG`). Twin: `R55_twin`. -/
theorem R56 :
    r56σ 0 = (SC.ofS3 (S3.init atomicStatics), [], []) ∧
    EncapRun pm kAtomic mutexLayout r56σ r56L ∧ Corresponds r56G.toGraph r56σ r56L r56K ∧
    r56G.toGraph.EventConsistent ∧ r56G.toGraph.FiniteCausalPast ∧
    OrdinaryAtomicOK kAtomic r56σ r56L ∧ r56G.toGraph.OrderLegal ∧
    StepOrders kAtomic mutexLayout refOrders r56σ r56L r56G.toGraph r56K ∧
    ¬ UnitLeaf kAtomic mutexLayout refOrders r56σ r56L r56G.toGraph r56K ∧
    ConfinedExcl kAtomic r56σ r56L ∧
    ConfinedHandoff kAtomic mutexLayout refOrders r56σ r56L r56G.toGraph r56K ∧
    SyncOrdered kAtomic mutexLayout refOrders r56σ r56L r56G.toGraph r56K ∧
    InheritedLegal kAtomic r56L ∧
    HandoffOrdered kAtomic mutexLayout refOrders r56σ r56L r56G.toGraph r56K ∧
    LifetimeOrdered r56G.toGraph (r56D (G := r56G.toGraph)) ∧
    LifecycleOK r56G.toGraph r56σ r56L r56K ∧ LockEdge r56G.toGraph r56L r56K ∧
    CorrQ1 r56G.toGraph r56L r56K r56D ∧
    CorrQ2 kAtomic mutexLayout refOrders r56σ r56L r56G.toGraph r56K r56D ∧
    CorrQ3 (r56D (G := r56G.toGraph)) ∧ CorrQ4 kAtomic mutexLayout refOrders r56σ r56L r56K ∧
    CtlAtomic kAtomic mutexLayout r56σ r56L ∧
    StepAccess kAtomic mutexLayout refOrders r56σ r56L 3 ⟨2, .write, some .release, .observe⟩ ∧
    StepAccess kAtomic mutexLayout refOrders r56σ r56L 4 ⟨1, .read, some .acquire, .observe⟩ ∧
    r56G.toGraph.unitOf 4 = some 9 ∧ r56G.toGraph.unitOf 5 = some 9 ∧ r56G.toGraph.SW 4 5 ∧
    (∀ a b, ¬ r56G.toGraph.Race a b) ∧
    r56hG.toGraph.EventConsistent ∧ ¬ r56hG.toGraph.SW 5 6 ∧ r56hG.toGraph.Race 4 7 ∧
    ¬ SafeConcurrentTrace pm kAtomic mutexLayout refOrders r56σ r56L r56G.toGraph r56K
      (r56D (G := r56G.toGraph)) := by
  have hK : Corresponds r56G.toGraph r56σ r56L r56K :=
    corresponds_of_check _ _ _ [(1, 1)] _ _ _ (by decide +kernel) (by decide) (by decide +kernel)
  have hno : ¬ UnitLeaf kAtomic mutexLayout refOrders r56σ r56L r56G.toGraph r56K := fun h => by
    obtain ⟨x, y, hx, hy, hl, -⟩ := h.leaf 3 4 4 5 9 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
    have hx' := mem_stepAcc hx
    have hy' := mem_stepAcc hy
    have h3 : stepAcc kAtomic mutexLayout refOrders r56σ r56L 3 =
        [⟨2, .write, some .release, .observe⟩] := by decide +kernel
    have h4 : stepAcc kAtomic mutexLayout refOrders r56σ r56L 4 =
        [⟨1, .read, some .acquire, .observe⟩] := by decide +kernel
    rw [h3, List.mem_singleton] at hx'
    rw [h4, List.mem_singleton] at hy'
    subst hx' hy'
    exact absurd hl (by decide)
  exact ⟨rfl, r56_run, hK, by decide +kernel, finitePast_fin _, by decide,
    orderLegal_of_check (by decide +kernel),
    stepOrders_of_check (listK_none (by decide)) (by decide +kernel), hno,
    confinedExcl_of_check [4] 2 kAtomic_conf (by decide) (by decide +kernel),
    confinedHandoff_of_check (by decide +kernel), syncOrdered_of_check (by decide +kernel),
    by decide, handoffOrdered_of_check (by decide +kernel),
    ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩, hK.lifecycle,
    lockEdge_none (by decide), by unfold CorrQ1; decide +kernel,
    corrQ2_of_check (listK_none (by decide)) (by decide +kernel),
    by unfold CorrQ3; decide +kernel, corrQ4_of_check (by decide +kernel),
    ctlAtomic_of_check (by decide), stepAccess_of_mem (by decide), stepAccess_of_mem (by decide),
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, fun h => hno h.unitLeaf⟩

/-- The graph of `R57`: the graph of the twin of S6 (the steps of `R50`) where the `release`
store of `A` designates the unit 1 and the `acquire` read of `A` the unit 2; the read reads by `rf`
a non-atomic initial write of the unit 2, an event of `c0` that precedes every step. -/
def r57G : ListGraph 6 Nat Nat Nat Nat where
  ev i := match i.val with
    | 0 => ⟨0, ⟨4, 0⟩, .marks (some (.unit 2 (.write 1))) none⟩
    | 1 => pEv 0 0 | 2 => lEv 0 1 0 (.spawn 1) | 3 => lEv 1 1 1 (.start 1)
    | 4 => accEv 0 2 (.atomic 1 .release (.write 1))
    | _ => accEv 1 3 (.atomic 2 .acquire (.read 1))
  uRange := rLeaf
  rf := [(0, 5)]
  mo := []

/-- The data of reading 9 of `R57`: the event 0 is an initial write. -/
def r57D : AccessData r57G.toGraph s6tL r50K :=
  ⟨fun e => if e.val = 4 then 1 else 2, fun e => decide (e.val = 0), by decide +kernel,
    by decide +kernel, initOrigin_of_check (lbls := s6tL) (listK_none (by decide))
      (by decide +kernel)⟩

set_option maxHeartbeats 400000 in
/-- **R57** (not safe: the units of the events of steps alone fail; no race). The steps of `R50`:
`o := derive(root, Observe, {A})`; `spawn c1` yielding `o`; `c0 : writeShared({A})` of kind
`store` with `release`; `c1 : readShared(o, A, acquire)`. The event of step 2 designates one unit,
that of step 3 another; the read of step 3 reads by `rf` a non-atomic initial write of that second
unit, which precedes every step. Expected (C38; C31: `mo` is "a strict total order over **all
writes/modifications of that location**"): the agreement of the units alone fails; no race. Steps
2 and 3 access the same leaf `A`: their events designate one unit. Obtained: the execution is an
`EncapsulatedTrace`; `UnitLeaf` fails; every other condition of the safe trace holds, and the
correspondence K1–K4, Q1–Q4 and reading 12 hold; steps 2 and 3 access `A`, and their events
designate the units 1 and 2; no pair of events races. Twin: `witness_s6_twin`. -/
theorem R57 :
    s6tσ 0 = (SC.ofS3 (S3.init atomicStatics), [], []) ∧
    EncapRun pm kAtomic mutexLayout s6tσ s6tL ∧ Corresponds r57G.toGraph s6tσ s6tL r50K ∧
    r57G.toGraph.EventConsistent ∧ r57G.toGraph.FiniteCausalPast ∧
    OrdinaryAtomicOK kAtomic s6tσ s6tL ∧ r57G.toGraph.OrderLegal ∧
    StepOrders kAtomic mutexLayout refOrders s6tσ s6tL r57G.toGraph r50K ∧
    ¬ UnitLeaf kAtomic mutexLayout refOrders s6tσ s6tL r57G.toGraph r50K ∧
    ConfinedExcl kAtomic s6tσ s6tL ∧
    ConfinedHandoff kAtomic mutexLayout refOrders s6tσ s6tL r57G.toGraph r50K ∧
    SyncOrdered kAtomic mutexLayout refOrders s6tσ s6tL r57G.toGraph r50K ∧
    InheritedLegal kAtomic s6tL ∧
    HandoffOrdered kAtomic mutexLayout refOrders s6tσ s6tL r57G.toGraph r50K ∧
    LifetimeOrdered r57G.toGraph r57D ∧
    LifecycleOK r57G.toGraph s6tσ s6tL r50K ∧ LockEdge r57G.toGraph s6tL r50K ∧
    CorrQ1 r57G.toGraph s6tL r50K r57D ∧
    CorrQ2 kAtomic mutexLayout refOrders s6tσ s6tL r57G.toGraph r50K r57D ∧
    CorrQ3 r57D ∧ CorrQ4 kAtomic mutexLayout refOrders s6tσ s6tL r50K ∧
    CtlAtomic kAtomic mutexLayout s6tσ s6tL ∧
    StepAccess kAtomic mutexLayout refOrders s6tσ s6tL 2 ⟨1, .write, some .release, .observe⟩ ∧
    StepAccess kAtomic mutexLayout refOrders s6tσ s6tL 3 ⟨1, .read, some .acquire, .observe⟩ ∧
    r57G.toGraph.unitOf 4 = some 1 ∧ r57G.toGraph.unitOf 5 = some 2 ∧
    (∀ a b, ¬ r57G.toGraph.Race a b) ∧
    ¬ SafeConcurrentTrace pm kAtomic mutexLayout refOrders s6tσ s6tL r57G.toGraph r50K r57D := by
  have hK : Corresponds r57G.toGraph s6tσ s6tL r50K :=
    corresponds_of_check _ _ _ [(1, 1)] _ _ _ (by decide +kernel) (by decide) (by decide +kernel)
  have hx : StepAccess kAtomic mutexLayout refOrders s6tσ s6tL 2
      ⟨1, .write, some .release, .observe⟩ := stepAccess_of_mem (by decide)
  have hy : StepAccess kAtomic mutexLayout refOrders s6tσ s6tL 3
      ⟨1, .read, some .acquire, .observe⟩ := stepAccess_of_mem (by decide)
  have e4 : r57G.toGraph.unitOf 4 = some 1 := by decide +kernel
  have e5 : r57G.toGraph.unitOf 5 = some 2 := by decide +kernel
  have hno : ¬ UnitLeaf kAtomic mutexLayout refOrders s6tσ s6tL r57G.toGraph r50K := fun h => by
    obtain ⟨u, h4, h5⟩ := h.unit 2 3 4 5 _ _ (by decide +kernel) (by decide +kernel) hx hy rfl
      (by decide) (by decide)
    rw [e4] at h4
    rw [e5] at h5
    cases h4
    cases h5
  exact ⟨rfl, s6t_run, hK, by decide +kernel, finitePast_fin _, by decide,
    orderLegal_of_check (by decide +kernel),
    stepOrders_of_check (listK_none (by decide)) (by decide +kernel), hno,
    confinedExcl_of_check [4] 2 kAtomic_conf (by decide) (by decide +kernel),
    confinedHandoff_of_check (by decide +kernel), syncOrdered_of_check (by decide +kernel),
    by decide, handoffOrdered_of_check (by decide +kernel),
    ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩, hK.lifecycle,
    lockEdge_none (by decide), by unfold CorrQ1; decide +kernel,
    corrQ2_of_check (listK_none (by decide)) (by decide +kernel),
    by unfold CorrQ3; decide +kernel, corrQ4_of_check (by decide +kernel),
    ctlAtomic_of_check (by decide), hx, hy, e4, e5, by decide +kernel,
    fun h => hno h.unitLeaf⟩

/-- The graph of `R58`: the graph of the twin of S6 where the unit 1 has an empty byte range. -/
def r58G : ListGraph 5 Nat Nat Nat Nat :=
  { s6tG with uRange := fun u => if u = 1 then ⟨8, 0⟩ else rLeaf u }

set_option maxHeartbeats 400000 in
/-- **R58** (not safe: the units of the events of steps alone fail; no race). The steps of `R50`,
with its graph without the initial write; the unit of `A` has an empty byte range. Expected (C38:
"An `Atomic(size, align)` leaf with zero physical size cannot satisfy the supported atomic-unit
requirement"): the agreement of the units alone fails; no race. The unit that the event of a step
designates has a nonempty byte range. Obtained: the execution is an `EncapsulatedTrace`;
`UnitLeaf` fails; every other condition of the safe trace holds, and the correspondence K1–K4,
Q1–Q4 and reading 12 hold; the event of step 2 designates the unit 1, of empty byte range; no pair
of events races. Twin: `witness_s6_twin`. -/
theorem R58 :
    s6tσ 0 = (SC.ofS3 (S3.init atomicStatics), [], []) ∧
    EncapRun pm kAtomic mutexLayout s6tσ s6tL ∧ Corresponds r58G.toGraph s6tσ s6tL pairK ∧
    r58G.toGraph.EventConsistent ∧ r58G.toGraph.FiniteCausalPast ∧
    OrdinaryAtomicOK kAtomic s6tσ s6tL ∧ r58G.toGraph.OrderLegal ∧
    StepOrders kAtomic mutexLayout refOrders s6tσ s6tL r58G.toGraph pairK ∧
    ¬ UnitLeaf kAtomic mutexLayout refOrders s6tσ s6tL r58G.toGraph pairK ∧
    ConfinedExcl kAtomic s6tσ s6tL ∧
    ConfinedHandoff kAtomic mutexLayout refOrders s6tσ s6tL r58G.toGraph pairK ∧
    SyncOrdered kAtomic mutexLayout refOrders s6tσ s6tL r58G.toGraph pairK ∧
    InheritedLegal kAtomic s6tL ∧
    HandoffOrdered kAtomic mutexLayout refOrders s6tσ s6tL r58G.toGraph pairK ∧
    LifetimeOrdered r58G.toGraph (leafData (lbls := s6tL) (K := pairK) 1) ∧
    LifecycleOK r58G.toGraph s6tσ s6tL pairK ∧ LockEdge r58G.toGraph s6tL pairK ∧
    CorrQ1 r58G.toGraph s6tL pairK (leafData 1) ∧
    CorrQ2 kAtomic mutexLayout refOrders s6tσ s6tL r58G.toGraph pairK (leafData 1) ∧
    CorrQ3 (leafData (G := r58G.toGraph) (lbls := s6tL) (K := pairK) 1) ∧
    CorrQ4 kAtomic mutexLayout refOrders s6tσ s6tL pairK ∧
    CtlAtomic kAtomic mutexLayout s6tσ s6tL ∧
    pairK.ev 2 = some 3 ∧ r58G.toGraph.unitOf 3 = some 1 ∧ (r58G.toGraph.uRange 1).len = 0 ∧
    (∀ a b, ¬ r58G.toGraph.Race a b) ∧
    ¬ SafeConcurrentTrace pm kAtomic mutexLayout refOrders s6tσ s6tL r58G.toGraph pairK
      (leafData 1) := by
  have hK : Corresponds r58G.toGraph s6tσ s6tL pairK :=
    corresponds_of_check _ _ _ [(1, 1)] _ _ _ (by decide +kernel) (by decide) (by decide +kernel)
  have hno : ¬ UnitLeaf kAtomic mutexLayout refOrders s6tσ s6tL r58G.toGraph pairK := fun h =>
    h.range 2 3 1 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact ⟨rfl, s6t_run, hK, by decide +kernel, finitePast_fin _, by decide,
    orderLegal_of_check (by decide +kernel),
    stepOrders_of_check (listK_none (by decide)) (by decide +kernel), hno,
    confinedExcl_of_check [4] 2 kAtomic_conf (by decide) (by decide +kernel),
    confinedHandoff_of_check (by decide +kernel), syncOrdered_of_check (by decide +kernel),
    by decide, handoffOrdered_of_check (by decide +kernel),
    ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩, hK.lifecycle,
    lockEdge_none (by decide), by unfold CorrQ1; decide +kernel,
    corrQ2_of_check (listK_none (by decide)) (by decide +kernel),
    by unfold CorrQ3; decide +kernel, corrQ4_of_check (by decide +kernel),
    ctlAtomic_of_check (by decide), by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, fun h => hno h.unitLeaf⟩

end Ern.Corpus.Concurrency
