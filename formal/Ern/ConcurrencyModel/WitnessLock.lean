import Ern.ConcurrencyModel.WitnessExec
import Ern.ConcurrencyModel.WitnessHandoff
import Ern.ConcurrencyModel.WitnessMutex

/-!
# Witnesses W7–W10: the reference mutex (C44, C48, C49)

Executions from the initial state of `WitnessMutex` (Spec 1 §47): `M = {slot, lock}` (places 0, 1,
2) and the protected root `T` (place 3), owned by `M`; root authorities `root_M` (0) and `root_T`
(1).

* **Block M**: `guarded := derive(root_T, Modify)` (authority 2); `store(guarded, slot)`;
  `newMutex(guarded)`, entry `e` (index 0), controller `lock` (leaf 2);
  `o1 := derive(root_M, Observe, {slot, lock})` (authority 3); `spawn c1` yielding `o1`.
* **Prefix P**: `c1 : acquire(e)` (grant, authority 4); `c1 : write3(T)` by the grant;
  `c1 : unlock(e)`; `c1 : release(o1)`.

Graphs of fragment F with realization R (C48; `ctlAcc`, `ctlSync`): the controller write of
`newMutex` is non-atomic, of value `0`; an `acquire` is an atomic RMW `0 → 1` of role `protocol`;
`unlock` and `resetLock` atomically write `0`, of role `protocol`. The `write3` events carry a
non-atomic access of the range of `T`; the other steps are pure authority markers, except the
lifecycle events.
-/

namespace Ern.ConcurrencyModel

open Ern.MemoryModel Ern.MemoryModel.Access Events

variable {pm : ProviderMeta}

/-- The relaxed order triple, outside the reference (C40). -/
def rlxOrders : CtlOrders := ⟨.relaxed, .relaxed, .relaxed⟩

/-- The range of `T`. -/
def rT : Range := ⟨16, 8⟩

/-- The event of the controller write of `newMutex` (realization R). -/
def nmEv (c k : Nat) : Event Nat Nat Nat Unit := ⟨c, ⟨k, 0⟩, .marks (some (.unit 2 (.write 0))) none⟩
/-- The event of an `acquire` of order `o` (realization R). -/
def acqEv (c k : Nat) (o : MemOrder) : Event Nat Nat Nat Unit :=
  ⟨c, ⟨k, 0⟩, .marks (some (.atomic 2 o (.rmw 0 1))) (some .protocol)⟩
/-- The event of an `unlock` or `resetLock` of order `o` (realization R). -/
def pubEv (c k : Nat) (o : MemOrder) : Event Nat Nat Nat Unit :=
  ⟨c, ⟨k, 0⟩, .marks (some (.atomic 2 o (.write 0))) (some .protocol)⟩

/-! ## Prefix P -/

/-- `c1 : write3(T)` by the grant. -/
def p6 : SC := m5.set (write3Eff (m5.view 1) [3])
/-- `c1 : unlock(e)`. -/
def p7 : SC := prospectiveUnlock p6 1 4
/-- `c1 : release(o1)`. -/
def p8 : SC := p7.set (releaseEff (p7.view 1) 3)
/-- `c0 : acquire(e)` after P (grant, authority 5). -/
def q9 : SC := deriveSyncEff p8 0 2
/-- The registry recording the grant 5. -/
def regT5 : SyncReg := [⟨2, some 5⟩]
/-- `c0 : write3(T)` by the grant 5. -/
def q10 : SC := q9.set (write3Eff (q9.view 0) [3])

/-! ## W7 -/

/-- The labels of W7: block M, P, `c0 : acquire(e)`, `c0 : write3(T)`. -/
def w7L : List Label :=
  [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 2 1), .newMutex 0 2,
   .kernel 0 (.derive 0 [1, 2] .observe), .spawn 0 [3] [], .acquire 1 0,
   .kernel 1 (.write 4 [3]), .unlock 1 0, .kernel 1 (.release 3), .acquire 0 0,
   .kernel 0 (.write 5 [3])]

/-- The states of W7. -/
def w7σ : Nat → SC × SyncReg × ArenaReg
  | 0 => (m0, [], []) | 1 => (m1, [], []) | 2 => (m2, [], []) | 3 => (m2, regFree, [])
  | 4 => (m3, regFree, []) | 5 => (m4, regFree, []) | 6 => (m5, regTaken, [])
  | 7 => (p6, regTaken, []) | 8 => (p7, regFree, []) | 9 => (p8, regFree, [])
  | 10 => (q9, regT5, []) | _ => (q10, regT5, [])

/-- W7 is an `EncapsulatedTrace` with named states from the initial state (C51.1). -/
theorem w7_run : EncapRun pm kMutex mutexLayout w7σ w7L := by
  refine encapRun_of_steps fun i hi lbl hl => ?_
  match i, hi with
  | 0, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 1, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel (.ok (by decide))⟩
  | 2, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .newMutex (st' := (m2, regFree)) ⟨by decide, rfl⟩⟩
  | 3, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 4, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .spawn (.ok (by decide))⟩
  | 5, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .acquire (st' := (m5, regTaken)) ⟨⟨2, none⟩, rfl, by decide, by decide, rfl⟩⟩
  | 6, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 7, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .unlock (st' := (p7, regFree)) ⟨⟨2, some 4⟩, 4, rfl, by decide, rfl, by decide, by decide,
        by decide, rfl⟩⟩
  | 8, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 9, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .acquire (st' := (q9, regT5)) ⟨⟨2, none⟩, rfl, by decide, by decide, rfl⟩⟩
  | 10, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩

/-- The graph of W7 under the orders `R`. -/
def w7G (R : CtlOrders) : ListGraph 12 Nat Nat Nat Unit where
  ev i := match i.val with
    | 0 => pureEv 0 0 | 1 => pureEv 0 1 | 2 => nmEv 0 2 | 3 => pureEv 0 3
    | 4 => lifeEv 0 4 0 (.spawn 1) | 5 => lifeEv 1 4 1 (.start 1) | 6 => acqEv 1 5 R.acq
    | 7 => wrEv 1 6 rT | 8 => pubEv 1 7 R.rel | 9 => pureEv 1 8 | 10 => acqEv 0 9 R.acq
    | _ => wrEv 0 10 rT
  uRange _ := ⟨8, 8⟩
  rf := [(2, 6), (8, 10)]
  mo := [(2, 6), (2, 8), (2, 10), (6, 8), (6, 10), (8, 10)]

/-- The correspondence of W7. -/
def w7K : StepEvents (Fin 12) := listK [0, 1, 2, 3, 4, 6, 7, 8, 9, 10, 11] [(1, 5)] []

/-- **Witness W7** (C48, C49, C44 case 2): under the reference triple, the controller reads
`newMutex` at the `acquire` of `c1` and the `unlock` at the `acquire` of `c0`; `sw` is the edge from
`spawn(c1)` to `start(c1)` and the edge from the `unlock` to the `acquire` of `c0`, alone. The two
writes of `T` are ordered, and so are `newMutex` and the `acquire` of `c1` on `lock`; their loss
markers are `unlock(e)` (step 7 of `c1`) and the `derive` of `o1` (step 3 of `c0`, where
`cap(c0, lock)` passes from `Modify` to `Observe`); `HandoffOrdered` holds for both; the graph has no
race; realization R holds, and 13e (`lock_order`) orders the `unlock` before the `acquire` of
`c0`. -/
theorem witness_w7 :
    w7σ 0 = (SC.ofS3 (S3.init mutexStatics), [], []) ∧ EncapRun pm kMutex mutexLayout w7σ w7L ∧
    Corresponds (w7G refOrders).toGraph w7σ w7L w7K ∧ (w7G refOrders).toGraph.EventConsistent ∧
    Realizes (w7G refOrders).toGraph mutexLayout w7σ w7L w7K 0 2 refOrders 0 1 ∧
    (w7G refOrders).toGraph.rf 2 6 ∧ (w7G refOrders).toGraph.rf 8 10 ∧
    (∀ a b, (w7G refOrders).toGraph.SW a b ↔ (a = 4 ∧ b = 5) ∨ (a = 8 ∧ b = 10)) ∧
    (w7G refOrders).toGraph.HB 7 11 ∧ (w7G refOrders).toGraph.HB 2 6 ∧
    (w7G refOrders).toGraph.HB 8 11 ∧ (w7G refOrders).toGraph.HB 3 6 ∧
    (∀ a b, ¬ (w7G refOrders).toGraph.Race a b) ∧
    FirstCompatible IncompatModify w7σ 6 1 3 .modify 7 ∧ w7L[7]? = some (.unlock 1 0) ∧
    FirstCompatible IncompatModify w7σ 2 0 2 .observe 3 ∧
    w7L[3]? = some (.kernel 0 (.derive 0 [1, 2] .observe)) ∧
    cap (w7σ 3).1 (w7σ 3).2.1 0 2 = some .modify ∧ cap (w7σ 4).1 (w7σ 4).2.1 0 2 = some .observe ∧
    (∀ eu ea, w7K.ev 7 = some eu → w7K.ev 9 = some ea → (w7G refOrders).toGraph.HB eu ea) := by
  have hr := w7_run (pm := pm)
  have hK : Corresponds (w7G refOrders).toGraph w7σ w7L w7K :=
    corresponds_of_check _ _ _ [(4, 1)] _ _ _ (by decide +kernel) (by decide) (by decide +kernel)
  have hc : (w7G refOrders).toGraph.EventConsistent := by decide +kernel
  have hR : Realizes (w7G refOrders).toGraph mutexLayout w7σ w7L w7K 0 2 refOrders 0 1 :=
    realizes_of_check _ _ _ _ _ _ _ _ _ _ _ _ (by decide +kernel)
  refine ⟨rfl, hr, hK, hc, hR, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    firstCompatible_of_check (by decide) (by decide) (by decide), rfl,
    firstCompatible_of_check (by decide) (by decide) (by decide), rfl, by decide, by decide, ?_⟩
  exact (lock_order hr hK hR (.inl rfl) (.inl rfl) (.inl rfl) hc.1 hc.2.2.1 (u := 7) (a := 9)
    (by decide) (by decide) ⟨1, .inl rfl⟩ (by decide) ⟨0, rfl⟩
    (forall_between (by decide))
    (fun k h1 h2 c h => by
      have : k = 8 := by omega
      subst this; cases h)
    (fun p h1 h2 ⟨c, h⟩ => by
      have : p = 8 := by omega
      subst this; cases h)).1

/-! ## W8 -/

/-- The labels of W8: block M, P, `c0 : resetLock(e)`, `c0 : acquire(e)`, `c0 : write3(T)`. -/
def w8L : List Label :=
  [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 2 1), .newMutex 0 2,
   .kernel 0 (.derive 0 [1, 2] .observe), .spawn 0 [3] [], .acquire 1 0,
   .kernel 1 (.write 4 [3]), .unlock 1 0, .kernel 1 (.release 3), .resetLock 0 0, .acquire 0 0,
   .kernel 0 (.write 5 [3])]

/-- The states of W8. -/
def w8σ : Nat → SC × SyncReg × ArenaReg
  | 0 => (m0, [], []) | 1 => (m1, [], []) | 2 => (m2, [], []) | 3 => (m2, regFree, [])
  | 4 => (m3, regFree, []) | 5 => (m4, regFree, []) | 6 => (m5, regTaken, [])
  | 7 => (p6, regTaken, []) | 8 => (p7, regFree, []) | 9 => (p8, regFree, [])
  | 10 => (p8, regFree, []) | 11 => (q9, regT5, []) | _ => (q10, regT5, [])

/-- W8 is an `EncapsulatedTrace` with named states from the initial state (C51.1). -/
theorem w8_run : EncapRun pm kMutex mutexLayout w8σ w8L := by
  refine encapRun_of_steps fun i hi lbl hl => ?_
  match i, hi with
  | 0, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 1, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel (.ok (by decide))⟩
  | 2, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .newMutex (st' := (m2, regFree)) ⟨by decide, rfl⟩⟩
  | 3, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 4, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .spawn (.ok (by decide))⟩
  | 5, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .acquire (st' := (m5, regTaken)) ⟨⟨2, none⟩, rfl, by decide, by decide, rfl⟩⟩
  | 6, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 7, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .unlock (st' := (p7, regFree)) ⟨⟨2, some 4⟩, 4, rfl, by decide, rfl, by decide, by decide,
        by decide, rfl⟩⟩
  | 8, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 9, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .resetLock (st' := (p8, regFree)) ⟨⟨2, none⟩, rfl, by decide, by decide, by decide, by decide,
        rfl⟩⟩
  | 10, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .acquire (st' := (q9, regT5)) ⟨⟨2, none⟩, rfl, by decide, by decide, rfl⟩⟩
  | 11, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩

/-- The graph of W8 under the orders `R`. -/
def w8G (R : CtlOrders) : ListGraph 13 Nat Nat Nat Unit where
  ev i := match i.val with
    | 0 => pureEv 0 0 | 1 => pureEv 0 1 | 2 => nmEv 0 2 | 3 => pureEv 0 3
    | 4 => lifeEv 0 4 0 (.spawn 1) | 5 => lifeEv 1 4 1 (.start 1) | 6 => acqEv 1 5 R.acq
    | 7 => wrEv 1 6 rT | 8 => pubEv 1 7 R.rel | 9 => pureEv 1 8 | 10 => pubEv 0 9 R.reset
    | 11 => acqEv 0 10 R.acq | _ => wrEv 0 11 rT
  uRange _ := ⟨8, 8⟩
  rf := [(2, 6), (10, 11)]
  mo := [(2, 6), (2, 8), (2, 10), (2, 11), (6, 8), (6, 10), (6, 11), (8, 10), (8, 11), (10, 11)]

/-- The correspondence of W8. -/
def w8K : StepEvents (Fin 13) := listK [0, 1, 2, 3, 4, 6, 7, 8, 9, 10, 11, 12] [(1, 5)] []

/-- **Witness W8** (C48, C49: "Recovery is **not automatically** a substitute for an acquire/release
edge missing from an abandoned grant"; C18): under the reference triple, the `acquire` of `c0`
reads the `resetLock`; `sw` is the edge from `spawn(c1)` to `start(c1)` and the edge from the
`resetLock` to the `acquire`, alone; no edge leaves the `unlock`; no `hb` relates the two writes of
`T`, which race; the loss marker is `unlock(e)` (step 7); `HandoffOrdered` is false; the recorded
grant is `none` at the `resetLock`. -/
theorem witness_w8 :
    w8σ 0 = (SC.ofS3 (S3.init mutexStatics), [], []) ∧ EncapRun pm kMutex mutexLayout w8σ w8L ∧
    Corresponds (w8G refOrders).toGraph w8σ w8L w8K ∧ (w8G refOrders).toGraph.EventConsistent ∧
    Realizes (w8G refOrders).toGraph mutexLayout w8σ w8L w8K 0 2 refOrders 0 1 ∧
    (w8G refOrders).toGraph.rf 10 11 ∧
    (∀ a b, (w8G refOrders).toGraph.SW a b ↔ (a = 4 ∧ b = 5) ∨ (a = 10 ∧ b = 11)) ∧
    (∀ b, ¬ (w8G refOrders).toGraph.SW 8 b) ∧
    ¬ (w8G refOrders).toGraph.HB 7 12 ∧ ¬ (w8G refOrders).toGraph.HB 12 7 ∧
    (w8G refOrders).toGraph.Race 7 12 ∧
    FirstCompatible IncompatModify w8σ 6 1 3 .modify 7 ∧ w8L[7]? = some (.unlock 1 0) ∧
    ¬ (w8G refOrders).toGraph.HB 8 12 ∧ grantOf (w8σ 9).2.1 0 = some none := by
  refine ⟨rfl, w8_run, corresponds_of_check _ _ _ [(4, 1)] _ _ _ (by decide +kernel) (by decide)
    (by decide +kernel),
    by decide +kernel, realizes_of_check _ _ _ _ _ _ _ _ _ _ _ _ (by decide +kernel),
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, firstCompatible_of_check (by decide) (by decide) (by decide), rfl,
    by decide +kernel, rfl⟩

/-! ## W9 -/

/-- W9, `c1 : terminate` after P. -/
def t9 : SC := termEffC p8 1
/-- W9, `c0 : acquire(e)` after `join(c1)` and `resetLock(e)` (grant, authority 5). -/
def t12 : SC := deriveSyncEff t9 0 2
/-- W9, `c0 : write3(T)` by the grant 5. -/
def t13 : SC := t12.set (write3Eff (t12.view 0) [3])

/-- The labels of W9: W8 with `c1 : terminate` and `c0 : join(c1)` before the `resetLock`. -/
def w9L : List Label :=
  [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 2 1), .newMutex 0 2,
   .kernel 0 (.derive 0 [1, 2] .observe), .spawn 0 [3] [], .acquire 1 0,
   .kernel 1 (.write 4 [3]), .unlock 1 0, .kernel 1 (.release 3), .terminate 1, .join 0 1,
   .resetLock 0 0, .acquire 0 0, .kernel 0 (.write 5 [3])]

/-- The states of W9. -/
def w9σ : Nat → SC × SyncReg × ArenaReg
  | 0 => (m0, [], []) | 1 => (m1, [], []) | 2 => (m2, [], []) | 3 => (m2, regFree, [])
  | 4 => (m3, regFree, []) | 5 => (m4, regFree, []) | 6 => (m5, regTaken, [])
  | 7 => (p6, regTaken, []) | 8 => (p7, regFree, []) | 9 => (p8, regFree, [])
  | 10 => (t9, regFree, []) | 11 => (t9, regFree, []) | 12 => (t9, regFree, [])
  | 13 => (t12, regT5, []) | _ => (t13, regT5, [])

/-- W9 is an `EncapsulatedTrace` with named states from the initial state (C51.1). -/
theorem w9_run : EncapRun pm kMutex mutexLayout w9σ w9L := by
  refine encapRun_of_steps fun i hi lbl hl => ?_
  match i, hi with
  | 0, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 1, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel (.ok (by decide))⟩
  | 2, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .newMutex (st' := (m2, regFree)) ⟨by decide, rfl⟩⟩
  | 3, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 4, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .spawn (.ok (by decide))⟩
  | 5, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .acquire (st' := (m5, regTaken)) ⟨⟨2, none⟩, rfl, by decide, by decide, rfl⟩⟩
  | 6, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 7, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .unlock (st' := (p7, regFree)) ⟨⟨2, some 4⟩, 4, rfl, by decide, rfl, by decide, by decide,
        by decide, rfl⟩⟩
  | 8, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 9, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .terminate (.ok (by decide))⟩
  | 10, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .join (.ok (by decide) (by decide))⟩
  | 11, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .resetLock (st' := (t9, regFree)) ⟨⟨2, none⟩, rfl, by decide, by decide, by decide, by decide,
        rfl⟩⟩
  | 12, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .acquire (st' := (t12, regT5)) ⟨⟨2, none⟩, rfl, by decide, by decide, rfl⟩⟩
  | 13, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩

/-- The graph of W9. -/
def w9G : ListGraph 16 Nat Nat Nat Unit where
  ev i := match i.val with
    | 0 => pureEv 0 0 | 1 => pureEv 0 1 | 2 => nmEv 0 2 | 3 => pureEv 0 3
    | 4 => lifeEv 0 4 0 (.spawn 1) | 5 => lifeEv 1 4 1 (.start 1) | 6 => acqEv 1 5 .acquire
    | 7 => wrEv 1 6 rT | 8 => pubEv 1 7 .release | 9 => pureEv 1 8 | 10 => pureEv 1 9
    | 11 => lifeEv 1 9 1 (.complete 1) | 12 => lifeEv 0 10 0 (.join 1)
    | 13 => pubEv 0 11 .release | 14 => acqEv 0 12 .acquire | _ => wrEv 0 13 rT
  uRange _ := ⟨8, 8⟩
  rf := [(2, 6), (13, 14)]
  mo := [(2, 6), (2, 8), (2, 13), (2, 14), (6, 8), (6, 13), (6, 14), (8, 13), (8, 14), (13, 14)]

/-- The correspondence of W9. -/
def w9K : StepEvents (Fin 16) :=
  listK [0, 1, 2, 3, 4, 6, 7, 8, 9, 10, 12, 13, 14, 15] [(1, 5)] [(1, 11)]

/-- **Witness W9** (C47, C49; twin of W8): with `c1 : terminate` and `c0 : join(c1)` before the
`resetLock`, the writes of `T` are ordered by the `join`; `sw` is the edges from `spawn(c1)`,
from `complete(c1)` and from the `resetLock`; `HandoffOrdered` holds; no race. -/
theorem witness_w9 :
    w9σ 0 = (SC.ofS3 (S3.init mutexStatics), [], []) ∧ EncapRun pm kMutex mutexLayout w9σ w9L ∧
    Corresponds w9G.toGraph w9σ w9L w9K ∧ w9G.toGraph.EventConsistent ∧
    Realizes w9G.toGraph mutexLayout w9σ w9L w9K 0 2 refOrders 0 1 ∧
    (∀ a b, w9G.toGraph.SW a b ↔ (a = 4 ∧ b = 5) ∨ (a = 11 ∧ b = 12) ∨ (a = 13 ∧ b = 14)) ∧
    w9G.toGraph.HB 7 15 ∧ ¬ w9G.toGraph.Race 7 15 ∧
    FirstCompatible IncompatModify w9σ 6 1 3 .modify 7 ∧ w9L[7]? = some (.unlock 1 0) ∧
    w9G.toGraph.HB 8 15 := by
  refine ⟨rfl, w9_run, corresponds_of_check _ _ _ [(4, 1)] _ _ _ (by decide +kernel) (by decide)
    (by decide +kernel),
    by decide +kernel, realizes_of_check _ _ _ _ _ _ _ _ _ _ _ _ (by decide +kernel),
    by decide +kernel, by decide +kernel, by decide +kernel,
    firstCompatible_of_check (by decide) (by decide) (by decide), rfl, by decide +kernel⟩

/-! ## W10 -/

/-- **Witness W10** (C32.1, C40, C48): the executions of W7 and W8 with the orders outside the
reference, `unlock`, `acquire` and `resetLock` `relaxed`: realization R holds with the relaxed
triple, the same `rf`, no `sw` edge of the controller (the edge from `spawn(c1)` to `start(c1)`
alone); for W7, the two writes of `T` are no longer ordered and race; for W8, they still race. -/
theorem witness_w10 :
    ((w7G rlxOrders).toGraph.EventConsistent ∧
      Corresponds (w7G rlxOrders).toGraph w7σ w7L w7K ∧
      Realizes (w7G rlxOrders).toGraph mutexLayout w7σ w7L w7K 0 2 rlxOrders 0 1 ∧
      (w7G rlxOrders).toGraph.rf 2 6 ∧ (w7G rlxOrders).toGraph.rf 8 10 ∧
      (∀ a b, (w7G rlxOrders).toGraph.SW a b ↔ a = 4 ∧ b = 5) ∧
      ¬ (w7G rlxOrders).toGraph.HB 7 11 ∧ (w7G rlxOrders).toGraph.Race 7 11) ∧
    ((w8G rlxOrders).toGraph.EventConsistent ∧
      Corresponds (w8G rlxOrders).toGraph w8σ w8L w8K ∧
      Realizes (w8G rlxOrders).toGraph mutexLayout w8σ w8L w8K 0 2 rlxOrders 0 1 ∧
      (w8G rlxOrders).toGraph.rf 10 11 ∧
      (∀ a b, (w8G rlxOrders).toGraph.SW a b ↔ a = 4 ∧ b = 5) ∧
      (w8G rlxOrders).toGraph.Race 7 12) := by
  refine ⟨⟨by decide +kernel, corresponds_of_check _ _ _ [(4, 1)] _ _ _ (by decide +kernel)
    (by decide) (by decide +kernel),
    realizes_of_check _ _ _ _ _ _ _ _ _ _ _ _ (by decide +kernel), by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩,
    ⟨by decide +kernel, corresponds_of_check _ _ _ [(4, 1)] _ _ _ (by decide +kernel)
    (by decide) (by decide +kernel),
    realizes_of_check _ _ _ _ _ _ _ _ _ _ _ _ (by decide +kernel), by decide +kernel,
    by decide +kernel, by decide +kernel⟩⟩

end Ern.ConcurrencyModel
