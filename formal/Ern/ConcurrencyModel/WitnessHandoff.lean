import Ern.ConcurrencyModel.WitnessExec
import Ern.ConcurrencyModel.WitnessBase

/-!
# Witnesses W1–W6: handoff, `spawn`, completion and `join` (C32, C33, C43–C47)

Each witness is an `EncapsulatedTrace` (C51.1) from the initial state of Spec 1 §47 with named
states, a hand-written graph of fragment F with its correspondence (K1–K4) and `EventConsistent`
(C34), and the facts its clauses give: the `sw` edges, the `hb` order of the pair of accesses,
`HandoffOrdered` (C46: `hb` from the loss marker to the later access), the race (C33), and the
loss marker (12d: the first step at the end of which the capability of the earlier context is
compatible with the later access).

**Block X**: in the base frame of context 0, a static `Init` place `X` (place 0) of root authority
`root_X` (authority 0). The `write3` events carry a non-atomic access of the range of `X`; the
other steps are pure authority markers, except the lifecycle events.
-/

namespace Ern.ConcurrencyModel

open Ern.MemoryModel Ern.MemoryModel.Access Events

variable {pm : ProviderMeta}

/-- Statics of block X (Spec 1 §47): one `Init` static place `X`, root authority `root_X` held by
the base frame. -/
def xStatics : Statics := [((none, none, 0), true)]

/-- The statics are well formed (Spec 1 §47). -/
theorem xStatics_ok : StaticsOK xStatics := by decide

/-- The contract of block X: no `SharedMutable` leaf. -/
abbrev kX : KShared := testKS [] (fun _ => none) (fun _ => none)

/-- The initial state (Spec 1 §47). -/
def x0 : SC := SC.ofS3 (S3.init xStatics)

/-- The event of a pure authority step of context `c` at step `k`. -/
def pureEv (c k : Nat) : Event Nat Nat Nat Unit := ⟨c, ⟨k, 0⟩, .marks none none⟩
/-- The event of a lifecycle step or marker of context `c` at step `k`, position `p`. -/
def lifeEv (c k p : Nat) (r : SyncRole Nat) : Event Nat Nat Nat Unit :=
  ⟨c, ⟨k, p⟩, .marks none (some r)⟩
/-- The event of a `write3` of context `c` at step `k` on the range `rg`. -/
def wrEv (c k : Nat) (rg : Range) : Event Nat Nat Nat Unit :=
  ⟨c, ⟨k, 0⟩, .marks (some (.plain rg .write)) none⟩

/-- The range of `X`. -/
def rX : Range := ⟨0, 8⟩

/-! ## W1 -/

/-- `a := derive(root_X, Modify)`, authority 1. -/
def w1s1 : SC := x0.set (deriveEff (x0.view 0) 0 [0] .modify)
/-- `spawn c1` yielding `a`. -/
def w1s2 : SC := spawnEff w1s1 0 [1] []
/-- `c1 : write3(X)` by `a`. -/
def w1s3 : SC := w1s2.set (write3Eff (w1s2.view 1) [0])
/-- `c1 : release(a)`. -/
def w1s4 : SC := w1s3.set (releaseEff (w1s3.view 1) 1)
/-- `c0 : write3(X)` by `root_X`. -/
def w1s5 : SC := w1s4.set (write3Eff (w1s4.view 0) [0])

/-- The labels of W1. -/
def w1L : List Label :=
  [.kernel 0 (.derive 0 [0] .modify), .spawn 0 [1] [], .kernel 1 (.write 1 [0]),
   .kernel 1 (.release 1), .kernel 0 (.write 0 [0])]

/-- The states of W1. -/
def w1σ : Nat → SC × SyncReg × ArenaReg
  | 0 => (x0, [], []) | 1 => (w1s1, [], []) | 2 => (w1s2, [], []) | 3 => (w1s3, [], [])
  | 4 => (w1s4, [], []) | _ => (w1s5, [], [])

/-- W1 is an `EncapsulatedTrace` with named states from the initial state (C51.1). -/
theorem w1_run : EncapRun pm kX mutexLayout w1σ w1L := by
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
      .kernel ⟨_, .ok (by decide), rfl⟩⟩

/-- The graph of W1: `derive`, `spawn(c1)`, `start(c1)`, the `write3` of `c1`, `release(a)`, the
`write3` of `c0`. -/
def w1G : ListGraph 6 Nat Nat Nat Unit where
  ev i := match i.val with
    | 0 => pureEv 0 0 | 1 => lifeEv 0 1 0 (.spawn 1) | 2 => lifeEv 1 1 1 (.start 1)
    | 3 => wrEv 1 2 rX | 4 => pureEv 1 3 | _ => wrEv 0 4 rX
  uRange _ := ⟨0, 0⟩
  rf := []
  mo := []

/-- The correspondence of W1. -/
def w1K : StepEvents (Fin 6) := listK [0, 1, 3, 4, 5] [(1, 2)] []

/-- **Witness W1** (C46, C33; C32.2): the execution is an `EncapsulatedTrace` from the initial
state; the graph with its correspondence is `EventConsistent`; `sw` is the edge from `spawn(c1)`
to `start(c1)` alone; no `hb` orders the two writes of `X`, which race; the loss marker of the
pair is `release(a)`, step 3 of `c1` (the capability of `c1` on `X` is `Modify` from step 2 to step
3 and `none` after it); `HandoffOrdered` (`hb` from it to the write of `c0`) is false. -/
theorem witness_w1 :
    w1σ 0 = (SC.ofS3 (S3.init xStatics), [], []) ∧ EncapRun pm kX mutexLayout w1σ w1L ∧
    Corresponds w1G.toGraph w1σ w1L w1K ∧ w1G.toGraph.EventConsistent ∧
    (∀ a b, w1G.toGraph.SW a b ↔ a = 1 ∧ b = 2) ∧
    ¬ w1G.toGraph.HB 3 5 ∧ ¬ w1G.toGraph.HB 5 3 ∧ w1G.toGraph.Race 3 5 ∧
    FirstCompatible IncompatModify w1σ 2 1 0 .modify 3 ∧ w1L[3]? = some (.kernel 1 (.release 1)) ∧
    ¬ w1G.toGraph.HB 4 5 := by
  refine ⟨rfl, w1_run, corresponds_of_check _ _ _ [(1, 1)] _ _ _ (by decide +kernel) (by decide),
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    firstCompatible_of_check (by decide) (by decide) (by decide), rfl, by decide +kernel⟩

/-! ## W2 -/

/-- `c1 : terminate` after W1's `release(a)`. -/
def w2s5 : SC := termEffC w1s4 1
/-- `c0 : write3(X)` by `root_X`, after `c0 : join(c1)`. -/
def w2s7 : SC := w2s5.set (write3Eff (w2s5.view 0) [0])

/-- The labels of W2. -/
def w2L : List Label :=
  [.kernel 0 (.derive 0 [0] .modify), .spawn 0 [1] [], .kernel 1 (.write 1 [0]),
   .kernel 1 (.release 1), .terminate 1, .join 0 1, .kernel 0 (.write 0 [0])]

/-- The states of W2. -/
def w2σ : Nat → SC × SyncReg × ArenaReg
  | 0 => (x0, [], []) | 1 => (w1s1, [], []) | 2 => (w1s2, [], []) | 3 => (w1s3, [], [])
  | 4 => (w1s4, [], []) | 5 => (w2s5, [], []) | 6 => (w2s5, [], []) | _ => (w2s7, [], [])

/-- W2 is an `EncapsulatedTrace` with named states from the initial state (C51.1). -/
theorem w2_run : EncapRun pm kX mutexLayout w2σ w2L := by
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

/-- The graph of W2: W1's events, then `terminate`, `complete(c1)`, `join(c1)` before the write of
`c0`. -/
def w2G : ListGraph 9 Nat Nat Nat Unit where
  ev i := match i.val with
    | 0 => pureEv 0 0 | 1 => lifeEv 0 1 0 (.spawn 1) | 2 => lifeEv 1 1 1 (.start 1)
    | 3 => wrEv 1 2 rX | 4 => pureEv 1 3 | 5 => pureEv 1 4 | 6 => lifeEv 1 4 1 (.complete 1)
    | 7 => lifeEv 0 5 0 (.join 1) | _ => wrEv 0 6 rX
  uRange _ := ⟨0, 0⟩
  rf := []
  mo := []

/-- The correspondence of W2. -/
def w2K : StepEvents (Fin 9) := listK [0, 1, 3, 4, 5, 7, 8] [(1, 2)] [(1, 6)]

/-- **Witness W2** (C46, C47): W1 with `c1 : terminate` and `c0 : join(c1)` before the write of
`c0`. `sw` is the edge from `spawn(c1)` to `start(c1)` and the edge from `complete(c1)` to
`join(c1)`; the writes are ordered by `hb`; the loss marker is still `release(a)`, step 3;
`HandoffOrdered` holds; no race. -/
theorem witness_w2 :
    w2σ 0 = (SC.ofS3 (S3.init xStatics), [], []) ∧ EncapRun pm kX mutexLayout w2σ w2L ∧
    Corresponds w2G.toGraph w2σ w2L w2K ∧ w2G.toGraph.EventConsistent ∧
    (∀ a b, w2G.toGraph.SW a b ↔ (a = 1 ∧ b = 2) ∨ (a = 6 ∧ b = 7)) ∧
    w2G.toGraph.HB 3 8 ∧ ¬ w2G.toGraph.Race 3 8 ∧
    FirstCompatible IncompatModify w2σ 2 1 0 .modify 3 ∧ w2L[3]? = some (.kernel 1 (.release 1)) ∧
    w2G.toGraph.HB 4 8 := by
  refine ⟨rfl, w2_run, corresponds_of_check _ _ _ [(1, 1)] _ _ _ (by decide +kernel) (by decide),
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    firstCompatible_of_check (by decide) (by decide) (by decide), rfl, by decide +kernel⟩

/-! ## W3 -/

/-- `b := derive(a, Modify)`, authority 2, after `a := derive(root_X, Modify)`. -/
def w3s2 : SC := w1s1.set (deriveEff (w1s1.view 0) 1 [0] .modify)
/-- `spawn c1` yielding `a`. -/
def w3s3 : SC := spawnEff w3s2 0 [1] []
/-- `c0 : write3(X)` by `b`. -/
def w3s4 : SC := w3s3.set (write3Eff (w3s3.view 0) [0])
/-- `c0 : release(b)`. -/
def w3s5 : SC := w3s4.set (releaseEff (w3s4.view 0) 2)
/-- `c1 : write3(X)` by `a`. -/
def w3s6 : SC := w3s5.set (write3Eff (w3s5.view 1) [0])

/-- The labels of W3. -/
def w3L : List Label :=
  [.kernel 0 (.derive 0 [0] .modify), .kernel 0 (.derive 1 [0] .modify), .spawn 0 [1] [],
   .kernel 0 (.write 2 [0]), .kernel 0 (.release 2), .kernel 1 (.write 1 [0])]

/-- The states of W3. -/
def w3σ : Nat → SC × SyncReg × ArenaReg
  | 0 => (x0, [], []) | 1 => (w1s1, [], []) | 2 => (w3s2, [], []) | 3 => (w3s3, [], [])
  | 4 => (w3s4, [], []) | 5 => (w3s5, [], []) | _ => (w3s6, [], [])

/-- W3 is an `EncapsulatedTrace` with named states from the initial state (C51.1). -/
theorem w3_run : EncapRun pm kX mutexLayout w3σ w3L := by
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
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 5, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩

/-- The graph of W3. -/
def w3G : ListGraph 7 Nat Nat Nat Unit where
  ev i := match i.val with
    | 0 => pureEv 0 0 | 1 => pureEv 0 1 | 2 => lifeEv 0 2 0 (.spawn 1)
    | 3 => lifeEv 1 2 1 (.start 1) | 4 => wrEv 0 3 rX | 5 => pureEv 0 4 | _ => wrEv 1 5 rX
  uRange _ := ⟨0, 0⟩
  rf := []
  mo := []

/-- The correspondence of W3. -/
def w3K : StepEvents (Fin 7) := listK [0, 1, 2, 4, 5, 6] [(1, 3)] []

/-- **Witness W3** (C47, first paragraph: "A parent's operation executed after `spawn` is not
ordered before a child's operation merely because the parent was the creator"; C46): the loss
marker of the pair is `release(b)`, step 4 of `c0` (the capability of `c0` on `X` is `Modify` from
step 3 to step 4, `none` after it); no `hb` from the write of `c0` to that of `c1`;
`HandoffOrdered` is false; the writes race. -/
theorem witness_w3 :
    w3σ 0 = (SC.ofS3 (S3.init xStatics), [], []) ∧ EncapRun pm kX mutexLayout w3σ w3L ∧
    Corresponds w3G.toGraph w3σ w3L w3K ∧ w3G.toGraph.EventConsistent ∧
    (∀ a b, w3G.toGraph.SW a b ↔ a = 2 ∧ b = 3) ∧
    ¬ w3G.toGraph.HB 4 6 ∧ w3G.toGraph.Race 4 6 ∧
    FirstCompatible IncompatModify w3σ 3 0 0 .modify 4 ∧ w3L[4]? = some (.kernel 0 (.release 2)) ∧
    ¬ w3G.toGraph.HB 5 6 := by
  refine ⟨rfl, w3_run, corresponds_of_check _ _ _ [(2, 1)] _ _ _ (by decide +kernel) (by decide),
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    firstCompatible_of_check (by decide) (by decide) (by decide), rfl, by decide +kernel⟩

/-! ## W4 -/

/-- `c0 : write3(X)` by `root_X`. -/
def w4s1 : SC := x0.set (write3Eff (x0.view 0) [0])
/-- `a := derive(root_X, Modify)`, authority 1. -/
def w4s2 : SC := w4s1.set (deriveEff (w4s1.view 0) 0 [0] .modify)
/-- `spawn c1` yielding `a`. -/
def w4s3 : SC := spawnEff w4s2 0 [1] []
/-- `c1 : write3(X)` by `a`. -/
def w4s4 : SC := w4s3.set (write3Eff (w4s3.view 1) [0])

/-- The labels of W4. -/
def w4L : List Label :=
  [.kernel 0 (.write 0 [0]), .kernel 0 (.derive 0 [0] .modify), .spawn 0 [1] [],
   .kernel 1 (.write 1 [0])]

/-- The states of W4. -/
def w4σ : Nat → SC × SyncReg × ArenaReg
  | 0 => (x0, [], []) | 1 => (w4s1, [], []) | 2 => (w4s2, [], []) | 3 => (w4s3, [], [])
  | _ => (w4s4, [], [])

/-- W4 is an `EncapsulatedTrace` with named states from the initial state (C51.1). -/
theorem w4_run : EncapRun pm kX mutexLayout w4σ w4L := by
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

/-- The graph of W4. -/
def w4G : ListGraph 5 Nat Nat Nat Unit where
  ev i := match i.val with
    | 0 => wrEv 0 0 rX | 1 => pureEv 0 1 | 2 => lifeEv 0 2 0 (.spawn 1)
    | 3 => lifeEv 1 2 1 (.start 1) | _ => wrEv 1 3 rX
  uRange _ := ⟨0, 0⟩
  rf := []
  mo := []

/-- The correspondence of W4. -/
def w4K : StepEvents (Fin 5) := listK [0, 1, 2, 4] [(1, 3)] []

/-- **Witness W4** (C47, C32.2; twin of W3): the loss marker of the pair is the `spawn` step itself,
step 2 of `c0` (the capability of `c0` on `X` is `Modify` until step 2, `none` after it); the writes
are ordered: `po`, the edge from `spawn(c1)` to `start(c1)`, `po`; `HandoffOrdered` holds; no race. -/
theorem witness_w4 :
    w4σ 0 = (SC.ofS3 (S3.init xStatics), [], []) ∧ EncapRun pm kX mutexLayout w4σ w4L ∧
    Corresponds w4G.toGraph w4σ w4L w4K ∧ w4G.toGraph.EventConsistent ∧
    (∀ a b, w4G.toGraph.SW a b ↔ a = 2 ∧ b = 3) ∧
    w4G.toGraph.po 0 2 ∧ w4G.toGraph.po 3 4 ∧ w4G.toGraph.HB 0 4 ∧ ¬ w4G.toGraph.Race 0 4 ∧
    FirstCompatible IncompatModify w4σ 0 0 0 .modify 2 ∧ w4L[2]? = some (.spawn 0 [1] []) ∧
    w4G.toGraph.HB 2 4 := by
  refine ⟨rfl, w4_run, corresponds_of_check _ _ _ [(2, 1)] _ _ _ (by decide +kernel) (by decide),
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, firstCompatible_of_check (by decide) (by decide) (by decide), rfl,
    by decide +kernel⟩

/-! ## W5 and W6 -/

/-- `c1 : a₂ := derive(a, Modify)`, authority 2. -/
def w5s3 : SC := w1s2.set (deriveEff (w1s2.view 1) 1 [0] .modify)
/-- `c1 : spawn c2` yielding `a₂`. -/
def w5s4 : SC := spawnEff w5s3 1 [2] []
/-- `c2 : write3(X)` by `a₂`. -/
def w5s5 : SC := w5s4.set (write3Eff (w5s4.view 2) [0])
/-- `c2 : release(a₂)`. -/
def w5s6 : SC := w5s5.set (releaseEff (w5s5.view 2) 2)
/-- W5, `c1 : release(a)`. -/
def w5s7 : SC := w5s6.set (releaseEff (w5s6.view 1) 1)
/-- W5, `c1 : terminate`. -/
def w5s8 : SC := termEffC w5s7 1
/-- W5, `c0 : write3(X)` by `root_X`, after `c0 : join(c1)`. -/
def w5s10 : SC := w5s8.set (write3Eff (w5s8.view 0) [0])

/-- The labels of W5. -/
def w5L : List Label :=
  [.kernel 0 (.derive 0 [0] .modify), .spawn 0 [1] [], .kernel 1 (.derive 1 [0] .modify),
   .spawn 1 [2] [], .kernel 2 (.write 2 [0]), .kernel 2 (.release 2), .kernel 1 (.release 1),
   .terminate 1, .join 0 1, .kernel 0 (.write 0 [0])]

/-- The states of W5. -/
def w5σ : Nat → SC × SyncReg × ArenaReg
  | 0 => (x0, [], []) | 1 => (w1s1, [], []) | 2 => (w1s2, [], []) | 3 => (w5s3, [], [])
  | 4 => (w5s4, [], []) | 5 => (w5s5, [], []) | 6 => (w5s6, [], []) | 7 => (w5s7, [], [])
  | 8 => (w5s8, [], []) | 9 => (w5s8, [], []) | _ => (w5s10, [], [])

/-- W5 is an `EncapsulatedTrace` with named states from the initial state (C51.1). -/
theorem w5_run : EncapRun pm kX mutexLayout w5σ w5L := by
  refine encapRun_of_steps fun i hi lbl hl => ?_
  match i, hi with
  | 0, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 1, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .spawn (.ok (by decide))⟩
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
  | 7, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .terminate (.ok (by decide))⟩
  | 8, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .join (.ok (by decide) (by decide))⟩
  | 9, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩

/-- The graph of W5. -/
def w5G : ListGraph 13 Nat Nat Nat Unit where
  ev i := match i.val with
    | 0 => pureEv 0 0 | 1 => lifeEv 0 1 0 (.spawn 1) | 2 => lifeEv 1 1 1 (.start 1)
    | 3 => pureEv 1 2 | 4 => lifeEv 1 3 0 (.spawn 2) | 5 => lifeEv 2 3 1 (.start 2)
    | 6 => wrEv 2 4 rX | 7 => pureEv 2 5 | 8 => pureEv 1 6 | 9 => pureEv 1 7
    | 10 => lifeEv 1 7 1 (.complete 1) | 11 => lifeEv 0 8 0 (.join 1) | _ => wrEv 0 9 rX
  uRange _ := ⟨0, 0⟩
  rf := []
  mo := []

/-- The correspondence of W5. -/
def w5K : StepEvents (Fin 13) := listK [0, 1, 3, 4, 6, 7, 8, 9, 11, 12] [(1, 2), (2, 5)] [(1, 10)]

/-- **Witness W5** (C47, third paragraph: "a successful join of an intermediate context does not
imply completion of a surviving descendant"; C46): the loss marker of the pair is `release(a₂)`,
step 5 of `c2`; no `hb` relates the two writes despite the successful `join(c1)`;
`HandoffOrdered` is false; the writes race. -/
theorem witness_w5 :
    w5σ 0 = (SC.ofS3 (S3.init xStatics), [], []) ∧ EncapRun pm kX mutexLayout w5σ w5L ∧
    Corresponds w5G.toGraph w5σ w5L w5K ∧ w5G.toGraph.EventConsistent ∧
    (∀ a b, w5G.toGraph.SW a b ↔ (a = 1 ∧ b = 2) ∨ (a = 4 ∧ b = 5) ∨ (a = 10 ∧ b = 11)) ∧
    ¬ w5G.toGraph.HB 6 12 ∧ ¬ w5G.toGraph.HB 12 6 ∧ w5G.toGraph.Race 6 12 ∧
    FirstCompatible IncompatModify w5σ 4 2 0 .modify 5 ∧ w5L[5]? = some (.kernel 2 (.release 2)) ∧
    ¬ w5G.toGraph.HB 7 12 := by
  refine ⟨rfl, w5_run, corresponds_of_check _ _ _ [(1, 1), (3, 2)] _ _ _ (by decide +kernel)
    (by decide), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, firstCompatible_of_check (by decide) (by decide) (by decide), rfl,
    by decide +kernel⟩

/-- W6, `c2 : terminate` after `release(a₂)`. -/
def w6s7 : SC := termEffC w5s6 2
/-- W6, `c1 : release(a)` after `c1 : join(c2)`. -/
def w6s9 : SC := w6s7.set (releaseEff (w6s7.view 1) 1)
/-- W6, `c1 : terminate`. -/
def w6s10 : SC := termEffC w6s9 1
/-- W6, `c0 : write3(X)` by `root_X`, after `c0 : join(c1)`. -/
def w6s12 : SC := w6s10.set (write3Eff (w6s10.view 0) [0])

/-- The labels of W6. -/
def w6L : List Label :=
  [.kernel 0 (.derive 0 [0] .modify), .spawn 0 [1] [], .kernel 1 (.derive 1 [0] .modify),
   .spawn 1 [2] [], .kernel 2 (.write 2 [0]), .kernel 2 (.release 2), .terminate 2, .join 1 2,
   .kernel 1 (.release 1), .terminate 1, .join 0 1, .kernel 0 (.write 0 [0])]

/-- The states of W6. -/
def w6σ : Nat → SC × SyncReg × ArenaReg
  | 0 => (x0, [], []) | 1 => (w1s1, [], []) | 2 => (w1s2, [], []) | 3 => (w5s3, [], [])
  | 4 => (w5s4, [], []) | 5 => (w5s5, [], []) | 6 => (w5s6, [], []) | 7 => (w6s7, [], [])
  | 8 => (w6s7, [], []) | 9 => (w6s9, [], []) | 10 => (w6s10, [], []) | 11 => (w6s10, [], [])
  | _ => (w6s12, [], [])

/-- W6 is an `EncapsulatedTrace` with named states from the initial state (C51.1). -/
theorem w6_run : EncapRun pm kX mutexLayout w6σ w6L := by
  refine encapRun_of_steps fun i hi lbl hl => ?_
  match i, hi with
  | 0, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 1, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .spawn (.ok (by decide))⟩
  | 2, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 3, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .spawn (.ok (by decide))⟩
  | 4, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 5, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 6, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .terminate (.ok (by decide))⟩
  | 7, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .join (.ok (by decide) (by decide))⟩
  | 8, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 9, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .terminate (.ok (by decide))⟩
  | 10, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .join (.ok (by decide) (by decide))⟩
  | 11, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩

/-- The graph of W6. -/
def w6G : ListGraph 16 Nat Nat Nat Unit where
  ev i := match i.val with
    | 0 => pureEv 0 0 | 1 => lifeEv 0 1 0 (.spawn 1) | 2 => lifeEv 1 1 1 (.start 1)
    | 3 => pureEv 1 2 | 4 => lifeEv 1 3 0 (.spawn 2) | 5 => lifeEv 2 3 1 (.start 2)
    | 6 => wrEv 2 4 rX | 7 => pureEv 2 5 | 8 => pureEv 2 6 | 9 => lifeEv 2 6 1 (.complete 2)
    | 10 => lifeEv 1 7 0 (.join 2) | 11 => pureEv 1 8 | 12 => pureEv 1 9
    | 13 => lifeEv 1 9 1 (.complete 1) | 14 => lifeEv 0 10 0 (.join 1) | _ => wrEv 0 11 rX
  uRange _ := ⟨0, 0⟩
  rf := []
  mo := []

/-- The correspondence of W6. -/
def w6K : StepEvents (Fin 16) :=
  listK [0, 1, 3, 4, 6, 7, 8, 10, 11, 12, 14, 15] [(1, 2), (2, 5)] [(2, 9), (1, 13)]

/-- **Witness W6** (C47: "Correct reference reuse may require **transitive** joining"; twin of
W5): `c2` terminates after `release(a₂)` and `c1` joins it before `release(a)`; the writes are
ordered through `complete(c2)` to `join(c2)` and `complete(c1)` to `join(c1)`; the loss marker is
`release(a₂)`, step 5; `HandoffOrdered` holds; no race. -/
theorem witness_w6 :
    w6σ 0 = (SC.ofS3 (S3.init xStatics), [], []) ∧ EncapRun pm kX mutexLayout w6σ w6L ∧
    Corresponds w6G.toGraph w6σ w6L w6K ∧ w6G.toGraph.EventConsistent ∧
    (∀ a b, w6G.toGraph.SW a b ↔
      (a = 1 ∧ b = 2) ∨ (a = 4 ∧ b = 5) ∨ (a = 9 ∧ b = 10) ∨ (a = 13 ∧ b = 14)) ∧
    w6G.toGraph.HB 6 15 ∧ ¬ w6G.toGraph.Race 6 15 ∧
    FirstCompatible IncompatModify w6σ 4 2 0 .modify 5 ∧ w6L[5]? = some (.kernel 2 (.release 2)) ∧
    w6G.toGraph.HB 7 15 := by
  refine ⟨rfl, w6_run, corresponds_of_check _ _ _ [(1, 1), (3, 2)] _ _ _ (by decide +kernel)
    (by decide), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    firstCompatible_of_check (by decide) (by decide) (by decide), rfl, by decide +kernel⟩

end Ern.ConcurrencyModel
