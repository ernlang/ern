import Ern.Concurrency.FullEncap.HandoffExt
import Ern.Concurrency.FullEncap.Replay

/-!
# Witnesses of the extended handoff

Brief of milestone 4, slice 4, task 1 (`corpus-spec2-m3.md` v15 §2 quaterdecies). Verdicts and
facts written from the corpus, decided by `decide`. Each trace is a `RunFull` from the initial
state of Spec 1 §47.

* W-HT, W-HS, W-HX: a context writes through a derivative, releases it and stays live; the creator
  then transfers, stores into, or kills the leaf; and their twins W-HT-J, W-HS-J, W-HX-J, with
  `terminate` and `join` before the third step.
* W-SV: the destination of a by-value `spawn` (setup and step 1 of S4).
* W-NM: initialization of the controller, then acquisition by another context.
* W-TR, W-TR-J: the pairs `(unlock, transfer, lock)` and `(acquire, transfer, lock)`.
* W-CR: ordinary read of the controller.

The facts on the graph bear on the abstract steps (brief, "Portée du résultat"): an extended race
is a fact about the model, not a verdict of WC5.3 C46.
-/

set_option autoImplicit false

namespace Ern.Concurrency.FullEncap.HandoffExtWitness

open Ern.MemoryModel Ern.MemoryModel.Access Ern.Concurrency Ern.Concurrency.MutexReal
open Ern.Concurrency.Corpus Ern.Concurrency.FullEncap.HandoffExt
open Ern.Concurrency.FullEncap.Witness (instDecidableEncap5R)
open Ern.Concurrency.Traces (L0)

/-! ## W-HT -/

/-- Statics of W-HT (Spec 1 §47): `X` (place 0), `Init`, and `Y` (place 1), no leaf `Init`, two
one-leaf locals of the base frame of the same shape; root authorities 0 and 1. -/
def htst : Statics := [((none, none, 0), true), ((none, none, 0), false)]

/-- Initial state of W-HT. -/
def ht0 : SC := SC.ofS3 (S3.init htst)
/-- `a := derive(root_X, Modify)`, authority 2 (O1). -/
def ht1 : SC := ht0.set (deriveEff (ht0.view 0) 0 [0] .modify)
/-- `spawn c1` yielding `a` (WC5.3 C4): context 1, initial frame 1. -/
def ht2 : SC := spawnEff ht1 0 [2] []
/-- Step 1, `c1 : write3(X)` via `a` (O10). -/
def ht3 : SC := ht2.set (write3Eff (ht2.view 1) [0])
/-- Step 2, `c1 : release(a)` (O3), context 1 staying live. -/
def ht4 : SC := ht3.set (releaseEff (ht3.view 1) 2)
/-- Step 3, `c0 : transfer(X, Y)` (O4). -/
def ht5 : SC := transferEffC ht4 0 0 1

/-- The labels of W-HT. -/
def htLbls : List Label :=
  [.kernel 0 (.derive 0 [0] .modify), .spawn 0 [2] [], .kernel 1 (.write 2 [0]),
   .kernel 1 (.release 2), .kernel 0 (.transfer 0 1)]

/-- The named states of W-HT. -/
def htσ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(ht0, [], []), (ht1, [], []), (ht2, [], []), (ht3, [], []), (ht4, [], []), (ht5, [], [])].getD i
    (ht5, [], [])

/-- `corpus-spec2-m3.md` v15 §2 quaterdecies W-HT: the setup and steps 1 to 3 are `ok` at the
kernel (O1; WC5.3 C4; O10.1; O3.1–O3.3; O4: §63.1–§63.9); the trace is a `RunFull` from the
initial state. -/
theorem W_HT_run : opStepC KF (.derive 0 [0] .modify) 0 ht0 (.ok ht1) ∧
    SpawnStep ht1 0 [2] [] (.ok ht2) ∧ opStepC KF (.write 2 [0]) 1 ht2 (.ok ht3) ∧
    opStepC KF (.release 2) 1 ht3 (.ok ht4) ∧ opStepC KF (.transfer 0 1) 0 ht4 (.ok ht5) ∧
    htσ 0 = (SC.ofS3 (S3.init htst), [], []) ∧ RunFull KF L0 htσ htLbls := by
  have s0 : opStepC KF (.derive 0 [0] .modify) 0 ht0 (.ok ht1) :=
    ⟨by decide, _, .ok (by decide), rfl⟩
  have s1 : SpawnStep ht1 0 [2] [] (.ok ht2) := ⟨by decide, .ok (by decide)⟩
  have s2 : opStepC KF (.write 2 [0]) 1 ht2 (.ok ht3) := ⟨by decide, _, .ok (by decide), rfl⟩
  have s3 : opStepC KF (.release 2) 1 ht3 (.ok ht4) := ⟨by decide, _, .ok (by decide), rfl⟩
  have s4 : opStepC KF (.transfer 0 1) 0 ht4 (.ok ht5) := ⟨by decide, .ok (by decide)⟩
  have h : Steps5R KF L0 [(ht0, [], []), (ht1, [], []), (ht2, [], []), (ht3, [], []),
      (ht4, [], []), (ht5, [], [])] htLbls :=
    .cons (by decide) (.kernel s0) <| .cons (by decide) (.spawn s1) <|
    .cons (by decide) (.kernel s2) <| .cons (by decide) (.kernel s3) <|
    .cons (by decide) (.kernel s4) .nil
  exact ⟨s0, s1, s2, s3, s4, rfl,
    runFull_of_run7 (run7_of_run5R (h.run _) (by decide)) (by decide)⟩

/-- `corpus-spec2-m3.md` v15 §2 quaterdecies W-HT, negative: step 3 before step 2 is `reject`
(§63.1: `root_X` has no effective mode on `X` while `a` is active, Spec 1 §43.3). -/
theorem W_HT_neg : opStepC KF (.transfer 0 1) 0 ht3 .reject ∧ effective ht3.flat 0 0 = none :=
  ⟨⟨by decide, .reject (by decide)⟩, by decide⟩

/-! ## W-HT-J -/

/-- W-HT-J, `c1 : terminate` (WC5.3 C7). -/
def htj5 : SC := termEffC ht4 1
/-- W-HT-J, step 3 after `join`, `c0 : transfer(X, Y)` (O4). -/
def htj6 : SC := transferEffC htj5 0 0 1

/-- The labels of W-HT-J. -/
def htjLbls : List Label :=
  [.kernel 0 (.derive 0 [0] .modify), .spawn 0 [2] [], .kernel 1 (.write 2 [0]),
   .kernel 1 (.release 2), .terminate 1, .join 0 1, .kernel 0 (.transfer 0 1)]

/-- The named states of W-HT-J. -/
def htjσ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(ht0, [], []), (ht1, [], []), (ht2, [], []), (ht3, [], []), (ht4, [], []), (htj5, [], []),
    (htj5, [], []), (htj6, [], [])].getD i (htj6, [], [])

/-- `corpus-spec2-m3.md` v15 §2 quaterdecies W-HT-J: steps 1 and 2, `c1 : terminate` (WC5.3 C7),
`c0 : join(c1)` (C8), step 3, all `ok`; the trace is a `RunFull` from the initial state. -/
theorem W_HTJ_run : TermStep KF ht4 1 (.ok htj5) ∧ JoinStep htj5 0 1 (.ok htj5) ∧
    opStepC KF (.transfer 0 1) 0 htj5 (.ok htj6) ∧ RunFull KF L0 htjσ htjLbls := by
  obtain ⟨s0, s1, s2, s3, -⟩ := W_HT_run
  have t : TermStep KF ht4 1 (.ok htj5) := ⟨by decide, .ok (by decide)⟩
  have j : JoinStep htj5 0 1 (.ok htj5) := .ok (by decide) (by decide)
  have s4 : opStepC KF (.transfer 0 1) 0 htj5 (.ok htj6) := ⟨by decide, .ok (by decide)⟩
  have h : Steps5R KF L0 [(ht0, [], []), (ht1, [], []), (ht2, [], []), (ht3, [], []),
      (ht4, [], []), (htj5, [], []), (htj5, [], []), (htj6, [], [])] htjLbls :=
    .cons (by decide) (.kernel s0) <| .cons (by decide) (.spawn s1) <|
    .cons (by decide) (.kernel s2) <| .cons (by decide) (.kernel s3) <|
    .cons (by decide) (.terminate t) <| .cons (by decide) (.join j) <|
    .cons (by decide) (.kernel s4) .nil
  exact ⟨t, j, s4, runFull_of_run7 (run7_of_run5R (h.run _) (by decide)) (by decide)⟩

/-- `corpus-spec2-m3.md` v15 §2 quaterdecies W-HT, graph: `(1, 3, X)` (steps 2 and 4 of the
trace) is an extended exclusive pair (`write3` requires `Modify`, §67.1; `transfer` requires
`Modify` on its source, §63.1); its frontier is step 2 of the corpus (index 3), a step of `c1`; no
strict `hb` path joins the two steps: extended race, no extended handoff order. -/
theorem W_HT_graph : ExtPair KF L0 htσ htLbls 2 4 0 ∧ IsFrontier KF htσ htLbls 2 4 0 3 ∧
    (htLbls[3]?).map Label.ctx = some 1 ∧ ¬ HBS htσ L0 htLbls (.step 2) (.step 4) ∧
    ¬ HandoffOrderedExtAtS KF htσ L0 htLbls 2 4 0 ∧ RaceExtS KF L0 htσ htLbls := by
  have hp : ExtPair KF L0 htσ htLbls 2 4 0 := by decide
  have hn : ¬ HBS htσ L0 htLbls (.step 2) (.step 4) := by decide
  exact ⟨hp, by decide, rfl, hn, by decide, 2, 4, 0, hp, hn⟩

/-- W-HT-J, graph: the same pair; its frontier is the same step; it is ordered: step 1 →`po`
`terminate(c1)` →`sw` `join(c1)` →`po` step 3; extended handoff order. -/
theorem W_HTJ_graph : ExtPair KF L0 htjσ htjLbls 2 6 0 ∧ IsFrontier KF htjσ htjLbls 2 6 0 3 ∧
    PO htjσ htjLbls (.step 2) (.step 4) ∧ SWS htjσ L0 htjLbls (.step 4) (.step 5) ∧
    PO htjσ htjLbls (.step 5) (.step 6) ∧ HBS htjσ L0 htjLbls (.step 2) (.step 6) ∧
    HandoffOrderedExtAtS KF htjσ L0 htjLbls 2 6 0 := by
  decide

/-- W-HT: the pair is not an `ExclPair` of the event pass (step 4 is no access, `Label.Access`). -/
theorem W_HT_notExcl : ¬ ExclPair htLbls 2 4 0 := by
  rintro ⟨-, hj, c, c', m, m', -, -, haj, -⟩
  exact haj

/-! ## W-HS -/

/-- Statics of W-HS (Spec 1 §47): `X` (place 0) and `Z` (place 1), one-leaf locals of the base
frame, `Init`; root authorities 0 and 1. -/
def hsst : Statics := [((none, none, 0), true), ((none, none, 0), true)]

/-- Initial state of W-HS. -/
def hs0 : SC := SC.ofS3 (S3.init hsst)
/-- `a := derive(root_X, Modify)`, authority 2 (O1). -/
def hs1 : SC := hs0.set (deriveEff (hs0.view 0) 0 [0] .modify)
/-- `z := derive(root_Z, Modify)`, authority 3 (O1). -/
def hs2 : SC := hs1.set (deriveEff (hs1.view 0) 1 [1] .modify)
/-- `spawn c1` yielding `a`, `z` staying held by frame 0 (WC5.3 C4). -/
def hs3 : SC := spawnEff hs2 0 [2] []
/-- Step 1, `c1 : write3(X)` via `a` (O10). -/
def hs4 : SC := hs3.set (write3Eff (hs3.view 1) [0])
/-- Step 2, `c1 : release(a)` (O3). -/
def hs5 : SC := hs4.set (releaseEff (hs4.view 1) 2)
/-- Step 3, `c0 : store(z, X)` (O8). -/
def hs6 : SC := storeEffC hs5 0 3 0

/-- The labels of W-HS. -/
def hsLbls : List Label :=
  [.kernel 0 (.derive 0 [0] .modify), .kernel 0 (.derive 1 [1] .modify), .spawn 0 [2] [],
   .kernel 1 (.write 2 [0]), .kernel 1 (.release 2), .kernel 0 (.store 3 0)]

/-- The named states of W-HS. -/
def hsσ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(hs0, [], []), (hs1, [], []), (hs2, [], []), (hs3, [], []), (hs4, [], []), (hs5, [], []),
    (hs6, [], [])].getD i (hs6, [], [])

/-- `corpus-spec2-m3.md` v15 §2 quaterdecies W-HS: the setup and steps 1 to 3 are `ok` at the
kernel (O1; WC5.3 C4; O10.1; O3.1–O3.3; O8: §65.1–§65.5); the trace is a `RunFull` from the
initial state. -/
theorem W_HS_run : opStepC KF (.write 2 [0]) 1 hs3 (.ok hs4) ∧
    opStepC KF (.release 2) 1 hs4 (.ok hs5) ∧ opStepC KF (.store 3 0) 0 hs5 (.ok hs6) ∧
    hsσ 0 = (SC.ofS3 (S3.init hsst), [], []) ∧ RunFull KF L0 hsσ hsLbls := by
  have d0 : opStepC KF (.derive 0 [0] .modify) 0 hs0 (.ok hs1) :=
    ⟨by decide, _, .ok (by decide), rfl⟩
  have d1 : opStepC KF (.derive 1 [1] .modify) 0 hs1 (.ok hs2) :=
    ⟨by decide, _, .ok (by decide), rfl⟩
  have sp : SpawnStep hs2 0 [2] [] (.ok hs3) := ⟨by decide, .ok (by decide)⟩
  have s1 : opStepC KF (.write 2 [0]) 1 hs3 (.ok hs4) := ⟨by decide, _, .ok (by decide), rfl⟩
  have s2 : opStepC KF (.release 2) 1 hs4 (.ok hs5) := ⟨by decide, _, .ok (by decide), rfl⟩
  have s3 : opStepC KF (.store 3 0) 0 hs5 (.ok hs6) := ⟨by decide, .ok (by decide)⟩
  have h : Steps5R KF L0 [(hs0, [], []), (hs1, [], []), (hs2, [], []), (hs3, [], []),
      (hs4, [], []), (hs5, [], []), (hs6, [], [])] hsLbls :=
    .cons (by decide) (.kernel d0) <| .cons (by decide) (.kernel d1) <|
    .cons (by decide) (.spawn sp) <| .cons (by decide) (.kernel s1) <|
    .cons (by decide) (.kernel s2) <| .cons (by decide) (.kernel s3) .nil
  exact ⟨s1, s2, s3, rfl, runFull_of_run7 (run7_of_run5R (h.run _) (by decide)) (by decide)⟩

/-- `corpus-spec2-m3.md` v15 §2 quaterdecies W-HS, negative: step 3 before step 2 is `reject`
(§65.2: `Modify` is not exercisable on `X` while `a` is active, Spec 1 §43.3). -/
theorem W_HS_neg : opStepC KF (.store 3 0) 0 hs4 .reject ∧ effective hs4.flat 0 0 = none :=
  ⟨⟨by decide, .reject (by decide)⟩, by decide⟩

/-- W-HS-J, `c1 : terminate` (WC5.3 C7). -/
def hsj6 : SC := termEffC hs5 1
/-- W-HS-J, step 3 after `join`, `c0 : store(z, X)` (O8). -/
def hsj7 : SC := storeEffC hsj6 0 3 0

/-- The labels of W-HS-J. -/
def hsjLbls : List Label :=
  [.kernel 0 (.derive 0 [0] .modify), .kernel 0 (.derive 1 [1] .modify), .spawn 0 [2] [],
   .kernel 1 (.write 2 [0]), .kernel 1 (.release 2), .terminate 1, .join 0 1,
   .kernel 0 (.store 3 0)]

/-- The named states of W-HS-J. -/
def hsjσ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(hs0, [], []), (hs1, [], []), (hs2, [], []), (hs3, [], []), (hs4, [], []), (hs5, [], []),
    (hsj6, [], []), (hsj6, [], []), (hsj7, [], [])].getD i (hsj7, [], [])

/-- `corpus-spec2-m3.md` v15 §2 quaterdecies W-HS-J: steps 1 and 2, `terminate`, `join`, step 3,
all `ok`; the trace is a `RunFull` from the initial state. -/
theorem W_HSJ_run : TermStep KF hs5 1 (.ok hsj6) ∧ JoinStep hsj6 0 1 (.ok hsj6) ∧
    opStepC KF (.store 3 0) 0 hsj6 (.ok hsj7) ∧ RunFull KF L0 hsjσ hsjLbls := by
  have d0 : opStepC KF (.derive 0 [0] .modify) 0 hs0 (.ok hs1) :=
    ⟨by decide, _, .ok (by decide), rfl⟩
  have d1 : opStepC KF (.derive 1 [1] .modify) 0 hs1 (.ok hs2) :=
    ⟨by decide, _, .ok (by decide), rfl⟩
  have sp : SpawnStep hs2 0 [2] [] (.ok hs3) := ⟨by decide, .ok (by decide)⟩
  obtain ⟨s1, s2, -⟩ := W_HS_run
  have t : TermStep KF hs5 1 (.ok hsj6) := ⟨by decide, .ok (by decide)⟩
  have j : JoinStep hsj6 0 1 (.ok hsj6) := .ok (by decide) (by decide)
  have s3 : opStepC KF (.store 3 0) 0 hsj6 (.ok hsj7) := ⟨by decide, .ok (by decide)⟩
  have h : Steps5R KF L0 [(hs0, [], []), (hs1, [], []), (hs2, [], []), (hs3, [], []),
      (hs4, [], []), (hs5, [], []), (hsj6, [], []), (hsj6, [], []), (hsj7, [], [])] hsjLbls :=
    .cons (by decide) (.kernel d0) <| .cons (by decide) (.kernel d1) <|
    .cons (by decide) (.spawn sp) <| .cons (by decide) (.kernel s1) <|
    .cons (by decide) (.kernel s2) <| .cons (by decide) (.terminate t) <|
    .cons (by decide) (.join j) <| .cons (by decide) (.kernel s3) .nil
  exact ⟨t, j, s3, runFull_of_run7 (run7_of_run5R (h.run _) (by decide)) (by decide)⟩

/-- `corpus-spec2-m3.md` v15 §2 quaterdecies W-HS, graph: `(1, 3, X)` (indices 3 and 5) is an
extended exclusive pair (`store` requires `Modify` on its target, §65.2); its frontier is step 2
(index 4), a step of `c1`; no strict `hb` path: extended race, no extended handoff order; it is
not an `ExclPair`. -/
theorem W_HS_graph : ExtPair KF L0 hsσ hsLbls 3 5 0 ∧ IsFrontier KF hsσ hsLbls 3 5 0 4 ∧
    (hsLbls[4]?).map Label.ctx = some 1 ∧ ¬ HBS hsσ L0 hsLbls (.step 3) (.step 5) ∧
    ¬ HandoffOrderedExtAtS KF hsσ L0 hsLbls 3 5 0 ∧ RaceExtS KF L0 hsσ hsLbls ∧
    ¬ ExclPair hsLbls 3 5 0 := by
  have hp : ExtPair KF L0 hsσ hsLbls 3 5 0 := by decide
  have hn : ¬ HBS hsσ L0 hsLbls (.step 3) (.step 5) := by decide
  exact ⟨hp, by decide, rfl, hn, by decide, ⟨3, 5, 0, hp, hn⟩,
    fun ⟨_, _, _, _, _, _, _, _, haj, _⟩ => haj⟩

/-- W-HS-J, graph: the same pair and frontier; ordered by `terminate` and `join`. -/
theorem W_HSJ_graph : ExtPair KF L0 hsjσ hsjLbls 3 7 0 ∧ IsFrontier KF hsjσ hsjLbls 3 7 0 4 ∧
    PO hsjσ hsjLbls (.step 3) (.step 5) ∧ SWS hsjσ L0 hsjLbls (.step 5) (.step 6) ∧
    PO hsjσ hsjLbls (.step 6) (.step 7) ∧ HBS hsjσ L0 hsjLbls (.step 3) (.step 7) ∧
    HandoffOrderedExtAtS KF hsjσ L0 hsjLbls 3 7 0 := by
  decide

/-! ## W-HX -/

/-- W-HX, step 1 from the setup of S1a (`Corpus.p4`), `c1 : write3(X)` via `a` (O10). -/
def hx5 : SC := p4.set (write3Eff (p4.view 1) [0])
/-- Step 2, `c1 : release(a)` (O3). -/
def hx6 : SC := hx5.set (releaseEff (hx5.view 1) 1)
/-- Step 3, `c0 : exitFrameC(f1)` (O7, WC5.3 C6); `X` dies with `f1`. -/
def hx7 : SC := exitEffC hx6 0

/-- The labels of W-HX: the setup of S1a, then steps 1 to 3. -/
def hxLbls : List Label :=
  [.kernel 0 (.enter [] [(none, 0)]), .kernel 0 (.write 0 [0]), .kernel 0 (.derive 0 [0] .modify),
   .spawn 0 [1] [], .kernel 1 (.write 1 [0]), .kernel 1 (.release 1), .kernel 0 .exit]

/-- The named states of W-HX. -/
def hxσ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(p0, [], []), (p1, [], []), (p2, [], []), (p3, [], []), (p4, [], []), (hx5, [], []),
    (hx6, [], []), (hx7, [], [])].getD i (hx7, [], [])

/-- `corpus-spec2-m3.md` v15 §2 quaterdecies W-HX: the setup of S1a and steps 1 to 3 are `ok` at
the kernel (O10.1; O3.1–O3.3; O7.1, O7.2, O7.4; WC5.3 C6); `X` is not usable after step 3; the
trace is a `RunFull` from the initial state. -/
theorem W_HX_run : opStepC KF (.write 1 [0]) 1 p4 (.ok hx5) ∧
    opStepC KF (.release 1) 1 hx5 (.ok hx6) ∧ opStepC KF .exit 0 hx6 (.ok hx7) ∧
    ¬ hx7.flat.Usable 0 ∧ hxσ 0 = (SC.ofS3 (S3.init nost), [], []) ∧ RunFull KF L0 hxσ hxLbls := by
  obtain ⟨e0, w0, d0, sp⟩ := s1a_setup
  have s1 : opStepC KF (.write 1 [0]) 1 p4 (.ok hx5) := ⟨by decide, _, .ok (by decide), rfl⟩
  have s2 : opStepC KF (.release 1) 1 hx5 (.ok hx6) := ⟨by decide, _, .ok (by decide), rfl⟩
  have s3 : opStepC KF .exit 0 hx6 (.ok hx7) := ⟨by decide, .ok (by decide)⟩
  have h : Steps5R KF L0 [(p0, [], []), (p1, [], []), (p2, [], []), (p3, [], []), (p4, [], []),
      (hx5, [], []), (hx6, [], []), (hx7, [], [])] hxLbls :=
    .cons (by decide) (.kernel e0) <| .cons (by decide) (.kernel w0) <|
    .cons (by decide) (.kernel d0) <| .cons (by decide) (.spawn sp) <|
    .cons (by decide) (.kernel s1) <| .cons (by decide) (.kernel s2) <|
    .cons (by decide) (.kernel s3) .nil
  exact ⟨s1, s2, s3, by decide, rfl,
    runFull_of_run7 (run7_of_run5R (h.run _) (by decide)) (by decide)⟩

/-- `corpus-spec2-m3.md` v15 §2 quaterdecies W-HX, negative: step 3 before step 2 is `reject`
(O7.2: an active authority is attached to the dying local `X`; this is S1a). -/
theorem W_HX_neg : opStepC KF .exit 0 hx5 .reject := ⟨by decide, .reject (by decide)⟩

/-- W-HX-J, `c1 : terminate` (WC5.3 C7). -/
def hxj7 : SC := termEffC hx6 1
/-- W-HX-J, step 3 after `join`, `c0 : exitFrameC(f1)` (O7). -/
def hxj8 : SC := exitEffC hxj7 0

/-- The labels of W-HX-J. -/
def hxjLbls : List Label :=
  [.kernel 0 (.enter [] [(none, 0)]), .kernel 0 (.write 0 [0]), .kernel 0 (.derive 0 [0] .modify),
   .spawn 0 [1] [], .kernel 1 (.write 1 [0]), .kernel 1 (.release 1), .terminate 1, .join 0 1,
   .kernel 0 .exit]

/-- The named states of W-HX-J. -/
def hxjσ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(p0, [], []), (p1, [], []), (p2, [], []), (p3, [], []), (p4, [], []), (hx5, [], []),
    (hx6, [], []), (hxj7, [], []), (hxj7, [], []), (hxj8, [], [])].getD i (hxj8, [], [])

/-- `corpus-spec2-m3.md` v15 §2 quaterdecies W-HX-J (the twin of S1a, preceded by step 1): all
steps `ok`; the trace is a `RunFull` from the initial state. -/
theorem W_HXJ_run : TermStep KF hx6 1 (.ok hxj7) ∧ JoinStep hxj7 0 1 (.ok hxj7) ∧
    opStepC KF .exit 0 hxj7 (.ok hxj8) ∧ RunFull KF L0 hxjσ hxjLbls := by
  obtain ⟨e0, w0, d0, sp⟩ := s1a_setup
  obtain ⟨s1, s2, -⟩ := W_HX_run
  have t : TermStep KF hx6 1 (.ok hxj7) := ⟨by decide, .ok (by decide)⟩
  have j : JoinStep hxj7 0 1 (.ok hxj7) := .ok (by decide) (by decide)
  have s3 : opStepC KF .exit 0 hxj7 (.ok hxj8) := ⟨by decide, .ok (by decide)⟩
  have h : Steps5R KF L0 [(p0, [], []), (p1, [], []), (p2, [], []), (p3, [], []), (p4, [], []),
      (hx5, [], []), (hx6, [], []), (hxj7, [], []), (hxj7, [], []), (hxj8, [], [])] hxjLbls :=
    .cons (by decide) (.kernel e0) <| .cons (by decide) (.kernel w0) <|
    .cons (by decide) (.kernel d0) <| .cons (by decide) (.spawn sp) <|
    .cons (by decide) (.kernel s1) <| .cons (by decide) (.kernel s2) <|
    .cons (by decide) (.terminate t) <| .cons (by decide) (.join j) <|
    .cons (by decide) (.kernel s3) .nil
  exact ⟨t, j, s3, runFull_of_run7 (run7_of_run5R (h.run _) (by decide)) (by decide)⟩

/-- `corpus-spec2-m3.md` v15 §2 quaterdecies W-HX, graph: `(1, 3, X)` (indices 4 and 6) is an
extended exclusive pair, `X` dying at step 3 (class D); its frontier is step 2 (index 5), a step of
`c1`; no strict `hb` path: extended race, no extended handoff order; it is not an `ExclPair`. -/
theorem W_HX_graph : ExtPair KF L0 hxσ hxLbls 4 6 0 ∧ ClassD (hxσ 6) (hxσ 7) 0 ∧
    IsFrontier KF hxσ hxLbls 4 6 0 5 ∧ (hxLbls[5]?).map Label.ctx = some 1 ∧
    ¬ HBS hxσ L0 hxLbls (.step 4) (.step 6) ∧ ¬ HandoffOrderedExtAtS KF hxσ L0 hxLbls 4 6 0 ∧
    RaceExtS KF L0 hxσ hxLbls ∧ ¬ ExclPair hxLbls 4 6 0 := by
  have hp : ExtPair KF L0 hxσ hxLbls 4 6 0 := by decide
  have hn : ¬ HBS hxσ L0 hxLbls (.step 4) (.step 6) := by decide
  exact ⟨hp, by decide, by decide, rfl, hn, by decide, ⟨4, 6, 0, hp, hn⟩,
    fun ⟨_, _, _, _, _, _, _, _, haj, _⟩ => haj⟩

/-- W-HX-J, graph: the same pair and frontier; ordered by `terminate` and `join`. -/
theorem W_HXJ_graph : ExtPair KF L0 hxjσ hxjLbls 4 8 0 ∧ IsFrontier KF hxjσ hxjLbls 4 8 0 5 ∧
    PO hxjσ hxjLbls (.step 4) (.step 6) ∧ SWS hxjσ L0 hxjLbls (.step 6) (.step 7) ∧
    PO hxjσ hxjLbls (.step 7) (.step 8) ∧ HBS hxjσ L0 hxjLbls (.step 4) (.step 8) ∧
    HandoffOrderedExtAtS KF hxjσ L0 hxjLbls 4 8 0 := by
  decide

/-! ## W-SV -/

open Ern.Concurrency.Traces (q0 q1 q2 q3 q4 q5 s4st s4_steps) in
/-- W-SV, step 2: `c1 : write3(d)` via `root_d` (authority 4, held by the initial frame of `c1`),
after the by-value `spawn` of S4 (`Traces.q5`). -/
def sv6 : SC := Traces.q5.set (write3Eff (Traces.q5.view 1) [4])

/-- The labels of W-SV: the setup of S4 and its step 1 (`spawnVal c1` moving `v` into `d`), then
step 2. -/
def svLbls : List Label :=
  [.kernel 0 (.enter [] [(none, 0), (none, 0)]), .kernel 0 (.write 1 [1]),
   .kernel 0 (.write 2 [2]), .kernel 0 (.alloc 2 1 [(none, 0)]),
   .spawnVal 0 [] [(none, 0)] [(1, 4)], .kernel 1 (.write 4 [4])]

/-- The named states of W-SV. -/
def svσ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(Traces.q0, [], []), (Traces.q1, [], []), (Traces.q2, [], []), (Traces.q3, [], []),
    (Traces.q4, [], []), (Traces.q5, [], []), (sv6, [], [])].getD i (sv6, [], [])

open Ern.MemoryModel.Access.Examples (K0) in
/-- `corpus-spec2-m3.md` v15 §2 quaterdecies W-SV: step 1 (S4) and step 2 (`c1 : write3(d)` via
`root_d`, O10.1: `root_d` is held by the initial frame of `c1`, WC5.3 C5 item 2, §40; `d` is
usable) are `ok`; the trace is a `RunFull` from the initial state. Negative, after step 1:
`c0 : read3(v)` via `root_v` is `reject` (O9.1: the leaves of `v` are `Moved`). -/
theorem W_SV_run : opStepC K0 (.write 4 [4]) 1 Traces.q5 (.ok sv6) ∧
    opStepC K0 (.read 1 [1]) 0 Traces.q5 .reject ∧ Traces.q5.I 1 = .moved ∧
    svσ 0 = (SC.ofS3 (S3.init Traces.s4st), [], []) ∧ RunFull K0 L0 svσ svLbls := by
  obtain ⟨e0, w1, w2, a3, sv, -⟩ := Traces.s4_steps
  have s2 : opStepC K0 (.write 4 [4]) 1 Traces.q5 (.ok sv6) :=
    ⟨by decide, _, .ok (by decide), rfl⟩
  have h : Steps5R K0 L0 [(Traces.q0, [], []), (Traces.q1, [], []), (Traces.q2, [], []),
      (Traces.q3, [], []), (Traces.q4, [], []), (Traces.q5, [], []), (sv6, [], [])] svLbls :=
    .cons (by decide) (.kernel e0) <| .cons (by decide) (.kernel w1) <|
    .cons (by decide) (.kernel w2) <| .cons (by decide) (.kernel a3) <|
    .cons (by decide) (.spawnVal sv) <| .cons (by decide) (.kernel s2) .nil
  exact ⟨s2, ⟨by decide, _, .reject (by decide), rfl⟩, by decide, rfl,
    runFull_of_run7 (run7_of_run5R (h.run _) (by decide)) (by decide)⟩

open Ern.MemoryModel.Access.Examples (K0) in
/-- `corpus-spec2-m3.md` v15 §2 quaterdecies W-SV, the four facts, for the leaf `l = 4` of `d`:
the pair `(1, 2, l)` (indices 4 and 5) is an extended exclusive pair (step 1 creates and writes
`l`, class C; step 2 requires `Modify`); its frontier is step 1 itself, `c0` having no capability
on `l` after it; the search from `k > i` of the event pass (`lossStep`) gives step 2, which is
neither strictly before `j` nor a step of the creator; the pair is ordered by the creation edge of
the strict graph, which the strict graph gives to `spawnVal` (`SWS`, `Label.creates`). -/
theorem W_SV_graph : ExtPair K0 L0 svσ svLbls 4 5 4 ∧ ClassC (svσ 4) (svσ 5) 4 ∧
    cap5 Traces.q5 [] 0 4 = none ∧ IsFrontier K0 svσ svLbls 4 5 4 4 ∧
    lossStep svσ svLbls 4 5 4 = some 5 ∧ ¬ (5 < 5) ∧
    (svLbls[5]?).map Label.ctx ≠ (svLbls[4]?).map Label.ctx ∧
    SWS svσ L0 svLbls (.step 4) (.start 4) ∧ PO svσ svLbls (.start 4) (.step 5) ∧
    HBS svσ L0 svLbls (.step 4) (.step 5) ∧ HandoffOrderedExtAtS K0 svσ L0 svLbls 4 5 4 := by
  decide

/-! ## W-NM -/

open Ern.Concurrency.Corpus.MutexEdge (rl0σ rl0Lbls) in
/-- `corpus-spec2-m3.md` v15 §2 quaterdecies W-NM: the steps 1 to 4 of block MX (`MX₄`), then
`c1 : acquire(e)`, form a `RunFull` from the initial state (a prefix of W-RL₀). -/
theorem W_NM_run : RunFull KM L0 rl0σ (rl0Lbls.take 6) :=
  Replay.RunFull.take NonRegression.runAmF_traces_full.2.2.2.2.2.2.1 6

open Ern.Concurrency.Corpus.MutexEdge (rl0σ rl0Lbls) in
/-- `corpus-spec2-m3.md` v15 §2 quaterdecies W-NM, the three facts: `(newMutex, acquire, lock)`
(indices 2 and 5, `lock` the place 2) is an extended exclusive pair (`newMutex` requires `Modify`
on the controller, WC5.3 C13 item 11; `acquire` requires `Observe`, C14 item 3); its frontier is
the `derive` of step 4 (index 3), a step of `c0` strictly between them, where the capability of
`c0` on `lock` goes from `Modify` to `Observe` (§43.4); it is ordered: `derive` →`po` `spawn c1`
→`sw` `start(c1)` →`po` `acquire`; extended handoff order. -/
theorem W_NM_graph : ExtPair KM L0 rl0σ (rl0Lbls.take 6) 2 5 2 ∧
    IsFrontier KM rl0σ (rl0Lbls.take 6) 2 5 2 3 ∧
    cap5 (rl0σ 3).1 (rl0σ 3).2.1 0 2 = some .modify ∧
    cap5 (rl0σ 4).1 (rl0σ 4).2.1 0 2 = some .observe ∧
    PO rl0σ (rl0Lbls.take 6) (.step 3) (.step 4) ∧
    SWS rl0σ L0 (rl0Lbls.take 6) (.step 4) (.start 4) ∧
    PO rl0σ (rl0Lbls.take 6) (.start 4) (.step 5) ∧
    HandoffOrderedExtAtS KM rl0σ L0 (rl0Lbls.take 6) 2 5 2 := by
  decide

/-! ## W-TR and W-TR-J -/

open Ern.Concurrency.Corpus.MutexEdge (trσ trLbls) in
/-- `corpus-spec2-m3.md` v15 §2 quaterdecies, W-TR: `(unlock, transfer, lock)` (indices 7 and 9)
and `(acquire, transfer, lock)` (indices 5 and 9) are extended exclusive pairs (`unlock` and
`acquire` require `Observe` on the controller, WC5.3 C17 item 4, C14 item 3; `transfer` requires
`Modify` on its source, of which `lock` is a leaf, §63.1); their frontier is step 4 of P,
`c1 : release(o1)` (index 8); no strict `hb` path from `c1` to the `transfer`: extended races, no
extended handoff order. -/
theorem W_TR_graph : ExtPair KM L0 trσ trLbls 7 9 2 ∧ ExtPair KM L0 trσ trLbls 5 9 2 ∧
    IsFrontier KM trσ trLbls 7 9 2 8 ∧ IsFrontier KM trσ trLbls 5 9 2 8 ∧
    ¬ HBS trσ L0 trLbls (.step 7) (.step 9) ∧ ¬ HBS trσ L0 trLbls (.step 5) (.step 9) ∧
    ¬ HandoffOrderedExtAtS KM trσ L0 trLbls 7 9 2 ∧
    ¬ HandoffOrderedExtAtS KM trσ L0 trLbls 5 9 2 := by
  decide

open Ern.Concurrency.Corpus.MutexEdge (trjσ trjLbls) in
/-- `corpus-spec2-m3.md` v15 §2 quaterdecies, W-TR-J: the same pairs (indices 7, 5 and 11), the
same frontier; ordered by `terminate` and `join`; extended handoff order. -/
theorem W_TRJ_graph : ExtPair KM L0 trjσ trjLbls 7 11 2 ∧ ExtPair KM L0 trjσ trjLbls 5 11 2 ∧
    IsFrontier KM trjσ trjLbls 7 11 2 8 ∧ IsFrontier KM trjσ trjLbls 5 11 2 8 ∧
    HBS trjσ L0 trjLbls (.step 7) (.step 11) ∧ HBS trjσ L0 trjLbls (.step 5) (.step 11) ∧
    HandoffOrderedExtAtS KM trjσ L0 trjLbls 7 11 2 ∧
    HandoffOrderedExtAtS KM trjσ L0 trjLbls 5 11 2 := by
  decide

/-! ## W-CR -/

/-- W-CR, `c0 : read3(lock)` via `root_M` (O9). -/
def crx : SC := x2.set (x2.view 0)

open Ern.Concurrency.Corpus.MutexEdge (rl0σ rl0Lbls) in
/-- `corpus-spec2-m3.md` v15 §2 quaterdecies W-CR. From `MX₃`, reached from the initial state by
the admitted prefix of W-RL₀ (steps 1 to 3 of block MX, a `RunFull`), `c0 : read3(lock)` via
`root_M` is `ok` at the kernel (O9.1, O9.2, O9.3) and excluded by the complete encapsulation by
WC5.3 C22 item 4 alone: it satisfies the guard-free forms (`PremG`, C22 item 6) and the conjuncts
`Encap` and `ChainExcl`, and fails both encodings of item 4, the restriction of ordinary accesses
to the controller (`CtlExcl`, "does not expose ordinary `read3` of `ControlOf(entry)`") and the
final restriction (`CtlRestrF`): `lock` is the controller of the live entry `e`. This is a local
verdict: a trace containing the step is not a `RunFull`. -/
theorem W_CR_excluded : RunFull KM L0 rl0σ (rl0Lbls.take 3) ∧ rl0σ 3 = (x2, regX, []) ∧
    opStepC KM (.read 0 [2]) 0 x2 (.ok crx) ∧
    PremG KM L0 (x2, regX, []) (.kernel 0 (.read 0 [2])) ∧
    Encap L0 (x2, regX) (.kernel 0 (.read 0 [2])) ∧ ChainExcl (x2, regX) (.kernel 0 (.read 0 [2])) ∧
    ¬ CtlExcl L0 (x2, regX) (.kernel 0 (.read 0 [2])) ∧
    ¬ CtlRestrF L0 (x2, regX, []) (.kernel 0 (.read 0 [2])) (crx, regX, []) ∧
    ¬ EncapFull KM L0 (x2, regX, []) (.kernel 0 (.read 0 [2])) (crx, regX, []) := by
  have hc : ¬ CtlRestrF L0 (x2, regX, []) (.kernel 0 (.read 0 [2])) (crx, regX, []) := by decide
  exact ⟨Replay.RunFull.take NonRegression.runAmF_traces_full.2.2.2.2.2.2.1 3, rfl,
    ⟨by decide, _, .ok (by decide), rfl⟩, by decide, by decide, by decide, by decide, hc,
    fun h => hc h.1.2⟩

/-- The labels of the twin of W-CR: steps 1 and 2 of block MX, then `c0 : read3(lock)` via
`root_M`, before `newMutex`. -/
def crjLbls : List Label :=
  [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 3 1), .kernel 0 (.read 0 [2])]

/-- The named states of the twin of W-CR. -/
def crjσ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(x0, [], []), (x1, [], []), (x2, [], []), (crx, [], [])].getD i (crx, [], [])

/-- `corpus-spec2-m3.md` v15 §2 quaterdecies W-CR, twin: the same read before `newMutex` is `ok`
and admitted (`lock` is the controller of no live entry); the trace is a `RunFull` from the
initial state. -/
theorem W_CR_twin : crjσ 0 = (SC.ofS3 (S3.init mxst), [], []) ∧ RunFull KM L0 crjσ crjLbls := by
  have hr : opStepC KM (.read 0 [2]) 0 x2 (.ok crx) := ⟨by decide, _, .ok (by decide), rfl⟩
  have h : Steps5R KM L0 [(x0, [], []), (x1, [], []), (x2, [], []), (crx, [], [])] crjLbls :=
    .cons (by decide) (.kernel mx_steps.1) <| .cons (by decide) (.kernel mx_steps.2.1) <|
    .cons (by decide) (.kernel hr) .nil
  exact ⟨rfl, runFull_of_run7 (run7_of_run5R (h.run _) (by decide)) (by decide)⟩

end Ern.Concurrency.FullEncap.HandoffExtWitness
