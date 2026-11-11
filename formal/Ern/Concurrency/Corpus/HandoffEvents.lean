import Ern.Concurrency.EventsCompose
import Ern.Concurrency.Corpus.Handoff
import Ern.Concurrency.Corpus.GuardedChainC

/-!
# Handoff witnesses on the event graph

`corpus-spec2-m3.md` v8 §2 septies, on the event graph of `Ern.Concurrency.Events`. Each trace is
given with its named states and is a `Run5R` from the initial state of Spec 1 §47 (no mutex, empty
registries), except the locked trace of `Corpus/GuardedChainC.lean`, which registers a mutex. Facts
written from `corpus-spec2-m3.md` v8 §2 septies, decided by `decide`.
-/

namespace Ern.Concurrency.Corpus.HandoffEvents

open Ern.MemoryModel.Access Ern.Concurrency Ern.Concurrency.Corpus Ern.Concurrency.Corpus.Handoff
open Ern.Concurrency.Traces (L0)

/-- A step without a registered entry extends a run through explicit states (`encap5R_nil`). -/
theorem Steps5R.consNil {k : K} {L : MutexLayout} {s : SC} {ar : ArenaReg}
    {st' : SC × SyncReg × ArenaReg} {sts : List (SC × SyncReg × ArenaReg)} {lbl : Label}
    {lbls : List Label} (h : LStep k L lbl (s, [], ar) st') (hs : Steps5R k L (st' :: sts) lbls) :
    Steps5R k L ((s, [], ar) :: st' :: sts) (lbl :: lbls) :=
  .cons (encap5R_nil h) h hs

/-! ## W-HO -/

/-- The labels of W-HO (`w_ho_trace`). -/
def hoLbls : List Label :=
  [.kernel 0 (.derive 0 [1, 2] .modify), .spawn 0 [1] [], .kernel 1 (.write 1 [1, 2]),
   .kernel 1 (.release 1), .kernel 0 (.write 0 [1, 2])]

/-- The states of W-HO. -/
def hoSts : List (SC × SyncReg × ArenaReg) :=
  [(t0, [], []), (t1, [], []), (t2, [], []), (h1, [], []), (h2, [], []), (h3, [], [])]

/-- The named states of W-HO. -/
def hoσ (i : Nat) : SC × SyncReg × ArenaReg := hoSts.getD i (h3, [], [])

/-- W-HO from the initial state of S13 is a `Run5R`. -/
theorem W_HO_run : hoσ 0 = (SC.ofS3 (S3.init xst), [], []) ∧ Run5R KF L0 hoσ hoLbls := by
  obtain ⟨h0, hs, -⟩ := S13_1_reject
  exact ⟨rfl, (Steps5R.consNil (.kernel h0) <| Steps5R.consNil (.spawn hs) <|
    Steps5R.consNil (.kernel W_HO_1_ok) <| Steps5R.consNil (.kernel W_HO_2_ok) <|
    Steps5R.consNil (.kernel W_HO_3_ok.2) .nil).run _⟩

/-- `corpus-spec2-m3.md` v8 §2 septies W-HO: the writes of `X` by context 1 (step 2) and by context
0 (step 4) form an exclusive pair on each leaf of `X`. -/
theorem W_HO_excl : ∀ l ∈ [1, 2], ExclPair hoLbls 2 4 l := fun _ hl =>
  ⟨by decide, by decide, 0, 1, .modify, .modify, by decide, ⟨rfl, hl, rfl⟩, ⟨rfl, hl, rfl⟩,
    Or.inl rfl⟩

/-- `corpus-spec2-m3.md` v8 §2 septies W-HO: no `hb` path from the write of context 1 to the write
of context 0 (no `sw` edge leaves context 1: neither `terminate` nor `join`). -/
theorem W_HO_noHb : ¬ HB hoσ hoLbls (.step 2) (.step 4) := by decide

/-- `corpus-spec2-m3.md` v8 §2 septies W-HO: the pair violates `HandoffOrdered` (WC5.1 C46) on each
leaf of `X`; so the trace is not `HandoffOrdered` and has a `Race`. -/
theorem W_HO_unordered : (∀ l ∈ [1, 2], ¬ HandoffOrderedAt hoσ hoLbls 2 4 l) ∧
    ¬ HandoffOrdered hoσ hoLbls ∧ Race hoσ hoLbls :=
  ⟨by decide, fun h => (by decide : ¬ HandoffOrderedAt hoσ hoLbls 2 4 1) (h 2 4 1 (W_HO_excl 1
    (by decide))), ⟨2, 4, 1, W_HO_excl 1 (by decide), W_HO_noHb⟩⟩

/-! ## W-HO′ -/

/-- The labels of W-HO′ (`w_ho2_trace`). -/
def ho2Lbls : List Label :=
  [.kernel 0 (.derive 0 [0] .modify), .kernel 0 (.derive 1 [0] .modify), .spawn 0 [1] [],
   .kernel 0 (.write 2 [0]), .kernel 0 (.release 2), .kernel 1 (.write 1 [0])]

/-- The states of W-HO′. -/
def ho2Sts : List (SC × SyncReg × ArenaReg) :=
  [(k0, [], []), (k1, [], []), (k2, [], []), (k3, [], []), (k4, [], []), (k5, [], []),
   (k6, [], [])]

/-- The named states of W-HO′. -/
def ho2σ (i : Nat) : SC × SyncReg × ArenaReg := ho2Sts.getD i (k6, [], [])

/-- W-HO′ from the initial state is a `Run5R`. -/
theorem W_HO2_run : ho2σ 0 = (SC.ofS3 (S3.init yst), [], []) ∧ Run5R KF L0 ho2σ ho2Lbls := by
  obtain ⟨d1, d2, hs⟩ := W_HO2_0_ok
  exact ⟨rfl, (Steps5R.consNil (.kernel d1) <| Steps5R.consNil (.kernel d2) <|
    Steps5R.consNil (.spawn hs) <| Steps5R.consNil (.kernel W_HO2_2_ok) <|
    Steps5R.consNil (.kernel W_HO2_3_ok) <| Steps5R.consNil (.kernel W_HO2_4_ok) .nil).run _⟩

/-- `corpus-spec2-m3.md` v8 §2 septies W-HO′: the write of `X` by context 0 via `b` (step 3) and
the write of `X` by context 1 via `a` (step 5) form an exclusive pair. -/
theorem W_HO2_excl : ExclPair ho2Lbls 3 5 0 :=
  ⟨by decide, by decide, 1, 0, .modify, .modify, by decide, ⟨rfl, by decide, rfl⟩,
    ⟨rfl, by decide, rfl⟩, Or.inl rfl⟩

/-- `corpus-spec2-m3.md` v8 §2 septies W-HO′: no `hb` path from the write of context 0 to the write
of context 1 (the only `sw` edge from context 0 to context 1 is that of the `spawn`, step 2,
before the write of context 0). -/
theorem W_HO2_noHb : ¬ HB ho2σ ho2Lbls (.step 3) (.step 5) := by decide

/-- `corpus-spec2-m3.md` v8 §2 septies W-HO′: the pair violates `HandoffOrdered` (WC5.1 C46). -/
theorem W_HO2_unordered : ¬ HandoffOrderedAt ho2σ ho2Lbls 3 5 0 ∧ ¬ HandoffOrdered ho2σ ho2Lbls ∧
    Race ho2σ ho2Lbls :=
  ⟨by decide, fun h => (by decide : ¬ HandoffOrderedAt ho2σ ho2Lbls 3 5 0) (h 3 5 0 W_HO2_excl),
    ⟨3, 5, 0, W_HO2_excl, W_HO2_noHb⟩⟩

/-! ## W-HO″ -/

/-- The labels of W-HO″ (`w_ho3_trace`). -/
def ho3Lbls : List Label :=
  [.kernel 0 (.derive 0 [0] .modify), .spawn 0 [1] [], .kernel 1 (.derive 1 [0] .modify),
   .spawn 1 [2] [], .kernel 2 (.write 2 [0]), .kernel 2 (.release 2), .kernel 1 (.release 1),
   .terminate 1, .join 0 1, .kernel 0 (.write 0 [0])]

/-- The states of W-HO″. -/
def ho3Sts : List (SC × SyncReg × ArenaReg) :=
  [(k0, [], []), (m1, [], []), (m2, [], []), (m3, [], []), (m4, [], []), (m5, [], []),
   (m6, [], []), (m7, [], []), (m8, [], []), (m8, [], []), (m9, [], [])]

/-- The named states of W-HO″. -/
def ho3σ (i : Nat) : SC × SyncReg × ArenaReg := ho3Sts.getD i (m9, [], [])

/-- W-HO″ from the initial state is a `Run5R`. -/
theorem W_HO3_run : ho3σ 0 = (SC.ofS3 (S3.init yst), [], []) ∧ Run5R KF L0 ho3σ ho3Lbls := by
  obtain ⟨d1, s1, d2, s2, -⟩ := w_ho3_setup
  exact ⟨rfl, (Steps5R.consNil (.kernel d1) <| Steps5R.consNil (.spawn s1) <|
    Steps5R.consNil (.kernel d2) <| Steps5R.consNil (.spawn s2) <|
    Steps5R.consNil (.kernel W_HO3_1_ok) <| Steps5R.consNil (.kernel W_HO3_2_ok) <|
    Steps5R.consNil (.kernel W_HO3_3_ok) <| Steps5R.consNil (.terminate W_HO3_4_ok.2.1) <|
    Steps5R.consNil (.join W_HO3_5_ok) <| Steps5R.consNil (.kernel W_HO3_6_ok.2) .nil).run _⟩

/-- `corpus-spec2-m3.md` v8 §2 septies W-HO″: the write of `X` by context 2 (step 4) and the write
of `X` by context 0 (step 9) form an exclusive pair. -/
theorem W_HO3_excl : ExclPair ho3Lbls 4 9 0 :=
  ⟨by decide, by decide, 0, 2, .modify, .modify, by decide, ⟨rfl, by decide, rfl⟩,
    ⟨rfl, by decide, rfl⟩, Or.inl rfl⟩

/-- `corpus-spec2-m3.md` v8 §2 septies W-HO″: the successful `join(c1)` by context 0 (step 8, an
`ok` step of the run) lies between the two writes. -/
theorem W_HO3_join_between : ho3Lbls[8]?.bind Label.joinOf = some 1 ∧ 4 < 8 ∧ 8 < 9 ∧
    JoinStep (ho3σ 8).1 0 1 (.ok (ho3σ 9).1) :=
  ⟨rfl, by decide, by decide, W_HO3_5_ok⟩

/-- `corpus-spec2-m3.md` v8 §2 septies W-HO″: no `hb` path from the write of context 2 to the write
of context 0, despite the successful `join(c1)` (no `sw` edge leaves context 2: it neither
terminates nor is joined). -/
theorem W_HO3_noHb : ¬ HB ho3σ ho3Lbls (.step 4) (.step 9) := by decide

/-- `corpus-spec2-m3.md` v8 §2 septies W-HO″: the pair violates `HandoffOrdered` (WC5.1 C46). -/
theorem W_HO3_unordered : ¬ HandoffOrderedAt ho3σ ho3Lbls 4 9 0 ∧ ¬ HandoffOrdered ho3σ ho3Lbls ∧
    Race ho3σ ho3Lbls :=
  ⟨by decide, fun h => (by decide : ¬ HandoffOrderedAt ho3σ ho3Lbls 4 9 0) (h 4 9 0 W_HO3_excl),
    ⟨4, 9, 0, W_HO3_excl, W_HO3_noHb⟩⟩

/-! ## W-HO-J -/

/-- W-HO-J, `c1 : terminate` (WC5.1 C7). -/
def j5 : SC := termEffC h2 1
/-- W-HO-J, `c0 : write3(X)` via `root_X` (O10). -/
def j7 : SC := j5.set (write3Eff (j5.view 0) [1, 2])

/-- `corpus-spec2-m3.md` v8 §2 septies W-HO-J, after the steps of W-HO up to `c1 : release(a)`
(`W_HO_1_ok`, `W_HO_2_ok`): `c1 : terminate` `ok` (WC5.1 C7), `c0 : join(c1)` `ok` (WC5.1 C8),
`c0 : write3(X)` via `root_X` `ok` (O10.1). -/
theorem W_HOJ_ok : TermStep KF h2 1 (.ok j5) ∧ JoinStep j5 0 1 (.ok j5) ∧
    opStepC KF (.write 0 [1, 2]) 0 j5 (.ok j7) :=
  ⟨⟨by decide, .ok (by decide)⟩, .ok (by decide) (by decide), ⟨by decide, _, .ok (by decide), rfl⟩⟩

/-- The labels of W-HO-J. -/
def hojLbls : List Label :=
  [.kernel 0 (.derive 0 [1, 2] .modify), .spawn 0 [1] [], .kernel 1 (.write 1 [1, 2]),
   .kernel 1 (.release 1), .terminate 1, .join 0 1, .kernel 0 (.write 0 [1, 2])]

/-- The states of W-HO-J. -/
def hojSts : List (SC × SyncReg × ArenaReg) :=
  [(t0, [], []), (t1, [], []), (t2, [], []), (h1, [], []), (h2, [], []), (j5, [], []),
   (j5, [], []), (j7, [], [])]

/-- The named states of W-HO-J. -/
def hojσ (i : Nat) : SC × SyncReg × ArenaReg := hojSts.getD i (j7, [], [])

/-- W-HO-J from the initial state of S13 is a `Run5R`. -/
theorem W_HOJ_run : hojσ 0 = (SC.ofS3 (S3.init xst), [], []) ∧ Run5R KF L0 hojσ hojLbls := by
  obtain ⟨h0, hs, -⟩ := S13_1_reject
  obtain ⟨ht, hj, hw⟩ := W_HOJ_ok
  exact ⟨rfl, (Steps5R.consNil (.kernel h0) <| Steps5R.consNil (.spawn hs) <|
    Steps5R.consNil (.kernel W_HO_1_ok) <| Steps5R.consNil (.kernel W_HO_2_ok) <|
    Steps5R.consNil (.terminate ht) <| Steps5R.consNil (.join hj) <|
    Steps5R.consNil (.kernel hw) .nil).run _⟩

/-- `corpus-spec2-m3.md` v8 §2 septies W-HO-J is an `EncapsulatedTrace5R` from the initial
state. -/
theorem W_HOJ_trace : EncapsulatedTrace5R KF L0 (t0, [], []) hojLbls (j7, [], []) :=
  run5R_trace W_HOJ_run.2

/-- `corpus-spec2-m3.md` v8 §2 septies W-HO-J: the writes of `X` by context 1 (step 2) and by
context 0 (step 6) form an exclusive pair on each leaf of `X`. -/
theorem W_HOJ_excl : ∀ l ∈ [1, 2], ExclPair hojLbls 2 6 l := fun _ hl =>
  ⟨by decide, by decide, 0, 1, .modify, .modify, by decide, ⟨rfl, hl, rfl⟩, ⟨rfl, hl, rfl⟩,
    Or.inl rfl⟩

/-- `corpus-spec2-m3.md` v8 §2 septies W-HO-J, expected `hb` path: write of context 1 →`po`
`terminate(c1)` →`sw` `join(c1)` →`po` write of context 0; the pair is ordered by `hb` and
satisfies `HandoffOrdered` (WC5.1 C46) on each leaf of `X`. -/
theorem W_HOJ_ordered : PO hojσ hojLbls (.step 2) (.step 4) ∧ SW hojLbls (.step 4) (.step 5) ∧
    PO hojσ hojLbls (.step 5) (.step 6) ∧ HB hojσ hojLbls (.step 2) (.step 6) ∧
    ∀ l ∈ [1, 2], HandoffOrderedAt hojσ hojLbls 2 6 l := by
  decide

/-! ## W-HO″-J -/

/-- W-HO″-J, `c2 : terminate` (WC5.1 C7). -/
def n7 : SC := termEffC m6 2
/-- W-HO″-J, `c1 : release(a)` (O3). -/
def n9 : SC := n7.set (releaseEff (n7.view 1) 1)
/-- W-HO″-J, `c1 : terminate` (WC5.1 C7). -/
def n10 : SC := termEffC n9 1
/-- W-HO″-J, `c0 : write3(X)` via `root_X` (O10). -/
def n12 : SC := n10.set (write3Eff (n10.view 0) [0])

/-- `corpus-spec2-m3.md` v8 §2 septies W-HO″-J, after the steps of W-HO″ up to `c2 : release(a₂)`
(`w_ho3_setup`, `W_HO3_1_ok`, `W_HO3_2_ok`): `c2 : terminate` `ok` (WC5.1 C7), `c1 : join(c2)`
`ok` (WC5.1 C8), `c1 : release(a)` `ok` (O3), `c1 : terminate` `ok`, `c0 : join(c1)` `ok`,
`c0 : write3(X)` via `root_X` `ok` (O10.1). -/
theorem W_HO3J_ok : TermStep KF m6 2 (.ok n7) ∧ JoinStep n7 1 2 (.ok n7) ∧
    opStepC KF (.release 1) 1 n7 (.ok n9) ∧ TermStep KF n9 1 (.ok n10) ∧
    JoinStep n10 0 1 (.ok n10) ∧ opStepC KF (.write 0 [0]) 0 n10 (.ok n12) :=
  ⟨⟨by decide, .ok (by decide)⟩, .ok (by decide) (by decide), ⟨by decide, _, .ok (by decide), rfl⟩,
    ⟨by decide, .ok (by decide)⟩, .ok (by decide) (by decide),
    ⟨by decide, _, .ok (by decide), rfl⟩⟩

/-- The labels of W-HO″-J. -/
def ho3jLbls : List Label :=
  [.kernel 0 (.derive 0 [0] .modify), .spawn 0 [1] [], .kernel 1 (.derive 1 [0] .modify),
   .spawn 1 [2] [], .kernel 2 (.write 2 [0]), .kernel 2 (.release 2), .terminate 2, .join 1 2,
   .kernel 1 (.release 1), .terminate 1, .join 0 1, .kernel 0 (.write 0 [0])]

/-- The states of W-HO″-J. -/
def ho3jSts : List (SC × SyncReg × ArenaReg) :=
  [(k0, [], []), (m1, [], []), (m2, [], []), (m3, [], []), (m4, [], []), (m5, [], []),
   (m6, [], []), (n7, [], []), (n7, [], []), (n9, [], []), (n10, [], []), (n10, [], []),
   (n12, [], [])]

/-- The named states of W-HO″-J. -/
def ho3jσ (i : Nat) : SC × SyncReg × ArenaReg := ho3jSts.getD i (n12, [], [])

/-- W-HO″-J from the initial state is a `Run5R`. -/
theorem W_HO3J_run : ho3jσ 0 = (SC.ofS3 (S3.init yst), [], []) ∧
    Run5R KF L0 ho3jσ ho3jLbls := by
  obtain ⟨d1, s1, d2, s2, -⟩ := w_ho3_setup
  obtain ⟨t2', j2, r1, t1', j1, w0⟩ := W_HO3J_ok
  exact ⟨rfl, (Steps5R.consNil (.kernel d1) <| Steps5R.consNil (.spawn s1) <|
    Steps5R.consNil (.kernel d2) <| Steps5R.consNil (.spawn s2) <|
    Steps5R.consNil (.kernel W_HO3_1_ok) <| Steps5R.consNil (.kernel W_HO3_2_ok) <|
    Steps5R.consNil (.terminate t2') <| Steps5R.consNil (.join j2) <|
    Steps5R.consNil (.kernel r1) <| Steps5R.consNil (.terminate t1') <|
    Steps5R.consNil (.join j1) <| Steps5R.consNil (.kernel w0) .nil).run _⟩

/-- `corpus-spec2-m3.md` v8 §2 septies W-HO″-J is an `EncapsulatedTrace5R` from the initial
state. -/
theorem W_HO3J_trace : EncapsulatedTrace5R KF L0 (k0, [], []) ho3jLbls (n12, [], []) :=
  run5R_trace W_HO3J_run.2

/-- `corpus-spec2-m3.md` v8 §2 septies W-HO″-J: the write of `X` by context 2 (step 4) and the
write of `X` by context 0 (step 11) form an exclusive pair. -/
theorem W_HO3J_excl : ExclPair ho3jLbls 4 11 0 :=
  ⟨by decide, by decide, 0, 2, .modify, .modify, by decide, ⟨rfl, by decide, rfl⟩,
    ⟨rfl, by decide, rfl⟩, Or.inl rfl⟩

/-- `corpus-spec2-m3.md` v8 §2 septies W-HO″-J, expected `hb` path: write of context 2 →`po`
`terminate(c2)` →`sw` `join(c2)` by context 1 →`po` `terminate(c1)` →`sw` `join(c1)` by context 0
→`po` write of context 0; the pair is ordered by `hb` and satisfies `HandoffOrdered` (WC5.1
C46). -/
theorem W_HO3J_ordered : PO ho3jσ ho3jLbls (.step 4) (.step 6) ∧
    SW ho3jLbls (.step 6) (.step 7) ∧ PO ho3jσ ho3jLbls (.step 7) (.step 9) ∧
    SW ho3jLbls (.step 9) (.step 10) ∧ PO ho3jσ ho3jLbls (.step 10) (.step 11) ∧
    HB ho3jσ ho3jLbls (.step 4) (.step 11) ∧ HandoffOrderedAt ho3jσ ho3jLbls 4 11 0 := by
  decide

/-! ## The locked trace -/

open Ern.Concurrency.Corpus.GuardedChain (gc0 gc1 gc2 gc3 gc4 gc5 gc6 greg)
open Ern.Concurrency.Corpus.GuardedChainC (lc7 lc8 lc9 lc10 lc11 lcLbls)

/-- The states of the locked trace (`lc_trace`). -/
def lcSts : List (SC × SyncReg × ArenaReg) :=
  [(gc0, [], []), (gc1, [], []), (gc2, [], []), (gc3, [], []), (gc4, [], []), (gc4, greg, []),
   (gc5, greg, []), (gc6, greg, []), (lc7, [⟨4, some 6⟩], []), (lc8, [⟨4, some 6⟩], []),
   (lc9, greg, []), (lc10, [⟨4, some 7⟩], []), (lc11, [⟨4, some 7⟩], [])]

/-- The named states of the locked trace. -/
def lcσ (i : Nat) : SC × SyncReg × ArenaReg := lcSts.getD i (lc11, [⟨4, some 7⟩], [])

/-- The locked trace from the initial state is a `Run5R` (the steps of `lc_trace5R`). -/
theorem lc_run : lcσ 0 = (SC.ofS3 (S3.init Ern.Concurrency.Corpus.GuardedChain.zst), [], []) ∧
    Run5R KM L0 lcσ lcLbls := by
  refine ⟨rfl, Steps5R.run ?_ _⟩
  exact Steps5R.consNil (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    Steps5R.consNil (.kernel ⟨by decide, .ok (by decide)⟩) <|
    Steps5R.consNil (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    Steps5R.consNil (.kernel ⟨by decide, .ok (by decide)⟩) <|
    Steps5R.consNil (.newMutex ⟨by decide, by decide, rfl⟩) <|
    .cons ⟨⟨(by decide : ∀ e ∈ greg, e.Live gc4 → 0 ≠ e.guarded), by decide, trivial⟩, trivial⟩
      (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, trivial⟩ (.spawn ⟨by decide, .ok (by decide)⟩) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, by decide⟩
      (.acquire ⟨by decide, ⟨4, none⟩, rfl, by decide, by decide, rfl⟩) <|
    .cons ⟨⟨trivial, by decide, by decide⟩, trivial⟩
      (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, trivial⟩
      (.unlock ⟨by decide, ⟨4, some 6⟩, 6, rfl, by decide, rfl, by decide, by decide, rfl⟩) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, by decide⟩
      (.acquire ⟨by decide, ⟨4, none⟩, rfl, by decide, by decide, rfl⟩) <|
    .cons ⟨⟨trivial, by decide, by decide⟩, trivial⟩
      (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) .nil

/-- `corpus-spec2-m3.md` v8 §2 septies, mutex: the read of `Y` by context 1 (step 8) and the write
of `Y` by context 0 (step 11) form an exclusive pair. -/
theorem lc_excl : ExclPair lcLbls 8 11 4 :=
  ⟨by decide, by decide, 0, 1, .observe, .modify, by decide, ⟨rfl, by decide, rfl⟩,
    ⟨rfl, by decide, rfl⟩, Or.inr rfl⟩

/-- `corpus-spec2-m3.md` v8 §2 septies, mutex, expected `hb` path: read of context 1 →`po`
`unlock(e)` →`sw` `acquire(e)` of context 0 →`po` write of context 0; the pair is ordered by `hb`
and satisfies `HandoffOrdered` (WC5.1 C46). The `sw` edge is the abstract edge of the mutex, from
`unlock(e)` to the next successful `acquire(e)` (WC5.1 C48, `OB-C05`). -/
theorem lc_ordered : PO lcσ lcLbls (.step 8) (.step 9) ∧ SW lcLbls (.step 9) (.step 10) ∧
    PO lcσ lcLbls (.step 10) (.step 11) ∧ HB lcσ lcLbls (.step 8) (.step 11) ∧
    HandoffOrderedAt lcσ lcLbls 8 11 4 := by
  decide

/-! ## `HandoffOrdered` on the whole trace -/

/-- The mode of an access step is defined (`access_ctx_mode`). -/
theorem accMode_of_access {lbls : List Label} {i c l : Nat} {m : Mode} (h : i < lbls.length)
    (ha : (lbls[i]'h).Access c l m) : (lbls[i]'h).accMode ≠ none := by
  rw [(access_ctx_mode ha).2]; exact fun h' => by cases h'

/-- W-HO-J satisfies `HandoffOrdered` (WC5.1 C46) on all its exclusive pairs: its only accesses are
steps 2 and 6. So the hypothesis `HandoffOrdered` of `handoffOrdered_no_race` holds on a trace with
an exclusive pair. -/
theorem W_HOJ_handoffOrdered : HandoffOrdered hojσ hojLbls := by
  intro i j l ⟨hij, hj, c, c', m, m', hcc, hai, haj, _⟩
  have key : ∀ k (h : k < hojLbls.length), (hojLbls[k]'h).accMode ≠ none → k = 2 ∨ k = 6 := by
    decide
  have hi := key i _ (accMode_of_access _ hai)
  have hj' := key j hj (accMode_of_access hj haj)
  have e1 : i = 2 := by omega
  have e2 : j = 6 := by omega
  subst e1 e2
  obtain ⟨-, hl, -⟩ := hai
  exact W_HOJ_ordered.2.2.2.2 l hl

/-- `handoffOrdered_no_race` applied to W-HO-J (contract `KF`, which satisfies `DDSound`). -/
theorem W_HOJ_noRace : ¬ Race hojσ hojLbls :=
  handoffOrdered_no_race (ddKC []) (by decide : StaticsOK xst) W_HOJ_run.1
    (run5R_imp W_HOJ_run.2) W_HOJ_handoffOrdered

/-- W-HO″-J satisfies `HandoffOrdered` (WC5.1 C46) on all its exclusive pairs: its only accesses
are steps 4 and 11. -/
theorem W_HO3J_handoffOrdered : HandoffOrdered ho3jσ ho3jLbls := by
  intro i j l ⟨hij, hj, c, c', m, m', hcc, hai, haj, _⟩
  have key : ∀ k (h : k < ho3jLbls.length), (ho3jLbls[k]'h).accMode ≠ none →
      k = 4 ∨ k = 11 := by
    decide
  have hi := key i _ (accMode_of_access _ hai)
  have hj' := key j hj (accMode_of_access hj haj)
  have e1 : i = 4 := by omega
  have e2 : j = 11 := by omega
  subst e1 e2
  obtain ⟨-, hl, -⟩ := hai
  rw [List.mem_singleton.1 hl]
  exact W_HO3J_ordered.2.2.2.2.2.2

/-- `handoffOrdered_no_race` applied to W-HO″-J. -/
theorem W_HO3J_noRace : ¬ Race ho3jσ ho3jLbls :=
  handoffOrdered_no_race (ddKC []) (by decide : StaticsOK yst) W_HO3J_run.1
    (run5R_imp W_HO3J_run.2) W_HO3J_handoffOrdered

/-- The locked trace satisfies `HandoffOrdered` (WC5.1 C46) on all its exclusive pairs: its only
accesses are steps 8 and 11. -/
theorem lc_handoffOrdered : HandoffOrdered lcσ lcLbls := by
  intro i j l ⟨hij, hj, c, c', m, m', hcc, hai, haj, _⟩
  have key : ∀ k (h : k < lcLbls.length), (lcLbls[k]'h).accMode ≠ none → k = 8 ∨ k = 11 := by
    decide
  have hi := key i _ (accMode_of_access _ hai)
  have hj' := key j hj (accMode_of_access hj haj)
  have e1 : i = 8 := by omega
  have e2 : j = 11 := by omega
  subst e1 e2
  obtain ⟨-, hl, -⟩ := hai
  rw [List.mem_singleton.1 hl]
  exact lc_ordered.2.2.2.2

/-- `handoffOrdered_no_race` applied to the locked trace (contract `KM`). -/
theorem lc_noRace : ¬ Race lcσ lcLbls :=
  handoffOrdered_no_race (ddKC [2]) Ern.Concurrency.Corpus.GuardedChain.zst_ok lc_run.1
    (run5R_imp lc_run.2) lc_handoffOrdered

end Ern.Concurrency.Corpus.HandoffEvents
