import Ern.Concurrency.Events
import Ern.Concurrency.Corpus.Handoff

/-!
# Handoff witnesses on the event graph

`corpus-spec2-m3.md` v8 §2 septies, on the event graph of `Ern.Concurrency.Events`. Each trace is
given with its named states and is a `Run5R` from the initial state of Spec 1 §47 (no mutex, empty
registries). Facts written from `corpus-spec2-m3.md` v8 §2 septies, decided by `decide`.
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

end Ern.Concurrency.Corpus.HandoffEvents
