import Ern.Concurrency.Corpus.MX

/-!
# Corpus of milestone 3, block AR

`corpus-spec2-m3.md` §0 block AR and §1 S3: an arena whose arena value is administered through a
mutex grant (WC4 C19; Spec 1 §36, §46, §76–§78), shared between contexts 0 and 1. One theorem per
verdict, written from `corpus-spec2-m3.md`; preconditions checked by `decide`.

The arena operations are those of `LStep` (`NewArenaStepC`, `IssueStepC`, `ResetStepC`): the
derived operations of `Ern.MemoryModel.Arena` executed by the context, `store` reading
`ancestorC` (WC4 C2, C3). `S3_8_view_literal` records that `Arena.IssueD` run on the view of the
executing context, which reads the stack order of the view instead of `ancestorC`, rejects step 8.
-/

namespace Ern.Concurrency.Corpus

open Ern.MemoryModel Ern.MemoryModel.Access Ern.Concurrency
open Ern.Concurrency.Traces (L0)

/-- Statics (Spec 1 §47): `0` the mutex value `M2` with fields `1` (`slot2`, `Uninit`) and `2`
(`lock2`, `Init`); `3` the arena value `AV`, a root leaf owned by `M2`, `Init`; `4` the storage
`ST`, a root owned by frame 0 with the leaves `5` (`R1`) and `6` (`R2`); `7` the leaf `d0`, a root
owned by frame 0. Root authorities: `0` of `M2`, `1` of `AV` (held by `M2`), `2` of `ST`, `3` of
`d0`. -/
def arst : Statics :=
  [((none, none, 0), false), ((some 0, none, 0), false), ((some 0, none, 0), true),
   ((none, some 0, 0), true), ((none, none, 0), false), ((some 4, none, 0), false),
   ((some 4, none, 0), false), ((none, none, 0), false)]

/-- The statics are well formed (Spec 1 §47). -/
theorem arst_ok : StaticsOK arst := by decide

/-- The contract of block AR: `lock2` (place 2) is the only `SharedMutable` leaf. -/
abbrev KA : K := KC [2]

/-- Initial state of block AR. -/
def a0 : SC := SC.ofS3 (S3.init arst)
/-- AR step 1: `internal := derive(root_ST, Modify, footprint(ST))`, authority 4. -/
def a1 : SC := a0.set (deriveEff (a0.view 0) 2 [5, 6] .modify)
/-- AR step 1: `store(internal, AV)`. -/
def a2 : SC := storeEffC a1 0 4 3
/-- AR step 1: the arena registry after `newArena(ST, internal)` (O17): the arena value is `AV`. -/
def arA : ArenaReg := [⟨4, 4, [5, 6], []⟩]
/-- AR step 2: `guarded2 := derive(root_AV, Modify, {AV})`, authority 5. -/
def a3 : SC := a2.set (deriveEff (a2.view 0) 1 [3] .modify)
/-- AR step 2: `store(guarded2, slot2)`. -/
def a4 : SC := storeEffC a3 0 5 1
/-- AR step 2: the synchronization registry after `newMutex(guarded2)`, entry `e2` (WC4 C13). -/
def regA : SyncReg := [⟨5, none⟩]
/-- AR step 3: `o1 := derive(root_M2, Observe, {slot2, lock2})`, authority 6. -/
def a5 : SC := a4.set (deriveEff (a4.view 0) 0 [1, 2] .observe)
/-- AR step 3: `spawn c1` yielding `o1`, with the local leaf `d1` (place 8, root authority 7):
context 1, initial frame 1. -/
def a6 : SC := spawnEff a5 0 [6] [(none, 0)]

/-- The construction of block AR (`corpus-spec2-m3.md` §0): an `EncapsulatedTrace` from the
initial state (WC4 C22, C23); `ControlOf(e2) = lock2`, the arena value is `AV`, and
`{AV} ∩ {slot2, lock2} = ∅` (WC4 C13.4). -/
theorem ar_trace : EncapsulatedTrace KA L0 (a0, [], [])
    [.kernel 0 (.derive 2 [5, 6] .modify), .kernel 0 (.store 4 3), .newArena 0 4 4,
     .kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 5 1), .newMutex 0 5,
     .kernel 0 (.derive 0 [1, 2] .observe), .spawn 0 [6] [(none, 0)]] (a6, regA, arA) ∧
    ControlOf L0 a4 ⟨5, none⟩ = some 2 ∧ Arena.arenaValue a2.flat ⟨4, 4, [5, 6], []⟩ = some 3 := by
  refine ⟨?_, by decide, by decide⟩
  have hn : NewMutexOk KA L0 arA a4 [] 0 5 (a4, regA) := ⟨by decide, by decide, rfl⟩
  have ha : NewArenaStepC a2 [] [] 0 4 4 (.ok (a2, arA)) := ⟨by decide, .ok (by decide)⟩
  exact .cons (fun e he => by cases he) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons trivial (.kernel ⟨by decide, .ok (by decide)⟩) <|
    .cons trivial (.newArena ha) <|
    .cons (fun e he => by cases he) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons trivial (.kernel ⟨by decide, .ok (by decide)⟩) <|
    .cons trivial (.newMutex hn) <|
    .cons (by decide : ∀ e ∈ regA, e.Live a4 → 0 ≠ e.guarded)
      (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons trivial (.spawn ⟨by decide, .ok (by decide)⟩) .nil

/-! ## S3 (`corpus-spec2-m3.md` §1 S3) -/

/-- `corpus-spec2-m3.md` §1 S3, step 1, `reject` (Spec 1 §77.1, `MetaRight`: context 1 has no
exercisable `Modify` over `AV`, only `Observe` over `M2`): `issue(arena, R1, d1)` by context 1
without grant, rejected by a static check. -/
theorem S3_1_reject : IssueStepC KA a6 arA 1 0 [5] 8 .reject ∧
    ¬ Arena.MetaRight (a6.view 1) ⟨4, 4, [5, 6], []⟩ :=
  ⟨.static (by decide) rfl (by decide), by decide⟩

/-- `c1 : acquire(e2)`: `g2`, authority 8, held by frame 1 (WC4 C16). -/
def a7 : SC := deriveSyncEff a6 1 5
/-- The registry with `g2` recorded. -/
def regA8 : SyncReg := [⟨5, some 8⟩]

/-- `corpus-spec2-m3.md` §1 S3, step 2, `ok` (WC4 C16): `acquire(e2)` by context 1. -/
theorem S3_2_ok : AcquireOk KA L0 a6 regA 1 0 (a7, regA8) :=
  ⟨by decide, ⟨5, none⟩, rfl, by decide, by decide, rfl⟩

/-- `split(internal, [R1])` by context 1: the block, authority 9, held by frame 1 (O2). -/
def a8s : SC := a7.set (splitEff (a7.view 1) 4 [[5]])
/-- `store(block, d1)` by context 1 (O8). -/
def a8 : SC := storeEffC a8s 1 a7.A.length 8
/-- The arena registry after the issue of `R1` (Spec 1 §77 effect). -/
def arA1 : ArenaReg := arA.set 0 (Arena.issueMeta a7.flat ⟨4, 4, [5, 6], []⟩ [5])

/-- The block of `R1` is authority 9; `R2` is still available (Spec 1 §77 effect). -/
theorem arA1_eq : a7.A.length = 9 ∧ arA1 = [⟨4, 4, [6], [([5], 9)]⟩] := by decide

/-- `corpus-spec2-m3.md` §1 S3, step 3, `ok` (Spec 1 §43 clause 2: `g2` gives `Modify` over `{AV}`,
so `ExercisableAt(internal, Modify)`; §77.3, §77.6: `d1` is a local leaf of context 1 and the
effective anchor `root_ST` is in frame 0, an ancestor): `issue(arena, R1, d1)` by context 1. -/
theorem S3_3_ok : IssueStepC KA a7 arA 1 0 [5] 8 (.ok (a8, arA1)) :=
  .ok (E := ⟨4, 4, [5, 6], []⟩) rfl (by decide) (by decide) ⟨by decide, _, .ok (by decide), rfl⟩
    ⟨by decide, .ok (by decide)⟩

/-- `corpus-spec2-m3.md` §1 S3, step 4, `non habilité` (WC4 C14.2): `acquire(e2)` by context 0
while `g2` is recorded. -/
theorem S3_4_wait : ∀ st', ¬ AcquireOk KA L0 a8 regA8 0 0 st' := by
  rintro st' ⟨-, e, he, ⟨-, hg, -⟩, -⟩
  cases he; cases hg

/-- `corpus-spec2-m3.md` §1 S3, extra negative, `reject` (Spec 1 §78.2: an active block derived
from `internal` covers `R1`): `reset(arena)` by context 1 under `g2`. In the derived operation the
`derive` of `internal` over the storage is rejected (§60.2: the effective mode of `internal` on
`R1` is absent, §43.3). -/
theorem S3_3b_reject : ResetStepC a8 arA1 1 0 .reject ∧
    ¬ DerivePre (a8.view 1) 4 [5, 6] .modify :=
  ⟨⟨by decide, _, .derive rfl (.reject (by decide)), rfl⟩, by decide⟩

/-- `c1 : unlock(e2)` (WC4 C17). -/
def a9 : SC := a8.set (releaseEff (a8.view 1) 8)

/-- `corpus-spec2-m3.md` §1 S3, step 5, `ok` (WC4 C17): `unlock(e2)` by context 1. -/
theorem S3_5_ok : UnlockOk L0 a8 regA8 1 0 (a9, regA) :=
  ⟨by decide, ⟨5, some 8⟩, 8, rfl, by decide, rfl, by decide, by decide, rfl⟩

/-- `c0 : acquire(e2)`: `g2′`, authority 10, held by frame 0 (WC4 C16). -/
def a10 : SC := deriveSyncEff a9 0 5
/-- The registry with `g2′` recorded. -/
def regA10 : SyncReg := [⟨5, some 10⟩]

/-- `corpus-spec2-m3.md` §1 S3, step 6, `ok` (WC4 C16): `acquire(e2)` by context 0. -/
theorem S3_6_ok : AcquireOk KA L0 a9 regA 0 0 (a10, regA10) :=
  ⟨by decide, ⟨5, none⟩, rfl, by decide, by decide, rfl⟩

/-- `corpus-spec2-m3.md` §1 S3, step 7, **`fail`** (Spec 1 §77.4: `R1` is unavailable; the state is
unchanged, no block is duplicated): `issue(arena, R1, d0)` by context 0, the static checks
holding. -/
theorem S3_7_fail : IssueStepC KA a10 arA1 0 0 [5] 7 .fail ∧
    Arena.IssueStatic (a10.view 0) ⟨4, 4, [6], [([5], 9)]⟩ [5] 7 ∧
    ∀ st', ¬ IssueStepC KA a10 arA1 0 0 [5] 7 (.ok st') := by
  have hE : arA1[0]? = some ⟨4, 4, [6], [([5], 9)]⟩ := by decide
  refine ⟨.fail (by decide) hE (by decide) (by decide), by decide, fun st' h => ?_⟩
  obtain ⟨E, s₁, hE', -, hav, -⟩ := issueStepC_ok h
  rw [hE] at hE'; cases hE'
  exact (by decide : ¬ Arena.Avail ⟨4, 4, [6], [([5], 9)]⟩ [5]) hav

/-- `split(internal, [R2])` by context 0: the block, authority 11, held by frame 0 (O2). -/
def a11s : SC := a10.set (splitEff (a10.view 0) 4 [[6]])
/-- `store(block, d0)` by context 0 (O8). -/
def a11 : SC := storeEffC a11s 0 a10.A.length 7
/-- The arena registry after the issue of `R2`. -/
def arA2 : ArenaReg := arA1.set 0 (Arena.issueMeta a10.flat ⟨4, 4, [6], [([5], 9)]⟩ [6])

/-- The block of `R2` is authority 11; nothing is available any more (Spec 1 §77 effect). -/
theorem arA2_eq : a10.A.length = 11 ∧ arA2 = [⟨4, 4, [], [([6], 11), ([5], 9)]⟩] := by decide

/-- `corpus-spec2-m3.md` §1 S3, step 8, `ok`: `issue(arena, R2, d0)` by context 0, while the block
of `R1`, anchored in frame 0, is held by `d1`, a local of context 1. -/
theorem S3_8_ok : IssueStepC KA a10 arA1 0 0 [6] 7 (.ok (a11, arA2)) :=
  .ok (E := ⟨4, 4, [6], [([5], 9)]⟩) (by decide) (by decide) (by decide)
    ⟨by decide, _, .ok (by decide), rfl⟩ ⟨by decide, .ok (by decide)⟩

/-- Step 8 with `Arena.IssueD` run on the view of context 0 (Spec 1 §77 with the sequential
`ancestor` of §39 on the stack of the view): the `store` of the block is rejected, because
`AnchorOrderHeld` (§65.5) reads the order of the view's stack, in which frame 0 is not an
ancestor of frame 1 holding `d1`; with `ancestorC` (WC4 C3) step 8 is `ok` (`S3_8_ok`). -/
theorem S3_8_view_literal : Arena.IssueD KA 0 [6] 7 ⟨a10.view 0, arA1⟩ .reject ∧
    ¬ AnchorOrderHeld (storeEff (splitEff (a10.view 0) 4 [[6]]) (a10.view 0).A.length 7) ∧
    AnchorOrderHeldC (storeEffC a11s 0 a10.A.length 7) :=
  ⟨.store (E := ⟨4, 4, [6], [([5], 9)]⟩) (by decide) (by decide) (by decide) (.ok (by decide))
    (.reject (by decide)), by decide, by decide⟩

/-- The construction of S3 continues the encapsulated trace of block AR (WC4 C22, C23). -/
theorem s3_trace : EncapsulatedTrace KA L0 (a0, [], [])
    [.kernel 0 (.derive 2 [5, 6] .modify), .kernel 0 (.store 4 3), .newArena 0 4 4,
     .kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 5 1), .newMutex 0 5,
     .kernel 0 (.derive 0 [1, 2] .observe), .spawn 0 [6] [(none, 0)], .acquire 1 0,
     .issue 1 0 [5] 8, .unlock 1 0, .acquire 0 0, .issue 0 0 [6] 7] (a11, regA10, arA2) := by
  have h := ar_trace.1.snoc (lbl := .acquire 1 0) (st' := (a7, regA8, arA)) trivial
    (.acquire S3_2_ok)
  have h := h.snoc (lbl := .issue 1 0 [5] 8) (st' := (a8, regA8, arA1)) trivial (.issue S3_3_ok)
  have h := h.snoc (lbl := .unlock 1 0) (st' := (a9, regA, arA1)) trivial (.unlock S3_5_ok)
  have h := h.snoc (lbl := .acquire 0 0) (st' := (a10, regA10, arA1)) trivial (.acquire S3_6_ok)
  exact h.snoc (lbl := .issue 0 0 [6] 7) (st' := (a11, regA10, arA2)) trivial (.issue S3_8_ok)

end Ern.Concurrency.Corpus
