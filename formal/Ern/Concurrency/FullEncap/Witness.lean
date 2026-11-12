import Ern.Concurrency.FullEncap.Inventory
import Ern.Concurrency.MutexReal.ClassifyWitness
import Ern.Concurrency.Corpus.MutexEdge

/-!
# Witnesses W-GI and W-RX of the complete encapsulation

`corpus-spec2-m3.md` v13 §2 duodecies. One theorem per expected fact, preconditions by `decide`;
the verdicts are written from the corpus.

* W-GI: an `issue` into the protected data without the lock (Spec 1 §77.2, §77.6), whose
  destination right rests only on a live `guarded`. Contract `KM`, layout `L0`.
* W-RX: the `resetLock` exception of WC5.2 C22 item 6 with a third-party `guarded`: two nested
  mutexes, the inner one inside the protected data of the outer one. Contract `KC [2, 6]`.
-/

set_option autoImplicit false

namespace Ern.Concurrency.FullEncap.Witness

open Ern.MemoryModel Ern.MemoryModel.Access Ern.Concurrency Ern.Concurrency.MutexReal
open Ern.Concurrency.Corpus
open Ern.Concurrency.Traces (L0)

/-! ## Decision of the existing encapsulation -/

/-- Decidability of `Encap` (WC5.2 C22 items 1–3 and 5). -/
instance instDecidableEncap (L : MutexLayout) (st : SC × SyncReg) (lbl : Label) :
    Decidable (Encap L st lbl) := by
  unfold Encap; split <;> infer_instance

/-- Decidability of `Encap5C`. -/
instance instDecidableEncap5C (L : MutexLayout) (st : SC × SyncReg) (lbl : Label) :
    Decidable (Encap5C L st lbl) := by
  unfold Encap5C; infer_instance

/-- Decidability of `Encap5R`. -/
instance instDecidableEncap5R (k : K) [DecidablePred k.SharedMutable] (L : MutexLayout)
    (st : SC × SyncReg × ArenaReg) (lbl : Label) : Decidable (Encap5R k L st lbl) := by
  unfold Encap5R; infer_instance

/-! ## W-GI -/

/-- Statics of W-GI (Spec 1 §47): block MX without `M′` (`0` the mutex value `M` with fields `1`
(`slot`, `Uninit`) and `2` (`lock`, `Init`); `3` the protected root `T`, a leaf `t`, `Init`, owned
by `M`), and a free arena of the base frame as in block AR (`4` the storage `ST0` with the leaves
`5` (`R1`) and `6` (`R2`); `7` the arena value `AV0`, a root leaf, `Init`). Root authorities: `0` of
`M` (frame 0), `1` of `T` (held by `M`), `2` of `ST0` (frame 0), `3` of `AV0` (frame 0). -/
def gist : Statics :=
  [((none, none, 0), false), ((some 0, none, 0), false), ((some 0, none, 0), true),
   ((none, some 0, 0), true), ((none, none, 0), false), ((some 4, none, 0), false),
   ((some 4, none, 0), false), ((none, none, 0), true)]

/-- The statics are well formed (Spec 1 §47). -/
theorem gist_ok : StaticsOK gist := by decide

/-- Initial state of W-GI. -/
def gi0 : SC := SC.ofS3 (S3.init gist)
/-- `internal0 := derive(root_ST0, Modify, footprint(ST0))`, authority 4 (O1). -/
def gi1 : SC := gi0.set (deriveEff (gi0.view 0) 2 [5, 6] .modify)
/-- `store(internal0, AV0)` (O8). -/
def gi2 : SC := storeEffC gi1 0 4 7
/-- The arena registry after `newArena(ST0, internal0)` (Spec 1 §76). -/
def giAr : ArenaReg := [⟨4, 4, [5, 6], []⟩]
/-- `guarded := derive(root_T, Modify, footprint(T))`, authority 5 (O1). -/
def gi3 : SC := gi2.set (deriveEff (gi2.view 0) 1 [3] .modify)
/-- `store(guarded, slot)` (O8). -/
def gi4 : SC := storeEffC gi3 0 5 1
/-- The registry after `newMutex(guarded)` (WC5.2 C13): entry `e`. -/
def giReg : SyncReg := [⟨5, none⟩]
/-- `o := derive(root_M, Observe, {lock})`, authority 6 (O1). -/
def gi5 : SC := gi4.set (deriveEff (gi4.view 0) 0 [2] .observe)
/-- `spawn c1` yielding `o` (WC5.2 C4): context 1, initial frame 1. -/
def gi6 : SC := spawnEff gi5 0 [6] []
/-- Step 1, internal `split(internal0, [R1])` of `issue` by context 0: the block, authority 7,
held by frame 0 (Spec 1 §77, Part XIV). -/
def gi7s : SC := gi6.set (splitEff (gi6.view 0) 4 [[5]])
/-- Step 1, internal `store(block, t)` of `issue` by context 0 (O8). -/
def gi7 : SC := storeEffC gi7s 0 gi6.A.length 3
/-- The arena registry after step 1 (Spec 1 §77 effect). -/
def giAr1 : ArenaReg := giAr.set 0 (Arena.issueMeta gi6.flat ⟨4, 4, [5, 6], []⟩ [5])
/-- Step 2, `c1 : acquire(e)`: `g₁`, authority 8, held by frame 1 (WC5.2 C16). -/
def gi8 : SC := deriveSyncEff gi7 1 5
/-- The registry with `g₁` recorded. -/
def giRegG : SyncReg := [⟨5, some 8⟩]
/-- Step 3, `c1 : read3(t)` via `g₁` (O9): the state is unchanged. -/
def gi9 : SC := gi8.set (gi8.view 1)

/-- The labels of the setup of W-GI. -/
def giSetup : List Label :=
  [.kernel 0 (.derive 2 [5, 6] .modify), .kernel 0 (.store 4 7), .newArena 0 4 4,
   .kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 5 1), .newMutex 0 5,
   .kernel 0 (.derive 0 [2] .observe), .spawn 0 [6] []]

/-- The labels of W-GI: the setup, then steps 1 to 3. -/
def giLbls : List Label :=
  giSetup ++ [.issue 0 0 [5] 3, .acquire 1 0, .kernel 1 (.read 8 [3])]

/-- The named states of W-GI. -/
def giσ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(gi0, [], []), (gi1, [], []), (gi2, [], []), (gi2, [], giAr), (gi3, [], giAr),
    (gi4, [], giAr), (gi4, giReg, giAr), (gi5, giReg, giAr), (gi6, giReg, giAr),
    (gi7, giReg, giAr1), (gi8, giRegG, giAr1), (gi9, giRegG, giAr1)].getD i (gi9, giRegG, giAr1)

/-- The block of `R1` is authority 7 (Spec 1 §77 effect). -/
theorem gi_block : gi6.A.length = 7 := by decide

/-- `corpus-spec2-m3.md` v13 §2 duodecies W-GI, step 1, `ok` (Spec 1 §77.1: `MetaRight` over
`AV0`, a local of `f0`; §77.2, §77.6: `Modify` over `t` through `guarded`, active, held by `slot`,
on whose leaves `root_M` is exercisable in `Modify` with effective `Modify`, third clause of §43):
`issue(arena0, R1, t)` by context 0 without the grant. -/
theorem W_GI_1_ok : IssueStepC KM gi6 giAr 0 0 [5] 3 (.ok (gi7, giAr1)) :=
  .ok (E := ⟨4, 4, [5, 6], []⟩) rfl (by decide) (by decide) ⟨by decide, _, .ok (by decide), rfl⟩
    ⟨by decide, .ok (by decide)⟩

/-- `corpus-spec2-m3.md` v13 §2 duodecies W-GI, step 2, `ok` (WC5.2 C14 items 1–3 through `o`,
C15): `acquire(e)` by context 1. -/
theorem W_GI_2_ok : AcquireOk KM L0 gi7 giReg 1 0 (gi8, giRegG) :=
  ⟨by decide, ⟨5, none⟩, rfl, by decide, by decide, rfl⟩

/-- `corpus-spec2-m3.md` v13 §2 duodecies W-GI, step 3, `ok` (O9): `read3(t)` via `g₁` by
context 1. -/
theorem W_GI_3_ok : opStepC KM (.read 8 [3]) 1 gi8 (.ok gi9) :=
  ⟨by decide, _, .ok (by decide), rfl⟩

/-- The setup and steps 1 to 3 of W-GI from the initial state, each step admitted by `Encap5R`. -/
theorem gi_steps : Steps5R KM L0
    [(gi0, [], []), (gi1, [], []), (gi2, [], []), (gi2, [], giAr), (gi3, [], giAr),
      (gi4, [], giAr), (gi4, giReg, giAr), (gi5, giReg, giAr), (gi6, giReg, giAr),
      (gi7, giReg, giAr1), (gi8, giRegG, giAr1), (gi9, giRegG, giAr1)] giLbls :=
  .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
  .cons (by decide) (.kernel ⟨by decide, .ok (by decide)⟩) <|
  .cons (by decide) (.newArena ⟨by decide, .ok (by decide)⟩) <|
  .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
  .cons (by decide) (.kernel ⟨by decide, .ok (by decide)⟩) <|
  .cons (by decide) (.newMutex ⟨by decide, by decide, rfl⟩) <|
  .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
  .cons (by decide) (.spawn ⟨by decide, .ok (by decide)⟩) <|
  .cons (by decide) (.issue W_GI_1_ok) <|
  .cons (by decide) (.acquire W_GI_2_ok) <|
  .cons (by decide) (.kernel W_GI_3_ok) .nil

/-- `corpus-spec2-m3.md` v13 §2 duodecies W-GI, "sous l'encapsulation actuelle": steps 1 to 3 are
`ok` and, from the initial state, the trace is a final amended execution; step 1 is admitted (the
destination right of `issue` is not read by `Encap7`). -/
theorem W_GI_current : giσ 0 = (SC.ofS3 (S3.init gist), [], []) ∧ RunAmF KM L0 giσ giLbls :=
  ⟨rfl, run7_of_run5R (gi_steps.run _) (by decide), by decide⟩

/-- `corpus-spec2-m3.md` v13 §2 duodecies W-GI, "sous l'encapsulation complète": step 1 is
excluded. `MetaRight` over `AV0` and the exercise of `internal0` hold without a live `guarded`;
the destination right (Spec 1 §77.2), the target right of the internal `store` (§65.2) and its
resulting-state right (§65.5) hold only through `guarded`. The trace is no `RunFull`. -/
theorem W_GI_1_excluded :
    MetaRightG (gi6, giReg) 0 ⟨4, 4, [5, 6], []⟩ ∧ Exer5 gi6 giReg 0 4 .modify ∧
    HasRight (gi6.view 0) .modify 3 ∧ ¬ HasRight5 (gi6, giReg) 0 .modify 3 ∧
    ¬ HasRight5 (gi7s, giReg) 0 .modify 3 ∧ ¬ HasRight5 (gi7, giReg) 0 .modify 3 ∧
    ¬ PremG KM L0 (giσ 8) (.issue 0 0 [5] 3) ∧ ¬ RunFull KM L0 giσ giLbls := by
  have h : ¬ PremG KM L0 (giσ 8) (.issue 0 0 [5] 3) := by decide
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, h,
    fun hr => h (hr 8 (by decide)).1.2⟩

/-! ### Twin of W-GI -/

/-- Twin, `c0 : acquire(e)`: `g₀`, authority 7, held by frame 0 (WC5.2 C16). -/
def gt7 : SC := deriveSyncEff gi6 0 5
/-- The registry with `g₀` recorded. -/
def gtReg : SyncReg := [⟨5, some 7⟩]
/-- Twin, internal `split(internal0, [R1])` of `issue` by context 0: the block, authority 8. -/
def gt8s : SC := gt7.set (splitEff (gt7.view 0) 4 [[5]])
/-- Twin, internal `store(block, t)` of `issue` by context 0, under `g₀` (O8). -/
def gt8 : SC := storeEffC gt8s 0 gt7.A.length 3
/-- The arena registry after the twin `issue`. -/
def gtAr1 : ArenaReg := giAr.set 0 (Arena.issueMeta gt7.flat ⟨4, 4, [5, 6], []⟩ [5])
/-- Twin, `c0 : unlock(e)` (WC5.2 C17). -/
def gt9 : SC := gt8.set (releaseEff (gt8.view 0) 7)

/-- The labels of the twin of W-GI. -/
def gtLbls : List Label := giSetup ++ [.acquire 0 0, .issue 0 0 [5] 3, .unlock 0 0]

/-- The named states of the twin of W-GI. -/
def gtσ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(gi0, [], []), (gi1, [], []), (gi2, [], []), (gi2, [], giAr), (gi3, [], giAr),
    (gi4, [], giAr), (gi4, giReg, giAr), (gi5, giReg, giAr), (gi6, giReg, giAr),
    (gt7, gtReg, giAr), (gt8, gtReg, gtAr1), (gt9, giReg, gtAr1)].getD i (gt9, giReg, gtAr1)

/-- `corpus-spec2-m3.md` v13 §2 duodecies W-GI, twin: `c0 : acquire(e)`, `c0 : issue(arena0, R1,
t)`, `c0 : unlock(e)` are `ok` and admitted: from the initial state, the trace is a `RunFull`; the
right over `t` rests on the grant of `c0` (WC5.2 C22 item 6: a legitimate acquired grant). -/
theorem W_GI_twin : gtσ 0 = (SC.ofS3 (S3.init gist), [], []) ∧ RunFull KM L0 gtσ gtLbls := by
  have hs : Steps5R KM L0
      [(gi0, [], []), (gi1, [], []), (gi2, [], []), (gi2, [], giAr), (gi3, [], giAr),
        (gi4, [], giAr), (gi4, giReg, giAr), (gi5, giReg, giAr), (gi6, giReg, giAr),
        (gt7, gtReg, giAr), (gt8, gtReg, gtAr1), (gt9, giReg, gtAr1)] gtLbls :=
    .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons (by decide) (.kernel ⟨by decide, .ok (by decide)⟩) <|
    .cons (by decide) (.newArena ⟨by decide, .ok (by decide)⟩) <|
    .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons (by decide) (.kernel ⟨by decide, .ok (by decide)⟩) <|
    .cons (by decide) (.newMutex ⟨by decide, by decide, rfl⟩) <|
    .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons (by decide) (.spawn ⟨by decide, .ok (by decide)⟩) <|
    .cons (by decide) (.acquire ⟨by decide, ⟨5, none⟩, rfl, by decide, by decide, rfl⟩) <|
    .cons (by decide) (.issue (.ok (E := ⟨4, 4, [5, 6], []⟩) rfl (by decide) (by decide)
      ⟨by decide, _, .ok (by decide), rfl⟩ ⟨by decide, .ok (by decide)⟩)) <|
    .cons (by decide)
      (.unlock ⟨by decide, ⟨5, some 7⟩, 7, rfl, by decide, rfl, by decide, by decide, rfl⟩) .nil
  exact ⟨rfl, runFull_of_run7 (run7_of_run5R (hs.run _) (by decide)) (by decide)⟩

/-! ## W-RX -/

/-- Statics of W-RX (Spec 1 §47): `0` the outer mutex value `M` with fields `1` (`slot`, `Uninit`)
and `2` (`lock`, `Init`); `3` its protected root `T`, owned by `M`, whose part `4` is the inner
mutex value `N` with fields `5` (`slot_n`, `Uninit`) and `6` (`lock_n`, `Init`); `7` the protected
root `U` of `N`, a leaf, `Init`, owned by `N`. Root authorities: `0` of `M` (frame 0), `1` of `T`
(held by `M`), `2` of `U` (held by `N`). -/
def rxst : Statics :=
  [((none, none, 0), false), ((some 0, none, 0), false), ((some 0, none, 0), true),
   ((none, some 0, 0), false), ((some 3, some 0, 0), false), ((some 4, some 0, 0), false),
   ((some 4, some 0, 0), true), ((none, some 4, 0), true)]

/-- The statics are well formed (Spec 1 §47). -/
theorem rxst_ok : StaticsOK rxst := by decide

/-- The contract of W-RX: the two controllers `lock` (place 2) and `lock_n` (place 6) are the
`SharedMutable` leaves (WC5.2 C13 item 6). -/
abbrev KX : K := Corpus.KC [2, 6]

/-- Initial state of W-RX. -/
def rx0 : SC := SC.ofS3 (S3.init rxst)
/-- `guarded_n := derive(root_U, Modify, footprint(U))`, authority 3 (O1). -/
def rx1 : SC := rx0.set (deriveEff (rx0.view 0) 2 [7] .modify)
/-- `store(guarded_n, slot_n)` (O8). -/
def rx2 : SC := storeEffC rx1 0 3 5
/-- The registry after `newMutex(guarded_n)` (WC5.2 C13): entry `e_n`, index 0. -/
def rxReg1 : SyncReg := [⟨3, none⟩]
/-- `guarded := derive(root_T, Modify, footprint(T))`, authority 4 (O1). -/
def rx3 : SC := rx2.set (deriveEff (rx2.view 0) 1 [5, 6] .modify)
/-- `store(guarded, slot)` (O8). -/
def rx4 : SC := storeEffC rx3 0 4 1
/-- The registry after `newMutex(guarded)` (WC5.2 C13): entry `e`, index 1. -/
def rxReg : SyncReg := [⟨3, none⟩, ⟨4, none⟩]
/-- Step B, `c0 : acquire(e)`: `g`, authority 5, held by frame 0 (WC5.2 C16). -/
def rx5 : SC := deriveSyncEff rx4 0 4
/-- The registry with `g` recorded for `e`. -/
def rxRegG : SyncReg := [⟨3, none⟩, ⟨4, some 5⟩]

/-- The labels of the setup of W-RX: the inner mutex first, then the outer one; no grant. -/
def rxSetup : List Label :=
  [.kernel 0 (.derive 2 [7] .modify), .kernel 0 (.store 3 5), .newMutex 0 3,
   .kernel 0 (.derive 1 [5, 6] .modify), .kernel 0 (.store 4 1), .newMutex 0 4]

/-- The setup of W-RX from the initial state, each step admitted by `Encap5R`. -/
theorem rx_setup {sts : List (SC × SyncReg × ArenaReg)} {lbls : List Label}
    (h : Steps5R KX L0 ((rx4, rxReg, []) :: sts) lbls) :
    Steps5R KX L0 ((rx0, [], []) :: (rx1, [], []) :: (rx2, [], []) :: (rx2, rxReg1, []) ::
      (rx3, rxReg1, []) :: (rx4, rxReg1, []) :: (rx4, rxReg, []) :: sts) (rxSetup ++ lbls) :=
  .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
  .cons (by decide) (.kernel ⟨by decide, .ok (by decide)⟩) <|
  .cons (by decide) (.newMutex ⟨by decide, by decide, rfl⟩) <|
  .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
  .cons (by decide) (.kernel ⟨by decide, .ok (by decide)⟩) <|
  .cons (by decide) (.newMutex ⟨by decide, by decide, rfl⟩) h

/-- The labels of W-RX, step A. -/
def rxaLbls : List Label := rxSetup ++ [.resetLock 0 0]

/-- The named states of W-RX, step A. -/
def rxaσ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(rx0, [], []), (rx1, [], []), (rx2, [], []), (rx2, rxReg1, []), (rx3, rxReg1, []),
    (rx4, rxReg1, []), (rx4, rxReg, []), (rx4, rxReg, [])].getD i (rx4, rxReg, [])

/-- `corpus-spec2-m3.md` v13 §2 duodecies W-RX: the nested setup is accepted by the kernel; both
entries are live and `ControlOf(e_n) = lock_n`, `ControlOf(e) = lock` (WC5.2 C13). -/
theorem W_RX_setup : rxaσ 0 = (SC.ofS3 (S3.init rxst), [], []) ∧
    ControlOf L0 rx4 ⟨3, none⟩ = some 6 ∧ ControlOf L0 rx4 ⟨4, none⟩ = some 2 ∧
    (⟨3, none⟩ : SyncEntry).Live rx4 ∧ (⟨4, none⟩ : SyncEntry).Live rx4 := by
  exact ⟨rfl, by decide, by decide, by decide, by decide⟩

/-- `corpus-spec2-m3.md` v13 §2 duodecies W-RX, step A, `ok` (WC5.2 C18 item 1:
`ExercisableAt(guarded_n, Modify)`, `guarded_n` being held by `slot_n`, a leaf of `T`, on which
`guarded` has effective `Modify`, `guarded` being held by `slot` under `root_M`, third clause of
Spec 1 §43 twice; C18 items 2 and 3; C18 item 4 through the same chain):
`resetLock(e_n)` by context 0 without the grant of `e`. -/
theorem W_RX_A_ok : ResetLockOk L0 rx4 rxReg 0 0 (rx4, rxReg) ∧
    AmCondF L0 (rx4, rxReg, []) (.resetLock 0 0) :=
  ⟨⟨by decide, ⟨3, none⟩, rfl, by decide, by decide, by decide, rfl⟩, by decide⟩

/-- `corpus-spec2-m3.md` v13 §2 duodecies W-RX, step A, under the existing encapsulation: from the
initial state, the trace is a final amended execution (nothing in `Encap7` reads the right of
C18 item 1). -/
theorem W_RX_A_current : RunAmF KX L0 rxaσ rxaLbls := by
  have h : Steps5R KX L0 [(rx4, rxReg, []), (rx4, rxReg, [])] [.resetLock 0 0] :=
    .cons (by decide) (.resetLock W_RX_A_ok.1) .nil
  exact ⟨run7_of_run5R ((rx_setup h).run _) (by decide), by decide⟩

/-- `corpus-spec2-m3.md` v13 §2 duodecies W-RX, step A, excluded by the complete encapsulation:
the chain of the right on `slot_n` contains `guarded`, the `guarded` of the other live entry `e`
(WC5.2 C22 item 6, `resetLock` exception); so does the controller-access right of C18 item 4.
Both guard-free forms fail; the trace is no `RunFull`. -/
theorem W_RX_A_excluded :
    ¬ ResetExerG (rx4, rxReg) 0 0 ∧ ¬ CtrlRight5 L0 (rx4, rxReg) ⟨3, none⟩ 0 ∧
    ¬ PremG KX L0 (rx4, rxReg, []) (.resetLock 0 0) ∧ ¬ RunFull KX L0 rxaσ rxaLbls := by
  have h : ¬ PremG KX L0 (rx4, rxReg, []) (.resetLock 0 0) := by decide
  exact ⟨by decide, by decide, h, fun hr => h (hr 6 (by decide)).1.2⟩

/-- The labels of W-RX, twin B. -/
def rxbLbls : List Label := rxSetup ++ [.acquire 0 1, .resetLock 0 0]

/-- The named states of W-RX, twin B. -/
def rxbσ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(rx0, [], []), (rx1, [], []), (rx2, [], []), (rx2, rxReg1, []), (rx3, rxReg1, []),
    (rx4, rxReg1, []), (rx4, rxReg, []), (rx5, rxRegG, []), (rx5, rxRegG, [])].getD i
    (rx5, rxRegG, [])

/-- `corpus-spec2-m3.md` v13 §2 duodecies W-RX, twin B, `ok` and admitted: `c0 : acquire(e)`,
then `c0 : resetLock(e_n)`; the rights on `slot_n` and `lock_n` rest on `g`, held by `f0`; only
`guarded_n`, the subject of the check, is exempt. From the initial state, the trace is a
`RunFull`. -/
theorem W_RX_B : rxbσ 0 = (SC.ofS3 (S3.init rxst), [], []) ∧ RunFull KX L0 rxbσ rxbLbls := by
  have h : Steps5R KX L0 [(rx4, rxReg, []), (rx5, rxRegG, []), (rx5, rxRegG, [])]
      [.acquire 0 1, .resetLock 0 0] :=
    .cons (by decide) (.acquire ⟨by decide, ⟨4, none⟩, rfl, by decide, by decide, rfl⟩) <|
    .cons (by decide) (.resetLock ⟨by decide, ⟨3, none⟩, rfl, by decide, by decide, by decide,
      rfl⟩) .nil
  exact ⟨rfl, runFull_of_run7 (run7_of_run5R ((rx_setup h).run _) (by decide)) (by decide)⟩

/-- `corpus-spec2-m3.md` v13 §2 duodecies W-RX, the other twin, already obtained: W-RL, whose
`resetLock(e)` (step 9) takes the right on `slot` from `root_M`, held by `f0`, is a `RunFull`
from the initial state; its `resetLock` satisfies the guard-free form of C18 item 1 under the
exception and of C18 item 4. -/
theorem W_RL_full : MutexEdge.rlLbls[9]? = some (.resetLock 0 0) ∧
    PremG KM L0 (MutexEdge.rlσ 9) (.resetLock 0 0) ∧ RunFull KM L0 MutexEdge.rlσ MutexEdge.rlLbls :=
  ⟨rfl, by decide,
    runFull_of_run7 (run7_of_run5R MutexEdge.W_RL_run.2 (by decide)) (by decide)⟩

end Ern.Concurrency.FullEncap.Witness
