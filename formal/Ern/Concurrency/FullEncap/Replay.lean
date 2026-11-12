import Ern.Concurrency.FullEncap.NonRegression
import Ern.Concurrency.Corpus.GuardedRead
import Ern.Concurrency.Corpus.GuardedChain
import Ern.Concurrency.Corpus.S10
import Ern.Concurrency.EncapTraces
import Ern.Concurrency.Traces

/-!
# Traces replayed under the complete encapsulation

Brief of milestone 4, slice 3, complement, task 6 (`corpus-spec2-m3.md` v14 §2 terdecies,
"Traces rejouées").

* W-GR, W-GC, W-GS: the excluded step is a local verdict, `ok` at the kernel and outside the
  guard-free forms, on its starting state, reached from the initial state by an admitted prefix;
  the positive suite (the setup, then the remaining steps, without the excluded one) is a
  `RunFull` from the initial state.
* The traces that existed only under an older encapsulation (S2, S3 in full, S4, S9, S10, the
  traces of WC4 in `Traces` and `EncapTraces`) are `RunFull` traces.
-/

set_option autoImplicit false

namespace Ern.Concurrency.FullEncap.Replay

open Ern.MemoryModel Ern.MemoryModel.Access Ern.Concurrency Ern.Concurrency.MutexReal
open Ern.Concurrency.Corpus
open Ern.Concurrency.FullEncap.Witness (instDecidableEncap5R)
open Ern.Concurrency.Traces (L0)
open Ern.MemoryModel.Access.Examples (K0)

/-- A prefix of a `RunFull` is a `RunFull`. -/
theorem RunFull.take {k : K} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg}
    {lbls : List Label} (h : RunFull k L σ lbls) (n : Nat) : RunFull k L σ (lbls.take n) :=
  fun i hi => by
    have hi' : i < lbls.length := by simp at hi; omega
    have e : (lbls.take n)[i] = lbls[i] := List.getElem_take
    rw [e]; exact h i hi'

/-! ## W-GR -/

/-- W-GR, suite without step 1: `c0 : acquire(e)` from `MX₄`, grant `g`, authority 5. -/
def wr5 : SC := deriveSyncEff x4 0 3
/-- W-GR, suite: `c0 : write3(T)` via `g` (O10). -/
def wr6 : SC := wr5.set (write3Eff (wr5.view 0) [3])
/-- The registry with `g` recorded. -/
def wrReg : SyncReg := [⟨3, some 5⟩]

/-- The labels of `MX₄`. -/
def mx4Lbls : List Label :=
  [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 3 1), .newMutex 0 3,
   .kernel 0 (.derive 0 [1, 2] .observe), .spawn 0 [4] []]

/-- The labels of the positive suite of W-GR. -/
def wrLbls : List Label := mx4Lbls ++ [.acquire 0 0, .kernel 0 (.write 5 [3])]

/-- The named states of the positive suite of W-GR. -/
def wrσ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(x0, [], []), (x1, [], []), (x2, [], []), (x2, regX, []), (x3, regX, []), (x4, regX, []),
    (wr5, wrReg, []), (wr6, wrReg, [])].getD i (wr6, wrReg, [])

/-- `corpus-spec2-m3.md` v14 §2 terdecies, W-GR under the complete encapsulation. Local verdict:
step 1, `c1 : read3(T)` with `access = guarded` from `MX₄`, is `ok` at the kernel (O9) and outside
the guard-free forms (its access authority is the live `guarded`, WC5.2 C22 item 6), `MX₄` being
reached by the admitted prefix of the suite. Suite: `MX₄`, then steps 2 and 3, is a `RunFull`
from the initial state; step 1 changes no state (O9), so the suite does not depend on it. -/
theorem W_GR_full : opStepC KM (.read 3 [3]) 1 x4 (.ok GuardedRead.gr1) ∧
    ¬ PremG KM L0 (x4, regX, []) (.kernel 1 (.read 3 [3])) ∧
    wrσ 0 = (SC.ofS3 (S3.init mxst), [], []) ∧ RunFull KM L0 wrσ wrLbls := by
  have h : Steps5R KM L0 [(x2, regX, []), (x3, regX, []), (x4, regX, []), (wr5, wrReg, []),
      (wr6, wrReg, [])]
      [.kernel 0 (.derive 0 [1, 2] .observe), .spawn 0 [4] [], .acquire 0 0,
        .kernel 0 (.write 5 [3])] :=
    .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons (by decide) (.spawn ⟨by decide, .ok (by decide)⟩) <|
    .cons (by decide) (.acquire ⟨by decide, ⟨3, none⟩, rfl, by decide, by decide, rfl⟩) <|
    .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) .nil
  exact ⟨GuardedRead.W_GR_1_ok, by decide, rfl,
    runFull_of_run7 (run7_of_run5R ((ClassifyWitness.mx3_steps h).run _) (by decide))
      (by decide)⟩

/-! ## W-GC -/

open Ern.Concurrency.Corpus.GuardedChain in
/-- W-GC, suite without step 1: `c0 : acquire(e)`, grant `g`, authority 6. -/
def cg7 : SC := deriveSyncEff GuardedChain.gc6 0 4
/-- W-GC, suite: `c0 : write3(Y)` via `z` (O10). -/
def cg8 : SC := cg7.set (write3Eff (cg7.view 0) [4])
/-- W-GC, suite: `c0 : read3(Y)` via `z` (O9). -/
def cg9 : SC := cg8.set (cg8.view 0)
/-- The registry with `g` recorded. -/
def cgReg : SyncReg := [⟨4, some 6⟩]

/-- The labels of the positive suite of W-GC: the setup, then steps 2 to 4. -/
def cgLbls : List Label :=
  GuardedChain.glbls.take 7 ++ [.acquire 0 0, .kernel 0 (.write 3 [4]), .kernel 0 (.read 3 [4])]

open Ern.Concurrency.Corpus.GuardedChain in
/-- The named states of the positive suite of W-GC. -/
def cgσ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(gc0, [], []), (gc1, [], []), (gc2, [], []), (gc3, [], []), (gc4, [], []), (gc4, greg, []),
    (gc5, greg, []), (gc6, greg, []), (cg7, cgReg, []), (cg8, cgReg, []), (cg9, cgReg, [])].getD i
    (cg9, cgReg, [])

open Ern.Concurrency.Corpus.GuardedChain in
/-- `corpus-spec2-m3.md` v14 §2 terdecies, W-GC under the complete encapsulation. Local verdict:
step 1, `c1 : read3(Y)` via `z`, is `ok` at the kernel (O9, `gc_read`) and outside the
guard-free forms (`Exer5` of `z` passes through the live `guarded`), its state being reached by
the admitted setup. Suite: the setup, then steps 2 to 4 (`c0 : acquire(e)`, `write3(Y)`,
`read3(Y)` via `z`, through the grant), is a `RunFull` from the initial state; step 1 changes no
state (O9). -/
theorem W_GC_full : opStepC KM (.read 3 [4]) 1 gc6 (.ok gc7) ∧
    ¬ PremG KM L0 (gc6, greg, []) (.kernel 1 (.read 3 [4])) ∧
    cgσ 0 = (SC.ofS3 (S3.init zst), [], []) ∧ RunFull KM L0 cgσ cgLbls := by
  have h : Steps5R KM L0 [(gc0, [], []), (gc1, [], []), (gc2, [], []), (gc3, [], []),
      (gc4, [], []), (gc4, greg, []), (gc5, greg, []), (gc6, greg, []), (cg7, cgReg, []),
      (cg8, cgReg, []), (cg9, cgReg, [])] cgLbls :=
    .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons (by decide) (.kernel ⟨by decide, .ok (by decide)⟩) <|
    .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons (by decide) (.kernel ⟨by decide, .ok (by decide)⟩) <|
    .cons (by decide) (.newMutex ⟨by decide, by decide, rfl⟩) <|
    .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons (by decide) (.spawn ⟨by decide, .ok (by decide)⟩) <|
    .cons (by decide) (.acquire ⟨by decide, ⟨4, none⟩, rfl, by decide, by decide, rfl⟩) <|
    .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) .nil
  exact ⟨gc_read.2, by decide, rfl,
    runFull_of_run7 (run7_of_run5R (h.run _) (by decide)) (by decide)⟩

/-! ## W-GS -/

open Ern.Concurrency.Corpus.GuardedStore in
/-- W-GS, suite without step 1: `c1 : acquire(e)` from the state before step 1, grant `g₁`,
authority 6, held by frame 1. -/
def sg6 : SC := deriveSyncEff gs5 1 3
/-- W-GS, suite: `c1 : read3(T)` via `g₁` (O9). -/
def sg7 : SC := sg6.set (sg6.view 1)

/-- The labels of the positive suite of W-GS. -/
def sgLbls : List Label :=
  GuardedStore.setupLbls ++ [.acquire 1 0, .kernel 1 (.read 6 [3])]

open Ern.Concurrency.Corpus.GuardedStore in
/-- The named states of the positive suite of W-GS. -/
def sgσ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(gs0, [], []), (gs1, [], []), (gs2, [], []), (gs2, sreg, []), (gs3, sreg, []),
    (gs4, sreg, []), (gs5, sreg, []), (sg6, sregG, []), (sg7, sregG, [])].getD i
    (sg7, sregG, [])

open Ern.Concurrency.Corpus.GuardedStore in
/-- `corpus-spec2-m3.md` v14 §2 terdecies, W-GS under the complete encapsulation. Local verdict:
step 1, `c0 : store(z2, T)` without the grant, is `ok` at the kernel (O8, `W_GS_1_ok`) and
outside the guard-free forms (the right on `T`, Spec 1 §65.2, holds only through `guarded`), its
state being reached by the admitted setup. Suite: the setup, then steps 2 and 3 replayed from the
state before step 1, is a `RunFull` from the initial state; there, unlike in W-GS, `z2` is still
held by `f0` (step 2 and 3 do not read it). The twin is a `RunFull` (`runAmF_traces_full`). -/
theorem W_GS_full : opStepC KM (.store 4 3) 0 gs5 (.ok gs6) ∧
    ¬ PremG KM L0 (gs5, sreg, []) (.kernel 0 (.store 4 3)) ∧
    sgσ 0 = (SC.ofS3 (S3.init GuardedChain.zst), [], []) ∧ RunFull KM L0 sgσ sgLbls := by
  have h : Steps5R KM L0 [(gs0, [], []), (gs1, [], []), (gs2, [], []), (gs2, sreg, []),
      (gs3, sreg, []), (gs4, sreg, []), (gs5, sreg, []), (sg6, sregG, []), (sg7, sregG, [])]
      sgLbls :=
    .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons (by decide) (.kernel ⟨by decide, .ok (by decide)⟩) <|
    .cons (by decide) (.newMutex ⟨by decide, by decide, rfl⟩) <|
    .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons (by decide) (.spawn ⟨by decide, .ok (by decide)⟩) <|
    .cons (by decide) (.acquire ⟨by decide, ⟨3, none⟩, rfl, by decide, by decide, rfl⟩) <|
    .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) .nil
  exact ⟨W_GS_1_ok, by decide, rfl,
    runFull_of_run7 (run7_of_run5R (h.run _) (by decide)) (by decide)⟩

/-! ## Traces under an older encapsulation -/

/-- The labels of S2 (`s2_trace`): `MX₄`, `c1 : acquire(e)`, `write3(T)`, `unlock(e)`. -/
def s2Lbls : List Label := mx4Lbls ++ [.acquire 1 0, .kernel 1 (.write 5 [3]), .unlock 1 0]

/-- `corpus-spec2-m3.md` §1 S2 (`s2_trace`, `cycle_trace5`) is a `RunFull` from the initial
state: the prefix of W-RL₀ of its eight labels. -/
theorem S2_full : (MutexEdge.rl0Lbls.take 8) = s2Lbls ∧
    RunFull KM L0 MutexEdge.rl0σ (MutexEdge.rl0Lbls.take 8) :=
  ⟨rfl, RunFull.take NonRegression.runAmF_traces_full.2.2.2.2.2.2.1 8⟩

/-- `corpus-spec2-m3.md` §1 S10 (`s10_trace`, up to `transfer(M, M′)`) is a `RunFull` from the
initial state: the prefix of the replayed S10 of its seven labels. -/
theorem S10_full : RunFull KM L0 MutexReal.NonRegression.s10σ
    (MutexReal.NonRegression.s10Lbls.take 7) :=
  RunFull.take NonRegression.runAmF_traces_full.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 7

/-- The labels of S3 in full (`s3_trace`). -/
def s3fLbls : List Label :=
  MutexReal.NonRegression.s3Lbls ++ [.unlock 1 0, .acquire 0 0, .issue 0 0 [6] 7]

/-- The named states of S3 in full. -/
def s3fσ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(a0, [], []), (a1, [], []), (a2, [], []), (a2, [], arA), (a3, [], arA), (a4, [], arA),
    (a4, regA, arA), (a5, regA, arA), (a6, regA, arA), (a7, regA8, arA), (a8, regA8, arA1),
    (a9, regA, arA1), (a10, regA10, arA1), (a11, regA10, arA2)].getD i (a11, regA10, arA2)

/-- `corpus-spec2-m3.md` §1 S3 in full (`s3_trace`: the arena administered through the mutex grant,
both issues and the reacquisition) is a `RunFull` from the initial state. -/
theorem S3_full : s3fσ 0 = (SC.ofS3 (S3.init arst), [], []) ∧ RunFull KA L0 s3fσ s3fLbls := by
  have hn : NewMutexOk KA L0 arA a4 [] 0 5 (a4, regA) := ⟨by decide, by decide, rfl⟩
  have ha : NewArenaStepC a2 [] [] 0 4 4 (.ok (a2, arA)) := ⟨by decide, .ok (by decide)⟩
  have h : Steps5R KA L0 [(a0, [], []), (a1, [], []), (a2, [], []), (a2, [], arA), (a3, [], arA),
      (a4, [], arA), (a4, regA, arA), (a5, regA, arA), (a6, regA, arA), (a7, regA8, arA),
      (a8, regA8, arA1), (a9, regA, arA1), (a10, regA10, arA1), (a11, regA10, arA2)] s3fLbls :=
    .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons (by decide) (.kernel ⟨by decide, .ok (by decide)⟩) <|
    .cons (by decide) (.newArena ha) <|
    .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons (by decide) (.kernel ⟨by decide, .ok (by decide)⟩) <|
    .cons (by decide) (.newMutex hn) <|
    .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons (by decide) (.spawn ⟨by decide, .ok (by decide)⟩) <|
    .cons (by decide) (.acquire S3_2_ok) <|
    .cons (by decide) (.issue S3_3_ok) <|
    .cons (by decide) (.unlock S3_5_ok) <|
    .cons (by decide) (.acquire S3_6_ok) <|
    .cons (by decide) (.issue S3_8_ok) .nil
  exact ⟨rfl, runFull_of_run7 (run7_of_run5R (h.run _) (by decide)) (by decide)⟩

/-- The labels of S4 (`s4_trace`, `s4_trace5R`). -/
def s4Lbls : List Label :=
  [.kernel 0 (.enter [] [(none, 0), (none, 0)]), .kernel 0 (.write 1 [1]),
   .kernel 0 (.write 2 [2]), .kernel 0 (.alloc 2 1 [(none, 0)]),
   .spawnVal 0 [] [(none, 0)] [(1, 4)], .kernel 0 .exit]

open Ern.Concurrency.Traces in
/-- The named states of S4. -/
def s4σ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(q0, [], []), (q1, [], []), (q2, [], []), (q3, [], []), (q4, [], []), (q5, [], []),
    (q6, [], [])].getD i (q6, [], [])

open Ern.Concurrency.Traces in
/-- `corpus-spec2-m3.md` §1 S4 (`s4_trace`): a detached child survives its creator; the trace is a
`RunFull` from the initial state (no mutex). -/
theorem S4_full : s4σ 0 = (SC.ofS3 (S3.init s4st), [], []) ∧ RunFull K0 L0 s4σ s4Lbls := by
  have h : Steps5R K0 L0 [(q0, [], []), (q1, [], []), (q2, [], []), (q3, [], []), (q4, [], []),
      (q5, [], []), (q6, [], [])] s4Lbls :=
    .cons (by decide) (.kernel s4_steps.1) <| .cons (by decide) (.kernel s4_steps.2.1) <|
    .cons (by decide) (.kernel s4_steps.2.2.1) <| .cons (by decide) (.kernel s4_steps.2.2.2.1) <|
    .cons (by decide) (.spawnVal s4_steps.2.2.2.2.1) <|
    .cons (by decide) (.kernel s4_steps.2.2.2.2.2) .nil
  exact ⟨rfl, runFull_of_run7 (run7_of_run5R (h.run _) (by decide)) (by decide)⟩

/-- The labels of S9 (`s9_trace`, `S9_1_ok`, `S9_2_ok`). -/
def s9Lbls : List Label :=
  [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 4 1), .kernel 0 (.derive 3 [7] .modify),
   .kernel 0 (.store 5 5), .newMutex 0 4, .newMutex 0 5, .acquire 0 0, .acquire 0 1]

/-- The named states of S9. -/
def s9σ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(n0, [], []), (n1, [], []), (n2, [], []), (n3, [], []), (n4, [], []), (n4, [⟨4, none⟩], []),
    (n4, reg9, []), (n5, [⟨4, some 6⟩, ⟨5, none⟩], []),
    (n6, [⟨4, some 6⟩, ⟨5, some 7⟩], [])].getD i (n6, [⟨4, some 6⟩, ⟨5, some 7⟩], [])

/-- `corpus-spec2-m3.md` §1 S9 (two mutexes, both acquired by context 0) is admitted: the trace is
a `RunFull` from the initial state, as the corpus v14 expects. -/
theorem S9_full : s9σ 0 = (SC.ofS3 (S3.init s9st), [], []) ∧ RunFull K9 L0 s9σ s9Lbls := by
  have h : Steps5R K9 L0 [(n0, [], []), (n1, [], []), (n2, [], []), (n3, [], []), (n4, [], []),
      (n4, [⟨4, none⟩], []), (n4, reg9, []), (n5, [⟨4, some 6⟩, ⟨5, none⟩], []),
      (n6, [⟨4, some 6⟩, ⟨5, some 7⟩], [])] s9Lbls :=
    .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons (by decide) (.kernel ⟨by decide, .ok (by decide)⟩) <|
    .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons (by decide) (.kernel ⟨by decide, .ok (by decide)⟩) <|
    .cons (by decide) (.newMutex ⟨by decide, by decide, rfl⟩) <|
    .cons (by decide) (.newMutex ⟨by decide, by decide, rfl⟩) <|
    .cons (by decide) (.acquire S9_1_ok.1) <|
    .cons (by decide) (.acquire S9_2_ok.1) .nil
  exact ⟨rfl, runFull_of_run7 (run7_of_run5R (h.run _) (by decide)) (by decide)⟩

/-! ## The traces of WC4 -/

open Ern.Concurrency.Traces in
/-- The named states of `mutex_trace` (WC4 C13, C16, C17). -/
def mtσ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(c0, [], []), (c0, reg1, []), (c2, reg2, []), (c3, reg1, [])].getD i (c3, reg1, [])

open Ern.Concurrency.Traces in
/-- `mutex_trace` (`newMutex`, `acquire`, `unlock` from `c0`) is a `RunFull`. -/
theorem mutex_full : RunFull K0 L0 mtσ [.newMutex 0 1, .acquire 0 0, .unlock 0 0] := by
  have h : Steps5R K0 L0 [(c0, [], []), (c0, reg1, []), (c2, reg2, []), (c3, reg1, [])]
      [.newMutex 0 1, .acquire 0 0, .unlock 0 0] :=
    .cons (by decide) (.newMutex newMutex_ok.1) <|
    .cons (by decide) (.acquire acquire_enabled) <|
    .cons (by decide) (.unlock unlock_enabled) .nil
  exact runFull_of_run7 (run7_of_run5R (h.run _) (by decide)) (by decide)

open Ern.Concurrency.Traces in
/-- `distinct_controllers_trace` (two `newMutex` with distinct controllers from `d1`) is a
`RunFull`. -/
theorem distinct_full : RunFull K0 L0
    (fun i => [(d1, [], []), (d1, [⟨2, none⟩], []), (d1, [⟨2, none⟩, ⟨3, none⟩], [])].getD i
      (d1, [⟨2, none⟩, ⟨3, none⟩], [])) [.newMutex 0 2, .newMutex 0 3] := by
  have h : Steps5R K0 L0 [(d1, [], []), (d1, [⟨2, none⟩], []), (d1, [⟨2, none⟩, ⟨3, none⟩], [])]
      [.newMutex 0 2, .newMutex 0 3] :=
    .cons (by decide) (.newMutex distinct_controllers_ok.1) <|
    .cons (by decide) (.newMutex distinct_controllers_ok.2.1) .nil
  exact runFull_of_run7 (run7_of_run5R (h.run _) (by decide)) (by decide)

open Ern.Concurrency.EncapTraces in
/-- The named states of `traceB` (WC4 S18, transfer of the whole mutex under the grant). -/
def tBσ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(e0, [], []), (e1, [], []), (e2, [], []), (e2, reg1, []), (e3, reg2, []), (eB, reg2, [])].getD i
    (eB, reg2, [])

open Ern.Concurrency.EncapTraces in
/-- The named states of `traceA` (WC4 S18, transfer of the whole mutex without grant); its prefix
of three labels is `traceMutex`. -/
def tAσ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(e0, [], []), (e1, [], []), (e2, [], []), (e2, reg1, []), (eA, reg1, [])].getD i
    (eA, reg1, [])

open Ern.Concurrency.EncapTraces in
/-- `traceA`, `traceB` and `traceMutex` (`EncapTraces`, WC4) are `RunFull` traces. -/
theorem wc4_full :
    RunFull K0 L0 tAσ [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 4 1), .newMutex 0 4,
      .kernel 0 (.transfer 0 4)] ∧
    RunFull K0 L0 tBσ [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 4 1), .newMutex 0 4,
      .acquire 0 0, .kernel 0 (.transfer 0 4)] ∧
    RunFull K0 L0 tAσ [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 4 1),
      .newMutex 0 4] := by
  have hA : Steps5R K0 L0 [(e0, [], []), (e1, [], []), (e2, [], []), (e2, reg1, []),
      (eA, reg1, [])] [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 4 1), .newMutex 0 4,
      .kernel 0 (.transfer 0 4)] :=
    .cons (by decide) (.kernel step_derive) <| .cons (by decide) (.kernel step_store) <|
    .cons (by decide) (.newMutex step_newMutex.1) <|
    .cons (by decide) (.kernel stepA_transfer) .nil
  have hB : Steps5R K0 L0 [(e0, [], []), (e1, [], []), (e2, [], []), (e2, reg1, []),
      (e3, reg2, []), (eB, reg2, [])] [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 4 1),
      .newMutex 0 4, .acquire 0 0, .kernel 0 (.transfer 0 4)] :=
    .cons (by decide) (.kernel step_derive) <| .cons (by decide) (.kernel step_store) <|
    .cons (by decide) (.newMutex step_newMutex.1) <| .cons (by decide) (.acquire step_acquire.1) <|
    .cons (by decide) (.kernel stepB_transfer) .nil
  have rA : RunFull K0 L0 tAσ [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 4 1),
      .newMutex 0 4, .kernel 0 (.transfer 0 4)] :=
    runFull_of_run7 (run7_of_run5R (hA.run (eA, reg1, [])) (by decide)) (by decide)
  exact ⟨rA, runFull_of_run7 (run7_of_run5R (hB.run (eB, reg2, [])) (by decide)) (by decide),
    RunFull.take rA 3⟩

end Ern.Concurrency.FullEncap.Replay
