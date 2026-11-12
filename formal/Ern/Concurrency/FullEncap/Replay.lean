import Ern.Concurrency.FullEncap.NonRegression
import Ern.Concurrency.Corpus.GuardedRead
import Ern.Concurrency.Corpus.GuardedChain
import Ern.Concurrency.Corpus.S10
import Ern.Concurrency.EncapTraces
import Ern.Concurrency.Traces
import Ern.Concurrency.Corpus.Witness
import Ern.Concurrency.FullEncap.ComplementSweep

/-!
# Traces replayed under the complete encapsulation

Brief of milestone 4, slice 3, complement, task 6 (`corpus-spec2-m3.md` v14 §2 terdecies,
"Traces rejouées").

* W-GR, W-GC, W-GS: the excluded step is a local verdict, `ok` at the kernel and outside the
  guard-free forms, on its starting state, reached from the initial state by an admitted prefix.
  The positive suite is a `RunFull` from the initial state: for W-GR and W-GC, the setup, then the
  remaining steps without the excluded one (a read, which leaves the state unchanged, `rfl`); for
  W-GS, its twin (the corpus v14 expects the twin admitted).
* The positive traces that existed only under an older encapsulation (S2, S3 in full, S4, S9, S10,
  the traces of `Traces` and `EncapTraces`, the positive twins of S17a and W-C22.3 (b)) are
  `RunFull` traces from the initial state.
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
from the initial state; step 1 leaves the state unchanged (`gr1 = x4`), so the suite is the
trace of the corpus without it. -/
theorem W_GR_full : opStepC KM (.read 3 [3]) 1 x4 (.ok GuardedRead.gr1) ∧ GuardedRead.gr1 = x4 ∧
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
  exact ⟨GuardedRead.W_GR_1_ok, rfl, by decide, rfl,
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
`read3(Y)` via `z`, through the grant), is a `RunFull` from the initial state; step 1 leaves the
state unchanged (`gc7 = gc6`), so the suite is the trace of the corpus without it. -/
theorem W_GC_full : opStepC KM (.read 3 [4]) 1 gc6 (.ok gc7) ∧ gc7 = gc6 ∧
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
  exact ⟨gc_read.2, rfl, by decide, rfl,
    runFull_of_run7 (run7_of_run5R (h.run _) (by decide)) (by decide)⟩

/-! ## W-GS -/

open Ern.Concurrency.Corpus.GuardedStore in
/-- `corpus-spec2-m3.md` v14 §2 terdecies, W-GS under the complete encapsulation. Local verdict:
step 1, `c0 : store(z2, T)` without the grant, is `ok` at the kernel (O8, `W_GS_1_ok`) and
outside the guard-free forms (the right on `T`, Spec 1 §65.2, holds only through `guarded`), its
state being reached by the admitted setup. Positive suite: the twin (`c0 : acquire(e)`, then
`store(z2, T)` under the grant) is a `RunFull` from the initial state, as the corpus v14 expects. -/
theorem W_GS_full : opStepC KM (.store 4 3) 0 gs5 (.ok gs6) ∧
    ¬ PremG KM L0 (gs5, sreg, []) (.kernel 0 (.store 4 3)) ∧
    MutexReal.NonRegression.gsTwinσ 0 = (SC.ofS3 (S3.init GuardedChain.zst), [], []) ∧
    RunFull KM L0 MutexReal.NonRegression.gsTwinσ MutexReal.NonRegression.gsTwinLbls :=
  ⟨W_GS_1_ok, by decide, rfl, NonRegression.runAmF_traces_full.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

open Ern.Concurrency.Corpus.GuardedStore in
/-- W-GS, steps 2 and 3 on the states of the corpus trace, after the excluded step 1: `c1 :
acquire(e)` from `gs6` and `c1 : read3(T)` via `g₁` from `gs7` are `ok` steps that the complete
encapsulation admits. The corpus v14 gives no verdict for these two steps under the complete
encapsulation (only `ok` at the kernel, v6 §2 sexies); this is a fact obtained, not an expected
one. -/
theorem W_GS_2_3_local :
    EncapFull KM L0 (gs6, sreg, []) (.acquire 1 0) (gs7, sregG, []) ∧
    LStep KM L0 (.acquire 1 0) (gs6, sreg, []) (gs7, sregG, []) ∧
    EncapFull KM L0 (gs7, sregG, []) (.kernel 1 (.read 6 [3])) (gs8, sregG, []) ∧
    LStep KM L0 (.kernel 1 (.read 6 [3])) (gs7, sregG, []) (gs8, sregG, []) :=
  ⟨⟨⟨by decide, by decide⟩, by decide⟩,
    .acquire ⟨by decide, ⟨3, none⟩, rfl, by decide, by decide, rfl⟩,
    ⟨⟨by decide, by decide⟩, by decide⟩, .kernel ⟨by decide, _, .ok (by decide), rfl⟩⟩

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

/-! ## The traces of `Traces` and `EncapTraces` -/

open Ern.Concurrency.Traces in
/-- The named states of `mutex_trace` (WC5.2 C13, C16, C17). -/
def mtσ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(c0, [], []), (c0, reg1, []), (c2, reg2, []), (c3, reg1, [])].getD i (c3, reg1, [])

/-- The labels of `mutex_trace`. -/
def mtLbls : List Label := [.newMutex 0 1, .acquire 0 0, .unlock 0 0]

open Ern.Concurrency.Traces in
/-- `mutex_trace` (`newMutex`, `acquire`, `unlock` from `c0`, WC5.2 C13, C16, C17) is a `RunFull`
from the initial state. -/
theorem mutex_full : mtσ 0 = (SC.ofS3 (S3.init mst), [], []) ∧ RunFull K0 L0 mtσ mtLbls := by
  have h : Steps5R K0 L0 [(c0, [], []), (c0, reg1, []), (c2, reg2, []), (c3, reg1, [])] mtLbls :=
    .cons (by decide) (.newMutex newMutex_ok.1) <|
    .cons (by decide) (.acquire acquire_enabled) <|
    .cons (by decide) (.unlock unlock_enabled) .nil
  exact ⟨rfl, runFull_of_run7 (run7_of_run5R (h.run _) (by decide)) (by decide)⟩

open Ern.Concurrency.Traces in
/-- The named states of `distinct_controllers_trace`. -/
def dtσ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(d1, [], []), (d1, [⟨2, none⟩], []), (d1, [⟨2, none⟩, ⟨3, none⟩], [])].getD i
    (d1, [⟨2, none⟩, ⟨3, none⟩], [])

/-- The labels of `distinct_controllers_trace`. -/
def dtLbls : List Label := [.newMutex 0 2, .newMutex 0 3]

open Ern.Concurrency.Traces in
/-- `distinct_controllers_trace` (two `newMutex` with distinct controllers from `d1`, WC5.2 C13)
is a `RunFull` from the initial state. -/
theorem distinct_full : dtσ 0 = (SC.ofS3 (S3.init mst3), [], []) ∧ RunFull K0 L0 dtσ dtLbls := by
  have h : Steps5R K0 L0 [(d1, [], []), (d1, [⟨2, none⟩], []), (d1, [⟨2, none⟩, ⟨3, none⟩], [])]
      dtLbls :=
    .cons (by decide) (.newMutex distinct_controllers_ok.1) <|
    .cons (by decide) (.newMutex distinct_controllers_ok.2.1) .nil
  exact ⟨rfl, runFull_of_run7 (run7_of_run5R (h.run _) (by decide)) (by decide)⟩

open Ern.Concurrency.EncapTraces in
/-- The named states of `traceB` (WC5.2 §V S18, positive: transfer of the whole mutex under the
grant). -/
def tBσ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(e0, [], []), (e1, [], []), (e2, [], []), (e2, reg1, []), (e3, reg2, []), (eB, reg2, [])].getD i
    (eB, reg2, [])

open Ern.Concurrency.EncapTraces in
/-- The named states of `traceA` (WC5.2 §V S18, positive: transfer of the whole mutex without
grant); its prefix of three labels is `traceMutex`. -/
def tAσ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(e0, [], []), (e1, [], []), (e2, [], []), (e2, reg1, []), (eA, reg1, [])].getD i
    (eA, reg1, [])

open Ern.Concurrency.EncapTraces in
/-- `traceA`, `traceB` and `traceMutex` (`EncapTraces`) are `RunFull` traces from the initial
state. -/
theorem wc4_full : tAσ 0 = (SC.ofS3 (S3.init est), [], []) ∧ tBσ 0 = tAσ 0 ∧
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
  exact ⟨rfl, rfl, rA,
    runFull_of_run7 (run7_of_run5R (hB.run (eB, reg2, [])) (by decide)) (by decide),
    RunFull.take rA 3⟩

open Ern.Concurrency.EncapTraces in
/-- The named states of `endUse_mutex_kills_entry`. -/
def kmσ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(e0, [], []), (e1, [], []), (e2, [], []), (e2, reg1, []), (eM, reg1, [])].getD i (eM, reg1, [])

/-- The labels of `endUse_mutex_kills_entry`. -/
def kmLbls : List Label :=
  [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 4 1), .newMutex 0 4, .kernel 0 (.endUse 0)]

open Ern.Concurrency.EncapTraces in
/-- `endUse_mutex_kills_entry` (WC5.2 C22 item 5, S17b positive: `endUse(M)` kills the entry) is a
`RunFull` from the initial state. -/
theorem endUseM_full : kmσ 0 = (SC.ofS3 (S3.init est), [], []) ∧ RunFull K0 L0 kmσ kmLbls := by
  have h : Steps5R K0 L0 [(e0, [], []), (e1, [], []), (e2, [], []), (e2, reg1, []),
      (eM, reg1, [])] kmLbls :=
    .cons (by decide) (.kernel step_derive) <| .cons (by decide) (.kernel step_store) <|
    .cons (by decide) (.newMutex step_newMutex.1) <|
    .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) .nil
  exact ⟨rfl, runFull_of_run7 (run7_of_run5R (h.run _) (by decide)) (by decide)⟩

/-- The named states of `endUse_slot_kills_entry`. -/
def ksσ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(EncapTraces.z0, [], []), (EncapTraces.z0, [⟨1, none⟩], []),
    (EncapTraces.z2, [⟨1, none⟩], [])].getD i (EncapTraces.z2, [⟨1, none⟩], [])

/-- The labels of `endUse_slot_kills_entry`. -/
def ksLbls : List Label := [.newMutex 0 1, .kernel 0 (.endUse 1)]

/-- `endUse_slot_kills_entry` (WC5.2 C22 item 5, S17b positive: `endUse(slot)` kills the entry) is
a `RunFull` from the initial state. -/
theorem endUseSlot_full : ksσ 0 = (SC.ofS3 (S3.init EncapTraces.sst), [], []) ∧
    RunFull K0 L0 ksσ ksLbls := by
  have h : Steps5R K0 L0 [(EncapTraces.z0, [], []), (EncapTraces.z0, [⟨1, none⟩], []),
      (EncapTraces.z2, [⟨1, none⟩], [])] ksLbls :=
    .cons (by decide) (.newMutex EncapTraces.z_newMutex) <|
    .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) .nil
  exact ⟨rfl, runFull_of_run7 (run7_of_run5R (h.run _) (by decide)) (by decide)⟩

/-! ## Positive twins of the corpus §1 and §2 -/

/-- The named states of the twin of W-C22.3 (b). -/
def tbσ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(Corpus.w0, [], []), (Corpus.w0, [⟨1, none⟩], []), (Corpus.w2, [⟨1, none⟩], [])].getD i
    (Corpus.w2, [⟨1, none⟩], [])

/-- The labels of the twin of W-C22.3 (b). -/
def tbLbls : List Label := [.newMutex 0 1, .kernel 0 (.transfer 0 7)]

/-- `corpus-spec2-m3.md` §2 W-C22.3 (b), twin (`W_C22_3b_ok`: `newMutex(guarded)`, then
`transfer(M, M′)`) is a `RunFull` from the initial state. -/
theorem W_C22_3b_twin_full : tbσ 0 = (SC.ofS3 (S3.init Corpus.wst), [], []) ∧
    RunFull Corpus.KW L0 tbσ tbLbls := by
  have hn : NewMutexOk Corpus.KW L0 [] Corpus.w0 [] 0 1 (Corpus.w0, [⟨1, none⟩]) :=
    ⟨by decide, by decide, rfl⟩
  have h : Steps5R Corpus.KW L0 [(Corpus.w0, [], []), (Corpus.w0, [⟨1, none⟩], []),
      (Corpus.w2, [⟨1, none⟩], [])] tbLbls :=
    .cons (by decide) (.newMutex hn) <| .cons (by decide) (.kernel Corpus.W_C22_3b_ok.1) .nil
  exact ⟨rfl, runFull_of_run7 (run7_of_run5R (h.run _) (by decide)) (by decide)⟩

open Ern.Concurrency.EncapTraces in
/-- The named states of the twin of S17a. -/
def saσ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(e0, [], []), (e1, [], []), (e2, [], []), (e2, reg1, []), (Corpus.eS, reg1, []),
    (Corpus.eL, reg1, [])].getD i (Corpus.eL, reg1, [])

/-- The labels of the twin of S17a. -/
def saLbls : List Label :=
  [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 4 1), .newMutex 0 4,
    .kernel 0 (.endUse 1), .kernel 0 (.endUse 2)]

open Ern.Concurrency.EncapTraces in
/-- `corpus-spec2-m3.md` §1 S17a, twin (`S17a_2_ok`: `MX₃`, then `endUse(slot)`, which kills the
entry, then `endUse(lock)`) is a `RunFull` from the initial state. -/
theorem S17a_twin_full : saσ 0 = (SC.ofS3 (S3.init est), [], []) ∧ RunFull K0 L0 saσ saLbls := by
  have h : Steps5R K0 L0 [(e0, [], []), (e1, [], []), (e2, [], []), (e2, reg1, []),
      (Corpus.eS, reg1, []), (Corpus.eL, reg1, [])] saLbls :=
    .cons (by decide) (.kernel step_derive) <| .cons (by decide) (.kernel step_store) <|
    .cons (by decide) (.newMutex step_newMutex.1) <|
    .cons (by decide) (.kernel Corpus.S17a_2_ok.1) <|
    .cons (by decide) (.kernel Corpus.S17a_2_ok.2.2.2.1) .nil
  exact ⟨rfl, runFull_of_run7 (run7_of_run5R (h.run _) (by decide)) (by decide)⟩

/-! ## The sweep of the complement on the replayed traces -/

open Ern.Concurrency.FullEncap.Sweep in
/-- Brief of the complement, tasks 2, 3 and 5, on the replayed traces: the closure, the three
cases, the absence of another context's capacity on a dying leaf, and the kinds that kill a leaf
(`KillOK`) are checked at every step. -/
theorem sweep_replay :
    (SweepOK L0 wrσ wrLbls ∧ KillOK wrσ wrLbls) ∧ (SweepOK L0 cgσ cgLbls ∧ KillOK cgσ cgLbls) ∧
    (SweepOK L0 s3fσ s3fLbls ∧ KillOK s3fσ s3fLbls) ∧
    (SweepOK L0 s4σ s4Lbls ∧ KillOK s4σ s4Lbls) ∧ (SweepOK L0 s9σ s9Lbls ∧ KillOK s9σ s9Lbls) ∧
    (SweepOK L0 mtσ mtLbls ∧ KillOK mtσ mtLbls) ∧ (SweepOK L0 dtσ dtLbls ∧ KillOK dtσ dtLbls) ∧
    (SweepOK L0 tAσ [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 4 1), .newMutex 0 4,
      .kernel 0 (.transfer 0 4)] ∧ KillOK tAσ [.kernel 0 (.derive 1 [3] .modify),
      .kernel 0 (.store 4 1), .newMutex 0 4, .kernel 0 (.transfer 0 4)]) ∧
    (SweepOK L0 tBσ [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 4 1), .newMutex 0 4,
      .acquire 0 0, .kernel 0 (.transfer 0 4)] ∧ KillOK tBσ [.kernel 0 (.derive 1 [3] .modify),
      .kernel 0 (.store 4 1), .newMutex 0 4, .acquire 0 0, .kernel 0 (.transfer 0 4)]) ∧
    (SweepOK L0 kmσ kmLbls ∧ KillOK kmσ kmLbls) ∧ (SweepOK L0 ksσ ksLbls ∧ KillOK ksσ ksLbls) ∧
    (SweepOK L0 tbσ tbLbls ∧ KillOK tbσ tbLbls) ∧ (SweepOK L0 saσ saLbls ∧ KillOK saσ saLbls) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end Ern.Concurrency.FullEncap.Replay
