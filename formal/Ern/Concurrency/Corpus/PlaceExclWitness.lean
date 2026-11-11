import Ern.Concurrency.Encap5R
import Ern.Concurrency.Corpus.GuardedStore
import Ern.Concurrency.Corpus.GuardedChainC
import Ern.Concurrency.Corpus.Encap5Witness
import Ern.Concurrency.Corpus.AR
import Ern.Concurrency.Corpus.S10

/-!
# Witnesses of the extended exclusion `PlaceExcl`

Brief of milestone 4, task 3: test of `PlaceExcl` (`Ern.Concurrency.Encap5R`) on W-GS
(`corpus-spec2-m3.md` v6 §2 sexies), on the locked trace of `Corpus/GuardedChainC.lean`, and on the
legitimate uses of `corpus-spec2-m3.md` v6 §1 (S2, S3 up to `issue`, S4, S10), replayed from the
initial state of Spec 1 §47, by `decide`.
-/

namespace Ern.Concurrency.Corpus.PlaceExclWitness

open Ern.MemoryModel.Access Ern.Concurrency Ern.Concurrency.Corpus
open Ern.Concurrency.Corpus.GuardedStore
open Ern.Concurrency.Corpus.GuardedChain (gc0 gc6 greg)
open Ern.Concurrency.Corpus.GuardedChainC (lc7 lc8 lc9 lc10 lc11 lcLbls)
open Ern.Concurrency.Traces (L0 q0 q6 s4_steps)
open Ern.MemoryModel.Access.Examples (K0)

/-! ## W-GS -/

/-- `corpus-spec2-m3.md` v6 §2 sexies W-GS, step 1, under the extended rule: `store(z2, T)` by
context 0 without the grant is an `ok` step of the kernel (O8) admitted by `Encap5C`, and excluded
by `PlaceExcl`: the right over `T` holds neither before the store (Spec 1 §65.2) nor in the
resulting state (§65.5) without `guarded`, the only authority with effective `Modify` on `T`. -/
theorem W_GS_1_placeExcl : opStepC KM (.store 4 3) 0 gs5 (.ok gs6) ∧
    Encap5C L0 (gs5, sreg) (.kernel 0 (.store 4 3)) ∧
    ¬ PlaceExcl KM L0 (gs5, sreg, []) (.kernel 0 (.store 4 3)) ∧
    ¬ HasRight5 (gs5, sreg) 0 .modify 3 ∧ ¬ HasRight5 (gs6, sreg) 0 .modify 3 :=
  ⟨W_GS_1_ok, ⟨trivial, trivial, trivial⟩, by decide, by decide, by decide⟩

/-- Twin, `c0 : unlock(e)`: `g₀` released (O3, WC5 C17). -/
def gt8 : SC := gt7.set (releaseEff (gt7.view 0) 6)

/-- The W-GS setup from the initial state, each step admitted by `Encap5R` (Spec 1 §60, §65;
WC5 C4, C13). -/
theorem gs_setup5R : EncapsulatedTrace5R KM L0 (gs0, [], []) setupLbls (gs5, sreg, []) :=
  .cons ⟨⟨(fun e he => by cases he), by decide, trivial⟩, trivial⟩
    (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
  .cons ⟨⟨trivial, trivial, trivial⟩, by decide⟩ (.kernel ⟨by decide, .ok (by decide)⟩) <|
  .cons ⟨⟨trivial, trivial, trivial⟩, trivial⟩ (.newMutex ⟨by decide, by decide, rfl⟩) <|
  .cons ⟨⟨(by decide : ∀ e ∈ sreg, e.Live gs2 → 2 ≠ e.guarded), by decide, trivial⟩, trivial⟩
    (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
  .cons ⟨⟨(by decide : ∀ e ∈ sreg, e.Live gs3 → 0 ≠ e.guarded), by decide, trivial⟩, trivial⟩
    (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
  .cons ⟨⟨trivial, trivial, trivial⟩, trivial⟩ (.spawn ⟨by decide, .ok (by decide)⟩) .nil

/-- `corpus-spec2-m3.md` v6 §2 sexies W-GS, twin under the extended rule, extended by an `unlock`:
from the initial state, the setup, then `acquire(e)`, `store(z2, T)` under `g₀` (the right over
`T` rests on the grant, held by frame 0) and `unlock(e)` by context 0 form an
`EncapsulatedTrace5R`. -/
theorem W_GS_twin_trace5R : EncapsulatedTrace5R KM L0 (gs0, [], [])
    (setupLbls ++ [.acquire 0 0] ++ [.kernel 0 (.store 4 3)] ++ [.unlock 0 0]) (gt8, sreg, []) := by
  have h := gs_setup5R.snoc (lbl := .acquire 0 0) (st'' := (gt6, sregG, []))
    ⟨⟨trivial, trivial, trivial⟩, by decide⟩ (.acquire W_GS_twin_ok.1)
  have h := h.snoc (lbl := .kernel 0 (.store 4 3)) (st'' := (gt7, sregG, []))
    ⟨⟨trivial, trivial, trivial⟩, by decide⟩ (.kernel W_GS_twin_ok.2)
  exact h.snoc (lbl := .unlock 0 0) (st'' := (gt8, sreg, [])) ⟨⟨trivial, trivial, trivial⟩, trivial⟩
    (.unlock ⟨by decide, ⟨3, some 6⟩, 6, rfl, by decide, rfl, by decide, by decide, rfl⟩)

/-! ## The locked trace -/

/-- The locked trace of `Corpus/GuardedChainC.lean` (`lc_trace`) is an `EncapsulatedTrace5R`. -/
theorem lc_trace5R :
    EncapsulatedTrace5R KM L0 (gc0, [], []) lcLbls (lc11, [⟨4, some 7⟩], []) := by
  have h : EncapsulatedTrace5R KM L0 (gc0, [], []) (lcLbls.take 7) (gc6, greg, []) :=
    .cons ⟨⟨(fun e he => by cases he), by decide, trivial⟩, trivial⟩
      (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, by decide⟩ (.kernel ⟨by decide, .ok (by decide)⟩) <|
    .cons ⟨⟨(fun e he => by cases he), by decide, trivial⟩, trivial⟩
      (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, by decide⟩ (.kernel ⟨by decide, .ok (by decide)⟩) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, trivial⟩ (.newMutex ⟨by decide, by decide, rfl⟩) <|
    .cons ⟨⟨(by decide : ∀ e ∈ greg, e.Live Ern.Concurrency.Corpus.GuardedChain.gc4 →
        0 ≠ e.guarded), by decide, trivial⟩, trivial⟩
      (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, trivial⟩ (.spawn ⟨by decide, .ok (by decide)⟩) .nil
  have h := h.snoc (lbl := .acquire 1 0) (st'' := (lc7, [⟨4, some 6⟩], []))
    ⟨⟨trivial, trivial, trivial⟩, by decide⟩
    (.acquire ⟨by decide, ⟨4, none⟩, rfl, by decide, by decide, rfl⟩)
  have h := h.snoc (lbl := .kernel 1 (.read 3 [4])) (st'' := (lc8, [⟨4, some 6⟩], []))
    ⟨⟨trivial, by decide, by decide⟩, trivial⟩ (.kernel ⟨by decide, _, .ok (by decide), rfl⟩)
  have h := h.snoc (lbl := .unlock 1 0) (st'' := (lc9, greg, [])) ⟨⟨trivial, trivial, trivial⟩, trivial⟩
    (.unlock ⟨by decide, ⟨4, some 6⟩, 6, rfl, by decide, rfl, by decide, by decide, rfl⟩)
  have h := h.snoc (lbl := .acquire 0 0) (st'' := (lc10, [⟨4, some 7⟩], []))
    ⟨⟨trivial, trivial, trivial⟩, by decide⟩
    (.acquire ⟨by decide, ⟨4, none⟩, rfl, by decide, by decide, rfl⟩)
  exact h.snoc (lbl := .kernel 0 (.write 3 [4])) (st'' := (lc11, [⟨4, some 7⟩], []))
    ⟨⟨trivial, by decide, by decide⟩, trivial⟩ (.kernel ⟨by decide, _, .ok (by decide), rfl⟩)

/-! ## Legitimate uses -/

/-- `corpus-spec2-m3.md` v6 §1 S2, which is the cycle of `cycle_trace5`: block MX from the initial
state, then `acquire(e)`, `write3(T)` via `g` and `unlock(e)` by context 1, form an
`EncapsulatedTrace5R`. -/
theorem s2_trace5R : EncapsulatedTrace5R KM L0 (x0, [], [])
    [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 3 1), .newMutex 0 3,
     .kernel 0 (.derive 0 [1, 2] .observe), .spawn 0 [4] [], .acquire 1 0,
     .kernel 1 (.write 5 [3]), .unlock 1 0] (x7, regX, []) :=
  .cons ⟨⟨(fun e he => by cases he), by decide, trivial⟩, trivial⟩ (.kernel mx_steps.1) <|
  .cons ⟨⟨trivial, trivial, trivial⟩, by decide⟩ (.kernel mx_steps.2.1) <|
  .cons ⟨⟨trivial, trivial, trivial⟩, trivial⟩ (.newMutex mx_steps.2.2.1) <|
  .cons ⟨⟨(by decide : ∀ e ∈ regX, e.Live x2 → 0 ≠ e.guarded), by decide, trivial⟩, trivial⟩
    (.kernel mx_steps.2.2.2.2.1) <|
  .cons ⟨⟨trivial, trivial, trivial⟩, trivial⟩ (.spawn mx_steps.2.2.2.2.2) <|
  .cons ⟨⟨trivial, trivial, trivial⟩, by decide⟩ (.acquire S2_1_ok) <|
  .cons ⟨⟨trivial, by decide, by decide⟩, trivial⟩ (.kernel S2_2_ok) <|
  .cons ⟨⟨trivial, trivial, trivial⟩, trivial⟩ (.unlock S2_3_ok) .nil

/-- `corpus-spec2-m3.md` v6 §1 S4: from the initial state of `q0`, the writes, the `alloc`, the
by-value composite moving `v` into `d` and the exit of the creating frame form an
`EncapsulatedTrace5R` (no mutex is registered). -/
theorem s4_trace5R : EncapsulatedTrace5R K0 L0 (q0, [], [])
    [.kernel 0 (.enter [] [(none, 0), (none, 0)]), .kernel 0 (.write 1 [1]),
     .kernel 0 (.write 2 [2]), .kernel 0 (.alloc 2 1 [(none, 0)]),
     .spawnVal 0 [] [(none, 0)] [(1, 4)], .kernel 0 .exit] (q6, [], []) :=
  .cons ⟨⟨trivial, trivial, trivial⟩, trivial⟩ (.kernel s4_steps.1) <|
  .cons ⟨⟨trivial, by decide, by decide⟩, trivial⟩ (.kernel s4_steps.2.1) <|
  .cons ⟨⟨trivial, by decide, by decide⟩, trivial⟩ (.kernel s4_steps.2.2.1) <|
  .cons ⟨⟨trivial, trivial, trivial⟩, by decide⟩ (.kernel s4_steps.2.2.2.1) <|
  .cons ⟨⟨⟨fun _ h => (by cases h), trivial⟩, trivial, trivial⟩, by decide⟩
    (.spawnVal s4_steps.2.2.2.2.1) <|
  .cons ⟨⟨trivial, trivial, trivial⟩, trivial⟩ (.kernel s4_steps.2.2.2.2.2) .nil

/-- `corpus-spec2-m3.md` v6 §1 S3 up to step 3 (the labels of `s3_realized`): block AR from the
initial state, then `acquire(e2)` and `issue(arena, R1, d1)` by context 1, form an
`EncapsulatedTrace5R`; the `MetaRight` over `AV` (Spec 1 §77.1) rests on `g2`. -/
theorem s3_trace5R : EncapsulatedTrace5R KA L0 (a0, [], [])
    [.kernel 0 (.derive 2 [5, 6] .modify), .kernel 0 (.store 4 3), .newArena 0 4 4,
     .kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 5 1), .newMutex 0 5,
     .kernel 0 (.derive 0 [1, 2] .observe), .spawn 0 [6] [(none, 0)], .acquire 1 0,
     .issue 1 0 [5] 8] (a8, regA8, arA1) := by
  have hn : NewMutexOk KA L0 arA a4 [] 0 5 (a4, regA) := ⟨by decide, by decide, rfl⟩
  have ha : NewArenaStepC a2 [] [] 0 4 4 (.ok (a2, arA)) := ⟨by decide, .ok (by decide)⟩
  exact .cons ⟨⟨(fun e he => by cases he), by decide, trivial⟩, trivial⟩
      (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, by decide⟩ (.kernel ⟨by decide, .ok (by decide)⟩) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, trivial⟩ (.newArena ha) <|
    .cons ⟨⟨(fun e he => by cases he), by decide, trivial⟩, trivial⟩
      (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, by decide⟩ (.kernel ⟨by decide, .ok (by decide)⟩) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, trivial⟩ (.newMutex hn) <|
    .cons ⟨⟨(by decide : ∀ e ∈ regA, e.Live a4 → 0 ≠ e.guarded), by decide, trivial⟩, trivial⟩
      (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, trivial⟩ (.spawn ⟨by decide, .ok (by decide)⟩) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, by decide⟩ (.acquire S3_2_ok) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, by decide⟩ (.issue S3_3_ok) .nil

/-- `corpus-spec2-m3.md` v6 §1 S10: block MX up to `MX₃` from the initial state, `acquire(e)` by
context 0, `derive(root_M, Modify)`, `enterFrame f1` yielding `m` with the local `M′`, then, with
the grant active, `transfer(M, M′)` of the whole mutex and the transfer back `transfer(M′, M)`, form
an `EncapsulatedTrace5R`: the rights over `M` and `M′` rest on `m` and `root_M′`, held by `f1`. -/
theorem s10_trace5R : EncapsulatedTrace5R KM L0 (x0, [], [])
    [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 3 1), .newMutex 0 3, .acquire 0 0,
     .kernel 0 (.derive 0 [1, 2] .modify),
     .kernel 0 (.enter [5] [(none, 0), (some 7, 0), (some 7, 0)]),
     .kernel 0 (.transfer 0 7), .kernel 0 (.transfer 7 0)] (r5, [⟨3, some 4⟩], []) :=
  .cons ⟨⟨(fun e he => by cases he), by decide, trivial⟩, trivial⟩ (.kernel mx_steps.1) <|
  .cons ⟨⟨trivial, trivial, trivial⟩, by decide⟩ (.kernel mx_steps.2.1) <|
  .cons ⟨⟨trivial, trivial, trivial⟩, trivial⟩ (.newMutex mx_steps.2.2.1) <|
  .cons ⟨⟨trivial, trivial, trivial⟩, by decide⟩ (.acquire s10_setup.1) <|
  .cons ⟨⟨(by decide : ∀ e ∈ ([⟨3, some 4⟩] : SyncReg), e.Live r1 → 0 ≠ e.guarded), by decide,
      trivial⟩, trivial⟩ (.kernel s10_setup.2.1) <|
  .cons ⟨⟨trivial, trivial, trivial⟩, trivial⟩ (.kernel s10_setup.2.2) <|
  .cons ⟨⟨S10_1_ok.2.1, trivial, trivial⟩, by decide⟩ (.kernel S10_1_ok.1) <|
  .cons ⟨⟨S10_2_ok.2, trivial, trivial⟩, by decide⟩ (.kernel S10_2_ok.1) .nil

end Ern.Concurrency.Corpus.PlaceExclWitness
