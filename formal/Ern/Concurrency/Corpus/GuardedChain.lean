import Ern.Concurrency.CapPreserve
import Ern.Concurrency.Corpus.MX

/-!
# Counterexample: exercise through `guarded` in a holder chain

Brief of milestone 4, task 4. `GuardedExcl` excludes the steps whose authority argument is a live
`guarded`, while the third clause of Spec 1 §43 is recursive along the holder chain: an authority
`z` stored in the protected `T` is exercisable by any frame that can exercise `guarded`, held by
`slot`, in `Observe`. The trace below is built from the initial state of Spec 1 §47 with the
contract `KM` of `corpus-spec2-m3.md` v4 §0; each step is an `ok` step admitted by `Encap5`, by
`decide`. It refutes `cap5_sound` and `handoff_loss_exists`.

Statics: `0` the mutex value `M` with fields `1` (`slot`, `Uninit`) and `2` (`lock`, `Init`), `3`
the protected root `T` (`Init`) owned by `M`, `4` a local `Y` (`Init`) of the base frame. Root
authorities: `0` of `M` (frame 0), `1` of `T` (held by `M`), `2` of `Y` (frame 0).
-/

namespace Ern.Concurrency.Corpus.GuardedChain

open Ern.MemoryModel.Access Ern.Concurrency Ern.Concurrency.Corpus
open Ern.Concurrency.Traces (L0)

/-- Statics (Spec 1 §47): block MX of `corpus-spec2-m3.md` v4 §0 without `M′`, and a local `Y`. -/
def zst : Statics :=
  [((none, none, 0), false), ((some 0, none, 0), false), ((some 0, none, 0), true),
   ((none, some 0, 0), true), ((none, none, 0), true)]

/-- The statics are well formed (Spec 1 §47). -/
theorem zst_ok : StaticsOK zst := by decide

/-- Initial state (Spec 1 §47). -/
def gc0 : SC := SC.ofS3 (S3.init zst)
/-- `z := derive(root_Y, Modify)`, authority 3 (O1). -/
def gc1 : SC := gc0.set (deriveEff (gc0.view 0) 2 [4] .modify)
/-- `store(z, T)` (O8): `z` is held by `T`. -/
def gc2 : SC := storeEffC gc1 0 3 3
/-- `guarded := derive(root_T, Modify, footprint(T))`, authority 4 (O1). -/
def gc3 : SC := gc2.set (deriveEff (gc2.view 0) 1 [3] .modify)
/-- `store(guarded, slot)` (O8). -/
def gc4 : SC := storeEffC gc3 0 4 1
/-- The registry after `newMutex(guarded)` (WC4 C13). -/
def greg : SyncReg := [⟨4, none⟩]
/-- `o1 := derive(root_M, Observe, {slot, lock})`, authority 5 (O1). -/
def gc5 : SC := gc4.set (deriveEff (gc4.view 0) 0 [1, 2] .observe)
/-- `spawn c1` yielding `o1` (WC4 C4): context 1, initial frame 1. -/
def gc6 : SC := spawnEff gc5 0 [5] []
/-- `c1 : read3(Y)` via `z` (O9): the state is unchanged. -/
def gc7 : SC := gc6.set (gc6.view 1)
/-- `c0 : acquire(e)`: grant `g`, authority 6, held by frame 0 (WC4 C16). -/
def gc8 : SC := deriveSyncEff gc7 0 4
/-- The registry with the grant recorded (WC4 C16). -/
def gregG : SyncReg := [⟨4, some 6⟩]
/-- `c0 : write3(Y)` via `z` (O10). -/
def gc9 : SC := gc8.set (write3Eff (gc8.view 0) [4])

/-- The labels of the trace. -/
def glbls : List Label :=
  [.kernel 0 (.derive 2 [4] .modify), .kernel 0 (.store 3 3), .kernel 0 (.derive 1 [3] .modify),
   .kernel 0 (.store 4 1), .newMutex 0 4, .kernel 0 (.derive 0 [1, 2] .observe), .spawn 0 [5] [],
   .kernel 1 (.read 3 [4]), .acquire 0 0, .kernel 0 (.write 3 [4])]

/-- The setup up to `MX₄` with `z` stored in `T`: each step is an `ok` step admitted by `Encap5`
(Spec 1 §60, §65; WC4 C4, C13). -/
theorem gc_setup : EncapsulatedTrace5 KM L0 (gc0, [], []) (glbls.take 7) (gc6, greg, []) :=
  .cons ⟨(fun e he => by cases he), (fun e he => by cases he), trivial⟩
    (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
  .cons ⟨trivial, trivial, trivial⟩ (.kernel ⟨by decide, .ok (by decide)⟩) <|
  .cons ⟨(fun e he => by cases he), (fun e he => by cases he), trivial⟩
    (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
  .cons ⟨trivial, trivial, trivial⟩ (.kernel ⟨by decide, .ok (by decide)⟩) <|
  .cons ⟨trivial, trivial, trivial⟩ (.newMutex ⟨by decide, by decide, rfl⟩) <|
  .cons ⟨(by decide : ∀ e ∈ greg, e.Live gc4 → 0 ≠ e.guarded),
      (by decide : ∀ e ∈ greg, e.Live gc4 → 0 ≠ e.guarded), trivial⟩
    (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
  .cons ⟨trivial, trivial, trivial⟩ (.spawn ⟨by decide, .ok (by decide)⟩) .nil

/-- Step 7: `read3(Y)` via `z` by context 1 is an `ok` step (O9; Spec 1 §43, third clause, along
`z` held by `T`, `guarded` held by `slot`, `o1` held by frame 1) admitted by `Encap5`: the authority
argument `z` is not `guarded`, and `Y` is not the controller. -/
theorem gc_read : Encap5 L0 (gc6, greg) (.kernel 1 (.read 3 [4])) ∧
    opStepC KM (.read 3 [4]) 1 gc6 (.ok gc7) :=
  ⟨⟨trivial, by decide, by decide⟩, ⟨by decide, _, .ok (by decide), rfl⟩⟩

/-- At the read, `cap5` of context 1 on `Y` is `none` (only `guarded` attributes `z` to context 1),
while `cap` of context 1 on `Y` is `Observe` (WC5 C43). -/
theorem gc_cap5_none : cap5 gc6 greg 1 4 = none ∧ cap gc6 1 4 = some .observe := by decide

/-- The whole trace: `acquire(e)` and `write3(Y)` via `z` by context 0 (WC4 C16; O10, through the
grant `g`, which has effective `Modify` on `T`) are `ok` steps admitted by `Encap5`. -/
theorem gc_trace : EncapsulatedTrace5 KM L0 (gc0, [], []) glbls (gc9, gregG, []) := by
  have h := gc_setup.snoc gc_read.1 (.kernel gc_read.2)
  have h := h.snoc (lbl := .acquire 0 0) (st'' := (gc8, gregG, [])) ⟨trivial, trivial, trivial⟩
    (.acquire ⟨by decide, ⟨4, none⟩, rfl, by decide, by decide, rfl⟩)
  exact h.snoc (lbl := .kernel 0 (.write 3 [4])) (st'' := (gc9, gregG, []))
    ⟨trivial, by decide, by decide⟩ (.kernel ⟨by decide, _, .ok (by decide), rfl⟩)

/-- `cap5_sound` is false (brief of milestone 4, task 4): with the corpus contract `KM`, which
satisfies `DDSound` (`ddKC`), the access `read3(Y)` via `z` of context 1 (`gc_read`) is admitted by
`Encap5` from a state reached by an `EncapsulatedTrace5` from the initial state, and `cap5` of
context 1 on `Y` is `none` (`gc_cap5_none`). -/
theorem cap5_sound_false : ¬ ∀ k L, DDSound k → Cap5Sound k L := by
  intro h
  have := (h KM L0 (ddKC [2]) zst (glbls.take 7) (gc6, greg, []) 1 3 [4] gc7 zst_ok
    gc_setup).1 gc_read.1 gc_read.2 4 (List.mem_singleton_self _)
  rw [gc_cap5_none.1] at this
  exact this

/-- `handoff_loss_exists` is false (brief of milestone 4, task 4): on `gc_trace`, context 1
accesses `Y` at step 7 (`read3`), context 0 accesses `Y` at step 9 requiring `Modify` (`write3`),
and the only step between them, step 8 (`acquire(e)`), is a step of context 0. -/
theorem handoff_loss_exists_false : ¬ ∀ k L, DDSound k → HandoffLossExists k L := by
  intro h
  obtain ⟨σ, h0, hr, -⟩ := run5_of_trace gc_trace
  obtain ⟨k', hk, h7, h9, hctx, -⟩ := h KM L0 (ddKC [2]) zst σ glbls zst_ok h0 hr 7 9 0 1 4
    .observe .modify (by decide) (by decide) (by decide)
    (by show Label.Access (.kernel 1 (.read 3 [4])) 1 4 .observe; exact ⟨rfl, by decide, rfl⟩)
    (by show Label.Access (.kernel 0 (.write 3 [4])) 0 4 .modify; exact ⟨rfl, by decide, rfl⟩)
    (Or.inr rfl)
  obtain rfl : k' = 8 := by omega
  have h8 : glbls[8]'hk = .acquire 0 0 := rfl
  rw [h8] at hctx
  exact absurd hctx (by decide)

end Ern.Concurrency.Corpus.GuardedChain
