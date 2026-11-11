import Ern.Concurrency.Encap5C
import Ern.Concurrency.Corpus.GuardedChain

/-!
# Witnesses of the corrected exclusion `ChainExcl`

Test of `ChainExcl` (`Ern.Concurrency.Encap5C`), the correction of `GuardedExcl` proposed in
`formal/reports/spec2-m4-handoff.md`, on the counterexample of `Corpus/GuardedChain.lean` and on
W-GR (`corpus-spec2-m3.md` v4 §2 ter), by `decide`: the reads through `guarded` are excluded; the
same access to `Y` made by context 1 while it holds the grant is admitted, and the loss marker is
its own `unlock` (WC5 C45).
-/

namespace Ern.Concurrency.Corpus.GuardedChainC

open Ern.MemoryModel.Access Ern.Concurrency Ern.Concurrency.Corpus
open Ern.Concurrency.Corpus.GuardedChain
open Ern.Concurrency.Traces (L0)

/-- `ChainExcl` excludes the read of the counterexample (`gc_read`): `z` is exercisable by context
1 only through `guarded` (Spec 1 §43, third clause). -/
theorem gc_read_excluded : ¬ ChainExcl (gc6, greg) (.kernel 1 (.read 3 [4])) := by decide

/-- `ChainExcl` excludes step 1 of W-GR (`corpus-spec2-m3.md` v4 §2 ter): `read3(T)` with
`access = guarded` by context 1 from `MX₄`. -/
theorem W_GR_1_excluded : ¬ ChainExcl (x4, regX) (.kernel 1 (.read 3 [3])) := by decide

/-- `c1 : acquire(e)`: grant `g₁`, authority 6, held by frame 1 (WC4 C16). -/
def lc7 : SC := deriveSyncEff gc6 1 4
/-- `c1 : read3(Y)` via `z` (O9): the state is unchanged. -/
def lc8 : SC := lc7.set (lc7.view 1)
/-- `c1 : unlock(e)`: `g₁` released (O3, WC4 C17). -/
def lc9 : SC := lc8.set (releaseEff (lc8.view 1) 6)
/-- `c0 : acquire(e)`: grant `g₂`, authority 7, held by frame 0 (WC4 C16). -/
def lc10 : SC := deriveSyncEff lc9 0 4
/-- `c0 : write3(Y)` via `z` (O10). -/
def lc11 : SC := lc10.set (write3Eff (lc10.view 0) [4])

/-- The labels of the locked trace. -/
def lcLbls : List Label :=
  [.kernel 0 (.derive 2 [4] .modify), .kernel 0 (.store 3 3), .kernel 0 (.derive 1 [3] .modify),
   .kernel 0 (.store 4 1), .newMutex 0 4, .kernel 0 (.derive 0 [1, 2] .observe), .spawn 0 [5] [],
   .acquire 1 0, .kernel 1 (.read 3 [4]), .unlock 1 0, .acquire 0 0, .kernel 0 (.write 3 [4])]

/-- The counterexample with the lock: from the initial state, the setup of `gc_setup`, then
`c1 : acquire(e)`, `c1 : read3(Y)` via `z` (exercisable through `g₁`, held by the current frame of
context 1), `c1 : unlock(e)`, `c0 : acquire(e)` and `c0 : write3(Y)` via `z`. Each step is an `ok`
step admitted by `Encap5C`. -/
theorem lc_trace : EncapsulatedTrace5C KM L0 (gc0, [], []) lcLbls (lc11, [⟨4, some 7⟩], []) := by
  have h : EncapsulatedTrace5C KM L0 (gc0, [], []) (lcLbls.take 7) (gc6, greg, []) :=
    .cons ⟨(fun e he => by cases he), by decide, trivial⟩
      (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons ⟨trivial, trivial, trivial⟩ (.kernel ⟨by decide, .ok (by decide)⟩) <|
    .cons ⟨(fun e he => by cases he), by decide, trivial⟩
      (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons ⟨trivial, trivial, trivial⟩ (.kernel ⟨by decide, .ok (by decide)⟩) <|
    .cons ⟨trivial, trivial, trivial⟩ (.newMutex ⟨by decide, by decide, rfl⟩) <|
    .cons ⟨(by decide : ∀ e ∈ greg, e.Live gc4 → 0 ≠ e.guarded), by decide, trivial⟩
      (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons ⟨trivial, trivial, trivial⟩ (.spawn ⟨by decide, .ok (by decide)⟩) .nil
  have h := h.snoc (lbl := .acquire 1 0) (st'' := (lc7, [⟨4, some 6⟩], []))
    ⟨trivial, trivial, trivial⟩ (.acquire ⟨by decide, ⟨4, none⟩, rfl, by decide, by decide, rfl⟩)
  have h := h.snoc (lbl := .kernel 1 (.read 3 [4])) (st'' := (lc8, [⟨4, some 6⟩], []))
    ⟨trivial, by decide, by decide⟩ (.kernel ⟨by decide, _, .ok (by decide), rfl⟩)
  have h := h.snoc (lbl := .unlock 1 0) (st'' := (lc9, greg, [])) ⟨trivial, trivial, trivial⟩
    (.unlock ⟨by decide, ⟨4, some 6⟩, 6, rfl, by decide, rfl, by decide, by decide, rfl⟩)
  have h := h.snoc (lbl := .acquire 0 0) (st'' := (lc10, [⟨4, some 7⟩], []))
    ⟨trivial, trivial, trivial⟩ (.acquire ⟨by decide, ⟨4, none⟩, rfl, by decide, by decide, rfl⟩)
  exact h.snoc (lbl := .kernel 0 (.write 3 [4])) (st'' := (lc11, [⟨4, some 7⟩], []))
    ⟨trivial, by decide, by decide⟩ (.kernel ⟨by decide, _, .ok (by decide), rfl⟩)

/-- `cap5` of contexts 0 and 1 on `Y` along the locked trace, from `gc6` to `lc11`: context 1
holds `Modify` from its `acquire` to its `unlock`, the loss marker of WC5 C45 between its read and
the write of context 0 (`handoff_loss_exists_C`), a step of context 1. -/
theorem lc_cap5 :
    [(gc6, greg), (lc7, [⟨4, some 6⟩]), (lc8, [⟨4, some 6⟩]), (lc9, greg), (lc10, [⟨4, some 7⟩]),
      (lc11, [⟨4, some 7⟩])].map
        (fun (st : SC × SyncReg) => [cap5 st.1 st.2 0 4, cap5 st.1 st.2 1 4]) =
    [[none, none], [none, some .modify], [none, some .modify], [none, none], [some .modify, none],
     [some .modify, none]] := by decide

end Ern.Concurrency.Corpus.GuardedChainC
