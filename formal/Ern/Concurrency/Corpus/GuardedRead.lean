import Ern.Concurrency.Corpus.MX

/-!
# Corpus v4, witness W-GR

`corpus-spec2-m3.md` v4 §2 ter, W-GR: from `MX₄` (`grant = none`, the leaves of `T` `Init`), a
trace of the authority machine alone. One theorem per verdict, written from `corpus-spec2-m3.md`
v4 §2 ter, preconditions by `decide`, contract `KM` and states of block MX
(`Ern.Concurrency.Corpus`). Only the verdicts of the steps are stated here.
-/

namespace Ern.Concurrency.Corpus.GuardedRead

open Ern.MemoryModel.Access Ern.Concurrency Ern.Concurrency.Corpus
open Ern.Concurrency.Traces (L0)

/-- `c1 : read3(T)` with `access = guarded` (O9): the state is unchanged. -/
def gr1 : SC := x4.set (x4.view 1)
/-- `c0 : acquire(e)`: grant `g`, authority 5, held by frame 0 (WC4 C16). -/
def gr2 : SC := deriveSyncEff gr1 0 3
/-- `c0 : write3(T)` via `g` (O10). -/
def gr3 : SC := gr2.set (write3Eff (gr2.view 0) [3])

/-- `corpus-spec2-m3.md` v4 §2 ter W-GR, step 1, `ok` (O9.1; O9.2 by the third clause of Spec 1
§43): from `MX₄`, `read3(T)` with `access = guarded` by context 1. -/
theorem W_GR_1_ok : opStepC KM (.read 3 [3]) 1 x4 (.ok gr1) := ⟨by decide, _, .ok (by decide), rfl⟩

/-- `corpus-spec2-m3.md` v4 §2 ter W-GR, step 2, `ok` (WC4 C14.1–C14.3, C15): `acquire(e)` by
context 0; `g` is held by frame 0. -/
theorem W_GR_2_ok : AcquireOk KM L0 gr1 regX 0 0 (gr2, regG) :=
  ⟨by decide, ⟨3, none⟩, rfl, by decide, by decide, rfl⟩

/-- `corpus-spec2-m3.md` v4 §2 ter W-GR, step 3, `ok` (O10.1): `write3(T)` via `g` by context 0. -/
theorem W_GR_3_ok : opStepC KM (.write 5 [3]) 0 gr2 (.ok gr3) :=
  ⟨by decide, _, .ok (by decide), rfl⟩

/-- `corpus-spec2-m3.md` v4 §2 ter W-GR, negative, `reject` (O9.2: the effective mode of
`guarded` is absent, Spec 1 §43.3): `read3(T)` with `access = guarded` by context 1 while `g` is
active. -/
theorem W_GR_4_reject : opStepC KM (.read 3 [3]) 1 gr2 .reject ∧ effective gr2.flat 3 3 = none :=
  ⟨⟨by decide, _, .reject (by decide), rfl⟩, by decide⟩

/-- `corpus-spec2-m3.md` v4 §2 ter W-GR, "Encapsulation": steps 1 to 3 continue the
`EncapsulatedTrace` of `MX₄` from the initial state (WC4 C22, C23). -/
theorem w_gr_trace : EncapsulatedTrace KM L0 (x0, [], [])
    [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 3 1), .newMutex 0 3,
     .kernel 0 (.derive 0 [1, 2] .observe), .spawn 0 [4] [], .kernel 1 (.read 3 [3]),
     .acquire 0 0, .kernel 0 (.write 5 [3])] (gr3, regG, []) := by
  have h := mx4_trace.snoc (lbl := .kernel 1 (.read 3 [3])) (st' := (gr1, regX, [])) trivial
    (.kernel W_GR_1_ok)
  have h := h.snoc (lbl := .acquire 0 0) (st' := (gr2, regG, [])) trivial (.acquire W_GR_2_ok)
  exact h.snoc (lbl := .kernel 0 (.write 5 [3])) (st' := (gr3, regG, [])) trivial
    (.kernel W_GR_3_ok)

end Ern.Concurrency.Corpus.GuardedRead
