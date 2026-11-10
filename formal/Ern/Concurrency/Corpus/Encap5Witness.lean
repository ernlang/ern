import Ern.Concurrency.Encap5
import Ern.Concurrency.Corpus.GuardedRead

/-!
# Witnesses of `Encap5`

Brief of milestone 4, task 3: the steps that `GuardedExcl` and `CtlExcl` (WC5 C22.4) exclude while
the kernel accepts them and `Encap` admits them, and the non-vacuity of `EncapsulatedTrace5`, on
the states of block MX (`corpus-spec2-m3.md` v4 §0), by `decide`.
-/

namespace Ern.Concurrency.Corpus.Encap5Witness

open Ern.MemoryModel.Access Ern.Concurrency Ern.Concurrency.Corpus
open Ern.Concurrency.Corpus.GuardedRead
open Ern.Concurrency.Traces (L0)

/-- W-GR, step 1 (`corpus-spec2-m3.md` v4 §2 ter): `read3(T)` with `access = guarded` by context 1
from `MX₄` is an `ok` kernel step (O9) admitted by `Encap`, and `GuardedExcl` excludes it. -/
theorem W_GR_1_guardedExcl : opStepC KM (.read 3 [3]) 1 x4 (.ok gr1) ∧
    Encap L0 (x4, regX) (.kernel 1 (.read 3 [3])) ∧
    ¬ GuardedExcl (x4, regX) (.kernel 1 (.read 3 [3])) :=
  ⟨W_GR_1_ok, trivial, by decide⟩

/-- S12 (`corpus-spec2-m3.md` v4 §1): `write3(lock)` via `root_M` by context 0 from `MX₃` is an `ok`
kernel step (O10) admitted by `Encap`, and `CtlExcl` (WC5 C22.4) excludes it. -/
theorem S12_1_ctlExcl : opStepC KM (.write 0 [2]) 0 x2 (.ok x2w) ∧
    Encap L0 (x2, regX) (.kernel 0 (.write 0 [2])) ∧
    ¬ CtlExcl L0 (x2, regX) (.kernel 0 (.write 0 [2])) :=
  ⟨S12_1_ok.1, S12_1_ok.2, by decide⟩

/-- The witness of `CrossContextConflictOnlyShared` of milestone 3 (`corpus-spec2-m3.md` v4 §3):
`read3(lock)` via `o1` by context 1 from `MX₄` is an `ok` kernel step (O9) admitted by `Encap`, and
`CtlExcl` (WC5 C22.4: ordinary `read3` of `ControlOf(entry)`) excludes it. -/
theorem read_lock_ctlExcl : opStepC KM (.read 4 [2]) 1 x4 (.ok (x4.set (x4.view 1))) ∧
    Encap L0 (x4, regX) (.kernel 1 (.read 4 [2])) ∧
    ¬ CtlExcl L0 (x4, regX) (.kernel 1 (.read 4 [2])) :=
  ⟨⟨by decide, _, .ok (by decide), rfl⟩, trivial, by decide⟩

/-- Non-vacuity of `EncapsulatedTrace5`: block MX from the initial state, then the cycle `acquire`,
`write3(T)` via the grant, `unlock` by context 1 (`corpus-spec2-m3.md` v4 §1 S2), is an
`EncapsulatedTrace5`. -/
theorem cycle_trace5 : EncapsulatedTrace5 KM L0 (x0, [], [])
    [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 3 1), .newMutex 0 3,
     .kernel 0 (.derive 0 [1, 2] .observe), .spawn 0 [4] [], .acquire 1 0,
     .kernel 1 (.write 5 [3]), .unlock 1 0] (x7, regX, []) :=
  .cons ⟨(fun e he => by cases he), (fun e he => by cases he), trivial⟩ (.kernel mx_steps.1) <|
  .cons ⟨trivial, trivial, trivial⟩ (.kernel mx_steps.2.1) <|
  .cons ⟨trivial, trivial, trivial⟩ (.newMutex mx_steps.2.2.1) <|
  .cons ⟨(by decide : ∀ e ∈ regX, e.Live x2 → 0 ≠ e.guarded),
      (by decide : ∀ e ∈ regX, e.Live x2 → 0 ≠ e.guarded), trivial⟩
    (.kernel mx_steps.2.2.2.2.1) <|
  .cons ⟨trivial, trivial, trivial⟩ (.spawn mx_steps.2.2.2.2.2) <|
  .cons ⟨trivial, trivial, trivial⟩ (.acquire S2_1_ok) <|
  .cons ⟨trivial, by decide, by decide⟩ (.kernel S2_2_ok) <|
  .cons ⟨trivial, trivial, trivial⟩ (.unlock S2_3_ok) .nil

end Ern.Concurrency.Corpus.Encap5Witness
