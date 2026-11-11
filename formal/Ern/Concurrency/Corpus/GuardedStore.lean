import Ern.Concurrency.Encap5C
import Ern.Concurrency.Corpus.GuardedChain

/-!
# Corpus v6, witness W-GS

`corpus-spec2-m3.md` v6 §2 sexies, W-GS: a write into the protected data without the lock, by a
right over a place. From `MX₃` (`grant = none`) with a local `Y2` of the base frame, the setup
derives `z2 := derive(root_Y2, Modify)`, shares only the controller by
`o := derive(root_M, Observe, {lock})` and spawns `c1` yielding `o`. One theorem per verdict,
written from `corpus-spec2-m3.md` v6 §2 sexies, preconditions by `decide`, contract `KM`.

Statics: those of `Corpus/GuardedChain.lean` (`zst`), place `4` being `Y2`. Root authorities: `0` of
`M` (frame 0), `1` of `T` (held by `M`), `2` of `Y2` (frame 0).
-/

namespace Ern.Concurrency.Corpus.GuardedStore

open Ern.MemoryModel.Access Ern.Concurrency Ern.Concurrency.Corpus
open Ern.Concurrency.Corpus.GuardedChain (zst)
open Ern.Concurrency.Traces (L0)

/-- Initial state (Spec 1 §47). -/
def gs0 : SC := SC.ofS3 (S3.init zst)
/-- `guarded := derive(root_T, Modify, footprint(T))`, authority 3 (O1). -/
def gs1 : SC := gs0.set (deriveEff (gs0.view 0) 1 [3] .modify)
/-- `store(guarded, slot)` (O8). -/
def gs2 : SC := storeEffC gs1 0 3 1
/-- The registry after `newMutex(guarded)` (WC5 C13): `MX₃`. -/
def sreg : SyncReg := [⟨3, none⟩]
/-- `z2 := derive(root_Y2, Modify)`, authority 4 (O1). -/
def gs3 : SC := gs2.set (deriveEff (gs2.view 0) 2 [4] .modify)
/-- `o := derive(root_M, Observe, {lock})`, authority 5 (O1). -/
def gs4 : SC := gs3.set (deriveEff (gs3.view 0) 0 [2] .observe)
/-- `spawn c1` yielding `o` (WC5 C4): context 1, initial frame 1. -/
def gs5 : SC := spawnEff gs4 0 [5] []
/-- Step 1, `c0 : store(z2, T)` (O8): `z2` is held by `T`. -/
def gs6 : SC := storeEffC gs5 0 4 3
/-- Step 2, `c1 : acquire(e)`: grant `g₁`, authority 6, held by frame 1 (WC5 C16). -/
def gs7 : SC := deriveSyncEff gs6 1 3
/-- The registry with the grant recorded (WC5 C16). -/
def sregG : SyncReg := [⟨3, some 6⟩]
/-- Step 3, `c1 : read3(T)` via `g₁` (O9): the state is unchanged. -/
def gs8 : SC := gs7.set (gs7.view 1)
/-- Twin, `c0 : acquire(e)`: grant `g₀`, authority 6, held by frame 0 (WC5 C16). -/
def gt6 : SC := deriveSyncEff gs5 0 3
/-- Twin, `c0 : store(z2, T)` under `g₀` (O8). -/
def gt7 : SC := storeEffC gt6 0 4 3

/-- The labels of the setup. -/
def setupLbls : List Label :=
  [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 3 1), .newMutex 0 3,
   .kernel 0 (.derive 2 [4] .modify), .kernel 0 (.derive 0 [2] .observe), .spawn 0 [5] []]

/-- The setup of `corpus-spec2-m3.md` v6 §2 sexies from the initial state: each step is an `ok`
step admitted by `Encap5C` (Spec 1 §60, §65; WC5 C4, C13). -/
theorem gs_setup : EncapsulatedTrace5C KM L0 (gs0, [], []) setupLbls (gs5, sreg, []) :=
  .cons ⟨(fun e he => by cases he), by decide, trivial⟩
    (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
  .cons ⟨trivial, trivial, trivial⟩ (.kernel ⟨by decide, .ok (by decide)⟩) <|
  .cons ⟨trivial, trivial, trivial⟩ (.newMutex ⟨by decide, by decide, rfl⟩) <|
  .cons ⟨(by decide : ∀ e ∈ sreg, e.Live gs2 → 2 ≠ e.guarded), by decide, trivial⟩
    (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
  .cons ⟨(by decide : ∀ e ∈ sreg, e.Live gs3 → 0 ≠ e.guarded), by decide, trivial⟩
    (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
  .cons ⟨trivial, trivial, trivial⟩ (.spawn ⟨by decide, .ok (by decide)⟩) .nil

/-- `corpus-spec2-m3.md` v6 §2 sexies W-GS, step 1, `ok` (O8; O8.2 through `guarded` held by
`slot`, on whose leaves `root_M` is exercisable in `Modify` with effective mode `Modify`, Spec 1
§43, third clause): `store(z2, T)` by context 0 without the grant. -/
theorem W_GS_1_ok : opStepC KM (.store 4 3) 0 gs5 (.ok gs6) := ⟨by decide, .ok (by decide)⟩

/-- `corpus-spec2-m3.md` v6 §2 sexies W-GS, step 2, `ok` (WC5 C14.1–C14.3, C15): `acquire(e)` by
context 1, whose `o` gives the controller access; `g₁` is held by frame 1. -/
theorem W_GS_2_ok : AcquireOk KM L0 gs6 sreg 1 0 (gs7, sregG) :=
  ⟨by decide, ⟨3, none⟩, rfl, by decide, by decide, rfl⟩

/-- `corpus-spec2-m3.md` v6 §2 sexies W-GS, step 3, `ok` (O9): `read3(T)` via `g₁` by context 1. -/
theorem W_GS_3_ok : opStepC KM (.read 6 [3]) 1 gs7 (.ok gs8) :=
  ⟨by decide, _, .ok (by decide), rfl⟩

/-- The labels of the setup and of steps 1 to 3. -/
def gsLbls : List Label :=
  setupLbls ++ [.kernel 0 (.store 4 3), .acquire 1 0, .kernel 1 (.read 6 [3])]

/-- `corpus-spec2-m3.md` v6 §2 sexies W-GS, "Encapsulation": from the initial state, the setup and
steps 1 to 3 form an `EncapsulatedTrace5C`; `store` has no exercised authority argument and
`ChainExcl` does not read its right over `T`. -/
theorem W_GS_encap : EncapsulatedTrace5C KM L0 (gs0, [], []) gsLbls (gs8, sregG, []) := by
  have h := gs_setup.snoc (lbl := .kernel 0 (.store 4 3)) (st'' := (gs6, sreg, []))
    ⟨trivial, trivial, trivial⟩ (.kernel W_GS_1_ok)
  have h := h.snoc (lbl := .acquire 1 0) (st'' := (gs7, sregG, [])) ⟨trivial, trivial, trivial⟩
    (.acquire W_GS_2_ok)
  exact h.snoc (lbl := .kernel 1 (.read 6 [3])) (st'' := (gs8, sregG, []))
    ⟨trivial, by decide, by decide⟩ (.kernel W_GS_3_ok)

/-- `corpus-spec2-m3.md` v6 §2 sexies W-GS, twin, `ok` then `ok` (WC5 C14.1–C14.3, C15; O8, the
right over `T` resting on the grant): `acquire(e)` by context 0, then `store(z2, T)` by context 0
under `g₀`. -/
theorem W_GS_twin_ok : AcquireOk KM L0 gs5 sreg 0 0 (gt6, sregG) ∧
    opStepC KM (.store 4 3) 0 gt6 (.ok gt7) :=
  ⟨⟨by decide, ⟨3, none⟩, rfl, by decide, by decide, rfl⟩, ⟨by decide, .ok (by decide)⟩⟩

end Ern.Concurrency.Corpus.GuardedStore
