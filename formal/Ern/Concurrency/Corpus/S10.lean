import Ern.Concurrency.Corpus.MX

/-!
# Corpus of milestone 3, case S10

`corpus-spec2-m3.md` §1 S10: from `MX₃`, context 0 acquires the grant `g` (held by frame 0), enters
`f1` yielding `m := derive(root_M, Modify)` with a local `M′` of the shape of `M`, and in `f1`
transfers `M` into `M′`. The corpus expects `reject` (O4.7). In the model the step is `ok`
(`S10_1_ok`): the re-indexed §63.7 (`TransferPreC.anchorOrderHeld`) reads `AnchorOrderHeld` on the
moved authorities held by places, and `g` is held by frame 0. The theorem records the state the
corpus describes (the effective anchor of `g` is now in `f1`, which is not an ancestor of frame 0)
and that the exit of `f1` is then rejected. This disagreement is a result, reported, not resolved.
-/

namespace Ern.Concurrency.Corpus

open Ern.MemoryModel.Access Ern.Concurrency
open Ern.Concurrency.Traces (L0)

/-- `c0 : acquire(e)` in `MX₃`: `g`, authority 4, held by frame 0 (WC4 C16). -/
def r1 : SC := deriveSyncEff x2 0 3
/-- `m := derive(root_M, Modify, footprint(M))`, authority 5 (O1). -/
def r2 : SC := r1.set (deriveEff (r1.view 0) 0 [1, 2] .modify)
/-- `enterFrame f1` yielding `m`, with the local `M′` (place 7, fields 8 and 9, `Uninit`) (O6). -/
def r3 : SC := enterEffC r2 0 [5] [(none, 0), (some 7, 0), (some 7, 0)]
/-- `f1 : transfer(M, M′)` (O4). -/
def r4 : SC := transferEffC r3 0 0 7

/-- The setup of S10 (`corpus-spec2-m3.md` §1 S10): `acquire(e)` by context 0, `derive`, then
`enterFrame f1` yielding `m` with the local `M′`. -/
theorem s10_setup : AcquireOk KM L0 x2 regX 0 0 (r1, [⟨3, some 4⟩]) ∧
    opStepC KM (.derive 0 [1, 2] .modify) 0 r1 (.ok r2) ∧
    opStepC KM (.enter [5] [(none, 0), (some 7, 0), (some 7, 0)]) 0 r2 (.ok r3) :=
  ⟨⟨by decide, ⟨3, none⟩, rfl, by decide, by decide, rfl⟩, ⟨by decide, _, .ok (by decide), rfl⟩,
    ⟨by decide, .ok (by decide)⟩⟩

/-- `corpus-spec2-m3.md` §1 S10: the corpus verdict is `reject` (O4.7: "`g` détenue par `f0`, son
anchor effectif `root_T` passe en `f1`"). Effective verdict of the model: `ok`. In `f1`,
`transfer(M, M′)` by context 0 is an `ok` step of Spec 1 §63 re-indexed; after it, the effective
anchor of `g` (authority 4) is in frame 1, which is not an ancestor of frame 0 holding `g`
(`EffAnchorOKC` fails for `g` and its holder frame), and `exitFrameC(f1)` is rejected. The
positive twin (`M′` local of `f0`) is `Ern.Concurrency.EncapTraces.traceB`. -/
theorem S10_1_ok : opStepC KM (.transfer 0 7) 0 r3 (.ok r4) ∧
    ¬ EffAnchorOKC r4 4 (some 0) ∧ opStepC KM .exit 0 r4 .reject :=
  ⟨⟨by decide, .ok (by decide)⟩, by decide, ⟨by decide, .reject (by decide)⟩⟩

end Ern.Concurrency.Corpus
