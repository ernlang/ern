import Ern.Concurrency.Corpus.MX

/-!
# Corpus of milestone 3, case S10

`corpus-spec2-m3.md` §1 S10: from `MX₃`, context 0 acquires the grant `g` (held by frame 0), enters
`f1` yielding `m := derive(root_M, Modify)` with a local `M′` of the shape of `M`, and in `f1`
transfers `M` into `M′`. Verdicts of the corpus: `ok` (§63.7 constrains only the moved held
authorities, and `AnchorOrderHeld`, §44, only authorities held by places; `g`, held by frame 0 and
not moved, is constrained by no clause); then `exitFrameC(f1)` `reject` (§73.4); then
`transfer(M′, M)` `ok` (§63.3); then `exitFrameC(f1)` `ok`: a liveness trap, reversible. The
sequential counterpart, in the kernel of Spec 1 alone, is `Ern.Concurrency.Corpus.S10Seq`.
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

/-- `corpus-spec2-m3.md` §1 S10, step 1, `ok`, then `exitFrameC(f1)` `reject` (§73.4): in `f1`,
`transfer(M, M′)` by context 0 is an `ok` step of Spec 1 §63 re-indexed admitted by `Encap`; after
it, the effective anchor of `g` (authority 4) is in frame 1, which is not an ancestor of frame 0
holding `g` (`EffAnchorOKC` fails for `g` and its holder frame), and `exitFrameC(f1)` is rejected.
The positive twin (`M′` local of `f0`) is `Ern.Concurrency.EncapTraces.traceB`. -/
theorem S10_1_ok : opStepC KM (.transfer 0 7) 0 r3 (.ok r4) ∧
    Encap L0 (r3, [⟨3, some 4⟩]) (.kernel 0 (.transfer 0 7)) ∧
    ¬ EffAnchorOKC r4 4 (some 0) ∧ opStepC KM .exit 0 r4 .reject :=
  ⟨⟨by decide, .ok (by decide)⟩, (by decide : TransferExcl L0 (r3, [⟨3, some 4⟩]) 0), by decide,
    ⟨by decide, .reject (by decide)⟩⟩

/-- The steps of S10 form an `EncapsulatedTrace` from the initial state (WC4 C22, C23): the
effective verdict of `S10_1_ok` is an `ok` of the machine with the library, not only of the
kernel. -/
theorem s10_trace : EncapsulatedTrace KM L0 (x0, [], [])
    [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 3 1), .newMutex 0 3, .acquire 0 0,
     .kernel 0 (.derive 0 [1, 2] .modify),
     .kernel 0 (.enter [5] [(none, 0), (some 7, 0), (some 7, 0)]),
     .kernel 0 (.transfer 0 7)] (r4, [⟨3, some 4⟩], []) := by
  have h := mx3_trace.snoc (lbl := .acquire 0 0) (st' := (r1, [⟨3, some 4⟩], [])) trivial
    (.acquire s10_setup.1)
  have h := h.snoc (lbl := .kernel 0 (.derive 0 [1, 2] .modify))
    (st' := (r2, [⟨3, some 4⟩], [])) (by decide : ∀ e ∈ ([⟨3, some 4⟩] : SyncReg), e.Live r1 →
      0 ≠ e.guarded) (.kernel s10_setup.2.1)
  have h := h.snoc (lbl := .kernel 0 (.enter [5] [(none, 0), (some 7, 0), (some 7, 0)]))
    (st' := (r3, [⟨3, some 4⟩], [])) trivial (.kernel s10_setup.2.2)
  exact h.snoc (lbl := .kernel 0 (.transfer 0 7)) (st' := (r4, [⟨3, some 4⟩], [])) S10_1_ok.2.1
    (.kernel S10_1_ok.1)

/-- `f1 : transfer(M′, M)` (O4). -/
def r5 : SC := transferEffC r4 0 7 0
/-- `exitFrameC(f1)` (O7, WC4 C6). -/
def r6 : SC := exitEffC r5 0

/-- `corpus-spec2-m3.md` §1 S10, suite, `ok` (§63.3: the leaves of `M` are `Moved`, not `Init`;
§63.1 via `m` and `root_M′`): `transfer(M′, M)` from `f1`, admitted by `Encap`. -/
theorem S10_2_ok : opStepC KM (.transfer 7 0) 0 r4 (.ok r5) ∧
    Encap L0 (r4, [⟨3, some 4⟩]) (.kernel 0 (.transfer 7 0)) :=
  ⟨⟨by decide, .ok (by decide)⟩, (by decide : TransferExcl L0 (r4, [⟨3, some 4⟩]) 7)⟩

/-- `corpus-spec2-m3.md` §1 S10, suite, `ok` (§73.4, §73.5): `exitFrameC(f1)` after the transfer
back. -/
theorem S10_3_ok : opStepC KM .exit 0 r5 (.ok r6) := ⟨by decide, .ok (by decide)⟩

end Ern.Concurrency.Corpus
