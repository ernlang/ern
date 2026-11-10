import Ern.MemoryModel.Access.Main

/-!
# Corpus of milestone 3, sequential witness of S10

`corpus-spec2-m3.md` §1 S10 and its note "Note Spec 1": the configuration of S10 in the kernel of
`specs/ERN_Memory_Model_Specification_v0.1.md` alone, without mutex, `deriveSync` or context. The
module imports `Ern.MemoryModel` only.

Base frame 0: the local `M = {slot}` owns the root `T`; `guarded := derive(root_T, Modify)` is
stored in `slot` (O1, O8); `g := derive(guarded, Modify)` is held by frame 0; frame 0 enters frame
1 yielding `m := derive(root_M, Modify, footprint(M))`, with a local `M′ = {slot′}` of the same
shape, `Uninit` (O6). Verdicts from `corpus-spec2-m3.md` §1 S10, by `decide`, on the contract
`Examples.K0`.
-/

namespace Ern.Concurrency.Corpus.S10Seq

open Ern.MemoryModel.Access Ern.MemoryModel.Access.Examples

/-- Statics (Spec 1 §47): `0` the local `M` of the base frame, with the field `1` (`slot`,
`Uninit`); `2` the root `T`, owned by `M`, `Init`. Root authorities: `0` of `M` (frame 0), `1` of
`T` (held by `M`). -/
def s10st : Statics :=
  [((none, none, 0), false), ((some 0, none, 0), false), ((none, some 0, 0), true)]

/-- The statics are well formed (Spec 1 §47). -/
theorem s10st_ok : StaticsOK s10st := by decide

/-- Initial state (Spec 1 §47). -/
def q0 : S3 := S3.init s10st
/-- `guarded := derive(root_T, Modify, footprint(T))`, authority 2 (O1). -/
def q1 : S3 := deriveEff q0 1 [2] .modify
/-- `store(guarded, slot)` (O8). -/
def q2 : S3 := storeEff q1 2 1
/-- `g := derive(guarded, Modify)`, authority 3, held by frame 0 (O1). -/
def q3 : S3 := deriveEff q2 2 [2] .modify
/-- `m := derive(root_M, Modify, footprint(M))`, authority 4 (O1). -/
def q4 : S3 := deriveEff q3 0 [1] .modify
/-- `enterFrame f1` yielding `m`, with the local `M′` (place 3) and its field `slot′` (place 4),
`Uninit` (O6): frame 1. -/
def q5 : S3 := enterEff q4 [4] [(none, 0), (some 3, 0)]
/-- `f1 : transfer(M, M′)` (O4). -/
def q6 : S3 := transferEff q5 0 3
/-- `f1 : transfer(M′, M)` (O4). -/
def q7 : S3 := transferEff q6 3 0
/-- `exitFrame` of frame 1 (O7). -/
def q8 : S3 := exitEff q7

/-- The setup of the witness: each step is an `ok` step of Spec 1 (§60, §65, §72); frame 1 is the
current frame and `g` is held by frame 0. -/
theorem s10seq_setup : DeriveStep 1 [2] .modify q0 (.ok q1) ∧ StoreStep 2 1 q1 (.ok q2) ∧
    DeriveStep 2 [2] .modify q2 (.ok q3) ∧ DeriveStep 0 [1] .modify q3 (.ok q4) ∧
    EnterStep [4] [(none, 0), (some 3, 0)] q4 (.ok q5) ∧ q5.F = [1, 0] ∧
    q5.A[3]? = some ⟨.modify, some 2, [2], .frame 0, true⟩ :=
  ⟨.ok (by decide), .ok (by decide), .ok (by decide), .ok (by decide), .ok (by decide), by decide,
    by decide⟩

/-- `corpus-spec2-m3.md` §1 S10, step 1, `ok` (§63.1 via `m` and `root_M′`; §63.4: `T` is not a
leaf of the source; §63.7: the moved held authorities, `guarded` and `root_T`, satisfy
`AnchorOrderHeld` in frame 1): `transfer(M, M′)` from frame 1. -/
theorem S10Seq_1_ok : TransferStep K0 0 3 q5 (.ok q6) := .ok (by decide)

/-- `corpus-spec2-m3.md` §1 S10, step 2, `reject` (§73.4: the origin chain of `g`, `guarded` then
`root_T`, reaches no surviving origin): `exitFrame` in the state after the transfer. -/
theorem S10Seq_2_reject : ExitStep K0 q6 .reject ∧
    firstSurv q6 q6.F.tail (q6.ancs 3) = none :=
  ⟨.reject (by decide), by decide⟩

/-- `corpus-spec2-m3.md` §1 S10: after the transfer, the frame of the effective anchor of `g`
(`root_T`, held by `M′` in frame 1) is not an ancestor of frame 0, the holder of `g`. Neither §44
(`AnchorOrderHeld` constrains authorities held by places) nor §63.7 (moved held authorities)
constrains `g`. A fact of this state, not a rule. -/
theorem S10Seq_anchor_misplaced : ¬ EffAnchorOK q6 3 (some 0) := by decide

/-- `corpus-spec2-m3.md` §1 S10, step 3, `ok` (§63.3: the leaves of `M` are `Moved`, not `Init`):
`transfer(M′, M)` from frame 1. -/
theorem S10Seq_3_ok : TransferStep K0 3 0 q6 (.ok q7) := .ok (by decide)

/-- `corpus-spec2-m3.md` §1 S10, step 4, `ok` (§73.4, §73.5): `exitFrame` after the transfer
back. -/
theorem S10Seq_4_ok : ExitStep K0 q7 (.ok q8) := .ok (by decide)

/-- The configuration of S10 is reachable in the sequential kernel (`corpus-spec2-m3.md` §5, "Note
Spec 1"): the stuck state `q6` and the final state `q8` are reachable from `S3.init s10st` under
`K0` (Spec 1 §57). -/
theorem s10seq_reachable : Reachable K0 s10st q6 ∧ Reachable K0 s10st q8 := by
  obtain ⟨h1, h2, h3, h4, h5, -, -⟩ := s10seq_setup
  have r5 : Reachable K0 s10st q5 :=
    ((((Reachable.init.step (.derive h1)).step (.store h2)).step (.derive h3)).step
      (.derive h4)).step (.enter h5)
  have r6 : Reachable K0 s10st q6 := r5.step (.transfer S10Seq_1_ok)
  exact ⟨r6, (r6.step (.transfer S10Seq_3_ok)).step (.exit S10Seq_4_ok)⟩

end Ern.Concurrency.Corpus.S10Seq
