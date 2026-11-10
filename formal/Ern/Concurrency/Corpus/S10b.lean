import Ern.MemoryModel.Access.Main

/-!
# Corpus v4, case S10b

`corpus-spec2-m3.md` v4 §2 quater, S10b: escape of a local anchor by transfer, in the kernel of
`specs/ERN_Memory_Model_Specification_v0.1.md` alone. The module imports `Ern.MemoryModel` only.
Verdicts from `corpus-spec2-m3.md` v4 §2 quater, by `decide`, on the contract `Examples.K0`.

Base frame 0: the local `D` (place 0), one leaf, `Uninit`; `d := derive(root_D, Modify)`; frame 0
enters frame 1 yielding `d`, with the locals `L` (place 1) and `L2` (place 2), one leaf each,
`Uninit`, and `X` (place 3). Spec 1 §72 creates the locals `Uninit`; `X` is made `Init` by
`write3(X)` via `root_X` (O10) to reach the setup of the corpus, where `X` is `Init`. In frame 1:
`x := derive(root_X, Modify)`, then `store(x, L)`.
-/

namespace Ern.Concurrency.Corpus.S10b

open Ern.MemoryModel.Access Ern.MemoryModel.Access.Examples

/-- Statics (Spec 1 §47): `0` the local `D` of the base frame, one leaf, `Uninit`. Root authority:
`0` of `D` (frame 0). -/
def bst : Statics := [((none, none, 0), false)]

/-- The statics are well formed (Spec 1 §47). -/
theorem bst_ok : StaticsOK bst := by decide

/-- Initial state (Spec 1 §47). -/
def b0 : S3 := S3.init bst
/-- `d := derive(root_D, Modify)`, authority 1 (O1). -/
def b1 : S3 := deriveEff b0 0 [0] .modify
/-- `enterFrame f1` yielding `d`, with the locals `L` (place 1), `L2` (place 2) and `X` (place 3),
of root authorities 2, 3 and 4 (O6): frame 1. -/
def b2 : S3 := enterEff b1 [1] [(none, 0), (none, 0), (none, 0)]
/-- `write3(X)` via `root_X` (O10): `X` is `Init`. -/
def b3 : S3 := write3Eff b2 [3]
/-- `x := derive(root_X, Modify)`, authority 5, held by frame 1 (O1). -/
def b4 : S3 := deriveEff b3 4 [3] .modify
/-- `store(x, L)` (O8). -/
def b5 : S3 := storeEff b4 5 1

/-- The setup of S10b (`corpus-spec2-m3.md` v4 §2 quater): each step is an `ok` step of Spec 1
(§60, §72, §67, §65); `store(x, L)` is `ok` (O8: the anchor of `x` and the place `L` are in frame
1). -/
theorem S10b_setup : DeriveStep 0 [0] .modify b0 (.ok b1) ∧
    EnterStep [1] [(none, 0), (none, 0), (none, 0)] b1 (.ok b2) ∧ Write3Step 4 [3] b2 (.ok b3) ∧
    DeriveStep 4 [3] .modify b3 (.ok b4) ∧ StoreStep 5 1 b4 (.ok b5) :=
  ⟨.ok (by decide), .ok (by decide), .ok (by decide), .ok (by decide), .ok (by decide)⟩

/-- `corpus-spec2-m3.md` v4 §2 quater S10b, `reject`: `transfer(L, D)` from frame 1. The failing
fields of `TransferPre` are `anchorOrderHeld` (§63.7: `x` would be held by `D`, a place of frame 0,
while its effective anchor `root_X` is in frame 1) and `anchorOrder` (§63.6); the fields of §63.1 to
§63.5 hold, as do those of §63.6 (`depsValid`), §63.8 and §63.9. -/
theorem S10b_1_reject : TransferStep K0 1 0 b5 .reject ∧
    ¬ (∀ x ∈ List.range b5.A.length, AnchorMoves b5 1 x →
      ∀ q ∈ List.range b5.P.length, (transferEff b5 1 0).Usable q →
        OptP ((transferEff b5 1 0).A[x]?) (fun y => y.active = true → y.holder = .place q →
          EffAnchorOK (transferEff b5 1 0) x ((transferEff b5 1 0).pframe q)) True) ∧
    ¬ AnchorOrder (transferEff b5 1 0) ∧
    (b5.Usable 1 ∧ b5.Usable 0 ∧ HasRight b5 .modify 1 ∧ HasRight b5 .modify 0) ∧
    SameShape b5.P 1 0 ∧
    ((∀ l ∈ footprint b5.P 1, b5.I l = .init) ∧ (∀ l ∈ footprint b5.P 0, b5.I l ≠ .init) ∧
      ¬ overlap b5.P 1 0) ∧
    (∃ g ∈ List.range b5.A.length, Grounds b5 .modify 1 g ∧
      ∀ j ∈ List.range b5.A.length, ActiveDerivedOutside b5 1 j → RightChain b5 g j) ∧
    (∀ l ∈ footprint b5.P 1, ¬ K0.Pinned l ∧ b5.pin l = false) ∧
    (∀ x ∈ movedDeps b5 1, b5.Active x) ∧ NoLocalSelfLock b5 1 0 ∧
    (transferEff b5 1 0).Usable 0 :=
  ⟨.reject (by decide), by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩

/-- `corpus-spec2-m3.md` v4 §2 quater S10b, twin, `ok`: `transfer(L, L2)` from frame 1; the anchor
and the new holding place are in frame 1 (§63.7), and `x` covers no leaf of `L2` (§63.8). -/
theorem S10b_2_ok : TransferStep K0 1 2 b5 (.ok (transferEff b5 1 2)) := .ok (by decide)

end Ern.Concurrency.Corpus.S10b
