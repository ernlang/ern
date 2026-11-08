import Ern.Concurrency.Frames

/-!
# Provisional by-value transmission at `spawn` (WC2 C5)

The composite of WC2 C5: `spawn` (WC2 C4) creating, among the locals of the new frame, a fresh
root `destination`, and the transfer of an owned `source` of the creator into it, with the
preconditions of O4 (Spec 1 §63) except the destination side of §63.1, replaced by WC2 C5.2–C5.3.

WC2 C5.4 evaluates the resulting-state conditions of O4 on the final state but does not say in
which state the other conditions are evaluated. Two of them depend on it: the source side of
§63.1 (exercisable `Modify` of the creating frame over the source, WC2 C5.1) and §63.4 (the
exemption of the grounding authority), since the spawn part moves the transmitted parameters to
the new frame. Both readings are defined (`SrcRightBefore`, `SrcRightAfterSpawn`) and
`readings_differ` exhibits a state where every other clause holds and the two readings disagree.
The composite relation itself is not defined: its definition requires that choice (see the
report).
-/

namespace Ern.Concurrency

open Ern.MemoryModel.Access

/-- Effect of the composite (WC2 C5 effect): the effect of `spawn` (WC2 C4), then the effect of
O4 (Spec 1 §63) from `src` to `dst` on the resulting state. -/
def spawnValEff (s : SC) (c : Nat) (ps : List Nat) (ls : LocalShape) (src dst : Nat) : SC :=
  (spawnEff s c ps ls).set (transferEff (spawnEff s c ps ls).flat src dst)

/-- WC2 C5.2: `dst` is a fresh root local of the initial frame of the new context (its leaves are
`Uninit`, it holds no derived authority and its root authority is held by that frame by
construction of `spawnEff`). -/
def FreshRootLocal (s : SC) (ls : LocalShape) (dst : Nat) : Prop :=
  ∃ i ∈ rootIdx ls.toShape, dst = s.P.length + i

/-- Decidability of `FreshRootLocal` (WC2 C5.2). -/
instance (s : SC) (ls : LocalShape) (dst : Nat) : Decidable (FreshRootLocal s ls dst) := by
  unfold FreshRootLocal; infer_instance

/-- Clauses of the composite whose state of evaluation is fixed by WC2 C4 and C5: C4.1, C4.3,
C4.5 (Spec 1 §72.2); C5.2; the source side of §63.1 without the right (usability); §63.2, §63.3,
§63.5, §63.6 (first half) and §63.8 on the state where the destination exists, after the spawn
part; the resulting-state conditions §63.6 (second half), §63.7 and §63.9 on the final state
(WC2 C5.4). Not included: the source right of §63.1 and §63.4 (two readings below), the
resulting-state conditions of WC2 C4.5–C4.6 (state of evaluation not fixed by WC2: after the
spawn part or after the composite) and WC2 C4.6, C5.8 ("invariants hold", see the report). -/
structure SpawnValPreBase (k : K) (s : SC) (c : Nat) (ps : List Nat) (ls : LocalShape)
    (src dst : Nat) : Prop where
  /-- WC2 C4.1: the creating context and its current frame are live. -/
  creatorLive : s.stk c ≠ []
  /-- WC2 C4.3: every transmitted parameter is an active derived authority held by the creating
  frame. -/
  params : ∀ a ∈ ps, OptP ((s.view c).A[a]?) (fun y => y.active = true ∧
    y.holder = .frame (s.view c).top ∧ y.origin ≠ none) False
  /-- WC2 C4.5 (Spec 1 §72.2): the locals form a well-formed shape. -/
  localsOK : ShapeOK s.P.length ls.toShape
  /-- WC2 C5.2: the destination is a fresh root local of the new frame. -/
  freshDst : FreshRootLocal s ls dst
  /-- WC2 C5.1 (Spec 1 §63.1): the source is usable. -/
  srcUsable : (s.view c).Usable src
  /-- WC2 C5.5 (Spec 1 §63.2): same shape of ordered subtrees. -/
  sameShape : SameShape (spawnEff s c ps ls).P src dst
  /-- Spec 1 §63.3: all source leaves are `Init`. -/
  srcInit : ∀ l ∈ footprint (spawnEff s c ps ls).P src, (spawnEff s c ps ls).I l = .init
  /-- Spec 1 §63.3, WC2 C5.2: no destination leaf is `Init`. -/
  dstNotInit : ∀ l ∈ footprint (spawnEff s c ps ls).P dst, (spawnEff s c ps ls).I l ≠ .init
  /-- WC2 C5.5 (Spec 1 §63.3): disjoint footprints. -/
  disjoint : ¬ overlap (spawnEff s c ps ls).P src dst
  /-- Spec 1 §63.5: no in-place source leaf is pinned. -/
  notPinned : ∀ l ∈ footprint (spawnEff s c ps ls).P src, ¬ k.Pinned l ∧
    (spawnEff s c ps ls).flat.pin l = false
  /-- Spec 1 §63.6: dependencies of the usable places following the value are valid. -/
  depsValid : ∀ x ∈ movedDeps (spawnEff s c ps ls).flat src, (spawnEff s c ps ls).flat.Active x
  /-- Spec 1 §63.6 re-indexed, WC2 C5.4: `AnchorOrder` (on `ancestorC`) in the final state. -/
  anchorOrder : AnchorOrderC (spawnValEff s c ps ls src dst)
  /-- Spec 1 §63.7 re-indexed, WC2 C5.4: moved held authorities satisfy `AnchorOrderHeld` (on
  `ancestorC`) in the final state. -/
  anchorOrderHeld : ∀ x ∈ List.range (spawnEff s c ps ls).A.length,
    AnchorMoves (spawnEff s c ps ls).flat src x → ∀ q ∈ List.range (spawnEff s c ps ls).P.length,
      (spawnValEff s c ps ls src dst).flat.Usable q →
      OptP ((spawnValEff s c ps ls src dst).A[x]?) (fun y => y.active = true →
        y.holder = .place q → EffAnchorOKC (spawnValEff s c ps ls src dst) x
          ((spawnValEff s c ps ls src dst).flat.pframe q)) True
  /-- Spec 1 §63.8: local self-blocking prevention. -/
  noSelfLock : NoLocalSelfLock (spawnEff s c ps ls).flat src dst
  /-- Spec 1 §63.9: the destination is usable in the final state. -/
  dstUsableAfter : (spawnValEff s c ps ls src dst).flat.Usable dst

/-- Decidability of `SpawnValPreBase` (WC2 C5). -/
instance (k : K) [DecidablePred k.Pinned] (s : SC) (c : Nat) (ps : List Nat) (ls : LocalShape)
    (src dst : Nat) : Decidable (SpawnValPreBase k s c ps ls src dst) :=
  decidable_of_iff (s.stk c ≠ [] ∧ (∀ a ∈ ps, OptP ((s.view c).A[a]?) (fun y =>
      y.active = true ∧ y.holder = .frame (s.view c).top ∧ y.origin ≠ none) False) ∧
    ShapeOK s.P.length ls.toShape ∧ FreshRootLocal s ls dst ∧ (s.view c).Usable src ∧
    SameShape (spawnEff s c ps ls).P src dst ∧
    (∀ l ∈ footprint (spawnEff s c ps ls).P src, (spawnEff s c ps ls).I l = .init) ∧
    (∀ l ∈ footprint (spawnEff s c ps ls).P dst, (spawnEff s c ps ls).I l ≠ .init) ∧
    ¬ overlap (spawnEff s c ps ls).P src dst ∧
    (∀ l ∈ footprint (spawnEff s c ps ls).P src, ¬ k.Pinned l ∧
      (spawnEff s c ps ls).flat.pin l = false) ∧
    (∀ x ∈ movedDeps (spawnEff s c ps ls).flat src, (spawnEff s c ps ls).flat.Active x) ∧
    AnchorOrderC (spawnValEff s c ps ls src dst) ∧
    (∀ x ∈ List.range (spawnEff s c ps ls).A.length,
      AnchorMoves (spawnEff s c ps ls).flat src x → ∀ q ∈ List.range (spawnEff s c ps ls).P.length,
        (spawnValEff s c ps ls src dst).flat.Usable q →
        OptP ((spawnValEff s c ps ls src dst).A[x]?) (fun y => y.active = true →
          y.holder = .place q → EffAnchorOKC (spawnValEff s c ps ls src dst) x
            ((spawnValEff s c ps ls src dst).flat.pframe q)) True) ∧
    NoLocalSelfLock (spawnEff s c ps ls).flat src dst ∧
    (spawnValEff s c ps ls src dst).flat.Usable dst)
    ⟨fun ⟨a, b, c, d, e, f, g, h, i, j, l, m, n, o, p⟩ =>
      ⟨a, b, c, d, e, f, g, h, i, j, l, m, n, o, p⟩,
     fun ⟨a, b, c, d, e, f, g, h, i, j, l, m, n, o, p⟩ =>
      ⟨a, b, c, d, e, f, g, h, i, j, l, m, n, o, p⟩⟩

/-- Source side of Spec 1 §63.1 and §63.4 for the creating context `c` in state `t` (WC2 C5.1,
C5.4): exercisable `Modify` over the source, and no active derived authority covering a source
leaf from outside the source except some grounding authority and its origin chain. -/
def SrcRight (t : SC) (c src : Nat) : Prop :=
  HasRight (t.view c) .modify src ∧
  ∃ g ∈ List.range (t.view c).A.length, Grounds (t.view c) .modify src g ∧
    ∀ j ∈ List.range (t.view c).A.length, ActiveDerivedOutside (t.view c) src j →
      RightChain (t.view c) g j

/-- Decidability of `SrcRight` (Spec 1 §63.1, §63.4). -/
instance (t : SC) (c src : Nat) : Decidable (SrcRight t c src) := by
  unfold SrcRight; infer_instance

/-- Reading (a) of WC2 C5.1, C5.4: the source clauses are evaluated in the state before the
composite. -/
def SrcRightBefore (s : SC) (c src : Nat) : Prop := SrcRight s c src

/-- Reading (b) of WC2 C5.1, C5.4: the source clauses are evaluated after the spawn part, when
the transmitted parameters are held by the new frame. -/
def SrcRightAfterSpawn (s : SC) (c : Nat) (ps : List Nat) (ls : LocalShape) (src : Nat) :
    Prop :=
  SrcRight (spawnEff s c ps ls) c src

/-- Decidability of reading (a) (WC2 C5.4). -/
instance (s : SC) (c src : Nat) : Decidable (SrcRightBefore s c src) := by
  unfold SrcRightBefore; infer_instance

/-- Decidability of reading (b) (WC2 C5.4). -/
instance (s : SC) (c : Nat) (ps : List Nat) (ls : LocalShape) (src : Nat) :
    Decidable (SrcRightAfterSpawn s c ps ls src) := by
  unfold SrcRightAfterSpawn; infer_instance

namespace TransferWitness

open Ern.MemoryModel.Access.Examples

/-- Statics of Spec 1 `Examples.st` with frame 0 deriving a `Modify` authority (3) over leaf 0
(Spec 1 §60). -/
def w0 : SC := SC.ofS3 (deriveEff s0 0 [0] .modify)

end TransferWitness

open TransferWitness Ern.MemoryModel.Access.Examples in
/-- The two readings of WC2 C5.1/C5.4 differ (report, problem of WC2 C5): in `w0`, context 0
spawns a context transmitting authority 3 (a `Modify` derivative over leaf 0, held by frame 0) and
moves the value of place 0 into a fresh one-leaf local (place 3) of the new frame. Every clause of
`SpawnValPreBase` holds; the source right holds before the composite (through authority 3) and
fails after the spawn part (authority 3 is held by the new frame and blocks the root of place
0). -/
theorem readings_differ : SpawnValPreBase K0 w0 0 [3] [(none, 0)] 0 3 ∧
    SrcRightBefore w0 0 0 ∧ ¬ SrcRightAfterSpawn w0 0 [3] [(none, 0)] 0 := by
  decide

end Ern.Concurrency
