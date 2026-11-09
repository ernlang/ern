import Ern.Concurrency.Frames

/-!
# Provisional by-value transmission at `spawn` (WC4 C5)

The composite of WC4 C5, a single transition with four ordered phases:

1. create (WC4 C5.1): the new context, its initial frame, its locals and their root authorities,
   without yielding the parameters (`spawnCreate`);
2. transfer (WC4 C5.2): each by-value argument `(source, destination)` in its declared order, by
   the effect of O4 (Spec 1 §63) executed by the creating context on the state produced by the
   earlier transfers (`transfersEff`); the clauses of O4 that are not resulting-state conditions
   are evaluated at the start of the corresponding transfer (`ValTransferPre`);
3. yield (WC4 C5.3): the parameters change holder to the new frame (`yieldEff`);
4. final checks (WC4 C5.4) on the final state.
-/

namespace Ern.Concurrency

open Ern.MemoryModel.Access

/-! ## Effects (WC4 C5 effects) -/

/-- Phase 1 of WC4 C5 (create): the effect of `spawn` (WC4 C4) with no parameter yielded. -/
def spawnCreate (s : SC) (c : Nat) (ls : LocalShape) : SC := spawnEff s c [] ls

/-- Phase 2 of WC4 C5 (transfer): the effects of O4 (Spec 1 §63) executed by `c`, in the declared
order, each on the state produced by the earlier ones. -/
def transfersEff (c : Nat) : SC → List (Nat × Nat) → SC
  | t, [] => t
  | t, v :: vs => transfersEff c (transferEffC t c v.1 v.2) vs

/-- Phase 3 of WC4 C5 (yield): the parameters `ps` change holder to the frame `f` (WC4 C4 effect,
Spec 1 §72 effect); no right is created. -/
def yieldEff (t : SC) (ps : List Nat) (f : Nat) : SC :=
  { t with A := mapI (fun j y => if j ∈ ps then { y with holder := .frame f } else y) 0 t.A }

/-- Effect of the composite (WC4 C5.1–C5.3): create, the transfers of `vs`, then the yield of `ps`
to the new frame `nF`. -/
def spawnValEff (s : SC) (c : Nat) (ps : List Nat) (ls : LocalShape) (vs : List (Nat × Nat)) :
    SC :=
  yieldEff (transfersEff c (spawnCreate s c ls) vs) ps s.nF

/-! ## Preconditions (WC4 C4, C5) -/

/-- WC4 C5 item 2: `dst` is a fresh root local of the initial frame of the new context (its leaves
are `Uninit`, it holds no derived authority and its root authority is held by that frame by
construction of `spawnCreate`). -/
def FreshRootLocal (s : SC) (ls : LocalShape) (dst : Nat) : Prop :=
  ∃ i ∈ rootIdx ls.toShape, dst = s.P.length + i

/-- Decidability of `FreshRootLocal` (WC4 C5 item 2). -/
instance (s : SC) (ls : LocalShape) (dst : Nat) : Decidable (FreshRootLocal s ls dst) := by
  unfold FreshRootLocal; infer_instance

/-- The clauses of O4 (Spec 1 §63) for the by-value argument `(src, dst)`, executed by the creating
context `c`, at the start of its transfer phase in state `t` (WC4 C5.2, C5 items 1, 3, 4): those
of `TransferPreC` other than the exercisable `Modify` over the destination (replaced by C5 item 2,
WC4 C5 item 3) and the resulting-state clauses; §63.8 is evaluated on the final state `fin` (WC4
C5.4). -/
structure ValTransferPre (k : K) (fin : S3) (t : SC) (c src dst : Nat) : Prop where
  /-- WC4 C5 item 1, Spec 1 §63.1: `source` is usable. -/
  srcUsable : (t.view c).Usable src
  /-- Spec 1 §63.1: `destination` is usable. -/
  dstUsable : (t.view c).Usable dst
  /-- WC4 C5.2, C5 item 1, Spec 1 §63.1: exercisable `Modify` of the creating frame over the
  source. -/
  srcRight : HasRight (t.view c) .modify src
  /-- WC4 C5.2, Spec 1 §63.2: same shape of ordered subtrees. -/
  sameShape : SameShape (t.view c).P src dst
  /-- WC4 C5 item 1, Spec 1 §63.3: all source leaves are `Init`. -/
  srcInit : ∀ l ∈ footprint (t.view c).P src, (t.view c).I l = .init
  /-- WC4 C5 item 2, Spec 1 §63.3: no destination leaf is `Init`. -/
  dstNotInit : ∀ l ∈ footprint (t.view c).P dst, (t.view c).I l ≠ .init
  /-- WC4 C5.2, Spec 1 §63.3: disjoint footprints. -/
  disjoint : ¬ overlap (t.view c).P src dst
  /-- WC4 C5.2, C5 item 4, Spec 1 §63.4: no active derived authority covers a source leaf from
  outside the source, except some authority grounding the `Modify` right over the source and its
  origin chain. -/
  noOutsideDerived : ∃ g ∈ List.range (t.view c).A.length, Grounds (t.view c) .modify src g ∧
    ∀ j ∈ List.range (t.view c).A.length, ActiveDerivedOutside (t.view c) src j →
      RightChain (t.view c) g j
  /-- WC4 C5 item 4, Spec 1 §63.5: no in-place source leaf is pinned. -/
  notPinned : ∀ l ∈ footprint (t.view c).P src, ¬ k.Pinned l ∧ (t.view c).pin l = false
  /-- WC4 C5 item 4, Spec 1 §63.6, first half: dependencies of the usable places following the
  value are valid. -/
  depsValid : ∀ x ∈ movedDeps (t.view c) src, (t.view c).Active x
  /-- WC4 C5 item 4, C5.4, Spec 1 §63.8: no authority held before the transfer by a part of the
  source covers, in the final state, a leaf of its holder. -/
  noSelfLock : ∀ j ∈ List.range (t.view c).A.length,
    OptP ((t.view c).A[j]?) (fun y => heldIn (t.view c).P src y.holder) False → ¬ SelfLock fin j

/-- Decidability of `ValTransferPre` (WC4 C5). -/
instance (k : K) [DecidablePred k.Pinned] (fin : S3) (t : SC) (c src dst : Nat) :
    Decidable (ValTransferPre k fin t c src dst) :=
  decidable_of_iff ((t.view c).Usable src ∧ (t.view c).Usable dst ∧
    HasRight (t.view c) .modify src ∧ SameShape (t.view c).P src dst ∧
    (∀ l ∈ footprint (t.view c).P src, (t.view c).I l = .init) ∧
    (∀ l ∈ footprint (t.view c).P dst, (t.view c).I l ≠ .init) ∧ ¬ overlap (t.view c).P src dst ∧
    (∃ g ∈ List.range (t.view c).A.length, Grounds (t.view c) .modify src g ∧
      ∀ j ∈ List.range (t.view c).A.length, ActiveDerivedOutside (t.view c) src j →
        RightChain (t.view c) g j) ∧
    (∀ l ∈ footprint (t.view c).P src, ¬ k.Pinned l ∧ (t.view c).pin l = false) ∧
    (∀ x ∈ movedDeps (t.view c) src, (t.view c).Active x) ∧
    (∀ j ∈ List.range (t.view c).A.length,
      OptP ((t.view c).A[j]?) (fun y => heldIn (t.view c).P src y.holder) False →
        ¬ SelfLock fin j))
    ⟨fun ⟨a, b, c, d, e, f, g, h, i, j, l⟩ => ⟨a, b, c, d, e, f, g, h, i, j, l⟩,
     fun ⟨a, b, c, d, e, f, g, h, i, j, l⟩ => ⟨a, b, c, d, e, f, g, h, i, j, l⟩⟩

/-- WC4 C5.2: every by-value argument satisfies `ValTransferPre` at the start of its transfer
phase, in the declared order, on the state produced by the earlier transfers. -/
def ValTransfersPre (k : K) (fin : S3) (c : Nat) : SC → List (Nat × Nat) → Prop
  | _, [] => True
  | t, v :: vs => ValTransferPre k fin t c v.1 v.2 ∧
      ValTransfersPre k fin c (transferEffC t c v.1 v.2) vs

/-- Decidability of `ValTransfersPre` (WC4 C5.2). -/
instance instDecidableValTransfersPre (k : K) [DecidablePred k.Pinned] (fin : S3) (c : Nat) :
    (t : SC) → (vs : List (Nat × Nat)) → Decidable (ValTransfersPre k fin c t vs)
  | _, [] => isTrue trivial
  | t, v :: vs =>
    haveI := instDecidableValTransfersPre k fin c (transferEffC t c v.1 v.2) vs
    inferInstanceAs (Decidable (ValTransferPre k fin t c v.1 v.2 ∧ _))

/-- Preconditions of the by-value composite executed by `c` (WC4 C4.1, C4.3, C4.5, C4.6, C5.1–C5.4
and C5 items 1–5). C4.2 (fresh identities), C4.4 and C5 item 6 (no duplication) hold by
construction of `spawnValEff`; the preservation obligations of WC4 C4 and C5 are theorems, not
preconditions. -/
structure SpawnValPre (k : K) (s : SC) (c : Nat) (ps : List Nat) (ls : LocalShape)
    (vs : List (Nat × Nat)) : Prop where
  /-- WC4 C4.1: the creating context and its current frame are live. -/
  creatorLive : s.stk c ≠ []
  /-- WC4 C4.3, C5.3 (Spec 1 §72.1): every parameter is an active derived authority held by the
  creating frame before the composite. -/
  params : ∀ a ∈ ps, OptP ((s.view c).A[a]?) (fun y => y.active = true ∧
    y.holder = .frame (s.view c).top ∧ y.origin ≠ none) False
  /-- WC4 C4.5 (Spec 1 §72.2): the locals form a well-formed shape. -/
  localsOK : ShapeOK s.P.length ls.toShape
  /-- WC4 C5 item 2: every destination is a fresh root local of the new frame. -/
  freshDst : ∀ v ∈ vs, FreshRootLocal s ls v.2
  /-- WC4 C5.2, C5 items 1, 3, 4: the transfer phases. -/
  transfers : ValTransfersPre k (spawnValEff s c ps ls vs).flat c (spawnCreate s c ls) vs
  /-- WC4 C5 item 5: no parameter covers a leaf of a by-value source, on the declared source
  footprints before consumption. -/
  paramsApart : ∀ a ∈ ps, ∀ v ∈ vs, ∀ l ∈ (s.view c).afp a, l ∉ footprint s.P v.1
  /-- WC4 C5.3 (Spec 1 §72.1): at the beginning of the yield phase, every parameter is active,
  derived and held by the creating frame, in the state produced by the transfers. -/
  paramsAtYield : ∀ a ∈ ps,
    OptP (((transfersEff c (spawnCreate s c ls) vs).view c).A[a]?) (fun y => y.active = true ∧
      y.holder = .frame ((transfersEff c (spawnCreate s c ls) vs).view c).top ∧
      y.origin ≠ none) False
  /-- WC4 C5.4, Spec 1 §63.6, second half: `AnchorOrder` (on `ancestorC`) in the final state. -/
  anchorOrder : AnchorOrderC (spawnValEff s c ps ls vs)
  /-- WC4 C5.4, Spec 1 §63.9: every destination is usable in the final state. -/
  dstUsableAfter : ∀ v ∈ vs, (spawnValEff s c ps ls vs).flat.Usable v.2
  /-- WC4 C4.5, C5.4, Spec 1 §72.3: origin protection in the final state, from the current frame of
  the new context. -/
  originHidden : ∀ p ∈ ps, ParamOriginHidden ((spawnValEff s c ps ls vs).view s.C.length) p
  /-- WC4 C4.5, C5.4, Spec 1 §72.4 (`AnchorOrderHeld` on `ancestorC`) in the final state, which
  includes Spec 1 §63.7 for the moved held authorities. -/
  anchorOrderHeld : AnchorOrderHeldC (spawnValEff s c ps ls vs)

/-- Decidability of `SpawnValPre` (WC4 C4, C5). -/
instance (k : K) [DecidablePred k.Pinned] (s : SC) (c : Nat) (ps : List Nat) (ls : LocalShape)
    (vs : List (Nat × Nat)) : Decidable (SpawnValPre k s c ps ls vs) :=
  decidable_of_iff (s.stk c ≠ [] ∧ (∀ a ∈ ps, OptP ((s.view c).A[a]?) (fun y =>
      y.active = true ∧ y.holder = .frame (s.view c).top ∧ y.origin ≠ none) False) ∧
    ShapeOK s.P.length ls.toShape ∧ (∀ v ∈ vs, FreshRootLocal s ls v.2) ∧
    ValTransfersPre k (spawnValEff s c ps ls vs).flat c (spawnCreate s c ls) vs ∧
    (∀ a ∈ ps, ∀ v ∈ vs, ∀ l ∈ (s.view c).afp a, l ∉ footprint s.P v.1) ∧
    (∀ a ∈ ps,
      OptP (((transfersEff c (spawnCreate s c ls) vs).view c).A[a]?) (fun y => y.active = true ∧
        y.holder = .frame ((transfersEff c (spawnCreate s c ls) vs).view c).top ∧
        y.origin ≠ none) False) ∧
    AnchorOrderC (spawnValEff s c ps ls vs) ∧
    (∀ v ∈ vs, (spawnValEff s c ps ls vs).flat.Usable v.2) ∧
    (∀ p ∈ ps, ParamOriginHidden ((spawnValEff s c ps ls vs).view s.C.length) p) ∧
    AnchorOrderHeldC (spawnValEff s c ps ls vs))
    ⟨fun ⟨a, b, c, d, e, f, g, h, i, j, l⟩ => ⟨a, b, c, d, e, f, g, h, i, j, l⟩,
     fun ⟨a, b, c, d, e, f, g, h, i, j, l⟩ => ⟨a, b, c, d, e, f, g, h, i, j, l⟩⟩

/-- The by-value composite executed by `c` (WC4 C5): `ok` or `reject`; no outcome if `c` is not
live. -/
def SpawnValStep (k : K) (s : SC) (c : Nat) (ps : List Nat) (ls : LocalShape)
    (vs : List (Nat × Nat)) (o : Outcome3 SC) : Prop :=
  s.Live c ∧ Guarded (SpawnValPre k s c ps ls vs) (spawnValEff s c ps ls vs) o

/-! ## Verdict of the milestone-1 case D2 (WC4 C5 item 5) -/

namespace TransferWitness

open Ern.MemoryModel.Access.Examples

/-- Statics of Spec 1 `Examples.st` with frame 0 deriving a `Modify` authority (3) over leaf 0
(Spec 1 §60). -/
def w0 : SC := SC.ofS3 (deriveEff s0 0 [0] .modify)

end TransferWitness

open TransferWitness Ern.MemoryModel.Access.Examples in
/-- WC4 C5 item 5: in `w0`, context 0 spawns a context transmitting authority 3 (a `Modify`
derivative over leaf 0, held by frame 0) and moving the value of place 0 into a fresh one-leaf local
(place 3) of the new frame. Authority 3 covers leaf 0 of the source: the composite is rejected. -/
theorem spawnVal_covering_rejected :
    ¬ SpawnValPre K0 w0 0 [3] [(none, 0)] [(0, 3)] ∧
    SpawnValStep K0 w0 0 [3] [(none, 0)] [(0, 3)] .reject :=
  ⟨by decide, by decide, .reject (by decide)⟩

open TransferWitness Ern.MemoryModel.Access.Examples in
/-- Positive twin of `spawnVal_covering_rejected` (WC4 C5): the same composite without the
parameter covering the source is `ok`; in its final state the source leaf 0 is `Moved` and the
destination leaf 3 is `Init` (WC4 C5 effect, Spec 1 §63 effect). -/
theorem spawnVal_apart_ok :
    SpawnValStep K0 w0 0 [] [(none, 0)] [(0, 3)] (.ok (spawnValEff w0 0 [] [(none, 0)] [(0, 3)])) ∧
    (spawnValEff w0 0 [] [(none, 0)] [(0, 3)]).I 0 = .moved ∧
    (spawnValEff w0 0 [] [(none, 0)] [(0, 3)]).I 3 = .init :=
  ⟨⟨by decide, .ok (by decide)⟩, by decide, by decide⟩

end Ern.Concurrency
