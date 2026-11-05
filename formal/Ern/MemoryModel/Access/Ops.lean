import Ern.MemoryModel.Access.Basic

/-!
# Access kernel: operations O1–O16

The sixteen kernel operations of `specs/ERN_Memory_Model_Specification_v0.md` §60–§75. Each
operation has a precondition structure with one named field per clause item (or per condition of
an item), each field citing its clause; a `Decidable` instance; an effect function; and a step
relation over `Outcome3` (§58). Every operation except `alloc` is `Guarded` (`ok` or `reject`);
`alloc` may also `fail` (§58, §71). `KStep` is the union of their `ok` transitions.
-/

namespace Ern.MemoryModel.Access

/-- `mapI f i l` applies `f` to each element of `l` with its index counted from `i` (used by the
effects of §72 and §73). -/
def mapI {α β : Type} (f : Nat → α → β) : Nat → List α → List β
  | _, [] => []
  | i, a :: l => f i a :: mapI f (i + 1) l

/-! ## O1 `derive` (§60) -/

/-- Effect of `derive(source, region, mode)` (§60, `ok` effect): a new active authority of fresh
identity, origin `src`, mode `m`, footprint `region`, held by the current frame. -/
def deriveEff (s : S3) (src : Nat) (region : List Nat) (m : Mode) : S3 :=
  s.addAuth ⟨m, some src, region, .frame s.top, true⟩

/-- Preconditions of `derive` (§60). -/
structure DerivePre (s : S3) (src : Nat) (region : List Nat) (m : Mode) : Prop where
  /-- §60.1: `source` is active. -/
  active : s.Active src
  /-- §60.1: `ExercisableAt(s, source, mode)`. -/
  exercisable : s.ExercisableAt src m
  /-- §60.2: the leaves of `region` exist. -/
  leaves : ∀ l ∈ region, l < s.P.length ∧ isLeaf s.P l
  /-- §60.2: the leaves of `region` belong to the footprint of `source`. -/
  within : ∀ l ∈ region, l ∈ s.afp src
  /-- §60.2: `mode` does not exceed the effective right of `source` on these leaves. -/
  modeOK : ∀ l ∈ region, Allows (effective s src l) m
  /-- §60.3: the addition preserves I1 (§50): an active authority outside the origin chain of the
  new one and sharing a leaf of `region` has own mode `Observe`, and so has the request. -/
  exclusive : ∀ b ∈ List.range s.A.length, OptP (s.A[b]?) (fun y => y.active = true →
    b ∉ src :: s.ancs src → (∃ l ∈ region, l ∈ y.footprint) → y.mode = .observe ∧ m = .observe)
    True
  /-- §60.4: the new holding frame is the live current frame. -/
  frameLive : s.top ∈ s.F

/-- Decidability of the preconditions of `derive` (§60). -/
instance (s : S3) (src : Nat) (region : List Nat) (m : Mode) :
    Decidable (DerivePre s src region m) :=
  decidable_of_iff (s.Active src ∧ s.ExercisableAt src m ∧
    (∀ l ∈ region, l < s.P.length ∧ isLeaf s.P l) ∧ (∀ l ∈ region, l ∈ s.afp src) ∧
    (∀ l ∈ region, Allows (effective s src l) m) ∧
    (∀ b ∈ List.range s.A.length, OptP (s.A[b]?) (fun y => y.active = true →
      b ∉ src :: s.ancs src → (∃ l ∈ region, l ∈ y.footprint) → y.mode = .observe ∧ m = .observe)
      True) ∧
    s.top ∈ s.F)
    ⟨fun ⟨a, b, c, d, e, f, g⟩ => ⟨a, b, c, d, e, f, g⟩,
     fun ⟨a, b, c, d, e, f, g⟩ => ⟨a, b, c, d, e, f, g⟩⟩

/-- `derive` as a relation (§60). -/
def DeriveStep (src : Nat) (region : List Nat) (m : Mode) (s : S3) : Outcome3 S3 → Prop :=
  Guarded (DerivePre s src region m) (deriveEff s src region m)

/-! ## O2 `split` (§61) -/

/-- Effect of `split(source, regions)` (§61, `ok` effect): one active derived `Modify` authority
per region, held by the current frame. -/
def splitEff (s : S3) (src : Nat) (rs : List (List Nat)) : S3 :=
  { s with A := s.A ++ rs.map fun r => ⟨.modify, some src, r, .frame s.top, true⟩ }

/-- Exclusive right already distributed by `src` on leaf `p` (§61.3): an active `Modify`
descendant of `src` covering `p`. -/
def DistribExcl (s : S3) (src j p : Nat) : Prop :=
  OptP (s.A[j]?) (fun y => y.active = true ∧ src ∈ s.ancs j ∧ p ∈ y.footprint ∧ y.mode = .modify)
    False

/-- Decidability of `DistribExcl` (§61.3). -/
instance (s : S3) (src j p : Nat) : Decidable (DistribExcl s src j p) := by
  unfold DistribExcl; infer_instance

/-- Preconditions of `split` (§61). §61.4 is not a precondition (see the note of §61). -/
structure SplitPre (k : K) (s : S3) (src : Nat) (rs : List (List Nat)) : Prop where
  /-- §61.1: `source` is active. -/
  active : s.Active src
  /-- §61.1: `source` is exercisable by the current frame in `Modify`. -/
  exercisable : s.ExercisableAt src .modify
  /-- §61.1: sufficient modification rights: effective `Modify` on every leaf of the regions. -/
  modifyOn : ∀ r ∈ rs, ∀ p ∈ r, effective s src p = some .modify
  /-- §61.2: each region lies within the available footprint of `source`. -/
  within : ∀ r ∈ rs, ∀ p ∈ r, p ∈ s.afp src ∧ effective s src p ≠ none
  /-- §61.3: regions are pairwise disjoint, structurally or by `K.DeclaredDisjoint`. -/
  disjoint : rs.Pairwise (fun r r' => (∀ l ∈ r, l ∉ r') ∨ k.DeclaredDisjoint r r')
  /-- §61.3: no exclusive right already distributed is overlapped. -/
  notDistributed : ∀ r ∈ rs, ∀ p ∈ r, ∀ j ∈ List.range s.A.length, ¬ DistribExcl s src j p

/-- Decidability of the preconditions of `split` (§61). -/
instance (k : K) [∀ r r', Decidable (k.DeclaredDisjoint r r')] (s : S3) (src : Nat)
    (rs : List (List Nat)) : Decidable (SplitPre k s src rs) :=
  decidable_of_iff (s.Active src ∧ s.ExercisableAt src .modify ∧
    (∀ r ∈ rs, ∀ p ∈ r, effective s src p = some .modify) ∧
    (∀ r ∈ rs, ∀ p ∈ r, p ∈ s.afp src ∧ effective s src p ≠ none) ∧
    rs.Pairwise (fun r r' => (∀ l ∈ r, l ∉ r') ∨ k.DeclaredDisjoint r r') ∧
    (∀ r ∈ rs, ∀ p ∈ r, ∀ j ∈ List.range s.A.length, ¬ DistribExcl s src j p))
    ⟨fun ⟨a, b, c, d, e, f⟩ => ⟨a, b, c, d, e, f⟩, fun ⟨a, b, c, d, e, f⟩ => ⟨a, b, c, d, e, f⟩⟩

/-- `split` as a relation (§61). -/
def SplitStep (k : K) (src : Nat) (rs : List (List Nat)) (s : S3) : Outcome3 S3 → Prop :=
  Guarded (SplitPre k s src rs) (splitEff s src rs)

/-! ## O3 `release` (§62) -/

/-- Effect of `release(authority)` (§62, `ok` effect): the authority becomes inactive and leaves
the anchors of its holding place. -/
def releaseEff (s : S3) (a : Nat) : S3 := match s.A[a]? with
  | some x => { s with
      A := s.A.set a { x with active := false }
      D := fun q => if x.holder = .place q then (s.D q).filter (· != a) else s.D q }
  | none => s

/-- Right of the current frame on a holder (§62.2): the current frame itself, or a place on which
the current frame has exercisable `Modify`. -/
def HolderRight (s : S3) : Holder → Prop
  | .frame f => f = s.top
  | .place p => HasRight s .modify p

/-- Decidability of `HolderRight` (§62.2). -/
instance (s : S3) (h : Holder) : Decidable (HolderRight s h) := by
  cases h <;> unfold HolderRight <;> infer_instance

/-- Preconditions of `release` (§62). §62.5 is not represented. -/
structure ReleasePre (s : S3) (a : Nat) : Prop where
  /-- §62.1: the authority is active. -/
  active : s.Active a
  /-- §62.1: the authority is derived. -/
  derived : OptP (s.A[a]?) (fun y => y.origin ≠ none) False
  /-- §62.2: it is held by the current frame or by a place with exercisable `Modify`. -/
  holderRight : OptP (s.A[a]?) (fun y => HolderRight s y.holder) False
  /-- §62.3: no active descendant. -/
  noActiveDesc : ∀ j ∈ List.range s.A.length, a ∈ s.ancs j → ¬ s.Active j
  /-- §62.3, §62.4: no usable place keeps `a` as anchor, except its holding place. -/
  anchors : ∀ q ∈ List.range s.P.length, s.Usable q → a ∈ s.D q →
    (s.A[a]?).map (·.holder) = some (.place q)

/-- Decidability of the preconditions of `release` (§62). -/
instance (s : S3) (a : Nat) : Decidable (ReleasePre s a) :=
  decidable_of_iff (s.Active a ∧ OptP (s.A[a]?) (fun y => y.origin ≠ none) False ∧
    OptP (s.A[a]?) (fun y => HolderRight s y.holder) False ∧
    (∀ j ∈ List.range s.A.length, a ∈ s.ancs j → ¬ s.Active j) ∧
    (∀ q ∈ List.range s.P.length, s.Usable q → a ∈ s.D q →
      (s.A[a]?).map (·.holder) = some (.place q)))
    ⟨fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩, fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩⟩

/-- `release` as a relation (§62). -/
def ReleaseStep (a : Nat) (s : S3) : Outcome3 S3 → Prop :=
  Guarded (ReleasePre s a) (releaseEff s a)

/-! ## O4 `transfer` (§63) -/

/-- Children of place `x` in index order (§63.2). -/
def kids (P : List Place) (x : Nat) : List Nat :=
  (List.range P.length).filter fun r => decide (parentOf P r = some x)

/-- Position of `r` in a list, its length if absent (§63.2). -/
def posIn (r : Nat) : List Nat → Nat
  | [] => 0
  | a :: l => if a = r then 0 else posIn r l + 1

/-- `corr(r)` within `n` steps (§63.2): `dst` for `src`; for another part, the child at the same
position of the place corresponding to its parent. -/
def corrF (P : List Place) (src dst : Nat) : Nat → Nat → Option Nat
  | 0, r => if r = src then some dst else none
  | n + 1, r => if r = src then some dst else
      match parentOf P r with
      | some p => if p < r then
          (corrF P src dst n p).bind fun p' => (kids P p')[posIn r (kids P p)]? else none
      | none => none

/-- `corr(r)` (§63.2, §63.8): the part of `dst` corresponding to the part `r` of `src`. -/
def corr (P : List Place) (src dst r : Nat) : Option Nat := corrF P src dst r r

/-- Same shape of ordered subtrees (§63.2): every part of `src` has a corresponding part of `dst`
with as many children, and every part of `dst` corresponds to a part of `src`. -/
def SameShape (P : List Place) (src dst : Nat) : Prop :=
  (∀ r ∈ List.range P.length, partOf P r src →
    OptP (corr P src dst r) (fun r' => (kids P r').length = (kids P r).length) False) ∧
  ∀ z ∈ List.range P.length, partOf P z dst →
    ∃ r ∈ List.range P.length, partOf P r src ∧ corr P src dst r = some z

/-- Decidability of `SameShape` (§63.2). -/
instance (P : List Place) (src dst : Nat) : Decidable (SameShape P src dst) := by
  unfold SameShape; infer_instance

/-- Holder within the value at `q` (§63, §69, §70): `q` or one of its parts. -/
def heldIn (P : List Place) (q : Nat) : Holder → Prop
  | .place r => partOf P r q
  | .frame _ => False

/-- Decidability of `heldIn` (§63). -/
instance (P : List Place) (q : Nat) (h : Holder) : Decidable (heldIn P q h) := by
  cases h <;> unfold heldIn <;> infer_instance

/-- Holder `h` after the transfer of `src` to `dst` (§63, `ok` effect): part `r` of `src` becomes
`corr(r)`. Applied to holders within `src` only. -/
def mvTo (P : List Place) (src dst : Nat) : Holder → Holder
  | .place r => .place ((corr P src dst r).getD dst)
  | .frame f => .frame f

/-- Anchors moved onto place `q` by the transfer (§63, `ok` effect, fourth item): those of every
part `r` of `src` with `corr(r) = q`. -/
def movedTo (s : S3) (src dst q : Nat) : List Nat :=
  ((List.range s.P.length).filter fun r =>
    decide (partOf s.P r src ∧ corr s.P src dst r = some q)).flatMap s.D

/-- Effect of `transfer(source, destination)` (§63, `ok` effect): source leaves `Moved`,
destination leaves `Init`; authorities held by part `r` of `src`, and places owned by `r`, move
to `corr(r)`; the anchors of `r` follow `corr(r)`. -/
def transferEff (s : S3) (src dst : Nat) : S3 :=
  { s with
    P := s.P.map fun pl =>
      if heldIn s.P src pl.owner then { pl with owner := mvTo s.P src dst pl.owner } else pl
    I := fun l => if l ∈ footprint s.P dst then .init
      else if l ∈ footprint s.P src then .moved else s.I l
    D := fun q => if partOf s.P q src then [] else s.D q ++ movedTo s src dst q
    A := s.A.map fun y =>
      if heldIn s.P src y.holder then { y with holder := mvTo s.P src dst y.holder } else y }

/-- Active derived authority covering a leaf of `src` and not held within it (§63.4). -/
def ActiveDerivedOutside (s : S3) (src j : Nat) : Prop :=
  OptP (s.A[j]?) (fun y => y.active = true ∧ y.origin ≠ none ∧ ¬ heldIn s.P src y.holder ∧
    ∃ l ∈ y.footprint, l ∈ footprint s.P src) False

/-- Decidability of `ActiveDerivedOutside` (§63.4). -/
instance (s : S3) (src j : Nat) : Decidable (ActiveDerivedOutside s src j) := by
  unfold ActiveDerivedOutside; infer_instance

/-- The holder moves with the value at `src` (§63.6, §63.7): a part of `src` or storage it owns,
transitively. -/
def HolderMoves (s : S3) (src : Nat) : Holder → Prop
  | .place p => partOf s.P p src ∨ OwnedIn s.P src p
  | .frame _ => False

/-- Decidability of `HolderMoves` (§63.7). -/
instance (s : S3) (src : Nat) (h : Holder) : Decidable (HolderMoves s src h) := by
  cases h <;> unfold HolderMoves <;> infer_instance

/-- Authority `x` is a moved held authority (§63.7): its holder moves with the value at `src`. -/
def AnchorMoves (s : S3) (src x : Nat) : Prop :=
  OptP (s.A[x]?) (fun y => HolderMoves s src y.holder) False

/-- Decidability of `AnchorMoves` (§63.7). -/
instance (s : S3) (src x : Nat) : Decidable (AnchorMoves s src x) := by
  unfold AnchorMoves; infer_instance

/-- Dependencies of the usable places following the value at `src` (§63.6): the anchors of its
parts and of the usable storage it owns, transitively. -/
def movedDeps (s : S3) (src : Nat) : List Nat :=
  ((List.range s.P.length).filter fun q =>
    decide (partOf s.P q src ∨ (OwnedIn s.P src q ∧ s.Usable q))).flatMap s.D

/-- Leaves of a holder (§63.8): those of a place, none for a frame. -/
def holderLeaves (s : S3) : Holder → List Nat
  | .place p => footprint s.P p
  | .frame _ => []

/-- Authority `a` is active and covers a leaf of its own holder (§63.8). -/
def SelfLock (s : S3) (a : Nat) : Prop :=
  OptP (s.A[a]?) (fun y => y.active = true ∧ ∃ l ∈ y.footprint, l ∈ holderLeaves s y.holder) False

/-- Decidability of `SelfLock` (§63.8). -/
instance (s : S3) (a : Nat) : Decidable (SelfLock s a) := by unfold SelfLock; infer_instance

/-- Local self-blocking prevention (§63.8): no authority held before the step within `src` covers,
in the resulting state, a leaf of its new holder `corr(r)`. -/
def NoLocalSelfLock (s : S3) (src dst : Nat) : Prop :=
  ∀ j ∈ List.range s.A.length, OptP (s.A[j]?) (fun y => heldIn s.P src y.holder) False →
    ¬ SelfLock (transferEff s src dst) j

/-- Decidability of `NoLocalSelfLock` (§63.8). -/
instance (s : S3) (src dst : Nat) : Decidable (NoLocalSelfLock s src dst) := by
  unfold NoLocalSelfLock; infer_instance

/-- Preconditions of `transfer` (§63). -/
structure TransferPre (k : K) (s : S3) (src dst : Nat) : Prop where
  /-- §63.1: `source` is usable. -/
  srcUsable : s.Usable src
  /-- §63.1: `destination` is usable. -/
  dstUsable : s.Usable dst
  /-- §63.1: exercisable `Modify` over the source. -/
  srcRight : HasRight s .modify src
  /-- §63.1: exercisable `Modify` over the destination. -/
  dstRight : HasRight s .modify dst
  /-- §63.2: same shape of ordered subtrees. -/
  sameShape : SameShape s.P src dst
  /-- §63.3: all source leaves are `Init`. -/
  srcInit : ∀ l ∈ footprint s.P src, s.I l = .init
  /-- §63.3: no destination leaf is `Init`. -/
  dstNotInit : ∀ l ∈ footprint s.P dst, s.I l ≠ .init
  /-- §63.3: source and destination footprints are disjoint. -/
  disjoint : ¬ overlap s.P src dst
  /-- §63.4: no active derived authority covers a source leaf from outside the source. -/
  noOutsideDerived : ∀ j ∈ List.range s.A.length, ¬ ActiveDerivedOutside s src j
  /-- §63.5: no in-place source leaf is pinned, statically or dynamically. -/
  notPinned : ∀ l ∈ footprint s.P src, ¬ k.Pinned l ∧ s.pin l = false
  /-- §63.6: dependencies of the usable places following the value are valid. -/
  depsValid : ∀ x ∈ movedDeps s src, s.Active x
  /-- §63.6: `AnchorOrder` in the resulting state. -/
  anchorOrder : AnchorOrder (transferEff s src dst)
  /-- §63.7: every moved held authority satisfies `AnchorOrderHeld` in the resulting state. -/
  anchorOrderHeld : ∀ x ∈ List.range s.A.length, AnchorMoves s src x →
    ∀ q ∈ List.range s.P.length, (transferEff s src dst).Usable q →
      OptP ((transferEff s src dst).A[x]?) (fun y => y.active = true → y.holder = .place q →
        EffAnchorOK (transferEff s src dst) x ((transferEff s src dst).pframe q)) True
  /-- §63.8: local self-blocking prevention. -/
  noSelfLock : NoLocalSelfLock s src dst

/-- Decidability of the preconditions of `transfer` (§63). -/
instance (k : K) [DecidablePred k.Pinned] (s : S3) (src dst : Nat) :
    Decidable (TransferPre k s src dst) :=
  decidable_of_iff (s.Usable src ∧ s.Usable dst ∧ HasRight s .modify src ∧
    HasRight s .modify dst ∧ SameShape s.P src dst ∧ (∀ l ∈ footprint s.P src, s.I l = .init) ∧
    (∀ l ∈ footprint s.P dst, s.I l ≠ .init) ∧ ¬ overlap s.P src dst ∧
    (∀ j ∈ List.range s.A.length, ¬ ActiveDerivedOutside s src j) ∧
    (∀ l ∈ footprint s.P src, ¬ k.Pinned l ∧ s.pin l = false) ∧
    (∀ x ∈ movedDeps s src, s.Active x) ∧ AnchorOrder (transferEff s src dst) ∧
    (∀ x ∈ List.range s.A.length, AnchorMoves s src x →
      ∀ q ∈ List.range s.P.length, (transferEff s src dst).Usable q →
        OptP ((transferEff s src dst).A[x]?) (fun y => y.active = true → y.holder = .place q →
          EffAnchorOK (transferEff s src dst) x ((transferEff s src dst).pframe q)) True) ∧
    NoLocalSelfLock s src dst)
    ⟨fun ⟨a, b, c, d, e, f, g, h, i, j, l, m, n, o⟩ => ⟨a, b, c, d, e, f, g, h, i, j, l, m, n, o⟩,
     fun ⟨a, b, c, d, e, f, g, h, i, j, l, m, n, o⟩ => ⟨a, b, c, d, e, f, g, h, i, j, l, m, n, o⟩⟩

/-- `transfer` as a relation (§63). -/
def TransferStep (k : K) (src dst : Nat) (s : S3) : Outcome3 S3 → Prop :=
  Guarded (TransferPre k s src dst) (transferEff s src dst)

/-! ## O5 `depend` (§64) -/

/-- Effect of `depend(result, anchor)` (§64, `ok` effect): `anchor` is added to `D(result)`. -/
def dependEff (s : S3) (q x : Nat) : S3 :=
  { s with D := fun r => if r = q then s.D q ++ [x] else s.D r }

/-- Preconditions of `depend` (§64). The "real dependency" part of §64.2 is not represented;
§64.4 holds by construction (`depsOf`). -/
structure DependPre (s : S3) (q x : Nat) : Prop where
  /-- §64.1: `result` is usable. -/
  usable : s.Usable q
  /-- §64.1: exercisable `Modify` over `result`. -/
  right : HasRight s .modify q
  /-- §64.2: `anchor` is active. -/
  anchorActive : s.Active x
  /-- §64.3: the effective anchor's frame is the frame of `result` or an ancestor. -/
  anchorOrder : EffAnchorOK s x (s.pframe q)

/-- Decidability of the preconditions of `depend` (§64). -/
instance (s : S3) (q x : Nat) : Decidable (DependPre s q x) :=
  decidable_of_iff (s.Usable q ∧ HasRight s .modify q ∧ s.Active x ∧ EffAnchorOK s x (s.pframe q))
    ⟨fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩, fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩⟩

/-- `depend` as a relation (§64). -/
def DependStep (q x : Nat) (s : S3) : Outcome3 S3 → Prop :=
  Guarded (DependPre s q x) (dependEff s q x)

/-! ## O8 `store` (§65) -/

/-- Effect of `store(authority, target)` (§65, `ok` effect): `target` becomes the holder, the
authority joins `D(target)`, and only leaf `target` becomes `Init`. -/
def storeEff (s : S3) (a p : Nat) : S3 := match s.A[a]? with
  | some y => { s with
      A := s.A.set a { y with holder := .place p }
      D := fun q => if q = p then s.D p ++ [a] else s.D q
      I := fun l => if l = p then .init else s.I l }
  | none => s

/-- Preconditions of `store` (§65). -/
structure StorePre (s : S3) (a p : Nat) : Prop where
  /-- §65.1: the authority is active, derived, and held by the current frame. -/
  derivedHeld : OptP (s.A[a]?) (fun y => y.active = true ∧ y.origin ≠ none ∧
    y.holder = .frame s.top) False
  /-- §65.2: `target` is usable. -/
  usable : s.Usable p
  /-- §65.2: `target` is a leaf. -/
  leaf : isLeaf s.P p
  /-- §65.2: exercisable `Modify` over `target`. -/
  right : HasRight s .modify p
  /-- §65.2: `target` holds no active authority. -/
  free : ∀ j ∈ List.range s.A.length,
    OptP (s.A[j]?) (fun z => z.active = true → z.holder ≠ .place p) True
  /-- §65.3: the authority covers no leaf of `target` nor of storage it owns, transitively. -/
  noCover : ∀ l ∈ s.afp a, l ∉ footprint s.P p ∧
    ∀ q ∈ List.range s.P.length, OwnedIn s.P p q → l ∉ footprint s.P q
  /-- §65.4: the effective anchor respects `AnchorOrder` relative to the frame of `target`. -/
  anchorOrder : EffAnchorOK s a (s.pframe p)
  /-- §65.5: in the resulting state, `target` is under exercisable `Modify`. -/
  keepsTarget : HasRight (storeEff s a p) .modify p
  /-- §65.5: `AnchorOrderHeld` in the resulting state. -/
  anchorOrderHeld : AnchorOrderHeld (storeEff s a p)

/-- Decidability of the preconditions of `store` (§65). -/
instance (s : S3) (a p : Nat) : Decidable (StorePre s a p) :=
  decidable_of_iff (OptP (s.A[a]?) (fun y => y.active = true ∧ y.origin ≠ none ∧
      y.holder = .frame s.top) False ∧ s.Usable p ∧ isLeaf s.P p ∧ HasRight s .modify p ∧
    (∀ j ∈ List.range s.A.length,
      OptP (s.A[j]?) (fun z => z.active = true → z.holder ≠ .place p) True) ∧
    (∀ l ∈ s.afp a, l ∉ footprint s.P p ∧
      ∀ q ∈ List.range s.P.length, OwnedIn s.P p q → l ∉ footprint s.P q) ∧
    EffAnchorOK s a (s.pframe p) ∧ HasRight (storeEff s a p) .modify p ∧
    AnchorOrderHeld (storeEff s a p))
    ⟨fun ⟨a, b, c, d, e, f, g, h, i⟩ => ⟨a, b, c, d, e, f, g, h, i⟩,
     fun ⟨a, b, c, d, e, f, g, h, i⟩ => ⟨a, b, c, d, e, f, g, h, i⟩⟩

/-- `store` as a relation (§65). -/
def StoreStep (a p : Nat) (s : S3) : Outcome3 S3 → Prop :=
  Guarded (StorePre s a p) (storeEff s a p)

/-! ## Shapes (§47, §71.1, §72) -/

/-- A local shape as a shape whose elements have no owning element (§71.1, §72: locals and
allocated storage are owned by the receiving holder). -/
def LocalShape.toShape (ls : LocalShape) : List (Option Nat × Option Nat × Nat) :=
  ls.map fun e => (e.1, none, e.2)

/-- Owner of element `i` of a shape (§47, §72, §71): its owning element if any, `hd`
otherwise. -/
def shapeOwner (ls : List (Option Nat × Option Nat × Nat)) (hd : Holder) (i : Nat) : Holder :=
  match (ls[i]?).bind (·.2.1) with
  | some o => .place o
  | none => hd

/-- Places `P` followed by the elements of a shape (§47, §71, §72): (parent, owning element,
kind), owned by their owning element or by `hd`. -/
def shapeP (P : List Place) (hd : Holder) (ls : List (Option Nat × Option Nat × Nat)) :
    List Place :=
  P ++ (List.range ls.length).map fun i =>
    ⟨(ls[i]?).bind (·.1), shapeOwner ls hd i, ((ls[i]?).map (·.2.2)).getD 0⟩

/-- Well-formed shape at offset `n` (§72.2, §71.1; for statics, the hypothesis recorded for
§47): the parent and the owning element of an element are earlier elements, and a part has the
owning element of its parent. -/
def ShapeOK (n : Nat) (ls : List (Option Nat × Option Nat × Nat)) : Prop :=
  ∀ i ∈ List.range ls.length,
    OptP ((ls[i]?).bind (·.1)) (fun r => n ≤ r ∧ r < n + i ∧
      (ls[i]?).bind (·.2.1) = (ls[r - n]?).bind (·.2.1)) True ∧
    OptP ((ls[i]?).bind (·.2.1)) (fun o => n ≤ o ∧ o < n + i) True

/-- Decidability of `ShapeOK` (§72.2, §71.1). -/
instance (n : Nat) (ls : List (Option Nat × Option Nat × Nat)) : Decidable (ShapeOK n ls) := by
  unfold ShapeOK; infer_instance

/-- Indices of the root elements (no parent) of a shape (§40 root places; §47, §71, §72). -/
def rootIdx (ls : List (Option Nat × Option Nat × Nat)) : List Nat :=
  (List.range ls.length).filter fun i => ((ls[i]?).bind (·.1)).isNone

/-! ## O6 `enterFrame` (§72) -/

/-- Places after `enterFrame` (§72, `ok` effect): the locals appended, owned by the new frame. -/
def enterP (s : S3) (ls : LocalShape) : List Place := shapeP s.P (.frame s.nF) ls.toShape

/-- Effect of `enterFrame(params, locals)` (§72, `ok` effect): a new frame `nF` is pushed; the
parameters are now held by it; locals are appended (uninitialized, no anchor, alive, unpinned)
with one active root `Modify` authority per root local, held by the new frame. -/
def enterEff (s : S3) (ps : List Nat) (ls : LocalShape) : S3 :=
  { F := s.nF :: s.F, nF := s.nF + 1, P := enterP s ls
    I := fun l => if s.P.length ≤ l then .uninit else s.I l
    A := mapI (fun j y => if j ∈ ps then { y with holder := .frame s.nF } else y) 0 s.A ++
      (rootIdx ls.toShape).map fun i =>
        ⟨.modify, none, footprint (enterP s ls) (s.P.length + i),
          shapeOwner ls.toShape (.frame s.nF) i, true⟩
    D := fun q => if s.P.length ≤ q then [] else s.D q
    dead := fun q => if s.P.length ≤ q then false else s.dead q
    pin := fun q => if s.P.length ≤ q then false else s.pin q }

/-- Origin protection on entry for parameter `p` in state `s'` (§72.3): if `p` is a `Modify`
authority with direct origin `o`, `o` is exercisable in no mode. -/
def ParamOriginHidden (s' : S3) (p : Nat) : Prop :=
  OptP (s'.A[p]?) (fun y => y.mode = .modify →
    OptP y.origin (fun o => ¬ s'.ExercisableAt o .observe ∧ ¬ s'.ExercisableAt o .modify) True) True

/-- Decidability of `ParamOriginHidden` (§72.3). -/
instance (s' : S3) (p : Nat) : Decidable (ParamOriginHidden s' p) := by
  unfold ParamOriginHidden; infer_instance

/-- Preconditions of `enterFrame` (§72). The modes/footprints/parameter-passing part of §72.2 is
not represented. -/
structure EnterPre (s : S3) (ps : List Nat) (ls : LocalShape) : Prop where
  /-- §72.1: the calling frame, the current frame, is live. -/
  callerLive : s.F ≠ []
  /-- §72.1: each parameter is an active derived authority held by the caller. -/
  params : ∀ a ∈ ps, OptP (s.A[a]?) (fun y => y.active = true ∧ y.holder = .frame s.top ∧
    y.origin ≠ none) False
  /-- §72.2: the locals form a well-formed shape (each parent is an earlier local). -/
  localsOK : ShapeOK s.P.length ls.toShape
  /-- §72.3: origin protection on entry, in the resulting state. -/
  originHidden : ∀ p ∈ ps, ParamOriginHidden (enterEff s ps ls) p
  /-- §72.4: `AnchorOrderHeld` over the resulting state. -/
  anchorOrderHeld : AnchorOrderHeld (enterEff s ps ls)

/-- Decidability of the preconditions of `enterFrame` (§72). -/
instance (s : S3) (ps : List Nat) (ls : LocalShape) : Decidable (EnterPre s ps ls) :=
  decidable_of_iff (s.F ≠ [] ∧ (∀ a ∈ ps, OptP (s.A[a]?) (fun y => y.active = true ∧
      y.holder = .frame s.top ∧ y.origin ≠ none) False) ∧ ShapeOK s.P.length ls.toShape ∧
    (∀ p ∈ ps, ParamOriginHidden (enterEff s ps ls) p) ∧ AnchorOrderHeld (enterEff s ps ls))
    ⟨fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩, fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩⟩

/-- `enterFrame` as a relation (§72). -/
def EnterStep (ps : List Nat) (ls : LocalShape) (s : S3) : Outcome3 S3 → Prop :=
  Guarded (EnterPre s ps ls) (enterEff s ps ls)

/-! ## O7 `exitFrame` (§73) -/

/-- Authority `x` survives the exit to stack `F₀` (§73.4): active and held by a surviving frame
or by a usable place whose terminal owner survives. -/
def Survives (s : S3) (F₀ : Frames) (x : Nat) : Prop :=
  OptP (s.A[x]?) (fun y => y.active = true ∧ HolderLive { s with F := F₀ } y.holder) False

/-- Decidability of `Survives` (§73.4). -/
instance (s : S3) (F₀ : Frames) (x : Nat) : Decidable (Survives s F₀ x) := by
  unfold Survives; infer_instance

/-- First surviving authority of a list (§73.4). -/
def firstSurv (s : S3) (F₀ : Frames) (l : List Nat) : Option Nat :=
  l.find? fun z => decide (Survives s F₀ z)

/-- Authority `a` after the exit (§73, `ok` effect): released unless it survives; a surviving
derived authority is reanchored to the first surviving active origin of its chain. -/
def exitG (s : S3) (F₀ : Frames) (a : Nat) (y : Authority) : Authority :=
  if Survives s F₀ a then
    match y.origin with
    | none => y
    | some _ => { y with origin := firstSurv s F₀ (s.ancs a) }
  else { y with active := false }

/-- Effect of `exitFrame` (§73, `ok` effect): the current frame is popped; authorities that do
not survive are released; surviving derived authorities and the anchors of `D` are reanchored to
the first surviving authority of their chains. -/
def exitEff (s : S3) : S3 :=
  { s with
    F := s.F.tail
    D := fun q => (s.D q).map fun x => (firstSurv s s.F.tail (x :: s.ancs x)).getD x
    A := mapI (exitG s s.F.tail) 0 s.A }

/-- Preconditions of `exitFrame` (§73). The result clause of §73.2 is not represented. -/
structure ExitPre (k : K) (s : S3) : Prop where
  /-- §73.1: the current frame is not the initial frame and has a surviving caller. -/
  hasCaller : s.F.tail ≠ []
  /-- §73.2, §73.4, §73.5: every anchor of a place usable after the exit has a surviving
  authority among itself and its origins. -/
  anchors : ∀ q ∈ List.range s.P.length, ({ s with F := s.F.tail } : S3).Usable q →
    ∀ x ∈ s.D q, firstSurv s s.F.tail (x :: s.ancs x) ≠ none
  /-- §73.4: every surviving derived authority has a surviving active origin. -/
  origins : ∀ a ∈ List.range s.A.length, Survives s s.F.tail a → s.org a ≠ none →
    firstSurv s s.F.tail (s.ancs a) ≠ none
  /-- §73.3: no leaf of a place that dies with the frame is pinned, statically or
  dynamically. -/
  notPinned : ∀ q ∈ List.range s.P.length, s.Usable q →
    ¬ ({ s with F := s.F.tail } : S3).Usable q →
    ∀ l ∈ footprint s.P q, s.pin l = false ∧ ¬ k.Pinned l
  /-- §73.5: `AnchorOrderHeld` in the resulting state. -/
  anchorOrderHeld : AnchorOrderHeld (exitEff s)

/-- Decidability of the preconditions of `exitFrame` (§73). -/
instance (k : K) [DecidablePred k.Pinned] (s : S3) : Decidable (ExitPre k s) :=
  decidable_of_iff (s.F.tail ≠ [] ∧
    (∀ q ∈ List.range s.P.length, ({ s with F := s.F.tail } : S3).Usable q →
      ∀ x ∈ s.D q, firstSurv s s.F.tail (x :: s.ancs x) ≠ none) ∧
    (∀ a ∈ List.range s.A.length, Survives s s.F.tail a → s.org a ≠ none →
      firstSurv s s.F.tail (s.ancs a) ≠ none) ∧
    (∀ q ∈ List.range s.P.length, s.Usable q → ¬ ({ s with F := s.F.tail } : S3).Usable q →
      ∀ l ∈ footprint s.P q, s.pin l = false ∧ ¬ k.Pinned l) ∧
    AnchorOrderHeld (exitEff s))
    ⟨fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩, fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩⟩

/-- `exitFrame` as a relation (§73). -/
def ExitStep (k : K) (s : S3) : Outcome3 S3 → Prop := Guarded (ExitPre k s) (exitEff s)

/-! ## O9 `read`, O10 `write`, O11 `writeShared` (§66–§68) -/

/-- Leaf `l` belongs to a usable place (§66.1, §67.1, §68.1). -/
def LeafOfUsable (s : S3) (l : Nat) : Prop :=
  ∃ q ∈ List.range s.P.length, s.Usable q ∧ l ∈ footprint s.P q

/-- Decidability of `LeafOfUsable` (§66.1). -/
instance (s : S3) (l : Nat) : Decidable (LeafOfUsable s l) := by
  unfold LeafOfUsable; infer_instance

/-- Preconditions of `read` of the leaves `ls` through `access` (§66). The type and storage
contract of §66.3 is not represented. -/
structure Read3Pre (s : S3) (a : Nat) (ls : List Nat) : Prop where
  /-- §66.1: every leaf read belongs to a usable place. -/
  usable : ∀ l ∈ ls, LeafOfUsable s l
  /-- §66.1: every leaf read is `Init`. -/
  init : ∀ l ∈ ls, s.I l = .init
  /-- §66.2: `access` is exercisable in `Observe`. -/
  exercisable : s.ExercisableAt a .observe
  /-- §66.2: the effective mode of `access` permits observation of each leaf. -/
  effectivePresent : ∀ l ∈ ls, effective s a l ≠ none
  /-- §66.3: required anchors are valid. -/
  anchorsValid : ∀ l ∈ ls, DepsValid s l

/-- Decidability of the preconditions of `read` (§66). -/
instance (s : S3) (a : Nat) (ls : List Nat) : Decidable (Read3Pre s a ls) :=
  decidable_of_iff ((∀ l ∈ ls, LeafOfUsable s l) ∧ (∀ l ∈ ls, s.I l = .init) ∧
    s.ExercisableAt a .observe ∧ (∀ l ∈ ls, effective s a l ≠ none) ∧
    (∀ l ∈ ls, DepsValid s l))
    ⟨fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩, fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩⟩

/-- `read` as a relation (§66): the state is unchanged. -/
def Read3Step (a : Nat) (ls : List Nat) (s : S3) : Outcome3 S3 → Prop :=
  Guarded (Read3Pre s a ls) s

/-- Preconditions of an ordinary `write` of the leaves `ls` through `access` (§67). The type,
storage and abstraction constraints of §67.3 are not represented. -/
structure Write3Pre (s : S3) (a : Nat) (ls : List Nat) : Prop where
  /-- §67.1: targeted leaves belong to usable places. -/
  usable : ∀ l ∈ ls, LeafOfUsable s l
  /-- §67.1: `access` is exercisable in `Modify`. -/
  exercisable : s.ExercisableAt a .modify
  /-- §67.1: `access` has effective `Modify` over each leaf. -/
  effectiveModify : ∀ l ∈ ls, effective s a l = some .modify
  /-- §67.2: no other authority holds an effective mode, all incompatible with `Modify` (§50),
  over the written leaves. -/
  exclusive : ∀ l ∈ ls, ∀ b ∈ List.range s.A.length, b ≠ a → effective s b l = none
  /-- §67.3: anchors remain valid. -/
  anchorsValid : ∀ l ∈ ls, DepsValid s l

/-- Decidability of the preconditions of `write` (§67). -/
instance (s : S3) (a : Nat) (ls : List Nat) : Decidable (Write3Pre s a ls) :=
  decidable_of_iff ((∀ l ∈ ls, LeafOfUsable s l) ∧ s.ExercisableAt a .modify ∧
    (∀ l ∈ ls, effective s a l = some .modify) ∧
    (∀ l ∈ ls, ∀ b ∈ List.range s.A.length, b ≠ a → effective s b l = none) ∧
    (∀ l ∈ ls, DepsValid s l))
    ⟨fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩, fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩⟩

/-- Effect of a write (§67, §68, `ok` effect): the written leaves become `Init`. -/
def write3Eff (s : S3) (ls : List Nat) : S3 :=
  { s with I := fun p => if p ∈ ls then .init else s.I p }

/-- `write` as a relation (§67). -/
def Write3Step (a : Nat) (ls : List Nat) (s : S3) : Outcome3 S3 → Prop :=
  Guarded (Write3Pre s a ls) (write3Eff s ls)

/-- Preconditions of `writeShared` of the leaves `ls` through `access` (§68). -/
structure WriteSharedPre (k : K) (s : S3) (a : Nat) (ls : List Nat) : Prop where
  /-- §68.1: every leaf of the region is usable (belongs to a usable place). -/
  usable : ∀ l ∈ ls, LeafOfUsable s l
  /-- §68.1: every leaf of the region is declared `K.SharedMutable`. -/
  shared : ∀ l ∈ ls, k.SharedMutable l
  /-- §68.2: `access` is exercisable in a mode at least `Observe`. -/
  exercisable : s.ExercisableAt a .observe
  /-- §68.2: `access` has a present effective mode on every leaf. -/
  effectivePresent : ∀ l ∈ ls, effective s a l ≠ none
  /-- §68.3: dependencies are valid. -/
  depsValid : ∀ l ∈ ls, DepsValid s l

/-- Decidability of the preconditions of `writeShared` (§68). -/
instance (k : K) [DecidablePred k.SharedMutable] (s : S3) (a : Nat) (ls : List Nat) :
    Decidable (WriteSharedPre k s a ls) :=
  decidable_of_iff ((∀ l ∈ ls, LeafOfUsable s l) ∧ (∀ l ∈ ls, k.SharedMutable l) ∧
    s.ExercisableAt a .observe ∧ (∀ l ∈ ls, effective s a l ≠ none) ∧ (∀ l ∈ ls, DepsValid s l))
    ⟨fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩, fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩⟩

/-- `writeShared` as a relation (§68). -/
def WriteSharedStep (k : K) (a : Nat) (ls : List Nat) (s : S3) : Outcome3 S3 → Prop :=
  Guarded (WriteSharedPre k s a ls) (write3Eff s ls)

/-! ## Release of authorities whose holder dies (§69, §70) -/

/-- Releases every authority whose holder is no longer live (§69, §70 `ok` effects). -/
def cleanup (s : S3) : S3 :=
  { s with A := s.A.map fun y => if HolderLive s y.holder then y else { y with active := false } }

/-! ## O12 `endUse` (§69) -/

/-- `endUse p` before releasing authorities whose holder died (§69, `ok` effect): the leaves of
`p` become `Uninit`; authorities held within `p` are released; anchors of `p` and its parts are
removed; storage owned by `p`, transitively, is marked dead. -/
def endUseS (s : S3) (p : Nat) : S3 :=
  { s with
    I := fun l => if l ∈ footprint s.P p then .uninit else s.I l
    D := fun q => if partOf s.P q p then [] else s.D q
    dead := fun q => s.dead q || decide (OwnedIn s.P p q)
    A := s.A.map fun y => if heldIn s.P p y.holder then { y with active := false } else y }

/-- Effect of `endUse p` (§69, `ok` effect): `endUseS`, then the authorities whose holder died
are released. -/
def endUseEff (s : S3) (p : Nat) : S3 := cleanup (endUseS s p)

/-- Leaf whose use ends with the value at `p` (§69.2, §69.4): a leaf of `p` or of storage that
stops being usable. -/
def EndingLeaf (s : S3) (p l : Nat) : Prop :=
  l ∈ footprint s.P p ∨ (s.Usable l ∧ ¬ (endUseS s p).Usable l)

/-- Decidability of `EndingLeaf` (§69). -/
instance (s : S3) (p l : Nat) : Decidable (EndingLeaf s p l) := by
  unfold EndingLeaf; infer_instance

/-- Root authority of the value at `p` (§69.3): an authority with no origin covering a leaf of
`p`. -/
def IsRootOf (s : S3) (p : Nat) (y : Authority) : Prop :=
  y.origin = none ∧ ∃ l ∈ footprint s.P p, l ∈ y.footprint

/-- Decidability of `IsRootOf` (§69.3). -/
instance (s : S3) (p : Nat) (y : Authority) : Decidable (IsRootOf s p y) := by
  unfold IsRootOf; infer_instance

/-- Authority `j` does not block `endUse p` (§69.2): if it is an active derived authority over an
ending leaf, it is held within `p` or its holder dies. -/
def EndUseAccessOK (s : S3) (p j : Nat) : Prop :=
  OptP (s.A[j]?) (fun y => y.active = true → y.origin ≠ none →
    (∃ l ∈ y.footprint, EndingLeaf s p l) →
      heldIn s.P p y.holder ∨ ¬ HolderLive (endUseS s p) y.holder) True

/-- Decidability of `EndUseAccessOK` (§69.2). -/
instance (s : S3) (p j : Nat) : Decidable (EndUseAccessOK s p j) := by
  unfold EndUseAccessOK OptP; split <;> infer_instance

/-- Anchor `x` survives `endUse p` (§69.3): not held within `p`, not a root of `p`, with a holder
that stays live. -/
def EndUseAnchorOK (s : S3) (p x : Nat) : Prop :=
  OptP (s.A[x]?) (fun y => ¬ heldIn s.P p y.holder ∧ ¬ IsRootOf s p y ∧
    HolderLive (endUseS s p) y.holder) True

/-- Decidability of `EndUseAnchorOK` (§69.3). -/
instance (s : S3) (p x : Nat) : Decidable (EndUseAnchorOK s p x) := by
  unfold EndUseAnchorOK OptP; split <;> infer_instance

/-- Preconditions of `endUse` (§69). -/
structure EndUsePre (k : K) (s : S3) (p : Nat) : Prop where
  /-- §69.1: `place` is usable. -/
  usable : s.Usable p
  /-- §69.1: exercisable `Modify` over `place`. -/
  right : HasRight s .modify p
  /-- §69.2: no active derived authority over an ending leaf is held outside the dying places. -/
  access : ∀ j ∈ List.range s.A.length, EndUseAccessOK s p j
  /-- §69.3: no place usable after the effect depends on an authority held by `place`, its root,
  or an authority whose holder dies. -/
  anchors : ∀ q ∈ List.range s.P.length, (endUseS s p).Usable q →
    ∀ x ∈ (endUseS s p).D q, EndUseAnchorOK s p x
  /-- §69.4: no ending leaf, owned storage included, is pinned, statically or dynamically. -/
  notPinned : ∀ l ∈ List.range s.P.length, EndingLeaf s p l → s.pin l = false ∧ ¬ k.Pinned l

/-- Decidability of the preconditions of `endUse` (§69). -/
instance (k : K) [DecidablePred k.Pinned] (s : S3) (p : Nat) : Decidable (EndUsePre k s p) :=
  decidable_of_iff (s.Usable p ∧ HasRight s .modify p ∧
    (∀ j ∈ List.range s.A.length, EndUseAccessOK s p j) ∧
    (∀ q ∈ List.range s.P.length, (endUseS s p).Usable q →
      ∀ x ∈ (endUseS s p).D q, EndUseAnchorOK s p x) ∧
    (∀ l ∈ List.range s.P.length, EndingLeaf s p l → s.pin l = false ∧ ¬ k.Pinned l))
    ⟨fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩, fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩⟩

/-- `endUse` as a relation (§69). -/
def EndUseStep (k : K) (p : Nat) (s : S3) : Outcome3 S3 → Prop :=
  Guarded (EndUsePre k s p) (endUseEff s p)

/-! ## O13 `free` (§70) -/

/-- The holder is a place (§70.1). -/
def Holder.isPlace : Holder → Bool
  | .place _ => true
  | .frame _ => false

/-- `OwnedRoot` (§70.1): a place with no structural parent, owned by a place. -/
def OwnedRoot (s : S3) (p : Nat) : Prop :=
  OptP (s.P[p]?) (fun pl => pl.parent = none ∧ pl.owner.isPlace = true) False

/-- Decidability of `OwnedRoot` (§70.1). -/
instance (s : S3) (p : Nat) : Decidable (OwnedRoot s p) := by
  unfold OwnedRoot; infer_instance

/-- Place `q` belongs to the unit released by `free p` (§70): a part of `p`, or storage owned by
`p`, transitively. -/
def FreedPlace (P : List Place) (p q : Nat) : Prop := partOf P q p ∨ OwnedIn P p q

/-- Decidability of `FreedPlace` (§70). -/
instance (P : List Place) (p q : Nat) : Decidable (FreedPlace P p q) := by
  unfold FreedPlace; infer_instance

/-- `free p` before releasing authorities whose holder died (§70, `ok` effect): the released unit
is marked dead; authorities covering it, roots included, or held within `p` become inactive. -/
def freeS (s : S3) (p : Nat) : S3 :=
  { s with
    dead := fun q => s.dead q || decide (FreedPlace s.P p q)
    A := s.A.map fun y =>
      if (∃ l ∈ y.footprint, FreedPlace s.P p l) ∨ heldIn s.P p y.holder then
        { y with active := false } else y }

/-- Effect of `free p` (§70, `ok` effect): `freeS`, then the authorities whose holder died are
released. -/
def freeEff (s : S3) (p : Nat) : S3 := cleanup (freeS s p)

/-- Leaf of the released unit (§70.3, §70.4): a leaf of `p` or of storage that stops being
usable. -/
def FreedLeaf (s : S3) (p l : Nat) : Prop :=
  l ∈ footprint s.P p ∨ (s.Usable l ∧ ¬ (freeS s p).Usable l)

/-- Decidability of `FreedLeaf` (§70). -/
instance (s : S3) (p l : Nat) : Decidable (FreedLeaf s p l) := by
  unfold FreedLeaf; infer_instance

/-- Authority `j` does not block `free p` (§70.3): if it is an active derivative over the
footprint being freed, it is held within `p` or its holder dies. -/
def FreeAccessOK (s : S3) (p j : Nat) : Prop :=
  OptP (s.A[j]?) (fun y => y.active = true → y.origin ≠ none →
    (∃ l ∈ y.footprint, FreedLeaf s p l) →
      heldIn s.P p y.holder ∨ ¬ HolderLive (freeS s p) y.holder) True

/-- Decidability of `FreeAccessOK` (§70.3). -/
instance (s : S3) (p j : Nat) : Decidable (FreeAccessOK s p j) := by
  unfold FreeAccessOK OptP; split <;> infer_instance

/-- Anchor `x` survives `free p` (§70.3): it covers no leaf of the released unit, is not held
within `p`, and its holder stays live. -/
def FreeAnchorOK (s : S3) (p x : Nat) : Prop :=
  OptP (s.A[x]?) (fun y => ¬ (∃ l ∈ y.footprint, FreedPlace s.P p l) ∧ ¬ heldIn s.P p y.holder ∧
    HolderLive (freeS s p) y.holder) True

/-- Decidability of `FreeAnchorOK` (§70.3). -/
instance (s : S3) (p x : Nat) : Decidable (FreeAnchorOK s p x) := by
  unfold FreeAnchorOK OptP; split <;> infer_instance

/-- Preconditions of `free p auth` (§70). -/
structure FreePre (k : K) (s : S3) (p auth : Nat) : Prop where
  /-- §70.1: `place` is an `OwnedRoot`. -/
  ownedRoot : OwnedRoot s p
  /-- §70.2: `K.Deallocable(place)`. -/
  deallocable : k.Deallocable p
  /-- §70.2: `K.FreeCompat(place, auth)`. -/
  freeCompat : k.FreeCompat p auth
  /-- §70.3: exercisable `Modify` over `place`. -/
  right : HasRight s .modify p
  /-- §70.3: no active derivative over the footprint being freed is held outside dying
  holders. -/
  access : ∀ j ∈ List.range s.A.length, FreeAccessOK s p j
  /-- §70.3: no surviving place is anchored to an authority of the released unit or of its dead
  holders. -/
  anchors : ∀ q ∈ List.range s.P.length, (freeS s p).Usable q → ∀ x ∈ s.D q, FreeAnchorOK s p x
  /-- §70.4: no leaf of the released unit is pinned, statically or dynamically. -/
  notPinned : ∀ l ∈ List.range s.P.length, FreedLeaf s p l → s.pin l = false ∧ ¬ k.Pinned l

/-- Decidability of the preconditions of `free` (§70). -/
instance (k : K) [DecidablePred k.Pinned] [DecidablePred k.Deallocable]
    [∀ p a, Decidable (k.FreeCompat p a)] (s : S3) (p auth : Nat) :
    Decidable (FreePre k s p auth) :=
  decidable_of_iff (OwnedRoot s p ∧ k.Deallocable p ∧ k.FreeCompat p auth ∧
    HasRight s .modify p ∧ (∀ j ∈ List.range s.A.length, FreeAccessOK s p j) ∧
    (∀ q ∈ List.range s.P.length, (freeS s p).Usable q → ∀ x ∈ s.D q, FreeAnchorOK s p x) ∧
    (∀ l ∈ List.range s.P.length, FreedLeaf s p l → s.pin l = false ∧ ¬ k.Pinned l))
    ⟨fun ⟨a, b, c, d, e, f, g⟩ => ⟨a, b, c, d, e, f, g⟩,
     fun ⟨a, b, c, d, e, f, g⟩ => ⟨a, b, c, d, e, f, g⟩⟩

/-- `free` as a relation (§70). -/
def FreeStep (k : K) (p auth : Nat) (s : S3) : Outcome3 S3 → Prop :=
  Guarded (FreePre k s p auth) (freeEff s p)

/-! ## O14 `alloc` (§71) -/

/-- Static preconditions of `alloc provider owner shape` (§71, items 1–3). -/
structure AllocStatic (k : K) (s : S3) (provider owner : Nat) (ls : LocalShape) : Prop where
  /-- §71.1: the shape is nonempty. -/
  nonempty : ls ≠ []
  /-- §71.1: the shape is represented like the locals of `enterFrame` (each parent is an earlier
  element). -/
  shapeOK : ShapeOK s.P.length ls.toShape
  /-- §71.1 with the `ok` outcome of §71 ("a new storage root"): exactly one element has no
  parent. -/
  oneRoot : (rootIdx ls.toShape).length = 1
  /-- §71.2: all leaves of the provider are `Init`. -/
  providerInit : ∀ l ∈ footprint s.P provider, s.I l = .init
  /-- §71.2: metadata updates are permitted through exercisable `Modify` on the provider or a
  valid `writeShared` (§68) over its leaves. -/
  providerRight : HasRight s .modify provider ∨
    ∃ via ∈ List.range s.A.length, WriteSharedPre k s via (footprint s.P provider)
  /-- §71.3: exercisable `Modify` over `owner`. -/
  ownerRight : HasRight s .modify owner
  /-- §71.3 (liveness restrictions): `owner` is usable. -/
  ownerUsable : s.Usable owner

/-- Decidability of the static preconditions of `alloc` (§71). -/
instance (k : K) [DecidablePred k.SharedMutable] (s : S3) (provider owner : Nat)
    (ls : LocalShape) : Decidable (AllocStatic k s provider owner ls) :=
  decidable_of_iff (ls ≠ [] ∧ ShapeOK s.P.length ls.toShape ∧ (rootIdx ls.toShape).length = 1 ∧
    (∀ l ∈ footprint s.P provider, s.I l = .init) ∧
    (HasRight s .modify provider ∨
      ∃ via ∈ List.range s.A.length, WriteSharedPre k s via (footprint s.P provider)) ∧
    HasRight s .modify owner ∧ s.Usable owner)
    ⟨fun ⟨a, b, c, d, e, f, g⟩ => ⟨a, b, c, d, e, f, g⟩,
     fun ⟨a, b, c, d, e, f, g⟩ => ⟨a, b, c, d, e, f, g⟩⟩

/-- Places after `alloc` (§71, `ok` outcome): the elements of the shape appended, owned by
`owner`. -/
def allocP (s : S3) (owner : Nat) (ls : LocalShape) : List Place :=
  shapeP s.P (.place owner) ls.toShape

/-- Effect of `alloc` (§71, `ok` outcome): a new storage root of fresh identities owned by
`owner`, its leaves `Uninit`, no anchor, alive, unpinned, with a root `Modify` authority with no
origin held by `owner`. -/
def allocEff (s : S3) (owner : Nat) (ls : LocalShape) : S3 :=
  { s with
    P := allocP s owner ls
    I := fun l => if s.P.length ≤ l then .uninit else s.I l
    A := s.A ++ (rootIdx ls.toShape).map fun i =>
      ⟨.modify, none, footprint (allocP s owner ls) (s.P.length + i),
        shapeOwner ls.toShape (.place owner) i, true⟩
    D := fun q => if s.P.length ≤ q then [] else s.D q
    dead := fun q => if s.P.length ≤ q then false else s.dead q
    pin := fun q => if s.P.length ≤ q then false else s.pin q }

/-- `alloc provider owner shape` as a relation (§71 outcomes, §58): `reject` when a static
precondition fails; `fail`, state unchanged, when `K.Satisfiable` is false; `ok` otherwise. -/
inductive AllocStep (k : K) (provider owner : Nat) (ls : LocalShape) (s : S3) :
    Outcome3 S3 → Prop where
  | ok : AllocStatic k s provider owner ls → k.Satisfiable provider ls s →
      AllocStep k provider owner ls s (.ok (allocEff s owner ls))
  | fail : AllocStatic k s provider owner ls → ¬ k.Satisfiable provider ls s →
      AllocStep k provider owner ls s .fail
  | reject : ¬ AllocStatic k s provider owner ls → AllocStep k provider owner ls s .reject

/-! ## O15 `pin`, O16 `unpin` (§74, §75) -/

/-- Preconditions of `pin` (§74). "Applicable pinning obligations" is not represented. -/
structure PinPre (s : S3) (p : Nat) : Prop where
  /-- §74: `place` is usable. -/
  usable : s.Usable p
  /-- §74: exercisable `Modify` over the leaves of `place`. -/
  right : HasRight s .modify p

/-- Decidability of the preconditions of `pin` (§74). -/
instance (s : S3) (p : Nat) : Decidable (PinPre s p) :=
  decidable_of_iff (s.Usable p ∧ HasRight s .modify p)
    ⟨fun ⟨a, b⟩ => ⟨a, b⟩, fun ⟨a, b⟩ => ⟨a, b⟩⟩

/-- Effect of `pin` (`b = true`, §74) and `unpin` (`b = false`, §75): the dynamic pinning flag of
the leaves of `place`. -/
def pinEff (s : S3) (p : Nat) (b : Bool) : S3 :=
  { s with pin := fun l => if l ∈ footprint s.P p then b else s.pin l }

/-- `pin` as a relation (§74). -/
def PinStep (p : Nat) (s : S3) : Outcome3 S3 → Prop := Guarded (PinPre s p) (pinEff s p true)

/-- Preconditions of `unpin` (§75). -/
structure UnpinPre (k : K) (s : S3) (p : Nat) : Prop where
  /-- §75: `place` is usable. -/
  usable : s.Usable p
  /-- §75: exercisable `Modify` over `place`. -/
  right : HasRight s .modify p
  /-- §75: `K.ExternalDone(place)`. -/
  externalDone : k.ExternalDone p

/-- Decidability of the preconditions of `unpin` (§75). -/
instance (k : K) [DecidablePred k.ExternalDone] (s : S3) (p : Nat) :
    Decidable (UnpinPre k s p) :=
  decidable_of_iff (s.Usable p ∧ HasRight s .modify p ∧ k.ExternalDone p)
    ⟨fun ⟨a, b, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨a, b, c⟩⟩

/-- `unpin` as a relation (§75). -/
def UnpinStep (k : K) (p : Nat) (s : S3) : Outcome3 S3 → Prop :=
  Guarded (UnpinPre k s p) (pinEff s p false)

/-! ## Kernel steps (§57, §58) -/

/-- One `ok` transition of a kernel operation O1–O16 (§60–§75; §57 reachability). -/
inductive KStep (k : K) : S3 → S3 → Prop where
  | derive {s s' : S3} {src : Nat} {region : List Nat} {m : Mode} :
      DeriveStep src region m s (.ok s') → KStep k s s'
  | split {s s' : S3} {src : Nat} {rs : List (List Nat)} :
      SplitStep k src rs s (.ok s') → KStep k s s'
  | release {s s' : S3} {a : Nat} : ReleaseStep a s (.ok s') → KStep k s s'
  | transfer {s s' : S3} {src dst : Nat} : TransferStep k src dst s (.ok s') → KStep k s s'
  | depend {s s' : S3} {q x : Nat} : DependStep q x s (.ok s') → KStep k s s'
  | enter {s s' : S3} {ps : List Nat} {ls : LocalShape} :
      EnterStep ps ls s (.ok s') → KStep k s s'
  | exit {s s' : S3} : ExitStep k s (.ok s') → KStep k s s'
  | read {s s' : S3} {a : Nat} {ls : List Nat} : Read3Step a ls s (.ok s') → KStep k s s'
  | write {s s' : S3} {a : Nat} {ls : List Nat} : Write3Step a ls s (.ok s') → KStep k s s'
  | writeShared {s s' : S3} {a : Nat} {ls : List Nat} :
      WriteSharedStep k a ls s (.ok s') → KStep k s s'
  | pin {s s' : S3} {p : Nat} : PinStep p s (.ok s') → KStep k s s'
  | unpin {s s' : S3} {p : Nat} : UnpinStep k p s (.ok s') → KStep k s s'
  | endUse {s s' : S3} {p : Nat} : EndUseStep k p s (.ok s') → KStep k s s'
  | free {s s' : S3} {p auth : Nat} : FreeStep k p auth s (.ok s') → KStep k s s'
  | alloc {s s' : S3} {pr ow : Nat} {ls : LocalShape} :
      AllocStep k pr ow ls s (.ok s') → KStep k s s'
  | store {s s' : S3} {a p : Nat} : StoreStep a p s (.ok s') → KStep k s s'

end Ern.MemoryModel.Access
