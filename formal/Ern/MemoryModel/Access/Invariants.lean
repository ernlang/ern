import Ern.MemoryModel.Access.Ops

/-!
# Access kernel: invariants, initial state, reachability

Invariants of `specs/ERN_Memory_Model_Specification_v0.1.md`: `WF3` (§49), `I1`–`I4` (§50–§53),
`NoDangling` and `NoOrphan` (§54), `Inv3` and `I5` (§57), the declared statics and `S3.init`
(§47), `StaticPinnedBottom` (§75), and reachability from `S3.init statics` under the kernel steps
O1–O16 (§57). `AnchorOrder` and `AnchorOrderHeld` (§44) are in
`Ern.MemoryModel.Access.Basic`, since operations read them.
-/

namespace Ern.MemoryModel.Access

/-! ## Root places and root authorities (§40, §49) -/

/-- Root place (§40): an existing place with no structural parent. -/
def RootPlace (P : List Place) (r : Nat) : Prop := r < P.length ∧ parentOf P r = none

/-- Decidability of `RootPlace` (§40). -/
instance (P : List Place) (r : Nat) : Decidable (RootPlace P r) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- `RootChain` (§49.6): the origin chain of an authority covering a leaf ends at a root
authority (no origin) whose footprint is the footprint of a root place containing that leaf. -/
def RootChain (s : S3) : Prop :=
  ∀ (a : Nat) (y : Authority) (l : Nat), s.A[a]? = some y → l ∈ y.footprint → isLeaf s.P l →
    ∃ x z r, (x = a ∨ x ∈ s.ancs a) ∧ s.A[x]? = some z ∧ z.origin = none ∧ RootPlace s.P r ∧
      partOf s.P l r ∧ ∀ l', l' ∈ z.footprint ↔ l' ∈ footprint s.P r

/-- `RootHeld` (§49.7, §40): every usable root place has an active root authority of own mode
`Modify`, with no origin, held by the owner of the place, whose footprint is the footprint of the
place. -/
def RootHeld (s : S3) : Prop :=
  ∀ r, RootPlace s.P r → s.Usable r → ∃ (i : Nat) (z : Authority) (pr : Place),
    s.A[i]? = some z ∧ z.active = true ∧ z.origin = none ∧ z.mode = .modify ∧
    s.P[r]? = some pr ∧ z.holder = pr.owner ∧ ∀ l, l ∈ z.footprint ↔ l ∈ footprint s.P r

/-- Auxiliary converse of `RootHeld` (§40, §49.7), not a clause of `WF3`: an authority with no
origin is held by the owner of the root place of every leaf it covers. -/
def RootHeldConv (s : S3) : Prop :=
  ∀ (x : Nat) (z : Authority) (l r : Nat), s.A[x]? = some z → z.origin = none → l ∈ z.footprint →
    RootPlace s.P r → partOf s.P l r → ∃ pr, s.P[r]? = some pr ∧ z.holder = pr.owner

/-! ## `WF3` (§49) -/

/-- `WF3(s)` (§49): one field per item of §49. Index order of parents and origins represents
acyclicity (§49, last paragraph). -/
structure WF3 (s : S3) : Prop where
  /-- §49.1: the stack is nonempty and duplicate-free, every frame below `nF`. -/
  frames : s.F ≠ [] ∧ s.F.Nodup ∧ ∀ f ∈ s.F, f < s.nF
  /-- §49.2: parent links are valid and acyclic (the parent precedes the child); a part shares
  its parent's owner and death marker. -/
  places : ∀ (q : Nat) (pl : Place) (r : Nat), s.P[q]? = some pl → pl.parent = some r →
    ∃ pr : Place, s.P[r]? = some pr ∧ r < q ∧ pr.owner = pl.owner ∧ s.dead r = s.dead q
  /-- §49.3: owner frames are below `nF`; owner places exist; the ownership chain of every usable
  place is finite and reaches a live frame. -/
  owners : (∀ (q : Nat) (pl : Place) (f : Nat), s.P[q]? = some pl → pl.owner = .frame f →
      f < s.nF) ∧
    (∀ (q : Nat) (pl : Place) (o : Nat), s.P[q]? = some pl → pl.owner = .place o →
      o < s.P.length) ∧
    ∀ q, s.Usable q → ∃ f, FrameOf s q f ∧ f ∈ s.F
  /-- §49.4: footprints consist of leaves of existing places. -/
  footprints : ∀ (a : Nat) (x : Authority), s.A[a]? = some x → ∀ l ∈ x.footprint,
    l < s.P.length ∧ isLeaf s.P l
  /-- §49.5: an existing origin precedes the authority, so origin chains are acyclic and end at a
  root authority. -/
  origins : ∀ (b : Nat) (y : Authority) (a : Nat), s.A[b]? = some y → y.origin = some a → a < b
  /-- §49.6: `RootChain`. -/
  rootChain : RootChain s
  /-- §49.7: `RootHeld`. -/
  rootHeld : RootHeld s
  /-- §49.8: every active authority is held by a frame of the stack or by a usable place. -/
  holders : ∀ (a : Nat) (y : Authority), s.A[a]? = some y → y.active = true →
    HolderLive s y.holder

/-! ## `I1`–`I4`, `NoDangling`, `Inv3` (§50–§54, §57) -/

/-- `I1` (§50): two distinct active authorities unrelated by derivation covering a common leaf
both have own mode `Observe`. -/
def I1 (s : S3) : Prop :=
  ∀ (a b : Nat) (x y : Authority) (p : Nat), a ≠ b → s.A[a]? = some x → s.A[b]? = some y →
    x.active = true → y.active = true → p ∈ x.footprint → p ∈ y.footprint →
    a ∉ s.ancs b → b ∉ s.ancs a → x.mode = .observe ∧ y.mode = .observe

/-- `I2` (§51): the origin of a derived authority exists; the derived mode does not exceed the
origin's, the derived footprint is within the origin's, and the origin of an active derived
authority is valid, that is, active. -/
def I2 (s : S3) : Prop :=
  ∀ (b : Nat) (y : Authority) (a : Nat), s.A[b]? = some y → y.origin = some a →
    ∃ x : Authority, s.A[a]? = some x ∧ y.mode.le x.mode ∧ (∀ p ∈ y.footprint, p ∈ x.footprint) ∧
      (y.active = true → x.active = true)

/-- `I3` (§52): every anchor of a usable place is valid (active). -/
def I3 (s : S3) : Prop := ∀ q, s.Usable q → ∀ x ∈ s.D q, s.Active x

/-- `I4` (§53, first sentence): no read of a region containing a `Moved` leaf is permitted. -/
def I4 (s : S3) : Prop := ∀ (a : Nat) (ls : List Nat) (l : Nat), l ∈ ls → s.I l = .moved →
  ¬ Read3Pre s a ls

/-- `I1 ∧ I2 ∧ I3 ∧ I4` (§57). -/
def Inv3base (s : S3) : Prop := I1 s ∧ I2 s ∧ I3 s ∧ I4 s

/-- `NoDangling` (§54): no active authority covers a leaf of an unusable place. -/
def NoDangling (s : S3) : Prop :=
  ∀ (j : Nat) (y : Authority), s.A[j]? = some y → y.active = true →
    ∀ q, ¬ s.Usable q → ∀ l ∈ footprint s.P q, l ∉ y.footprint

/-- `Inv3 = I1 ∧ I2 ∧ I3 ∧ I4 ∧ AnchorOrder ∧ NoDangling` (§57). -/
def Inv3 (s : S3) : Prop := Inv3base s ∧ AnchorOrder s ∧ NoDangling s

/-- `I5` (§57): every pinned leaf, statically (`K.Pinned`) or dynamically (an active pinning
obligation, §74), belongs to a usable place. The quantifier ranges over the leaves of the state
(§40): `K.Pinned` on an index that is not a leaf of `s` is not constrained. A specialized
obligation of `K.Pinned`, not a conjunct of the main invariant (§57). -/
def I5 (k : K) (s : S3) : Prop :=
  ∀ l, l < s.P.length → isLeaf s.P l → (k.Pinned l ∨ s.pin l = true) →
    ∃ q, s.Usable q ∧ l ∈ footprint s.P q

/-! ## `NoOrphan` (§54) -/

/-- One link of a `NoOrphan` chain (§54): `a` is active and structurally covers every leaf of the
place holding `b`. -/
def CoversHolder (s : S3) (a b : Nat) : Prop :=
  OptP (s.A[b]?) (fun z => match z.holder with
    | .place q => s.Active a ∧ ∀ l ∈ footprint s.P q, l ∈ s.afp a
    | .frame _ => False) False

/-- Consecutive elements of a list are related by `R` (§54, chains of `NoOrphan`). -/
def Linked (R : Nat → Nat → Prop) : List Nat → Prop
  | a :: b :: c => R a b ∧ Linked R (b :: c)
  | _ => True

/-- `NoOrphan` (§54): every active authority held by a place ends a finite, non-repeating chain of
authorities whose first link is active and held by a frame of the stack, each link covering the
whole place holding the next. -/
def NoOrphan (s : S3) : Prop :=
  ∀ (x : Nat) (y : Authority) (q : Nat), s.A[x]? = some y → y.active = true → y.holder = .place q →
    ∃ (a₀ : Nat) (z : Authority) (f : Nat) (c : List Nat), s.A[a₀]? = some z ∧ z.active = true ∧
      z.holder = .frame f ∧ f ∈ s.F ∧ (a₀ :: c).Nodup ∧ (a₀ :: c).getLast? = some x ∧
      Linked (CoversHolder s) (a₀ :: c)

/-! ## Initial state (§47) -/

/-- Declared static storage (§47): each element is (parent, owning static, kind) with its
initial state, `true` for `Init` and `false` for `Uninit` (read on leaves only). -/
abbrev Statics := List ((Option Nat × Option Nat × Nat) × Bool)

/-- Well-formed statics declaration (§47: the ownership graph of statics is acyclic; §49, last
paragraph: the ordering of identifiers represents this well-foundedness, and that of structural
parents): parents and owning statics are earlier statics, and a part has its parent's owning
static (§49.2). -/
def StaticsOK (statics : Statics) : Prop := ShapeOK 0 (statics.map (·.1))

/-- Decidability of `StaticsOK` (§47). -/
instance (statics : Statics) : Decidable (StaticsOK statics) := by
  unfold StaticsOK; infer_instance

/-- `S3.init statics` (§47): base frame 0 and the declared statics, owned by frame 0 or by
another static; one root `Modify` authority with no origin per root static, held by its owner;
leaves `Init` or `Uninit` as declared; no anchor, no derived authority, nothing dead, no
dynamic pinning obligation. -/
def S3.init (statics : Statics) : S3 :=
  { F := [0]
    nF := 1
    P := shapeP [] (.frame 0) (statics.map (·.1))
    I := fun l => if ((statics[l]?).map (·.2)).getD false then .init else .uninit
    A := (rootIdx (statics.map (·.1))).map fun i =>
      ⟨.modify, none, footprint (shapeP [] (.frame 0) (statics.map (·.1))) i,
        shapeOwner (statics.map (·.1)) (.frame 0) i, true⟩
    D := fun _ => []
    dead := fun _ => false
    pins := [] }

/-- `StaticPinnedBottom` (§75, §80): every static place whose leaf is designated by `K.Pinned` is
directly owned by the base frame 0. A condition on `(K, statics)`. -/
def StaticPinnedBottom (k : K) (statics : Statics) : Prop :=
  ∀ l < statics.length, k.Pinned l →
    OptP ((S3.init statics).P[l]?) (fun pl => pl.owner = .frame 0) False

/-! ## Reachability (§57) -/

/-- States reachable from `S3.init statics` under the kernel steps O1–O16 (§57). -/
inductive Reachable (k : K) (statics : Statics) : S3 → Prop where
  | init : Reachable k statics (S3.init statics)
  | step {s s' : S3} : Reachable k statics s → KStep k s s' → Reachable k statics s'

/-! ## Non-vacuity examples (§47, §60–§75)

Each operation has an accepting state, decided by `decide` on concrete states built from
`S3.init`; a few rejections are included. -/

namespace Examples

/-- Test contract (§48): nothing declared disjoint or pinned, every leaf `SharedMutable`, every
external use done, every place deallocable, every request satisfiable. -/
def K0 : K := ⟨fun _ _ => False, fun _ => True, fun _ => False, fun _ => True, fun _ => True,
  fun _ _ => True, fun _ _ _ => True⟩

/-- Decidability of `K0.DeclaredDisjoint` (§48). -/
instance : ∀ r r', Decidable (K0.DeclaredDisjoint r r') :=
  fun _ _ => inferInstanceAs (Decidable False)
/-- Decidability of `K0.SharedMutable` (§48). -/
instance : DecidablePred K0.SharedMutable := fun _ => inferInstanceAs (Decidable True)
/-- Decidability of `K0.Pinned` (§48). -/
instance : DecidablePred K0.Pinned := fun _ => inferInstanceAs (Decidable False)
/-- Decidability of `K0.ExternalDone` (§48). -/
instance : DecidablePred K0.ExternalDone := fun _ => inferInstanceAs (Decidable True)
/-- Decidability of `K0.Deallocable` (§48). -/
instance : DecidablePred K0.Deallocable := fun _ => inferInstanceAs (Decidable True)
/-- Decidability of `K0.FreeCompat` (§48). -/
instance : ∀ p a, Decidable (K0.FreeCompat p a) := fun _ _ => inferInstanceAs (Decidable True)

/-- Three static leaves owned by frame 0 (§47): place 0 `Init`, places 1 and 2 `Uninit`. -/
def st : Statics := [((none, none, 0), true), ((none, none, 0), false), ((none, none, 0), false)]

/-- `S3.init st` (§47). -/
def s0 : S3 := S3.init st
/-- After `derive(0, [0], Modify)` (§60): authority 3 held by frame 0. -/
def s1 : S3 := deriveEff s0 0 [0] .modify
/-- After `alloc(provider 0, owner 1, one leaf)` (§71): place 3 owned by place 1, root 3. -/
def s2 : S3 := allocEff s0 1 [(none, 0)]
/-- After `derive(1, [1], Modify)` then `store(3, 0)` (§60, §65): authority 3 on leaf 1 stored in
place 0. -/
def s3 : S3 := storeEff (deriveEff s0 1 [1] .modify) 3 0
/-- After `pin(0)` (§74): obligation 0 pins leaf 0. -/
def s4 : S3 := pinEff s0 0

example : StaticsOK st := by decide
example : DerivePre s0 0 [0] .modify := by decide
example : SplitPre K0 s0 0 [[0]] := by decide
example : ReleasePre s1 3 := by decide
example : TransferPre K0 s0 0 1 := by decide
example : ¬ TransferPre K0 s0 1 0 := by decide
example : DependPre s1 2 3 := by decide
example : EnterPre s1 [3] [(none, 0), (some 3, 0)] := by decide
example : StorePre s1 3 1 := by decide
example : ¬ ExitPre K0 s0 := by decide
example : Read3Pre s0 0 [0] := by decide
example : Write3Pre s0 1 [1] := by decide
example : WriteSharedPre K0 s0 0 [0] := by decide
example : EndUsePre K0 s0 0 := by decide
example : FreePre K0 s2 3 0 := by decide
example : AllocStatic K0 s0 0 1 [(none, 0), (some 3, 0)] := by decide
example : ¬ AllocStatic K0 s0 0 1 [(none, 0), (none, 0)] := by decide
example : PinPre s0 0 := by decide
example : UnpinPre K0 s4 0 := by decide
example : ¬ UnpinPre K0 s0 0 := by decide
example : ¬ EndUsePre K0 s4 0 := by decide

/-- §75: `unpin` ends only the designated obligation; with two obligations on leaf 0, ending
obligation 0 leaves the leaf pinned by obligation 1. -/
example : (unpinEff (pinEff s4 0) 0).pin 0 = true ∧ (unpinEff s4 0).pin 0 = false := by decide

/-- §63.8 decides alone: in `s3`, the transfer of place 0 to place 1 satisfies §63.1–§63.7 and
§63.9 and is rejected by local self-blocking prevention. -/
example : (s3.Usable 0 ∧ s3.Usable 1 ∧ HasRight s3 .modify 0 ∧ HasRight s3 .modify 1 ∧
    SameShape s3.P 0 1 ∧ (∀ l ∈ footprint s3.P 0, s3.I l = .init) ∧
    (∀ l ∈ footprint s3.P 1, s3.I l ≠ .init) ∧ ¬ overlap s3.P 0 1 ∧
    (∃ g ∈ List.range s3.A.length, Grounds s3 .modify 0 g ∧
      ∀ j ∈ List.range s3.A.length, ActiveDerivedOutside s3 0 j → RightChain s3 g j) ∧
    (∀ l ∈ footprint s3.P 0, ¬ K0.Pinned l ∧ s3.pin l = false) ∧
    (∀ x ∈ movedDeps s3 0, s3.Active x) ∧ AnchorOrder (transferEff s3 0 1) ∧
    (∀ x ∈ List.range s3.A.length, AnchorMoves s3 0 x →
      ∀ q ∈ List.range s3.P.length, (transferEff s3 0 1).Usable q →
        OptP ((transferEff s3 0 1).A[x]?) (fun y => y.active = true → y.holder = .place q →
          EffAnchorOK (transferEff s3 0 1) x ((transferEff s3 0 1).pframe q)) True) ∧
    (transferEff s3 0 1).Usable 1) ∧
    ¬ NoLocalSelfLock s3 0 1 ∧ ¬ TransferPre K0 s3 0 1 := by decide

end Examples

end Ern.MemoryModel.Access
