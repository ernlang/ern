import Ern.MemoryModel.Access.Main

/-!
# Arenas: the reference library abstraction (Part XIV)

Arenas of `specs/ERN_Memory_Model_Specification_v0.1.md`, Part XIV (§76–§78), with §36, §46, §55,
§56, §58, §79, §86 and §88. An arena is a library abstraction (Part XIV): its entries live in a
library state separate from the kernel state `S₃` (§38, §46). `newArena` (O17) only registers an
entry; `issue` (O18) and `reset` (O19) are defined twice:

* as their contracts, clause by clause (§77, §78): `IssueC`, `ResetC`;
* as derived operations over the kernel steps (Part XIV): `issue` is its static checks, the
  availability `fail`, then `split` of `internal` on the region and `store` of the block into the
  destination (`IssueD`); `reset` is `derive` of `internal` at `Modify` over the whole storage,
  then `release`, then the explicit check of §78.3 (`ResetD`), which never rejects after an
  accepted `derive` on states satisfying I3 (`resetNoDeps_of_derive`).

On library-reachable states, `issue_as_kernel` and `reset_as_kernel` show that both definitions
have the same outcomes and the same arrival states, and `lReach_inv` that every live entry
satisfies `ArenaInv` (§55). Library reachability (`LReach`, `LReachNG`) uses the derived
operations, so its kernel states are kernel-reachable (`newArena_as_library`) and satisfy the
kernel invariant of §57 (`Access.reachable_kinv`).
-/

namespace Ern.MemoryModel.Arena

open Ern.MemoryModel.Access

/-! ## Library state (§46) -/

/-- Arena entry (§46): administered storage, `internal` authority, available leaves and issued
regions with their block authorities. The sets of §46 are lists read by membership. -/
structure ArenaEntry where
  storage : Nat
  internal : Nat
  available : List Nat
  issued : List (List Nat × Nat)
deriving DecidableEq, Repr

/-- Library state (§46, §38): the kernel state `S₃` and, separately, the arena registry. -/
structure LState where
  kern : S3
  arenas : List ArenaEntry

/-- Initial library state (§47): the initial kernel state and an empty arena registry. -/
def LState.init (statics : Statics) : LState := ⟨S3.init statics, []⟩

/-- Live arena (§46): `internal` is active. -/
def Live (s : S3) (E : ArenaEntry) : Prop := s.Active E.internal

/-- Decidability of `Live` (§46). -/
instance (s : S3) (E : ArenaEntry) : Decidable (Live s E) :=
  inferInstanceAs (Decidable (s.Active _))

/-- Arena value (§46): the place holding `internal`. -/
def arenaValue (s : S3) (E : ArenaEntry) : Option Nat :=
  match s.A[E.internal]? with
  | some y => match y.holder with
    | .place v => some v
    | .frame _ => none
  | none => none

/-- `MetaRight(s, arena)` (§36, §77.1, §78.1): exercisable `Modify` over the arena value; there is
no `writeShared` branch. -/
def MetaRight (s : S3) (E : ArenaEntry) : Prop :=
  OptP (arenaValue s E) (fun v => HasRight s .modify v) False

/-- Decidability of `MetaRight` (§36). -/
instance (s : S3) (E : ArenaEntry) : Decidable (MetaRight s E) := by
  unfold MetaRight; infer_instance

/-- Available region (§46): each of its leaves belongs to `available`; the empty region is always
available. -/
def Avail (E : ArenaEntry) (region : List Nat) : Prop := ∀ l ∈ region, l ∈ E.available

/-- Decidability of `Avail` (§46). -/
instance (E : ArenaEntry) (region : List Nat) : Decidable (Avail E region) := by
  unfold Avail; infer_instance

/-! ## `ArenaInv` (§55) -/

/-- `ArenaInv` (§55), required for live arenas. "Still-issued" is read as "with an active block
authority". The clause "anchor and ownership restrictions are respected" has no referent and is
not represented; "complying with exclusivity and validity rules" is left to the kernel
invariants (§57). -/
structure ArenaInv (s : S3) (E : ArenaEntry) : Prop where
  /-- §55, item 1: `storage` designates an existing, usable place. -/
  storageUsable : s.Usable E.storage
  /-- §55, item 1: the footprint of `internal` is exactly the footprint of `storage`. -/
  fpEq : ∀ l, l ∈ s.afp E.internal ↔ l ∈ footprint s.P E.storage
  /-- §55, item 2: `internal` is active. -/
  active : s.Active E.internal
  /-- §55, item 2: `internal` has own mode `Modify` and is held by a place, the arena value. -/
  shape : OptP (s.A[E.internal]?) (fun y => y.mode = .modify ∧ y.holder.isPlace = true) False
  /-- §55, item 3: available leaves belong to the administered storage. -/
  availableIn : ∀ l ∈ E.available, l ∈ footprint s.P E.storage
  /-- §55, item 3: issued regions belong to the administered storage. -/
  issuedIn : ∀ e ∈ E.issued, ∀ l ∈ e.1, l ∈ footprint s.P E.storage
  /-- §55, item 4: two still-active issuances have disjoint regions. -/
  disjoint : ∀ e ∈ E.issued, ∀ e' ∈ E.issued, e ≠ e' → s.Active e.2 → s.Active e'.2 →
    ∀ l ∈ e.1, l ∉ e'.1
  /-- §55, item 4: no leaf of a still-issued region belongs to `available`. -/
  notAvailable : ∀ e ∈ E.issued, s.Active e.2 → ∀ l ∈ e.1, l ∉ E.available
  /-- §55, item 5: every still-issued block authority is a derivative of `internal`. -/
  derived : ∀ e ∈ E.issued, s.Active e.2 → E.internal ∈ s.ancs e.2

/-- Decidability of `ArenaInv` (§55): the footprint equality is the two inclusions. -/
instance (s : S3) (E : ArenaEntry) : Decidable (ArenaInv s E) :=
  @decidable_of_iff (ArenaInv s E) ((s.Usable E.storage ∧
    (∀ l ∈ s.afp E.internal, l ∈ footprint s.P E.storage) ∧
    (∀ l ∈ footprint s.P E.storage, l ∈ s.afp E.internal) ∧ s.Active E.internal ∧
    OptP (s.A[E.internal]?) (fun y => y.mode = .modify ∧ y.holder.isPlace = true) False) ∧
    ((∀ l ∈ E.available, l ∈ footprint s.P E.storage) ∧
    (∀ e ∈ E.issued, ∀ l ∈ e.1, l ∈ footprint s.P E.storage)) ∧
    (∀ e ∈ E.issued, ∀ e' ∈ E.issued, e ≠ e' → s.Active e.2 → s.Active e'.2 →
      ∀ l ∈ e.1, l ∉ e'.1) ∧
    (∀ e ∈ E.issued, s.Active e.2 → ∀ l ∈ e.1, l ∉ E.available) ∧
    (∀ e ∈ E.issued, s.Active e.2 → E.internal ∈ s.ancs e.2))
    ⟨fun ⟨⟨a, b, c, d, e⟩, ⟨f, g⟩, h, i, j⟩ => ⟨a, fun l => ⟨b l, c l⟩, d, e, f, g, h, i, j⟩,
     fun h => ⟨⟨h.storageUsable, fun l => (h.fpEq l).1, fun l => (h.fpEq l).2, h.active,
      h.shape⟩, ⟨h.availableIn, h.issuedIn⟩, h.disjoint, h.notAvailable, h.derived⟩⟩
    (@instDecidableAnd _ _ inferInstance (@instDecidableAnd _ _ inferInstance inferInstance))

/-- Shape of the issued blocks (support for §55, item 5, from the `ok` effect of §77; not a clause
of `ArenaInv`): every issued block authority exists, has direct origin `internal`, a fresh identity
above it, its region as footprint and mode `Modify`. -/
def IssuedShape (s : S3) (E : ArenaEntry) : Prop :=
  ∀ e ∈ E.issued, ∃ y, s.A[e.2]? = some y ∧ y.origin = some E.internal ∧ E.internal < e.2 ∧
    y.footprint = e.1 ∧ y.mode = .modify

/-- The per-entry library invariant (§55): `ArenaInv` and the auxiliary `IssuedShape`. -/
def EntryInv (s : S3) (E : ArenaEntry) : Prop := ArenaInv s E ∧ IssuedShape s E

/-- The library invariant (§55, §46): every registered `internal` exists, and every live entry
satisfies `EntryInv`. -/
def LInv (L : LState) : Prop :=
  ∀ E ∈ L.arenas, E.internal < L.kern.A.length ∧ (Live L.kern E → EntryInv L.kern E)

/-! ## A decision procedure for the kernel invariant on concrete states (§49–§54, §57)

`KInvB` restates `KInv ∧ KAux` with every quantifier bounded by the lists of the state, so that
`decide` evaluates it on the concrete states of the witnesses below; `KInvB.sound` derives
`KInv ∧ KAux`. `WF3` (§49) and `I1` (§50), which §76.6 asks of the resulting state of `newArena`,
are decidable through their bounded forms (`wf3_iff_kb`, `i1_iff_kb`). -/

/-- A leaf of the footprint of `q` makes `q` an existing place (§40). -/
theorem footprint_lt {P : List Place} {q l : Nat} (h : l ∈ footprint P q) : q < P.length := by
  obtain ⟨hl, -, -, hlq⟩ := mem_footprint.1 h
  rcases hlq with rfl | hc
  · exact hl
  · exact Nat.lt_trans (chain_lt hc) hl

/-- The footprint of the authority record `z` is the footprint of place `r` (§49.6, §49.7). -/
def FpIs (s : S3) (z : Authority) (r : Nat) : Prop :=
  (∀ l ∈ z.footprint, l ∈ footprint s.P r) ∧ ∀ l ∈ footprint s.P r, l ∈ z.footprint

/-- Decidability of `FpIs` (§49.6). -/
instance (s : S3) (z : Authority) (r : Nat) : Decidable (FpIs s z r) := by
  unfold FpIs; infer_instance

/-- The record `z` is a root authority for the root place of leaf `l` (§49.6). -/
def RootFor (s : S3) (l : Nat) (z : Authority) : Prop :=
  z.origin = none ∧ ∃ r ∈ List.range s.P.length, RootPlace s.P r ∧ partOf s.P l r ∧ FpIs s z r

/-- Decidability of `RootFor` (§49.6). -/
instance (s : S3) (l : Nat) (z : Authority) : Decidable (RootFor s l z) := by
  unfold RootFor; infer_instance

/-- The origin chain of `a` reaches a root authority for the root place of leaf `l`
(§49.6). -/
def ChainRoot (s : S3) (a l : Nat) : Prop :=
  ∃ x ∈ a :: s.ancs a, OptP (s.A[x]?) (RootFor s l) False

/-- Decidability of `ChainRoot` (§49.6). -/
instance (s : S3) (a l : Nat) : Decidable (ChainRoot s a l) := by
  unfold ChainRoot; infer_instance

/-- The record `z` is the active root `Modify` authority of root place `r`, held by its owner
(§49.7). -/
def RootAuth (s : S3) (r : Nat) (z : Authority) : Prop :=
  z.active = true ∧ z.origin = none ∧ z.mode = .modify ∧
    OptP (s.P[r]?) (fun pr => z.holder = pr.owner) False ∧ FpIs s z r

/-- Decidability of `RootAuth` (§49.7). -/
instance (s : S3) (r : Nat) (z : Authority) : Decidable (RootAuth s r z) := by
  unfold RootAuth; infer_instance

/-- Valid owner (§49.3): a frame below `nF` or an existing place. -/
def OwnerOK (s : S3) : Holder → Prop
  | .frame f => f < s.nF
  | .place o => o < s.P.length

/-- Decidability of `OwnerOK` (§49.3). -/
instance (s : S3) (h : Holder) : Decidable (OwnerOK s h) := by
  cases h <;> unfold OwnerOK <;> infer_instance

/-- The active record `y` covers no leaf of an unusable place (§54, `NoDangling`). -/
def NoDangB (s : S3) (y : Authority) : Prop :=
  ∀ q ∈ List.range s.P.length, ¬ s.Usable q → ∀ l ∈ footprint s.P q, l ∉ y.footprint

/-- Decidability of `NoDangB` (§54). -/
instance (s : S3) (y : Authority) : Decidable (NoDangB s y) := by
  unfold NoDangB; infer_instance

/-- The origin-less record `z` is held by the owner of the root place of every leaf it covers
(`RootHeldConv`, §40, §49.7). -/
def RHConvB (s : S3) (z : Authority) : Prop :=
  ∀ l ∈ z.footprint, ∀ r ∈ List.range s.P.length, RootPlace s.P r → partOf s.P l r →
    OptP (s.P[r]?) (fun pr => z.holder = pr.owner) False

/-- Decidability of `RHConvB` (§49.7). -/
instance (s : S3) (z : Authority) : Decidable (RHConvB s z) := by
  unfold RHConvB; infer_instance

/-- Bounded check §49.1 (decision procedure). -/
def KB_frames (s : S3) : Prop :=
  s.F ≠ [] ∧ s.F.Nodup ∧ ∀ f ∈ s.F, f < s.nF

/-- Decidability of `KB_frames` (decision procedure for §57). -/
instance (s : S3) : Decidable (KB_frames s) := by
  unfold KB_frames; infer_instance

/-- Bounded check §49.2 (decision procedure). -/
def KB_places (s : S3) : Prop :=
  ∀ q ∈ List.range s.P.length, OptP (s.P[q]?) (fun pl => OptP pl.parent (fun r =>
    OptP (s.P[r]?) (fun pr => r < q ∧ pr.owner = pl.owner ∧ s.dead r = s.dead q) False) True) True

/-- Decidability of `KB_places` (decision procedure for §57). -/
instance (s : S3) : Decidable (KB_places s) := by
  unfold KB_places; infer_instance

/-- Bounded check §49.3 (decision procedure). -/
def KB_owners (s : S3) : Prop :=
  ∀ q ∈ List.range s.P.length, OptP (s.P[q]?) (fun pl => OwnerOK s pl.owner) True

/-- Decidability of `KB_owners` (decision procedure for §57). -/
instance (s : S3) : Decidable (KB_owners s) := by
  unfold KB_owners; infer_instance

/-- Bounded check §49.4 (decision procedure). -/
def KB_footprints (s : S3) : Prop :=
  ∀ a ∈ List.range s.A.length, OptP (s.A[a]?) (fun x =>
    ∀ l ∈ x.footprint, l < s.P.length ∧ isLeaf s.P l) True

/-- Decidability of `KB_footprints` (decision procedure for §57). -/
instance (s : S3) : Decidable (KB_footprints s) := by
  unfold KB_footprints; infer_instance

/-- Bounded check §49.5 (decision procedure). -/
def KB_origins (s : S3) : Prop :=
  ∀ b ∈ List.range s.A.length, OptP (s.A[b]?) (fun y => OptP y.origin (· < b) True) True

/-- Decidability of `KB_origins` (decision procedure for §57). -/
instance (s : S3) : Decidable (KB_origins s) := by
  unfold KB_origins; infer_instance

/-- Bounded check §49.6 (decision procedure). -/
def KB_rootChain (s : S3) : Prop :=
  ∀ a ∈ List.range s.A.length, OptP (s.A[a]?) (fun y => ∀ l ∈ y.footprint,
    isLeaf s.P l → ChainRoot s a l) True

/-- Decidability of `KB_rootChain` (decision procedure for §57). -/
instance (s : S3) : Decidable (KB_rootChain s) := by
  unfold KB_rootChain; infer_instance

/-- Bounded check §49.7 (decision procedure). -/
def KB_rootHeld (s : S3) : Prop :=
  ∀ r ∈ List.range s.P.length, RootPlace s.P r → s.Usable r →
    ∃ i ∈ List.range s.A.length, OptP (s.A[i]?) (RootAuth s r) False

/-- Decidability of `KB_rootHeld` (decision procedure for §57). -/
instance (s : S3) : Decidable (KB_rootHeld s) := by
  unfold KB_rootHeld; infer_instance

/-- Bounded check §49.8 (decision procedure). -/
def KB_holders (s : S3) : Prop :=
  ∀ a ∈ List.range s.A.length, OptP (s.A[a]?) (fun y =>
    y.active = true → HolderLive s y.holder) True

/-- Decidability of `KB_holders` (decision procedure for §57). -/
instance (s : S3) : Decidable (KB_holders s) := by
  unfold KB_holders; infer_instance

/-- Bounded check §50 (decision procedure). -/
def KB_i1 (s : S3) : Prop :=
  ∀ a ∈ List.range s.A.length, ∀ b ∈ List.range s.A.length, OptP (s.A[a]?) (fun x =>
    OptP (s.A[b]?) (fun y => a ≠ b → x.active = true → y.active = true →
    (∃ p ∈ x.footprint, p ∈ y.footprint) → a ∉ s.ancs b → b ∉ s.ancs a →
    x.mode = .observe ∧ y.mode = .observe) True) True

/-- Decidability of `KB_i1` (decision procedure for §57). -/
instance (s : S3) : Decidable (KB_i1 s) := by
  unfold KB_i1; infer_instance

/-- Bounded check §51 (decision procedure). -/
def KB_i2 (s : S3) : Prop :=
  ∀ b ∈ List.range s.A.length, OptP (s.A[b]?) (fun y => OptP y.origin (fun a =>
    OptP (s.A[a]?) (fun x => y.mode.le x.mode ∧ (∀ p ∈ y.footprint, p ∈ x.footprint) ∧
      (y.active = true → x.active = true)) False) True) True

/-- Decidability of `KB_i2` (decision procedure for §57). -/
instance (s : S3) : Decidable (KB_i2 s) := by
  unfold KB_i2; infer_instance

/-- Bounded check §52 (decision procedure). -/
def KB_i3 (s : S3) : Prop :=
  ∀ q ∈ List.range s.P.length, s.Usable q → ∀ x ∈ s.D q, s.Active x

/-- Decidability of `KB_i3` (decision procedure for §57). -/
instance (s : S3) : Decidable (KB_i3 s) := by
  unfold KB_i3; infer_instance

/-- Bounded check §44 (decision procedure). -/
def KB_anchorOrder (s : S3) : Prop :=
  AnchorOrder s

/-- Decidability of `KB_anchorOrder` (decision procedure for §57). -/
instance (s : S3) : Decidable (KB_anchorOrder s) := by
  unfold KB_anchorOrder; infer_instance

/-- Bounded check §54, `NoDangling` (decision procedure). -/
def KB_noDangling (s : S3) : Prop :=
  ∀ j ∈ List.range s.A.length, OptP (s.A[j]?) (fun y => y.active = true → NoDangB s y) True

/-- Decidability of `KB_noDangling` (decision procedure for §57). -/
instance (s : S3) : Decidable (KB_noDangling s) := by
  unfold KB_noDangling; infer_instance

/-- Bounded check §44 (decision procedure). -/
def KB_anchorOrderHeld (s : S3) : Prop :=
  AnchorOrderHeld s

/-- Decidability of `KB_anchorOrderHeld` (decision procedure for §57). -/
instance (s : S3) : Decidable (KB_anchorOrderHeld s) := by
  unfold KB_anchorOrderHeld; infer_instance

/-- Bounded check `RootHeldConv` (§40, §49.7) (decision procedure). -/
def KB_rootHeldConv (s : S3) : Prop :=
  ∀ x ∈ List.range s.A.length, OptP (s.A[x]?) (fun z => z.origin = none → RHConvB s z) True

/-- Decidability of `KB_rootHeldConv` (decision procedure for §57). -/
instance (s : S3) : Decidable (KB_rootHeldConv s) := by
  unfold KB_rootHeldConv; infer_instance

/-- `WF3` (§49) is its bounded check, item by item. -/
theorem wf3_iff_kb {s : S3} : WF3 s ↔ KB_frames s ∧ KB_places s ∧ KB_owners s ∧
    KB_footprints s ∧ KB_origins s ∧ KB_rootChain s ∧ KB_rootHeld s ∧ KB_holders s := by
  constructor
  · intro hw
    refine ⟨hw.frames, fun q _ => ?_, fun q _ => ?_, fun a _ => ?_, fun b _ => ?_, fun a _ => ?_,
      fun r _ hr hu => ?_, fun a _ => ?_⟩
    · cases hpl : s.P[q]? with
      | none => trivial
      | some pl =>
        show OptP pl.parent _ True
        cases hr : pl.parent with
        | none => trivial
        | some r =>
          obtain ⟨pr, hpr, h1, h2, h3⟩ := hw.places q pl r hpl hr
          show OptP (s.P[r]?) _ False
          rw [hpr]; exact ⟨h1, h2, h3⟩
    · cases hpl : s.P[q]? with
      | none => trivial
      | some pl =>
        show OwnerOK s pl.owner
        cases ho : pl.owner with
        | frame f => exact hw.owners.1 q pl f hpl ho
        | place o => exact hw.owners.2.1 q pl o hpl ho
    · cases hx : s.A[a]? with
      | none => trivial
      | some x => exact hw.footprints a x hx
    · cases hy : s.A[b]? with
      | none => trivial
      | some y =>
        show OptP y.origin _ True
        cases ho : y.origin with
        | none => trivial
        | some o => exact hw.origins b y o hy ho
    · cases hy : s.A[a]? with
      | none => trivial
      | some y =>
        intro l hl hleaf
        obtain ⟨x, z, r, hx, hz, hzo, hr, hlr, hfp⟩ := hw.rootChain a y l hy hl hleaf
        refine ⟨x, ?_, ?_⟩
        · rcases hx with rfl | hx
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ hx
        · rw [hz]
          exact ⟨hzo, r, List.mem_range.2 hr.1, hr, hlr, fun l' h => (hfp l').1 h,
            fun l' h => (hfp l').2 h⟩
    · obtain ⟨j, z, pr, hz, za, zo, zm, hpr, hh, hfp⟩ := hw.rootHeld r hr hu
      refine ⟨j, List.mem_range.2 (lt_of_getElem? hz), ?_⟩
      rw [hz]
      refine ⟨za, zo, zm, ?_, fun l h => (hfp l).1 h, fun l h => (hfp l).2 h⟩
      show OptP (s.P[r]?) _ False
      rw [hpr]; exact hh
    · cases hy : s.A[a]? with
      | none => trivial
      | some y => exact hw.holders a y hy
  · rintro ⟨hfr, hpl, how, hfp, hor, hrc, hrh, hho⟩
    refine ⟨hfr, fun q pl r hq hr => ?_, ⟨fun q pl f hq hf => ?_, fun q pl o hq ho => ?_,
      fun q hq => hq.frameOf⟩, fun a x hx l hl => ?_, fun b y a hy ho => ?_,
      fun a y l hy hl hleaf => ?_, fun r hr hu => ?_, fun a y hy ha => ?_⟩
    · have := hpl q (List.mem_range.2 (lt_of_getElem? hq))
      rw [hq] at this; simp only [OptP, hr] at this
      cases hpr : s.P[r]? with
      | none => rw [hpr] at this; exact this.elim
      | some pr => rw [hpr] at this; exact ⟨pr, rfl, this⟩
    · have := how q (List.mem_range.2 (lt_of_getElem? hq))
      rw [hq] at this; simp only [OptP, OwnerOK, hf] at this; exact this
    · have := how q (List.mem_range.2 (lt_of_getElem? hq))
      rw [hq] at this; simp only [OptP, OwnerOK, ho] at this; exact this
    · have := hfp a (List.mem_range.2 (lt_of_getElem? hx))
      rw [hx] at this; exact this l hl
    · have := hor b (List.mem_range.2 (lt_of_getElem? hy))
      rw [hy] at this; simp only [OptP, ho] at this; exact this
    · have := hrc a (List.mem_range.2 (lt_of_getElem? hy))
      rw [hy] at this
      obtain ⟨x, hx, hz⟩ := this l hl hleaf
      cases hzx : s.A[x]? with
      | none => rw [hzx] at hz; exact hz.elim
      | some z =>
        rw [hzx] at hz
        obtain ⟨hzo, r, -, hr, hlr, h1, h2⟩ := hz
        exact ⟨x, z, r, (List.mem_cons.1 hx).imp id id, hzx, hzo, hr, hlr,
          fun l' => ⟨h1 l', h2 l'⟩⟩
    · obtain ⟨i, -, hz⟩ := hrh r (List.mem_range.2 hr.1) hr hu
      cases hzi : s.A[i]? with
      | none => rw [hzi] at hz; exact hz.elim
      | some z =>
        rw [hzi] at hz
        obtain ⟨za, zo, zm, hpr, h1, h2⟩ := hz
        cases hp : s.P[r]? with
        | none => rw [hp] at hpr; exact hpr.elim
        | some pr =>
          rw [hp] at hpr
          exact ⟨i, z, pr, hzi, za, zo, zm, rfl, hpr, fun l => ⟨h1 l, h2 l⟩⟩
    · have := hho a (List.mem_range.2 (lt_of_getElem? hy))
      rw [hy] at this; exact this ha

/-- Decidability of `WF3` (§49), through its bounded check. -/
instance (s : S3) : Decidable (WF3 s) := decidable_of_iff _ wf3_iff_kb.symm

/-- `I1` (§50) is its bounded check. -/
theorem i1_iff_kb {s : S3} : I1 s ↔ KB_i1 s := by
  constructor
  · intro h1 a _ b _
    cases hx : s.A[a]? with
    | none => trivial
    | some x =>
      show OptP (s.A[b]?) _ True
      cases hy : s.A[b]? with
      | none => trivial
      | some y =>
        intro hab xa ya ⟨p, hpx, hpy⟩ hba hab'
        exact h1 a b x y p hab hx hy xa ya hpx hpy hba hab'
  · intro h a b x y p hab hx hy xa ya hpx hpy hab' hba
    have := h a (List.mem_range.2 (lt_of_getElem? hx)) b (List.mem_range.2 (lt_of_getElem? hy))
    rw [hx] at this; simp only [OptP, hy] at this
    exact this hab xa ya ⟨p, hpx, hpy⟩ hab' hba

/-- Decidability of `I1` (§50), through its bounded check. -/
instance (s : S3) : Decidable (I1 s) := decidable_of_iff _ i1_iff_kb.symm

/-- `KInv ∧ KAux` with bounded quantifiers (§49–§54, §57; decision procedure). -/
structure KInvB (s : S3) : Prop where
  /-- §49.1. -/
  frames : KB_frames s
  /-- §49.2. -/
  places : KB_places s
  /-- §49.3. -/
  owners : KB_owners s
  /-- §49.4. -/
  footprints : KB_footprints s
  /-- §49.5. -/
  origins : KB_origins s
  /-- §49.6. -/
  rootChain : KB_rootChain s
  /-- §49.7. -/
  rootHeld : KB_rootHeld s
  /-- §49.8. -/
  holders : KB_holders s
  /-- §50. -/
  i1 : KB_i1 s
  /-- §51. -/
  i2 : KB_i2 s
  /-- §52. -/
  i3 : KB_i3 s
  /-- §44. -/
  anchorOrder : KB_anchorOrder s
  /-- §54, `NoDangling`. -/
  noDangling : KB_noDangling s
  /-- §44. -/
  anchorOrderHeld : KB_anchorOrderHeld s
  /-- `RootHeldConv` (§40, §49.7). -/
  rootHeldConv : KB_rootHeldConv s

/-- Decidability of `KInvB` (decision procedure for §49–§54, §57). -/
instance (s : S3) : Decidable (KInvB s) :=
  decidable_of_iff (KB_frames s ∧ KB_places s ∧ KB_owners s ∧ KB_footprints s ∧ KB_origins s ∧
    KB_rootChain s ∧ KB_rootHeld s ∧ KB_holders s ∧ KB_i1 s ∧ KB_i2 s ∧ KB_i3 s ∧
    KB_anchorOrder s ∧ KB_noDangling s ∧ KB_anchorOrderHeld s ∧ KB_rootHeldConv s)
    ⟨fun ⟨a, b, c, d, e, f, g, h, i, j, l, m, n, o, q⟩ =>
      ⟨a, b, c, d, e, f, g, h, i, j, l, m, n, o, q⟩,
     fun ⟨a, b, c, d, e, f, g, h, i, j, l, m, n, o, q⟩ =>
      ⟨a, b, c, d, e, f, g, h, i, j, l, m, n, o, q⟩⟩

/-- Soundness of `KInvB` (decision procedure for §49–§54, §57): it gives `KInv ∧ KAux`. -/
theorem KInvB.sound {s : S3} (h : KInvB s) : KInv s ∧ KAux s := by
  have hw : WF3 s := wf3_iff_kb.2 ⟨h.frames, h.places, h.owners, h.footprints, h.origins,
    h.rootChain, h.rootHeld, h.holders⟩
  refine ⟨⟨hw, ⟨⟨i1_iff_kb.2 h.i1, fun b y a hy ho => ?_,
    fun q hq x hx => h.i3 q (List.mem_range.2 hq.lt) hq x hx, i4_always s⟩, h.anchorOrder,
    fun j y hy ya q hq l hl hly => ?_⟩, h.anchorOrderHeld, noOrphan_of_wf3 hw⟩,
    fun x z l r hz hzo hl hr hlr => ?_⟩
  · have := h.i2 b (List.mem_range.2 (lt_of_getElem? hy))
    rw [hy] at this; simp only [OptP, ho] at this
    cases hxa : s.A[a]? with
    | none => rw [hxa] at this; exact this.elim
    | some x => rw [hxa] at this; exact ⟨x, rfl, this⟩
  · have := h.noDangling j (List.mem_range.2 (lt_of_getElem? hy))
    rw [hy] at this
    exact this ya q (List.mem_range.2 (footprint_lt hl)) hq l hl hly
  · have := h.rootHeldConv x (List.mem_range.2 (lt_of_getElem? hz))
    rw [hz] at this
    have h' := this hzo l hl r (List.mem_range.2 hr.1) hr hlr
    cases hp : s.P[r]? with
    | none => rw [hp] at h'; exact h'.elim
    | some pr => rw [hp] at h'; exact ⟨pr, rfl, h'⟩

/-! ## O17 `newArena` (§76) and the guard of §56 -/

/-- All leaves of the place holding an authority are `Init` (§76.5); vacuous for a frame. -/
def LeavesInit (s : S3) : Holder → Prop
  | .place v => ∀ l ∈ footprint s.P v, s.I l = .init
  | .frame _ => True

/-- Decidability of `LeavesInit` (§76.5). -/
instance (s : S3) (h : Holder) : Decidable (LeavesInit s h) := by
  cases h <;> unfold LeavesInit <;> infer_instance

/-- The unified administration guard (§56, §76.4) as a contract predicate: `internal` is absent
from every registry of live administrations. A registry is given by the `internal` identities of
its live administrations; `regs` lists all relevant registries. -/
def Guard56 (regs : List (List Nat)) (i : Nat) : Prop := ∀ R ∈ regs, i ∉ R

/-- Decidability of `Guard56` (§56). -/
instance (regs : List (List Nat)) (i : Nat) : Decidable (Guard56 regs i) := by
  unfold Guard56; infer_instance

/-- The arena registry as a registry of live administrations (§46, §56): the `internal`
identities of its live entries. -/
def liveInternals (s : S3) (arenas : List ArenaEntry) : List Nat :=
  (arenas.filter fun E => decide (s.Active E.internal)).map (·.internal)

/-- Preconditions of `newArena(storage, internal)` other than the guard (§76.1–§76.3, §76.5,
§76.6). §76.6 is read on the resulting state (v0.1 §76.6): its kernel component is `s`, since
`newArena` changes no kernel component (§76 `ok` effect, `newArena_kernel`), so `WF3`, `I1`,
`AnchorOrder` and `AnchorOrderHeld` are required of the whole kernel state `s`; the new entry is
the one `newArenaEff` registers, `available` holding the leaves of the storage and `issued`
empty, and it must satisfy `ArenaInv` (§55). -/
structure NewArenaBase (s : S3) (storage internal : Nat) : Prop where
  /-- §76.1: `storage` is an existing, usable place. -/
  storageUsable : s.Usable storage
  /-- §76.1: `storage` is under exercisable `Modify` by the current frame. -/
  storageRight : HasRight s .modify storage
  /-- §76.2: `internal` exists, is active and has own mode `Modify`. -/
  internalAuth : OptP (s.A[internal]?) (fun y => y.active = true ∧ y.mode = .modify) False
  /-- §76.2: `ExercisableAt(s, internal, Modify)`. -/
  exercisable : s.ExercisableAt internal .modify
  /-- §76.3: `internal` is held by a place, the arena value. -/
  heldByPlace : OptP (s.A[internal]?) (fun y => y.holder.isPlace = true) False
  /-- §76.3: `footprint(internal) ⊆ footprint(storage)`. -/
  fpSub : ∀ l ∈ s.afp internal, l ∈ footprint s.P storage
  /-- §76.3: `footprint(storage) ⊆ footprint(internal)`. -/
  fpSup : ∀ l ∈ footprint s.P storage, l ∈ s.afp internal
  /-- §76.5: all leaves of the arena value are already `Init`. -/
  valueInit : OptP (s.A[internal]?) (fun y => LeavesInit s y.holder) True
  /-- §76.6: `WF3` (§49) over the whole kernel state of the resulting state. -/
  wf3 : WF3 s
  /-- §76.6: `I1` (§50) over the whole kernel state of the resulting state. -/
  i1 : I1 s
  /-- §76.6: `AnchorOrder` (§44) over the whole kernel state of the resulting state. -/
  anchorOrder : AnchorOrder s
  /-- §76.6: `AnchorOrderHeld` (§44) over the whole kernel state of the resulting state. -/
  anchorOrderHeld : AnchorOrderHeld s
  /-- §76.6: the new entry satisfies `ArenaInv` (§55). -/
  arenaInv : ArenaInv s ⟨storage, internal, footprint s.P storage, []⟩

/-- Decidability of `NewArenaBase` (§76). -/
instance (s : S3) (storage internal : Nat) : Decidable (NewArenaBase s storage internal) :=
  decidable_of_iff (s.Usable storage ∧ HasRight s .modify storage ∧
    OptP (s.A[internal]?) (fun y => y.active = true ∧ y.mode = .modify) False ∧
    s.ExercisableAt internal .modify ∧
    OptP (s.A[internal]?) (fun y => y.holder.isPlace = true) False ∧
    (∀ l ∈ s.afp internal, l ∈ footprint s.P storage) ∧
    (∀ l ∈ footprint s.P storage, l ∈ s.afp internal) ∧
    OptP (s.A[internal]?) (fun y => LeavesInit s y.holder) True ∧
    WF3 s ∧ I1 s ∧ AnchorOrder s ∧ AnchorOrderHeld s ∧
    ArenaInv s ⟨storage, internal, footprint s.P storage, []⟩)
    ⟨fun ⟨a, b, c, d, e, f, g, h, i, j, l, m, n⟩ => ⟨a, b, c, d, e, f, g, h, i, j, l, m, n⟩,
     fun ⟨a, b, c, d, e, f, g, h, i, j, l, m, n⟩ => ⟨a, b, c, d, e, f, g, h, i, j, l, m, n⟩⟩

/-- Preconditions of `newArena(storage, internal)` (§76): those of `NewArenaBase` and the guard of
§76.4 over the arena registry and the other registries `others` (§56). -/
structure NewArenaPre (s : S3) (arenas : List ArenaEntry) (others : List (List Nat))
    (storage internal : Nat) : Prop where
  /-- §76.1–§76.3, §76.5. -/
  base : NewArenaBase s storage internal
  /-- §76.4, §56: no live administration of any relevant registry uses `internal`. -/
  guard : Guard56 (liveInternals s arenas :: others) internal

/-- Decidability of `NewArenaPre` (§76). -/
instance (s : S3) (arenas : List ArenaEntry) (others : List (List Nat)) (storage internal : Nat) :
    Decidable (NewArenaPre s arenas others storage internal) :=
  decidable_of_iff (NewArenaBase s storage internal ∧
    Guard56 (liveInternals s arenas :: others) internal)
    ⟨fun ⟨a, b⟩ => ⟨a, b⟩, fun ⟨a, b⟩ => ⟨a, b⟩⟩

/-- Effect of `newArena` (§76, `ok` effect): a live entry is added, `available` holding the leaves
of the storage and `issued` empty; the kernel state is unchanged. -/
def newArenaEff (L : LState) (storage internal : Nat) : LState :=
  { L with arenas := L.arenas ++ [⟨storage, internal, footprint L.kern.P storage, []⟩] }

/-- `newArena` as a relation (§76, §58): `ok` or `reject`; `others` are the other registries of
live administrations consulted by the guard (§56). -/
def NewArenaStep (others : List (List Nat)) (storage internal : Nat) (L : LState) :
    Outcome3 LState → Prop :=
  Guarded (NewArenaPre L.kern L.arenas others storage internal) (newArenaEff L storage internal)

/-! ## O18 `issue` (§77) -/

/-- Static preconditions of `issue(arena, region, destination)` (§77.1, §77.2). The static
restrictions of §77.3 are given no list by the text and are not represented. -/
structure IssueStatic (s : S3) (E : ArenaEntry) (region : List Nat) (dst : Nat) : Prop where
  /-- §77.1: the entry is live; `internal` is active. -/
  live : s.Active E.internal
  /-- §77.1: `MetaRight`, exercisable `Modify` over the arena value (§36). -/
  metaRight : MetaRight s E
  /-- §77.2: `region` belongs to the administered storage. -/
  regionIn : ∀ l ∈ region, l ∈ footprint s.P E.storage
  /-- §77.2: `destination` is usable. -/
  dstUsable : s.Usable dst
  /-- §77.2: `destination` is a leaf. -/
  dstLeaf : isLeaf s.P dst
  /-- §77.2: `destination` holds no active authority. -/
  dstFree : ∀ j ∈ List.range s.A.length,
    OptP (s.A[j]?) (fun z => z.active = true → z.holder ≠ .place dst) True
  /-- §77.2: `destination` can legally receive the block value in mode `Modify`. -/
  dstRight : HasRight s .modify dst
  /-- §77.2: local self-blocking prevention, `destination` is not in `region`. -/
  dstNotIn : dst ∉ region

/-- Decidability of `IssueStatic` (§77). -/
instance (s : S3) (E : ArenaEntry) (region : List Nat) (dst : Nat) :
    Decidable (IssueStatic s E region dst) :=
  decidable_of_iff (s.Active E.internal ∧ MetaRight s E ∧
    (∀ l ∈ region, l ∈ footprint s.P E.storage) ∧ s.Usable dst ∧ isLeaf s.P dst ∧
    (∀ j ∈ List.range s.A.length,
      OptP (s.A[j]?) (fun z => z.active = true → z.holder ≠ .place dst) True) ∧
    HasRight s .modify dst ∧ dst ∉ region)
    ⟨fun ⟨a, b, c, d, e, f, g, h⟩ => ⟨a, b, c, d, e, f, g, h⟩,
     fun ⟨a, b, c, d, e, f, g, h⟩ => ⟨a, b, c, d, e, f, g, h⟩⟩

/-- §77.5: the effective mode of `internal` permits `Modify` on every leaf of the region. -/
def IssueRight (s : S3) (E : ArenaEntry) (region : List Nat) : Prop :=
  ∀ l ∈ region, Allows (effective s E.internal l) .modify

/-- Decidability of `IssueRight` (§77.5). -/
instance (s : S3) (E : ArenaEntry) (region : List Nat) : Decidable (IssueRight s E region) := by
  unfold IssueRight; infer_instance

/-- Kernel part of the effect of `issue` (§77, `ok` effect): a block authority of fresh identity
`|A|`, derived from `internal`, of mode `Modify`, on the region, held by `destination`, which
receives the corresponding anchor; only leaf `destination` becomes `Init`. -/
def issueKEff (s : S3) (E : ArenaEntry) (region : List Nat) (dst : Nat) : S3 :=
  { s with
    A := s.A ++ [⟨.modify, some E.internal, region, .place dst, true⟩]
    D := fun q => if q = dst then s.D dst ++ [s.A.length] else s.D q
    I := fun l => if l = dst then .init else s.I l }

/-- Metadata part of the effect of `issue` (§77, `ok` effect; §46): the leaves of the region leave
`available`; the issuance joins `issued` with its authority. -/
def issueMeta (s : S3) (E : ArenaEntry) (region : List Nat) : ArenaEntry :=
  { E with
    available := E.available.filter fun l => decide (l ∉ region)
    issued := (region, s.A.length) :: E.issued }

/-- Checks of `issue` on the simulated resulting state (§77.3, §77.6). -/
structure IssueArrival (s : S3) (E : ArenaEntry) (region : List Nat) (dst : Nat) : Prop where
  /-- §77.3: `AnchorOrder` for the new anchor of `destination`, in the resulting state. -/
  anchorOrder : EffAnchorOK (issueKEff s E region dst) s.A.length
    ((issueKEff s E region dst).pframe dst)
  /-- §77.6: `AnchorOrderHeld` in the resulting state. -/
  anchorOrderHeld : AnchorOrderHeld (issueKEff s E region dst)
  /-- §77.6, O8.5: `destination` remains under exercisable `Modify` in the resulting state. -/
  keepsDst : HasRight (issueKEff s E region dst) .modify dst

/-- Decidability of `IssueArrival` (§77). -/
instance (s : S3) (E : ArenaEntry) (region : List Nat) (dst : Nat) :
    Decidable (IssueArrival s E region dst) :=
  decidable_of_iff (EffAnchorOK (issueKEff s E region dst) s.A.length
      ((issueKEff s E region dst).pframe dst) ∧ AnchorOrderHeld (issueKEff s E region dst) ∧
    HasRight (issueKEff s E region dst) .modify dst)
    ⟨fun ⟨a, b, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨a, b, c⟩⟩

/-- Library state after an `ok` issue of entry `i` (§77, `ok` effect). -/
def issueL (L : LState) (i : Nat) (E : ArenaEntry) (region : List Nat) (dst : Nat) : LState :=
  ⟨issueKEff L.kern E region dst, L.arenas.set i (issueMeta L.kern E region)⟩

/-- The contract of `issue` on entry `i` (§77, §58): `reject` when the entry is missing or a
static precondition fails; `fail`, the state unchanged, when the region is unavailable (§77.4);
`reject` when the effective right (§77.5) or a check on the resulting state (§77.3, §77.6)
fails; `ok` otherwise. -/
inductive IssueC (i : Nat) (region : List Nat) (dst : Nat) (L : LState) :
    Outcome3 LState → Prop where
  | noEntry : L.arenas[i]? = none → IssueC i region dst L .reject
  | static {E : ArenaEntry} : L.arenas[i]? = some E → ¬ IssueStatic L.kern E region dst →
      IssueC i region dst L .reject
  | fail {E : ArenaEntry} : L.arenas[i]? = some E → IssueStatic L.kern E region dst →
      ¬ Avail E region → IssueC i region dst L .fail
  | noRight {E : ArenaEntry} : L.arenas[i]? = some E → IssueStatic L.kern E region dst →
      Avail E region → ¬ IssueRight L.kern E region → IssueC i region dst L .reject
  | noArrival {E : ArenaEntry} : L.arenas[i]? = some E → IssueStatic L.kern E region dst →
      Avail E region → IssueRight L.kern E region → ¬ IssueArrival L.kern E region dst →
      IssueC i region dst L .reject
  | ok {E : ArenaEntry} : L.arenas[i]? = some E → IssueStatic L.kern E region dst →
      Avail E region → IssueRight L.kern E region → IssueArrival L.kern E region dst →
      IssueC i region dst L (.ok (issueL L i E region dst))

/-- `issue` as a derived operation (Part XIV, §77): its static checks, then the availability
`fail` (§77.4), then `split` of `internal` on the region (O2) and `store` of the block, of fresh
identity `|A|`, into the destination (O8); the metadata is updated on `ok`. -/
inductive IssueD (k : K) (i : Nat) (region : List Nat) (dst : Nat) (L : LState) :
    Outcome3 LState → Prop where
  | noEntry : L.arenas[i]? = none → IssueD k i region dst L .reject
  | static {E : ArenaEntry} : L.arenas[i]? = some E → ¬ IssueStatic L.kern E region dst →
      IssueD k i region dst L .reject
  | fail {E : ArenaEntry} : L.arenas[i]? = some E → IssueStatic L.kern E region dst →
      ¬ Avail E region → IssueD k i region dst L .fail
  | split {E : ArenaEntry} : L.arenas[i]? = some E → IssueStatic L.kern E region dst →
      Avail E region → SplitStep k E.internal [region] L.kern .reject →
      IssueD k i region dst L .reject
  | store {E : ArenaEntry} {s₁ : S3} : L.arenas[i]? = some E → IssueStatic L.kern E region dst →
      Avail E region → SplitStep k E.internal [region] L.kern (.ok s₁) →
      StoreStep L.kern.A.length dst s₁ .reject → IssueD k i region dst L .reject
  | ok {E : ArenaEntry} {s₁ s₂ : S3} : L.arenas[i]? = some E →
      IssueStatic L.kern E region dst → Avail E region →
      SplitStep k E.internal [region] L.kern (.ok s₁) →
      StoreStep L.kern.A.length dst s₁ (.ok s₂) →
      IssueD k i region dst L (.ok ⟨s₂, L.arenas.set i (issueMeta L.kern E region)⟩)

/-! ## O19 `reset` (§78) -/

/-- §78.3 (v0.1): no still-usable place depends on an anchor in the strict origin subtree of
`internal` that covers a leaf of the administered storage. Dependencies of contained values are
covered since parts are places. -/
def ResetNoDeps (s : S3) (E : ArenaEntry) : Prop :=
  ∀ q ∈ List.range s.P.length, s.Usable q → ∀ x ∈ s.D q, E.internal ∈ s.ancs x →
    ∀ l ∈ s.afp x, l ∉ footprint s.P E.storage

/-- Decidability of `ResetNoDeps` (§78.3). -/
instance (s : S3) (E : ArenaEntry) : Decidable (ResetNoDeps s E) := by
  unfold ResetNoDeps; infer_instance

/-- Preconditions of `reset(arena)` (§78). "`internal` and the arena's other restrictions remain
valid" (§78.1) and "validity obligations of other nested arenas remain satisfied" (§78.3) name no
checkable condition beyond `ArenaInv` and are not represented. -/
structure ResetPre (s : S3) (E : ArenaEntry) : Prop where
  /-- §78.1: the entry is live. -/
  live : s.Active E.internal
  /-- §78.1: `MetaRight`, exercisable `Modify` over the arena value (§36). -/
  metaRight : MetaRight s E
  /-- §78.2: no active authority derived from `internal` covers a leaf of the storage. -/
  noCover : ∀ j ∈ List.range s.A.length, E.internal ∈ s.ancs j → s.Active j →
    ∀ l ∈ s.afp j, l ∉ footprint s.P E.storage
  /-- §78.3: no usable place depends on an anchor in the strict origin subtree of `internal`
  covering a leaf of the storage. -/
  noDeps : ResetNoDeps s E

/-- Decidability of `ResetPre` (§78). -/
instance (s : S3) (E : ArenaEntry) : Decidable (ResetPre s E) :=
  decidable_of_iff (s.Active E.internal ∧ MetaRight s E ∧
    (∀ j ∈ List.range s.A.length, E.internal ∈ s.ancs j → s.Active j →
      ∀ l ∈ s.afp j, l ∉ footprint s.P E.storage) ∧ ResetNoDeps s E)
    ⟨fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩, fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩⟩

/-- Kernel part of the effect of `reset` (§78 `ok` effect, Part XIV): the record of the `Modify`
derivation of `internal` over all the storage, already released; no leaf becomes `Init`. -/
def resetKEff (s : S3) (E : ArenaEntry) : S3 :=
  { s with A := s.A ++ [⟨.modify, some E.internal, footprint s.P E.storage, .frame s.top, false⟩] }

/-- Metadata part of the effect of `reset` (§78 `ok` effect, §46): all leaves of the storage
become available; `issued` is cleared. -/
def resetMeta (s : S3) (E : ArenaEntry) : ArenaEntry :=
  { E with available := footprint s.P E.storage, issued := [] }

/-- Library state after an `ok` reset of entry `i` (§78). -/
def resetL (L : LState) (i : Nat) (E : ArenaEntry) : LState :=
  ⟨resetKEff L.kern E, L.arenas.set i (resetMeta L.kern E)⟩

/-- The contract of `reset` on entry `i` (§78, §58): `ok` when the entry exists and the
preconditions hold, `reject` otherwise. -/
inductive ResetC (i : Nat) (L : LState) : Outcome3 LState → Prop where
  | noEntry : L.arenas[i]? = none → ResetC i L .reject
  | reject {E : ArenaEntry} : L.arenas[i]? = some E → ¬ ResetPre L.kern E → ResetC i L .reject
  | ok {E : ArenaEntry} : L.arenas[i]? = some E → ResetPre L.kern E →
      ResetC i L (.ok (resetL L i E))

/-- `reset` as a derived operation (Part XIV, §78): `derive` of `internal` at `Modify` over the
footprint of the storage (O1), `release` of the derived authority (O3), then the explicit contract
check of §78.3; the metadata is updated on `ok`. -/
inductive ResetD (i : Nat) (L : LState) : Outcome3 LState → Prop where
  | noEntry : L.arenas[i]? = none → ResetD i L .reject
  | derive {E : ArenaEntry} : L.arenas[i]? = some E →
      DeriveStep E.internal (footprint L.kern.P E.storage) .modify L.kern .reject →
      ResetD i L .reject
  | release {E : ArenaEntry} {s₁ : S3} : L.arenas[i]? = some E →
      DeriveStep E.internal (footprint L.kern.P E.storage) .modify L.kern (.ok s₁) →
      ReleaseStep L.kern.A.length s₁ .reject → ResetD i L .reject
  | contract {E : ArenaEntry} {s₁ s₂ : S3} : L.arenas[i]? = some E →
      DeriveStep E.internal (footprint L.kern.P E.storage) .modify L.kern (.ok s₁) →
      ReleaseStep L.kern.A.length s₁ (.ok s₂) → ¬ ResetNoDeps L.kern E → ResetD i L .reject
  | ok {E : ArenaEntry} {s₁ s₂ : S3} : L.arenas[i]? = some E →
      DeriveStep E.internal (footprint L.kern.P E.storage) .modify L.kern (.ok s₁) →
      ReleaseStep L.kern.A.length s₁ (.ok s₂) → ResetNoDeps L.kern E →
      ResetD i L (.ok ⟨s₂, L.arenas.set i (resetMeta L.kern E)⟩)

/-! ## Helper lemmas (§40, §42, §43, §65) -/

/-- `Allows` at `Modify` is effective `Modify` (§43). -/
theorem allows_modify_iff {e : Option Mode} : Allows e .modify ↔ e = some .modify := by
  cases e with
  | none => simp [Allows, OptP]
  | some m => cases m <;> simp [Allows, OptP, Mode.le]

/-- Effective `Modify` permits every requested mode (§43: `Observe ≤ Modify`). -/
theorem allows_some_modify (m : Mode) : Allows (some .modify) m := by
  cases m <;> simp [Allows, OptP, Mode.le]

/-- An exercisable authority exists (§43). -/
theorem exercisable_lt {s : S3} {a : Nat} {m : Mode} (h : s.ExercisableAt a m) :
    a < s.A.length := by
  cases h <;> exact lt_of_getElem? ‹_›

/-- An exercise at `Modify` is an exercise at every mode (§43: `Observe ≤ Modify`). -/
theorem exercisable_of_modify {s : S3} {a : Nat} {m : Mode} (h : s.ExercisableAt a .modify) :
    s.ExercisableAt a m := by
  generalize hm : Mode.modify = m' at h
  induction h with
  | base hy ha hle hf =>
    subst hm
    exact .base hy ha (.inr (hle.resolve_left (by decide))) hf
  | held hy ha hle hp _ hc ih =>
    subst hm
    exact .held hy ha (.inr (hle.resolve_left (by decide))) hp (ih rfl)
      fun l hl => by rw [allows_modify_iff.1 (hc l hl)]; exact allows_some_modify m

/-- A permitted effective mode comes from an existing authority covering the leaf (§43,
case 1). -/
theorem mem_of_allows {s : S3} {a l : Nat} {m : Mode} (h : Allows (effective s a l) m) :
    ∃ x, s.A[a]? = some x ∧ l ∈ x.footprint := by
  unfold effective at h
  cases hx : s.A[a]? with
  | none => rw [hx] at h; exact h.elim
  | some x =>
    rw [hx] at h; simp only at h
    split at h
    · exact ⟨x, rfl, ‹_ ∧ _›.2⟩
    · exact h.elim

/-- More covering descendants permit no more (§43, cases 2–4). -/
theorem allows_effOf_append {m m' : Mode} {ds e : List Mode}
    (h : Allows (effOf m (ds ++ e)) m') : Allows (effOf m ds) m' := by
  by_cases h0 : ds ++ e = []
  · rw [(List.append_eq_nil_iff.1 h0).1]; simpa [effOf, h0] using h
  · by_cases h1 : Mode.modify ∈ ds ++ e
    · simp [effOf, h0, h1, Allows, OptP] at h
    · have hm' : m' = .observe := by
        cases m' with
        | observe => rfl
        | modify => simp [effOf, h0, h1, Allows, OptP, Mode.le] at h
      subst hm'
      have h1' : Mode.modify ∉ ds := fun h' => h1 (List.mem_append_left _ h')
      by_cases hd : ds = []
      · simp [effOf, hd, Allows, OptP, Mode.le]
      · simp [effOf, hd, h1', Allows, OptP, Mode.le]

/-- Adding an authority only takes effective modes away from the existing ones (§43,
case 3). -/
theorem allows_addAuth_back {s : S3} {y₀ : Authority} {b l : Nat} {m : Mode}
    (hb : b < s.A.length) (h : Allows (effective (s.addAuth y₀) b l) m) :
    Allows (effective s b l) m := by
  unfold effective at h ⊢
  rw [addAuth_lt hb, descModes_addAuth] at h
  cases hx : s.A[b]? with
  | none => rw [hx] at h; exact h
  | some x =>
    rw [hx] at h; simp only at h ⊢
    split at h
    · rename_i hc; simp only [hc, and_self, ite_true]; exact allows_effOf_append h
    · exact h.elim

/-- Exercise after adding the block `y₀` of `src`, for a former authority, comes from an
exercise before: a link through the block is replaced by a link through `src` (§43). -/
theorem exercisable_addAuth_back {s : S3} {y₀ : Authority} {src : Nat}
    (hsrc : s.ExercisableAt src .modify)
    (hfp : ∀ l ∈ y₀.footprint, effective s src l = some .modify) {a : Nat} {m : Mode}
    (h : (s.addAuth y₀).ExercisableAt a m) : a < s.A.length → s.ExercisableAt a m := by
  induction h with
  | base hy ha hle hf =>
    intro hlt
    rw [addAuth_lt hlt] at hy
    exact .base hy ha hle hf
  | @held a' p b m' y hy ha hle hp hb hc ih =>
    intro hlt
    rw [addAuth_lt hlt] at hy
    by_cases hbl : b < s.A.length
    · exact .held hy ha hle hp (ih hbl) fun l hl => allows_addAuth_back hbl (hc l hl)
    · have hbe : b = s.A.length := by
        have := exercisable_lt hb; simp [S3.addAuth] at this; omega
      subst hbe
      refine .held hy ha hle hp (exercisable_of_modify hsrc) fun l hl => ?_
      obtain ⟨x, hx, hlx⟩ := mem_of_allows (hc l hl)
      rw [addAuth_self] at hx; cases hx
      rw [hfp l hlx]; exact allows_some_modify m'

/-- `HasRight` after adding the block `y₀` of `src`, on a place none of whose leaves the block
covers, comes from `HasRight` before (§43). -/
theorem hasRight_addAuth_back {s : S3} {y₀ : Authority} {src p : Nat} {m : Mode}
    (hsrc : s.ExercisableAt src .modify)
    (hfp : ∀ l ∈ y₀.footprint, effective s src l = some .modify)
    (hout : ∀ l ∈ footprint s.P p, l ∉ y₀.footprint) (h : HasRight (s.addAuth y₀) m p) :
    HasRight s m p := by
  obtain ⟨a, -, ha, hall⟩ := h
  by_cases hlt : a < s.A.length
  · exact ⟨a, List.mem_range.2 hlt, exercisable_addAuth_back hsrc hfp ha hlt,
      fun l hl => allows_addAuth_back hlt (hall l hl)⟩
  · have hae : a = s.A.length := by
      have := exercisable_lt ha; simp [S3.addAuth] at this; omega
    subst hae
    refine ⟨src, List.mem_range.2 (exercisable_lt hsrc), exercisable_of_modify hsrc,
      fun l hl => ?_⟩
    obtain ⟨x, hx, hlx⟩ := mem_of_allows (hall l hl)
    rw [addAuth_self] at hx; cases hx
    exact absurd hlx (hout l hl)

/-- The effect of `store` on an existing authority (§65, `ok` effect). -/
theorem storeEff_eq {s : S3} {a p : Nat} {y : Authority} (hy : s.A[a]? = some y) :
    storeEff s a p = { s with
      A := s.A.set a { y with holder := .place p }
      D := fun q => if q = p then s.D p ++ [a] else s.D q
      I := fun l => if l = p then .init else s.I l } := by
  simp [storeEff, hy]

/-- `store` changes holders only (§65, `ok` effect). -/
theorem store_skel (s : S3) (a p : Nat) : SameSkel s (storeEff s a p) := by
  unfold storeEff; split
  · rename_i y hy
    refine ⟨by simp, fun j => ?_⟩
    by_cases hj : a = j
    · subst hj; rw [List.getElem?_set_self (lt_of_getElem? hy), hy]; rfl
    · rw [List.getElem?_set_ne hj]
  · exact ⟨rfl, fun _ => rfl⟩

/-- Exercise after `store` comes from an exercise before: `store` only moves the stored authority
from the current frame to a place (§43, §65). -/
theorem exercisable_store_back {s : S3} {a p : Nat} {y : Authority} (hy : s.A[a]? = some y)
    (hh : y.holder = .frame s.top) {b : Nat} {m : Mode}
    (h : (storeEff s a p).ExercisableAt b m) : s.ExercisableAt b m := by
  have hA : (storeEff s a p).A = s.A.set a { y with holder := .place p } := by
    rw [storeEff_eq hy]
  have hF : (storeEff s a p).F = s.F := by rw [storeEff_eq hy]
  have hP : (storeEff s a p).P = s.P := by rw [storeEff_eq hy]
  have he := (store_skel s a p).effective
  have hal := lt_of_getElem? hy
  induction h with
  | @base b m z hz za hle hf =>
    have hne : a ≠ b := by
      rintro rfl
      rw [hA, List.getElem?_set_self hal] at hz; cases hz
      simp at hf
    rw [hA, List.getElem?_set_ne hne] at hz
    exact .base hz za hle (by rw [hf]; simp only [S3.top, hF])
  | @held b q c m z hz za hle hq _ hc ih =>
    by_cases hba : a = b
    · subst hba
      rw [hA, List.getElem?_set_self hal] at hz; cases hz
      exact .base hy za hle hh
    · rw [hA, List.getElem?_set_ne hba] at hz
      exact .held hz za hle hq ih fun l hl => by rw [← he]; exact hc l (by rw [hP]; exact hl)

/-- `HasRight` after `store` comes from `HasRight` before (§43, §65). -/
theorem hasRight_store_back {s : S3} {a p q : Nat} {y : Authority} {m : Mode}
    (hy : s.A[a]? = some y) (hh : y.holder = .frame s.top) (h : HasRight (storeEff s a p) m q) :
    HasRight s m q := by
  obtain ⟨b, -, hb, hall⟩ := h
  have hP : (storeEff s a p).P = s.P := by rw [storeEff_eq hy]
  have hb' := exercisable_store_back hy hh hb
  exact ⟨b, List.mem_range.2 (exercisable_lt hb'), hb', fun l hl => by
    rw [← (store_skel s a p).effective]; exact hall l (by rw [hP]; exact hl)⟩

/-- An element of a chain of strict ancestors is the link of some element (§40, §42). -/
theorem mem_chainF_link {org : Nat → Option Nat} :
    ∀ k i x, x ∈ chainF org k i → ∃ j, org j = some x
  | 0, _, _, h => by simp [chainF] at h
  | k + 1, i, x, h => by
    simp only [chainF] at h
    cases ho : org i with
    | none => rw [ho] at h; simp at h
    | some o =>
      rw [ho] at h; simp only at h
      split at h
      · rcases List.mem_cons.1 h with rfl | h
        · exact ⟨i, ho⟩
        · exact mem_chainF_link k o x h
      · simp at h

/-- A leaf is a strict structural ancestor of no place (§40). -/
theorem not_mem_chain_of_leaf {P : List Place} {d x : Nat} (hd : isLeaf P d) :
    d ∉ chain (parentOf P) x := by
  intro h
  obtain ⟨j, hj⟩ := mem_chainF_link _ _ _ h
  have hjl : j < P.length := by
    unfold parentOf at hj
    cases hp : P[j]? with
    | none => rw [hp] at hj; simp at hj
    | some _ => exact lt_of_getElem? hp
  exact hd j hjl hj

/-- The footprint of a leaf is the leaf itself (§40). -/
theorem mem_footprint_leaf {P : List Place} {d l : Nat} (hd : isLeaf P d) (hlt : d < P.length) :
    l ∈ footprint P d ↔ l = d := by
  constructor
  · intro hl
    obtain ⟨-, -, -, h⟩ := mem_footprint.1 hl
    exact h.resolve_right (not_mem_chain_of_leaf hd)
  · rintro rfl; exact mem_footprint.2 ⟨hlt, hd, hlt, .inl rfl⟩

/-- `NoDangling` (§54): a place containing a leaf covered by an active authority is usable. -/
theorem usable_of_covered {s : S3} (hnd : NoDangling s) {j q l : Nat} {y : Authority}
    (hy : s.A[j]? = some y) (ya : y.active = true) (hly : l ∈ y.footprint)
    (hl : l ∈ footprint s.P q) : s.Usable q :=
  Decidable.byContradiction fun hu => hnd j y hy ya q hu l hl hly

/-- Under `WF3`, a usable place owned, transitively, by the leaf `dst` makes `dst` hold an active
authority: the root authority of its root place (§40, §49.7). -/
theorem ownedIn_holds {s : S3} (hw : WF3 s) {dst : Nat} (hd : isLeaf s.P dst) {q : Nat}
    (h : OwnedIn s.P dst q) (hu : s.Usable q) :
    ∃ (j : Nat) (z : Authority), s.A[j]? = some z ∧ z.active = true ∧ z.holder = .place dst := by
  induction h with
  | @direct q o pl hq ho hpo =>
    have hod : o = dst := hpo.2.resolve_right (not_mem_chain_of_leaf hd)
    subst hod
    obtain ⟨r, hrp, hqr⟩ := exists_rootPlace hw (q + 1) q (Nat.lt_succ_self q) hu.lt
    obtain ⟨pl', pr, hpl', hpr, hown⟩ := hw.ownerOf hqr
    rw [hq] at hpl'; cases hpl'
    have hdead : s.dead r = false := by rw [← hw.deadOf hqr]; cases hu <;> assumption
    have hou : s.Usable o := by
      cases hu with
      | frame hq' _ ho' _ => rw [hq] at hq'; cases hq'; rw [ho] at ho'; cases ho'
      | place hq' _ ho' hu' => rw [hq] at hq'; cases hq'; rw [ho] at ho'; cases ho'; exact hu'
    have hur : s.Usable r := .place hpr hdead (by rw [← hown, ho]) hou
    obtain ⟨i, z, pr', hz, za, -, -, hpr', hzh, -⟩ := hw.rootHeld r hrp hur
    rw [hpr] at hpr'; cases hpr'
    exact ⟨i, z, hz, za, by rw [hzh, ← hown, ho]⟩
  | @step q o pl hq ho _ ih =>
    apply ih
    cases hu with
    | frame hq' _ ho' _ => rw [hq] at hq'; cases hq'; rw [ho] at ho'; cases ho'
    | place hq' _ ho' hu' => rw [hq] at hq'; cases hq'; rw [ho] at ho'; cases ho'; exact hu'

/-- An active `Modify` descendant of `a` covering `p` takes the effective `Modify` of `a` on `p`
away (§43, case 3). -/
theorem effective_ne_modify_of_desc {s : S3} {a j p : Nat} {y : Authority}
    (hy : s.A[j]? = some y) (ya : y.active = true) (hp : p ∈ y.footprint) (hj : a ∈ s.ancs j)
    (hm : y.mode = .modify) : effective s a p ≠ some .modify := by
  intro he
  obtain ⟨x, -, -, -, hx⟩ := effective_some he
  have hmem : Mode.modify ∈ descModes s a p := mem_descModes.2 ⟨j, y, hy, ya, hp, hj, hm⟩
  rcases effOf_cases hx with ⟨h0, -⟩ | ⟨-, h1, -⟩
  · rw [h0] at hmem; simp at hmem
  · exact h1 hmem

/-- Effective `Modify` of `a` on `p` excludes every active descendant covering `p` (§43,
cases 2–4). -/
theorem no_desc_of_modify {s : S3} {a j p : Nat} {y : Authority} (hy : s.A[j]? = some y)
    (ya : y.active = true) (hp : p ∈ y.footprint) (hj : a ∈ s.ancs j)
    (he : effective s a p = some .modify) : False := by
  obtain ⟨x, -, -, -, hx⟩ := effective_some he
  have hmem : y.mode ∈ descModes s a p := mem_descModes.2 ⟨j, y, hy, ya, hp, hj, rfl⟩
  rcases effOf_cases hx with ⟨h0, -⟩ | ⟨-, -, h1⟩
  · rw [h0] at hmem; simp at hmem
  · cases h1

/-- The effective anchor of an authority with an origin is strictly older than it (§44). -/
theorem effAnchor_lt {s : S3} {x o : Nat} (ho : s.org x = some o) (hlt : o < x) :
    s.effAnchor x < x := by
  unfold S3.effAnchor S3.ancs
  rw [chain_cons ho hlt]
  exact chain_lt (by rw [chain_cons ho hlt, List.getLastD_cons]; exact List.getLastD_mem_cons)

/-- `store` changes no `EffAnchorOK` whose effective anchor is not the stored authority (§44,
§65). -/
theorem effAnchorOK_store {s : S3} {a p x : Nat} {y : Authority} (hy : s.A[a]? = some y)
    (hne : s.effAnchor x ≠ a) (fd : Option Nat) :
    EffAnchorOK (storeEff s a p) x fd ↔ EffAnchorOK s x fd := by
  have he : (storeEff s a p).effAnchor x = s.effAnchor x := by
    unfold S3.effAnchor; rw [(store_skel s a p).ancs]
  have hP : (storeEff s a p).P = s.P := by rw [storeEff_eq hy]
  have hF : (storeEff s a p).F = s.F := by rw [storeEff_eq hy]
  have hA : (storeEff s a p).A[s.effAnchor x]? = s.A[s.effAnchor x]? := by
    rw [storeEff_eq hy]; exact List.getElem?_set_ne (Ne.symm hne)
  unfold EffAnchorOK
  rw [he, hA, hF]
  simp only [S3.hframe_congr hP]

/-- Under `ArenaInv`, `MetaRight` is exactly the exercise of `internal` at `Modify` (§36, §43,
§55): `internal` is a `Modify` authority held by the arena value. -/
theorem metaRight_iff {s : S3} {E : ArenaEntry} (hai : ArenaInv s E) :
    MetaRight s E ↔ s.ExercisableAt E.internal .modify := by
  have hsh := hai.shape
  obtain ⟨y, hy, ya⟩ := hai.active
  rw [hy] at hsh
  obtain ⟨hm, hp⟩ := hsh
  obtain ⟨v, hv⟩ : ∃ v, y.holder = .place v := by
    cases h : y.holder with
    | place v => exact ⟨v, rfl⟩
    | frame f => rw [h] at hp; cases hp
  have hav : arenaValue s E = some v := by simp [arenaValue, hy, hv]
  unfold MetaRight; rw [hav]; simp only [OptP]
  constructor
  · rintro ⟨b, -, hb, hall⟩
    exact .held hy ya (.inr hm) hv hb hall
  · intro h
    cases h with
    | base hy₂ _ _ hf => rw [hy] at hy₂; cases hy₂; rw [hv] at hf; cases hf
    | held hy₂ _ _ hp hb hc =>
      rw [hy] at hy₂; cases hy₂; rw [hv] at hp; cases hp
      exact ⟨_, List.mem_range.2 (exercisable_lt hb), hb, hc⟩

/-! ## `issue` as `split` then `store` (Part XIV, §77) -/

/-- `split` of `internal` on one region adds one authority (§61, `ok` effect). -/
theorem splitEff_one (s : S3) (src : Nat) (region : List Nat) :
    splitEff s src [region] = s.addAuth ⟨.modify, some src, region, .frame s.top, true⟩ := rfl

/-- The block added by `split` of `internal` on the region (§61, `ok` effect). -/
theorem split_block (s : S3) (src : Nat) (region : List Nat) :
    (splitEff s src [region]).A[s.A.length]? =
      some ⟨.modify, some src, region, .frame s.top, true⟩ := by
  simp [splitEff]

/-- The kernel part of the effect of `issue` is the arrival state of `split` of `internal` on the
region followed by `store` of the block into the destination (Part XIV, §77): literal
equality. -/
theorem issueKEff_eq (s : S3) (E : ArenaEntry) (region : List Nat) (dst : Nat) :
    issueKEff s E region dst = storeEff (splitEff s E.internal [region]) s.A.length dst := by
  rw [storeEff_eq (split_block s E.internal region)]
  simp [issueKEff, splitEff, List.set_append_right]

/-- Under `ArenaInv` and the static preconditions of `issue`, the effective right of §77.5 is
exactly the precondition of `split` of `internal` on the region (§61, Part XIV). -/
theorem issueRight_iff_split (k : K) {s : S3} {E : ArenaEntry} {region : List Nat} {dst : Nat}
    (hai : ArenaInv s E) (hst : IssueStatic s E region dst) :
    IssueRight s E region ↔ SplitPre k s E.internal [region] := by
  constructor
  · intro hr
    have hm : ∀ p ∈ region, effective s E.internal p = some .modify :=
      fun p hp => allows_modify_iff.1 (hr p hp)
    refine ⟨hst.live, (metaRight_iff hai).1 hst.metaRight, ?_, ?_,
      List.pairwise_singleton _ _, ?_⟩
    · intro r hr' p hp; rw [List.mem_singleton.1 hr'] at hp; exact hm p hp
    · intro r hr' p hp; rw [List.mem_singleton.1 hr'] at hp
      exact ⟨(hai.fpEq p).2 (hst.regionIn p hp), by rw [hm p hp]; simp⟩
    · intro r hr' p hp j _ hd
      rw [List.mem_singleton.1 hr'] at hp
      unfold DistribExcl at hd
      cases hj : s.A[j]? with
      | none => rw [hj] at hd; exact hd
      | some y =>
        rw [hj] at hd; obtain ⟨ya, hanc, hpy, hmy⟩ := hd
        exact effective_ne_modify_of_desc hj ya hpy hanc hmy (hm p hp)
  · intro h p hp
    rw [h.modifyOn region (List.mem_singleton_self _) p hp]; exact allows_some_modify _

/-- Under `WF3`, `NoDangling`, `ArenaInv` and the static preconditions of `issue`, the checks on
the resulting state (§77.3, §77.6) are exactly the preconditions of `store` of the block into the
destination after `split` (§65, Part XIV). §65.3 for the storage owned by the destination follows
from §77.2 (no active authority held by the destination) through §49.7 and `NoDangling`. -/
theorem arrival_iff_store {s : S3} {E : ArenaEntry} {region : List Nat} {dst : Nat}
    (hw : WF3 s) (hnd : NoDangling s) (hai : ArenaInv s E) (hst : IssueStatic s E region dst) :
    IssueArrival s E region dst ↔ StorePre (splitEff s E.internal [region]) s.A.length dst := by
  have hy₀ := split_block s E.internal region
  have heq := issueKEff_eq s E region dst
  obtain ⟨yi, hyi, yia⟩ := hst.live
  have hil := lt_of_getElem? hyi
  have hne : (splitEff s E.internal [region]).effAnchor s.A.length ≠ s.A.length := by
    have := effAnchor_lt (s := splitEff s E.internal [region]) (x := s.A.length)
      (o := E.internal) (by simp [S3.org, hy₀]) hil
    omega
  have hpf : (storeEff (splitEff s E.internal [region]) s.A.length dst).pframe dst =
      (splitEff s E.internal [region]).pframe dst :=
    S3.pframe_congr (by rw [storeEff_eq hy₀]) dst
  constructor
  · rintro ⟨h1, h2, h3⟩
    rw [heq] at h1 h2 h3
    rw [hpf, effAnchorOK_store hy₀ hne] at h1
    have hfd : ∀ l, l ∈ footprint s.P dst ↔ l = dst :=
      fun l => mem_footprint_leaf hst.dstLeaf hst.dstUsable.lt
    refine ⟨by rw [hy₀]; exact ⟨rfl, by simp, rfl⟩,
      (S3.Usable.congr (s := s) (s' := splitEff s E.internal [region]) rfl rfl rfl).2
        hst.dstUsable, hst.dstLeaf,
      hasRight_store_back hy₀ rfl h3, ?_, ?_, h1, h3, h2⟩
    · intro j hj
      by_cases hjl : j < s.A.length
      · have e : (splitEff s E.internal [region]).A[j]? = s.A[j]? := List.getElem?_append_left hjl
        rw [e]; exact hst.dstFree j (List.mem_range.2 hjl)
      · have : j = s.A.length := by
          have := List.mem_range.1 hj; simp [splitEff] at this; omega
        subst this; rw [hy₀]; simp [OptP]
    · intro l hl
      have hlr : l ∈ region := by simpa [S3.afp, hy₀] using hl
      refine ⟨fun hld => hst.dstNotIn (by rw [(hfd l).1 hld] at hlr; exact hlr),
        fun q _ hown hlq => ?_⟩
      have hli : l ∈ yi.footprint := by
        have := (hai.fpEq l).2 (hst.regionIn l hlr); simpa [S3.afp, hyi] using this
      have huq := usable_of_covered hnd hyi yia hli hlq
      obtain ⟨j, z, hz, za, hzh⟩ := ownedIn_holds hw hst.dstLeaf hown huq
      have := hst.dstFree j (List.mem_range.2 (lt_of_getElem? hz))
      rw [hz] at this; exact this za hzh
  · intro hp
    have h1 := hp.anchorOrder
    have h2 := hp.anchorOrderHeld
    have h3 := hp.keepsTarget
    rw [← effAnchorOK_store (p := dst) hy₀ hne, ← hpf] at h1
    rw [← heq] at h1 h2 h3
    exact ⟨h1, h2, h3⟩

/-- `issue` as its kernel sequence, per step (Part XIV, §77, §58): on a state satisfying the
kernel invariant, when the entry satisfies `ArenaInv` if live, the contract of `issue` and the
derived operation (`split` then `store`) have the same outcomes, `ok`, `fail` and `reject`, with
the same arrival state, kernel part included (literal equality, `issueKEff_eq`). On
library-reachable states the hypotheses hold (`issue_as_kernel`). -/
theorem issue_as_kernel_of_inv (k : K) {L : LState} {i : Nat} {region : List Nat} {dst : Nat}
    (hk : KInv L.kern)
    (hai : ∀ E, L.arenas[i]? = some E → Live L.kern E → ArenaInv L.kern E)
    (o : Outcome3 LState) : IssueC i region dst L o ↔ IssueD k i region dst L o := by
  have hw := hk.1
  have hnd := hk.2.1.2.2
  have e : ∀ E, issueL L i E region dst = ⟨storeEff (splitEff L.kern E.internal [region])
      L.kern.A.length dst, L.arenas.set i (issueMeta L.kern E region)⟩ := fun E => by
    rw [issueL, issueKEff_eq]
  constructor
  · intro h
    cases h with
    | noEntry h0 => exact .noEntry h0
    | static hE hs => exact .static hE hs
    | fail hE hs hav => exact .fail hE hs hav
    | noRight hE hs hav hr =>
      exact .split hE hs hav
        (.reject fun hp => hr ((issueRight_iff_split k (hai _ hE hs.live) hs).2 hp))
    | noArrival hE hs hav hr ha =>
      have hA := hai _ hE hs.live
      exact .store hE hs hav (.ok ((issueRight_iff_split k hA hs).1 hr))
        (.reject fun hp => ha ((arrival_iff_store hw hnd hA hs).2 hp))
    | @ok E hE hs hav hr ha =>
      have hA := hai _ hE hs.live
      rw [e E]
      exact .ok hE hs hav (.ok ((issueRight_iff_split k hA hs).1 hr))
        (.ok ((arrival_iff_store hw hnd hA hs).1 ha))
  · intro h
    cases h with
    | noEntry h0 => exact .noEntry h0
    | static hE hs => exact .static hE hs
    | fail hE hs hav => exact .fail hE hs hav
    | split hE hs hav hsp =>
      exact .noRight hE hs hav fun hr =>
        Guarded.reject_iff.1 hsp ((issueRight_iff_split k (hai _ hE hs.live) hs).1 hr)
    | store hE hs hav hsp hst =>
      have hA := hai _ hE hs.live
      obtain ⟨hp, rfl⟩ := Guarded.ok_iff.1 hsp
      exact .noArrival hE hs hav ((issueRight_iff_split k hA hs).2 hp)
        fun ha => Guarded.reject_iff.1 hst ((arrival_iff_store hw hnd hA hs).1 ha)
    | @ok E s₁ s₂ hE hs hav hsp hst =>
      have hA := hai _ hE hs.live
      obtain ⟨hp, rfl⟩ := Guarded.ok_iff.1 hsp
      obtain ⟨hq, rfl⟩ := Guarded.ok_iff.1 hst
      rw [← e E]
      exact .ok hE hs hav ((issueRight_iff_split k hA hs).2 hp)
        ((arrival_iff_store hw hnd hA hs).2 hq)

/-! ## `reset` as `derive` then `release` (Part XIV, §78) -/

/-- The kernel part of the effect of `reset` is the arrival state of `derive` of `internal` at
`Modify` over the storage followed by `release` of the derived authority (Part XIV, §78): literal
equality. -/
theorem resetKEff_eq (s : S3) (E : ArenaEntry) :
    resetKEff s E =
      releaseEff (deriveEff s E.internal (footprint s.P E.storage) .modify) s.A.length := by
  have hy : (deriveEff s E.internal (footprint s.P E.storage) .modify).A[s.A.length]? =
      some ⟨.modify, some E.internal, footprint s.P E.storage, .frame s.top, true⟩ := by
    simp [deriveEff, S3.addAuth]
  rw [releaseEff_eq hy]
  simp [resetKEff, deriveEff, S3.addAuth, List.set_append_right]

/-- `derive` and `split` on one region add the same authority and reach the same state
(Part XIV: "through `derive` or `split`"; §60, §61 `ok` effects). -/
theorem deriveEff_eq_split (s : S3) (src : Nat) (region : List Nat) :
    deriveEff s src region .modify = splitEff s src [region] := rfl

/-- Under `I3`, `release` of the authority just derived is always accepted (§62): it is active,
derived, held by the current frame, has no descendant and anchors no place. -/
theorem release_after_derive {s : S3} {src : Nat} {R : List Nat} {m : Mode} (h3 : I3 s) :
    ReleasePre (deriveEff s src R m) s.A.length := by
  have hy₀ : (deriveEff s src R m).A[s.A.length]? = some ⟨m, some src, R, .frame s.top, true⟩ := by
    simp [deriveEff, S3.addAuth]
  refine ⟨⟨_, hy₀, rfl⟩, by rw [hy₀]; simp [OptP], by rw [hy₀]; exact rfl,
    fun j hj hn => ?_, fun q _ hq hx => ?_⟩
  · have := chain_lt hn
    have := List.mem_range.1 hj; simp [deriveEff, S3.addAuth] at this; omega
  · obtain ⟨z, hz, -⟩ :=
      h3 q ((S3.Usable.congr (s := s) (s' := deriveEff s src R m) rfl rfl rfl).1 hq) _ hx
    have := lt_of_getElem? hz; omega

/-- §60.2 for `derive` of `internal` at `Modify` over the storage gives §78.2: an active
derivative of `internal` covering a leaf of the storage would take the effective `Modify` of
`internal` on that leaf away (§43, case 3). -/
theorem noCover_of_derive {s : S3} {E : ArenaEntry}
    (hd : DerivePre s E.internal (footprint s.P E.storage) .modify) :
    ∀ j ∈ List.range s.A.length, E.internal ∈ s.ancs j → s.Active j →
      ∀ l ∈ s.afp j, l ∉ footprint s.P E.storage := by
  intro j _ ha hja l hl hls
  obtain ⟨y, hy, ya⟩ := hja
  have hly : l ∈ y.footprint := by simpa [S3.afp, hy] using hl
  exact no_desc_of_modify hy ya hly ha (allows_modify_iff.1 (hd.modeOK l hls))

/-- v0.1 §78.3, second sentence: under precondition 2 of §78 and invariant I3 (§52; a valid
anchor is an active one, §51), §78.3 holds. An anchor of a usable place is active (I3), so an
anchor in the strict origin subtree of `internal` covering a leaf of the storage would be an
active derivative of `internal` covering that leaf, which §78.2 excludes. -/
theorem resetNoDeps_of_noCover {s : S3} {E : ArenaEntry} (h3 : I3 s)
    (h2 : ∀ j ∈ List.range s.A.length, E.internal ∈ s.ancs j → s.Active j →
      ∀ l ∈ s.afp j, l ∉ footprint s.P E.storage) : ResetNoDeps s E := by
  intro q _ hq x hx hix l hl hls
  obtain ⟨y, hy, ya⟩ := h3 q hq x hx
  exact h2 x (List.mem_range.2 (lt_of_getElem? hy)) hix ⟨y, hy, ya⟩ l hl hls

/-- On states satisfying I3, the explicit check of §78.3 in `ResetD` never rejects after an
accepted `derive` of `internal` over the storage (v0.1 §78.3, second sentence;
`noCover_of_derive`, `resetNoDeps_of_noCover`): the derived `reset` is its kernel sequence. -/
theorem resetNoDeps_of_derive {s : S3} {E : ArenaEntry} (h3 : I3 s)
    (hd : DerivePre s E.internal (footprint s.P E.storage) .modify) : ResetNoDeps s E :=
  resetNoDeps_of_noCover h3 (noCover_of_derive hd)

/-- Under `WF3`, `I1`, `I2` and `ArenaInv` of a live entry, the preconditions of `reset` are
exactly the preconditions of `derive` of `internal` at `Modify` over the storage (§60) and the
explicit check of §78.3: §78.1 is §60.1 (`metaRight_iff`; the origin chain of the active `internal`
is active by I2, §51), §78.2 is §60.2 (effective `Modify` on every leaf of the storage), §60.3
follows from I1. -/
theorem resetPre_iff {s : S3} {E : ArenaEntry} (hw : WF3 s) (h1 : I1 s) (h2 : I2 s)
    (hai : Live s E → ArenaInv s E) :
    ResetPre s E ↔
      DerivePre s E.internal (footprint s.P E.storage) .modify ∧ ResetNoDeps s E := by
  constructor
  · intro hp
    have hA := hai hp.live
    have hsh := hA.shape
    obtain ⟨yi, hyi, yia⟩ := hp.live
    rw [hyi] at hsh
    have hli : ∀ l ∈ footprint s.P E.storage, l ∈ yi.footprint := fun l hl => by
      have := (hA.fpEq l).2 hl; simpa [S3.afp, hyi] using this
    have hmod : ∀ l ∈ footprint s.P E.storage, Allows (effective s E.internal l) .modify := by
      intro l hl
      have hd : descModes s E.internal l = [] := by
        apply nil_of_forall_not_mem; intro e he
        obtain ⟨j, y, hy, ya, hly, hj, -⟩ := mem_descModes.1 he
        exact hp.noCover j (List.mem_range.2 (lt_of_getElem? hy)) hj ⟨y, hy, ya⟩ l
          (by simp [S3.afp, hy, hly]) hl
      rw [effective_eq hyi yia (hli l hl), hd]
      simp [effOf, hsh.1, Allows, OptP, Mode.le]
    refine ⟨⟨⟨yi, hyi, yia⟩, (metaRight_iff hA).1 hp.metaRight, h2.ancs_active ⟨yi, hyi, yia⟩,
      fun l hl => (mem_footprint.1 hl).elim fun h h' => ⟨h, h'.1⟩,
      fun l hl => (hA.fpEq l).2 hl, hmod, fun b _ => ?_, top_mem hw.frames.1⟩, hp.noDeps⟩
    unfold OptP; split
    · rename_i y hy
      rintro ya hb ⟨l, hl, hly⟩
      have hb1 : b ≠ E.internal := fun h => hb (h ▸ List.mem_cons_self ..)
      have hb2 : b ∉ s.ancs E.internal := fun h => hb (List.mem_cons_of_mem _ h)
      obtain ⟨h₁, h₂⟩ := new_vs_old h1 hyi yia (hli l hl) (hmod l hl) hy ya hly hb1 hb2
      exact ⟨h₂, h₁⟩
    · trivial
  · rintro ⟨hd, h3⟩
    have hA := hai hd.active
    exact ⟨hd.active, (metaRight_iff hA).2 hd.exercisable, noCover_of_derive hd, h3⟩

/-- `reset` as its kernel sequence, per step (Part XIV, §78, §58): on a state satisfying the
kernel invariant, when the entry satisfies `ArenaInv` if live, the contract of `reset` and the
derived operation (`derive` then `release`, then the explicit check of §78.3) have the same
outcomes, `ok` and `reject`, with the same arrival state, kernel part included (literal equality,
`resetKEff_eq`). On library-reachable states the hypotheses hold (`reset_as_kernel`). -/
theorem reset_as_kernel_of_inv {L : LState} {i : Nat} (hk : KInv L.kern)
    (hai : ∀ E, L.arenas[i]? = some E → Live L.kern E → ArenaInv L.kern E)
    (o : Outcome3 LState) : ResetC i L o ↔ ResetD i L o := by
  have hw := hk.1
  have h1 := hk.2.1.1.1
  have h2 := hk.2.1.1.2.1
  have h3 := hk.2.1.1.2.2.1
  have e : ∀ E, resetL L i E = ⟨releaseEff (deriveEff L.kern E.internal
      (footprint L.kern.P E.storage) .modify) L.kern.A.length,
      L.arenas.set i (resetMeta L.kern E)⟩ := fun E => by
    rw [resetL, resetKEff_eq]
  constructor
  · intro h
    cases h with
    | noEntry h0 => exact .noEntry h0
    | @reject E hE hn =>
      have hiff := resetPre_iff hw h1 h2 (hai E hE)
      by_cases hd : DerivePre L.kern E.internal (footprint L.kern.P E.storage) .modify
      · exact .contract hE (.ok hd) (.ok (release_after_derive h3)) fun h3' => hn (hiff.2 ⟨hd, h3'⟩)
      · exact .derive hE (.reject hd)
    | @ok E hE hp =>
      obtain ⟨hd, h3'⟩ := (resetPre_iff hw h1 h2 (hai E hE)).1 hp
      rw [e E]
      exact .ok hE (.ok hd) (.ok (release_after_derive h3)) h3'
  · intro h
    cases h with
    | noEntry h0 => exact .noEntry h0
    | @derive E hE hd =>
      exact .reject hE fun hp =>
        Guarded.reject_iff.1 hd ((resetPre_iff hw h1 h2 (hai E hE)).1 hp).1
    | @release E s₁ hE hd hr =>
      obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hd
      exact absurd (release_after_derive h3) (Guarded.reject_iff.1 hr)
    | @contract E s₁ s₂ hE hd _ hn =>
      exact .reject hE fun hp => hn ((resetPre_iff hw h1 h2 (hai E hE)).1 hp).2
    | @ok E s₁ s₂ hE hd hr h3' =>
      obtain ⟨hd', rfl⟩ := Guarded.ok_iff.1 hd
      obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hr
      rw [← e E]
      exact .ok hE ((resetPre_iff hw h1 h2 (hai E hE)).2 ⟨hd', h3'⟩)

/-! ## Effects of `issue` and `reset` (§77, §78) -/

/-- The `ok` effect of the derived `issue` of entry `i` (§77): the kernel state is `issueKEff`
(`issueKEff_eq`); the entry becomes `issueMeta`, earlier issuances kept; former authorities are
unchanged; only leaf `destination` changes initialization and only its anchors change. -/
theorem issue_effect {k : K} {L L' : LState} {i : Nat} {region : List Nat} {dst : Nat}
    {E : ArenaEntry} (hE : L.arenas[i]? = some E) (hs : IssueD k i region dst L (.ok L')) :
    L'.kern = issueKEff L.kern E region dst ∧
    L'.arenas[i]? = some (issueMeta L.kern E region) ∧
    (∀ e ∈ E.issued, e ∈ (issueMeta L.kern E region).issued) ∧
    (∀ x < L.kern.A.length, L'.kern.A[x]? = L.kern.A[x]?) ∧
    (∀ l, l ≠ dst → L'.kern.I l = L.kern.I l) ∧ L'.kern.I dst = .init ∧
    ∀ q, q ≠ dst → L'.kern.D q = L.kern.D q := by
  cases hs with
  | @ok E' s₁ s₂ hE' _ _ hsp hsto =>
  rw [hE] at hE'; cases hE'
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hsp
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hsto
  rw [← issueKEff_eq]
  refine ⟨rfl, ?_, fun e he => List.mem_cons_of_mem _ he, fun x hx => ?_, fun l hl => ?_, ?_,
    fun q hq => ?_⟩
  · simp only [List.getElem?_set, lt_of_getElem? hE, ↓reduceIte]
  · exact List.getElem?_append_left hx
  · simp [issueKEff, hl]
  · simp [issueKEff]
  · simp [issueKEff, hq]

/-- v0.1 §86 (initialization state): an accepted derived `issue` leaves the initialization state of
every leaf of the issued region unchanged, so a reissued leaf keeps its initialization state. Only
leaf `destination` becomes `Init` (§77 `ok` effect), and it is not in the region (§77.2). -/
theorem issue_keeps_init {k : K} {L L' : LState} {i : Nat} {region : List Nat} {dst : Nat}
    (hs : IssueD k i region dst L (.ok L')) : ∀ l ∈ region, L'.kern.I l = L.kern.I l := by
  cases hs with
  | @ok E s₁ s₂ hE hst _ hsp hsto =>
    intro l hl
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hsp
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hsto
    rw [← issueKEff_eq]
    have hne : l ≠ dst := fun h => hst.dstNotIn (h ▸ hl)
    simp [issueKEff, hne]

/-- v0.1 §86 (initialization state) for the contract of `issue` (§77): an `ok` leaves the
initialization state of every leaf of the issued region unchanged. -/
theorem issueC_keeps_init {L L' : LState} {i : Nat} {region : List Nat} {dst : Nat}
    (hs : IssueC i region dst L (.ok L')) : ∀ l ∈ region, L'.kern.I l = L.kern.I l := by
  cases hs with
  | ok _ hst _ _ _ =>
    intro l hl
    have hne : l ≠ dst := fun h => hst.dstNotIn (h ▸ hl)
    simp [issueL, issueKEff, hne]

/-- The `ok` effect of the derived `reset` of entry `i` (§78): the kernel state is `resetKEff`
(`resetKEff_eq`), which adds only an inactive record: places, initialization ("no leaf is made
`Init` by `reset`"), anchors, and former authorities are unchanged; the entry becomes
`resetMeta`, all leaves of the storage available and `issued` cleared. -/
theorem reset_effect {L L' : LState} {i : Nat} {E : ArenaEntry} (hE : L.arenas[i]? = some E)
    (hs : ResetD i L (.ok L')) :
    L'.kern = resetKEff L.kern E ∧ L'.arenas[i]? = some (resetMeta L.kern E) ∧
    L'.kern.P = L.kern.P ∧ L'.kern.I = L.kern.I ∧ L'.kern.D = L.kern.D ∧
    (∀ x < L.kern.A.length, L'.kern.A[x]? = L.kern.A[x]?) ∧
    ¬ L'.kern.Active L.kern.A.length := by
  cases hs with
  | @ok E' s₁ s₂ hE' hd hrl _ =>
  rw [hE] at hE'; cases hE'
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hd
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hrl
  rw [← resetKEff_eq]
  refine ⟨rfl, ?_, rfl, rfl, rfl, fun x hx => List.getElem?_append_left hx, ?_⟩
  · simp only [List.getElem?_set, lt_of_getElem? hE, ↓reduceIte]
  · rintro ⟨y, hy, ya⟩
    simp [resetKEff] at hy; rw [← hy] at ya; cases ya

/-- §88, §77.2: `issue` into a leaf of the issued region is rejected, by a static check, even
when the region is unavailable (no `fail`). -/
theorem issue_into_region_rejected {L : LState} {i : Nat} {region : List Nat} {dst : Nat}
    {o : Outcome3 LState} (hd : dst ∈ region) (h : IssueC i region dst L o) : o = .reject := by
  cases h with
  | noEntry => rfl
  | static => rfl
  | fail _ hs => exact absurd hd hs.dstNotIn
  | noRight => rfl
  | noArrival => rfl
  | ok _ hs => exact absurd hd hs.dstNotIn

/-- §88, §77.6 (O8.5): `issue` into a destination that would no longer be under exercisable
`Modify` in the resulting state is not `ok`. -/
theorem issue_keeps_dst {L L' : LState} {i : Nat} {region : List Nat} {dst : Nat}
    (h : IssueC i region dst L (.ok L')) :
    ∃ E, L.arenas[i]? = some E ∧ HasRight (issueKEff L.kern E region dst) .modify dst := by
  cases h with
  | ok hE _ _ _ ha => exact ⟨_, hE, ha.keepsDst⟩

/-! ## Library runs (Part XIV, §46, §56, §57) -/

/-- One `ok` step of a library run (Part XIV): a kernel step O1–O16 of non-administrative code,
the registry unchanged; `newArena` with the guard of §56 against the other registries `others`;
the derived `issue` or `reset`. -/
inductive LStep (k : K) : LState → LState → Prop where
  | kernel {L : LState} {s' : S3} : KStep k L.kern s' → LStep k L ⟨s', L.arenas⟩
  | newArena {L L' : LState} {others : List (List Nat)} {st i : Nat} :
      NewArenaStep others st i L (.ok L') → LStep k L L'
  | issue {L L' : LState} {i : Nat} {region : List Nat} {dst : Nat} :
      IssueD k i region dst L (.ok L') → LStep k L L'
  | reset {L L' : LState} {i : Nat} : ResetD i L (.ok L') → LStep k L L'

/-- One `ok` step of a library run in which `newArena` registers without the guard of §56
(§76.4 removed, the other preconditions of §76 kept). -/
inductive LStepNG (k : K) : LState → LState → Prop where
  | kernel {L : LState} {s' : S3} : KStep k L.kern s' → LStepNG k L ⟨s', L.arenas⟩
  | newArena {L : LState} {st i : Nat} : NewArenaBase L.kern st i →
      LStepNG k L (newArenaEff L st i)
  | issue {L L' : LState} {i : Nat} {region : List Nat} {dst : Nat} :
      IssueD k i region dst L (.ok L') → LStepNG k L L'
  | reset {L L' : LState} {i : Nat} : ResetD i L (.ok L') → LStepNG k L L'

/-- Library states reachable from the initial library state (§47) by library steps (Part
XIV). -/
inductive LReach (k : K) (statics : Statics) : LState → Prop where
  | init : LReach k statics (LState.init statics)
  | step {L L' : LState} : LReach k statics L → LStep k L L' → LReach k statics L'

/-- Library states reachable when `newArena` registers without the guard of §56. -/
inductive LReachNG (k : K) (statics : Statics) : LState → Prop where
  | init : LReachNG k statics (LState.init statics)
  | step {L L' : LState} : LReachNG k statics L → LStepNG k L L' → LReachNG k statics L'

/-- Finite sequences of library steps (Part XIV, §46). -/
inductive LRun (k : K) : LState → LState → Prop where
  | refl (L : LState) : LRun k L L
  | tail {L L' L'' : LState} : LRun k L L' → LStep k L' L'' → LRun k L L''

/-- `newArena` changes no kernel component (Part XIV, §76 `ok` effect: registering the entry
fabricates no place, access right or `Init` state). -/
theorem newArena_kernel {others : List (List Nat)} {st i : Nat} {L L' : LState}
    (h : NewArenaStep others st i L (.ok L')) : L'.kern = L.kern := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; rfl

/-- A guarded library step is a step without the guard (§56). -/
theorem LStep.ng {k : K} {L L' : LState} (h : LStep k L L') : LStepNG k L L' := by
  cases h with
  | kernel hk => exact .kernel hk
  | newArena hs => obtain ⟨hp, rfl⟩ := Guarded.ok_iff.1 hs; exact .newArena hp.base
  | issue hs => exact .issue hs
  | reset hs => exact .reset hs

/-- Every library-reachable state is reachable without the guard (§56). -/
theorem LReach.ng {k : K} {statics : Statics} {L : LState} (h : LReach k statics L) :
    LReachNG k statics L := by
  induction h with
  | init => exact .init
  | step _ hs ih => exact .step ih hs.ng

/-- The kernel part of a library step without the guard is reached by kernel steps (Part XIV,
§57: `newArena` changes no kernel component, `issue` is `split` then `store`, `reset` is `derive`
then `release`). -/
theorem LStepNG.reachable {k : K} {statics : Statics} {L L' : LState}
    (hr : Reachable k statics L.kern) (h : LStepNG k L L') : Reachable k statics L'.kern := by
  cases h with
  | kernel hk => exact .step hr hk
  | newArena _ => exact hr
  | issue hs =>
    cases hs with
    | ok _ _ _ hsp hst => exact .step (.step hr (.split hsp)) (.store hst)
  | reset hs =>
    cases hs with
    | ok _ hd hrl _ => exact .step (.step hr (.derive hd)) (.release hrl)

/-- The kernel state of every library state reachable without the guard is kernel-reachable
(§57, Part XIV). -/
theorem LReachNG.reachable {k : K} {statics : Statics} {L : LState}
    (h : LReachNG k statics L) : Reachable k statics L.kern := by
  induction h with
  | init => exact .init
  | step _ hs ih => exact hs.reachable ih

/-- `newArena_as_library` (Part XIV, §56, §57): registration changes no kernel component, and no
safety property of §57 depends on the guard of §56: every property of kernel-reachable states holds
for the kernel states of library runs with or without the guard. -/
theorem newArena_as_library (k : K) (statics : Statics) :
    (∀ (others : List (List Nat)) (st i : Nat) (L L' : LState),
      NewArenaStep others st i L (.ok L') → L'.kern = L.kern) ∧
    (∀ L, LReach k statics L → LReachNG k statics L) ∧
    ∀ Q : S3 → Prop, (∀ s, Reachable k statics s → Q s) →
      ∀ L, LReachNG k statics L → Q L.kern :=
  ⟨fun _ _ _ _ _ h => newArena_kernel h, fun _ h => h.ng, fun _ hQ _ h => hQ _ h.reachable⟩

/-! ## Transport of `EntryInv` (§55) -/

/-- `s'` keeps the authorities of `s` (§42, §58): each keeps its mode and footprint, becomes
active only if it was, stays held by a place if it was, and keeps an origin `o` below it that is
active in `s'`. -/
def AKeep (s s' : S3) : Prop :=
  ∀ j y, s.A[j]? = some y → ∃ y', s'.A[j]? = some y' ∧ y'.mode = y.mode ∧
    y'.footprint = y.footprint ∧ (y'.active = true → y.active = true) ∧
    (y'.holder.isPlace = false → y.holder.isPlace = false) ∧
    ∀ o, y.origin = some o → o < j → s'.Active o → y'.origin = some o

/-- Authorities are never reactivated (§42, §58). -/
theorem AKeep.active_back {s s' : S3} (h : AKeep s s') {x : Nat} (hx : s'.Active x)
    (hlt : x < s.A.length) : s.Active x := by
  obtain ⟨y, hy⟩ : ∃ y, s.A[x]? = some y := ⟨_, List.getElem?_eq_some_iff.2 ⟨hlt, rfl⟩⟩
  obtain ⟨y', hy', -, -, ha, -⟩ := h x y hy
  obtain ⟨z, hz, za⟩ := hx
  rw [hy'] at hz; cases hz; exact ⟨y, hy, ha za⟩

/-- Authorities are never removed (§42). -/
theorem AKeep.lt {s s' : S3} (h : AKeep s s') {x : Nat} (hlt : x < s.A.length) :
    x < s'.A.length := by
  obtain ⟨y', hy', -⟩ := h x _ (List.getElem?_eq_some_iff.2 ⟨hlt, rfl⟩)
  exact lt_of_getElem? hy'

/-- `AKeep` composes (§42). -/
theorem AKeep.trans {s s' s'' : S3} (h : AKeep s s') (h' : AKeep s' s'') : AKeep s s'' := by
  intro j y hy
  obtain ⟨y', hy', m, f, a, p, o⟩ := h j y hy
  obtain ⟨y'', hy'', m', f', a', p', o'⟩ := h' j y' hy'
  refine ⟨y'', hy'', m'.trans m, f'.trans f, fun h => a (a' h), fun h => p (p' h),
    fun x hx hxj hxa => o' x (o x hx hxj ?_) hxj hxa⟩
  obtain ⟨z, hz, za⟩ := hxa
  obtain ⟨w, hw⟩ : ∃ w, s'.A[x]? = some w := by
    obtain ⟨y₀, hy₀⟩ : ∃ y₀, s.A[x]? = some y₀ :=
      ⟨_, List.getElem?_eq_some_iff.2 ⟨Nat.lt_trans hxj (lt_of_getElem? hy), rfl⟩⟩
    obtain ⟨w, hw, -⟩ := h x y₀ hy₀; exact ⟨w, hw⟩
  obtain ⟨z', hz', -, -, ha, -⟩ := h' x w hw
  rw [hz] at hz'; cases hz'; exact ⟨w, hw, ha za⟩

/-- Unchanged authorities (§42). -/
theorem akeep_of_eq {s s' : S3} (hA : s'.A = s.A) : AKeep s s' := by
  intro j y hy
  refine ⟨y, by rw [hA]; exact hy, rfl, rfl, id, id, fun o ho _ _ => ho⟩

/-- Appended authorities (§60, §61, §71, §77, §78). -/
theorem akeep_append {s s' : S3} {l : List Authority} (hA : s'.A = s.A ++ l) : AKeep s s' := by
  intro j y hy
  refine ⟨y, by rw [hA, List.getElem?_append_left (lt_of_getElem? hy)]; exact hy, rfl, rfl, id,
    id, fun o ho _ _ => ho⟩

/-- Authorities mapped by a function keeping mode, footprint, origin and place holders, and
activating nothing (§62, §63, §69, §70). -/
theorem akeep_map {s s' : S3} {f : Authority → Authority} (hA : s'.A = s.A.map f)
    (hf : ∀ y, (f y).mode = y.mode ∧ (f y).footprint = y.footprint ∧
      ((f y).active = true → y.active = true) ∧
      ((f y).holder.isPlace = false → y.holder.isPlace = false) ∧ (f y).origin = y.origin) :
    AKeep s s' := by
  intro j y hy
  obtain ⟨h1, h2, h3, h4, h5⟩ := hf y
  exact ⟨f y, by rw [hA, List.getElem?_map, hy]; rfl, h1, h2, h3, h4, fun o ho _ _ => h5 ▸ ho⟩

/-- One authority replaced by a record with the same mode, footprint and origin, active only if
it was, held by a place if it was (§62, §65). -/
theorem akeep_set {s s' : S3} {a : Nat} {x x' : Authority} (hx : s.A[a]? = some x)
    (hA : s'.A = s.A.set a x') (hm : x'.mode = x.mode) (hf : x'.footprint = x.footprint)
    (ha : x'.active = true → x.active = true)
    (hp : x'.holder.isPlace = false → x.holder.isPlace = false) (ho : x'.origin = x.origin) :
    AKeep s s' := by
  intro j y hy
  by_cases hj : a = j
  · subst hj; rw [hx] at hy; cases hy
    exact ⟨x', by rw [hA, List.getElem?_set_self (lt_of_getElem? hx)], hm, hf, ha, hp,
      fun o h _ _ => ho ▸ h⟩
  · exact ⟨y, by rw [hA, List.getElem?_set_ne hj]; exact hy, rfl, rfl, id, id,
      fun o h _ _ => h⟩

/-- `EntryInv` carries over to a state keeping the authorities (`AKeep`), the footprint and the
usability of the storage, when the entry is still live (§55). -/
theorem entryInv_transport {s s' : S3} {E : ArenaEntry} (h : EntryInv s E) (hA : AKeep s s')
    (hfp : ∀ l, l ∈ footprint s'.P E.storage ↔ l ∈ footprint s.P E.storage)
    (hus : s'.Usable E.storage) (hlive : s'.Active E.internal) : EntryInv s' E := by
  obtain ⟨hai, hsh⟩ := h
  obtain ⟨yi, hyi, -⟩ := hai.active
  obtain ⟨yi', hyi', mi, fi, -, pi, -⟩ := hA _ yi hyi
  have hafp : ∀ l, l ∈ s'.afp E.internal ↔ l ∈ s.afp E.internal := by
    intro l; simp [S3.afp, hyi, hyi', fi]
  have old : ∀ e ∈ E.issued, e.2 < s.A.length := fun e he => by
    obtain ⟨y, hy, -⟩ := hsh e he; exact lt_of_getElem? hy
  have act : ∀ e ∈ E.issued, s'.Active e.2 → s.Active e.2 :=
    fun e he ha => hA.active_back ha (old e he)
  have hsh' : IssuedShape s' E := by
    intro e he
    obtain ⟨y, hy, ho, hlt, hf, hm⟩ := hsh e he
    obtain ⟨y', hy', m', f', -, -, o'⟩ := hA e.2 y hy
    exact ⟨y', hy', o' _ ho hlt hlive, hlt, f'.trans hf, m'.trans hm⟩
  refine ⟨⟨hus, fun l => (hafp l).trans ((hai.fpEq l).trans (hfp l).symm), hlive, ?_,
    fun l hl => (hfp l).2 (hai.availableIn l hl),
    fun e he l hl => (hfp l).2 (hai.issuedIn e he l hl),
    fun e he e' he' hne ha ha' => hai.disjoint e he e' he' hne (act e he ha) (act e' he' ha'),
    fun e he ha => hai.notAvailable e he (act e he ha), fun e he ha => ?_⟩, hsh'⟩
  · have hs := hai.shape; rw [hyi] at hs; rw [hyi']
    refine ⟨mi.trans hs.1, ?_⟩
    cases e : yi'.holder.isPlace
    · exact absurd (pi e) (by rw [hs.2]; decide)
    · rfl
  · obtain ⟨y', hy', ho', hlt, -⟩ := hsh' e he
    unfold S3.ancs; rw [chain_cons (by simp [S3.org, hy', ho']) hlt]
    exact List.mem_cons_self ..

/-! ## Kernel steps keep the authorities and the footprints (§42, §58, §60–§75) -/

/-- `exitFrame` keeps the authorities (§73, `ok` effect): a surviving authority keeps an origin
that survives, the first surviving element of its chain. -/
theorem exit_akeep (s : S3) : AKeep s (exitEff s) := by
  intro j y hy
  have hA : ∀ x, (exitEff s).A[x]? = (s.A[x]?).map (exitG s s.F.tail x) := fun x => by
    simp only [exitEff, getElem?_mapI, Nat.zero_add]
  refine ⟨_, by rw [hA, hy]; rfl, ?_⟩
  unfold exitG
  by_cases hsv : Survives s s.F.tail j
  · have ya : y.active = true := by
      have h := hsv; unfold Survives at h; rw [hy] at h; exact h.1
    rw [ite_eq_left_of_eq_true _ _ (eq_true hsv)]
    split
    · exact ⟨rfl, rfl, fun _ => ya, id, fun o h _ _ => h⟩
    · rename_i o' ho'
      refine ⟨rfl, rfl, fun _ => ya, id, fun o h hoj hoa => ?_⟩
      rw [ho'] at h; cases h
      obtain ⟨z, hz, za⟩ := hoa
      rw [hA] at hz
      cases hw : s.A[o']? with
      | none => rw [hw] at hz; cases hz
      | some w =>
        rw [hw] at hz; simp only [Option.map_some, Option.some.injEq] at hz; subst hz
        have hso : Survives s s.F.tail o' := by
          unfold exitG at za; split at za
          · assumption
          · simp at za
        have horg : s.org j = some o' := by simp [S3.org, hy, ho']
        show firstSurv s s.F.tail (s.ancs j) = some o'
        unfold S3.ancs; rw [chain_cons horg hoj]
        simp [firstSurv, hso]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hsv)]
    exact ⟨rfl, rfl, fun h => by simp at h, id, fun o h _ _ => h⟩

/-- Every kernel step keeps the authorities (§42, §58; §60–§75 `ok` effects): none is removed,
reactivated, or given another mode or footprint. -/
theorem kstep_akeep {k : K} {s s' : S3} (h : KStep k s s') : AKeep s s' := by
  cases h with
  | derive hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact akeep_append rfl
  | split hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact akeep_append rfl
  | release hs =>
    obtain ⟨hp, rfl⟩ := Guarded.ok_iff.1 hs
    obtain ⟨x, hx, -⟩ := hp.active
    exact akeep_set (x' := { x with active := false }) hx (by rw [releaseEff_eq hx]) rfl rfl
      (fun h => by simp at h) id rfl
  | transfer hs =>
    rename_i src dst
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
    refine akeep_map rfl fun y => ?_
    cases e : y.holder with
    | frame f => simp [heldIn, e, Holder.isPlace]
    | place r => by_cases hc : partOf s.P r src <;> simp [heldIn, hc, mvTo, Holder.isPlace, e]
  | depend hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact akeep_of_eq rfl
  | enter hs =>
    rename_i ps ls
    obtain ⟨hp, rfl⟩ := Guarded.ok_iff.1 hs
    intro j y hy
    have hj := lt_of_getElem? hy
    refine ⟨if j ∈ ps then { y with holder := .frame s.nF } else y, ?_, ?_⟩
    · simp only [enterEff]
      rw [List.getElem?_append_left (by rw [length_mapI]; exact hj), getElem?_mapI, hy]
      simp
    · by_cases hjp : j ∈ ps
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hjp)]
        refine ⟨rfl, rfl, id, fun _ => ?_, fun o h _ _ => h⟩
        have := hp.params j hjp; rw [hy] at this
        rw [this.2.1]; rfl
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hjp)]; exact ⟨rfl, rfl, id, id, fun o h _ _ => h⟩
  | exit hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact exit_akeep s
  | read hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact akeep_of_eq rfl
  | write hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact akeep_of_eq rfl
  | writeShared hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact akeep_of_eq rfl
  | pin hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact akeep_of_eq rfl
  | unpin hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact akeep_of_eq rfl
  | endUse hs =>
    rename_i p
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
    refine (akeep_map (s' := endUseS s p) rfl fun y => ?_).trans (akeep_map rfl fun y => ?_)
    · by_cases hc : heldIn s.P p y.holder <;> simp [hc]
    · by_cases hc : HolderLive (endUseS s p) y.holder <;> simp [hc]
  | free hs =>
    rename_i p _
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
    refine (akeep_map (s' := freeS s p) rfl fun y => ?_).trans (akeep_map rfl fun y => ?_)
    · by_cases hc : (∃ l ∈ y.footprint, FreedPlace s.P p l) ∨ heldIn s.P p y.holder <;> simp [hc]
    · by_cases hc : HolderLive (freeS s p) y.holder <;> simp [hc]
  | alloc hs => cases hs with
    | ok _ _ => exact akeep_append rfl
  | store hs =>
    rename_i a p
    obtain ⟨hp, rfl⟩ := Guarded.ok_iff.1 hs
    have hd := hp.derivedHeld
    cases hy : s.A[a]? with
    | none => rw [hy] at hd; exact hd.elim
    | some y =>
      exact akeep_set (x' := { y with holder := .place p }) hy (by rw [storeEff_eq hy]) rfl rfl
        id (fun h => by simp [Holder.isPlace] at h) rfl

/-- Structural parents of the former places are kept by appending a shape (§47, §71, §72). -/
theorem parentOf_shapeP_lt {P : List Place} {hd : Holder}
    {ls : List (Option Nat × Option Nat × Nat)} {j : Nat} (hj : j < P.length) :
    parentOf (shapeP P hd ls) j = parentOf P j := by
  simp only [parentOf, shapeP, List.getElem?_append_left hj]

/-- The parent of an element appended by a well-formed shape is an appended element (§71.1,
§72.2). -/
theorem shapeP_parent_ge {P : List Place} {hd : Holder} {ls : List (Option Nat × Option Nat × Nat)}
    (hok : ShapeOK P.length ls) {j r : Nat} (hj : P.length ≤ j)
    (h : parentOf (shapeP P hd ls) j = some r) : P.length ≤ r := by
  unfold parentOf shapeP at h
  rw [List.getElem?_append_right hj, List.getElem?_map] at h
  cases hi : (List.range ls.length)[j - P.length]? with
  | none => rw [hi] at h; simp at h
  | some i =>
    rw [hi] at h
    obtain ⟨hlt, hii⟩ := List.getElem?_eq_some_iff.1 hi
    simp only [List.getElem_range] at hii
    subst hii
    simp only [Option.map_some, Option.bind_some] at h
    have := (hok (j - P.length) (List.mem_range.2 (by simpa using hlt))).1
    rw [h] at this
    exact this.1

/-- The chain of an appended element stays among the appended elements (§71.1, §72.2). -/
theorem chainF_shapeP_ge {P : List Place} {hd : Holder} {ls : List (Option Nat × Option Nat × Nat)}
    (hok : ShapeOK P.length ls) :
    ∀ k i, P.length ≤ i → ∀ x ∈ chainF (parentOf (shapeP P hd ls)) k i, P.length ≤ x
  | 0, _, _, _, h => by simp [chainF] at h
  | k + 1, i, hi, x, h => by
    simp only [chainF] at h
    split at h
    · rename_i o ho
      split at h
      · have hoP := shapeP_parent_ge hok hi ho
        rcases List.mem_cons.1 h with rfl | h
        · exact hoP
        · exact chainF_shapeP_ge hok k o hoP x h
      · simp at h
    · simp at h

/-- Appending a well-formed shape keeps the footprint of every former place (§40; §71, §72
effects). -/
theorem footprint_shapeP {P : List Place} {hd : Holder} {ls : List (Option Nat × Option Nat × Nat)}
    (hok : ShapeOK P.length ls) {q : Nat} (hq : q < P.length) (l : Nat) :
    l ∈ footprint (shapeP P hd ls) q ↔ l ∈ footprint P q := by
  rw [mem_footprint, mem_footprint]
  have hlen : P.length ≤ (shapeP P hd ls).length := by simp [shapeP]
  have hch : ∀ i, i < P.length →
      chain (parentOf (shapeP P hd ls)) i = chain (parentOf P) i := fun i hi =>
    chain_congr fun j hj => parentOf_shapeP_lt (Nat.lt_of_le_of_lt hj hi)
  constructor
  · rintro ⟨-, hleaf, -, hpart⟩
    by_cases hlP : l < P.length
    · refine ⟨hlP, fun r hr => ?_, hlP, ?_⟩
      · have := hleaf r (Nat.lt_of_lt_of_le hr hlen); rwa [parentOf_shapeP_lt hr] at this
      · rcases hpart with rfl | hc
        · exact .inl rfl
        · exact .inr (by rwa [← hch l hlP])
    · exfalso
      rcases hpart with rfl | hc
      · exact hlP hq
      · have := chainF_shapeP_ge hok _ _ (Nat.le_of_not_lt hlP) _ hc; omega
  · rintro ⟨hlP, hleaf, -, hpart⟩
    refine ⟨Nat.lt_of_lt_of_le hlP hlen, fun r hr => ?_, Nat.lt_of_lt_of_le hlP hlen, ?_⟩
    · by_cases hrP : r < P.length
      · rw [parentOf_shapeP_lt hrP]; exact hleaf r hrP
      · intro h; have := shapeP_parent_ge hok (Nat.le_of_not_lt hrP) h; omega
    · rcases hpart with rfl | hc
      · exact .inl rfl
      · exact .inr (by rwa [hch l hlP])

/-- Every kernel step keeps the footprint of every existing place (§40; §60–§75 `ok` effects:
places are only appended, and `transfer` changes owners only). -/
theorem kstep_fp {k : K} {s s' : S3} (h : KStep k s s') {q : Nat} (hq : q < s.P.length) (l : Nat) :
    l ∈ footprint s'.P q ↔ l ∈ footprint s.P q := by
  cases h with
  | derive hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact Iff.rfl
  | split hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact Iff.rfl
  | release hs =>
    obtain ⟨hp, rfl⟩ := Guarded.ok_iff.1 hs
    obtain ⟨x, hx, -⟩ := hp.active
    rw [releaseEff_eq hx]
  | transfer hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; rw [transfer_footprint]
  | depend hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact Iff.rfl
  | enter hs =>
    obtain ⟨hp, rfl⟩ := Guarded.ok_iff.1 hs
    exact footprint_shapeP hp.localsOK hq l
  | exit hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact Iff.rfl
  | read hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact Iff.rfl
  | write hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact Iff.rfl
  | writeShared hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact Iff.rfl
  | pin hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact Iff.rfl
  | unpin hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact Iff.rfl
  | endUse hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact Iff.rfl
  | free hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact Iff.rfl
  | alloc hs => cases hs with
    | ok hst _ => exact footprint_shapeP hst.shapeOK hq l
  | store hs =>
    rename_i a p
    obtain ⟨hp, rfl⟩ := Guarded.ok_iff.1 hs
    have hd := hp.derivedHeld
    cases hy : s.A[a]? with
    | none => rw [hy] at hd; exact hd.elim
    | some y => rw [storeEff_eq hy]

/-! ## `ArenaInv` preserved (§55) -/

/-- A step that only appends authorities and keeps places, stack and death markers keeps
`EntryInv` of every entry still live (§55). -/
theorem entryInv_append {s s' : S3} {E : ArenaEntry} {l : List Authority} (h : EntryInv s E)
    (hA : s'.A = s.A ++ l) (hP : s'.P = s.P) (hF : s'.F = s.F) (hd : s'.dead = s.dead)
    (hlive : s'.Active E.internal) : EntryInv s' E :=
  entryInv_transport h (akeep_append hA) (fun _ => by rw [hP])
    ((S3.Usable.congr hP hF hd).2 h.1.storageUsable) hlive

/-- A live entry registered by `newArena` satisfies `EntryInv`: `ArenaInv` by §76.6 (§55), and
`IssuedShape` since nothing is issued. -/
theorem newEntry_inv {s : S3} {st i : Nat} (h : NewArenaBase s st i) :
    EntryInv s ⟨st, i, footprint s.P st, []⟩ :=
  ⟨h.arenaInv, fun _ he => by cases he⟩

/-- `newArena` without the guard preserves the library invariant (§55, §76). -/
theorem lInv_newArena {L : LState} {st i : Nat} (h : NewArenaBase L.kern st i) (hi : LInv L) :
    LInv (newArenaEff L st i) := by
  intro F hF
  rcases List.mem_append.1 hF with hF | hF
  · exact hi F hF
  · rw [List.mem_singleton.1 hF]
    have hia := h.internalAuth
    cases hy : L.kern.A[i]? with
    | none => rw [hy] at hia; exact hia.elim
    | some y => exact ⟨lt_of_getElem? hy, fun _ => newEntry_inv h⟩

/-- `issue` preserves the library invariant, for the issuing entry and every other entry (§55,
§77). -/
theorem lInv_issue {k : K} {L L' : LState} {i : Nat} {region : List Nat} {dst : Nat}
    (hs : IssueD k i region dst L (.ok L')) (hi : LInv L) : LInv L' := by
  cases hs with
  | @ok E s₁ s₂ hE hst hav hsp hsto =>
  obtain ⟨hp, rfl⟩ := Guarded.ok_iff.1 hsp
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hsto
  rw [← issueKEff_eq]
  have hEm : E ∈ L.arenas := List.mem_of_getElem? hE
  have hright : IssueRight L.kern E region := fun l hl => by
    rw [hp.modifyOn region (List.mem_singleton_self _) l hl]; exact allows_some_modify _
  have hil := (hi E hEm).1
  have hAe : (issueKEff L.kern E region dst).A =
      L.kern.A ++ [⟨.modify, some E.internal, region, .place dst, true⟩] := rfl
  have hold : ∀ F ∈ L.arenas, F.internal < (issueKEff L.kern E region dst).A.length ∧
      (Live (issueKEff L.kern E region dst) F → EntryInv (issueKEff L.kern E region dst) F) := by
    intro F hF
    obtain ⟨hlt, hinv⟩ := hi F hF
    refine ⟨by rw [hAe, List.length_append]; omega, fun hl => ?_⟩
    exact entryInv_append (hinv ((akeep_append hAe).active_back hl hlt)) hAe rfl rfl rfl hl
  intro F hF
  rcases List.mem_or_eq_of_mem_set hF with hF | rfl
  · exact hold F hF
  · obtain ⟨hlt, hinv'⟩ := hold E hEm
    refine ⟨hlt, fun hl => ?_⟩
    obtain ⟨hai, hsh⟩ := hinv' hl
    obtain ⟨hai0, hsh0⟩ := (hi E hEm).2 hst.live
    have hnew : (issueKEff L.kern E region dst).A[L.kern.A.length]? =
        some ⟨.modify, some E.internal, region, .place dst, true⟩ := by simp [hAe]
    have hold' : ∀ e ∈ E.issued, e.2 < L.kern.A.length := fun e he => by
      obtain ⟨y, hy, -⟩ := hsh0 e he; exact lt_of_getElem? hy
    have hact : ∀ e ∈ E.issued, (issueKEff L.kern E region dst).Active e.2 → L.kern.Active e.2 :=
      fun e he ha => (akeep_append hAe).active_back ha (hold' e he)
    -- an active issued block and the new region are disjoint (§43, case 3; §77.5)
    have hdis : ∀ e ∈ E.issued, L.kern.Active e.2 → ∀ l ∈ region, l ∉ e.1 := by
      intro e he ha l hl hle
      obtain ⟨y, hy, -, -, hf, hm⟩ := hsh0 e he
      obtain ⟨y', hy', ya⟩ := ha
      rw [hy] at hy'; cases hy'
      exact effective_ne_modify_of_desc hy ya (hf ▸ hle) (hai0.derived e he ⟨y, hy, ya⟩) hm
        (allows_modify_iff.1 (hright l hl))
    refine ⟨⟨hai.storageUsable, hai.fpEq, hai.active, hai.shape,
      fun l hl => hai.availableIn l (List.mem_filter.1 hl).1, fun e he l hl => ?_,
      fun e he e' he' hne ha ha' l hl hl' => ?_, fun e he ha l hl hla => ?_,
      fun e he ha => ?_⟩, fun e he => ?_⟩
    · rcases List.mem_cons.1 he with rfl | he
      · exact hst.regionIn l hl
      · exact hai.issuedIn e he l hl
    · rcases List.mem_cons.1 he with rfl | he <;> rcases List.mem_cons.1 he' with rfl | he'
      · exact hne rfl
      · exact hdis e' he' (hact e' he' ha') l hl hl'
      · exact hdis e he (hact e he ha) l hl' hl
      · exact hai.disjoint e he e' he' hne ha ha' l hl hl'
    · have hla' := List.mem_filter.1 hla
      rcases List.mem_cons.1 he with rfl | he
      · simp at hla'; exact hla'.2 hl
      · exact hai.notAvailable e he ha l hl hla'.1
    · rcases List.mem_cons.1 he with rfl | he
      · show E.internal ∈ (L.kern.addAuth ⟨.modify, some E.internal, region, .place dst, true⟩).ancs
          L.kern.A.length
        rw [ancs_addAuth_self rfl hil]; exact List.mem_cons_self ..
      · exact hai.derived e he ha
    · rcases List.mem_cons.1 he with rfl | he
      · exact ⟨_, hnew, rfl, hil, rfl, rfl⟩
      · exact hsh e he

/-- `reset` preserves the library invariant, for the reset entry and every other entry (§55,
§78). -/
theorem lInv_reset {L L' : LState} {i : Nat} (hs : ResetD i L (.ok L')) (hi : LInv L) :
    LInv L' := by
  cases hs with
  | @ok E s₁ s₂ hE hd hrl _ =>
  obtain ⟨hdp, rfl⟩ := Guarded.ok_iff.1 hd
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hrl
  rw [← resetKEff_eq]
  have hEm : E ∈ L.arenas := List.mem_of_getElem? hE
  have hAe : (resetKEff L.kern E).A = L.kern.A ++
      [⟨.modify, some E.internal, footprint L.kern.P E.storage, .frame L.kern.top, false⟩] := rfl
  have hold : ∀ F ∈ L.arenas, F.internal < (resetKEff L.kern E).A.length ∧
      (Live (resetKEff L.kern E) F → EntryInv (resetKEff L.kern E) F) := by
    intro F hF
    obtain ⟨hlt, hinv⟩ := hi F hF
    refine ⟨by rw [hAe, List.length_append]; omega, fun hl => ?_⟩
    exact entryInv_append (hinv ((akeep_append hAe).active_back hl hlt)) hAe rfl rfl rfl hl
  intro F hF
  rcases List.mem_or_eq_of_mem_set hF with hF | rfl
  · exact hold F hF
  · obtain ⟨hlt, hinv'⟩ := hold E hEm
    refine ⟨hlt, fun hl => ?_⟩
    obtain ⟨hai, -⟩ := hinv' hl
    exact ⟨⟨hai.storageUsable, hai.fpEq, hai.active, hai.shape, fun l hl => hl,
      fun _ he => (by cases he), fun _ he => (by cases he), fun _ he => (by cases he),
      fun _ he => (by cases he)⟩, fun _ he => (by cases he)⟩

/-- A kernel step of non-administrative code preserves the library invariant (§55), when the
state before satisfies `WF3` and the state after `NoDangling` (§57): the storage of a live arena
stays usable since `internal` covers it. -/
theorem lInv_kernel {k : K} {L : LState} {s' : S3} (hk : KStep k L.kern s') (hw : WF3 L.kern)
    (hnd : NoDangling s') (hi : LInv L) : LInv ⟨s', L.arenas⟩ := by
  have hA := kstep_akeep hk
  intro E hE
  obtain ⟨hlt, hinv⟩ := hi E hE
  refine ⟨hA.lt hlt, fun hlive => ?_⟩
  have hEI := hinv (hA.active_back hlive hlt)
  have hfp := kstep_fp hk hEI.1.storageUsable.lt
  refine entryInv_transport hEI hA hfp ?_ hlive
  obtain ⟨l, hl⟩ := exists_mem_footprint hw (L.kern.P.length - E.storage + 1) E.storage (by omega)
    hEI.1.storageUsable.lt
  obtain ⟨yi, hyi, -⟩ := hEI.1.active
  obtain ⟨y', hy', -, hf', -⟩ := hA _ yi hyi
  obtain ⟨y'', hy'', ya''⟩ := hlive
  rw [hy'] at hy''; cases hy''
  have hli : l ∈ yi.footprint := by
    have := (hEI.1.fpEq l).2 hl; simpa [S3.afp, hyi] using this
  exact usable_of_covered hnd hy' ya'' (hf' ▸ hli) ((hfp l).2 hl)

/-- Every library step, with or without the guard of §56, preserves the library invariant (§55),
when the kernel state before satisfies `WF3` and the one after `NoDangling` (§57). -/
theorem lInv_stepNG {k : K} {L L' : LState} (h : LStepNG k L L') (hw : WF3 L.kern)
    (hnd : NoDangling L'.kern) (hi : LInv L) : LInv L' := by
  cases h with
  | kernel hk => exact lInv_kernel hk hw hnd hi
  | newArena hb => exact lInv_newArena hb hi
  | issue hs => exact lInv_issue hs hi
  | reset hs => exact lInv_reset hs hi

/-- `ArenaInv` (§55) on library runs, with or without the guard of §56: in every library state
reachable under `DDSound` (§80) and `StaticsOK` (§47), every registered `internal` exists and
every live entry satisfies `EntryInv`. The kernel states of such runs are kernel-reachable
(`LReachNG.reachable`), so they satisfy `WF3` and `NoDangling` (`Access.reachable_kinv`, §57),
which `lInv_stepNG` asks of them. -/
theorem lReachNG_inv {k : K} {statics : Statics} (hdd : DDSound k) (hst : StaticsOK statics)
    {L : LState} (h : LReachNG k statics L) : LInv L := by
  induction h with
  | init => intro E hE; cases hE
  | step hL hs ih =>
    exact lInv_stepNG hs (reachable_kinv hdd hst hL.reachable).1
      (reachable_kinv hdd hst (hL.step hs).reachable).2.1.2.2 ih

/-- `ArenaInv` (§55) on library-reachable states: under `DDSound` (§80) and `StaticsOK` (§47),
every live entry of a library-reachable state satisfies `ArenaInv` (`lReachNG_inv`). -/
theorem lReach_inv {k : K} {statics : Statics} (hdd : DDSound k) (hst : StaticsOK statics)
    {L : LState} (h : LReach k statics L) : ∀ E ∈ L.arenas, Live L.kern E → ArenaInv L.kern E :=
  fun E hE hl => ((lReachNG_inv hdd hst h.ng E hE).2 hl).1

/-- `issue_as_kernel` (Part XIV, §77, §58): on every library-reachable state, under `DDSound`
(§80) and `StaticsOK` (§47), the contract of `issue` and the derived operation (`split` then
`store`) have the same outcomes, `ok`, `fail` and `reject`, with the same arrival state, kernel
part included (literal equality, `issueKEff_eq`). The kernel invariant
(`Access.reachable_kinv`) and `ArenaInv` of the entry (`lReach_inv`) hold there. -/
theorem issue_as_kernel {k : K} {statics : Statics} (hdd : DDSound k) (hst : StaticsOK statics)
    {L : LState} (hr : LReach k statics L) {i : Nat} {region : List Nat} {dst : Nat}
    (o : Outcome3 LState) : IssueC i region dst L o ↔ IssueD k i region dst L o :=
  issue_as_kernel_of_inv k (reachable_kinv hdd hst hr.ng.reachable)
    (fun E hE hl => lReach_inv hdd hst hr E (List.mem_of_getElem? hE) hl) o

/-- `reset_as_kernel` (Part XIV, §78, §58): on every library-reachable state, under `DDSound`
(§80) and `StaticsOK` (§47), the contract of `reset` and the derived operation (`derive` then
`release`, then the explicit check of §78.3) have the same outcomes, `ok` and `reject`, with the
same arrival state, kernel part included (literal equality, `resetKEff_eq`). The kernel invariant
(`Access.reachable_kinv`) and `ArenaInv` of the entry (`lReach_inv`) hold there; by I3 the check
of §78.3 never rejects after an accepted `derive` (`resetNoDeps_of_derive`), so the derived
operation is the kernel sequence `derive` then `release`. -/
theorem reset_as_kernel {k : K} {statics : Statics} (hdd : DDSound k) (hst : StaticsOK statics)
    {L : LState} (hr : LReach k statics L) {i : Nat} (o : Outcome3 LState) :
    ResetC i L o ↔ ResetD i L o :=
  reset_as_kernel_of_inv (reachable_kinv hdd hst hr.ng.reachable)
    (fun E hE hl => lReach_inv hdd hst hr E (List.mem_of_getElem? hE) hl) o

/-! ## Safe reuse after `reset` (§78, §86) -/

/-- Library steps keep the authorities (§42, §58, Part XIV). -/
theorem lstep_akeep {k : K} {L L' : LState} (h : LStep k L L') : AKeep L.kern L'.kern := by
  cases h with
  | kernel hk => exact kstep_akeep hk
  | newArena hs => rw [newArena_kernel hs]; exact akeep_of_eq rfl
  | issue hs =>
    cases hs with
    | ok _ _ _ hsp hsto =>
      obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hsp
      obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hsto
      exact akeep_append (by rw [← issueKEff_eq]; rfl)
  | reset hs =>
    cases hs with
    | ok _ hd hrl _ =>
      obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hd
      obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hrl
      exact akeep_append (by rw [← resetKEff_eq]; rfl)

/-- Library runs keep the authorities (§42, §58, Part XIV). -/
theorem LRun.akeep {k : K} {L L' : LState} (h : LRun k L L') : AKeep L.kern L'.kern := by
  induction h with
  | refl => exact akeep_of_eq rfl
  | tail _ hs ih => exact ih.trans (lstep_akeep hs)

/-- `reset` ends every authority derived from `internal` covering a recycled leaf (§78.2, §78
`ok` effect). -/
theorem reset_ends_covering {L L₁ : LState} {i : Nat} {E : ArenaEntry}
    (hE : L.arenas[i]? = some E) (hr : ResetD i L (.ok L₁)) {j : Nat}
    (hj : E.internal ∈ L.kern.ancs j) (hc : ∃ l ∈ L.kern.afp j, l ∈ footprint L.kern.P E.storage) :
    ¬ L₁.kern.Active j := by
  cases hr with
  | @ok E' s₁ s₂ hE' hd hrl _ =>
  rw [hE] at hE'; cases hE'
  obtain ⟨hdp, rfl⟩ := Guarded.ok_iff.1 hd
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hrl
  rw [← resetKEff_eq]
  intro ha
  obtain ⟨l, hl, hls⟩ := hc
  obtain ⟨y, hy, ya⟩ := ha
  have hA : (resetKEff L.kern E).A = L.kern.A ++ [⟨.modify, some E.internal,
      footprint L.kern.P E.storage, .frame L.kern.top, false⟩] := rfl
  rw [hA] at hy
  by_cases hjl : j < L.kern.A.length
  · rw [List.getElem?_append_left hjl] at hy
    have hly : l ∈ y.footprint := by simpa [S3.afp, hy] using hl
    exact no_desc_of_modify hy ya hly hj (allows_modify_iff.1 (hdp.modeOK l hls))
  · rw [List.getElem?_append_right (by omega)] at hy
    cases h0 : j - L.kern.A.length with
    | zero => rw [h0] at hy; simp at hy; rw [← hy] at ya; cases ya
    | succ n => rw [h0] at hy; simp at hy

/-- `arena_reuse_safe` (§78, §86): after a legal `reset`, along every continuation of the library
run, no authority that was derived from `internal` and covered a recycled leaf, previously issued
blocks included, is active again, so none is exercisable: no access to it is possible. -/
theorem arena_reuse_safe {k : K} {L L₁ L₂ : LState} {i : Nat} {E : ArenaEntry}
    (hE : L.arenas[i]? = some E) (hr : ResetD i L (.ok L₁)) (hrun : LRun k L₁ L₂) {j : Nat}
    (hj : E.internal ∈ L.kern.ancs j) (hc : ∃ l ∈ L.kern.afp j, l ∈ footprint L.kern.P E.storage) :
    ¬ L₂.kern.Active j ∧ ∀ m, ¬ L₂.kern.ExercisableAt j m := by
  have h1 := reset_ends_covering hE hr hj hc
  have hnot : ¬ L₂.kern.Active j := fun ha => by
    by_cases hjl : j < L₁.kern.A.length
    · exact h1 (hrun.akeep.active_back ha hjl)
    · obtain ⟨y, hy, -⟩ := ha
      obtain ⟨l, hl, -⟩ := hc
      have hjL : j < L.kern.A.length := by
        cases hlj : L.kern.A[j]? with
        | none => simp [S3.afp, hlj] at hl
        | some _ => exact lt_of_getElem? hlj
      exact hjl ((lstep_akeep (k := k) (.reset hr)).lt hjL)
  refine ⟨hnot, fun m hx => hnot ?_⟩
  cases hx with
  | base hy ha => exact ⟨_, hy, ha⟩
  | held hy ha => exact ⟨_, hy, ha⟩

/-- `arena_reuse_safe` for the issued blocks, per step (§78, §86): after a legal `reset` of a live
entry satisfying `EntryInv`, no block issued before it on a nonempty region is active or
exercisable in any continuation of the library run. On library-reachable states the hypothesis
holds (`arena_reuse_safe_issued`). -/
theorem arena_reuse_safe_issued_of_inv {k : K} {L L₁ L₂ : LState} {i : Nat} {E : ArenaEntry}
    (hE : L.arenas[i]? = some E) (hinv : EntryInv L.kern E) (hr : ResetD i L (.ok L₁))
    (hrun : LRun k L₁ L₂) :
    ∀ e ∈ E.issued, e.1 ≠ [] → ¬ L₂.kern.Active e.2 ∧ ∀ m, ¬ L₂.kern.ExercisableAt e.2 m := by
  intro e he hne
  obtain ⟨y, hy, ho, hlt, hf, -⟩ := hinv.2 e he
  have hj : E.internal ∈ L.kern.ancs e.2 := by
    unfold S3.ancs; rw [chain_cons (by simp [S3.org, hy, ho]) hlt]; exact List.mem_cons_self ..
  obtain ⟨l, hl⟩ := List.exists_mem_of_ne_nil _ hne
  exact arena_reuse_safe hE hr hrun hj
    ⟨l, by simp [S3.afp, hy, hf, hl], hinv.1.issuedIn e he l hl⟩

/-- `arena_reuse_safe` for the issued blocks (§78, §86): after a legal `reset` of an entry of a
library-reachable state, under `DDSound` (§80) and `StaticsOK` (§47), no block issued before it
on a nonempty region is active or exercisable in any continuation of the library run. The entry is
live (§78.1, through §60.1) and satisfies `EntryInv` there (`lReachNG_inv`). -/
theorem arena_reuse_safe_issued {k : K} {statics : Statics} (hdd : DDSound k)
    (hst : StaticsOK statics) {L L₁ L₂ : LState} (hL : LReach k statics L) {i : Nat}
    {E : ArenaEntry} (hE : L.arenas[i]? = some E) (hr : ResetD i L (.ok L₁))
    (hrun : LRun k L₁ L₂) :
    ∀ e ∈ E.issued, e.1 ≠ [] → ¬ L₂.kern.Active e.2 ∧ ∀ m, ¬ L₂.kern.ExercisableAt e.2 m := by
  have hlive : Live L.kern E := by
    cases hr with
    | @ok E' _ _ hE' hd _ _ =>
      rw [hE] at hE'; cases hE'
      exact (Guarded.ok_iff.1 hd).1.active
  exact arena_reuse_safe_issued_of_inv hE
    ((lReachNG_inv hdd hst hL.ng E (List.mem_of_getElem? hE)).2 hlive) hr hrun

/-- `ArenaInv` (§55) after an `ok` of the contract of `issue` (§77) from a library-reachable state,
under `DDSound` (§80) and `StaticsOK` (§47): the arrival state is library-reachable through the
derived operation (`issue_as_kernel`). -/
theorem lInv_issueC {k : K} {statics : Statics} (hdd : DDSound k) (hst : StaticsOK statics)
    {L L' : LState} (hr : LReach k statics L) {i : Nat} {region : List Nat} {dst : Nat}
    (hs : IssueC i region dst L (.ok L')) : LInv L' :=
  lReachNG_inv hdd hst (hr.step (.issue ((issue_as_kernel hdd hst hr _).1 hs))).ng

/-- `ArenaInv` (§55) after an `ok` of the contract of `reset` (§78) from a library-reachable state,
under `DDSound` (§80) and `StaticsOK` (§47): the arrival state is library-reachable through the
derived operation (`reset_as_kernel`). -/
theorem lInv_resetC {k : K} {statics : Statics} (hdd : DDSound k) (hst : StaticsOK statics)
    {L L' : LState} (hr : LReach k statics L) {i : Nat} (hs : ResetC i L (.ok L')) : LInv L' :=
  lReachNG_inv hdd hst (hr.step (.reset ((reset_as_kernel hdd hst hr _).1 hs))).ng

/-- "Through `derive` or `split`" (Part XIV): under `WF3`, `I1` and `I2`, `derive` at `Modify` of
`src` on a region of existing leaves and `split` of `src` on that one region have the same
preconditions (§60, §61) and the same effect (`deriveEff_eq_split`). I2 (§51) gives the active
origin chain that §60.1 asks of `derive` and §61.1 does not list. -/
theorem derive_iff_split (k : K) {s : S3} {src : Nat} {R : List Nat} (hw : WF3 s) (h1 : I1 s)
    (h2 : I2 s) (hR : ∀ l ∈ R, l < s.P.length ∧ isLeaf s.P l) :
    DerivePre s src R .modify ↔ SplitPre k s src [R] := by
  constructor
  · intro hd
    have hm : ∀ p ∈ R, effective s src p = some .modify :=
      fun p hp => allows_modify_iff.1 (hd.modeOK p hp)
    refine ⟨hd.active, hd.exercisable, ?_, ?_, List.pairwise_singleton _ _, ?_⟩
    · intro r hr p hp; rw [List.mem_singleton.1 hr] at hp; exact hm p hp
    · intro r hr p hp; rw [List.mem_singleton.1 hr] at hp
      exact ⟨hd.within p hp, by rw [hm p hp]; simp⟩
    · intro r hr p hp j _ hdx
      rw [List.mem_singleton.1 hr] at hp
      unfold DistribExcl at hdx
      cases hj : s.A[j]? with
      | none => rw [hj] at hdx; exact hdx
      | some y =>
        rw [hj] at hdx; obtain ⟨ya, hanc, hpy, hmy⟩ := hdx
        exact effective_ne_modify_of_desc hj ya hpy hanc hmy (hm p hp)
  · intro hp
    have hm : ∀ p ∈ R, effective s src p = some .modify :=
      fun p hq => hp.modifyOn R (List.mem_singleton_self _) p hq
    have hal : ∀ p ∈ R, Allows (effective s src p) .modify :=
      fun p hq => by rw [hm p hq]; exact allows_some_modify _
    refine ⟨hp.active, hp.exercisable, h2.ancs_active hp.active, hR,
      fun l hl => (hp.within R (List.mem_singleton_self _) l hl).1, hal, fun b _ => ?_,
      top_mem hw.frames.1⟩
    unfold OptP; split
    · rename_i y hy
      rintro ya hb ⟨l, hl, hly⟩
      obtain ⟨x, hx, xa, xl, -⟩ := effective_some (hm l hl)
      have hb1 : b ≠ src := fun h => hb (h ▸ List.mem_cons_self ..)
      have hb2 : b ∉ s.ancs src := fun h => hb (List.mem_cons_of_mem _ h)
      obtain ⟨h₁, h₂⟩ := new_vs_old h1 hx xa xl (hal l hl) hy ya hly hb1 hb2
      exact ⟨h₂, h₁⟩
    · trivial

/-! ## Uniqueness of live administration in the arena registry (§56) -/

/-- Every registered `internal` exists (§46, §76.2). -/
def RegOK (L : LState) : Prop := ∀ E ∈ L.arenas, E.internal < L.kern.A.length

/-- §56 for the arena registry: two live entries at distinct positions have distinct `internal`
identities. -/
def Unique56 (L : LState) : Prop :=
  ∀ (i j : Nat) (E F : ArenaEntry), L.arenas[i]? = some E → L.arenas[j]? = some F → i ≠ j →
    Live L.kern E → Live L.kern F → E.internal ≠ F.internal

/-- Entries after updating entry `i` with the same `internal` (§77, §78 metadata effects). -/
theorem get_set_internal {l : List ArenaEntry} {i j : Nat} {E' F : ArenaEntry}
    (h : (l.set i E')[j]? = some F) : (i = j ∧ ∃ E, l[i]? = some E ∧ F = E') ∨ l[j]? = some F := by
  rw [List.getElem?_set] at h
  split at h
  · subst_vars; split at h
    · rename_i hlt; cases h
      exact .inl ⟨rfl, _, List.getElem?_eq_some_iff.2 ⟨hlt, rfl⟩, rfl⟩
    · cases h
  · exact .inr h

/-- The guard of §56 keeps `internal` identities of live arenas unique along every guarded
library step; the kernel never reactivates an authority, and `issue` and `reset` keep the
`internal` of the entry (§56, Part XIV). -/
theorem unique56_step {k : K} {L L' : LState} (h : LStep k L L') (hr : RegOK L)
    (hu : Unique56 L) : RegOK L' ∧ Unique56 L' := by
  have hA := lstep_akeep h
  have back : ∀ E ∈ L.arenas, Live L'.kern E → Live L.kern E :=
    fun E hE hl => hA.active_back hl (hr E hE)
  cases h with
  | kernel hk =>
    refine ⟨fun E hE => hA.lt (hr E hE), fun i j E F hE hF hij hlE hlF => ?_⟩
    exact hu i j E F hE hF hij (back E (List.mem_of_getElem? hE) hlE)
      (back F (List.mem_of_getElem? hF) hlF)
  | newArena hs =>
    rename_i others st n
    obtain ⟨hp, rfl⟩ := Guarded.ok_iff.1 hs
    have hia := hp.base.internalAuth
    have hn : n < L.kern.A.length := by
      cases hy : L.kern.A[n]? with
      | none => rw [hy] at hia; exact hia.elim
      | some _ => exact lt_of_getElem? hy
    have hg : ∀ E ∈ L.arenas, Live L.kern E → E.internal ≠ n := by
      intro E hE hl he
      refine hp.guard _ (List.mem_cons_self ..) ?_
      rw [← he]
      exact List.mem_map.2 ⟨E, List.mem_filter.2 ⟨hE, by simpa [Live] using hl⟩, rfl⟩
    have hget : ∀ (j : Nat) (F : ArenaEntry), (newArenaEff L st n).arenas[j]? = some F →
        (j < L.arenas.length ∧ L.arenas[j]? = some F) ∨
          (j = L.arenas.length ∧ F = ⟨st, n, footprint L.kern.P st, []⟩) := by
      intro j F hF
      simp only [newArenaEff] at hF
      by_cases hj : j < L.arenas.length
      · exact .inl ⟨hj, by rwa [List.getElem?_append_left hj] at hF⟩
      · rw [List.getElem?_append_right (by omega)] at hF
        cases h0 : j - L.arenas.length with
        | zero => rw [h0] at hF; simp at hF; exact .inr ⟨by omega, hF.symm⟩
        | succ m => rw [h0] at hF; simp at hF
    refine ⟨fun E hE => ?_, fun i j E F hE hF hij hlE hlF => ?_⟩
    · rcases List.mem_append.1 hE with hE | hE
      · exact hr E hE
      · rw [List.mem_singleton.1 hE]; exact hn
    · rcases hget i E hE with ⟨-, hE'⟩ | ⟨hi, rfl⟩ <;> rcases hget j F hF with ⟨-, hF'⟩ | ⟨hj, rfl⟩
      · exact hu i j E F hE' hF' hij hlE hlF
      · exact hg E (List.mem_of_getElem? hE') hlE
      · exact fun he => hg F (List.mem_of_getElem? hF') hlF he.symm
      · exact absurd (hi.trans hj.symm) hij
  | issue hs =>
    rename_i i₀ region dst
    cases hs with
    | @ok E₀ s₁ s₂ hE₀ _ _ hsp hsto =>
    have keep : ∀ (j : Nat) (F : ArenaEntry),
        (L.arenas.set i₀ (issueMeta L.kern E₀ region))[j]? = some F →
        ∃ G : ArenaEntry, L.arenas[j]? = some G ∧ G.internal = F.internal := by
      intro j F hF
      rcases get_set_internal hF with ⟨rfl, G, hG, rfl⟩ | hF
      · rw [hE₀] at hG; cases hG; exact ⟨E₀, hE₀, rfl⟩
      · exact ⟨F, hF, rfl⟩
    refine ⟨fun F hF => ?_, fun i j E F hE hF hij hlE hlF => ?_⟩
    · rcases List.mem_or_eq_of_mem_set hF with hF | rfl
      · exact hA.lt (hr F hF)
      · exact hA.lt (hr E₀ (List.mem_of_getElem? hE₀))
    · obtain ⟨G, hG, hGi⟩ := keep i E hE
      obtain ⟨H, hH, hHi⟩ := keep j F hF
      have hlG : Live L.kern G := back G (List.mem_of_getElem? hG) (by simpa [Live, hGi] using hlE)
      have hlH : Live L.kern H := back H (List.mem_of_getElem? hH) (by simpa [Live, hHi] using hlF)
      rw [← hGi, ← hHi]; exact hu i j G H hG hH hij hlG hlH
  | reset hs =>
    rename_i i₀
    cases hs with
    | @ok E₀ s₁ s₂ hE₀ _ _ _ =>
    have keep : ∀ (j : Nat) (F : ArenaEntry), (L.arenas.set i₀ (resetMeta L.kern E₀))[j]? = some F →
        ∃ G : ArenaEntry, L.arenas[j]? = some G ∧ G.internal = F.internal := by
      intro j F hF
      rcases get_set_internal hF with ⟨rfl, G, hG, rfl⟩ | hF
      · rw [hE₀] at hG; cases hG; exact ⟨E₀, hE₀, rfl⟩
      · exact ⟨F, hF, rfl⟩
    refine ⟨fun F hF => ?_, fun i j E F hE hF hij hlE hlF => ?_⟩
    · rcases List.mem_or_eq_of_mem_set hF with hF | rfl
      · exact hA.lt (hr F hF)
      · exact hA.lt (hr E₀ (List.mem_of_getElem? hE₀))
    · obtain ⟨G, hG, hGi⟩ := keep i E hE
      obtain ⟨H, hH, hHi⟩ := keep j F hF
      have hlG : Live L.kern G := back G (List.mem_of_getElem? hG) (by simpa [Live, hGi] using hlE)
      have hlH : Live L.kern H := back H (List.mem_of_getElem? hH) (by simpa [Live, hHi] using hlF)
      rw [← hGi, ← hHi]; exact hu i j G H hG hH hij hlG hlH

/-- §56 for the arena registry: in every library-reachable state, an authority identity serves as
`internal` for at most one live entry. The other registries are library parameters (`others`),
whose own uniqueness belongs to their contracts. -/
theorem live_internal_unique {k : K} {statics : Statics} {L : LState}
    (h : LReach k statics L) : Unique56 L := by
  have : RegOK L ∧ Unique56 L := by
    induction h with
    | init => exact ⟨fun E hE => (by cases hE), fun i _ E _ hE => (by simp [LState.init] at hE)⟩
    | step _ hs ih => exact unique56_step hs ih.1 ih.2
  exact this.2

/-! ## Witness on a library-reachable state (§86)

A run from `LState.init Examples.st` (§47: static leaves 0 `Init`, 1 and 2 `Uninit`, with root
authorities 0, 1 and 2 held by frame 0) under the test contract `Examples.K0`: leaf 0 is the arena
value, leaf 1 the storage, leaf 2 the destination. Every precondition is decided by `decide`;
`KInv ∧ KAux` of the final state is decided through `KInvB`. -/

namespace Witness

open Examples

/-- Initial library state (§47). -/
def w0 : LState := LState.init st
/-- `derive(1, [1], Modify)`: authority 3 on the storage leaf, held by frame 0 (§60). -/
def w1 : LState := ⟨deriveEff w0.kern 1 [1] .modify, w0.arenas⟩
/-- `store(3, 0)`: authority 3 becomes `internal`, held by the arena value 0 (§65). -/
def w2 : LState := ⟨storeEff w1.kern 3 0, w1.arenas⟩
/-- `newArena(1, 3)` (§76). -/
def w3 : LState := newArenaEff w2 1 3
/-- The entry registered by `newArena(1, 3)` (§46, §76). -/
def wE : ArenaEntry := ⟨1, 3, [1], []⟩

/-- The common prefix is library-reachable (Part XIV, §76). -/
theorem w3_reach : LReach K0 st w3 := by
  have r1 : LReach K0 st w1 := .step .init (.kernel (.derive (.ok (by decide))))
  have r2 : LReach K0 st w2 := .step r1 (.kernel (.store (.ok (by decide))))
  exact .step r2 (.newArena (others := []) (.ok (by decide)))

/-- `issue(0, [1], 2)`: `split(3, [[1]])` then `store(4, 2)` (§77). -/
def r4 : LState :=
  ⟨storeEff (splitEff w3.kern 3 [[1]]) w3.kern.A.length 2,
    w3.arenas.set 0 (issueMeta w3.kern wE [1])⟩
/-- `write(4, [1])`: the storage leaf 1 is written through block 4 (§67). -/
def r5 : LState := ⟨write3Eff r4.kern [1], r4.arenas⟩
/-- `endUse(2)`: the destination ends; block 4, held by it, is released (§69). -/
def r6 : LState := ⟨endUseEff r5.kern 2, r5.arenas⟩
/-- The entry after the first issue (§77 `ok` effect). -/
def rE : ArenaEntry := ⟨1, 3, [], [([1], 4)]⟩
/-- `reset(0)`: `derive(3, [1], Modify)`, `release(5)`, metadata restored (§78). -/
def r7 : LState :=
  ⟨releaseEff (deriveEff r6.kern 3 (footprint r6.kern.P 1) .modify) r6.kern.A.length,
    r6.arenas.set 0 (resetMeta r6.kern rE)⟩
/-- The entry after the reset (§78 `ok` effect). -/
def rE' : ArenaEntry := ⟨1, 3, [1], []⟩
/-- `issue(0, [1], 2)` again: `split(3, [[1]])` then `store(6, 2)` (§77). -/
def r8 : LState :=
  ⟨storeEff (splitEff r7.kern 3 [[1]]) r7.kern.A.length 2,
    r7.arenas.set 0 (issueMeta r7.kern rE' [1])⟩

/-- v0.1 §86, example: a reissued leaf keeps its initialization state and a read of it remains
subject to the ordinary conditions of the memory model. Leaf 1 is `Uninit` when it is first issued,
is written through block 4, keeps `Init` across `endUse` of the destination, the legal `reset`
(§78: "No leaf is made `Init` by `reset`") and the reissue, which modifies the initialization state
of no leaf of the region (§86, `issue_keeps_init`) and initializes only the destination 2 (§77).
In the final library-reachable state, `read` of leaf 1 through the new block 6 is `ok`: the leaf
is `Init` and block 6 is exercisable (§66). -/
theorem reissue_reads_former_value :
    LReach K0 st r8 ∧ KInv r8.kern ∧ KAux r8.kern ∧
    r4.kern.I 1 = .uninit ∧ r5.kern.I 1 = .init ∧ r7.kern.I 1 = .init ∧ r8.kern.I 1 = .init ∧
    ¬ r8.kern.Active 4 ∧
    (r8.kern.A[6]?).map (fun y => (y.origin, y.footprint, y.holder, y.active)) =
      some (some 3, [1], .place 2, true) ∧
    r8.arenas = [⟨1, 3, [], [([1], 6)]⟩] ∧
    Read3Step 6 [1] r8.kern (.ok r8.kern) := by
  have h4 : LReach K0 st r4 := .step w3_reach
    (.issue (i := 0) (region := [1]) (dst := 2)
      (.ok (E := wE) (by decide) (by decide) (by decide) (.ok (by decide)) (.ok (by decide))))
  have h5 : LReach K0 st r5 := .step h4 (.kernel (.write (a := 4) (.ok (by decide))))
  have h6 : LReach K0 st r6 := .step h5 (.kernel (.endUse (.ok (by decide))))
  have h7 : LReach K0 st r7 := .step h6
    (.reset (i := 0) (.ok (E := rE) (by decide) (.ok (by decide)) (.ok (by decide)) (by decide)))
  have h8 : LReach K0 st r8 := .step h7
    (.issue (i := 0) (region := [1]) (dst := 2)
      (.ok (E := rE') (by decide) (by decide) (by decide) (.ok (by decide)) (.ok (by decide))))
  have hk := KInvB.sound (s := r8.kern) (by decide)
  exact ⟨h8, hk.1, hk.2, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, .ok (by decide)⟩

end Witness

end Ern.MemoryModel.Arena
