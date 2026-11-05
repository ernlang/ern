import Ern.MemoryModel.Arena
import Ern.MemoryModel.Access.Preserve.EndFree

/-!
# Handle pool: a library instance of the access discipline (non-normative)

**Non-normative.** This module formalizes the library contract "HandlePool v0.4 annex" (items
D.1–D.4), which `specs/ERN_Memory_Model_Specification_v0.md` does not define (§75, Part XIV
preamble: "The contracts of `HandlePool` and `DataStack` belong to their library abstractions and
are not defined here"). The normative clauses that constrain it are
§36 (`MetaRight` is exercisable `Modify` on the administering value; `writeShared` alone is
insufficient), §37 and §89 (handles are data, not authorities), §38 and §46 (library state outside
`S₃`), §47 (empty initial registry), §56 (the guard over all registries of live administrations)
and §58 (outcomes, statics before `fail`).

The pool registry lives beside the kernel state (`PState`). Its operations are built on the
kernel operations O1–O16 (§60–§75): `newPool` registers only; `allocSlot` writes the handle into
its destination (O10); `resolve` derives a companion from `internal` over the whole storage, then
an entry authority from the companion (O1 twice); `resolveMany` does the same with `split` (O2) in
`Modify` and with one `Observe` derive per handle (O1) in `Observe`; `unresolve` releases (O3).
`freeSlot` applies the effect function of O12 (§69) to the slot content under preconditions that
exempt `internal` and its ancestors (`ContentEndPre`): it is not a kernel `endUse` step.
`contentEnd_preserves` proves that it preserves `KInv ∧ KAux` (§57); `pstep_kernel` states what
every pool step is on the kernel side.
-/

namespace Ern.Lib.HandlePool

open Ern.MemoryModel
open Ern.MemoryModel.Access

/-! ## Library state (HandlePool v0.4 annex, D.1; §38, §46) -/

/-- Slot of a pool entry (HandlePool v0.4 annex, D.1: `{place, gen : Nat, live : Bool}`;
non-normative library contract; §38, §46). -/
structure Slot where
  place : Nat
  gen : Nat
  live : Bool
deriving DecidableEq, Repr

/-- Pool entry `{storage, internal, slots}` with its logical identity (HandlePool v0.4 annex, D.1;
non-normative library contract). The pool value is the place holding `internal` (§46 analogue). -/
structure Pool where
  id : Nat
  storage : Nat
  internal : Nat
  slots : List Slot
deriving DecidableEq, Repr

/-- Handle `(poolId, slot, gen)`: data, not an authority (HandlePool v0.4 annex, D.1; §37, §89;
non-normative library contract). -/
structure Handle where
  id : Nat
  slot : Nat
  gen : Nat
deriving DecidableEq, Repr

/-- Ghost record of a resolution (HandlePool v0.4 annex, D.2; auxiliary information creating no
right, §38): pool identity and `internal`, the companion, the mode, and the entry authorities
tagged with their slot and resolved generation. Read only by `unresolve` and by the invariants. -/
structure Res where
  pool : Nat
  internal : Nat
  comp : Nat
  mode : Mode
  entries : List (Nat × Nat × Nat)
deriving DecidableEq, Repr

/-- Library state (§38, §46; HandlePool v0.4 annex, D.1; non-normative library contract): the
kernel state `S₃` and, separately, the pool registry, the next fresh pool identity and the ghost
resolutions. -/
structure PState where
  kern : S3
  pools : List Pool
  nId : Nat
  res : List Res

/-- Initial library state (§47; HandlePool v0.4 annex, D.1): the initial kernel state, an empty
registry. -/
def PState.init (statics : Statics) : PState := ⟨S3.init statics, [], 0, []⟩

/-- The pool read as an arena entry with nothing available or issued, to reuse `MetaRight` of §36
(HandlePool v0.4 annex, D.3; non-normative library contract). -/
def Pool.entry (pl : Pool) : Arena.ArenaEntry := ⟨pl.storage, pl.internal, [], []⟩

/-- Administrative right on the pool (§36; HandlePool v0.4 annex, D.3, corrected by §36;
non-normative library contract): the pool is live (`internal` active) and `MetaRight` holds,
exercisable `Modify` over the pool value; no `writeShared` branch. -/
def AdminRight (s : S3) (pl : Pool) : Prop := s.Active pl.internal ∧ Arena.MetaRight s pl.entry

/-- Decidability of `AdminRight` (§36). -/
instance (s : S3) (pl : Pool) : Decidable (AdminRight s pl) := by
  unfold AdminRight; infer_instance

/-- Place of slot `i`, `0` if absent (HandlePool v0.4 annex, D.1; non-normative library
contract; §46). -/
def slotPlace (pl : Pool) (i : Nat) : Nat := ((pl.slots[i]?).map (·.place)).getD 0

/-- The pool with slot `i` replaced (HandlePool v0.4 annex, D.3; non-normative library
contract; §46). -/
def setSlot (pl : Pool) (i : Nat) (sl : Slot) : Pool := { pl with slots := pl.slots.set i sl }

/-! ## `newPool` (HandlePool v0.4 annex, D.1; §56) -/

/-- The pool registry as a registry of live administrations (§56; HandlePool v0.4 annex, D.1;
non-normative library contract): the `internal` identities of its live pools. -/
def liveInternals (s : S3) (pools : List Pool) : List Nat :=
  (pools.filter fun pl => decide (s.Active pl.internal)).map (·.internal)

/-- Preconditions of `newPool(storage, internal)` (HandlePool v0.4 annex, D.1; non-normative
library contract; §56, §76). -/
structure NewPoolPre (s : S3) (pools : List Pool) (others : List (List Nat))
    (storage internal : Nat) : Prop where
  /-- D.1: "reprend les autres obligations applicables de `newArena`" (§76.1–§76.3, §76.5). -/
  base : Arena.NewArenaBase s storage internal
  /-- D.1: every leaf of the input storage is `Uninit`. -/
  uninit : ∀ l ∈ footprint s.P storage, s.I l = .uninit
  /-- D.1, §56: `internal` is absent from the pool registry and from every other registry of live
  administrations `others`. -/
  guard : Arena.Guard56 (liveInternals s pools :: others) internal

/-- Decidability of `NewPoolPre` (HandlePool v0.4 annex, D.1; §56, §76). -/
instance (s : S3) (pools : List Pool) (others : List (List Nat)) (storage internal : Nat) :
    Decidable (NewPoolPre s pools others storage internal) :=
  decidable_of_iff (Arena.NewArenaBase s storage internal ∧
    (∀ l ∈ footprint s.P storage, s.I l = .uninit) ∧
    Arena.Guard56 (liveInternals s pools :: others) internal)
    ⟨fun ⟨a, b, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨a, b, c⟩⟩

/-- Effect of `newPool` (HandlePool v0.4 annex, D.1; non-normative library contract): a pool with
the fresh identity `nId`, one free slot of generation zero per child of the storage, the kernel
state unchanged (§46, §76). -/
def newPoolEff (L : PState) (storage internal : Nat) : PState :=
  { L with
    pools := L.pools ++ [⟨L.nId, storage, internal,
      (kids L.kern.P storage).map fun q => ⟨q, 0, false⟩⟩]
    nId := L.nId + 1 }

/-- `newPool` as a relation (HandlePool v0.4 annex, D.1; §58; non-normative library contract):
`ok` or `reject`; `others` are the other registries of live administrations (§56). -/
def NewPoolStep (others : List (List Nat)) (storage internal : Nat) (L : PState) :
    Outcome3 PState → Prop :=
  Guarded (NewPoolPre L.kern L.pools others storage internal) (newPoolEff L storage internal)

/-! ## `allocSlot` (HandlePool v0.4 annex, D.3) -/

/-- Static preconditions of `allocSlot(pool, dst)` (HandlePool v0.4 annex, D.3, corrected by §36;
non-normative library contract). "Apte à recevoir la représentation d'un handle" names no state
component and is not represented. -/
structure AllocSlotStatic (s : S3) (pl : Pool) (dst : Nat) : Prop where
  /-- D.3, §36: live pool and `MetaRight`. -/
  right : AdminRight s pl
  /-- D.3: `dst` is usable. -/
  dstUsable : s.Usable dst
  /-- D.3: `dst` is a leaf (the handle is written into "la seule feuille `dst`"). -/
  dstLeaf : isLeaf s.P dst
  /-- D.3 with §67.1: the write of the handle needs exercisable `Modify` over `dst`. -/
  dstRight : HasRight s .modify dst
  /-- D.3: `dst` is not `Init`. -/
  dstNotInit : s.I dst ≠ .init
  /-- D.3: `dst` holds no active authority. -/
  dstFree : ∀ j ∈ List.range s.A.length,
    OptP (s.A[j]?) (fun z => z.active = true → z.holder ≠ .place dst) True

/-- Decidability of `AllocSlotStatic` (HandlePool v0.4 annex, D.3; §36, §67). -/
instance (s : S3) (pl : Pool) (dst : Nat) : Decidable (AllocSlotStatic s pl dst) :=
  decidable_of_iff (AdminRight s pl ∧ s.Usable dst ∧ isLeaf s.P dst ∧ HasRight s .modify dst ∧
    s.I dst ≠ .init ∧ ∀ j ∈ List.range s.A.length,
      OptP (s.A[j]?) (fun z => z.active = true → z.holder ≠ .place dst) True)
    ⟨fun ⟨a, b, c, d, e, f⟩ => ⟨a, b, c, d, e, f⟩, fun ⟨a, b, c, d, e, f⟩ => ⟨a, b, c, d, e, f⟩⟩

/-- Effect of `allocSlot` on slot `i` of pool `j` (HandlePool v0.4 annex, D.3; non-normative
library contract): the slot becomes live with its generation kept; the handle is written into the
leaf `dst`, which alone becomes `Init` (§67 effect). -/
def allocSlotEff (L : PState) (j : Nat) (pl : Pool) (i : Nat) (sl : Slot) (dst : Nat) : PState :=
  { L with
    kern := write3Eff L.kern [dst]
    pools := L.pools.set j (setSlot pl i { sl with live := true }) }

/-- The handle written by `allocSlot` for slot `i` (HandlePool v0.4 annex, D.3; non-normative
library contract; §37, §89). -/
def slotHandle (pl : Pool) (i : Nat) : Option Handle :=
  (pl.slots[i]?).map fun sl => ⟨pl.id, i, sl.gen⟩

/-- `allocSlot(pool j, dst)` as a relation (HandlePool v0.4 annex, D.3; §58; non-normative library
contract): `reject` without the pool or a static precondition; then `fail` when no slot is free;
`ok` on any free slot. -/
inductive AllocSlotStep (j dst : Nat) (L : PState) : Outcome3 PState → Prop where
  | noPool : L.pools[j]? = none → AllocSlotStep j dst L .reject
  | static {pl : Pool} : L.pools[j]? = some pl → ¬ AllocSlotStatic L.kern pl dst →
      AllocSlotStep j dst L .reject
  | fail {pl : Pool} : L.pools[j]? = some pl → AllocSlotStatic L.kern pl dst →
      (∀ sl ∈ pl.slots, sl.live = true) → AllocSlotStep j dst L .fail
  | ok {pl : Pool} {i : Nat} {sl : Slot} : L.pools[j]? = some pl → AllocSlotStatic L.kern pl dst →
      pl.slots[i]? = some sl → sl.live = false →
      AllocSlotStep j dst L (.ok (allocSlotEff L j pl i sl dst))

/-! ## `resolve`, `resolveMany` (HandlePool v0.4 annex, D.2) -/

/-- The handle designates a live slot of the pool at its generation (HandlePool v0.4 annex, D.2,
D.3; §89; non-normative library contract); a slot index outside the pool designates nothing. -/
def HandleOK (pl : Pool) (h : Handle) : Prop :=
  h.id = pl.id ∧ OptP (pl.slots[h.slot]?) (fun sl => sl.gen = h.gen ∧ sl.live = true) False

/-- Decidability of `HandleOK` (HandlePool v0.4 annex, D.2; §89). -/
instance (pl : Pool) (h : Handle) : Decidable (HandleOK pl h) := by
  unfold HandleOK; infer_instance

/-- Legal exercise of `internal` at mode `m` for the companion (HandlePool v0.4 annex, D.2;
non-normative library contract): the preconditions of the `derive` of the companion from
`internal` over all leaves of the storage (§60). -/
def ResolveRight (s : S3) (pl : Pool) (m : Mode) : Prop :=
  DerivePre s pl.internal (footprint s.P pl.storage) m

/-- Decidability of `ResolveRight` (HandlePool v0.4 annex, D.2; §60). -/
instance (s : S3) (pl : Pool) (m : Mode) : Decidable (ResolveRight s pl m) := by
  unfold ResolveRight; infer_instance

/-- State after the companion (HandlePool v0.4 annex, D.2; §60 effect; non-normative library
contract): authority `|A|`, derived from `internal` at mode `m` over all leaves of the storage. -/
def compS (s : S3) (pl : Pool) (m : Mode) : S3 :=
  deriveEff s pl.internal (footprint s.P pl.storage) m

/-- Observe derivations from `c`, one per region in order (HandlePool v0.4 annex, D.2:
`resolveMany` in `Observe`; §60; non-normative library contract): each accepted in the state left
by the previous ones. -/
def DerivesPre (s : S3) (c : Nat) : List (List Nat) → Prop
  | [] => True
  | r :: rs => DerivePre s c r .observe ∧ DerivesPre (deriveEff s c r .observe) c rs

/-- Decidability of `DerivesPre` (HandlePool v0.4 annex, D.2, §60). -/
instance decDerivesPre (s : S3) (c : Nat) :
    (rs : List (List Nat)) → Decidable (DerivesPre s c rs)
  | [] => isTrue trivial
  | r :: rs =>
    have := decDerivesPre (deriveEff s c r .observe) c rs
    inferInstanceAs (Decidable (_ ∧ _))

/-- Effect of the `Observe` derivations from `c`, in order (HandlePool v0.4 annex, D.2; §60 effect).
-/
def derivesEff (s : S3) (c : Nat) : List (List Nat) → S3
  | [] => s
  | r :: rs => derivesEff (deriveEff s c r .observe) c rs

/-- Entry authorities of a batch from the companion `c` (HandlePool v0.4 annex, D.2; non-normative
library contract): `split` (§61) in `Modify`, successive `Observe` derivations (§60) in
`Observe`. -/
def EntriesPre (k : K) : Mode → S3 → Nat → List (List Nat) → Prop
  | .modify, s, c, rs => SplitPre k s c rs
  | .observe, s, c, rs => DerivesPre s c rs

/-- Decidability of `EntriesPre` (HandlePool v0.4 annex, D.2; §60, §61). -/
instance (k : K) [∀ r r', Decidable (k.DeclaredDisjoint r r')] (m : Mode) (s : S3) (c : Nat)
    (rs : List (List Nat)) : Decidable (EntriesPre k m s c rs) := by
  cases m <;> unfold EntriesPre <;> infer_instance

/-- Effect of the entry authorities of a batch (HandlePool v0.4 annex, D.2; §60, §61 effects). -/
def entriesEff : Mode → S3 → Nat → List (List Nat) → S3
  | .modify, s, c, rs => splitEff s c rs
  | .observe, s, c, rs => derivesEff s c rs

/-- Regions of the entries designated by a batch: the footprint of each slot (HandlePool v0.4
annex, D.2; non-normative library contract; §60). -/
def entryRegions (s : S3) (pl : Pool) (hs : List Handle) : List (List Nat) :=
  hs.map fun h => footprint s.P (slotPlace pl h.slot)

/-- Ghost entries of a batch: the `n`-th entry authority is `c + 1 + n`, for slot and generation of
the `n`-th handle (HandlePool v0.4 annex, D.2; auxiliary, §38). -/
def batchEntries (c : Nat) (hs : List Handle) : List (Nat × Nat × Nat) :=
  mapI (fun i h => (i, h.slot, h.gen)) (c + 1) hs

/-- `resolve(h, m)` on pool `j` as a relation (HandlePool v0.4 annex, D.2; §58; non-normative
library contract): `reject` without the pool or the legal exercise of `internal`; then `fail` for
a handle of another pool, stale, absent or free; then the companion and the entry authority
derived from it, `reject` when the second derivation is not accepted. -/
inductive ResolveStep (j : Nat) (h : Handle) (m : Mode) (L : PState) : Outcome3 PState → Prop where
  | noPool : L.pools[j]? = none → ResolveStep j h m L .reject
  | noRight {pl : Pool} : L.pools[j]? = some pl → ¬ ResolveRight L.kern pl m →
      ResolveStep j h m L .reject
  | fail {pl : Pool} : L.pools[j]? = some pl → ResolveRight L.kern pl m → ¬ HandleOK pl h →
      ResolveStep j h m L .fail
  | noEntry {pl : Pool} {sl : Slot} : L.pools[j]? = some pl → ResolveRight L.kern pl m →
      HandleOK pl h → pl.slots[h.slot]? = some sl →
      ¬ DerivePre (compS L.kern pl m) L.kern.A.length (footprint L.kern.P sl.place) m →
      ResolveStep j h m L .reject
  | ok {pl : Pool} {sl : Slot} : L.pools[j]? = some pl → ResolveRight L.kern pl m →
      HandleOK pl h → pl.slots[h.slot]? = some sl →
      DerivePre (compS L.kern pl m) L.kern.A.length (footprint L.kern.P sl.place) m →
      ResolveStep j h m L (.ok { L with
        kern := deriveEff (compS L.kern pl m) L.kern.A.length (footprint L.kern.P sl.place) m
        res := L.res ++ [⟨pl.id, pl.internal, L.kern.A.length, m,
          [(L.kern.A.length + 1, h.slot, h.gen)]⟩] })

/-- Validity of a batch (HandlePool v0.4 annex, D.2; non-normative library contract): every handle
designates a live slot at its generation; pairwise distinct slots in `Modify` only (§58, §89). -/
def BatchOK (pl : Pool) (hs : List Handle) (m : Mode) : Prop :=
  (∀ h ∈ hs, HandleOK pl h) ∧ (m = .modify → (hs.map (·.slot)).Nodup)

/-- Decidability of `BatchOK` (HandlePool v0.4 annex, D.2; §58, §89). -/
instance (pl : Pool) (hs : List Handle) (m : Mode) : Decidable (BatchOK pl hs m) := by
  unfold BatchOK; infer_instance

/-- `resolveMany(hs, m)` on pool `j` as a relation (HandlePool v0.4 annex, D.2; §58; non-normative
library contract): `reject` without the pool or the legal exercise of `internal`; then an atomic
`fail` for an invalid batch; then one companion and the entry authorities (`EntriesPre`), `reject`
when they are not accepted. -/
inductive ResolveManyStep (k : K) (j : Nat) (hs : List Handle) (m : Mode) (L : PState) :
    Outcome3 PState → Prop where
  | noPool : L.pools[j]? = none → ResolveManyStep k j hs m L .reject
  | noRight {pl : Pool} : L.pools[j]? = some pl → ¬ ResolveRight L.kern pl m →
      ResolveManyStep k j hs m L .reject
  | fail {pl : Pool} : L.pools[j]? = some pl → ResolveRight L.kern pl m → ¬ BatchOK pl hs m →
      ResolveManyStep k j hs m L .fail
  | noEntries {pl : Pool} : L.pools[j]? = some pl → ResolveRight L.kern pl m → BatchOK pl hs m →
      ¬ EntriesPre k m (compS L.kern pl m) L.kern.A.length (entryRegions L.kern pl hs) →
      ResolveManyStep k j hs m L .reject
  | ok {pl : Pool} : L.pools[j]? = some pl → ResolveRight L.kern pl m → BatchOK pl hs m →
      EntriesPre k m (compS L.kern pl m) L.kern.A.length (entryRegions L.kern pl hs) →
      ResolveManyStep k j hs m L (.ok { L with
        kern := entriesEff m (compS L.kern pl m) L.kern.A.length (entryRegions L.kern pl hs)
        res := L.res ++ [⟨pl.id, pl.internal, L.kern.A.length, m,
          batchEntries L.kern.A.length hs⟩] })

/-! ## `unresolve` (HandlePool v0.4 annex, D.2) -/

/-- Releases the authorities of a list in order (§62); `none` as soon as one release is not
accepted (HandlePool v0.4 annex, D.2: "Les règles de `release` … restent applicables"). -/
def releaseAll : S3 → List Nat → Option S3
  | s, [] => some s
  | s, a :: l => if ReleasePre s a then releaseAll (releaseEff s a) l else none

/-- The resolution of companion `c` (HandlePool v0.4 annex, D.2; ghost lookup, §38). -/
def findRes (L : PState) (c : Nat) : Option Res := L.res.find? fun r => r.comp == c

/-- Authorities released by `unresolve` of `r` (HandlePool v0.4 annex, D.2; non-normative library
contract): the entry authorities still active, then the companion (§62). -/
def unresolveList (s : S3) (r : Res) : List Nat :=
  ((r.entries.map (·.1)).filter fun a => decide (s.Active a)) ++ [r.comp]

/-- `unresolve(c)` as a relation (HandlePool v0.4 annex, D.2; §58; non-normative library
contract): the releases of `unresolveList`; `reject` when one is not accepted or `c` is no
companion. -/
inductive UnresolveStep (c : Nat) (L : PState) : Outcome3 PState → Prop where
  | none : findRes L c = none → UnresolveStep c L .reject
  | reject {r : Res} : findRes L c = some r → releaseAll L.kern (unresolveList L.kern r) = none →
      UnresolveStep c L .reject
  | ok {r : Res} {s' : S3} : findRes L c = some r →
      releaseAll L.kern (unresolveList L.kern r) = some s' →
      UnresolveStep c L (.ok { L with kern := s' })

/-! ## `freeSlot` (HandlePool v0.4 annex, D.3) -/

/-- `x` is exempt from the end-of-use checks of a slot of the pool of `internal` `i`: `internal` or
one of its ancestors (HandlePool v0.4 annex, D.3: "hors `internal` et ses ancêtres"; non-normative
library contract; §69). -/
def Exempt (s : S3) (i x : Nat) : Prop := x = i ∨ x ∈ s.ancs i

/-- Decidability of `Exempt` (HandlePool v0.4 annex, D.3; §69). -/
instance (s : S3) (i x : Nat) : Decidable (Exempt s i x) := by unfold Exempt; infer_instance

/-- §69.2 for storage that dies with the content (HandlePool v0.4 annex, D.3: the end-of-use
effects of O12; non-normative library contract): an active derived authority over a leaf of a place
that stops being usable is held within the slot `q` or by a dying holder. -/
def DyingAccessOK (s : S3) (q j : Nat) : Prop :=
  OptP (s.A[j]?) (fun y => y.active = true → y.origin ≠ none →
    (∃ l ∈ y.footprint, isLeaf s.P l ∧ s.Usable l ∧ ¬ (endUseS s q).Usable l) →
      heldIn s.P q y.holder ∨ ¬ HolderLive (endUseS s q) y.holder) True

/-- Decidability of `DyingAccessOK` (§69.2). -/
instance (s : S3) (q j : Nat) : Decidable (DyingAccessOK s q j) := by
  unfold DyingAccessOK OptP; split <;> infer_instance

/-- §69.3 with the exemption of D.3 (HandlePool v0.4 annex, D.3; non-normative library contract):
anchor `x` of a place remaining usable is not held within the slot `q` and keeps a live holder;
unless exempt, it is not a root of `q`. -/
def ContentAnchorOK (s : S3) (q i x : Nat) : Prop :=
  OptP (s.A[x]?) (fun y => ¬ heldIn s.P q y.holder ∧ (¬ Exempt s i x → ¬ IsRootOf s q y) ∧
    HolderLive (endUseS s q) y.holder) True

/-- Decidability of `ContentAnchorOK` (§69.3). -/
instance (s : S3) (q i x : Nat) : Decidable (ContentAnchorOK s q i x) := by
  unfold ContentAnchorOK OptP; split <;> infer_instance

/-- Preconditions of the end of the content of slot place `q` of the pool of `internal` `i`
(HandlePool v0.4 annex, D.3: "la fin logique du contenu doit être admissible"; the preconditions
of O12, §69, excluding `internal` and its ancestors; non-normative library contract). §69.1 is not
a precondition: `freeSlot_modify_right` derives it from `AdminRight`. -/
structure ContentEndPre (k : K) (s : S3) (q i : Nat) : Prop where
  /-- D.3: no active authority covers the entry except `internal` and its ancestors (§69.2 on the
  leaves of the entry, with the exemption). -/
  entry : ∀ j ∈ List.range s.A.length, s.Active j → (∃ l ∈ s.afp j, l ∈ footprint s.P q) →
    Exempt s i j
  /-- §69.2 on the storage that dies with the content. -/
  dying : ∀ j ∈ List.range s.A.length, DyingAccessOK s q j
  /-- D.3, §69.3: no usable dependency is invalidated. -/
  anchors : ∀ q' ∈ List.range s.P.length, (endUseS s q).Usable q' →
    ∀ x ∈ (endUseS s q).D q', ContentAnchorOK s q i x
  /-- D.3, §69.4: no ending leaf is pinned, statically or dynamically. -/
  notPinned : ∀ l ∈ List.range s.P.length, EndingLeaf s q l → s.pin l = false ∧ ¬ k.Pinned l

/-- Decidability of `ContentEndPre` (HandlePool v0.4 annex, D.3; §69). -/
instance (k : K) [DecidablePred k.Pinned] (s : S3) (q i : Nat) :
    Decidable (ContentEndPre k s q i) :=
  decidable_of_iff ((∀ j ∈ List.range s.A.length, s.Active j →
      (∃ l ∈ s.afp j, l ∈ footprint s.P q) → Exempt s i j) ∧
    (∀ j ∈ List.range s.A.length, DyingAccessOK s q j) ∧
    (∀ q' ∈ List.range s.P.length, (endUseS s q).Usable q' →
      ∀ x ∈ (endUseS s q).D q', ContentAnchorOK s q i x) ∧
    (∀ l ∈ List.range s.P.length, EndingLeaf s q l → s.pin l = false ∧ ¬ k.Pinned l))
    ⟨fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩, fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩⟩

/-- Effect of `freeSlot` on slot `i` of pool `j` (HandlePool v0.4 annex, D.3; non-normative library
contract): the effects of O12 on the slot content (`endUseEff`, §69), no deallocation; the slot
becomes free and its generation is incremented. -/
def freeSlotEff (L : PState) (j : Nat) (pl : Pool) (i : Nat) (sl : Slot) : PState :=
  { L with
    kern := endUseEff L.kern sl.place
    pools := L.pools.set j (setSlot pl i ⟨sl.place, sl.gen + 1, false⟩) }

/-- `freeSlot(h)` on pool `j` as a relation (HandlePool v0.4 annex, D.3, corrected by §36; §58;
non-normative library contract): `reject` without the pool, without a live pool or `MetaRight`;
then `fail` for a handle of another pool, stale, absent or free; then `reject` unless the end of
the content is admissible (`ContentEndPre`). -/
inductive FreeSlotStep (k : K) (j : Nat) (h : Handle) (L : PState) : Outcome3 PState → Prop where
  | noPool : L.pools[j]? = none → FreeSlotStep k j h L .reject
  | noRight {pl : Pool} : L.pools[j]? = some pl → ¬ AdminRight L.kern pl →
      FreeSlotStep k j h L .reject
  | fail {pl : Pool} : L.pools[j]? = some pl → AdminRight L.kern pl → ¬ HandleOK pl h →
      FreeSlotStep k j h L .fail
  | noEnd {pl : Pool} {sl : Slot} : L.pools[j]? = some pl → AdminRight L.kern pl →
      HandleOK pl h → pl.slots[h.slot]? = some sl → ¬ ContentEndPre k L.kern sl.place pl.internal →
      FreeSlotStep k j h L .reject
  | ok {pl : Pool} {sl : Slot} : L.pools[j]? = some pl → AdminRight L.kern pl →
      HandleOK pl h → pl.slots[h.slot]? = some sl → ContentEndPre k L.kern sl.place pl.internal →
      FreeSlotStep k j h L (.ok (freeSlotEff L j pl h.slot sl))

/-! ## Library runs (HandlePool v0.4 annex; §38, §46, §57) -/

/-- One `ok` step of a library run (HandlePool v0.4 annex; non-normative library contract): a
kernel step O1–O16 of non-administrative code, the registry unchanged, or an accepted pool
operation (§57, §58). -/
inductive PStep (k : K) : PState → PState → Prop where
  | kernel {L : PState} {s' : S3} : KStep k L.kern s' → PStep k L { L with kern := s' }
  | newPool {L L' : PState} {others : List (List Nat)} {st i : Nat} :
      NewPoolStep others st i L (.ok L') → PStep k L L'
  | allocSlot {L L' : PState} {j dst : Nat} : AllocSlotStep j dst L (.ok L') → PStep k L L'
  | resolve {L L' : PState} {j : Nat} {h : Handle} {m : Mode} :
      ResolveStep j h m L (.ok L') → PStep k L L'
  | resolveMany {L L' : PState} {j : Nat} {hs : List Handle} {m : Mode} :
      ResolveManyStep k j hs m L (.ok L') → PStep k L L'
  | unresolve {L L' : PState} {c : Nat} : UnresolveStep c L (.ok L') → PStep k L L'
  | freeSlot {L L' : PState} {j : Nat} {h : Handle} : FreeSlotStep k j h L (.ok L') →
      PStep k L L'

/-- Library states reachable from the initial library state (§47) by library steps (HandlePool v0.4
annex; non-normative library contract). -/
inductive PReach (k : K) (statics : Statics) : PState → Prop where
  | init : PReach k statics (PState.init statics)
  | step {L L' : PState} : PReach k statics L → PStep k L L' → PReach k statics L'

/-- Library runs in which every step starts from a kernel state satisfying `KInv` (§57; HandlePool
v0.4 annex). Under the guarantee of §57 every library-reachable state is such a state
(`PReach.toI`); the pool theorems are stated on these runs, so that they do not depend on that
guarantee. -/
inductive PReachI (k : K) (statics : Statics) : PState → Prop where
  | init : PReachI k statics (PState.init statics)
  | step {L L' : PState} : PReachI k statics L → KInv L.kern → PStep k L L' →
      PReachI k statics L'

/-- Kernel side of library runs (§57, §69 effect; HandlePool v0.4 annex, D.3): a kernel step
O1–O16, or the end of the content of a slot place `q` under `ContentEndPre` for some `internal`
`i`. -/
inductive XStep (k : K) : S3 → S3 → Prop where
  | kernel {s s' : S3} : KStep k s s' → XStep k s s'
  | contentEnd {s : S3} {q i : Nat} : ContentEndPre k s q i → XStep k s (endUseEff s q)

/-- States reachable from `S3.init statics` by `XStep` (§57; HandlePool v0.4 annex, D.3). -/
inductive XReach (k : K) (statics : Statics) : S3 → Prop where
  | init : XReach k statics (S3.init statics)
  | step {s s' : S3} : XReach k statics s → XStep k s s' → XReach k statics s'

/-- Finite sequences of kernel steps O1–O16 (§57, §58). -/
inductive KSeq (k : K) : S3 → S3 → Prop where
  | refl (s : S3) : KSeq k s s
  | tail {s s₁ s₂ : S3} : KSeq k s s₁ → KStep k s₁ s₂ → KSeq k s s₂

/-! ## The end of a slot content preserves the kernel invariant (§57, §69; D.3) -/

/-- Under `ContentEndPre` (HandlePool v0.4 annex, D.3, §69.3 with the exemption) and `I3` (§52),
every anchor of a place usable after `endUseS` stays active after the end of the content. -/
theorem contentEnd_anchors {k : K} {s : S3} {q i : Nat} (h3 : I3 s)
    (hpre : ContentEndPre k s q i) :
    ∀ q', (endUseS s q).Usable q' → ∀ x ∈ (endUseS s q).D q', (endUseEff s q).Active x := by
  intro q' hq x hx
  have hq₀ := EndFree.endUseS_usable hq
  have hx₀ : x ∈ s.D q' := by
    simp only [endUseS] at hx; split at hx
    · simp at hx
    · exact hx
  obtain ⟨y, hy, ya⟩ := h3 q' hq₀ x hx₀
  have hc := hpre.anchors q' (List.mem_range.2 hq₀.lt) hq x hx
  unfold ContentAnchorOK OptP at hc; rw [hy] at hc
  obtain ⟨hnh, -, hl⟩ := hc
  exact ⟨y, by rw [endUseEff, EndFree.cleanup_get, EndFree.endUseS_get, hy]; simp [hnh, hl], ya⟩

/-- The end of the content preserves `NoDangling` (§54, §69; HandlePool v0.4 annex, D.3), under
`WF3` (§49) and `RootHeldConv` (§40): an active authority on a leaf of a place that stops being
usable is derived, and blocked by §69.2 on dying storage, or a root, held by the owner of the root
place of the leaf, which stays usable. -/
theorem contentEnd_noDangling {k : K} {s : S3} {q i : Nat} (hw : WF3 s) (hnd : NoDangling s)
    (ha : RootHeldConv s) (hpre : ContentEndPre k s q i) (hw' : WF3 (endUseEff s q)) :
    NoDangling (endUseEff s q) := by
  have hU := EndFree.cleanup_usable (endUseS s q)
  intro j z hz za q' hq l hl hlz
  obtain ⟨hz₀, hnh, hlive⟩ := EndFree.endUse_active hz za
  by_cases hq₀ : ¬ s.Usable q'
  · exact hnd j z hz₀ za q' hq₀ l hl hlz
  replace hq₀ := Decidable.of_not_not hq₀
  obtain ⟨-, hleaf, hlq⟩ := mem_footprint.1 hl
  have hl₀ : s.Usable l := usable_of_partOf hw (l + 1) l q' (Nat.lt_succ_self l) hlq hq₀
  have hl₁ : ¬ (endUseS s q).Usable l := fun hu => hq (usable_of_part hw' hlq ((hU l).2 hu))
  cases hzo : z.origin with
  | some o =>
    have hacc := hpre.dying j (List.mem_range.2 (lt_of_getElem? hz₀))
    unfold DyingAccessOK OptP at hacc; rw [hz₀] at hacc
    rcases hacc za (by rw [hzo]; simp) ⟨l, hlz, hleaf, hl₀, hl₁⟩ with e | e
    · exact hnh e
    · exact e hlive
  | none =>
    obtain ⟨-, -, r, -, -, -, hr, hlr, -⟩ := hw.rootChain j z l hz₀ hlz hleaf
    obtain ⟨pr, hpr, hh⟩ := ha j z l r hz₀ hzo hlz hr hlr
    have hnown : ¬ OwnedIn s.P q r := fun hown => by
      cases hown with
      | @direct _ o _ hpl ho hpart =>
        have e : pr.owner = .place o := by rw [hpr] at hpl; cases hpl; exact ho
        rw [hh, e] at hnh; exact hnh hpart
      | @step _ o _ hpl ho hown' =>
        have e : pr.owner = .place o := by rw [hpr] at hpl; cases hpl; exact ho
        rw [hh, e] at hlive
        have := EndFree.dead_false hlive
        simp only [endUseS, Bool.or_eq_false_iff, decide_eq_false_iff_not] at this
        exact this.2 hown'
    have hd : (endUseS s q).dead r = false := by
      simp only [endUseS, ← hw.deadOf hlr, EndFree.dead_false hl₀, Bool.false_or,
        decide_eq_false_iff_not]
      exact hnown
    have hr₁ : (endUseS s q).Usable r := EndFree.usable_of_owner hpr hd (hh ▸ hlive)
    exact hl₁ ((hU l).1 (usable_of_partOf hw' (l + 1) l r (Nat.lt_succ_self l) hlr ((hU r).2 hr₁)))

/-- The end of the content of a slot place `q` under `ContentEndPre` preserves the kernel invariant
`KInv` (§57) and `KAux` (§40, §49.7) (HandlePool v0.4 annex, D.3: "la préservation des invariants
sous ce droit constitue une obligation explicite"; §69 effect). -/
theorem contentEnd_preserves {k : K} {s : S3} {q i : Nat} (hk : KInv s) (ha : KAux s)
    (hpre : ContentEndPre k s q i) : KInv (endUseEff s q) ∧ KAux (endUseEff s q) := by
  have hw := hk.1
  refine EndFree.releases_preserve hk ha (EndFree.endUseS_releases s q) rfl rfl rfl
    (fun q h => by simp only [endUseS, Bool.or_eq_false_iff] at h; exact h.1)
    (fun q' pl r hq hp => ?_) (fun q' _ x hx => ?_) (contentEnd_anchors hk.2.1.1.2.2.1 hpre)
    (fun r n z pr _ hur hz _ _ hpr hzh _ => ?_)
    (contentEnd_noDangling hw hk.2.1.2.2 ha hpre)
  · obtain ⟨-, -, -, -, hd⟩ := hw.places q' pl r hq hp
    simp only [endUseS, hd, decide_eq_decide.2 (EndFree.ownedIn_parent hw hq hp)]
  · simp only [endUseS] at hx; split at hx
    · simp at hx
    · exact hx
  · have hnh : ¬ heldIn s.P q z.holder := fun hh => by
      have hd := EndFree.dead_false hur
      simp only [endUseS, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hd
      rw [hzh] at hh
      cases ho : pr.owner with
      | frame f => rw [ho] at hh; exact hh
      | place o => rw [ho] at hh; exact hd.2 (.direct hpr ho hh)
    rw [EndFree.endUseS_get, hz]; simp [hnh]

/-! ## Kernel side of the pool operations (§57, §58; HandlePool v0.4 annex) -/

/-- Sequences of kernel steps compose (§57). -/
theorem KSeq.trans {k : K} {s₁ s₂ s₃ : S3} (h₁ : KSeq k s₁ s₂) (h₂ : KSeq k s₂ s₃) :
    KSeq k s₁ s₃ := by
  induction h₂ with
  | refl => exact h₁
  | tail _ hs ih => exact .tail ih hs

/-- One kernel step is a sequence (§57). -/
theorem KSeq.single {k : K} {s s' : S3} (h : KStep k s s') : KSeq k s s' := .tail (.refl s) h

/-- `releaseAll` is a sequence of `release` steps (§62; HandlePool v0.4 annex, D.2). -/
theorem releaseAll_kseq {k : K} : ∀ {s s' : S3} {l : List Nat}, releaseAll s l = some s' →
    KSeq k s s'
  | s, s', [], h => by simp only [releaseAll, Option.some.injEq] at h; subst h; exact .refl s
  | s, s', a :: l, h => by
    simp only [releaseAll] at h
    split at h
    · rename_i hpre
      exact (KSeq.single (.release (Guarded.ok hpre))).trans (releaseAll_kseq h)
    · cases h

/-- The `Observe` derivations of `resolveMany` are a sequence of `derive` steps (§60; HandlePool
v0.4 annex, D.2). -/
theorem derives_kseq {k : K} {c : Nat} : ∀ {s : S3} {rs : List (List Nat)}, DerivesPre s c rs →
    KSeq k s (derivesEff s c rs)
  | s, [], _ => .refl s
  | _, _ :: _, ⟨h₁, h₂⟩ => (KSeq.single (.derive (Guarded.ok h₁))).trans (derives_kseq h₂)

/-- The entry authorities of `resolveMany` are a `split` (§61) or a sequence of `derive` steps
(§60) (HandlePool v0.4 annex, D.2). -/
theorem entries_kseq {k : K} {m : Mode} {s : S3} {c : Nat} {rs : List (List Nat)}
    (h : EntriesPre k m s c rs) : KSeq k s (entriesEff m s c rs) := by
  cases m with
  | modify => exact KSeq.single (.split (Guarded.ok h))
  | observe => exact derives_kseq h

/-- Under `KInv` (§57), exercisable `Modify` over a usable leaf gives the preconditions of an
ordinary write of that leaf (§67; HandlePool v0.4 annex, D.3: the write of the handle). -/
theorem write_of_right {s : S3} (hk : KInv s) {dst : Nat} (hu : s.Usable dst)
    (hl : isLeaf s.P dst) (hr : HasRight s .modify dst) : ∃ a, Write3Pre s a [dst] := by
  obtain ⟨a, -, hex, hall⟩ := hr
  have hmem : dst ∈ footprint s.P dst := mem_footprint.2 ⟨hu.lt, hl, hu.lt, .inl rfl⟩
  have he : effective s a dst = some .modify := Arena.allows_modify_iff.1 (hall dst hmem)
  refine ⟨a, ⟨fun l hl' => ?_, hex, fun l hl' => ?_, fun l hl' b _ hb => ?_, fun l hl' => ?_⟩⟩
  · rw [List.mem_singleton.1 hl']; exact ⟨dst, List.mem_range.2 hu.lt, hu, hmem⟩
  · rw [List.mem_singleton.1 hl']; exact he
  · rw [List.mem_singleton.1 hl']; exact effective_exclusive hk.2.1.1.1 (Ne.symm hb) he
  · rw [List.mem_singleton.1 hl']
    exact fun q _ hq x hx => hk.2.1.1.2.2.1 q (usable_of_part hk.1 hq hu) x hx

/-- What a pool step is on the kernel side (HandlePool v0.4 annex; §57, §69): under `KInv`, every
step but `freeSlot` is a finite sequence of kernel steps O1–O16 (`newPool` none, `allocSlot` one
`write`, `resolve` two `derive`, `resolveMany` one `derive` then one `split` or one `derive` per
handle, `unresolve` `release` steps); `freeSlot` is the effect of O12 on the slot content under
`ContentEndPre`. -/
theorem pstep_kernel {k : K} {L L' : PState} (hk : KInv L.kern) (h : PStep k L L') :
    KSeq k L.kern L'.kern ∨
      ∃ q i, ContentEndPre k L.kern q i ∧ L'.kern = endUseEff L.kern q := by
  cases h with
  | kernel hs => exact .inl (KSeq.single hs)
  | newPool hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact .inl (.refl _)
  | allocSlot hs =>
    cases hs with
    | ok _ hst _ _ =>
      obtain ⟨a, hw⟩ := write_of_right hk hst.dstUsable hst.dstLeaf hst.dstRight
      exact .inl (KSeq.single (.write (a := a) (Guarded.ok hw)))
  | resolve hs =>
    cases hs with
    | ok _ hR _ _ hE =>
      exact .inl ((KSeq.single (.derive (Guarded.ok hR))).tail (.derive (Guarded.ok hE)))
  | resolveMany hs =>
    cases hs with
    | ok _ hR _ hE => exact .inl ((KSeq.single (.derive (Guarded.ok hR))).trans (entries_kseq hE))
  | unresolve hs =>
    cases hs with
    | ok _ hr => exact .inl (releaseAll_kseq hr)
  | freeSlot hs =>
    cases hs with
    | ok _ _ _ _ hE => exact .inr ⟨_, _, hE, rfl⟩

/-- `XReach` is closed under sequences of kernel steps (§57). -/
theorem XReach.kseq {k : K} {statics : Statics} {s s' : S3} (hr : XReach k statics s)
    (h : KSeq k s s') : XReach k statics s' := by
  induction h with
  | refl => exact hr
  | tail _ hs ih => exact .step ih (.kernel hs)

/-- The guarantee of §57 on the kernel side of library runs (HandlePool v0.4 annex): `KInv` on
every state reached by kernel steps O1–O16 and ends of slot contents. It is not a clause of the
contract and is not proved here: `xreach_inv` reduces it to the preservation of `KInv ∧ KAux` by
every kernel step, which the transfer of §63 breaks (`transfer_breaks_kinv`). -/
def KernelGuarantee (k : K) (statics : Statics) : Prop := ∀ s, XReach k statics s → KInv s

/-- A library step from a kernel state in `XReach` lands in `XReach`, under `KInv` (§57;
HandlePool v0.4 annex). -/
theorem xreach_pstep {k : K} {statics : Statics} {L L' : PState}
    (hr : XReach k statics L.kern) (hk : KInv L.kern) (hs : PStep k L L') :
    XReach k statics L'.kern := by
  rcases pstep_kernel hk hs with h | ⟨q, i, hpre, he⟩
  · exact hr.kseq h
  · rw [he]; exact .step hr (.contentEnd hpre)

/-- The kernel state of every library-reachable state is reached from `S3.init statics` by kernel
steps O1–O16 and ends of slot contents (§57; HandlePool v0.4 annex), given `KInv` on such
states. -/
theorem pReach_xreach {k : K} {statics : Statics} (hX : KernelGuarantee k statics)
    {L : PState} (h : PReach k statics L) : XReach k statics L.kern := by
  induction h with
  | init => exact .init
  | step _ hs ih => exact xreach_pstep ih (hX _ ih) hs

/-- `KInv ∧ KAux` (§57) holds on every state reached by kernel steps and ends of slot contents,
when it holds initially and every kernel step O1–O16 preserves it (`contentEnd_preserves` covers the
ends of slot contents; HandlePool v0.4 annex, D.3). -/
theorem xreach_inv {k : K} {statics : Statics}
    (h0 : KInv (S3.init statics) ∧ KAux (S3.init statics))
    (hK : ∀ s s', KInv s → KAux s → KStep k s s' → KInv s' ∧ KAux s') {s : S3}
    (h : XReach k statics s) : KInv s ∧ KAux s := by
  induction h with
  | init => exact h0
  | step _ hs ih =>
    cases hs with
    | kernel hs => exact hK _ _ ih.1 ih.2 hs
    | contentEnd hpre => exact contentEnd_preserves ih.1 ih.2 hpre

/-! ## Helper lemmas (lists, chains, effects) -/

/-- An optional value satisfying a predicate with default `False` exists (§38). -/
theorem optP_false_iff {α : Type} {o : Option α} {P : α → Prop} :
    OptP o P False ↔ ∃ y, o = some y ∧ P y := by
  cases o with
  | none => simp [OptP]
  | some y => simp [OptP]

/-- The replaced element belongs to the list (HandlePool v0.4 annex, D.3: pool updates; §46). -/
theorem mem_set_self' {α : Type} : ∀ {l : List α} {i : Nat} {a x : α}, l[i]? = some a →
    x ∈ l.set i x
  | [], _, _, _, h => by simp at h
  | _ :: _, 0, _, _, _ => by simp
  | _ :: l, i + 1, a, x, h => by
    simp only [List.getElem?_cons_succ] at h
    simp only [List.set_cons_succ, List.mem_cons]; exact .inr (mem_set_self' h)

/-- An element other than the replaced one stays in the list (HandlePool v0.4 annex, D.3; §46). -/
theorem mem_set_of_ne {α : Type} : ∀ {l : List α} {i : Nat} {a b x : α}, l[i]? = some a →
    b ∈ l → b ≠ a → b ∈ l.set i x
  | [], _, _, _, _, h, _, _ => by simp at h
  | c :: l, 0, a, b, x, h, hb, hne => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h
    rcases List.mem_cons.1 hb with rfl | hb
    · exact absurd rfl hne
    · simp only [List.set_cons_zero, List.mem_cons]; exact .inr hb
  | c :: l, i + 1, a, b, x, h, hb, hne => by
    simp only [List.getElem?_cons_succ] at h
    simp only [List.set_cons_succ, List.mem_cons]
    rcases List.mem_cons.1 hb with rfl | hb
    · exact .inl rfl
    · exact .inr (mem_set_of_ne h hb hne)

/-- An element of an updated list is an old element or the new one (HandlePool v0.4 annex,
D.3; §46). -/
theorem mem_set_cases {α : Type} : ∀ {l : List α} {i : Nat} {x b : α}, b ∈ l.set i x →
    b ∈ l ∨ b = x
  | [], _, _, _, h => by simp at h
  | c :: l, 0, x, b, h => by
    simp only [List.set_cons_zero, List.mem_cons] at h
    rcases h with rfl | h
    · exact .inr rfl
    · exact .inl (List.mem_cons_of_mem _ h)
  | c :: l, i + 1, x, b, h => by
    simp only [List.set_cons_succ, List.mem_cons] at h
    rcases h with rfl | h
    · exact .inl (List.mem_cons_self ..)
    · rcases mem_set_cases h with h | h
      · exact .inl (List.mem_cons_of_mem _ h)
      · exact .inr h

/-- Reading the replaced index (HandlePool v0.4 annex, D.3; §46). -/
theorem getElem?_set_eq' {α : Type} : ∀ {l : List α} {i : Nat} {a x : α}, l[i]? = some a →
    (l.set i x)[i]? = some x
  | [], _, _, _, h => by simp at h
  | _ :: _, 0, _, _, _ => by simp
  | _ :: l, i + 1, a, x, h => by
    simp only [List.getElem?_cons_succ] at h
    simp only [List.set_cons_succ, List.getElem?_cons_succ]; exact getElem?_set_eq' h

/-- Reading another index (HandlePool v0.4 annex, D.3; §46). -/
theorem getElem?_set_ne' {α : Type} : ∀ {l : List α} {i n : Nat} {x : α}, n ≠ i →
    (l.set i x)[n]? = l[n]?
  | [], _, _, _, _ => by simp
  | _ :: _, 0, 0, _, h => absurd rfl h
  | _ :: _, 0, _ + 1, _, _ => by simp
  | _ :: _, _ + 1, 0, _, _ => by simp
  | _ :: l, i + 1, n + 1, x, h => by
    simp only [List.set_cons_succ, List.getElem?_cons_succ]
    exact getElem?_set_ne' (l := l) (fun e => h (by rw [e]))

/-- Replacing an element by one with the same image keeps the image of the list (HandlePool v0.4
annex, D.3; §46). -/
theorem map_set_same {α β : Type} (f : α → β) : ∀ {l : List α} {i : Nat} {a x : α},
    l[i]? = some a → f x = f a → (l.set i x).map f = l.map f
  | [], _, _, _, h, _ => by simp at h
  | b :: l, 0, a, x, h, hf => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h
    simp [hf]
  | b :: l, i + 1, a, x, h, hf => by
    simp only [List.getElem?_cons_succ] at h
    simp only [List.set_cons_succ, List.map_cons, map_set_same f h hf]

/-- Two parts containing a common leaf are related by the parent chain (§40). -/
theorem chain_total {org : Nat → Option Nat} : ∀ n i, i < n → ∀ a b, a ∈ i :: chain org i →
    b ∈ i :: chain org i → a = b ∨ a ∈ chain org b ∨ b ∈ chain org a
  | 0, _, h, _, _, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, i, hi, a, b, ha, hb => by
    cases ho : org i with
    | none =>
      rw [chain_none ho] at ha hb
      rw [List.mem_singleton.1 ha, List.mem_singleton.1 hb]; exact .inl rfl
    | some o =>
      by_cases hlt : o < i
      · have hc := chain_cons ho hlt
        rcases List.mem_cons.1 ha with rfl | ha <;> rcases List.mem_cons.1 hb with rfl | hb
        · exact .inl rfl
        · exact .inr (.inr hb)
        · exact .inr (.inl ha)
        · rw [hc] at ha hb; exact chain_total n o (by omega) a b ha hb
      · have hc : chain org i = [] := by
          cases i with
          | zero => rfl
          | succ k => simp [chain, chainF, ho, hlt]
        rw [hc] at ha hb
        rw [List.mem_singleton.1 ha, List.mem_singleton.1 hb]; exact .inl rfl

/-- Two distinct children of a place have disjoint footprints under `WF3` (§40, §49.2; HandlePool
v0.4 annex, D.1: slots are pairwise disjoint). -/
theorem kids_disjoint {s : S3} (hw : WF3 s) {st q₁ q₂ : Nat} (h₁ : q₁ ∈ kids s.P st)
    (h₂ : q₂ ∈ kids s.P st) (hne : q₁ ≠ q₂) : ∀ l ∈ footprint s.P q₁, l ∉ footprint s.P q₂ := by
  intro l hl₁ hl₂
  obtain ⟨-, hp₁⟩ := mem_kids.1 h₁
  obtain ⟨-, hp₂⟩ := mem_kids.1 h₂
  have hpar : ∀ i o, parentOf s.P i = some o → o < i := fun i o h => (hw.parent_lt h).1
  have m₁ : q₁ ∈ l :: chain (parentOf s.P) l := by
    rcases (mem_footprint.1 hl₁).2.2.2 with h | h
    · rw [h]; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ h
  have m₂ : q₂ ∈ l :: chain (parentOf s.P) l := by
    rcases (mem_footprint.1 hl₂).2.2.2 with h | h
    · rw [h]; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ h
  have below : ∀ a b, parentOf s.P a = some st → parentOf s.P b = some st →
      b ∈ chain (parentOf s.P) a → False := fun a b ha hb hc => by
    rw [chain_cons ha (hpar a st ha)] at hc
    have hbst := (hw.parent_lt hb).1
    rcases List.mem_cons.1 hc with rfl | hc
    · exact Nat.lt_irrefl _ hbst
    · exact Nat.lt_asymm (chain_lt hc) hbst
  rcases chain_total (l + 1) l (Nat.lt_succ_self l) q₁ q₂ m₁ m₂ with h | h | h
  · exact hne h
  · exact below q₂ q₁ hp₂ hp₁ h
  · exact below q₁ q₂ hp₁ hp₂ h

/-- `List.range` is strictly increasing (HandlePool v0.4 annex, D.1: slot indices; §40). -/
theorem range_pairwise_lt : ∀ n, (List.range n).Pairwise (· < ·)
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.pairwise_append]
    exact ⟨range_pairwise_lt n, by simp, fun a ha b hb => by
      rw [List.mem_singleton.1 hb]; exact List.mem_range.1 ha⟩

/-- In a strictly increasing list, an element has one index (HandlePool v0.4 annex, D.1; §40). -/
theorem index_inj_of_lt : ∀ {l : List Nat} {i j a : Nat}, l.Pairwise (· < ·) → l[i]? = some a →
    l[j]? = some a → i = j
  | [], _, _, _, _, h, _ => by simp at h
  | _ :: _, 0, 0, _, _, _, _ => rfl
  | _ :: _, 0, j + 1, _, hp, h₁, h₂ => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h₁; subst h₁
    simp only [List.getElem?_cons_succ] at h₂
    exact absurd ((List.pairwise_cons.1 hp).1 _ (List.mem_of_getElem? h₂)) (Nat.lt_irrefl _)
  | _ :: _, i + 1, 0, _, hp, h₁, h₂ => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h₂; subst h₂
    simp only [List.getElem?_cons_succ] at h₁
    exact absurd ((List.pairwise_cons.1 hp).1 _ (List.mem_of_getElem? h₁)) (Nat.lt_irrefl _)
  | _ :: _, i + 1, j + 1, _, hp, h₁, h₂ => by
    simp only [List.getElem?_cons_succ] at h₁ h₂
    exact congrArg (· + 1) (index_inj_of_lt (List.pairwise_cons.1 hp).2 h₁ h₂)

/-- The `Observe` derivations append one authority per region, of origin `c`, held by the current
frame (§60 effect; HandlePool v0.4 annex, D.2). -/
theorem derivesEff_eq (c : Nat) : ∀ (s : S3) (rs : List (List Nat)),
    derivesEff s c rs =
      { s with A := s.A ++ rs.map fun r => ⟨.observe, some c, r, .frame s.top, true⟩ }
  | s, [] => by cases s; simp [derivesEff]
  | s, r :: rs => by
    rw [derivesEff, derivesEff_eq c _ rs]
    simp [deriveEff, S3.addAuth, S3.top]

/-- The entry authorities of a batch: one per region, of origin `c` and mode `m`, held by the
current frame (§60, §61 effects; HandlePool v0.4 annex, D.2). -/
theorem entriesEff_eq (m : Mode) (s : S3) (c : Nat) (rs : List (List Nat)) :
    entriesEff m s c rs =
      { s with A := s.A ++ rs.map fun r => ⟨m, some c, r, .frame s.top, true⟩ } := by
  cases m with
  | modify => rfl
  | observe => exact derivesEff_eq c s rs

/-- Ghost entries of a batch (HandlePool v0.4 annex, D.2): the `n`-th is the authority
`c + 1 + n` with the slot and generation of the `n`-th handle (§38). -/
theorem mem_batchEntries : ∀ {c : Nat} {hs : List Handle} {e : Nat × Nat × Nat},
    e ∈ batchEntries c hs → ∃ n h, hs[n]? = some h ∧ e = (c + 1 + n, h.slot, h.gen)
  | _, [], _, he => by simp [batchEntries, mapI] at he
  | c, h :: hs, e, he => by
    simp only [batchEntries, mapI, List.mem_cons] at he
    rcases he with rfl | he
    · exact ⟨0, h, rfl, rfl⟩
    · obtain ⟨n, h', hh', rfl⟩ := mem_batchEntries (c := c + 1) he
      exact ⟨n + 1, h', by simpa using hh', by rw [show c + 1 + (n + 1) = c + 1 + 1 + n by omega]⟩

/-! ## Ghost well-formedness of the pool layer (HandlePool v0.4 annex, D.1, D.2; auxiliary) -/

/-- What `allocSlot` and `freeSlot` keep of a pool: identity, storage, `internal` and slot places
(HandlePool v0.4 annex, D.1, D.3; auxiliary information, §38). -/
structure PoolShape where
  id : Nat
  storage : Nat
  internal : Nat
  places : List Nat

/-- The shape of a pool (HandlePool v0.4 annex, D.1; auxiliary; §38). -/
def Pool.shape (pl : Pool) : PoolShape := ⟨pl.id, pl.storage, pl.internal, pl.slots.map (·.place)⟩

/-- Updating a slot with the same place keeps the shape (HandlePool v0.4 annex, D.3; §38). -/
theorem setSlot_shape {pl : Pool} {i : Nat} {sl x : Slot} (hs : pl.slots[i]? = some sl)
    (hx : x.place = sl.place) : (setSlot pl i x).shape = pl.shape := by
  simp only [Pool.shape, setSlot, map_set_same (·.place) hs hx]

/-- Well-formedness of a pool shape (auxiliary, not a clause of the contract; HandlePool v0.4 annex,
HandlePool v0.4 annex, D.1, from `newPool`): `internal` is a `Modify` authority whose footprint is
the footprint of the storage (§76.2, §76.3); the storage and every slot have a leaf; slots lie in
the storage and are pairwise disjoint (D.1). -/
structure PoolOK (s : S3) (sh : PoolShape) : Prop where
  /-- §76.2: `internal` exists, with own mode `Modify`. -/
  internalMode : OptP (s.A[sh.internal]?) (fun y => y.mode = .modify) False
  /-- §76.3: `footprint(internal) = footprint(storage)`. -/
  fpEq : ∀ l, l ∈ s.afp sh.internal ↔ l ∈ footprint s.P sh.storage
  /-- §40, §49.2: the storage has a leaf. -/
  storageLeaf : ∃ l, l ∈ footprint s.P sh.storage
  /-- §40, §49.2: every slot has a leaf. -/
  slotLeaf : ∀ q ∈ sh.places, ∃ l, l ∈ footprint s.P q
  /-- D.1: slots lie in the storage. -/
  slotIn : ∀ q ∈ sh.places, ∀ l ∈ footprint s.P q, l ∈ footprint s.P sh.storage
  /-- D.1: slots are pairwise disjoint. -/
  disjoint : ∀ (a b qa qb : Nat), sh.places[a]? = some qa → sh.places[b]? = some qb → a ≠ b →
    ∀ l ∈ footprint s.P qa, l ∉ footprint s.P qb

/-- Well-formedness of a ghost resolution (auxiliary, HandlePool v0.4 annex, D.2): it belongs to a
pool of `shs` with its `internal`; the companion is younger than `internal`, of the mode of the
resolution, over the footprint of the storage; each entry authority is younger than the companion,
over the footprint of its slot (§38, §60). -/
def ResOK (s : S3) (shs : List PoolShape) (r : Res) : Prop :=
  ∃ sh ∈ shs, sh.id = r.pool ∧ sh.internal = r.internal ∧ r.internal < r.comp ∧
    OptP (s.A[r.comp]?) (fun y => y.mode = r.mode ∧
      ∀ l, l ∈ y.footprint ↔ l ∈ footprint s.P sh.storage) False ∧
    ∀ e ∈ r.entries, r.comp < e.1 ∧ ∃ q, sh.places[e.2.1]? = some q ∧
      OptP (s.A[e.1]?) (fun y => ∀ l, l ∈ y.footprint ↔ l ∈ footprint s.P q) False

/-- Ghost well-formedness of the pool layer (auxiliary, not a clause of the contract; HandlePool
v0.4 annex, D.1, D.2): fresh distinct identities, well-formed pools and
resolutions (§38). -/
structure PoolWF (L : PState) : Prop where
  /-- D.1: identities are below the next fresh identity. -/
  ids : ∀ sh ∈ L.pools.map Pool.shape, sh.id < L.nId
  /-- D.1: identities are distinct. -/
  nodup : ((L.pools.map Pool.shape).map (·.id)).Nodup
  /-- D.1: every pool is well formed. -/
  pools : ∀ sh ∈ L.pools.map Pool.shape, PoolOK L.kern sh
  /-- D.2: every ghost resolution is well formed. -/
  res : ∀ r ∈ L.res, ResOK L.kern (L.pools.map Pool.shape) r

/-- `pool_no_stale_access` as a state predicate (HandlePool v0.4 annex, D.4, item 2; non-normative
library contract): no active entry authority designates a free slot or a former generation (§89). -/
def NoStale (L : PState) : Prop :=
  ∀ r ∈ L.res, ∀ e ∈ r.entries, L.kern.Active e.1 → ∃ pl ∈ L.pools, pl.id = r.pool ∧
    ∃ sl, pl.slots[e.2.1]? = some sl ∧ sl.gen = e.2.2 ∧ sl.live = true

/-- Exclusivity of companions (HandlePool v0.4 annex, D.2; non-normative library contract): two
distinct active companions of a pool are both `Observe` (§43, §50). -/
def CompExcl (L : PState) : Prop :=
  ∀ r₁ ∈ L.res, ∀ r₂ ∈ L.res, r₁.pool = r₂.pool → r₁.comp ≠ r₂.comp →
    L.kern.Active r₁.comp → L.kern.Active r₂.comp → r₁.mode = .observe ∧ r₂.mode = .observe

/-- Footprints of every place with a leaf are kept (§40; support for HandlePool v0.4 annex, D.1). -/
def FpKeep (s s' : S3) : Prop :=
  ∀ q l₀, l₀ ∈ footprint s.P q → ∀ l, l ∈ footprint s'.P q ↔ l ∈ footprint s.P q

/-- Same places keep footprints (§40). -/
theorem fpKeep_of_P {s s' : S3} (h : s'.P = s.P) : FpKeep s s' := fun _ _ _ _ => by rw [h]

/-- Kernel steps keep footprints (§40; §60–§75 effects). -/
theorem fpKeep_kstep {k : K} {s s' : S3} (h : KStep k s s') : FpKeep s s' :=
  fun _ _ h₀ l => Arena.kstep_fp h (Arena.footprint_lt h₀) l

/-- `FpKeep` composes (§40). -/
theorem FpKeep.trans {s s₁ s₂ : S3} (h₁ : FpKeep s s₁) (h₂ : FpKeep s₁ s₂) : FpKeep s s₂ :=
  fun q l₀ h₀ l => (h₂ q l₀ ((h₁ q l₀ h₀ l₀).2 h₀) l).trans (h₁ q l₀ h₀ l)

/-- A sequence of kernel steps keeps the authorities and the footprints (§42, §58; §60–§75). -/
theorem KSeq.keep {k : K} {s s' : S3} (h : KSeq k s s') : Arena.AKeep s s' ∧ FpKeep s s' := by
  induction h with
  | refl => exact ⟨Arena.akeep_of_eq rfl, fpKeep_of_P rfl⟩
  | tail _ hs ih => exact ⟨ih.1.trans (Arena.kstep_akeep hs), ih.2.trans (fpKeep_kstep hs)⟩

/-- The end of a slot content keeps the authorities (§69 effect: authorities are only released). -/
theorem endUseEff_akeep (s : S3) (q : Nat) : Arena.AKeep s (endUseEff s q) :=
  (Arena.akeep_map (s' := endUseS s q) rfl fun y => by
      by_cases hc : heldIn s.P q y.holder <;> simp [hc]).trans
    (Arena.akeep_map rfl fun y => by
      by_cases hc : HolderLive (endUseS s q) y.holder <;> simp [hc])

/-- The ended place stays usable (§69 `ok` effect: "`place` remains usable as a place";
HandlePool v0.4 annex, D.3: no deallocation), under `WF3` (§49): no place on its ownership chain is
owned by it. -/
theorem endUseEff_usable {s : S3} {p : Nat} (hw : WF3 s) (hp : s.Usable p) :
    (endUseEff s p).Usable p := by
  refine (EndFree.cleanup_usable _ p).2 ?_
  suffices ∀ q, s.Usable q → (q = p ∨ EndFree.Above s.P p q) → (endUseS s p).Usable q from
    this p hp (.inl rfl)
  intro q hq
  induction hq with
  | frame hpl hd ho hf =>
    intro hc
    have hn := EndFree.not_ownedIn_chain hw hp hc
    exact .frame hpl (by simp [endUseS, hd, hn]) ho hf
  | place hpl hd ho _ ih =>
    intro hc
    have hn := EndFree.not_ownedIn_chain hw hp hc
    refine .place hpl (by simp [endUseS, hd, hn]) ho (ih ?_)
    rcases hc with rfl | hc
    · exact .inr (.owner hpl ho)
    · exact .inr (hc.trans (.owner hpl ho))

/-- `PoolOK` carries over to a state keeping authorities and footprints (§42, §40; HandlePool v0.4
annex, D.1). -/
theorem PoolOK.transport {s s' : S3} {sh : PoolShape} (h : PoolOK s sh) (hA : Arena.AKeep s s')
    (hf : FpKeep s s') : PoolOK s' sh := by
  obtain ⟨hm, hfp, ⟨l₀, hl₀⟩, hsl, hin, hd⟩ := h
  obtain ⟨y, hy, hym⟩ := optP_false_iff.1 hm
  obtain ⟨y', hy', m', f', -⟩ := hA _ y hy
  have hst := hf sh.storage l₀ hl₀
  have hq : ∀ q ∈ sh.places, ∀ l, l ∈ footprint s'.P q ↔ l ∈ footprint s.P q := fun q hq' => by
    obtain ⟨l₁, hl₁⟩ := hsl q hq'; exact hf q l₁ hl₁
  have hafp : s'.afp sh.internal = s.afp sh.internal := by simp [S3.afp, hy, hy', f']
  refine ⟨optP_false_iff.2 ⟨y', hy', m'.trans hym⟩, fun l => ?_, ⟨l₀, (hst l₀).2 hl₀⟩,
    fun q hq' => ?_, fun q hq' l hl => ?_, fun a b qa qb ha hb hab l hla hlb => ?_⟩
  · rw [hafp, hst]; exact hfp l
  · obtain ⟨l₁, hl₁⟩ := hsl q hq'; exact ⟨l₁, (hq q hq' l₁).2 hl₁⟩
  · exact (hst l).2 (hin q hq' l ((hq q hq' l).1 hl))
  · exact hd a b qa qb ha hb hab l ((hq qa (List.mem_of_getElem? ha) l).1 hla)
      ((hq qb (List.mem_of_getElem? hb) l).1 hlb)

/-- `ResOK` carries over to a state keeping authorities and footprints and to a larger list of
shapes (HandlePool v0.4 annex, D.2; §42). -/
theorem ResOK.transport {s s' : S3} {shs shs' : List PoolShape} {r : Res} (h : ResOK s shs r)
    (hA : Arena.AKeep s s') (hf : FpKeep s s') (hok : ∀ sh ∈ shs, PoolOK s sh)
    (hsub : ∀ sh ∈ shs, sh ∈ shs') : ResOK s' shs' r := by
  obtain ⟨sh, hsh, hid, hint, hlt, hc, he⟩ := h
  have hok' := hok sh hsh
  obtain ⟨l₀, hl₀⟩ := hok'.storageLeaf
  obtain ⟨y, hy, hm, hfp⟩ := optP_false_iff.1 hc
  obtain ⟨y', hy', m', f', -⟩ := hA _ y hy
  refine ⟨sh, hsub sh hsh, hid, hint, hlt, optP_false_iff.2 ⟨y', hy', m'.trans hm, fun l => ?_⟩,
    fun e he' => ?_⟩
  · rw [f', hf _ l₀ hl₀ l]; exact hfp l
  · obtain ⟨hlt', q, hq, ho⟩ := he e he'
    obtain ⟨z, hz, hzf⟩ := optP_false_iff.1 ho
    obtain ⟨z', hz', -, zf', -⟩ := hA _ z hz
    obtain ⟨l₁, hl₁⟩ := hok'.slotLeaf q (List.mem_of_getElem? hq)
    exact ⟨hlt', q, hq,
      optP_false_iff.2 ⟨z', hz', fun l => by rw [zf', hf q l₁ hl₁ l]; exact hzf l⟩⟩

/-- `PoolWF` carries over to a state keeping authorities and footprints, with pools of the same
shapes (HandlePool v0.4 annex, D.1, D.2, D.3; §42). -/
theorem PoolWF.transport {L : PState} {s' : S3} {pools' : List Pool} (h : PoolWF L)
    (hA : Arena.AKeep L.kern s') (hf : FpKeep L.kern s')
    (hsh : pools'.map Pool.shape = L.pools.map Pool.shape) :
    PoolWF ⟨s', pools', L.nId, L.res⟩ := by
  refine ⟨?_, ?_, ?_, fun r hr => ?_⟩
  · show ∀ sh ∈ pools'.map Pool.shape, sh.id < L.nId
    rw [hsh]; exact h.ids
  · show ((pools'.map Pool.shape).map (·.id)).Nodup
    rw [hsh]; exact h.nodup
  · show ∀ sh ∈ pools'.map Pool.shape, PoolOK s' sh
    rw [hsh]; exact fun sh hs => (h.pools sh hs).transport hA hf
  · show ResOK s' (pools'.map Pool.shape) r
    rw [hsh]; exact (h.res r hr).transport hA hf h.pools fun _ h => h

/-- An entry authority of a ghost resolution exists (HandlePool v0.4 annex, D.2; §42). -/
theorem entry_lt {L : PState} (hw : PoolWF L) {r : Res} (hr : r ∈ L.res) {e : Nat × Nat × Nat}
    (he : e ∈ r.entries) : e.1 < L.kern.A.length := by
  obtain ⟨_, _, _, _, _, _, hen⟩ := hw.res r hr
  obtain ⟨_, _, _, ho⟩ := hen e he
  obtain ⟨y, hy, -⟩ := optP_false_iff.1 ho
  exact lt_of_getElem? hy

/-- A companion of a ghost resolution exists (HandlePool v0.4 annex, D.2; §42). -/
theorem comp_lt {L : PState} (hw : PoolWF L) {r : Res} (hr : r ∈ L.res) :
    r.comp < L.kern.A.length := by
  obtain ⟨_, _, _, _, _, hc, _⟩ := hw.res r hr
  obtain ⟨y, hy, -⟩ := optP_false_iff.1 hc
  exact lt_of_getElem? hy

/-- `NoStale` carries over to a kernel state that reactivates nothing (HandlePool v0.4 annex, D.4,
item 2; §42). -/
theorem NoStale.kern {L : PState} {s' : S3} (h : NoStale L) (hw : PoolWF L)
    (hA : Arena.AKeep L.kern s') : NoStale { L with kern := s' } :=
  fun r hr e he ha => h r hr e he (hA.active_back ha (entry_lt hw hr he))

/-- `CompExcl` carries over to a kernel state that reactivates nothing (HandlePool v0.4 annex, D.2)
(§42). -/
theorem CompExcl.kern {L : PState} {s' : S3} (h : CompExcl L) (hw : PoolWF L)
    (hA : Arena.AKeep L.kern s') : CompExcl { L with kern := s' } :=
  fun r₁ hr₁ r₂ hr₂ hp hne ha₁ ha₂ => h r₁ hr₁ r₂ hr₂ hp hne
    (hA.active_back ha₁ (comp_lt hw hr₁)) (hA.active_back ha₂ (comp_lt hw hr₂))

/-- Two shapes of a list with distinct identities and the same identity are equal (HandlePool v0.4
annex, D.1; §46). -/
theorem eq_of_id : ∀ {l : List PoolShape} {a b : PoolShape}, (l.map (·.id)).Nodup → a ∈ l →
    b ∈ l → a.id = b.id → a = b
  | [], _, _, _, ha, _, _ => by simp at ha
  | c :: l, a, b, hn, ha, hb, he => by
    rw [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.1 ha with ha' | ha' <;> rcases List.mem_cons.1 hb with hb' | hb'
    · rw [ha', hb']
    · subst ha'; exact absurd (he ▸ List.mem_map_of_mem (f := (·.id)) hb') hn.1
    · subst hb'; exact absurd (he.symm ▸ List.mem_map_of_mem (f := (·.id)) ha') hn.1
    · exact eq_of_id hn.2 ha' hb' he

/-- The ghost resolution of pool `pl` names its `internal` (HandlePool v0.4 annex, D.2; §38). -/
theorem res_internal {L : PState} (hw : PoolWF L) {r : Res} (hr : r ∈ L.res) {pl : Pool}
    (hpl : pl ∈ L.pools) (hp : r.pool = pl.id) :
    r.internal = pl.internal ∧ r.internal < r.comp ∧
      (∀ e ∈ r.entries, r.comp < e.1 ∧ ∃ q, (pl.slots.map (·.place))[e.2.1]? = some q ∧
        OptP (L.kern.A[e.1]?) (fun y => ∀ l, l ∈ y.footprint ↔ l ∈ footprint L.kern.P q) False) ∧
      OptP (L.kern.A[r.comp]?) (fun y => y.mode = r.mode ∧
        ∀ l, l ∈ y.footprint ↔ l ∈ footprint L.kern.P pl.storage) False := by
  obtain ⟨sh, hsh, hid, hint, hlt, hc, he⟩ := hw.res r hr
  have e : sh = pl.shape :=
    eq_of_id hw.nodup hsh (List.mem_map_of_mem hpl) (hid.trans hp)
  subst e
  exact ⟨hint.symm, hlt, he, hc⟩

/-! ## Preservation of the ghost invariants (HandlePool v0.4 annex, D.1–D.4) -/

/-- An active companion of a pool and a new companion are both `Observe` (HandlePool v0.4 annex,
D.2: "Une compagne `Modify` active bloque les nouvelles compagnes … ; des compagnes `Observe`
peuvent coexister"): an active companion unrelated to `internal` contradicts I1 (§50), since
`internal` is `Modify`; a descendant takes away the effective mode that the new derivation needs
(§43, §60.2). -/
theorem companion_blocks {s : S3} (hi1 : I1 s) {pl : Pool} {m : Mode} (hR : ResolveRight s pl m)
    (hok : PoolOK s pl.shape) {c : Nat} {y : Authority} (hc : s.A[c]? = some y)
    (ya : y.active = true) (hlt : pl.internal < c)
    (hfp : ∀ l, l ∈ y.footprint ↔ l ∈ footprint s.P pl.storage) :
    y.mode = .observe ∧ m = .observe := by
  obtain ⟨l, hl⟩ := hok.storageLeaf
  obtain ⟨xi, hxi, xa⟩ := hR.active
  obtain ⟨xi', hxi', hmi⟩ := optP_false_iff.1 hok.internalMode
  have e : xi' = xi := Option.some.inj (hxi'.symm.trans hxi)
  subst e
  have hli : l ∈ xi'.footprint := by have := hR.within l hl; simpa [S3.afp, hxi] using this
  have hly : l ∈ y.footprint := (hfp l).2 hl
  have hz : pl.internal ∈ s.ancs c := Decidable.byContradiction fun hn => by
    have hn2 : c ∉ s.ancs pl.internal := fun h => absurd (chain_lt h) (by omega)
    have := hi1 pl.internal c xi' y l (by omega) hxi hc xa ya hli hly hn hn2
    rw [hmi] at this; cases this.1
  have hal := hR.modeOK l hl
  rw [effective_eq hxi xa hli] at hal
  have hd : y.mode ∈ descModes s pl.internal l := mem_descModes.2 ⟨c, y, hc, ya, hly, hz, rfl⟩
  rcases allows_effOf hal with ⟨h0, -⟩ | ⟨hn, rfl⟩
  · rw [h0] at hd; cases hd
  · exact ⟨mode_eq_observe fun e => hn (e ▸ hd), rfl⟩

/-- A new resolution of pool `pl`, made under `ResolveRight`, keeps `CompExcl` (HandlePool v0.4
annex, D.2; §43, §50, §60). -/
theorem compExcl_new {L : PState} {s' : S3} {pl : Pool} {m : Mode} {rn : Res}
    (hi1 : I1 L.kern) (hwf : PoolWF L) (hce : CompExcl L) (hA : Arena.AKeep L.kern s')
    (hpl : pl ∈ L.pools) (hR : ResolveRight L.kern pl m) (hrp : rn.pool = pl.id)
    (hrm : rn.mode = m) : CompExcl ⟨s', L.pools, L.nId, L.res ++ [rn]⟩ := by
  have hok := hwf.pools _ (List.mem_map_of_mem hpl)
  have key : ∀ r ∈ L.res, r.pool = pl.id → L.kern.Active r.comp →
      r.mode = .observe ∧ m = .observe := fun r hr hp ha => by
    obtain ⟨hint, hlt, -, hc⟩ := res_internal hwf hr hpl hp
    obtain ⟨y, hy, hm, hfp⟩ := optP_false_iff.1 hc
    obtain ⟨y', hy', ya⟩ := ha; rw [hy] at hy'; cases hy'
    have := companion_blocks hi1 hR hok hy ya (hint ▸ hlt) hfp
    exact ⟨by rw [← hm]; exact this.1, this.2⟩
  have hb : ∀ r ∈ L.res, s'.Active r.comp → L.kern.Active r.comp :=
    fun r hr ha => hA.active_back ha (comp_lt hwf hr)
  intro r₁ hr₁ r₂ hr₂ hp hne ha₁ ha₂
  rcases List.mem_append.1 hr₁ with hr₁ | hr₁ <;> rcases List.mem_append.1 hr₂ with hr₂ | hr₂
  · exact hce r₁ hr₁ r₂ hr₂ hp hne (hb r₁ hr₁ ha₁) (hb r₂ hr₂ ha₂)
  · rw [List.mem_singleton.1 hr₂] at hp ⊢
    have := key r₁ hr₁ (hp.trans hrp) (hb r₁ hr₁ ha₁)
    exact ⟨this.1, hrm.trans this.2⟩
  · rw [List.mem_singleton.1 hr₁] at hp ⊢
    have := key r₂ hr₂ (hp.symm.trans hrp) (hb r₂ hr₂ ha₂)
    exact ⟨hrm.trans this.2, this.1⟩
  · rw [List.mem_singleton.1 hr₁, List.mem_singleton.1 hr₂] at hne; exact absurd rfl hne

/-- Adding a well-formed resolution keeps `PoolWF` (HandlePool v0.4 annex, D.2; §60). -/
theorem poolWF_addRes {L : PState} {s' : S3} {rn : Res} (h : PoolWF L)
    (hA : Arena.AKeep L.kern s') (hf : FpKeep L.kern s')
    (hrn : ResOK s' (L.pools.map Pool.shape) rn) : PoolWF ⟨s', L.pools, L.nId, L.res ++ [rn]⟩ := by
  have h' := h.transport hA hf rfl
  refine ⟨h'.ids, h'.nodup, h'.pools, fun r hr => ?_⟩
  rcases List.mem_append.1 hr with hr | hr
  · exact h'.res r hr
  · rw [List.mem_singleton.1 hr]; exact hrn

/-- Adding a resolution whose entries designate live slots at their generation keeps `NoStale`
(HandlePool v0.4 annex, D.4, item 2; §60). -/
theorem noStale_addRes {L : PState} {s' : S3} {rn : Res} (h : NoStale L) (hw : PoolWF L)
    (hA : Arena.AKeep L.kern s')
    (hrn : ∀ e ∈ rn.entries, ∃ pl ∈ L.pools, pl.id = rn.pool ∧
      ∃ sl, pl.slots[e.2.1]? = some sl ∧ sl.gen = e.2.2 ∧ sl.live = true) :
    NoStale ⟨s', L.pools, L.nId, L.res ++ [rn]⟩ := by
  intro r hr e he ha
  rcases List.mem_append.1 hr with hr | hr
  · exact (h.kern hw hA) r hr e he ha
  · rw [List.mem_singleton.1 hr] at he ⊢; exact hrn e he

/-- Authorities after `resolve` (§60 effects; HandlePool v0.4 annex, D.2): the companion `|A|`,
then the entry authority `|A| + 1` derived from it. -/
theorem resolve_A (s : S3) (pl : Pool) (m : Mode) (R : List Nat) :
    (deriveEff (compS s pl m) s.A.length R m).A = s.A ++
      [⟨m, some pl.internal, footprint s.P pl.storage, .frame s.top, true⟩,
        ⟨m, some s.A.length, R, .frame s.top, true⟩] := by
  simp [deriveEff, compS, S3.addAuth, S3.top]

/-- Authorities after `resolveMany` (§60, §61 effects; HandlePool v0.4 annex, D.2): the companion
`|A|`, then one entry authority per handle, derived from it. -/
theorem resolveMany_A (m : Mode) (s : S3) (pl : Pool) (hs : List Handle) :
    (entriesEff m (compS s pl m) s.A.length (entryRegions s pl hs)).A = s.A ++
      ⟨m, some pl.internal, footprint s.P pl.storage, .frame s.top, true⟩ ::
        hs.map fun h => ⟨m, some s.A.length, footprint s.P (slotPlace pl h.slot), .frame s.top,
          true⟩ := by
  rw [entriesEff_eq]; simp [compS, deriveEff, S3.addAuth, S3.top, entryRegions]

/-- `newPool` keeps the ghost invariants (HandlePool v0.4 annex, D.1): the new pool is well formed
under `WF3` (§49), its slots being the children of the storage. -/
theorem pinv_newPool {L L' : PState} {others : List (List Nat)} {st i : Nat} (hw : WF3 L.kern)
    (hwf : PoolWF L) (hns : NoStale L) (hce : CompExcl L)
    (h : NewPoolStep others st i L (.ok L')) : PoolWF L' ∧ NoStale L' ∧ CompExcl L' := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  have hb := hpre.base
  have hshape : (newPoolEff L st i).pools.map Pool.shape =
      L.pools.map Pool.shape ++ [⟨L.nId, st, i, kids L.kern.P st⟩] := by
    simp [newPoolEff, Pool.shape, Function.comp_def]
  have hsub : ∀ sh ∈ L.pools.map Pool.shape, sh ∈ (newPoolEff L st i).pools.map Pool.shape :=
    fun sh hs => by rw [hshape]; exact List.mem_append_left _ hs
  have hnew : PoolOK L.kern ⟨L.nId, st, i, kids L.kern.P st⟩ := by
    obtain ⟨y, hy, -, hm⟩ := optP_false_iff.1 hb.internalAuth
    have hk : (kids L.kern.P st).Pairwise (· < ·) := (range_pairwise_lt _).filter _
    refine ⟨optP_false_iff.2 ⟨y, hy, hm⟩, fun l => ⟨hb.fpSub l, hb.fpSup l⟩,
      exists_mem_footprint hw _ st (Nat.lt_succ_self _) hb.storageUsable.lt,
      fun q hq => exists_mem_footprint hw _ q (Nat.lt_succ_self _) (mem_kids.1 hq).1,
      fun q hq l hl => ?_, fun a b qa qb ha hb' hab => ?_⟩
    · obtain ⟨hql, hpq⟩ := mem_kids.1 hq
      exact footprint_sub hw ⟨hql, .inr (by
        rw [chain_cons hpq (hw.parent_lt hpq).1]; exact List.mem_cons_self ..)⟩ hl
    · exact kids_disjoint hw (List.mem_of_getElem? ha) (List.mem_of_getElem? hb')
        fun e => hab (index_inj_of_lt hk ha (e ▸ hb'))
  refine ⟨⟨fun sh hs => ?_, ?_, fun sh hs => ?_, fun r hr => ?_⟩, fun r hr e he ha => ?_, hce⟩
  · rw [hshape] at hs
    rcases List.mem_append.1 hs with hs | hs
    · exact Nat.lt_succ_of_lt (hwf.ids sh hs)
    · rw [List.mem_singleton.1 hs]; exact Nat.lt_succ_self _
  · show (((newPoolEff L st i).pools.map Pool.shape).map (·.id)).Nodup
    rw [hshape, List.map_append]
    refine List.nodup_append.2 ⟨hwf.nodup, by simp, fun a ha b hb' => ?_⟩
    rw [List.mem_singleton.1 hb']
    obtain ⟨sh, hsh, rfl⟩ := List.mem_map.1 ha
    exact Nat.ne_of_lt (hwf.ids sh hsh)
  · rw [hshape] at hs
    rcases List.mem_append.1 hs with hs | hs
    · exact hwf.pools sh hs
    · rw [List.mem_singleton.1 hs]; exact hnew
  · exact (hwf.res r hr).transport (Arena.akeep_of_eq rfl) (fpKeep_of_P rfl) hwf.pools hsub
  · obtain ⟨pl, hpl, rest⟩ := hns r hr e he ha
    exact ⟨pl, List.mem_append_left _ hpl, rest⟩

/-- `allocSlot` keeps the ghost invariants (HandlePool v0.4 annex, D.3): the chosen slot was free,
so no active entry authority designates it (§67). -/
theorem pinv_allocSlot {L L' : PState} {j dst : Nat} (hwf : PoolWF L) (hns : NoStale L)
    (hce : CompExcl L) (h : AllocSlotStep j dst L (.ok L')) :
    PoolWF L' ∧ NoStale L' ∧ CompExcl L' := by
  cases h with
  | @ok pl i sl hpj _ hsl hfree =>
    have hshape :=
      map_set_same Pool.shape hpj (setSlot_shape (x := { sl with live := true }) hsl rfl)
    have hA : Arena.AKeep L.kern (write3Eff L.kern [dst]) := Arena.akeep_of_eq rfl
    refine ⟨hwf.transport hA (fpKeep_of_P rfl) hshape, fun r hr e he ha => ?_,
      hce.kern hwf hA⟩
    obtain ⟨pl0, hpl0, hid, sl0, hs0, hg, hlv⟩ := hns r hr e he ha
    by_cases hp : pl0 = pl
    · subst hp
      refine ⟨_, mem_set_self' hpj, hid, ?_⟩
      by_cases hi : e.2.1 = i
      · rw [hi, hsl] at hs0; cases hs0; rw [hfree] at hlv; cases hlv
      · exact ⟨sl0, by simp only [setSlot]; rw [getElem?_set_ne' hi]; exact hs0, hg, hlv⟩
    · exact ⟨pl0, mem_set_of_ne hpj hpl0 hp, hid, sl0, hs0, hg, hlv⟩

/-- `resolve` keeps the ghost invariants (HandlePool v0.4 annex, D.2), under I1 (§50). -/
theorem pinv_resolve {L L' : PState} {j : Nat} {h : Handle} {m : Mode} (hi1 : I1 L.kern)
    (hwf : PoolWF L) (hns : NoStale L) (hce : CompExcl L) (hst : ResolveStep j h m L (.ok L')) :
    PoolWF L' ∧ NoStale L' ∧ CompExcl L' := by
  cases hst with
  | @ok pl sl hpj hR hH hsl _ =>
    have hpl : pl ∈ L.pools := List.mem_of_getElem? hpj
    have hok := hwf.pools _ (List.mem_map_of_mem hpl)
    have hAe := resolve_A L.kern pl m (footprint L.kern.P sl.place)
    have hA : Arena.AKeep L.kern
        (deriveEff (compS L.kern pl m) L.kern.A.length (footprint L.kern.P sl.place) m) :=
      Arena.akeep_append hAe
    obtain ⟨xi, hxi, -⟩ := optP_false_iff.1 hok.internalMode
    obtain ⟨-, hsl'⟩ := hH
    rw [hsl] at hsl'; obtain ⟨hg, hlv⟩ := hsl'
    refine ⟨poolWF_addRes hwf hA (fpKeep_of_P rfl) ⟨pl.shape, List.mem_map_of_mem hpl, rfl, rfl,
        lt_of_getElem? hxi, ?_, fun e he => ?_⟩,
      noStale_addRes hns hwf hA fun e he => ?_, compExcl_new hi1 hwf hce hA hpl hR rfl rfl⟩
    · rw [hAe]; simp [OptP, Pool.shape]; exact fun _ => Iff.rfl
    · rw [List.mem_singleton.1 he]
      refine ⟨Nat.lt_succ_self _, sl.place, by simp [Pool.shape, hsl], ?_⟩
      rw [hAe]; simp [OptP]; exact fun _ => Iff.rfl
    · rw [List.mem_singleton.1 he]
      exact ⟨pl, hpl, rfl, sl, hsl, hg, hlv⟩

/-- `resolveMany` keeps the ghost invariants (HandlePool v0.4 annex, D.2), under I1 (§50). -/
theorem pinv_resolveMany {k : K} {L L' : PState} {j : Nat} {hs : List Handle} {m : Mode}
    (hi1 : I1 L.kern) (hwf : PoolWF L) (hns : NoStale L) (hce : CompExcl L)
    (hst : ResolveManyStep k j hs m L (.ok L')) : PoolWF L' ∧ NoStale L' ∧ CompExcl L' := by
  cases hst with
  | @ok pl hpj hR hB _ =>
    have hpl : pl ∈ L.pools := List.mem_of_getElem? hpj
    have hok := hwf.pools _ (List.mem_map_of_mem hpl)
    have hAe := resolveMany_A m L.kern pl hs
    have hA : Arena.AKeep L.kern
        (entriesEff m (compS L.kern pl m) L.kern.A.length (entryRegions L.kern pl hs)) :=
      Arena.akeep_append hAe
    obtain ⟨xi, hxi, -⟩ := optP_false_iff.1 hok.internalMode
    have hval : ∀ h ∈ hs, ∃ sl, pl.slots[h.slot]? = some sl ∧ sl.gen = h.gen ∧
        sl.live = true ∧ slotPlace pl h.slot = sl.place := fun h hh => by
      obtain ⟨-, hsl⟩ := hB.1 h hh
      obtain ⟨sl, hsl, hg, hlv⟩ := optP_false_iff.1 hsl
      exact ⟨sl, hsl, hg, hlv, by simp [slotPlace, hsl]⟩
    have hP : (entriesEff m (compS L.kern pl m) L.kern.A.length (entryRegions L.kern pl hs)).P =
        L.kern.P := by rw [entriesEff_eq]; rfl
    refine ⟨poolWF_addRes hwf hA (fpKeep_of_P hP) ⟨pl.shape, List.mem_map_of_mem hpl, rfl, rfl,
        lt_of_getElem? hxi, ?_, fun e he => ?_⟩,
      noStale_addRes hns hwf hA fun e he => ?_, compExcl_new hi1 hwf hce hA hpl hR rfl rfl⟩
    · rw [hAe, hP]; simp [OptP, Pool.shape]
    · obtain ⟨n, h, hh, rfl⟩ := mem_batchEntries he
      obtain ⟨sl, hsl, -, -, hsp⟩ := hval h (List.mem_of_getElem? hh)
      refine ⟨by simp; omega, sl.place, by simp [Pool.shape, hsl], ?_⟩
      rw [hAe, hP, List.getElem?_append_right (by omega)]
      simp [show L.kern.A.length + 1 + n - L.kern.A.length = n + 1 by omega, hh, OptP, hsp]
    · obtain ⟨n, h, hh, rfl⟩ := mem_batchEntries he
      obtain ⟨sl, hsl, hg, hlv, -⟩ := hval h (List.mem_of_getElem? hh)
      exact ⟨pl, hpl, rfl, sl, hsl, hg, hlv⟩

/-- `unresolve` keeps the ghost invariants (HandlePool v0.4 annex, D.2): it is a sequence of
`release` steps (§62). -/
theorem pinv_unresolve {k : K} {L L' : PState} {c : Nat} (hwf : PoolWF L) (hns : NoStale L)
    (hce : CompExcl L) (h : UnresolveStep c L (.ok L')) : PoolWF L' ∧ NoStale L' ∧ CompExcl L' := by
  cases h with
  | ok _ hr =>
    obtain ⟨hA, hf⟩ := (releaseAll_kseq (k := k) hr).keep
    exact ⟨hwf.transport hA hf rfl, hns.kern hwf hA, hce.kern hwf hA⟩

/-- `freeSlot` keeps the ghost invariants (HandlePool v0.4 annex, D.3, D.4): an active entry
authority of the freed slot would cover the entry without being `internal` or one of its
ancestors, which `ContentEndPre` excludes (§69). -/
theorem pinv_freeSlot {k : K} {L L' : PState} {j : Nat} {h : Handle} (hwf : PoolWF L)
    (hns : NoStale L) (hce : CompExcl L) (hst : FreeSlotStep k j h L (.ok L')) :
    PoolWF L' ∧ NoStale L' ∧ CompExcl L' := by
  cases hst with
  | @ok pl sl hpj _ _ hsl hpre =>
    have hshape := map_set_same Pool.shape hpj
      (setSlot_shape (x := ⟨sl.place, sl.gen + 1, false⟩) hsl rfl)
    have hA := endUseEff_akeep L.kern sl.place
    refine ⟨hwf.transport hA (fpKeep_of_P rfl) hshape, fun r hr e he ha => ?_, hce.kern hwf hA⟩
    have hpl : pl ∈ L.pools := List.mem_of_getElem? hpj
    have ha₀ := hA.active_back ha (entry_lt hwf hr he)
    obtain ⟨pl0, hpl0, hid, sl0, hs0, hg, hlv⟩ := hns r hr e he ha₀
    by_cases hp : pl0 = pl
    · subst hp
      refine ⟨_, mem_set_self' hpj, hid, ?_⟩
      by_cases hi : e.2.1 = h.slot
      · exfalso
        obtain ⟨hint, hlt, hen, -⟩ := res_internal hwf hr hpl hid.symm
        obtain ⟨hlt', q, hq, ho⟩ := hen e he
        rw [hi, List.getElem?_map, hsl] at hq; cases hq
        obtain ⟨y, hy, hfp⟩ := optP_false_iff.1 ho
        obtain ⟨l, hl⟩ := (hwf.pools _ (List.mem_map_of_mem hpl)).slotLeaf sl.place
          (List.mem_map_of_mem (f := (·.place)) (List.mem_of_getElem? hsl))
        have hex := hpre.entry e.1 (List.mem_range.2 (entry_lt hwf hr he)) ha₀
          ⟨l, by simp only [S3.afp, hy]; exact (hfp l).2 hl, hl⟩
        rcases hex with he' | he'
        · omega
        · have := chain_lt he'; omega
      · exact ⟨sl0, by simp only [setSlot]; rw [getElem?_set_ne' hi]; exact hs0, hg, hlv⟩
    · exact ⟨pl0, mem_set_of_ne hpj hpl0 hp, hid, sl0, hs0, hg, hlv⟩

/-- Every library step keeps the ghost invariants (HandlePool v0.4 annex, D.1–D.4), under `WF3`
and I1 (§49, §50). -/
theorem pstep_inv {k : K} {L L' : PState} (hw : WF3 L.kern) (hi1 : I1 L.kern) (hwf : PoolWF L)
    (hns : NoStale L) (hce : CompExcl L) (h : PStep k L L') :
    PoolWF L' ∧ NoStale L' ∧ CompExcl L' := by
  cases h with
  | kernel hs =>
    have hA := Arena.kstep_akeep hs
    exact ⟨hwf.transport hA (fpKeep_kstep hs) rfl, hns.kern hwf hA, hce.kern hwf hA⟩
  | newPool hs => exact pinv_newPool hw hwf hns hce hs
  | allocSlot hs => exact pinv_allocSlot hwf hns hce hs
  | resolve hs => exact pinv_resolve hi1 hwf hns hce hs
  | resolveMany hs => exact pinv_resolveMany hi1 hwf hns hce hs
  | unresolve hs => exact pinv_unresolve (k := k) hwf hns hce hs
  | freeSlot hs => exact pinv_freeSlot hwf hns hce hs

/-- The invariants of library runs (HandlePool v0.4 annex, D.1–D.4; §57): on every state reached
by steps from states satisfying `KInv`, the kernel state is reached by kernel steps and ends of slot
contents, and the ghost invariants hold. -/
theorem pReachI_inv {k : K} {statics : Statics} {L : PState} (h : PReachI k statics L) :
    XReach k statics L.kern ∧ PoolWF L ∧ NoStale L ∧ CompExcl L := by
  induction h with
  | init =>
    refine ⟨.init, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;> simp [PState.init, NoStale, CompExcl]
  | step _ hk hs ih =>
    obtain ⟨hr, hwf, hns, hce⟩ := ih
    exact ⟨xreach_pstep hr hk hs, pstep_inv hk.1 hk.2.1.1.1 hwf hns hce hs⟩

/-- Under the guarantee of §57 (`KernelGuarantee`), every library-reachable state is reached by
steps from states satisfying `KInv` (HandlePool v0.4 annex). -/
theorem PReach.toI {k : K} {statics : Statics} (hX : KernelGuarantee k statics) {L : PState}
    (h : PReach k statics L) : PReachI k statics L := by
  have hxr := pReach_xreach hX h
  induction h with
  | init => exact .init
  | step hr hs ih => exact .step (ih (pReach_xreach hX hr)) (hX _ (pReach_xreach hX hr)) hs

/-! ## `PoolInv` (HandlePool v0.4 annex, D.4) -/

/-- `PoolInv`, item 1 (HandlePool v0.4 annex, D.4; non-normative library contract): the entries of
every pool lie in its storage and are pairwise disjoint (§40). -/
def EntriesDisjoint (L : PState) : Prop :=
  ∀ pl ∈ L.pools,
    (∀ sl ∈ pl.slots, ∀ l ∈ footprint L.kern.P sl.place, l ∈ footprint L.kern.P pl.storage) ∧
    ∀ (a b : Nat) (sa sb : Slot), pl.slots[a]? = some sa → pl.slots[b]? = some sb → a ≠ b →
      ∀ l ∈ footprint L.kern.P sa.place, l ∉ footprint L.kern.P sb.place

/-- `PoolInv`, item 3, the transition guarantee (HandlePool v0.4 annex, D.4; non-normative library
contract): `freeSlot` never succeeds while an active descendant of a companion of the pool covers
the slot concerned (§43, §69). -/
def FreeGuarantee (k : K) (L : PState) : Prop :=
  ∀ (j : Nat) (h : Handle) (L' : PState), FreeSlotStep k j h L (.ok L') →
    ∀ (pl : Pool) (sl : Slot), L.pools[j]? = some pl → pl.slots[h.slot]? = some sl →
      ∀ r ∈ L.res, r.pool = pl.id → ∀ x, L.kern.Active x → (x = r.comp ∨ r.comp ∈ L.kern.ancs x) →
        ∀ l ∈ L.kern.afp x, l ∉ footprint L.kern.P sl.place

/-- `PoolInv` (HandlePool v0.4 annex, D.4, as corrected; non-normative library contract): entry
disjointness, `pool_no_stale_access`, and the transition guarantee of `freeSlot` (§55, §57). -/
def PoolInv (k : K) (L : PState) : Prop := EntriesDisjoint L ∧ NoStale L ∧ FreeGuarantee k L

/-- `EntriesDisjoint` follows from the ghost well-formedness (HandlePool v0.4 annex, D.4, item 1)
(§40). -/
theorem entriesDisjoint_of {L : PState} (hwf : PoolWF L) : EntriesDisjoint L := by
  intro pl hpl
  have hok := hwf.pools _ (List.mem_map_of_mem hpl)
  exact ⟨fun sl hsl l hl => hok.slotIn sl.place (List.mem_map_of_mem (f := (·.place)) hsl) l hl,
    fun a b sa sb ha hb hab => hok.disjoint a b sa.place sb.place
      (by simp [Pool.shape, ha]) (by simp [Pool.shape, hb]) hab⟩

/-- The transition guarantee follows from the ghost well-formedness (HandlePool v0.4 annex, D.4,
item 3): an active descendant of a companion of the pool is younger than `internal`, so it is
neither `internal` nor one of its ancestors, and `ContentEndPre` forbids it to cover the entry (§43,
§69). -/
theorem freeGuarantee_of {k : K} {L : PState} (hwf : PoolWF L) : FreeGuarantee k L := by
  intro j h L' hst pl sl hpj hsl r hr hrp x hx hxr l hl hlq
  cases hst with
  | @ok pl' sl' hpj' _ _ hsl' hpre =>
    rw [hpj] at hpj'; cases hpj'
    rw [hsl] at hsl'; cases hsl'
    obtain ⟨hint, hlt, -, -⟩ := res_internal hwf hr (List.mem_of_getElem? hpj) hrp
    obtain ⟨y, hy, ya⟩ := hx
    have hex := hpre.entry x (List.mem_range.2 (lt_of_getElem? hy)) ⟨y, hy, ya⟩ ⟨l, hl, hlq⟩
    have hcx : r.comp ≤ x := by
      rcases hxr with rfl | hc
      · exact Nat.le_refl _
      · exact Nat.le_of_lt (chain_lt hc)
    unfold Exempt at hex
    rcases hex with rfl | h'
    · omega
    · have := chain_lt h'; omega

/-- `pool_inv_preserved` (HandlePool v0.4 annex, D.4): `PoolInv` holds on every state of a library
run whose steps start from states satisfying `KInv` (§57); with `PReach.toI`, on every
library-reachable state under the guarantee of §57. -/
theorem pool_inv_preserved {k : K} {statics : Statics} {L : PState} (h : PReachI k statics L) :
    PoolInv k L :=
  have ⟨_, hwf, hns, _⟩ := pReachI_inv h
  ⟨entriesDisjoint_of hwf, hns, freeGuarantee_of hwf⟩

/-- `pool_entries_disjoint` (HandlePool v0.4 annex, D.4, item 1; §40). -/
theorem pool_entries_disjoint {k : K} {statics : Statics} {L : PState} (h : PReachI k statics L) :
    EntriesDisjoint L :=
  (pool_inv_preserved h).1

/-- `pool_no_stale_access` (HandlePool v0.4 annex, D.4, item 2): on every state of a library run
(`PReachI`), an active entry authority designates a live slot at its current generation (§89). -/
theorem pool_no_stale_access {k : K} {statics : Statics} {L : PState} (h : PReachI k statics L) :
    NoStale L :=
  (pool_inv_preserved h).2.1

/-- `pool_freeSlot_no_companion_desc` (HandlePool v0.4 annex, D.4, item 3): on every state of a
library run (`PReachI`), `freeSlot` never succeeds while an active descendant of a companion of the
pool covers the slot (§43, §69). -/
theorem pool_freeSlot_no_companion_desc {k : K} {statics : Statics} {L : PState}
    (h : PReachI k statics L) : FreeGuarantee k L :=
  (pool_inv_preserved h).2.2

/-- `pool_resolve_modify_exclusive` (HandlePool v0.4 annex, D.2: "La propriété d'exclusivité
concerne toutes les suites d'opérations admises du noyau"): on every state of a library run
(`PReachI`), whatever its kernel steps, an active `Modify` companion of a pool is its only active
companion (§43, §50). -/
theorem pool_resolve_modify_exclusive {k : K} {statics : Statics} {L : PState}
    (h : PReachI k statics L) :
    ∀ r₁ ∈ L.res, ∀ r₂ ∈ L.res, r₁.pool = r₂.pool → L.kern.Active r₁.comp →
      L.kern.Active r₂.comp → r₁.mode = .modify → r₁.comp = r₂.comp := by
  intro r₁ hr₁ r₂ hr₂ hp ha₁ ha₂ hm
  refine Decidable.byContradiction fun hne => ?_
  have := (pReachI_inv h).2.2.2 r₁ hr₁ r₂ hr₂ hp hne ha₁ ha₂
  rw [hm] at this; cases this.1

/-! ## Handle validation: stale, other pool, free slot (HandlePool v0.4 annex, D.2, D.3; §89) -/

/-- A handle of another pool is not valid (HandlePool v0.4 annex, D.2, D.3; §89). -/
theorem not_handleOK_other {pl : Pool} {h : Handle} (hid : h.id ≠ pl.id) : ¬ HandleOK pl h :=
  fun ⟨e, _⟩ => hid e

/-- A stale handle is not valid (HandlePool v0.4 annex, D.2, D.3; §89). -/
theorem not_handleOK_stale {pl : Pool} {h : Handle} {sl : Slot} (hsl : pl.slots[h.slot]? = some sl)
    (hg : sl.gen ≠ h.gen) : ¬ HandleOK pl h :=
  fun ⟨_, ho⟩ => by rw [hsl] at ho; exact hg ho.1

/-- A handle of a free slot is not valid, even at the slot's generation (HandlePool v0.4 annex,
D.2: "slot … libre ⇒ `fail`"; D.3: "un slot déjà libre n'est pas rendu libérable par cette seule
égalité"; §89). -/
theorem not_handleOK_free {pl : Pool} {h : Handle} {sl : Slot} (hsl : pl.slots[h.slot]? = some sl)
    (hf : sl.live = false) : ¬ HandleOK pl h :=
  fun ⟨_, ho⟩ => by rw [hsl] at ho; have h2 := ho.2; rw [hf] at h2; cases h2

/-- With the legal exercise of `internal`, an invalid handle makes `resolve` fail, and `fail` is its
only outcome (HandlePool v0.4 annex, D.2: "⇒ `fail`, sans changement d'état"; §58). -/
theorem pool_resolve_invalid_fails {L : PState} {j : Nat} {pl : Pool} {h : Handle} {m : Mode}
    (hp : L.pools[j]? = some pl) (hR : ResolveRight L.kern pl m) (hH : ¬ HandleOK pl h) :
    ResolveStep j h m L .fail ∧ ∀ o, ResolveStep j h m L o → o = .fail := by
  refine ⟨.fail hp hR hH, fun o ho => ?_⟩
  cases ho with
  | noPool hn => rw [hp] at hn; cases hn
  | noRight hp' hn => rw [hp] at hp'; cases hp'; exact absurd hR hn
  | fail => rfl
  | noEntry hp' _ hH' => rw [hp] at hp'; cases hp'; exact absurd hH' hH
  | ok hp' _ hH' => rw [hp] at hp'; cases hp'; exact absurd hH' hH

/-- `pool_resolve_stale_fails` (HandlePool v0.4 annex, D.2; §89: "a stale identity or generation
leads to defined failure"). -/
theorem pool_resolve_stale_fails {L : PState} {j : Nat} {pl : Pool} {h : Handle} {m : Mode}
    {sl : Slot} (hp : L.pools[j]? = some pl) (hR : ResolveRight L.kern pl m)
    (hsl : pl.slots[h.slot]? = some sl) (hg : sl.gen ≠ h.gen) :
    ResolveStep j h m L .fail ∧ ∀ o, ResolveStep j h m L o → o = .fail :=
  pool_resolve_invalid_fails hp hR (not_handleOK_stale hsl hg)

/-- `pool_resolve_other_pool_fails` (HandlePool v0.4 annex, D.2; §89). -/
theorem pool_resolve_other_pool_fails {L : PState} {j : Nat} {pl : Pool} {h : Handle} {m : Mode}
    (hp : L.pools[j]? = some pl) (hR : ResolveRight L.kern pl m) (hid : h.id ≠ pl.id) :
    ResolveStep j h m L .fail ∧ ∀ o, ResolveStep j h m L o → o = .fail :=
  pool_resolve_invalid_fails hp hR (not_handleOK_other hid)

/-- With `AdminRight`, an invalid handle makes `freeSlot` fail, and `fail` is its only outcome
(HandlePool v0.4 annex, D.3: "`fail` si l'identité ou la génération ne correspond pas; un slot déjà
libre n'est pas rendu libérable par cette seule égalité"; §58). -/
theorem pool_freeSlot_invalid_fails {k : K} {L : PState} {j : Nat} {pl : Pool} {h : Handle}
    (hp : L.pools[j]? = some pl) (hR : AdminRight L.kern pl) (hH : ¬ HandleOK pl h) :
    FreeSlotStep k j h L .fail ∧ ∀ o, FreeSlotStep k j h L o → o = .fail := by
  refine ⟨.fail hp hR hH, fun o ho => ?_⟩
  cases ho with
  | noPool hn => rw [hp] at hn; cases hn
  | noRight hp' hn => rw [hp] at hp'; cases hp'; exact absurd hR hn
  | fail => rfl
  | noEnd hp' _ hH' => rw [hp] at hp'; cases hp'; exact absurd hH' hH
  | ok hp' _ hH' => rw [hp] at hp'; cases hp'; exact absurd hH' hH

/-- `freeSlot` of a stale handle, of a handle of another pool, or of a free slot at its generation
fails (HandlePool v0.4 annex, D.3; §58, §89). -/
theorem pool_freeSlot_stale_other_free_fails {k : K} {L : PState} {j : Nat} {pl : Pool}
    {h : Handle} {sl : Slot} (hp : L.pools[j]? = some pl) (hR : AdminRight L.kern pl)
    (hsl : pl.slots[h.slot]? = some sl) :
    (sl.gen ≠ h.gen ∨ h.id ≠ pl.id ∨ sl.live = false) →
      FreeSlotStep k j h L .fail ∧ ∀ o, FreeSlotStep k j h L o → o = .fail := by
  rintro (hg | hid | hf)
  · exact pool_freeSlot_invalid_fails hp hR (not_handleOK_stale hsl hg)
  · exact pool_freeSlot_invalid_fails hp hR (not_handleOK_other hid)
  · exact pool_freeSlot_invalid_fails hp hR (not_handleOK_free hsl hf)

/-! ## `resolveMany`: atomicity and distinctness (HandlePool v0.4 annex, D.2) -/

/-- With the legal exercise of `internal`, an invalid batch makes `resolveMany` fail, and `fail` is
its only outcome: no partial creation of rights (HandlePool v0.4 annex, D.2: "`fail` atomique";
§58). -/
theorem pool_resolveMany_invalid_fails {k : K} {L : PState} {j : Nat} {pl : Pool}
    {hs : List Handle} {m : Mode} (hp : L.pools[j]? = some pl) (hR : ResolveRight L.kern pl m)
    (hB : ¬ BatchOK pl hs m) :
    ResolveManyStep k j hs m L .fail ∧ ∀ o, ResolveManyStep k j hs m L o → o = .fail := by
  refine ⟨.fail hp hR hB, fun o ho => ?_⟩
  cases ho with
  | noPool hn => rw [hp] at hn; cases hn
  | noRight hp' hn => rw [hp] at hp'; cases hp'; exact absurd hR hn
  | fail => rfl
  | noEntries hp' _ hB' => rw [hp] at hp'; cases hp'; exact absurd hB' hB
  | ok hp' _ hB' => rw [hp] at hp'; cases hp'; exact absurd hB' hB

/-- `pool_resolveMany_atomic` (HandlePool v0.4 annex, D.2): an invalid handle makes the whole batch
fail; an accepted batch creates exactly one companion and one entry authority per handle, each
derived from the companion, in one step (§58, §60, §61). -/
theorem pool_resolveMany_atomic {k : K} {L L' : PState} {j : Nat} {pl : Pool} {hs : List Handle}
    {m : Mode} :
    (L.pools[j]? = some pl → ResolveRight L.kern pl m → (∃ h ∈ hs, ¬ HandleOK pl h) →
      ∀ o, ResolveManyStep k j hs m L o → o = .fail) ∧
    (ResolveManyStep k j hs m L (.ok L') → ∃ pl', L.pools[j]? = some pl' ∧ BatchOK pl' hs m ∧
      L'.kern.A = L.kern.A ++
        ⟨m, some pl'.internal, footprint L.kern.P pl'.storage, .frame L.kern.top, true⟩ ::
          hs.map fun h => ⟨m, some L.kern.A.length, footprint L.kern.P (slotPlace pl' h.slot),
            .frame L.kern.top, true⟩) := by
  refine ⟨fun hp hR ⟨h, hh, hn⟩ => (pool_resolveMany_invalid_fails hp hR
    fun hB => hn (hB.1 h hh)).2, fun hst => ?_⟩
  cases hst with
  | @ok pl' hp _ hB _ => exact ⟨pl', hp, hB, resolveMany_A m L.kern pl' hs⟩

/-- `pool_resolveMany_distinct` (HandlePool v0.4 annex, D.2: distinctness is checked in `Modify`
only): in `Modify`, a repeated slot makes the batch fail and an accepted batch has distinct slots;
in `Observe`, validity does not depend on distinctness, so a repeated valid handle never makes the
batch fail (§58, §61). -/
theorem pool_resolveMany_distinct {k : K} {L L' : PState} {j : Nat} {pl : Pool}
    {hs : List Handle} :
    (L.pools[j]? = some pl → ResolveRight L.kern pl .modify → ¬ (hs.map (·.slot)).Nodup →
      ∀ o, ResolveManyStep k j hs .modify L o → o = .fail) ∧
    (ResolveManyStep k j hs .modify L (.ok L') → (hs.map (·.slot)).Nodup) ∧
    (BatchOK pl hs .observe ↔ ∀ h ∈ hs, HandleOK pl h) ∧
    (L.pools[j]? = some pl → (∀ h ∈ hs, HandleOK pl h) →
      ∀ o, ResolveManyStep k j hs .observe L o → o ≠ .fail) := by
  refine ⟨fun hp hR hd => (pool_resolveMany_invalid_fails hp hR fun hB => hd (hB.2 rfl)).2,
    fun h => ?_, ⟨fun h => h.1, fun h => ⟨h, fun e => by cases e⟩⟩, fun hp hv o ho => ?_⟩
  · cases h with
    | ok _ _ hB _ => exact hB.2 rfl
  · cases ho with
    | fail hp' _ hB => rw [hp] at hp'; cases hp'; exact absurd ⟨hv, fun e => by cases e⟩ hB
    | _ => exact fun e => by cases e

/-! ## The composite borrow (HandlePool v0.4 annex, D.2) -/

/-- The composite borrow of `resolve` (HandlePool v0.4 annex, D.2: "dérive de `internal` une
autorité compagne couvrant toutes les feuilles du stockage … puis dérive de cette compagne une
autorité de même mode"): in the arrival state, the companion `|A|` has origin `internal` and covers
the storage, the entry `|A| + 1` has origin the companion and covers the slot, both at mode `m`, and
the origin chain of the entry is the companion, `internal` and the chain of `internal` (§42, §60).
-/
theorem resolve_composite {L L' : PState} {j : Nat} {h : Handle} {m : Mode}
    (hst : ResolveStep j h m L (.ok L')) :
    ∃ pl sl, L.pools[j]? = some pl ∧ pl.slots[h.slot]? = some sl ∧ HandleOK pl h ∧
      L'.kern.A[L.kern.A.length]? =
        some ⟨m, some pl.internal, footprint L.kern.P pl.storage, .frame L.kern.top, true⟩ ∧
      L'.kern.A[L.kern.A.length + 1]? =
        some ⟨m, some L.kern.A.length, footprint L.kern.P sl.place, .frame L.kern.top, true⟩ ∧
      L'.kern.ancs (L.kern.A.length + 1) =
        L.kern.A.length :: pl.internal :: L.kern.ancs pl.internal := by
  cases hst with
  | @ok pl sl hp hR hH hsl _ =>
    have hAe := resolve_A L.kern pl m (footprint L.kern.P sl.place)
    obtain ⟨xi, hxi, -⟩ := hR.active
    have hilt := lt_of_getElem? hxi
    refine ⟨pl, sl, hp, hsl, hH, by rw [hAe]; simp, by rw [hAe]; simp, ?_⟩
    have hlen : (compS L.kern pl m).A.length = L.kern.A.length + 1 := by
      simp [compS, deriveEff, S3.addAuth]
    show ((compS L.kern pl m).addAuth _).ancs (L.kern.A.length + 1) = _
    rw [← hlen, ancs_addAuth_self rfl (by rw [hlen]; exact Nat.lt_succ_self _)]
    exact congrArg _ (ancs_addAuth_self rfl hilt)

/-! ## `freeSlot` (HandlePool v0.4 annex, D.3) -/

/-- `pool_freeSlot_ends_content` (HandlePool v0.4 annex, D.3: "L'effet `ok` applique au contenu
les effets de fin d'usage d'`endUse`, remet les feuilles de l'entrée à `Uninit`, marque l'entrée
libre et incrémente sa génération"): an accepted `freeSlot` has a live pool with `MetaRight`, a
valid handle and `ContentEndPre`; its kernel state is the effect of O12 on the slot (§69), whose
leaves are `Uninit`; the slot is free with its generation incremented. -/
theorem pool_freeSlot_ends_content {k : K} {L L' : PState} {j : Nat} {h : Handle}
    (hst : FreeSlotStep k j h L (.ok L')) :
    ∃ pl sl, L.pools[j]? = some pl ∧ pl.slots[h.slot]? = some sl ∧ AdminRight L.kern pl ∧
      HandleOK pl h ∧ ContentEndPre k L.kern sl.place pl.internal ∧
      L'.kern = endUseEff L.kern sl.place ∧
      (∀ l ∈ footprint L.kern.P sl.place, L'.kern.I l = .uninit) ∧
      L'.pools[j]? = some (setSlot pl h.slot ⟨sl.place, sl.gen + 1, false⟩) := by
  cases hst with
  | @ok pl sl hp hR hH hsl hpre =>
    refine ⟨pl, sl, hp, hsl, hR, hH, hpre, rfl, fun l hl => ?_, getElem?_set_eq' hp⟩
    show (cleanup (endUseS L.kern sl.place)).I l = .uninit
    simp [cleanup, endUseS, hl]

/-- §69.1 under the `Modify` right (HandlePool v0.4 annex, D.3: "Il ne s'agit pas de supposer une
invocation de O12 autorisée par simple `MetaRight`"): for a slot of a well-formed pool, `AdminRight`
and the entry clause of `ContentEndPre` give exercisable `Modify` over the slot, through
`internal`, and, under `NoDangling` (§54), its usability. -/
theorem freeSlot_modify_right {k : K} {s : S3} {pl : Pool} {q : Nat} (hok : PoolOK s pl.shape)
    (hq : q ∈ pl.shape.places) (hr : AdminRight s pl) (hpre : ContentEndPre k s q pl.internal)
    (hnd : NoDangling s) : s.Usable q ∧ HasRight s .modify q := by
  obtain ⟨y, hy, ya⟩ := hr.1
  obtain ⟨y', hy', hmy⟩ := optP_false_iff.1 hok.internalMode
  have e : y' = y := Option.some.inj (hy'.symm.trans hy)
  subst e
  have hmr := hr.2
  simp only [Arena.MetaRight, Arena.arenaValue, Pool.entry, hy] at hmr
  obtain ⟨v, hv, b, -, hb, hall⟩ : ∃ v, y'.holder = .place v ∧ HasRight s .modify v := by
    revert hmr; cases hh : y'.holder with
    | frame f => simp [OptP]
    | place v => exact fun hm => ⟨v, rfl, hm⟩
  have hex : s.ExercisableAt pl.internal .modify := .held hy ya (.inr hmy) hv hb hall
  have hcov : ∀ l ∈ footprint s.P q, l ∈ y'.footprint := fun l hl => by
    have := (hok.fpEq l).2 (hok.slotIn q hq l hl); simpa [S3.afp, Pool.shape, hy] using this
  have heff : ∀ l ∈ footprint s.P q, effective s pl.internal l = some .modify := fun l hl => by
    rw [effective_eq hy ya (hcov l hl)]
    have hnil : descModes s pl.internal l = [] := nil_of_forall_not_mem fun md hmd => by
      obtain ⟨j, z, hz, za, hlz, hij, -⟩ := mem_descModes.1 hmd
      have hex' := hpre.entry j (List.mem_range.2 (lt_of_getElem? hz)) ⟨z, hz, za⟩
        ⟨l, by simpa [S3.afp, hz] using hlz, hl⟩
      have := chain_lt hij
      unfold Exempt at hex'
      rcases hex' with rfl | h'
      · omega
      · have := chain_lt h'; omega
    rw [hnil, hmy]; rfl
  obtain ⟨l, hl⟩ := hok.slotLeaf q hq
  exact ⟨Arena.usable_of_covered hnd hy ya (hcov l hl) hl,
    ⟨pl.internal, List.mem_range.2 (lt_of_getElem? hy), hex,
      fun l hl => by rw [heff l hl]; exact Arena.allows_some_modify _⟩⟩

/-- An accepted `freeSlot` preserves the kernel invariant `KInv ∧ KAux` (§57; HandlePool v0.4 annex,
HandlePool v0.4 annex, D.3: "la préservation des invariants sous ce droit constitue une obligation
explicite"). -/
theorem freeSlot_preserves {k : K} {L L' : PState} {j : Nat} {h : Handle} (hk : KInv L.kern)
    (ha : KAux L.kern) (hst : FreeSlotStep k j h L (.ok L')) : KInv L'.kern ∧ KAux L'.kern := by
  obtain ⟨pl, sl, -, -, -, -, hpre, he, -⟩ := pool_freeSlot_ends_content hst
  rw [he]; exact contentEnd_preserves hk ha hpre

/-- `pool_freeSlot_ends_content` under the `Modify` right (HandlePool v0.4 annex, D.3): on a state
of a library run (`PReachI`) satisfying `KInv` (§57), an accepted `freeSlot` acts on a usable slot
over which the current frame has exercisable `Modify` through `internal` (§69.1), and leaves the
slot usable (§69: "`place` remains usable"; D.3: no deallocation). -/
theorem pool_freeSlot_under_modify {k : K} {statics : Statics} {L L' : PState}
    (hL : PReachI k statics L) (hk : KInv L.kern) {j : Nat} {h : Handle}
    (hst : FreeSlotStep k j h L (.ok L')) :
    ∃ pl sl, L.pools[j]? = some pl ∧ pl.slots[h.slot]? = some sl ∧
      L.kern.Usable sl.place ∧ HasRight L.kern .modify sl.place ∧
      L'.kern = endUseEff L.kern sl.place ∧ L'.kern.Usable sl.place := by
  obtain ⟨-, hwf, -⟩ := pReachI_inv hL
  obtain ⟨pl, sl, hp, hsl, hR, -, hpre, he, -⟩ := pool_freeSlot_ends_content hst
  have hpl : pl ∈ L.pools := List.mem_of_getElem? hp
  obtain ⟨hu, hright⟩ := freeSlot_modify_right (hwf.pools _ (List.mem_map_of_mem hpl))
    (List.mem_map_of_mem (f := (·.place)) (List.mem_of_getElem? hsl)) hR hpre hk.2.1.2.2
  exact ⟨pl, sl, hp, hsl, hu, hright, he, by rw [he]; exact endUseEff_usable hk.1 hu⟩

/-! ## Rights required by `allocSlot`, `freeSlot`, `newPool` (HandlePool v0.4 annex, D.1, D.3) -/

/-- `allocSlot` requires a live pool and `MetaRight`, exercisable `Modify` over the pool value
(HandlePool v0.4 annex, D.3, corrected by §36). Its effect writes only `dst`, makes the chosen free
slot live with its generation kept, and changes no other slot (D.3). -/
theorem allocSlot_effect {L L' : PState} {j dst : Nat} (h : AllocSlotStep j dst L (.ok L')) :
    ∃ pl i sl, L.pools[j]? = some pl ∧ AdminRight L.kern pl ∧ AllocSlotStatic L.kern pl dst ∧
      pl.slots[i]? = some sl ∧ sl.live = false ∧ L'.kern = write3Eff L.kern [dst] ∧
      L'.kern.I dst = .init ∧ (∀ l, l ≠ dst → L'.kern.I l = L.kern.I l) ∧
      L'.pools[j]? = some (setSlot pl i { sl with live := true }) ∧
      slotHandle pl i = some ⟨pl.id, i, sl.gen⟩ := by
  cases h with
  | @ok pl i sl hp hst hsl hf =>
    refine ⟨pl, i, sl, hp, hst.right, hst, hsl, hf, rfl,
      by show (write3Eff L.kern [dst]).I dst = .init; simp [write3Eff], fun l hl => ?_,
      getElem?_set_eq' hp, by simp [slotHandle, hsl]⟩
    show (write3Eff L.kern [dst]).I l = L.kern.I l
    simp [write3Eff, hl]

/-- `freeSlot` requires a live pool and `MetaRight`, exercisable `Modify` over the pool value
(HandlePool v0.4 annex, D.3, corrected by §36). -/
theorem freeSlot_requires {k : K} {L L' : PState} {j : Nat} {h : Handle}
    (hst : FreeSlotStep k j h L (.ok L')) :
    ∃ pl, L.pools[j]? = some pl ∧ L.kern.Active pl.internal ∧ Arena.MetaRight L.kern pl.entry := by
  obtain ⟨pl, -, hp, -, hR, -⟩ := pool_freeSlot_ends_content hst
  exact ⟨pl, hp, hR⟩

/-- `newPool` requires `Uninit` storage and the guard of §56 over the pool registry and every
other registry of live administrations, and changes no kernel component (HandlePool v0.4 annex,
D.1; §56). -/
theorem newPool_requires {others : List (List Nat)} {st i : Nat} {L L' : PState}
    (h : NewPoolStep others st i L (.ok L')) :
    (∀ l ∈ footprint L.kern.P st, L.kern.I l = .uninit) ∧
      Arena.Guard56 (liveInternals L.kern L.pools :: others) i ∧
      Arena.NewArenaBase L.kern st i ∧ L'.kern = L.kern := by
  obtain ⟨hp, rfl⟩ := Guarded.ok_iff.1 h
  exact ⟨hp.uninit, hp.guard, hp.base, rfl⟩

/-! ## Uniqueness of live administration in the pool registry (§56) -/

/-- §56 for the pool registry (HandlePool v0.4 annex, D.1: "Une autorité ne peut être `internal`
de deux abstractions vivantes"): two live pools at distinct positions have distinct
`internal`. -/
def Unique56 (L : PState) : Prop :=
  ∀ (a b : Nat) (pa pb : Pool), a ≠ b → L.pools[a]? = some pa → L.pools[b]? = some pb →
    L.kern.Active pa.internal → L.kern.Active pb.internal → pa.internal ≠ pb.internal

/-- Every registered `internal` exists (§42; HandlePool v0.4 annex, D.1; auxiliary). -/
def RegOK (L : PState) : Prop := ∀ pl ∈ L.pools, pl.internal < L.kern.A.length

/-- A step that keeps the authorities and the `internal` of every registered pool keeps
`Unique56` and `RegOK` (§56; authorities are never reactivated, §42). -/
theorem unique56_keep {L L' : PState} (hu : Unique56 L) (hr : RegOK L)
    (hA : Arena.AKeep L.kern L'.kern)
    (hp : ∀ n : Nat, (L'.pools[n]?).map Pool.internal = (L.pools[n]?).map Pool.internal) :
    Unique56 L' ∧ RegOK L' := by
  have back : ∀ (n : Nat) (pl' : Pool), L'.pools[n]? = some pl' → ∃ pl, L.pools[n]? = some pl ∧
      pl.internal = pl'.internal := fun n pl' h => by
    have := hp n; rw [h] at this
    cases hn : L.pools[n]? with
    | none => rw [hn] at this; cases this
    | some pl => rw [hn] at this; exact ⟨pl, rfl, (Option.some.inj this).symm⟩
  refine ⟨fun a b pa' pb' hab ha hb haa hba => ?_, fun pl' hpl' => ?_⟩
  · obtain ⟨pa, ha₀, ea⟩ := back a pa' ha
    obtain ⟨pb, hb₀, eb⟩ := back b pb' hb
    rw [← ea] at haa ⊢; rw [← eb] at hba ⊢
    exact hu a b pa pb hab ha₀ hb₀
      (hA.active_back haa (hr pa (List.mem_of_getElem? ha₀)))
      (hA.active_back hba (hr pb (List.mem_of_getElem? hb₀)))
  · obtain ⟨n, hn, hn'⟩ := List.getElem_of_mem hpl'
    obtain ⟨pl, h₀, e⟩ := back n pl' (by rw [List.getElem?_eq_getElem hn, hn'])
    rw [← e]; exact hA.lt (hr pl (List.mem_of_getElem? h₀))

/-- Replacing a slot keeps the `internal` at every position (HandlePool v0.4 annex, D.3; §56). -/
theorem internals_set {pools : List Pool} {j i : Nat} {pl : Pool} {x : Slot}
    (hj : pools[j]? = some pl) (n : Nat) :
    ((pools.set j (setSlot pl i x))[n]?).map Pool.internal = (pools[n]?).map Pool.internal := by
  by_cases hn : n = j
  · subst hn; rw [getElem?_set_eq' hj, hj]; rfl
  · rw [getElem?_set_ne' hn]

/-- `newPool` keeps `Unique56` and `RegOK` (§56, §76.4; HandlePool v0.4 annex, D.1): the guard
excludes the `internal` of every live registered pool. -/
theorem unique56_newPool {L L' : PState} {others : List (List Nat)} {st i : Nat}
    (hu : Unique56 L) (hr : RegOK L) (hs : NewPoolStep others st i L (.ok L')) :
    Unique56 L' ∧ RegOK L' := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 hs
  obtain ⟨y, hy, -⟩ := optP_false_iff.1 hpre.base.internalAuth
  have hg : ∀ pl ∈ L.pools, L.kern.Active pl.internal → pl.internal ≠ i := fun pl hpl ha e =>
    hpre.guard _ (List.mem_cons_self ..) (by
      rw [← e]; exact List.mem_map_of_mem (List.mem_filter.2 ⟨hpl, by simpa using ha⟩))
  have get : ∀ (n : Nat) (pl : Pool), (newPoolEff L st i).pools[n]? = some pl →
      L.pools[n]? = some pl ∨ pl.internal = i := fun n pl h => by
    simp only [newPoolEff] at h
    by_cases hn : n < L.pools.length
    · exact .inl (by rwa [List.getElem?_append_left hn] at h)
    · rw [List.getElem?_append_right (by omega)] at h
      cases e : n - L.pools.length with
      | zero =>
        rw [e] at h; simp only [List.getElem?_cons_zero, Option.some.injEq] at h
        exact .inr (by rw [← h])
      | succ _ => rw [e] at h; simp at h
  refine ⟨fun a b pa pb hab ha hb haa hba => ?_, fun pl hpl => ?_⟩
  · rcases get a pa ha with ha₀ | ea <;> rcases get b pb hb with hb₀ | eb
    · exact hu a b pa pb hab ha₀ hb₀ haa hba
    · rw [eb]; exact hg pa (List.mem_of_getElem? ha₀) haa
    · rw [ea]; exact fun e => hg pb (List.mem_of_getElem? hb₀) hba e.symm
    · exfalso
      have hla := lt_of_getElem? ha; have hlb := lt_of_getElem? hb
      simp only [newPoolEff, List.length_append, List.length_singleton] at hla hlb
      have hna : ¬ a < L.pools.length := fun hl => by
        rw [show (newPoolEff L st i).pools = L.pools ++ _ from rfl,
          List.getElem?_append_left hl] at ha
        exact hg pa (List.mem_of_getElem? ha) haa (ea ▸ rfl)
      have hnb : ¬ b < L.pools.length := fun hl => by
        rw [show (newPoolEff L st i).pools = L.pools ++ _ from rfl,
          List.getElem?_append_left hl] at hb
        exact hg pb (List.mem_of_getElem? hb) hba (eb ▸ rfl)
      omega
  · rcases List.mem_append.1 hpl with hpl | hpl
    · exact hr pl hpl
    · rw [List.mem_singleton.1 hpl]; exact lt_of_getElem? hy

/-- `live_pool_internal_unique` (§56; HandlePool v0.4 annex, D.1): on every library-reachable
state, two live pools at distinct positions of the registry have distinct `internal`. The guard of
`newPool` gives it; no kernel invariant is needed. -/
theorem live_pool_internal_unique {k : K} {statics : Statics} {L : PState}
    (h : PReach k statics L) : Unique56 L ∧ RegOK L := by
  induction h with
  | init => exact ⟨fun _ _ _ _ _ ha => by simp [PState.init] at ha, fun _ h => by
      simp [PState.init] at h⟩
  | step _ hs ih =>
    obtain ⟨hu, hr⟩ := ih
    cases hs with
    | kernel hk => exact unique56_keep hu hr (Arena.kstep_akeep hk) fun _ => rfl
    | allocSlot hs =>
      cases hs with
      | ok hj _ _ _ => exact unique56_keep hu hr (Arena.akeep_of_eq rfl) (internals_set hj)
    | resolve hs =>
      cases hs with
      | ok =>
        exact unique56_keep hu hr (Arena.akeep_append (resolve_A _ _ _ _)) fun _ => rfl
    | resolveMany hs =>
      cases hs with
      | ok => exact unique56_keep hu hr (Arena.akeep_append (resolveMany_A _ _ _ _)) fun _ => rfl
    | unresolve hs =>
      cases hs with
      | ok _ hrl => exact unique56_keep hu hr (releaseAll_kseq (k := k) hrl).keep.1 fun _ => rfl
    | freeSlot hs =>
      cases hs with
      | ok hj _ _ _ _ => exact unique56_keep hu hr (endUseEff_akeep _ _) (internals_set hj)
    | newPool hs => exact unique56_newPool hu hr hs

/-! ## Witnesses on library-reachable states (HandlePool v0.4 annex, D.2, D.3)

Runs from `PState.init Witness.hst` under the test contract `Examples.K0` (§48). Statics (§47):
place 0 is the pool storage, with two leaf children 1 and 2 (`Uninit`); place 3 is the pool value
(`Init`); place 4 is a destination (`Uninit`); root authorities 0, 1 and 2 cover places 0, 3 and 4.
`internal` is authority 3, derived from 0 over `[1, 2]` and stored in place 3. Every precondition is
decided by `decide`. -/

namespace Witness

open Examples

/-- Statics of the witnesses (§47; HandlePool v0.4 annex, D.1). -/
def hst : Statics :=
  [((none, none, 0), false), ((some 0, none, 0), false), ((some 0, none, 0), false),
    ((none, none, 0), true), ((none, none, 0), false)]

/-- Initial library state (§47). -/
def w0 : PState := PState.init hst

/-- After `derive(0, [1, 2], Modify)` (§60): authority 3, the future `internal`. -/
def w1 : PState := { w0 with kern := deriveEff w0.kern 0 [1, 2] .modify }

/-- After `store(3, 3)` (§65): `internal` is held by the pool value, place 3. -/
def w2 : PState := { w1 with kern := storeEff w1.kern 3 3 }

/-- After `newPool(0, 3)` (HandlePool v0.4 annex, D.1): pool 0 with slots 1 and 2, free, of
generation 0 (§47). -/
def w3 : PState := newPoolEff w2 0 3

/-- Pool 0 after `newPool` (HandlePool v0.4 annex, D.1; §47). -/
def pl3 : Pool := ⟨0, 0, 3, [⟨1, 0, false⟩, ⟨2, 0, false⟩]⟩

/-- After `allocSlot(0, 4)` on slot 0 (HandlePool v0.4 annex, D.3): the handle `⟨0, 0, 0⟩` is
written into place 4 (§47, §67). -/
def w4 : PState := allocSlotEff w3 0 pl3 0 ⟨1, 0, false⟩ 4

/-- Pool 0 after `allocSlot` (HandlePool v0.4 annex, D.3; §47). -/
def pl4 : Pool := ⟨0, 0, 3, [⟨1, 0, true⟩, ⟨2, 0, false⟩]⟩

/-- `w3` is reached by a library run whose steps start from states satisfying `KInv` (§57, §60,
§65; HandlePool v0.4 annex, D.1). -/
theorem w3_reach : PReachI K0 hst w3 :=
  .step (.step (.step .init (Arena.KInvB.sound (by decide)).1
    (.kernel (.derive (Guarded.ok (by decide))))) (Arena.KInvB.sound (by decide)).1
    (.kernel (.store (Guarded.ok (by decide))))) (Arena.KInvB.sound (by decide)).1
    (.newPool (others := []) (Guarded.ok (by decide)))

/-- `w4` is library-reachable (HandlePool v0.4 annex, D.3; §47, §67). -/
theorem w4_reach : PReachI K0 hst w4 :=
  .step w3_reach (Arena.KInvB.sound (by decide)).1
    (.allocSlot (.ok (pl := pl3) rfl (by decide) rfl rfl))

/-- `resolveMany` in `Observe` accepts a repeated valid handle (HandlePool v0.4 annex, D.2: "la
répétition du même handle valide est permise"): two `Observe` entry authorities on slot 0, derived
from one `Observe` companion; the same batch in `Modify` fails (§60). -/
theorem observe_repeat_ok :
    (∃ L', ResolveManyStep K0 0 [⟨0, 0, 0⟩, ⟨0, 0, 0⟩] .observe w4 (.ok L') ∧ PReachI K0 hst L' ∧
      L'.res = [⟨0, 3, 4, .observe, [(5, 0, 0), (6, 0, 0)]⟩]) ∧
    ∀ o, ResolveManyStep K0 0 [⟨0, 0, 0⟩, ⟨0, 0, 0⟩] .modify w4 o → o = .fail := by
  have hok : ResolveManyStep K0 0 [⟨0, 0, 0⟩, ⟨0, 0, 0⟩] .observe w4 (.ok _) :=
    .ok (pl := pl4) rfl (by decide) (by decide) (by decide)
  exact ⟨⟨_, hok, .step w4_reach (Arena.KInvB.sound (by decide)).1 (.resolveMany hok), rfl⟩,
    (pool_resolveMany_distinct (L' := w4) (pl := pl4)).1 rfl (by decide) (by decide)⟩

/-- `freeSlot` is not a kernel `endUse` (HandlePool v0.4 annex, D.3: "Le contrôle n'interprète pas
`internal` comme un emprunt externe"; §69.2): on `w4`, `freeSlot(⟨0, 0, 0⟩)` is accepted, while the
kernel `endUse` of slot place 1 is rejected, because `internal` (authority 3, derived, active,
covering place 1) is held by the pool value outside the slot. Both states satisfy `KInv ∧ KAux`
(§57), decided through `Arena.KInvB`. -/
theorem freeSlot_not_endUse :
    (∃ L', FreeSlotStep K0 0 ⟨0, 0, 0⟩ w4 (.ok L') ∧ PReachI K0 hst L' ∧
      KInv L'.kern ∧ KAux L'.kern) ∧
      ¬ EndUsePre K0 w4.kern 1 ∧ KInv w4.kern ∧ KAux w4.kern := by
  have hok : FreeSlotStep K0 0 ⟨0, 0, 0⟩ w4 (.ok _) :=
    .ok (pl := pl4) (sl := ⟨1, 0, true⟩) rfl (by decide) (by decide) rfl (by decide)
  have hk4 : KInv w4.kern ∧ KAux w4.kern := Arena.KInvB.sound (by decide)
  exact ⟨⟨_, hok, .step w4_reach hk4.1 (.freeSlot hok), Arena.KInvB.sound (by decide)⟩, by decide,
    hk4⟩

/-- Contract problem (HandlePool v0.4 annex, D.3: "Le contenu du slot demeure `Uninit` jusqu'à son
écriture ; l'écriture du handle dans `dst` n'initialise pas le slot"): the preconditions of
`allocSlot` do not exclude a destination inside the allocated slot. On `w3`, `allocSlot(0, 1)` is
accepted on slot 0, whose place is 1: the slot becomes live and its content `Init` (§67). -/
theorem allocSlot_into_own_slot :
    ∃ L', AllocSlotStep 0 1 w3 (.ok L') ∧ PReachI K0 hst L' ∧
      L'.pools[0]? = some pl4 ∧ L'.kern.I 1 = .init := by
  have hok : AllocSlotStep 0 1 w3 (.ok (allocSlotEff w3 0 pl3 0 ⟨1, 0, false⟩ 1)) :=
    .ok rfl (by decide) rfl rfl
  exact ⟨_, hok, .step w3_reach (Arena.KInvB.sound (by decide)).1 (.allocSlot hok), rfl, by decide⟩

/-- Contract problem (HandlePool v0.4 annex, D.1: "Les entrées libres sont `Uninit`"): free
entries are not `Uninit` in every library-reachable state. On `w3`, a frame with `Modify` over the
pool value derives from `internal` over slot place 1 (O1, §60) and writes it (O10, §67): slot 0
stays free while its content is `Init`. -/
theorem free_slot_init :
    ∃ L, PReachI K0 hst L ∧ L.pools[0]? = some pl3 ∧ L.kern.I 1 = .init := by
  have h₁ : PStep K0 w3 { w3 with kern := deriveEff w3.kern 3 [1] .modify } :=
    .kernel (.derive (Guarded.ok (by decide)))
  have h₂ : PStep K0 { w3 with kern := deriveEff w3.kern 3 [1] .modify }
      { w3 with kern := write3Eff (deriveEff w3.kern 3 [1] .modify) [1] } :=
    .kernel (.write (a := 4) (Guarded.ok (by decide)))
  exact ⟨_, .step (.step w3_reach (Arena.KInvB.sound (by decide)).1 h₁)
    (Arena.KInvB.sound (by decide)).1 h₂, rfl, by decide⟩

end Witness

end Ern.Lib.HandlePool
