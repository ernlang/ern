import Ern.MemoryModel.Arena
import Ern.MemoryModel.Access.HolderCover

/-!
# Handle pool: a library instance of the access discipline (non-normative)

**Non-normative.** This module formalizes the library contract "HandlePool v0.5": the HandlePool
v0.4 annex (items D.1–D.4) with the items HP5-1 to HP5-7, HP5-1' and HP5-1'' of the
arbitrations Q3, Q4, Q5 and Q12.
`specs/ERN_Memory_Model_Specification_v0.1.md` does not define it (Part XIV preamble: "The
contracts of `HandlePool` and `DataStack` belong to their library abstractions and are not defined
here"). The normative clauses that constrain it are §36 (`MetaRight` is exercisable `Modify` on the
administering value; `writeShared` alone is insufficient; the library adds no rights to the
kernel), §37 and §89 (handles are data, not authorities; a stale identity or generation leads to
defined failure), §38 and §46 (library state outside `S₃`), §47 (empty initial registry), §56 (the
guard over all registries of live administrations), §58 (outcomes) and §76 (the obligations of
`newArena` that `newPool` takes over).

The pool registry lives beside the kernel state (`PState`). Its operations are built on the
kernel operations O1–O16 (§60–§75): `newPool` registers only; `allocSlot` writes the handle into
its destination (O10); `resolve` derives a companion from `internal` over the whole storage, then
an entry authority from the companion (O1 twice); `resolveMany` does the same with `split` (O2) in
`Modify` and with one `Observe` derive per handle (O1) in `Observe`; `unresolve` releases (O3);
`freeSlot` writes its metadata leaves, the leaves of the pool value (O10), then updates the
registry (HP5-1). Every library step is thus, on the kernel side, a finite sequence of accepted
kernel steps (`pstep_kernel`), so, under `DDSound` (§80) and `StaticsOK` (§47), every kernel state
of a library run is kernel-reachable and satisfies the invariant of §57 (`kernel_guarantee`, HP5-7).
-/

namespace Ern.Lib.HandlePool

open Ern.MemoryModel
open Ern.MemoryModel.Access

/-! ## Library state (HandlePool v0.5, D.1; §38, §46) -/

/-- Slot of a pool entry (HandlePool v0.5, D.1: `{place, gen : Nat, live : Bool}`; non-normative
library contract; §38, §46). -/
structure Slot where
  place : Nat
  gen : Nat
  live : Bool
deriving DecidableEq, Repr

/-- Pool entry `{storage, internal, slots}` with its logical identity (HandlePool v0.5, D.1;
non-normative library contract). The pool value is the place holding `internal` (§46 analogue). -/
structure Pool where
  id : Nat
  storage : Nat
  internal : Nat
  slots : List Slot
deriving DecidableEq, Repr

/-- Handle `(poolId, slot, gen)`: data, not an authority (HandlePool v0.5, D.1; §37, §89;
non-normative library contract). -/
structure Handle where
  id : Nat
  slot : Nat
  gen : Nat
deriving DecidableEq, Repr

/-- Ghost record of a resolution (HandlePool v0.5, D.2; auxiliary information creating no right,
§38): pool identity and `internal`, the companion, the mode, and the entry authorities tagged with
their slot and resolved generation. Read by `unresolve` and by the invariants. -/
structure Res where
  pool : Nat
  internal : Nat
  comp : Nat
  mode : Mode
  entries : List (Nat × Nat × Nat)
deriving DecidableEq, Repr

/-- Library state (§38, §46; HandlePool v0.5, D.1; non-normative library contract): the kernel
state `S₃` and, separately, the pool registry, the next fresh pool identity and the ghost
resolutions. -/
structure PState where
  kern : S3
  pools : List Pool
  nId : Nat
  res : List Res

/-- Initial library state (§47; HandlePool v0.5, D.1): the initial kernel state, an empty
registry. -/
def PState.init (statics : Statics) : PState := ⟨S3.init statics, [], 0, []⟩

/-- The pool read as an arena entry with nothing available or issued, to reuse `MetaRight` of §36
(HandlePool v0.5, D.3; non-normative library contract). -/
def Pool.entry (pl : Pool) : Arena.ArenaEntry := ⟨pl.storage, pl.internal, [], []⟩

/-- Administration right on the pool (§36; HandlePool v0.5, D.3 corrected by §36, HP5-1;
non-normative library contract): the pool is live (`internal` active) and `MetaRight` holds,
exercisable `Modify` over the pool value; no `writeShared` branch. -/
def AdminRight (s : S3) (pl : Pool) : Prop := s.Active pl.internal ∧ Arena.MetaRight s pl.entry

/-- Decidability of `AdminRight` (§36; HandlePool v0.5, D.3). -/
instance (s : S3) (pl : Pool) : Decidable (AdminRight s pl) := by
  unfold AdminRight; infer_instance

/-- Place of slot `i`, `0` if absent (HandlePool v0.5, D.1; non-normative library contract;
§46). -/
def slotPlace (pl : Pool) (i : Nat) : Nat := ((pl.slots[i]?).map (·.place)).getD 0

/-- The pool with slot `i` replaced (HandlePool v0.5, D.3; non-normative library contract;
§46). -/
def setSlot (pl : Pool) (i : Nat) (sl : Slot) : Pool := { pl with slots := pl.slots.set i sl }

/-! ## `newPool` (HandlePool v0.5, D.1; §56, §76) -/

/-- The pool registry as a registry of live administrations (§56; HandlePool v0.5, D.1;
non-normative library contract): the `internal` identities of its live pools. -/
def liveInternals (s : S3) (pools : List Pool) : List Nat :=
  (pools.filter fun pl => decide (s.Active pl.internal)).map (·.internal)

/-- Preconditions of `newPool(storage, internal)` (HandlePool v0.5, D.1; non-normative library
contract; §56, §76). -/
structure NewPoolPre (s : S3) (pools : List Pool) (others : List (List Nat))
    (storage internal : Nat) : Prop where
  /-- HandlePool v0.5, D.1: "reprend les autres obligations applicables de `newArena`"
  (§76.1–§76.3, §76.5, §76.6, read on the resulting state as v0.1 §76.6 states it). -/
  base : Arena.NewArenaBase s storage internal
  /-- HandlePool v0.5, D.1: every leaf of the input storage is `Uninit`. -/
  uninit : ∀ l ∈ footprint s.P storage, s.I l = .uninit
  /-- HandlePool v0.5, D.1, §56: `internal` is absent from the pool registry and from every other
  registry of live administrations `others`. -/
  guard : Arena.Guard56 (liveInternals s pools :: others) internal

/-- Decidability of `NewPoolPre` (HandlePool v0.5, D.1; §56, §76). -/
instance (s : S3) (pools : List Pool) (others : List (List Nat)) (storage internal : Nat) :
    Decidable (NewPoolPre s pools others storage internal) :=
  decidable_of_iff (Arena.NewArenaBase s storage internal ∧
    (∀ l ∈ footprint s.P storage, s.I l = .uninit) ∧
    Arena.Guard56 (liveInternals s pools :: others) internal)
    ⟨fun ⟨a, b, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨a, b, c⟩⟩

/-- Effect of `newPool` (HandlePool v0.5, D.1; non-normative library contract): a pool with the
fresh identity `nId`, one free slot of generation zero per child of the storage, the kernel state
unchanged (§46, §76). -/
def newPoolEff (L : PState) (storage internal : Nat) : PState :=
  { L with
    pools := L.pools ++ [⟨L.nId, storage, internal,
      (kids L.kern.P storage).map fun q => ⟨q, 0, false⟩⟩]
    nId := L.nId + 1 }

/-- `newPool` as a relation (HandlePool v0.5, D.1; §58; non-normative library contract): `ok` or
`reject`; `others` are the other registries of live administrations (§56). -/
def NewPoolStep (others : List (List Nat)) (storage internal : Nat) (L : PState) :
    Outcome3 PState → Prop :=
  Guarded (NewPoolPre L.kern L.pools others storage internal) (newPoolEff L storage internal)

/-! ## `allocSlot` (HandlePool v0.5, D.3) -/

/-- Static preconditions of `allocSlot(pool, dst)` (HandlePool v0.5, D.3 corrected by §36;
non-normative library contract). "Apte à recevoir la représentation d'un handle" names no state
component and is not represented. -/
structure AllocSlotStatic (s : S3) (pl : Pool) (dst : Nat) : Prop where
  /-- HandlePool v0.5, D.3, §36: live pool and `MetaRight`. -/
  right : AdminRight s pl
  /-- HandlePool v0.5, D.3: `dst` is usable. -/
  dstUsable : s.Usable dst
  /-- HandlePool v0.5, D.3: `dst` is a leaf (the handle is written into "la seule feuille
  `dst`"). -/
  dstLeaf : isLeaf s.P dst
  /-- HandlePool v0.5, D.3 with §67.1: the write of the handle needs exercisable `Modify` over
  `dst`. -/
  dstRight : HasRight s .modify dst
  /-- HandlePool v0.5, D.3: `dst` is not `Init`. -/
  dstNotInit : s.I dst ≠ .init
  /-- HandlePool v0.5, D.3: `dst` holds no active authority. -/
  dstFree : ∀ j ∈ List.range s.A.length,
    OptP (s.A[j]?) (fun z => z.active = true → z.holder ≠ .place dst) True

/-- Decidability of `AllocSlotStatic` (HandlePool v0.5, D.3; §36, §67). -/
instance (s : S3) (pl : Pool) (dst : Nat) : Decidable (AllocSlotStatic s pl dst) :=
  decidable_of_iff (AdminRight s pl ∧ s.Usable dst ∧ isLeaf s.P dst ∧ HasRight s .modify dst ∧
    s.I dst ≠ .init ∧ ∀ j ∈ List.range s.A.length,
      OptP (s.A[j]?) (fun z => z.active = true → z.holder ≠ .place dst) True)
    ⟨fun ⟨a, b, c, d, e, f⟩ => ⟨a, b, c, d, e, f⟩, fun ⟨a, b, c, d, e, f⟩ => ⟨a, b, c, d, e, f⟩⟩

/-- Effect of `allocSlot` on slot `i` of pool `j` (HandlePool v0.5, D.3; non-normative library
contract): the slot becomes live with its generation kept; the handle is written into the leaf
`dst`, which alone becomes `Init` (§67 effect). -/
def allocSlotEff (L : PState) (j : Nat) (pl : Pool) (i : Nat) (sl : Slot) (dst : Nat) : PState :=
  { L with
    kern := write3Eff L.kern [dst]
    pools := L.pools.set j (setSlot pl i { sl with live := true }) }

/-- The handle written by `allocSlot` for slot `i` (HandlePool v0.5, D.3; non-normative library
contract; §37, §89). -/
def slotHandle (pl : Pool) (i : Nat) : Option Handle :=
  (pl.slots[i]?).map fun sl => ⟨pl.id, i, sl.gen⟩

/-- `allocSlot(pool j, dst)` as a relation (HandlePool v0.5, D.3; §58; non-normative library
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

/-! ## `resolve`, `resolveMany` (HandlePool v0.5, D.2, HP5-5, HP5-6) -/

/-- Validity of a handle for pool `pl` (HandlePool v0.5, D.2, D.3, HP5-5, HP5-6, HP5-1''; §89;
non-normative library contract): the pool is live (`internal` active, §46 analogue: a handle of a
dead pool is stale, HP5-5), the handle names the pool, and it designates a live slot at its
generation (a handle of a free entry is stale, HP5-6); a slot index outside the pool designates
nothing. -/
def HandleOK (s : S3) (pl : Pool) (h : Handle) : Prop :=
  s.Active pl.internal ∧ h.id = pl.id ∧
    OptP (pl.slots[h.slot]?) (fun sl => sl.gen = h.gen ∧ sl.live = true) False

/-- Decidability of `HandleOK` (HandlePool v0.5, D.2; §89). -/
instance (s : S3) (pl : Pool) (h : Handle) : Decidable (HandleOK s pl h) := by
  unfold HandleOK; infer_instance

/-- Legal exercise of `internal` at mode `m` for the companion (HandlePool v0.5, D.2;
non-normative library contract): the preconditions of the `derive` of the companion from
`internal` over all leaves of the storage (§60). -/
def ResolveRight (s : S3) (pl : Pool) (m : Mode) : Prop :=
  DerivePre s pl.internal (footprint s.P pl.storage) m

/-- Decidability of `ResolveRight` (HandlePool v0.5, D.2; §60). -/
instance (s : S3) (pl : Pool) (m : Mode) : Decidable (ResolveRight s pl m) := by
  unfold ResolveRight; infer_instance

/-- State after the companion (HandlePool v0.5, D.2; §60 effect; non-normative library contract):
authority `|A|`, derived from `internal` at mode `m` over all leaves of the storage. -/
def compS (s : S3) (pl : Pool) (m : Mode) : S3 :=
  deriveEff s pl.internal (footprint s.P pl.storage) m

/-- Observe derivations from `c`, one per region in order (HandlePool v0.5, D.2: `resolveMany` in
`Observe`; §60; non-normative library contract): each accepted in the state left by the previous
ones. -/
def DerivesPre (s : S3) (c : Nat) : List (List Nat) → Prop
  | [] => True
  | r :: rs => DerivePre s c r .observe ∧ DerivesPre (deriveEff s c r .observe) c rs

/-- Decidability of `DerivesPre` (HandlePool v0.5, D.2, §60). -/
instance decDerivesPre (s : S3) (c : Nat) :
    (rs : List (List Nat)) → Decidable (DerivesPre s c rs)
  | [] => isTrue trivial
  | r :: rs =>
    have := decDerivesPre (deriveEff s c r .observe) c rs
    inferInstanceAs (Decidable (_ ∧ _))

/-- Effect of the `Observe` derivations from `c`, in order (HandlePool v0.5, D.2; §60 effect). -/
def derivesEff (s : S3) (c : Nat) : List (List Nat) → S3
  | [] => s
  | r :: rs => derivesEff (deriveEff s c r .observe) c rs

/-- Entry authorities of a batch from the companion `c` (HandlePool v0.5, D.2; non-normative
library contract): `split` (§61) in `Modify`, successive `Observe` derivations (§60) in
`Observe`. -/
def EntriesPre (k : K) : Mode → S3 → Nat → List (List Nat) → Prop
  | .modify, s, c, rs => SplitPre k s c rs
  | .observe, s, c, rs => DerivesPre s c rs

/-- Decidability of `EntriesPre` (HandlePool v0.5, D.2; §60, §61). -/
instance (k : K) [∀ r r', Decidable (k.DeclaredDisjoint r r')] (m : Mode) (s : S3) (c : Nat)
    (rs : List (List Nat)) : Decidable (EntriesPre k m s c rs) := by
  cases m <;> unfold EntriesPre <;> infer_instance

/-- Effect of the entry authorities of a batch (HandlePool v0.5, D.2; §60, §61 effects). -/
def entriesEff : Mode → S3 → Nat → List (List Nat) → S3
  | .modify, s, c, rs => splitEff s c rs
  | .observe, s, c, rs => derivesEff s c rs

/-- Regions of the entries designated by a batch: the footprint of each slot (HandlePool v0.5,
D.2; non-normative library contract; §60). -/
def entryRegions (s : S3) (pl : Pool) (hs : List Handle) : List (List Nat) :=
  hs.map fun h => footprint s.P (slotPlace pl h.slot)

/-- Ghost entries of a batch: the `n`-th entry authority is `c + 1 + n`, for slot and generation of
the `n`-th handle (HandlePool v0.5, D.2; auxiliary, §38). -/
def batchEntries (c : Nat) (hs : List Handle) : List (Nat × Nat × Nat) :=
  mapI (fun i h => (i, h.slot, h.gen)) (c + 1) hs

/-- `resolve(h, m)` on pool `j` as a relation (HandlePool v0.5, D.2, HP5-5, HP5-6; §58, §89;
non-normative library contract): `reject` without the pool; then `fail` for a handle of a dead
pool, of another pool, stale, absent or free, before the right is checked (HP5-5); then `reject`
without the legal exercise of `internal`; then the companion and the entry authority derived from
it, `reject` when the second derivation is not accepted. -/
inductive ResolveStep (j : Nat) (h : Handle) (m : Mode) (L : PState) : Outcome3 PState → Prop where
  | noPool : L.pools[j]? = none → ResolveStep j h m L .reject
  | fail {pl : Pool} : L.pools[j]? = some pl → ¬ HandleOK L.kern pl h →
      ResolveStep j h m L .fail
  | noRight {pl : Pool} : L.pools[j]? = some pl → HandleOK L.kern pl h →
      ¬ ResolveRight L.kern pl m → ResolveStep j h m L .reject
  | noEntry {pl : Pool} {sl : Slot} : L.pools[j]? = some pl → HandleOK L.kern pl h →
      ResolveRight L.kern pl m → pl.slots[h.slot]? = some sl →
      ¬ DerivePre (compS L.kern pl m) L.kern.A.length (footprint L.kern.P sl.place) m →
      ResolveStep j h m L .reject
  | ok {pl : Pool} {sl : Slot} : L.pools[j]? = some pl → HandleOK L.kern pl h →
      ResolveRight L.kern pl m → pl.slots[h.slot]? = some sl →
      DerivePre (compS L.kern pl m) L.kern.A.length (footprint L.kern.P sl.place) m →
      ResolveStep j h m L (.ok { L with
        kern := deriveEff (compS L.kern pl m) L.kern.A.length (footprint L.kern.P sl.place) m
        res := L.res ++ [⟨pl.id, pl.internal, L.kern.A.length, m,
          [(L.kern.A.length + 1, h.slot, h.gen)]⟩] })

/-- Validity of a batch (HandlePool v0.5, D.2, HP5-5; non-normative library contract): every
handle is valid (`HandleOK`); pairwise distinct slots in `Modify` only (§58, §89). -/
def BatchOK (s : S3) (pl : Pool) (hs : List Handle) (m : Mode) : Prop :=
  (∀ h ∈ hs, HandleOK s pl h) ∧ (m = .modify → (hs.map (·.slot)).Nodup)

/-- Decidability of `BatchOK` (HandlePool v0.5, D.2; §58, §89). -/
instance (s : S3) (pl : Pool) (hs : List Handle) (m : Mode) : Decidable (BatchOK s pl hs m) := by
  unfold BatchOK; infer_instance

/-- `resolveMany(hs, m)` on pool `j` as a relation (HandlePool v0.5, D.2, HP5-5; §58;
non-normative library contract): `reject` without the pool; then an atomic `fail` for an invalid
batch, before the right is checked (HP5-5); then `reject` without the legal exercise of
`internal`; then one companion and the entry authorities (`EntriesPre`), `reject` when they are
not accepted. -/
inductive ResolveManyStep (k : K) (j : Nat) (hs : List Handle) (m : Mode) (L : PState) :
    Outcome3 PState → Prop where
  | noPool : L.pools[j]? = none → ResolveManyStep k j hs m L .reject
  | fail {pl : Pool} : L.pools[j]? = some pl → ¬ BatchOK L.kern pl hs m →
      ResolveManyStep k j hs m L .fail
  | noRight {pl : Pool} : L.pools[j]? = some pl → BatchOK L.kern pl hs m →
      ¬ ResolveRight L.kern pl m → ResolveManyStep k j hs m L .reject
  | noEntries {pl : Pool} : L.pools[j]? = some pl → BatchOK L.kern pl hs m →
      ResolveRight L.kern pl m →
      ¬ EntriesPre k m (compS L.kern pl m) L.kern.A.length (entryRegions L.kern pl hs) →
      ResolveManyStep k j hs m L .reject
  | ok {pl : Pool} : L.pools[j]? = some pl → BatchOK L.kern pl hs m → ResolveRight L.kern pl m →
      EntriesPre k m (compS L.kern pl m) L.kern.A.length (entryRegions L.kern pl hs) →
      ResolveManyStep k j hs m L (.ok { L with
        kern := entriesEff m (compS L.kern pl m) L.kern.A.length (entryRegions L.kern pl hs)
        res := L.res ++ [⟨pl.id, pl.internal, L.kern.A.length, m,
          batchEntries L.kern.A.length hs⟩] })

/-! ## `unresolve` (HandlePool v0.5, D.2) -/

/-- Releases the authorities of a list in order (§62); `none` as soon as one release is not
accepted (HandlePool v0.5, D.2: "Les règles de `release` … restent applicables"). -/
def releaseAll : S3 → List Nat → Option S3
  | s, [] => some s
  | s, a :: l => if ReleasePre s a then releaseAll (releaseEff s a) l else none

/-- The resolution of companion `c` (HandlePool v0.5, D.2; ghost lookup, §38). -/
def findRes (L : PState) (c : Nat) : Option Res := L.res.find? fun r => r.comp == c

/-- Authorities released by `unresolve` of `r` (HandlePool v0.5, D.2; non-normative library
contract): the entry authorities still active, then the companion (§62). -/
def unresolveList (s : S3) (r : Res) : List Nat :=
  ((r.entries.map (·.1)).filter fun a => decide (s.Active a)) ++ [r.comp]

/-- `unresolve(c)` as a relation (HandlePool v0.5, D.2; §58; non-normative library contract): the
releases of `unresolveList`; `reject` when one is not accepted or `c` is no companion. -/
inductive UnresolveStep (c : Nat) (L : PState) : Outcome3 PState → Prop where
  | none : findRes L c = none → UnresolveStep c L .reject
  | reject {r : Res} : findRes L c = some r → releaseAll L.kern (unresolveList L.kern r) = none →
      UnresolveStep c L .reject
  | ok {r : Res} {s' : S3} : findRes L c = some r →
      releaseAll L.kern (unresolveList L.kern r) = some s' →
      UnresolveStep c L (.ok { L with kern := s' })

/-! ## `freeSlot` (HandlePool v0.5, D.3 as amended by HP5-1, HP5-1', HP5-1'') -/

/-- No active strict descendant of the `internal` of pool `pl` covers a leaf of place `q`
(HandlePool v0.5, HP5-1 as amended by HP5-1': "aucune autorité active, descendante stricte de
internal de ce pool, ne couvre l'entrée"; §42: descendants along the current origin chain, which
covers the reanchoring of §73.4 onto `internal`; non-normative library contract). -/
def NoInternalDesc (s : S3) (pl : Pool) (q : Nat) : Prop :=
  ∀ x ∈ List.range s.A.length, s.Active x → pl.internal ∈ s.ancs x →
    ∀ l ∈ s.afp x, l ∉ footprint s.P q

/-- Decidability of `NoInternalDesc` (HandlePool v0.5, HP5-1'; §42). -/
instance (s : S3) (pl : Pool) (q : Nat) : Decidable (NoInternalDesc s pl q) := by
  unfold NoInternalDesc; infer_instance

/-- Content conditions of `freeSlot` on slot place `q` of pool `pl` (HandlePool v0.5, HP5-1,
HP5-1'; non-normative library contract; §41, §42). -/
structure FreeContentOK (L : PState) (pl : Pool) (q : Nat) : Prop where
  /-- HandlePool v0.5, HP5-1: no leaf of the entry is `Init`; each is `Uninit` or `Moved`
  (§41). -/
  notInit : ∀ l ∈ footprint L.kern.P q, L.kern.I l ≠ .init
  /-- HandlePool v0.5, HP5-1': no active strict descendant of `internal` of this pool covers a
  leaf of the entry (§42). -/
  noDesc : NoInternalDesc L.kern pl q

/-- Decidability of `FreeContentOK` (HandlePool v0.5, HP5-1, HP5-1'; §41, §42). -/
instance (L : PState) (pl : Pool) (q : Nat) : Decidable (FreeContentOK L pl q) :=
  decidable_of_iff ((∀ l ∈ footprint L.kern.P q, L.kern.I l ≠ .init) ∧ NoInternalDesc L.kern pl q)
    ⟨fun ⟨a, b⟩ => ⟨a, b⟩, fun ⟨a, b⟩ => ⟨a, b⟩⟩

/-- Metadata leaves of pool `pl` (HandlePool v0.5, HP5-1; non-normative library contract; §46
analogue, §36): the leaves (§40) of the pool value, the place holding `internal`
(`Arena.arenaValue`); empty when `internal` is absent or held by a frame, a case `AdminRight`
excludes. Taking all the leaves of the pool value is the reading of this formalization, on the basis
of §36 (`MetaRight` is exercisable `Modify` on the administering value) and HP5-3 (the write of the
pool value). -/
def metaLeaves (s : S3) (pl : Pool) : List Nat :=
  match Arena.arenaValue s pl.entry with
  | some v => footprint s.P v
  | none => []

/-- The metadata leaves are the leaves of the pool value (HandlePool v0.5, HP5-1; §46 analogue,
§40). -/
theorem metaLeaves_of {s : S3} {pl : Pool} {v : Nat} (h : Arena.arenaValue s pl.entry = some v) :
    metaLeaves s pl = footprint s.P v := by
  unfold metaLeaves; rw [h]

/-- Effect of `freeSlot` on slot `i` of pool `j` (HandlePool v0.5, HP5-1; non-normative library
contract): the kernel write of the metadata leaves (§67 effect: they become `Init`), then the
abstract update: the slot becomes free and its generation is incremented. There is no end-of-use
effect, and the library adds no rights to the kernel (§36). -/
def freeSlotEff (L : PState) (j : Nat) (pl : Pool) (i : Nat) (sl : Slot) : PState :=
  { L with
    kern := write3Eff L.kern (metaLeaves L.kern pl)
    pools := L.pools.set j (setSlot pl i ⟨sl.place, sl.gen + 1, false⟩) }

/-- `freeSlot(h)` on pool `j` as a relation (HandlePool v0.5, D.3 corrected by §36, HP5-1; outcome
order of HP5-1'' (Q5 extended to `freeSlot`); §58, §89; non-normative library contract): `reject`
without the pool; then `fail` for a handle of a dead pool, of another pool, stale, absent or free,
before the right is checked; then `reject` without the administration right (live pool and
`MetaRight`); then `reject` unless the content conditions hold (`FreeContentOK`); then `ok`, whose
effect is `freeSlotEff` (the write of the metadata leaves). As for `allocSlot`, the preconditions of
that kernel write (§67) are not fields of the step: they follow from `AdminRight` under `KInv`
(`meta_write_of_kinv`). -/
inductive FreeSlotStep (j : Nat) (h : Handle) (L : PState) : Outcome3 PState → Prop where
  | noPool : L.pools[j]? = none → FreeSlotStep j h L .reject
  | fail {pl : Pool} : L.pools[j]? = some pl → ¬ HandleOK L.kern pl h → FreeSlotStep j h L .fail
  | noRight {pl : Pool} : L.pools[j]? = some pl → HandleOK L.kern pl h → ¬ AdminRight L.kern pl →
      FreeSlotStep j h L .reject
  | noContent {pl : Pool} {sl : Slot} : L.pools[j]? = some pl → HandleOK L.kern pl h →
      AdminRight L.kern pl → pl.slots[h.slot]? = some sl → ¬ FreeContentOK L pl sl.place →
      FreeSlotStep j h L .reject
  | ok {pl : Pool} {sl : Slot} : L.pools[j]? = some pl → HandleOK L.kern pl h →
      AdminRight L.kern pl → pl.slots[h.slot]? = some sl → FreeContentOK L pl sl.place →
      FreeSlotStep j h L (.ok (freeSlotEff L j pl h.slot sl))

/-! ## Library runs (HandlePool v0.5; §38, §46, §47) -/

/-- One `ok` step of a library run (HandlePool v0.5; non-normative library contract): a kernel
step O1–O16 of non-administrative code, the registry unchanged, or an accepted pool operation
(§58). -/
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
  | freeSlot {L L' : PState} {j : Nat} {h : Handle} : FreeSlotStep j h L (.ok L') →
      PStep k L L'

/-- Library states reachable from the initial library state (§47) by library steps
(HandlePool v0.5; non-normative library contract). -/
inductive PReach (k : K) (statics : Statics) : PState → Prop where
  | init : PReach k statics (PState.init statics)
  | step {L L' : PState} : PReach k statics L → PStep k L L' → PReach k statics L'

/-! ## Kernel side of the pool operations (§57, §58; HandlePool v0.5, HP5-7) -/

/-- Finite sequences of kernel steps O1–O16 (§57, §58; HandlePool v0.5, HP5-7). -/
inductive KSeq (k : K) : S3 → S3 → Prop where
  | refl (s : S3) : KSeq k s s
  | tail {s s₁ s₂ : S3} : KSeq k s s₁ → KStep k s₁ s₂ → KSeq k s s₂

/-- Sequences of kernel steps compose (§57; HandlePool v0.5, HP5-7). -/
theorem KSeq.trans {k : K} {s₁ s₂ s₃ : S3} (h₁ : KSeq k s₁ s₂) (h₂ : KSeq k s₂ s₃) :
    KSeq k s₁ s₃ := by
  induction h₂ with
  | refl => exact h₁
  | tail _ hs ih => exact .tail ih hs

/-- One kernel step is a sequence (§57; HandlePool v0.5, HP5-7). -/
theorem KSeq.single {k : K} {s s' : S3} (h : KStep k s s') : KSeq k s s' := .tail (.refl s) h

/-- Kernel reachability (§57) is closed under sequences of kernel steps (HandlePool v0.5,
HP5-7). -/
theorem KSeq.reachable {k : K} {statics : Statics} {s s' : S3} (hr : Reachable k statics s)
    (h : KSeq k s s') : Reachable k statics s' := by
  induction h with
  | refl => exact hr
  | tail _ hs ih => exact .step ih hs

/-- `releaseAll` is a sequence of `release` steps (§62; HandlePool v0.5, D.2). -/
theorem releaseAll_kseq {k : K} : ∀ {s s' : S3} {l : List Nat}, releaseAll s l = some s' →
    KSeq k s s'
  | s, s', [], h => by simp only [releaseAll, Option.some.injEq] at h; subst h; exact .refl s
  | s, s', a :: l, h => by
    simp only [releaseAll] at h
    split at h
    · rename_i hpre
      exact (KSeq.single (.release (Guarded.ok hpre))).trans (releaseAll_kseq h)
    · cases h

/-- The `Observe` derivations of `resolveMany` are a sequence of `derive` steps (§60;
HandlePool v0.5, D.2). -/
theorem derives_kseq {k : K} {c : Nat} : ∀ {s : S3} {rs : List (List Nat)}, DerivesPre s c rs →
    KSeq k s (derivesEff s c rs)
  | s, [], _ => .refl s
  | _, _ :: _, ⟨h₁, h₂⟩ => (KSeq.single (.derive (Guarded.ok h₁))).trans (derives_kseq h₂)

/-- The entry authorities of `resolveMany` are a `split` (§61) or a sequence of `derive` steps
(§60) (HandlePool v0.5, D.2). -/
theorem entries_kseq {k : K} {m : Mode} {s : S3} {c : Nat} {rs : List (List Nat)}
    (h : EntriesPre k m s c rs) : KSeq k s (entriesEff m s c rs) := by
  cases m with
  | modify => exact KSeq.single (.split (Guarded.ok h))
  | observe => exact derives_kseq h

/-- Under `KInv` (§57), an authority `a` exercisable in `Modify` with effective `Modify` over every
leaf of a usable place `q` satisfies the preconditions of an ordinary write (§67) of any leaves of
`q` (HandlePool v0.5, D.3: the write of the handle; HP5-3: the write of the pool value). -/
theorem write_of_right {s : S3} (hk : KInv s) {q a : Nat} {ls : List Nat} (hu : s.Usable q)
    (hex : s.ExercisableAt a .modify)
    (hall : ∀ l ∈ footprint s.P q, Allows (effective s a l) .modify)
    (hls : ∀ l ∈ ls, l ∈ footprint s.P q) : Write3Pre s a ls := by
  refine ⟨fun l hl => ⟨q, List.mem_range.2 hu.lt, hu, hls l hl⟩, hex,
    fun l hl => Arena.allows_modify_iff.1 (hall l (hls l hl)),
    fun l hl b _ hb => effective_exclusive hk.2.1.1.1 (Ne.symm hb)
      (Arena.allows_modify_iff.1 (hall l (hls l hl))), fun l hl => ?_⟩
  obtain ⟨-, -, hlq⟩ := mem_footprint.1 (hls l hl)
  have hul : s.Usable l := usable_of_partOf hk.1 (l + 1) l q (Nat.lt_succ_self l) hlq hu
  exact fun q' _ hq' x hx => hk.2.1.1.2.2.1 q' (usable_of_part hk.1 hq' hul) x hx

/-- The metadata write of `freeSlot` under `KInv` (§57) (HandlePool v0.5, HP5-1; §36, §43, §67): for
a pool with `AdminRight`, `internal` is held by the pool value `v`, the metadata leaves are the
leaves of `v`, an authority `a` grounds `MetaRight` (`Grounds`: exercisable `Modify` with effective
`Modify` over every leaf of `v`), and the ordinary write of the metadata leaves through `a`
satisfies the preconditions of §67. -/
theorem meta_write_of_kinv {s : S3} (hk : KInv s) {pl : Pool} (hR : AdminRight s pl) :
    ∃ v a, Arena.arenaValue s pl.entry = some v ∧ metaLeaves s pl = footprint s.P v ∧
      Grounds s .modify v a ∧ Write3Pre s a (metaLeaves s pl) := by
  obtain ⟨⟨y, hy, ya⟩, hm⟩ := hR
  unfold Arena.MetaRight at hm
  cases hv : Arena.arenaValue s pl.entry with
  | none => rw [hv] at hm; exact (hm : False).elim
  | some v =>
    rw [hv] at hm
    obtain ⟨a, ha, hex, hall⟩ : HasRight s .modify v := hm
    have hhold : y.holder = .place v := by
      simp only [Arena.arenaValue, Pool.entry, hy] at hv
      revert hv; cases y.holder <;> simp
    have hu : s.Usable v := by
      have := hk.1.holders _ y hy ya; rw [hhold] at this; exact this
    have hml := metaLeaves_of hv
    exact ⟨v, a, rfl, hml, ⟨ha, hex, hall⟩,
      hml ▸ write_of_right hk hu hex hall fun _ h => h⟩

/-- What a pool step is on the kernel side (HandlePool v0.5, HP5-7; §57, §58): under `KInv`, every
library step is a finite sequence of accepted kernel steps O1–O16: `newPool` none (the identity),
`allocSlot` one `write` (§67) of the handle, `freeSlot` one `write` (§67) of the metadata leaves
through the authority on which `MetaRight` rests (HP5-1), `resolve` two `derive` (§60),
`resolveMany` one `derive` then one `split` (§61) or one `derive` per handle, `unresolve` `release`
steps (§62). -/
theorem pstep_kernel {k : K} {L L' : PState} (hk : KInv L.kern) (h : PStep k L L') :
    KSeq k L.kern L'.kern := by
  cases h with
  | kernel hs => exact KSeq.single hs
  | newPool hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact .refl _
  | allocSlot hs =>
    cases hs with
    | ok _ hst _ _ =>
      obtain ⟨a, -, hex, hall⟩ := hst.dstRight
      exact KSeq.single (.write (a := a) (Guarded.ok (write_of_right hk hst.dstUsable hex hall
        fun l hl => by
          rw [List.mem_singleton.1 hl]
          exact mem_footprint.2 ⟨hst.dstUsable.lt, hst.dstLeaf, hst.dstUsable.lt, .inl rfl⟩)))
  | resolve hs =>
    cases hs with
    | ok _ _ hR _ hE =>
      exact (KSeq.single (.derive (Guarded.ok hR))).tail (.derive (Guarded.ok hE))
  | resolveMany hs =>
    cases hs with
    | ok _ _ hR hE => exact (KSeq.single (.derive (Guarded.ok hR))).trans (entries_kseq hE)
  | unresolve hs =>
    cases hs with
    | ok _ hr => exact releaseAll_kseq hr
  | freeSlot hs =>
    cases hs with
    | ok _ _ hR _ _ =>
      obtain ⟨-, a, -, -, -, hw⟩ := meta_write_of_kinv hk hR
      exact KSeq.single (.write (a := a) (Guarded.ok hw))

/-- The kernel state of every library-reachable state is reachable from `S3.init statics` by
kernel steps O1–O16 (§57; HandlePool v0.5, HP5-7), under `DDSound` (§80) and `StaticsOK` (§47),
which give `KInv` on the kernel side of the run (`Access.reachable_kinv`). -/
theorem pReach_reachable {k : K} {statics : Statics} (hdd : DDSound k) (hst : StaticsOK statics)
    {L : PState} (h : PReach k statics L) : Reachable k statics L.kern := by
  induction h with
  | init => exact .init
  | step _ hs ih => exact (pstep_kernel (reachable_kinv hdd hst ih) hs).reachable ih

/-- The guarantee of §57 on the kernel side of library runs (HandlePool v0.5, HP5-7, O5.g;
non-normative library contract): every kernel state of a library-reachable state satisfies
`KInv`. -/
def KernelGuarantee (k : K) (statics : Statics) : Prop := ∀ L, PReach k statics L → KInv L.kern

/-- `KernelGuarantee` holds under `DDSound` (§80) and `StaticsOK` (§47) (HandlePool v0.5, HP5-7;
§57): the kernel state of a library-reachable state is kernel-reachable (`pReach_reachable`). -/
theorem kernel_guarantee {k : K} {statics : Statics} (hdd : DDSound k) (hst : StaticsOK statics) :
    KernelGuarantee k statics :=
  fun _ h => reachable_kinv hdd hst (pReach_reachable hdd hst h)

/-! ## Helper lemmas (lists, chains, effects) -/

/-- An optional value satisfying a predicate with default `False` exists (§38; HandlePool v0.5). -/
theorem optP_false_iff {α : Type} {o : Option α} {P : α → Prop} :
    OptP o P False ↔ ∃ y, o = some y ∧ P y := by
  cases o with
  | none => simp [OptP]
  | some y => simp [OptP]

/-- The replaced element belongs to the list (HandlePool v0.5, D.3: pool updates; §46). -/
theorem mem_set_self' {α : Type} : ∀ {l : List α} {i : Nat} {a x : α}, l[i]? = some a →
    x ∈ l.set i x
  | [], _, _, _, h => by simp at h
  | _ :: _, 0, _, _, _ => by simp
  | _ :: l, i + 1, a, x, h => by
    simp only [List.getElem?_cons_succ] at h
    simp only [List.set_cons_succ, List.mem_cons]; exact .inr (mem_set_self' h)

/-- Reading the replaced index (HandlePool v0.5, D.3; §46). -/
theorem getElem?_set_eq' {α : Type} : ∀ {l : List α} {i : Nat} {a x : α}, l[i]? = some a →
    (l.set i x)[i]? = some x
  | [], _, _, _, h => by simp at h
  | _ :: _, 0, _, _, _ => by simp
  | _ :: l, i + 1, a, x, h => by
    simp only [List.getElem?_cons_succ] at h
    simp only [List.set_cons_succ, List.getElem?_cons_succ]; exact getElem?_set_eq' h

/-- Reading another index (HandlePool v0.5, D.3; §46). -/
theorem getElem?_set_ne' {α : Type} : ∀ {l : List α} {i n : Nat} {x : α}, n ≠ i →
    (l.set i x)[n]? = l[n]?
  | [], _, _, _, _ => by simp
  | _ :: _, 0, 0, _, h => absurd rfl h
  | _ :: _, 0, _ + 1, _, _ => by simp
  | _ :: _, _ + 1, 0, _, _ => by simp
  | _ :: l, i + 1, n + 1, x, h => by
    simp only [List.set_cons_succ, List.getElem?_cons_succ]
    exact getElem?_set_ne' (l := l) (fun e => h (by rw [e]))

/-- Replacing an element by one with the same image keeps the image of the list
(HandlePool v0.5, D.3; §46). -/
theorem map_set_same {α β : Type} (f : α → β) : ∀ {l : List α} {i : Nat} {a x : α},
    l[i]? = some a → f x = f a → (l.set i x).map f = l.map f
  | [], _, _, _, h, _ => by simp at h
  | b :: l, 0, a, x, h, hf => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h
    simp [hf]
  | b :: l, i + 1, a, x, h, hf => by
    simp only [List.getElem?_cons_succ] at h
    simp only [List.set_cons_succ, List.map_cons, map_set_same f h hf]

/-- Two parts containing a common leaf are related by the parent chain (§40; HandlePool v0.5). -/
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

/-- Two distinct children of a place have disjoint footprints under `WF3` (§40, §49.2;
HandlePool v0.5, D.1: slots are pairwise disjoint). -/
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

/-- `List.range` is strictly increasing (HandlePool v0.5, D.1: slot indices; §40). -/
theorem range_pairwise_lt : ∀ n, (List.range n).Pairwise (· < ·)
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.pairwise_append]
    exact ⟨range_pairwise_lt n, by simp, fun a ha b hb => by
      rw [List.mem_singleton.1 hb]; exact List.mem_range.1 ha⟩

/-- In a strictly increasing list, an element has one index (HandlePool v0.5, D.1; §40). -/
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
frame (§60 effect; HandlePool v0.5, D.2). -/
theorem derivesEff_eq (c : Nat) : ∀ (s : S3) (rs : List (List Nat)),
    derivesEff s c rs =
      { s with A := s.A ++ rs.map fun r => ⟨.observe, some c, r, .frame s.top, true⟩ }
  | s, [] => by cases s; simp [derivesEff]
  | s, r :: rs => by
    rw [derivesEff, derivesEff_eq c _ rs]
    simp [deriveEff, S3.addAuth, S3.top]

/-- The entry authorities of a batch: one per region, of origin `c` and mode `m`, held by the
current frame (§60, §61 effects; HandlePool v0.5, D.2). -/
theorem entriesEff_eq (m : Mode) (s : S3) (c : Nat) (rs : List (List Nat)) :
    entriesEff m s c rs =
      { s with A := s.A ++ rs.map fun r => ⟨m, some c, r, .frame s.top, true⟩ } := by
  cases m with
  | modify => rfl
  | observe => exact derivesEff_eq c s rs

/-- Ghost entries of a batch (HandlePool v0.5, D.2): the `n`-th is the authority `c + 1 + n` with
the slot and generation of the `n`-th handle (§38). -/
theorem mem_batchEntries : ∀ {c : Nat} {hs : List Handle} {e : Nat × Nat × Nat},
    e ∈ batchEntries c hs → ∃ n h, hs[n]? = some h ∧ e = (c + 1 + n, h.slot, h.gen)
  | _, [], _, he => by simp [batchEntries, mapI] at he
  | c, h :: hs, e, he => by
    simp only [batchEntries, mapI, List.mem_cons] at he
    rcases he with rfl | he
    · exact ⟨0, h, rfl, rfl⟩
    · obtain ⟨n, h', hh', rfl⟩ := mem_batchEntries (c := c + 1) he
      exact ⟨n + 1, h', by simpa using hh', by rw [show c + 1 + (n + 1) = c + 1 + 1 + n by omega]⟩

/-- Authorities after `resolve` (§60 effects; HandlePool v0.5, D.2): the companion `|A|`, then the
entry authority `|A| + 1` derived from it. -/
theorem resolve_A (s : S3) (pl : Pool) (m : Mode) (R : List Nat) :
    (deriveEff (compS s pl m) s.A.length R m).A = s.A ++
      [⟨m, some pl.internal, footprint s.P pl.storage, .frame s.top, true⟩,
        ⟨m, some s.A.length, R, .frame s.top, true⟩] := by
  simp [deriveEff, compS, S3.addAuth, S3.top]

/-- Authorities after `resolveMany` (§60, §61 effects; HandlePool v0.5, D.2): the companion `|A|`,
then one entry authority per handle, derived from it. -/
theorem resolveMany_A (m : Mode) (s : S3) (pl : Pool) (hs : List Handle) :
    (entriesEff m (compS s pl m) s.A.length (entryRegions s pl hs)).A = s.A ++
      ⟨m, some pl.internal, footprint s.P pl.storage, .frame s.top, true⟩ ::
        hs.map fun h => ⟨m, some s.A.length, footprint s.P (slotPlace pl h.slot), .frame s.top,
          true⟩ := by
  rw [entriesEff_eq]; simp [compS, deriveEff, S3.addAuth, S3.top, entryRegions]

/-! ## Ghost well-formedness of the pool layer (HandlePool v0.5, D.1, D.2; auxiliary) -/

/-- What `allocSlot` and `freeSlot` keep of a pool: identity, storage, `internal` and slot places
(HandlePool v0.5, D.1, D.3; auxiliary information, §38). -/
structure PoolShape where
  id : Nat
  storage : Nat
  internal : Nat
  places : List Nat

/-- The shape of a pool (HandlePool v0.5, D.1; auxiliary; §38). -/
def Pool.shape (pl : Pool) : PoolShape := ⟨pl.id, pl.storage, pl.internal, pl.slots.map (·.place)⟩

/-- Updating a slot with the same place keeps the shape (HandlePool v0.5, D.3; §38). -/
theorem setSlot_shape {pl : Pool} {i : Nat} {sl x : Slot} (hs : pl.slots[i]? = some sl)
    (hx : x.place = sl.place) : (setSlot pl i x).shape = pl.shape := by
  simp only [Pool.shape, setSlot, map_set_same (·.place) hs hx]

/-- Well-formedness of a pool shape (auxiliary, not a clause of the contract; HandlePool v0.5, D.1,
from `newPool`): `internal` is a `Modify` authority whose footprint is the footprint of the storage
(§76.2, §76.3); the storage and every slot have a leaf; slots lie in the storage and are pairwise
disjoint (D.1). -/
structure PoolOK (s : S3) (sh : PoolShape) : Prop where
  /-- §76.2: `internal` exists, with own mode `Modify` (HandlePool v0.5, D.1). -/
  internalMode : OptP (s.A[sh.internal]?) (fun y => y.mode = .modify) False
  /-- §76.3: `footprint(internal) = footprint(storage)` (HandlePool v0.5, D.1). -/
  fpEq : ∀ l, l ∈ s.afp sh.internal ↔ l ∈ footprint s.P sh.storage
  /-- §40, §49.2: the storage has a leaf (HandlePool v0.5, D.1). -/
  storageLeaf : ∃ l, l ∈ footprint s.P sh.storage
  /-- §40, §49.2: every slot has a leaf (HandlePool v0.5, D.1). -/
  slotLeaf : ∀ q ∈ sh.places, ∃ l, l ∈ footprint s.P q
  /-- HandlePool v0.5, D.1: slots lie in the storage. -/
  slotIn : ∀ q ∈ sh.places, ∀ l ∈ footprint s.P q, l ∈ footprint s.P sh.storage
  /-- HandlePool v0.5, D.1: slots are pairwise disjoint. -/
  disjoint : ∀ (a b qa qb : Nat), sh.places[a]? = some qa → sh.places[b]? = some qb → a ≠ b →
    ∀ l ∈ footprint s.P qa, l ∉ footprint s.P qb

/-- Well-formedness of a ghost resolution (auxiliary, HandlePool v0.5, D.2): it belongs to a pool
of `shs` with its `internal`; the companion is younger than `internal`, of the mode of the
resolution, over the footprint of the storage; each entry authority is younger than the companion,
over the footprint of its slot (§38, §60). -/
def ResOK (s : S3) (shs : List PoolShape) (r : Res) : Prop :=
  ∃ sh ∈ shs, sh.id = r.pool ∧ sh.internal = r.internal ∧ r.internal < r.comp ∧
    OptP (s.A[r.comp]?) (fun y => y.mode = r.mode ∧
      ∀ l, l ∈ y.footprint ↔ l ∈ footprint s.P sh.storage) False ∧
    ∀ e ∈ r.entries, r.comp < e.1 ∧ ∃ q, sh.places[e.2.1]? = some q ∧
      OptP (s.A[e.1]?) (fun y => ∀ l, l ∈ y.footprint ↔ l ∈ footprint s.P q) False

/-- Ghost well-formedness of the pool layer (auxiliary, not a clause of the contract;
HandlePool v0.5, D.1, D.2): fresh distinct identities, well-formed pools and resolutions (§38). -/
structure PoolWF (L : PState) : Prop where
  /-- HandlePool v0.5, D.1: identities are below the next fresh identity. -/
  ids : ∀ sh ∈ L.pools.map Pool.shape, sh.id < L.nId
  /-- HandlePool v0.5, D.1: identities are distinct. -/
  nodup : ((L.pools.map Pool.shape).map (·.id)).Nodup
  /-- HandlePool v0.5, D.1: every pool is well formed. -/
  pools : ∀ sh ∈ L.pools.map Pool.shape, PoolOK L.kern sh
  /-- HandlePool v0.5, D.2: every ghost resolution is well formed. -/
  res : ∀ r ∈ L.res, ResOK L.kern (L.pools.map Pool.shape) r

/-- Exclusivity of the companions of a pool (HandlePool v0.5, D.2 restricted to the companions of
the pool, HP5-4; non-normative library contract): two distinct active companions of the same pool
are both `Observe` (§43, §50). -/
def CompExcl (L : PState) : Prop :=
  ∀ r₁ ∈ L.res, ∀ r₂ ∈ L.res, r₁.pool = r₂.pool → r₁.comp ≠ r₂.comp →
    L.kern.Active r₁.comp → L.kern.Active r₂.comp → r₁.mode = .observe ∧ r₂.mode = .observe

/-- Footprints of every place with a leaf are kept (§40; support for HandlePool v0.5, D.1). -/
def FpKeep (s s' : S3) : Prop :=
  ∀ q l₀, l₀ ∈ footprint s.P q → ∀ l, l ∈ footprint s'.P q ↔ l ∈ footprint s.P q

/-- Same places keep footprints (§40; support for HandlePool v0.5, D.1). -/
theorem fpKeep_of_P {s s' : S3} (h : s'.P = s.P) : FpKeep s s' := fun _ _ _ _ => by rw [h]

/-- Kernel steps keep footprints (§40; §60–§75 effects; support for HandlePool v0.5, D.1). -/
theorem fpKeep_kstep {k : K} {s s' : S3} (h : KStep k s s') : FpKeep s s' :=
  fun _ _ h₀ l => Arena.kstep_fp h (Arena.footprint_lt h₀) l

/-- `FpKeep` composes (§40; support for HandlePool v0.5, D.1). -/
theorem FpKeep.trans {s s₁ s₂ : S3} (h₁ : FpKeep s s₁) (h₂ : FpKeep s₁ s₂) : FpKeep s s₂ :=
  fun q l₀ h₀ l => (h₂ q l₀ ((h₁ q l₀ h₀ l₀).2 h₀) l).trans (h₁ q l₀ h₀ l)

/-- A sequence of kernel steps keeps the authorities and the footprints (§42, §58; §60–§75;
HandlePool v0.5). -/
theorem KSeq.keep {k : K} {s s' : S3} (h : KSeq k s s') : Arena.AKeep s s' ∧ FpKeep s s' := by
  induction h with
  | refl => exact ⟨Arena.akeep_of_eq rfl, fpKeep_of_P rfl⟩
  | tail _ hs ih => exact ⟨ih.1.trans (Arena.kstep_akeep hs), ih.2.trans (fpKeep_kstep hs)⟩

/-- `PoolOK` carries over to a state keeping authorities and footprints (§42, §40;
HandlePool v0.5, D.1). -/
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
shapes (HandlePool v0.5, D.2; §42). -/
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
shapes (HandlePool v0.5, D.1, D.2, D.3; §42). -/
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

/-- A companion of a ghost resolution exists (HandlePool v0.5, D.2; §42). -/
theorem comp_lt {L : PState} (hw : PoolWF L) {r : Res} (hr : r ∈ L.res) :
    r.comp < L.kern.A.length := by
  obtain ⟨_, _, _, _, _, hc, _⟩ := hw.res r hr
  obtain ⟨y, hy, -⟩ := optP_false_iff.1 hc
  exact lt_of_getElem? hy

/-- `CompExcl` carries over to a kernel state that reactivates nothing (HandlePool v0.5, D.2;
§42). -/
theorem CompExcl.kern {L : PState} {s' : S3} (h : CompExcl L) (hw : PoolWF L)
    (hA : Arena.AKeep L.kern s') : CompExcl { L with kern := s' } :=
  fun r₁ hr₁ r₂ hr₂ hp hne ha₁ ha₂ => h r₁ hr₁ r₂ hr₂ hp hne
    (hA.active_back ha₁ (comp_lt hw hr₁)) (hA.active_back ha₂ (comp_lt hw hr₂))

/-- Two shapes of a list with distinct identities and the same identity are equal
(HandlePool v0.5, D.1; §46). -/
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

/-- The ghost resolution of pool `pl` names its `internal` (HandlePool v0.5, D.2; §38). -/
theorem res_internal {L : PState} (hw : PoolWF L) {r : Res} (hr : r ∈ L.res) {pl : Pool}
    (hpl : pl ∈ L.pools) (hp : r.pool = pl.id) :
    r.internal = pl.internal ∧ r.internal < r.comp ∧
      OptP (L.kern.A[r.comp]?) (fun y => y.mode = r.mode ∧
        ∀ l, l ∈ y.footprint ↔ l ∈ footprint L.kern.P pl.storage) False := by
  obtain ⟨sh, hsh, hid, hint, hlt, hc, -⟩ := hw.res r hr
  have e : sh = pl.shape :=
    eq_of_id hw.nodup hsh (List.mem_map_of_mem hpl) (hid.trans hp)
  subst e
  exact ⟨hint.symm, hlt, hc⟩

/-! ## Preservation of the ghost invariants (HandlePool v0.5, D.1, D.2, HP5-4) -/

/-- An active companion of a pool and a new companion are both `Observe` (HandlePool v0.5, D.2
restricted to the companions of the pool, HP5-4: "Une compagne `Modify` active bloque les
nouvelles compagnes … ; des compagnes `Observe` peuvent coexister"): an active companion unrelated
to `internal` contradicts I1 (§50), since `internal` is `Modify`; a descendant takes away the
effective mode that the new derivation needs (§43, §60.2). -/
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

/-- A new resolution of pool `pl`, made under `ResolveRight`, keeps `CompExcl` (HandlePool v0.5,
D.2, HP5-4; §43, §50, §60). -/
theorem compExcl_new {L : PState} {s' : S3} {pl : Pool} {m : Mode} {rn : Res}
    (hi1 : I1 L.kern) (hwf : PoolWF L) (hce : CompExcl L) (hA : Arena.AKeep L.kern s')
    (hpl : pl ∈ L.pools) (hR : ResolveRight L.kern pl m) (hrp : rn.pool = pl.id)
    (hrm : rn.mode = m) : CompExcl ⟨s', L.pools, L.nId, L.res ++ [rn]⟩ := by
  have hok := hwf.pools _ (List.mem_map_of_mem hpl)
  have key : ∀ r ∈ L.res, r.pool = pl.id → L.kern.Active r.comp →
      r.mode = .observe ∧ m = .observe := fun r hr hp ha => by
    obtain ⟨hint, hlt, hc⟩ := res_internal hwf hr hpl hp
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

/-- Adding a well-formed resolution keeps `PoolWF` (HandlePool v0.5, D.2; §60). -/
theorem poolWF_addRes {L : PState} {s' : S3} {rn : Res} (h : PoolWF L)
    (hA : Arena.AKeep L.kern s') (hf : FpKeep L.kern s')
    (hrn : ResOK s' (L.pools.map Pool.shape) rn) : PoolWF ⟨s', L.pools, L.nId, L.res ++ [rn]⟩ := by
  have h' := h.transport hA hf rfl
  refine ⟨h'.ids, h'.nodup, h'.pools, fun r hr => ?_⟩
  rcases List.mem_append.1 hr with hr | hr
  · exact h'.res r hr
  · rw [List.mem_singleton.1 hr]; exact hrn

/-- `newPool` keeps `PoolWF` (HandlePool v0.5, D.1): the new pool is well formed under `WF3`
(§49), which §76.6 requires of the state (`NewArenaBase.wf3`), its slots being the children of the
storage. -/
theorem poolWF_newPool {L L' : PState} {others : List (List Nat)} {st i : Nat} (hwf : PoolWF L)
    (h : NewPoolStep others st i L (.ok L')) : PoolWF L' := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  have hb := hpre.base
  have hw := hb.wf3
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
  refine ⟨fun sh hs => ?_, ?_, fun sh hs => ?_, fun r hr => ?_⟩
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

/-- `resolve` keeps `PoolWF` (HandlePool v0.5, D.2; §60). -/
theorem poolWF_resolve {L L' : PState} {j : Nat} {h : Handle} {m : Mode} (hwf : PoolWF L)
    (hst : ResolveStep j h m L (.ok L')) : PoolWF L' := by
  cases hst with
  | @ok pl sl hpj _ hR hsl _ =>
    have hpl : pl ∈ L.pools := List.mem_of_getElem? hpj
    have hAe := resolve_A L.kern pl m (footprint L.kern.P sl.place)
    obtain ⟨xi, hxi, -⟩ := hR.active
    refine poolWF_addRes hwf (Arena.akeep_append hAe) (fpKeep_of_P rfl)
      ⟨pl.shape, List.mem_map_of_mem hpl, rfl, rfl, lt_of_getElem? hxi, ?_, fun e he => ?_⟩
    · rw [hAe]; simp [OptP, Pool.shape]; exact fun _ => Iff.rfl
    · rw [List.mem_singleton.1 he]
      refine ⟨Nat.lt_succ_self _, sl.place, by simp [Pool.shape, hsl], ?_⟩
      rw [hAe]; simp [OptP]; exact fun _ => Iff.rfl

/-- `resolveMany` keeps `PoolWF` (HandlePool v0.5, D.2; §60, §61). -/
theorem poolWF_resolveMany {k : K} {L L' : PState} {j : Nat} {hs : List Handle} {m : Mode}
    (hwf : PoolWF L) (hst : ResolveManyStep k j hs m L (.ok L')) : PoolWF L' := by
  cases hst with
  | @ok pl hpj hB hR _ =>
    have hpl : pl ∈ L.pools := List.mem_of_getElem? hpj
    have hAe := resolveMany_A m L.kern pl hs
    obtain ⟨xi, hxi, -⟩ := hR.active
    have hval : ∀ h ∈ hs, ∃ sl, pl.slots[h.slot]? = some sl ∧ slotPlace pl h.slot = sl.place :=
      fun h hh => by
        obtain ⟨-, -, hsl⟩ := hB.1 h hh
        obtain ⟨sl, hsl, -⟩ := optP_false_iff.1 hsl
        exact ⟨sl, hsl, by simp [slotPlace, hsl]⟩
    have hP : (entriesEff m (compS L.kern pl m) L.kern.A.length (entryRegions L.kern pl hs)).P =
        L.kern.P := by rw [entriesEff_eq]; rfl
    refine poolWF_addRes hwf (Arena.akeep_append hAe) (fpKeep_of_P hP)
      ⟨pl.shape, List.mem_map_of_mem hpl, rfl, rfl, lt_of_getElem? hxi, ?_, fun e he => ?_⟩
    · rw [hAe, hP]; simp [OptP, Pool.shape]
    · obtain ⟨n, h, hh, rfl⟩ := mem_batchEntries he
      obtain ⟨sl, hsl, hsp⟩ := hval h (List.mem_of_getElem? hh)
      refine ⟨by simp; omega, sl.place, by simp [Pool.shape, hsl], ?_⟩
      rw [hAe, hP, List.getElem?_append_right (by omega)]
      simp [show L.kern.A.length + 1 + n - L.kern.A.length = n + 1 by omega, hh, OptP, hsp]

/-- Every library step keeps `PoolWF` (HandlePool v0.5, D.1–D.3, HP5-1; §42): kernel steps and
`unresolve` keep authorities and footprints, `allocSlot` and `freeSlot` keep the shapes of the
pools. -/
theorem pstep_poolWF {k : K} {L L' : PState} (hwf : PoolWF L) (h : PStep k L L') : PoolWF L' := by
  cases h with
  | kernel hs => exact hwf.transport (Arena.kstep_akeep hs) (fpKeep_kstep hs) rfl
  | newPool hs => exact poolWF_newPool hwf hs
  | allocSlot hs =>
    cases hs with
    | @ok pl i sl hpj _ hsl _ =>
      exact hwf.transport (Arena.akeep_of_eq rfl) (fpKeep_of_P rfl)
        (map_set_same Pool.shape hpj (setSlot_shape (x := { sl with live := true }) hsl rfl))
  | resolve hs => exact poolWF_resolve hwf hs
  | resolveMany hs => exact poolWF_resolveMany hwf hs
  | unresolve hs =>
    cases hs with
    | ok _ hr =>
      obtain ⟨hA, hf⟩ := (releaseAll_kseq (k := k) hr).keep
      exact hwf.transport hA hf rfl
  | freeSlot hs =>
    cases hs with
    | @ok pl sl hpj _ _ hsl _ =>
      exact hwf.transport (Arena.akeep_of_eq rfl) (fpKeep_of_P rfl)
        (map_set_same Pool.shape hpj (setSlot_shape (x := ⟨sl.place, sl.gen + 1, false⟩) hsl rfl))

/-- Every library step keeps `CompExcl` (HandlePool v0.5, D.2, HP5-4), under I1 (§50) and
`PoolWF`: kernel steps, `allocSlot` and `unresolve` reactivate no authority (§42), `newPool`
changes neither the kernel state nor the resolutions, `freeSlot` (a write, §67) neither the
authorities nor the resolutions, and a new companion is checked by `companion_blocks`. -/
theorem pstep_compExcl {k : K} {L L' : PState} (hi1 : I1 L.kern) (hwf : PoolWF L)
    (hce : CompExcl L) (h : PStep k L L') : CompExcl L' := by
  cases h with
  | kernel hs => exact hce.kern hwf (Arena.kstep_akeep hs)
  | newPool hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact hce
  | allocSlot hs =>
    cases hs with
    | ok => exact hce.kern hwf (Arena.akeep_of_eq rfl)
  | resolve hs =>
    cases hs with
    | @ok pl sl hpj _ hR _ _ =>
      exact compExcl_new hi1 hwf hce (Arena.akeep_append (resolve_A _ _ _ _))
        (List.mem_of_getElem? hpj) hR rfl rfl
  | resolveMany hs =>
    cases hs with
    | @ok pl hpj _ hR _ =>
      exact compExcl_new hi1 hwf hce (Arena.akeep_append (resolveMany_A _ _ _ _))
        (List.mem_of_getElem? hpj) hR rfl rfl
  | unresolve hs =>
    cases hs with
    | ok _ hr => exact hce.kern hwf (releaseAll_kseq (k := k) hr).keep.1
  | freeSlot hs =>
    cases hs with
    | ok => exact hce

/-- `PoolWF` holds on every library-reachable state (HandlePool v0.5, D.1, D.2; §47: the initial
registry is empty). -/
theorem pReach_poolWF {k : K} {statics : Statics} {L : PState} (h : PReach k statics L) :
    PoolWF L := by
  induction h with
  | init => exact ⟨by simp [PState.init], by simp [PState.init], by simp [PState.init],
      by simp [PState.init]⟩
  | step _ hs ih => exact pstep_poolWF ih hs

/-- `CompExcl` holds on every library-reachable state (HandlePool v0.5, D.2, HP5-4), under
`DDSound` (§80) and `StaticsOK` (§47), which give I1 (§50) on the kernel side of the run
(`kernel_guarantee`). -/
theorem pReach_compExcl {k : K} {statics : Statics} (hdd : DDSound k) (hst : StaticsOK statics)
    {L : PState} (h : PReach k statics L) : CompExcl L := by
  induction h with
  | init => intro r hr; simp [PState.init] at hr
  | step hr hs ih =>
    exact pstep_compExcl (kernel_guarantee hdd hst _ hr).2.1.1.1 (pReach_poolWF hr) ih hs

/-! ## `PoolInv` (HandlePool v0.5, D.4 per pool, HP5-4) -/

/-- `PoolInv`, item 1 (HandlePool v0.5, D.4 (1); non-normative library contract): the entries of
every pool lie in its storage and are pairwise disjoint (§40). -/
def EntriesDisjoint (L : PState) : Prop :=
  ∀ pl ∈ L.pools,
    (∀ sl ∈ pl.slots, ∀ l ∈ footprint L.kern.P sl.place, l ∈ footprint L.kern.P pl.storage) ∧
    ∀ (a b : Nat) (sa sb : Slot), pl.slots[a]? = some sa → pl.slots[b]? = some sb → a ≠ b →
      ∀ l ∈ footprint L.kern.P sa.place, l ∉ footprint L.kern.P sb.place

/-- `PoolInv`, item 2, `pool_no_stale_access` as a state predicate (HandlePool v0.5, D.4 (2);
non-normative library contract): no active entry authority designates a free slot or a former
generation (§89). -/
def NoStale (L : PState) : Prop :=
  ∀ r ∈ L.res, ∀ e ∈ r.entries, L.kern.Active e.1 → ∃ pl ∈ L.pools, pl.id = r.pool ∧
    ∃ sl, pl.slots[e.2.1]? = some sl ∧ sl.gen = e.2.2 ∧ sl.live = true

/-- `PoolInv`, item 3, the transition guarantee per pool (HandlePool v0.5, D.4 (3) as amended by
HP5-1'; non-normative library contract; §42, §43): `freeSlot` never succeeds while an active strict
descendant of the `internal` of the slot's pool covers a leaf of the slot. -/
def FreeGuarantee (L : PState) : Prop :=
  ∀ (j : Nat) (h : Handle) (L' : PState), FreeSlotStep j h L (.ok L') →
    ∀ (pl : Pool) (sl : Slot), L.pools[j]? = some pl → pl.slots[h.slot]? = some sl →
      ∀ x, L.kern.Active x → pl.internal ∈ L.kern.ancs x →
        ∀ l ∈ L.kern.afp x, l ∉ footprint L.kern.P sl.place

/-- `PoolInv` (HandlePool v0.5, D.4 per pool, HP5-4, HP5-1'; non-normative library contract): entry
disjointness, `pool_no_stale_access`, and the per-pool transition guarantee of `freeSlot` (§55
analogue, §57). -/
def PoolInv (L : PState) : Prop := EntriesDisjoint L ∧ NoStale L ∧ FreeGuarantee L

/-- `EntriesDisjoint` follows from the ghost well-formedness (HandlePool v0.5, D.4 (1); §40). -/
theorem entriesDisjoint_of {L : PState} (hwf : PoolWF L) : EntriesDisjoint L := by
  intro pl hpl
  have hok := hwf.pools _ (List.mem_map_of_mem hpl)
  exact ⟨fun sl hsl l hl => hok.slotIn sl.place (List.mem_map_of_mem (f := (·.place)) hsl) l hl,
    fun a b sa sb ha hb hab => hok.disjoint a b sa.place sb.place
      (by simp [Pool.shape, ha]) (by simp [Pool.shape, hb]) hab⟩

/-- `pool_entries_disjoint` (HandlePool v0.5, D.4 (1); §40, §47): on every library-reachable
state, the entries of every pool lie in its storage and are pairwise disjoint. -/
theorem pool_entries_disjoint {k : K} {statics : Statics} {L : PState} (h : PReach k statics L) :
    EntriesDisjoint L :=
  entriesDisjoint_of (pReach_poolWF h)

/-- `pool_freeSlot_no_internal_desc` (HandlePool v0.5, D.4 (3) as amended by HP5-1'): on every
library state, `freeSlot` never succeeds while an active strict descendant of the `internal` of the
slot's pool covers a leaf of the slot (§42, §43). It is the content condition of `freeSlot`. -/
theorem pool_freeSlot_no_internal_desc (L : PState) : FreeGuarantee L := by
  intro j h L' hst pl sl hpj hsl x hx hxi l hl hlq
  cases hst with
  | @ok pl' sl' hpj' _ _ hsl' hc =>
    rw [hpj] at hpj'; cases hpj'
    rw [hsl] at hsl'; cases hsl'
    obtain ⟨y, hy, ya⟩ := hx
    exact hc.noDesc x (List.mem_range.2 (lt_of_getElem? hy)) ⟨y, hy, ya⟩ hxi l hl hlq

/-! ## Origin chains of the companions and entry authorities (HandlePool v0.5, D.2, HP5-1') -/

/-- Appending authorities keeps the origin chains of the former ones (§42). -/
theorem ancs_append {s s' : S3} {l : List Authority} (hA : s'.A = s.A ++ l) {j : Nat}
    (hj : j < s.A.length) : s'.ancs j = s.ancs j :=
  chain_congr fun i hi => by
    simp only [S3.org, hA, List.getElem?_append_left (Nat.lt_of_le_of_lt hi hj)]

/-- A kernel step keeps on the origin chain of a former authority every ancestor still active
after it (§42, §58; §60–§75 `ok` effects): only `exitFrame` changes origins, reanchoring a
surviving authority to the first surviving active origin of its chain (§73.4), and an ancestor
active after the exit survives. -/
theorem kstep_ancs_keep {k : K} {s s' : S3} (h : KStep k s s') {x : Nat} (hx : x < s.A.length)
    {w : Nat} (hw : w ∈ s.ancs x) (hwa : s'.Active w) : w ∈ s'.ancs x := by
  cases h with
  | derive hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; rw [ancs_append rfl hx]; exact hw
  | split hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; rw [ancs_append rfl hx]; exact hw
  | release hs =>
    obtain ⟨hp, rfl⟩ := Guarded.ok_iff.1 hs
    obtain ⟨y, hy, -⟩ := hp.active
    rw [release_ancs hy]; exact hw
  | transfer hs =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; rw [(transfer_skel _ _ _).ancs]; exact hw
  | depend hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact hw
  | enter hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; rw [Frames.enter_ancs_lt hx]; exact hw
  | exit hs =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
    obtain ⟨z, hz, za⟩ := hwa
    obtain ⟨z₀, -, rfl⟩ := Frames.exit_get hz
    exact Frames.exit_ancs_keep (x + 1) x (Nat.lt_succ_self x) w hw (Frames.exitG_active za)
  | read hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact hw
  | write hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact hw
  | writeShared hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact hw
  | pin hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact hw
  | unpin hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact hw
  | endUse hs =>
    rename_i p
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
    rw [show endUseEff s p = cleanup (endUseS s p) from rfl,
      ((EndFree.endUseS_releases s p).trans (EndFree.cleanup_releases _)).ancs]
    exact hw
  | free hs =>
    rename_i p _
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
    rw [show freeEff s p = cleanup (freeS s p) from rfl,
      ((EndFree.freeS_releases s p).trans (EndFree.cleanup_releases _)).ancs]
    exact hw
  | alloc hs => cases hs with
    | ok _ _ => rw [ancs_append rfl hx]; exact hw
  | store hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; rw [(Arena.store_skel _ _ _).ancs]; exact hw

/-- A sequence of kernel steps keeps on the origin chain of a former authority every ancestor still
active at its end (§42, §73.4). -/
theorem KSeq.ancs_keep {k : K} {s s' : S3} (h : KSeq k s s') {x : Nat} (hx : x < s.A.length)
    {w : Nat} (hw : w ∈ s.ancs x) (hwa : s'.Active w) : w ∈ s'.ancs x := by
  induction h with
  | refl => exact hw
  | tail h₁ hs ih =>
    have hK := h₁.keep.1
    exact kstep_ancs_keep hs (hK.lt hx)
      (ih ((Arena.kstep_akeep hs).active_back hwa (hK.lt (Nat.lt_trans (chain_lt hw) hx)))) hwa

/-- The companion and the entry authorities of every ghost resolution, while active, have the
`internal` of their pool on their origin chain as long as `internal` is active (auxiliary, not a
clause of the contract; HandlePool v0.5, D.2: the companion is derived from `internal`, each entry
authority from the companion; §42, §73.4). -/
def ResAnc (L : PState) : Prop :=
  ∀ r ∈ L.res, ∀ x ∈ r.comp :: r.entries.map (·.1), L.kern.Active x →
    L.kern.Active r.internal → r.internal ∈ L.kern.ancs x

/-- The `internal`, the companion and the entry authorities of a ghost resolution exist (§42;
HandlePool v0.5, D.2). -/
theorem res_lt {L : PState} (hw : PoolWF L) {r : Res} (hr : r ∈ L.res) :
    r.internal < L.kern.A.length ∧ ∀ x ∈ r.comp :: r.entries.map (·.1), x < L.kern.A.length := by
  obtain ⟨sh, -, -, -, hlt, hc, he⟩ := hw.res r hr
  obtain ⟨y, hy, -⟩ := optP_false_iff.1 hc
  have hc' := lt_of_getElem? hy
  refine ⟨Nat.lt_trans hlt hc', fun x hx => ?_⟩
  rcases List.mem_cons.1 hx with rfl | hx
  · exact hc'
  · obtain ⟨e, he', rfl⟩ := List.mem_map.1 hx
    obtain ⟨-, q, -, ho⟩ := he e he'
    obtain ⟨z, hz, -⟩ := optP_false_iff.1 ho
    exact lt_of_getElem? hz

/-- A companion of origin `i` and entry authorities of origin the companion have `i` on their
origin chain (§42, §60; HandlePool v0.5, D.2). -/
theorem anc_new {s : S3} {i c : Nat} {es : List Nat} (hic : i < c)
    (hc : OptP (s.A[c]?) (fun y => y.origin = some i) False)
    (he : ∀ e ∈ es, c < e ∧ OptP (s.A[e]?) (fun y => y.origin = some c) False) :
    ∀ x ∈ c :: es, i ∈ s.ancs x := by
  obtain ⟨yc, hyc, hoc⟩ := optP_false_iff.1 hc
  have hci : i ∈ s.ancs c := by
    unfold S3.ancs; rw [chain_cons (by simp [S3.org, hyc, hoc]) hic]; exact List.mem_cons_self ..
  intro x hx
  rcases List.mem_cons.1 hx with rfl | hx
  · exact hci
  · obtain ⟨hlt, ho⟩ := he x hx
    obtain ⟨y, hy, hoy⟩ := optP_false_iff.1 ho
    unfold S3.ancs; rw [chain_cons (by simp [S3.org, hy, hoy]) hlt]
    exact List.mem_cons_of_mem _ hci

/-- `ResAnc` carries over a sequence of kernel steps (§42, §73.4; HandlePool v0.5, D.2). -/
theorem ResAnc.kseq {k : K} {L : PState} {s' : S3} (h : ResAnc L) (hw : PoolWF L)
    (hs : KSeq k L.kern s') : ResAnc { L with kern := s' } := by
  intro r hr x hx hxa hia
  obtain ⟨hil, hxl⟩ := res_lt hw hr
  have hA := hs.keep.1
  exact hs.ancs_keep (hxl x hx)
    (h r hr x hx (hA.active_back hxa (hxl x hx)) (hA.active_back hia hil)) hia

/-- `ResAnc` carries over the addition of authorities and of a resolution satisfying it (§42, §60;
HandlePool v0.5, D.2). -/
theorem ResAnc.addRes {L : PState} {s' : S3} {l : List Authority} {rn : Res} (h : ResAnc L)
    (hw : PoolWF L) (hA : s'.A = L.kern.A ++ l)
    (hrn : ∀ x ∈ rn.comp :: rn.entries.map (·.1), rn.internal ∈ s'.ancs x) :
    ResAnc ⟨s', L.pools, L.nId, L.res ++ [rn]⟩ := by
  intro r hr x hx hxa hia
  rcases List.mem_append.1 hr with hr | hr
  · obtain ⟨hil, hxl⟩ := res_lt hw hr
    have hK := Arena.akeep_append hA
    show r.internal ∈ s'.ancs x
    rw [ancs_append hA (hxl x hx)]
    exact h r hr x hx (hK.active_back hxa (hxl x hx)) (hK.active_back hia hil)
  · rw [List.mem_singleton.1 hr] at hx ⊢; exact hrn x hx

/-- Every library step keeps `ResAnc` (HandlePool v0.5, D.2; §42, §73.4): kernel steps and
`unresolve` keep every active ancestor on the chains (`KSeq.ancs_keep`), `newPool`, `allocSlot` and
`freeSlot` change neither the authorities nor the resolutions, and `resolve` and `resolveMany` add
a companion of origin `internal` and entry authorities of origin the companion (§60, §61). -/
theorem pstep_resAnc {k : K} {L L' : PState} (hw : PoolWF L) (h : ResAnc L) (hs : PStep k L L') :
    ResAnc L' := by
  cases hs with
  | kernel hs => exact h.kseq hw (KSeq.single hs)
  | newPool hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact h
  | allocSlot hs =>
    cases hs with
    | ok => exact h
  | @resolve _ _ _ m hs =>
    cases hs with
    | @ok pl sl _ _ hR _ _ =>
      obtain ⟨xi, hxi, -⟩ := hR.active
      have hAe := resolve_A L.kern pl m (footprint L.kern.P sl.place)
      refine h.addRes hw hAe (anc_new (lt_of_getElem? hxi) (by rw [hAe]; simp [OptP])
        fun e he => ?_)
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at he
      subst he
      exact ⟨Nat.lt_succ_self _, by rw [hAe]; simp [OptP]⟩
  | @resolveMany _ _ hl m hs =>
    cases hs with
    | @ok pl _ _ hR _ =>
      obtain ⟨xi, hxi, -⟩ := hR.active
      have hAe := resolveMany_A m L.kern pl hl
      refine h.addRes hw hAe (anc_new (lt_of_getElem? hxi) (by rw [hAe]; simp [OptP])
        fun e he => ?_)
      obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
      obtain ⟨n, h, hh, rfl⟩ := mem_batchEntries he'
      refine ⟨by simp; omega, ?_⟩
      rw [hAe, List.getElem?_append_right (by omega)]
      simp [show L.kern.A.length + 1 + n - L.kern.A.length = n + 1 by omega, hh, OptP]
  | unresolve hs =>
    cases hs with
    | ok _ hr => exact h.kseq hw (releaseAll_kseq (k := k) hr)
  | freeSlot hs =>
    cases hs with
    | ok => exact h

/-- `ResAnc` holds on every library-reachable state (HandlePool v0.5, D.2; §47: no resolution
initially). -/
theorem pReach_resAnc {k : K} {statics : Statics} {L : PState} (h : PReach k statics L) :
    ResAnc L := by
  induction h with
  | init => intro r hr; simp [PState.init] at hr
  | step hr hs ih => exact pstep_resAnc (pReach_poolWF hr) ih hs

/-! ## `pool_no_stale_access` and `pool_inv_preserved` (HandlePool v0.5, D.4, HP5-1') -/

/-- An entry authority covers a leaf of the place of its slot (HandlePool v0.5, D.2; §40, §42). -/
theorem entry_covers {L : PState} (hw : PoolWF L) {r : Res} (hr : r ∈ L.res)
    {e : Nat × Nat × Nat} (he : e ∈ r.entries) {pl : Pool} (hpl : pl ∈ L.pools)
    (hp : r.pool = pl.id) {sl : Slot} (hsl : pl.slots[e.2.1]? = some sl) :
    ∃ l ∈ L.kern.afp e.1, l ∈ footprint L.kern.P sl.place := by
  obtain ⟨sh, hsh, hid, -, -, -, hen⟩ := hw.res r hr
  have e' : sh = pl.shape := eq_of_id hw.nodup hsh (List.mem_map_of_mem hpl) (hid.trans hp)
  subst e'
  obtain ⟨-, q, hq, ho⟩ := hen e he
  have hq' : q = sl.place := by simp [Pool.shape, hsl] at hq; exact hq.symm
  subst hq'
  obtain ⟨y, hy, hfp⟩ := optP_false_iff.1 ho
  obtain ⟨l, hl⟩ := (hw.pools _ (List.mem_map_of_mem hpl)).slotLeaf sl.place
    (List.mem_map_of_mem (f := (·.place)) (List.mem_of_getElem? hsl))
  exact ⟨l, by simp only [S3.afp, hy]; exact (hfp l).2 hl, hl⟩

/-- A slot update keeps a live slot live at its generation, unless it is the updated slot of the
updated pool and the update says otherwise (HandlePool v0.5, D.3; §89). -/
theorem live_after_set {pools : List Pool} {j i : Nat} {pl : Pool} {x : Slot}
    (hj : pools[j]? = some pl) {pl₀ : Pool} (h₀ : pl₀ ∈ pools) {a : Nat} {sl₀ : Slot}
    (ha : pl₀.slots[a]? = some sl₀) (hlv : sl₀.live = true)
    (hx : pl₀ = pl → a = i → x.gen = sl₀.gen ∧ x.live = true) :
    ∃ pl' ∈ pools.set j (setSlot pl i x), pl'.id = pl₀.id ∧
      ∃ sl', pl'.slots[a]? = some sl' ∧ sl'.gen = sl₀.gen ∧ sl'.live = true := by
  obtain ⟨n, hn⟩ := List.mem_iff_getElem?.1 h₀
  by_cases hnj : n = j
  · subst hnj
    have e : pl₀ = pl := Option.some.inj (hn.symm.trans hj)
    refine ⟨setSlot pl i x, mem_set_self' hj, by rw [e]; rfl, ?_⟩
    by_cases hai : a = i
    · subst hai; obtain ⟨hg, hl⟩ := hx e rfl
      exact ⟨x, getElem?_set_eq' (e ▸ ha), hg, hl⟩
    · exact ⟨sl₀, by simp only [setSlot]; rw [getElem?_set_ne' hai]; exact e ▸ ha, rfl, hlv⟩
  · exact ⟨pl₀, List.mem_of_getElem? (by rw [getElem?_set_ne' hnj]; exact hn), rfl, sl₀, ha, rfl,
      hlv⟩

/-- `NoStale` carries over a sequence of kernel steps (HandlePool v0.5, D.4 (2); §42). -/
theorem NoStale.kseq {k : K} {L : PState} {s' : S3} (h : NoStale L) (hw : PoolWF L)
    (hs : KSeq k L.kern s') : NoStale { L with kern := s' } := fun r hr e he ha =>
  h r hr e he (hs.keep.1.active_back ha
    ((res_lt hw hr).2 e.1 (List.mem_cons_of_mem _ (List.mem_map_of_mem he))))

/-- `NoStale` carries over the addition of authorities and of a resolution whose entries designate
live slots at their generation (HandlePool v0.5, D.2, D.4 (2); §60). -/
theorem NoStale.addRes {L : PState} {s' : S3} {l : List Authority} {rn : Res} (h : NoStale L)
    (hw : PoolWF L) (hA : s'.A = L.kern.A ++ l)
    (hrn : ∀ e ∈ rn.entries, ∃ pl ∈ L.pools, pl.id = rn.pool ∧
      ∃ sl, pl.slots[e.2.1]? = some sl ∧ sl.gen = e.2.2 ∧ sl.live = true) :
    NoStale ⟨s', L.pools, L.nId, L.res ++ [rn]⟩ := by
  intro r hr e he ha
  rcases List.mem_append.1 hr with hr | hr
  · exact h r hr e he ((Arena.akeep_append hA).active_back ha
      ((res_lt hw hr).2 e.1 (List.mem_cons_of_mem _ (List.mem_map_of_mem he))))
  · rw [List.mem_singleton.1 hr] at he ⊢; exact hrn e he

/-- Every library step keeps `NoStale` (HandlePool v0.5, D.4 (2), HP5-1'), under `PoolWF` and
`ResAnc`: kernel steps and `unresolve` reactivate no authority (§42); `allocSlot` makes a free slot
live; `resolve` and `resolveMany` record entries of valid handles (§89); `freeSlot` cannot free the
slot of an active entry authority, a strict descendant of `internal` covering the slot (`ResAnc`,
`entry_covers`, HP5-1'). -/
theorem pstep_noStale {k : K} {L L' : PState} (hw : PoolWF L) (ha : ResAnc L) (h : NoStale L)
    (hs : PStep k L L') : NoStale L' := by
  cases hs with
  | kernel hs => exact h.kseq hw (KSeq.single hs)
  | newPool hs =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
    intro r hr e he hea
    obtain ⟨pl, hpl, rest⟩ := h r hr e he hea
    exact ⟨pl, List.mem_append_left _ hpl, rest⟩
  | allocSlot hs =>
    cases hs with
    | @ok pl i sl hpj _ hsl _ =>
      intro r hr e he hea
      obtain ⟨pl₀, hpl₀, hid, sl₀, hs₀, hg, hlv⟩ := h r hr e he hea
      obtain ⟨pl', hpl', hid', sl', h₁, h₂, h₃⟩ := live_after_set (i := i)
        (x := { sl with live := true }) hpj hpl₀ hs₀ hlv fun e₁ e₂ => by
          subst e₁; rw [e₂, hsl] at hs₀; cases hs₀; exact ⟨rfl, rfl⟩
      exact ⟨pl', hpl', hid'.trans hid, sl', h₁, h₂.trans hg, h₃⟩
  | resolve hs =>
    cases hs with
    | @ok pl sl hpj hH _ _ _ =>
      refine h.addRes hw (resolve_A _ _ _ _) fun e he => ?_
      rw [List.mem_singleton.1 he]
      obtain ⟨-, -, ho⟩ := hH
      obtain ⟨sl', hsl', hg, hlv⟩ := optP_false_iff.1 ho
      exact ⟨pl, List.mem_of_getElem? hpj, rfl, sl', hsl', hg, hlv⟩
  | resolveMany hs =>
    cases hs with
    | @ok pl hpj hB _ _ =>
      refine h.addRes hw (resolveMany_A _ _ _ _) fun e he => ?_
      obtain ⟨n, hd, hh, rfl⟩ := mem_batchEntries he
      obtain ⟨-, -, ho⟩ := hB.1 hd (List.mem_of_getElem? hh)
      obtain ⟨sl', hsl', hg, hlv⟩ := optP_false_iff.1 ho
      exact ⟨pl, List.mem_of_getElem? hpj, rfl, sl', hsl', hg, hlv⟩
  | unresolve hs =>
    cases hs with
    | ok _ hr => exact h.kseq hw (releaseAll_kseq (k := k) hr)
  | @freeSlot _ _ hd hs =>
    cases hs with
    | @ok pl sl hpj _ hR hsl hc =>
      intro r hr e he hea
      obtain ⟨pl₀, hpl₀, hid, sl₀, hs₀, hg, hlv⟩ := h r hr e he hea
      obtain ⟨pl', hpl', hid', sl', h₁, h₂, h₃⟩ := live_after_set (i := hd.slot)
        (x := ⟨sl.place, sl.gen + 1, false⟩) hpj hpl₀ hs₀ hlv fun e₁ e₂ => by
        subst e₁
        have hpl := List.mem_of_getElem? hpj
        obtain ⟨hint, -⟩ := res_internal hw hr hpl hid.symm
        have hanc := ha r hr e.1 (List.mem_cons_of_mem _ (List.mem_map_of_mem he)) hea
          (hint ▸ hR.1)
        obtain ⟨l, hl, hlq⟩ := entry_covers hw hr he hpl hid.symm (by rw [e₂]; exact hsl)
        obtain ⟨y, hy, ya⟩ := hea
        exact (hc.noDesc e.1 (List.mem_range.2 (lt_of_getElem? hy)) ⟨y, hy, ya⟩ (hint ▸ hanc) l
          hl hlq).elim
      exact ⟨pl', hpl', hid'.trans hid, sl', h₁, h₂.trans hg, h₃⟩

/-- `pool_no_stale_access` (HandlePool v0.5, D.4 (2), under the content condition of HP5-1'): on
every library-reachable state, every active entry authority designates a live slot of its pool at
its resolved generation (§89). No kernel hypothesis is needed. -/
theorem pool_no_stale_access {k : K} {statics : Statics} {L : PState} (h : PReach k statics L) :
    NoStale L := by
  induction h with
  | init => intro r hr; simp [PState.init] at hr
  | step hr hs ih => exact pstep_noStale (pReach_poolWF hr) (pReach_resAnc hr) ih hs

/-- `pool_inv_preserved` (HandlePool v0.5, D.4 per pool, HP5-4, HP5-1'): `PoolInv` holds on every
library-reachable state (§47, §57). -/
theorem pool_inv_preserved {k : K} {statics : Statics} {L : PState} (h : PReach k statics L) :
    PoolInv L :=
  ⟨pool_entries_disjoint h, pool_no_stale_access h, pool_freeSlot_no_internal_desc L⟩

/-- Nested pools, first fact (HandlePool v0.5, HP5-1'): on every library-reachable state, a live
pool `pb` nested in an entry of pool `pa` (its `internal` a strict descendant of `internal` of `pa`,
its storage sharing a leaf with the slot) blocks the freeing of that slot (§42, §43, §76.3). -/
theorem pool_nested_blocks_entry {k : K} {statics : Statics} {L : PState} (hr : PReach k statics L)
    {j : Nat} {h : Handle} {pa pb : Pool} {sl : Slot} (hpa : L.pools[j]? = some pa)
    (hsl : pa.slots[h.slot]? = some sl) (hpb : pb ∈ L.pools) (hlive : L.kern.Active pb.internal)
    (hanc : pa.internal ∈ L.kern.ancs pb.internal)
    (hin : ∃ l ∈ footprint L.kern.P pb.storage, l ∈ footprint L.kern.P sl.place) :
    ∀ L', ¬ FreeSlotStep j h L (.ok L') := by
  intro L' hst
  obtain ⟨l, hl, hlq⟩ := hin
  have hok := (pReach_poolWF hr).pools _ (List.mem_map_of_mem hpb)
  exact pool_freeSlot_no_internal_desc L j h L' hst pa sl hpa hsl pb.internal hlive hanc l
    ((hok.fpEq l).2 hl) hlq

/-- Nested pools, second fact (HandlePool v0.5, HP5-1'): `internal` of a pool and its ancestors —
for a nested pool, the authorities of the parent pool from which its `internal` descends — are not
strict descendants of that `internal`, so the content condition of `freeSlot` (`NoInternalDesc`)
never counts them, and they do not block the freeing of the nested pool's slots (§42). -/
theorem not_internal_desc_of_anc (s : S3) (pl : Pool) {x : Nat}
    (hx : x = pl.internal ∨ x ∈ s.ancs pl.internal) : pl.internal ∉ s.ancs x := fun h => by
  have h₁ := chain_lt h
  rcases hx with rfl | hx
  · exact Nat.lt_irrefl _ h₁
  · exact Nat.lt_asymm h₁ (chain_lt hx)

/-- `pool_resolve_modify_exclusive` per pool (HandlePool v0.5, D.2 restricted to the companions of
the pool, HP5-4: "La propriété d'exclusivité concerne toutes les suites d'opérations admises du
noyau"): on every library-reachable state, under `DDSound` (§80) and `StaticsOK` (§47), whatever
its kernel steps, an active `Modify` companion of a pool is the only active companion of that pool
(§43, §50). -/
theorem pool_resolve_modify_exclusive {k : K} {statics : Statics} (hdd : DDSound k)
    (hst : StaticsOK statics) {L : PState} (h : PReach k statics L) :
    ∀ r₁ ∈ L.res, ∀ r₂ ∈ L.res, r₁.pool = r₂.pool → L.kern.Active r₁.comp →
      L.kern.Active r₂.comp → r₁.mode = .modify → r₁.comp = r₂.comp := by
  intro r₁ hr₁ r₂ hr₂ hp ha₁ ha₂ hm
  refine Decidable.byContradiction fun hne => ?_
  have := pReach_compExcl hdd hst h r₁ hr₁ r₂ hr₂ hp hne ha₁ ha₂
  rw [hm] at this; cases this.1

/-! ## Handle validation: dead pool, other pool, stale, absent or free slot (HandlePool v0.5, D.2,
D.3, HP5-5, HP5-6, HP5-1''; §89) -/

/-- A handle of a dead pool is not valid (HandlePool v0.5, HP5-5; §46 analogue, §89). -/
theorem not_handleOK_dead {s : S3} {pl : Pool} {h : Handle} (hd : ¬ s.Active pl.internal) :
    ¬ HandleOK s pl h :=
  fun ⟨ha, _⟩ => hd ha

/-- A handle of another pool is not valid (HandlePool v0.5, D.2, D.3; §89). -/
theorem not_handleOK_other {s : S3} {pl : Pool} {h : Handle} (hid : h.id ≠ pl.id) :
    ¬ HandleOK s pl h :=
  fun ⟨_, e, _⟩ => hid e

/-- A stale handle is not valid (HandlePool v0.5, D.2, D.3; §89). -/
theorem not_handleOK_stale {s : S3} {pl : Pool} {h : Handle} {sl : Slot}
    (hsl : pl.slots[h.slot]? = some sl) (hg : sl.gen ≠ h.gen) : ¬ HandleOK s pl h :=
  fun ⟨_, _, ho⟩ => by rw [hsl] at ho; exact hg ho.1

/-- A handle of a free slot is not valid, even at the slot's generation (HandlePool v0.5, D.2:
"slot … libre ⇒ `fail`", HP5-6; §89). -/
theorem not_handleOK_free {s : S3} {pl : Pool} {h : Handle} {sl : Slot}
    (hsl : pl.slots[h.slot]? = some sl) (hf : sl.live = false) : ¬ HandleOK s pl h :=
  fun ⟨_, _, ho⟩ => by rw [hsl] at ho; have h2 := ho.2; rw [hf] at h2; cases h2

/-- A handle of an absent slot is not valid (HandlePool v0.5, D.2: "slot absent ⇒ `fail`";
§89). -/
theorem not_handleOK_absent {s : S3} {pl : Pool} {h : Handle} (hn : pl.slots[h.slot]? = none) :
    ¬ HandleOK s pl h :=
  fun ⟨_, _, ho⟩ => by rw [hn] at ho; exact ho

/-- An invalid handle makes `resolve` fail, before the right is checked, and `fail` is its only
outcome (HandlePool v0.5, D.2: "⇒ `fail`, sans changement d'état"; HP5-5; §58). -/
theorem pool_resolve_invalid_fails {L : PState} {j : Nat} {pl : Pool} {h : Handle} {m : Mode}
    (hp : L.pools[j]? = some pl) (hH : ¬ HandleOK L.kern pl h) :
    ResolveStep j h m L .fail ∧ ∀ o, ResolveStep j h m L o → o = .fail := by
  refine ⟨.fail hp hH, fun o ho => ?_⟩
  cases ho with
  | noPool hn => rw [hp] at hn; cases hn
  | fail => rfl
  | noRight hp' hH' => rw [hp] at hp'; cases hp'; exact absurd hH' hH
  | noEntry hp' hH' => rw [hp] at hp'; cases hp'; exact absurd hH' hH
  | ok hp' hH' => rw [hp] at hp'; cases hp'; exact absurd hH' hH

/-- `pool_resolve_stale_fails` (HandlePool v0.5, D.2, HP5-5; §89: "a stale identity or generation
leads to defined failure"): whatever the right, a handle of a former generation makes `resolve`
fail. -/
theorem pool_resolve_stale_fails {L : PState} {j : Nat} {pl : Pool} {h : Handle} {m : Mode}
    {sl : Slot} (hp : L.pools[j]? = some pl) (hsl : pl.slots[h.slot]? = some sl)
    (hg : sl.gen ≠ h.gen) :
    ResolveStep j h m L .fail ∧ ∀ o, ResolveStep j h m L o → o = .fail :=
  pool_resolve_invalid_fails hp (not_handleOK_stale hsl hg)

/-- `pool_resolve_other_pool_fails` (HandlePool v0.5, D.2, HP5-5; §89). -/
theorem pool_resolve_other_pool_fails {L : PState} {j : Nat} {pl : Pool} {h : Handle} {m : Mode}
    (hp : L.pools[j]? = some pl) (hid : h.id ≠ pl.id) :
    ResolveStep j h m L .fail ∧ ∀ o, ResolveStep j h m L o → o = .fail :=
  pool_resolve_invalid_fails hp (not_handleOK_other hid)

/-- A handle of a dead pool (`internal` inactive) is stale: `resolve` fails (HandlePool v0.5,
HP5-5; §89). -/
theorem pool_resolve_dead_fails {L : PState} {j : Nat} {pl : Pool} {h : Handle} {m : Mode}
    (hp : L.pools[j]? = some pl) (hd : ¬ L.kern.Active pl.internal) :
    ResolveStep j h m L .fail ∧ ∀ o, ResolveStep j h m L o → o = .fail :=
  pool_resolve_invalid_fails hp (not_handleOK_dead hd)

/-- A handle of a free entry is stale: `resolve` fails (HandlePool v0.5, HP5-6; §89). -/
theorem pool_resolve_free_fails {L : PState} {j : Nat} {pl : Pool} {h : Handle} {m : Mode}
    {sl : Slot} (hp : L.pools[j]? = some pl) (hsl : pl.slots[h.slot]? = some sl)
    (hf : sl.live = false) :
    ResolveStep j h m L .fail ∧ ∀ o, ResolveStep j h m L o → o = .fail :=
  pool_resolve_invalid_fails hp (not_handleOK_free hsl hf)

/-- An invalid handle, a handle of a dead pool included, makes `freeSlot` fail, before the right is
checked, and `fail` is its only outcome (HandlePool v0.5, D.3: "`fail` si l'identité ou la
génération ne correspond pas; un slot déjà libre n'est pas rendu libérable par cette seule
égalité"; HP5-1''; §58, §89). -/
theorem pool_freeSlot_invalid_fails {L : PState} {j : Nat} {pl : Pool} {h : Handle}
    (hp : L.pools[j]? = some pl) (hH : ¬ HandleOK L.kern pl h) :
    FreeSlotStep j h L .fail ∧ ∀ o, FreeSlotStep j h L o → o = .fail := by
  refine ⟨.fail hp hH, fun o ho => ?_⟩
  cases ho with
  | noPool hn => rw [hp] at hn; cases hn
  | fail => rfl
  | noRight hp' hH' => rw [hp] at hp'; cases hp'; exact absurd hH' hH
  | noContent hp' hH' => rw [hp] at hp'; cases hp'; exact absurd hH' hH
  | ok hp' hH' => rw [hp] at hp'; cases hp'; exact absurd hH' hH

/-- `freeSlot` of a stale handle, of a handle of another pool, or of a free slot at its generation
fails, whatever the right (HandlePool v0.5, D.3, HP5-1''; §58, §89). -/
theorem pool_freeSlot_stale_other_free_fails {L : PState} {j : Nat} {pl : Pool} {h : Handle}
    {sl : Slot} (hp : L.pools[j]? = some pl) (hsl : pl.slots[h.slot]? = some sl) :
    (sl.gen ≠ h.gen ∨ h.id ≠ pl.id ∨ sl.live = false) →
      FreeSlotStep j h L .fail ∧ ∀ o, FreeSlotStep j h L o → o = .fail := by
  rintro (hg | hid | hf)
  · exact pool_freeSlot_invalid_fails hp (not_handleOK_stale hsl hg)
  · exact pool_freeSlot_invalid_fails hp (not_handleOK_other hid)
  · exact pool_freeSlot_invalid_fails hp (not_handleOK_free hsl hf)

/-- A handle of a dead pool (`internal` inactive) is stale: `freeSlot` fails (HandlePool v0.5,
HP5-1''; §89). -/
theorem pool_freeSlot_dead_fails {L : PState} {j : Nat} {pl : Pool} {h : Handle}
    (hp : L.pools[j]? = some pl) (hd : ¬ L.kern.Active pl.internal) :
    FreeSlotStep j h L .fail ∧ ∀ o, FreeSlotStep j h L o → o = .fail :=
  pool_freeSlot_invalid_fails hp (not_handleOK_dead hd)

/-- A missing pool index makes `freeSlot` reject, and `reject` is its only outcome
(HandlePool v0.5, HP5-1''; §58). -/
theorem pool_freeSlot_missing_rejects {L : PState} {j : Nat} {h : Handle}
    (hn : L.pools[j]? = none) : ∀ o, FreeSlotStep j h L o → o = .reject := by
  intro o ho
  cases ho with
  | noPool => rfl
  | fail hp => cases hp.symm.trans hn
  | noRight hp => cases hp.symm.trans hn
  | noContent hp => cases hp.symm.trans hn
  | ok hp => cases hp.symm.trans hn

/-- With a valid handle, `freeSlot` without the administration right rejects, and `reject` is its
only outcome (HandlePool v0.5, D.3 corrected by §36, HP5-1''; §58). -/
theorem pool_freeSlot_noRight_rejects {L : PState} {j : Nat} {pl : Pool} {h : Handle}
    (hp : L.pools[j]? = some pl) (hH : HandleOK L.kern pl h) (hR : ¬ AdminRight L.kern pl) :
    FreeSlotStep j h L .reject ∧ ∀ o, FreeSlotStep j h L o → o = .reject := by
  refine ⟨.noRight hp hH hR, fun o ho => ?_⟩
  cases ho with
  | noPool => rfl
  | fail hp' hn => rw [hp] at hp'; cases hp'; exact absurd hH hn
  | noRight => rfl
  | noContent => rfl
  | ok hp' _ hR' => rw [hp] at hp'; cases hp'; exact absurd hR' hR

/-- With a valid handle and the administration right, `freeSlot` rejects when the content
conditions fail, and `reject` is its only outcome (HandlePool v0.5, HP5-1, HP5-1', HP5-1''; §58). -/
theorem pool_freeSlot_content_rejects {L : PState} {j : Nat} {pl : Pool} {h : Handle} {sl : Slot}
    (hp : L.pools[j]? = some pl) (hH : HandleOK L.kern pl h) (hR : AdminRight L.kern pl)
    (hsl : pl.slots[h.slot]? = some sl) (hc : ¬ FreeContentOK L pl sl.place) :
    FreeSlotStep j h L .reject ∧ ∀ o, FreeSlotStep j h L o → o = .reject := by
  refine ⟨.noContent hp hH hR hsl hc, fun o ho => ?_⟩
  cases ho with
  | noPool => rfl
  | fail hp' hn => rw [hp] at hp'; cases hp'; exact absurd hH hn
  | noRight => rfl
  | noContent => rfl
  | ok hp' _ _ hsl' hc' =>
    rw [hp] at hp'; cases hp'; rw [hsl] at hsl'; cases hsl'; exact absurd hc' hc

/-! ## `resolveMany`: atomicity and distinctness (HandlePool v0.5, D.2, HP5-5) -/

/-- An invalid batch makes `resolveMany` fail, before the right is checked, and `fail` is its only
outcome: no partial creation of rights (HandlePool v0.5, D.2: "`fail` atomique"; HP5-5; §58). -/
theorem pool_resolveMany_invalid_fails {k : K} {L : PState} {j : Nat} {pl : Pool}
    {hs : List Handle} {m : Mode} (hp : L.pools[j]? = some pl) (hB : ¬ BatchOK L.kern pl hs m) :
    ResolveManyStep k j hs m L .fail ∧ ∀ o, ResolveManyStep k j hs m L o → o = .fail := by
  refine ⟨.fail hp hB, fun o ho => ?_⟩
  cases ho with
  | noPool hn => rw [hp] at hn; cases hn
  | fail => rfl
  | noRight hp' hB' => rw [hp] at hp'; cases hp'; exact absurd hB' hB
  | noEntries hp' hB' => rw [hp] at hp'; cases hp'; exact absurd hB' hB
  | ok hp' hB' => rw [hp] at hp'; cases hp'; exact absurd hB' hB

/-- A missing pool index makes `resolve` and `resolveMany` reject, and `reject` is their only
outcome (HandlePool v0.5, HP5-5: "A missing pool index stays `reject`"; §58). -/
theorem pool_resolve_missing_rejects {k : K} {L : PState} {j : Nat} (hn : L.pools[j]? = none) :
    (∀ h m o, ResolveStep j h m L o → o = .reject) ∧
      ∀ hs m o, ResolveManyStep k j hs m L o → o = .reject := by
  refine ⟨fun h m o ho => ?_, fun hs m o ho => ?_⟩
  · cases ho with
    | noPool => rfl
    | fail hp => cases hp.symm.trans hn
    | noRight hp => cases hp.symm.trans hn
    | noEntry hp => cases hp.symm.trans hn
    | ok hp => cases hp.symm.trans hn
  · cases ho with
    | noPool => rfl
    | fail hp => cases hp.symm.trans hn
    | noRight hp => cases hp.symm.trans hn
    | noEntries hp => cases hp.symm.trans hn
    | ok hp => cases hp.symm.trans hn

/-- `pool_resolveMany_atomic` (HandlePool v0.5, D.2, HP5-5): an invalid handle, a handle of a dead
pool included, makes the whole batch fail; an accepted batch creates exactly one companion and one
entry authority per handle, each derived from the companion, in one step (§58, §60, §61). -/
theorem pool_resolveMany_atomic {k : K} {L L' : PState} {j : Nat} {pl : Pool} {hs : List Handle}
    {m : Mode} :
    (L.pools[j]? = some pl → (∃ h ∈ hs, ¬ HandleOK L.kern pl h) →
      ∀ o, ResolveManyStep k j hs m L o → o = .fail) ∧
    (ResolveManyStep k j hs m L (.ok L') → ∃ pl', L.pools[j]? = some pl' ∧
      BatchOK L.kern pl' hs m ∧
      L'.kern.A = L.kern.A ++
        ⟨m, some pl'.internal, footprint L.kern.P pl'.storage, .frame L.kern.top, true⟩ ::
          hs.map fun h => ⟨m, some L.kern.A.length, footprint L.kern.P (slotPlace pl' h.slot),
            .frame L.kern.top, true⟩) := by
  refine ⟨fun hp ⟨h, hh, hn⟩ => (pool_resolveMany_invalid_fails hp
    fun hB => hn (hB.1 h hh)).2, fun hst => ?_⟩
  cases hst with
  | @ok pl' hp hB _ _ => exact ⟨pl', hp, hB, resolveMany_A m L.kern pl' hs⟩

/-- `pool_resolveMany_distinct` (HandlePool v0.5, D.2: distinctness is checked in `Modify` only):
in `Modify`, a repeated slot makes the batch fail and an accepted batch has distinct slots; in
`Observe`, validity does not depend on distinctness, so a repeated valid handle never makes the
batch fail (§58, §61). -/
theorem pool_resolveMany_distinct {k : K} {L L' : PState} {j : Nat} {pl : Pool}
    {hs : List Handle} :
    (L.pools[j]? = some pl → ¬ (hs.map (·.slot)).Nodup →
      ∀ o, ResolveManyStep k j hs .modify L o → o = .fail) ∧
    (ResolveManyStep k j hs .modify L (.ok L') → (hs.map (·.slot)).Nodup) ∧
    (BatchOK L.kern pl hs .observe ↔ ∀ h ∈ hs, HandleOK L.kern pl h) ∧
    (L.pools[j]? = some pl → (∀ h ∈ hs, HandleOK L.kern pl h) →
      ∀ o, ResolveManyStep k j hs .observe L o → o ≠ .fail) := by
  refine ⟨fun hp hd => (pool_resolveMany_invalid_fails hp fun hB => hd (hB.2 rfl)).2,
    fun h => ?_, ⟨fun h => h.1, fun h => ⟨h, fun e => by cases e⟩⟩, fun hp hv o ho => ?_⟩
  · cases h with
    | ok _ hB _ _ => exact hB.2 rfl
  · cases ho with
    | fail hp' hB => rw [hp] at hp'; cases hp'; exact absurd ⟨hv, fun e => by cases e⟩ hB
    | _ => exact fun e => by cases e

/-! ## The composite borrow (HandlePool v0.5, D.2) -/

/-- The composite borrow of `resolve` (HandlePool v0.5, D.2: "dérive de `internal` une autorité
compagne couvrant toutes les feuilles du stockage … puis dérive de cette compagne une autorité de
même mode"): in the arrival state, the companion `|A|` has origin `internal` and covers the
storage, the entry `|A| + 1` has origin the companion and covers the slot, both at mode `m`, and
the origin chain of the entry is the companion, `internal` and the chain of `internal` (§42, §60).
-/
theorem resolve_composite {L L' : PState} {j : Nat} {h : Handle} {m : Mode}
    (hst : ResolveStep j h m L (.ok L')) :
    ∃ pl sl, L.pools[j]? = some pl ∧ pl.slots[h.slot]? = some sl ∧ HandleOK L.kern pl h ∧
      L'.kern.A[L.kern.A.length]? =
        some ⟨m, some pl.internal, footprint L.kern.P pl.storage, .frame L.kern.top, true⟩ ∧
      L'.kern.A[L.kern.A.length + 1]? =
        some ⟨m, some L.kern.A.length, footprint L.kern.P sl.place, .frame L.kern.top, true⟩ ∧
      L'.kern.ancs (L.kern.A.length + 1) =
        L.kern.A.length :: pl.internal :: L.kern.ancs pl.internal := by
  cases hst with
  | @ok pl sl hp hH hR hsl _ =>
    have hAe := resolve_A L.kern pl m (footprint L.kern.P sl.place)
    obtain ⟨xi, hxi, -⟩ := hR.active
    have hilt := lt_of_getElem? hxi
    refine ⟨pl, sl, hp, hsl, hH, by rw [hAe]; simp, by rw [hAe]; simp, ?_⟩
    have hlen : (compS L.kern pl m).A.length = L.kern.A.length + 1 := by
      simp [compS, deriveEff, S3.addAuth]
    show ((compS L.kern pl m).addAuth _).ancs (L.kern.A.length + 1) = _
    rw [← hlen, ancs_addAuth_self rfl (by rw [hlen]; exact Nat.lt_succ_self _)]
    exact congrArg _ (ancs_addAuth_self rfl hilt)

/-! ## `freeSlot` (HandlePool v0.5, HP5-1, HP5-3, HP5-6) -/

/-- The effect of an accepted `freeSlot` (HandlePool v0.5, HP5-1): the pool exists with the
administration right, the handle is valid, and the content conditions hold; the arrival state is
`freeSlotEff`, whose kernel state is the write of the metadata leaves (§67 effect), whose
resolutions are those of the departure state (no end-of-use effect; §36, §58), and whose slot is
free with its generation incremented. -/
theorem freeSlot_effect {L L' : PState} {j : Nat} {h : Handle}
    (hst : FreeSlotStep j h L (.ok L')) :
    ∃ pl sl, L.pools[j]? = some pl ∧ pl.slots[h.slot]? = some sl ∧ AdminRight L.kern pl ∧
      HandleOK L.kern pl h ∧ FreeContentOK L pl sl.place ∧ L' = freeSlotEff L j pl h.slot sl ∧
      L'.kern = write3Eff L.kern (metaLeaves L.kern pl) ∧ L'.res = L.res ∧
      L'.pools[j]? = some (setSlot pl h.slot ⟨sl.place, sl.gen + 1, false⟩) := by
  cases hst with
  | @ok pl sl hp hH hR hsl hc =>
    exact ⟨pl, sl, hp, hsl, hR, hH, hc, rfl, rfl, rfl, getElem?_set_eq' hp⟩

/-- After an accepted `freeSlot(h)`, the freed slot is free with generation `h.gen + 1`, and `h` is
stale: `resolve` of `h`, and `resolveMany` of any batch containing `h`, fail (HandlePool v0.5,
HP5-6; §89). -/
theorem pool_freeSlot_then_stale {k : K} {L L' : PState} {j : Nat} {h : Handle}
    (hst : FreeSlotStep j h L (.ok L')) :
    (∃ pl' sl', L'.pools[j]? = some pl' ∧ pl'.slots[h.slot]? = some sl' ∧ sl'.live = false ∧
      sl'.gen = h.gen + 1) ∧
    (∀ m o, ResolveStep j h m L' o → o = .fail) ∧
    (∀ hs m o, h ∈ hs → ResolveManyStep k j hs m L' o → o = .fail) := by
  cases hst with
  | @ok pl sl hp hH _ hsl _ =>
    have hp' := getElem?_set_eq' (x := setSlot pl h.slot ⟨sl.place, sl.gen + 1, false⟩) hp
    have hs' := getElem?_set_eq' (x := (⟨sl.place, sl.gen + 1, false⟩ : Slot)) hsl
    have hn : ¬ HandleOK (freeSlotEff L j pl h.slot sl).kern
        (setSlot pl h.slot ⟨sl.place, sl.gen + 1, false⟩) h := not_handleOK_free hs' rfl
    obtain ⟨-, -, ho⟩ := hH
    rw [hsl] at ho
    exact ⟨⟨_, _, hp', hs', rfl, by rw [ho.1]⟩, fun m => (pool_resolve_invalid_fails hp' hn).2,
      fun hs m o hh => (pool_resolveMany_invalid_fails hp' fun hB => hn (hB.1 h hh)).2 o⟩

/-- A write that sets only `Init` leaves is the identity on the kernel state (§67 effect, §41). -/
theorem write3Eff_of_init {s : S3} {ls : List Nat} (h : ∀ l ∈ ls, s.I l = .init) :
    write3Eff s ls = s := by
  have e : (fun p => if p ∈ ls then InitSt.init else s.I p) = s.I :=
    funext fun p => by
      by_cases hp : p ∈ ls
      · simp only [hp, ↓reduceIte]; exact (h p hp).symm
      · simp only [hp, ↓reduceIte]
  unfold write3Eff; rw [e]

/-- HandlePool v0.5, HP5-3 (mandatory proof (2) of arbitration Q3): the metadata update of
`freeSlot` (free state, generation) is realizable by an authorized write under the administration
right. On every library-reachable state, under `DDSound` (§80) and `StaticsOK` (§47), for every
pool with `AdminRight` (§36), the pool value `v` (the place holding `internal`) exists and the
kernel `write` (§67) of the leaves of `v` through the authority grounding `MetaRight` is accepted;
when the leaves of `v` are `Init`, its effect is the identity on the kernel state. This write is the
kernel part of an accepted `freeSlot` (`freeSlotEff`, `freeSlot_meta_leaves`). §76.5 requires `Init`
leaves only when the pool is created: on a library-reachable state with `AdminRight`, a leaf of `v`
can be `Moved`, and the write of an accepted `freeSlot` then makes it `Init`
(`Witness.meta_write_not_identity`, `freeSlot_kernel_write`). -/
theorem freeSlot_meta_write {k : K} {statics : Statics} (hdd : DDSound k)
    (hst : StaticsOK statics) {L : PState} (hr : PReach k statics L) {pl : Pool}
    (hR : AdminRight L.kern pl) :
    ∃ v a, Arena.arenaValue L.kern pl.entry = some v ∧
      Write3Step a (footprint L.kern.P v) L.kern (.ok (write3Eff L.kern (footprint L.kern.P v))) ∧
      ((∀ l ∈ footprint L.kern.P v, L.kern.I l = .init) →
        write3Eff L.kern (footprint L.kern.P v) = L.kern) := by
  have hk := kernel_guarantee hdd hst L hr
  obtain ⟨⟨y, hy, ya⟩, hm⟩ := hR
  unfold Arena.MetaRight at hm
  cases hv : Arena.arenaValue L.kern pl.entry with
  | none => rw [hv] at hm; exact (hm : False).elim
  | some v =>
    rw [hv] at hm
    obtain ⟨a, -, hex, hall⟩ : HasRight L.kern .modify v := hm
    have hhold : y.holder = .place v := by
      simp only [Arena.arenaValue, Pool.entry, hy] at hv
      revert hv; cases y.holder <;> simp
    have hu : L.kern.Usable v := by
      have := hk.1.holders _ y hy ya; rw [hhold] at this; exact this
    exact ⟨v, a, rfl, Guarded.ok (write_of_right hk hu hex hall fun _ h => h), write3Eff_of_init⟩

/-- HandlePool v0.5, HP5-1, proof (a): on every library-reachable state, under `DDSound` (§80) and
`StaticsOK` (§47), an accepted `freeSlot` identifies its metadata leaves exactly: `internal` is held
by the pool value `v` (§46 analogue), the metadata leaves are the leaves of `v` (§40), and the
kernel part of the step is the ordinary write (§67) of those leaves through an authority `a` on
which `MetaRight` rests, exercisable `Modify` with effective `Modify` over every leaf of `v`
(`Grounds`; §36, §43). -/
theorem freeSlot_meta_leaves {k : K} {statics : Statics} (hdd : DDSound k)
    (hst : StaticsOK statics) {L L' : PState} (hr : PReach k statics L) {j : Nat} {h : Handle}
    (hs : FreeSlotStep j h L (.ok L')) :
    ∃ pl v a, L.pools[j]? = some pl ∧ Arena.arenaValue L.kern pl.entry = some v ∧
      metaLeaves L.kern pl = footprint L.kern.P v ∧ Grounds L.kern .modify v a ∧
      Write3Step a (metaLeaves L.kern pl) L.kern (.ok L'.kern) := by
  cases hs with
  | @ok pl _ hp _ hR _ _ =>
    obtain ⟨v, a, hv, hml, hg, hw⟩ := meta_write_of_kinv (kernel_guarantee hdd hst L hr) hR
    exact ⟨pl, v, a, hp, hv, hml, hg, Guarded.ok hw⟩

/-- HandlePool v0.5, HP5-1, proof (b): the kernel state after an accepted `freeSlot` is exactly the
effect of the write of the metadata leaves, the leaves of the pool value `v` (§67 effect): every
metadata leaf is `Init`, with no hypothesis on its state before (`Moved` included, §41, §59), every
other leaf keeps its state, and the other kernel components are unchanged (§38, §58). -/
theorem freeSlot_kernel_write {L L' : PState} {j : Nat} {h : Handle}
    (hs : FreeSlotStep j h L (.ok L')) :
    ∃ pl v, L.pools[j]? = some pl ∧ Arena.arenaValue L.kern pl.entry = some v ∧
      metaLeaves L.kern pl = footprint L.kern.P v ∧
      L'.kern = write3Eff L.kern (metaLeaves L.kern pl) ∧
      (∀ l ∈ metaLeaves L.kern pl, L'.kern.I l = .init) ∧
      (∀ l, l ∉ metaLeaves L.kern pl → L'.kern.I l = L.kern.I l) ∧
      L'.kern.F = L.kern.F ∧ L'.kern.nF = L.kern.nF ∧ L'.kern.P = L.kern.P ∧
      L'.kern.A = L.kern.A ∧ L'.kern.D = L.kern.D ∧ L'.kern.dead = L.kern.dead ∧
      L'.kern.pins = L.kern.pins := by
  cases hs with
  | @ok pl _ hp _ hR _ _ =>
    obtain ⟨v, hv, -⟩ := optP_false_iff.1 hR.2
    refine ⟨pl, v, hp, hv, metaLeaves_of hv, rfl, fun l hl => ?_, fun l hl => ?_, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl⟩
    · show (write3Eff L.kern (metaLeaves L.kern pl)).I l = .init; simp [write3Eff, hl]
    · show (write3Eff L.kern (metaLeaves L.kern pl)).I l = L.kern.I l; simp [write3Eff, hl]

/-- HandlePool v0.5, HP5-1, proof (c): the abstract update of an accepted `freeSlot` frees the slot
with its generation incremented; the identity, storage, `internal` and other slots of the pool, the
other pools, the resolutions and the next pool identity are unchanged; no memory right is added (`A`
and `D` unchanged; §36: the library adds no rights to the kernel); the metadata leaves of the
updated pool are the written leaves, all `Init` (§46 analogue, §67). The correspondence of (c) holds
at the level of the written leaves and of their initialization state only: `S3` has no value
component (§38), so the values written (free state, generation) cannot be stated. -/
theorem freeSlot_abstract_update {L L' : PState} {j : Nat} {h : Handle}
    (hs : FreeSlotStep j h L (.ok L')) :
    ∃ pl sl pl', L.pools[j]? = some pl ∧ pl.slots[h.slot]? = some sl ∧
      pl' = setSlot pl h.slot ⟨sl.place, sl.gen + 1, false⟩ ∧ L'.pools[j]? = some pl' ∧
      pl'.slots[h.slot]? = some ⟨sl.place, sl.gen + 1, false⟩ ∧
      (∀ i, i ≠ h.slot → pl'.slots[i]? = pl.slots[i]?) ∧
      pl'.id = pl.id ∧ pl'.storage = pl.storage ∧ pl'.internal = pl.internal ∧
      (∀ n, n ≠ j → L'.pools[n]? = L.pools[n]?) ∧ L'.pools.length = L.pools.length ∧
      L'.res = L.res ∧ L'.nId = L.nId ∧ L'.kern.A = L.kern.A ∧ L'.kern.D = L.kern.D ∧
      metaLeaves L'.kern pl' = metaLeaves L.kern pl ∧
      ∀ l ∈ metaLeaves L'.kern pl', L'.kern.I l = .init := by
  cases hs with
  | @ok pl sl hp _ _ hsl _ =>
    refine ⟨pl, sl, _, hp, hsl, rfl, getElem?_set_eq' hp, getElem?_set_eq' hsl,
      fun i hi => getElem?_set_ne' hi, rfl, rfl, rfl, fun n hn => getElem?_set_ne' hn,
      List.length_set .., rfl, rfl, rfl, rfl, rfl, fun l hl => ?_⟩
    have hl' : l ∈ metaLeaves L.kern pl := hl
    show (write3Eff L.kern (metaLeaves L.kern pl)).I l = .init; simp [write3Eff, hl']

/-- HandlePool v0.5, HP5-1: on every library-reachable state, under `DDSound` (§80) and `StaticsOK`
(§47), the metadata leaves written by an accepted `freeSlot` are disjoint from the leaves of the
freed slot, whose states the write keeps (HP5-1: no leaf of the entry is `Init`). A shared leaf
would be covered by `internal` (§76.3: `footprint(internal) = footprint(storage)`), while the
authority on which `MetaRight` rests has effective `Modify` on it; by I1 (§50), either that
authority is `internal`, impossible along the holder chain of §43 since `internal` is held by the
pool value, or `internal` has no effective mode there, so an active strict descendant of `internal`
of own mode `Modify` covers the leaf (§43, case 3), which HP5-1' excludes. -/
theorem freeSlot_meta_disjoint {k : K} {statics : Statics} (hdd : DDSound k)
    (hst : StaticsOK statics) {L L' : PState} (hr : PReach k statics L) {j : Nat} {h : Handle}
    (hs : FreeSlotStep j h L (.ok L')) :
    ∃ pl sl, L.pools[j]? = some pl ∧ pl.slots[h.slot]? = some sl ∧
      (∀ l ∈ metaLeaves L.kern pl, l ∉ footprint L.kern.P sl.place) ∧
      ∀ l ∈ footprint L.kern.P sl.place, L'.kern.I l = L.kern.I l := by
  cases hs with
  | @ok pl sl hp _ hR hsl hc =>
    have hk := kernel_guarantee hdd hst L hr
    have hi1 : I1 L.kern := hk.2.1.1.1
    obtain ⟨v, a, hv, hml, ⟨-, hex, hall⟩, -⟩ := meta_write_of_kinv hk hR
    have hdis : ∀ l ∈ metaLeaves L.kern pl, l ∉ footprint L.kern.P sl.place := by
      intro l hl hlq
      rw [hml] at hl
      have hok := (pReach_poolWF hr).pools _ (List.mem_map_of_mem (List.mem_of_getElem? hp))
      have hin := hok.slotIn sl.place (List.mem_map_of_mem (List.mem_of_getElem? hsl)) l hlq
      obtain ⟨y, hy, ya⟩ := hR.1
      have hly : l ∈ y.footprint := by
        have := (hok.fpEq l).2 hin; simpa [Pool.shape, S3.afp, hy] using this
      have haM : effective L.kern a l = some .modify := Arena.allows_modify_iff.1 (hall l hl)
      by_cases hai : a = pl.internal
      · subst hai
        have hhold : y.holder = .place v := by
          simp only [Arena.arenaValue, Pool.entry, hy] at hv
          revert hv; cases y.holder <;> simp
        have key : ∀ x m, L.kern.ExercisableAt x m → m = .modify → x = pl.internal → False := by
          intro x m hx
          induction hx with
          | base hy' _ _ hf =>
            intro _ e; subst e; rw [hy] at hy'; cases hy'; rw [hhold] at hf; cases hf
          | @held x' p b _ y' hy' _ _ hp' _ hcb ih =>
            intro em e; subst e em; rw [hy] at hy'; cases hy'; rw [hhold] at hp'; cases hp'
            refine ih rfl (Decidable.byContradiction fun hb => ?_)
            have := effective_exclusive hi1 (Ne.symm hb) haM
            have hc' := hcb l hl
            rw [this] at hc'; exact hc'
        exact key _ _ hex rfl rfl
      · have hnone := effective_exclusive hi1 hai haM
        rw [effective_eq hy ya hly] at hnone
        have hmod : Mode.modify ∈ descModes L.kern pl.internal l := by
          unfold effOf at hnone
          split at hnone
          · cases hnone
          · split at hnone
            · assumption
            · cases hnone
        obtain ⟨c, z, hz, za, hlz, hanc, -⟩ := mem_descModes.1 hmod
        exact hc.noDesc c (List.mem_range.2 (lt_of_getElem? hz)) ⟨z, hz, za⟩ hanc l
          (by simp [S3.afp, hz, hlz]) hlq
    refine ⟨pl, sl, hp, hsl, hdis, fun l hl => ?_⟩
    have hn : l ∉ metaLeaves L.kern pl := fun h => hdis l h hl
    show (write3Eff L.kern (metaLeaves L.kern pl)).I l = L.kern.I l
    simp [write3Eff, hn]

/-- HandlePool v0.5, D.1 and HP5-1: on every library-reachable state, under `DDSound` (§80) and
`StaticsOK` (§47), no leaf of an entry of a live pool (`internal` active, §46 analogue) is a
metadata leaf, a leaf of the pool value. An entry lies in the storage (D.1), whose leaves are those
of `internal` (§76.3, `PoolOK.fpEq`); a shared leaf would make `internal` `SelfLock` (§63.8), which
`NoSelfLock` excludes on reachable states (§63.8, §65.3; `reachable_noSelfLock`). No ownership of
the storage by the pool value is assumed (§46). -/
theorem pool_entries_meta_disjoint {k : K} {statics : Statics} (hdd : DDSound k)
    (hst : StaticsOK statics) {L : PState} (hr : PReach k statics L) {pl : Pool}
    (hpl : pl ∈ L.pools) (ha : L.kern.Active pl.internal) {sl : Slot} (hsl : sl ∈ pl.slots) :
    ∀ l ∈ footprint L.kern.P sl.place, l ∉ metaLeaves L.kern pl := by
  intro l hlq hl
  have hok := (pReach_poolWF hr).pools _ (List.mem_map_of_mem hpl)
  have hin := hok.slotIn sl.place (List.mem_map_of_mem hsl) l hlq
  obtain ⟨y, hy, ya⟩ := ha
  have hly : l ∈ y.footprint := by
    have := (hok.fpEq l).2 hin; simpa [Pool.shape, S3.afp, hy] using this
  unfold metaLeaves at hl
  cases hv : Arena.arenaValue L.kern pl.entry with
  | none => rw [hv] at hl; simp at hl
  | some v =>
    rw [hv] at hl
    have hhold : y.holder = .place v := by
      simp only [Arena.arenaValue, Pool.entry, hy] at hv
      revert hv; cases y.holder <;> simp
    exact (reachable_noSelfLock hdd hst (pReach_reachable hdd hst hr)).elim hy ya hly
      (by rw [hhold]; exact hl)

/-! ## Rights required by `allocSlot`, `freeSlot`, `newPool` (HandlePool v0.5, D.1, D.3) -/

/-- `allocSlot` requires a live pool and `MetaRight`, exercisable `Modify` over the pool value
(HandlePool v0.5, D.3 corrected by §36). Its effect writes only `dst`, makes the chosen free slot
live with its generation kept, and changes no other slot (D.3). -/
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
(HandlePool v0.5, D.3 corrected by §36, HP5-1). -/
theorem freeSlot_requires {L L' : PState} {j : Nat} {h : Handle}
    (hst : FreeSlotStep j h L (.ok L')) :
    ∃ pl, L.pools[j]? = some pl ∧ L.kern.Active pl.internal ∧ Arena.MetaRight L.kern pl.entry := by
  obtain ⟨pl, -, hp, -, hR, -⟩ := freeSlot_effect hst
  exact ⟨pl, hp, hR⟩

/-- `newPool` requires `Uninit` storage, the obligations of `newArena` (`NewArenaBase`: §76.1–§76.3,
§76.5, §76.6) and the guard of §56 over the pool registry and every other registry of live
administrations, and changes no kernel component (HandlePool v0.5, D.1; §56, §76). -/
theorem newPool_requires {others : List (List Nat)} {st i : Nat} {L L' : PState}
    (h : NewPoolStep others st i L (.ok L')) :
    (∀ l ∈ footprint L.kern.P st, L.kern.I l = .uninit) ∧
      Arena.Guard56 (liveInternals L.kern L.pools :: others) i ∧
      Arena.NewArenaBase L.kern st i ∧ L'.kern = L.kern := by
  obtain ⟨hp, rfl⟩ := Guarded.ok_iff.1 h
  exact ⟨hp.uninit, hp.guard, hp.base, rfl⟩

/-! ## Uniqueness of live administration in the pool registry (§56) -/

/-- §56 for the pool registry (HandlePool v0.5, D.1: "Une autorité ne peut être `internal` de deux
abstractions vivantes"): two live pools at distinct positions have distinct `internal`. -/
def Unique56 (L : PState) : Prop :=
  ∀ (a b : Nat) (pa pb : Pool), a ≠ b → L.pools[a]? = some pa → L.pools[b]? = some pb →
    L.kern.Active pa.internal → L.kern.Active pb.internal → pa.internal ≠ pb.internal

/-- Every registered `internal` exists (§42; HandlePool v0.5, D.1; auxiliary). -/
def RegOK (L : PState) : Prop := ∀ pl ∈ L.pools, pl.internal < L.kern.A.length

/-- A step that keeps the authorities and the `internal` of every registered pool keeps `Unique56`
and `RegOK` (§56; HandlePool v0.5, D.1; authorities are never reactivated, §42). -/
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

/-- Replacing a slot keeps the `internal` at every position (HandlePool v0.5, D.3; §56). -/
theorem internals_set {pools : List Pool} {j i : Nat} {pl : Pool} {x : Slot}
    (hj : pools[j]? = some pl) (n : Nat) :
    ((pools.set j (setSlot pl i x))[n]?).map Pool.internal = (pools[n]?).map Pool.internal := by
  by_cases hn : n = j
  · subst hn; rw [getElem?_set_eq' hj, hj]; rfl
  · rw [getElem?_set_ne' hn]

/-- `newPool` keeps `Unique56` and `RegOK` (§56, §76.4; HandlePool v0.5, D.1): the guard excludes
the `internal` of every live registered pool. -/
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

/-- `live_pool_internal_unique` (§56; HandlePool v0.5, D.1): on every library-reachable state, two
live pools at distinct positions of the registry have distinct `internal`. The guard of `newPool`
gives it; no kernel invariant is needed. -/
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
      | ok hj _ _ _ _ => exact unique56_keep hu hr (Arena.akeep_of_eq rfl) (internals_set hj)
    | newPool hs => exact unique56_newPool hu hr hs

/-! ## Witnesses on library-reachable states (HandlePool v0.5, D.2, D.3, HP5-2)

Runs from `PState.init Witness.hst` under the test contract `Examples.K0` (§48). Statics (§47):
place 0 is the pool storage, with two leaf children 1 and 2 (`Uninit`); place 3 is the pool value
(`Init`); place 4 is a destination (`Uninit`); root authorities 0, 1 and 2 cover places 0, 3 and 4.
`internal` is authority 3, derived from 0 over `[1, 2]` and stored in place 3. Every precondition is
decided by `decide`. -/

namespace Witness

open Examples

/-- Statics of the witnesses (§47; HandlePool v0.5, D.1). -/
def hst : Statics :=
  [((none, none, 0), false), ((some 0, none, 0), false), ((some 0, none, 0), false),
    ((none, none, 0), true), ((none, none, 0), false)]

/-- Initial library state (§47; HandlePool v0.5). -/
def w0 : PState := PState.init hst

/-- After `derive(0, [1, 2], Modify)` (§60): authority 3, the future `internal`
(HandlePool v0.5, D.1). -/
def w1 : PState := { w0 with kern := deriveEff w0.kern 0 [1, 2] .modify }

/-- After `store(3, 3)` (§65): `internal` is held by the pool value, place 3 (HandlePool v0.5,
D.1). -/
def w2 : PState := { w1 with kern := storeEff w1.kern 3 3 }

/-- After `newPool(0, 3)` (HandlePool v0.5, D.1): pool 0 with slots 1 and 2, free, of generation 0
(§47). -/
def w3 : PState := newPoolEff w2 0 3

/-- Pool 0 after `newPool` (HandlePool v0.5, D.1; §47). -/
def pl3 : Pool := ⟨0, 0, 3, [⟨1, 0, false⟩, ⟨2, 0, false⟩]⟩

/-- After `allocSlot(0, 4)` on slot 0 (HandlePool v0.5, D.3): the handle `⟨0, 0, 0⟩` is written
into place 4 (§47, §67). -/
def w4 : PState := allocSlotEff w3 0 pl3 0 ⟨1, 0, false⟩ 4

/-- Pool 0 after `allocSlot` (HandlePool v0.5, D.3; §47). -/
def pl4 : Pool := ⟨0, 0, 3, [⟨1, 0, true⟩, ⟨2, 0, false⟩]⟩

/-- `newPool(0, 3)` is accepted on `w2` (HandlePool v0.5, D.1; §56, §76). -/
theorem w3_step : NewPoolStep [] 0 3 w2 (.ok w3) := Guarded.ok (by decide)

/-- `allocSlot(0, 4)` is accepted on `w3`, on slot 0 (HandlePool v0.5, D.3; §67). -/
theorem w4_step : AllocSlotStep 0 4 w3 (.ok w4) := .ok (pl := pl3) rfl (by decide) rfl rfl

/-- `w3` is library-reachable (§47, §60, §65; HandlePool v0.5, D.1). -/
theorem w3_reach : PReach K0 hst w3 :=
  .step (.step (.step .init (.kernel (.derive (Guarded.ok (by decide)))))
    (.kernel (.store (Guarded.ok (by decide))))) (.newPool w3_step)

/-- `w4` is library-reachable (HandlePool v0.5, D.3; §47, §67). -/
theorem w4_reach : PReach K0 hst w4 := .step w3_reach (.allocSlot w4_step)

/-- `resolveMany` in `Observe` accepts a repeated valid handle (HandlePool v0.5, D.2: "la
répétition du même handle valide est permise"): two `Observe` entry authorities on slot 0, derived
from one `Observe` companion; the same batch in `Modify` fails (§60). -/
theorem observe_repeat_ok :
    (∃ L', ResolveManyStep K0 0 [⟨0, 0, 0⟩, ⟨0, 0, 0⟩] .observe w4 (.ok L') ∧ PReach K0 hst L' ∧
      L'.res = [⟨0, 3, 4, .observe, [(5, 0, 0), (6, 0, 0)]⟩]) ∧
    ∀ o, ResolveManyStep K0 0 [⟨0, 0, 0⟩, ⟨0, 0, 0⟩] .modify w4 o → o = .fail := by
  have hok : ResolveManyStep K0 0 [⟨0, 0, 0⟩, ⟨0, 0, 0⟩] .observe w4 (.ok _) :=
    .ok (pl := pl4) rfl (by decide) (by decide) (by decide)
  exact ⟨⟨_, hok, .step w4_reach (.resolveMany hok), rfl⟩,
    (pool_resolveMany_distinct (L' := w4) (pl := pl4)).1 rfl (by decide)⟩

/-- Contract problem (HandlePool v0.5, D.3: "Le contenu du slot demeure `Uninit` jusqu'à son
écriture ; l'écriture du handle dans `dst` n'initialise pas le slot"): the preconditions of
`allocSlot` do not exclude a destination inside the allocated slot. On `w3`, `allocSlot(0, 1)` is
accepted on slot 0, whose place is 1: the slot becomes live and its content `Init` (§67). -/
theorem allocSlot_into_own_slot :
    ∃ L', AllocSlotStep 0 1 w3 (.ok L') ∧ PReach K0 hst L' ∧
      L'.pools[0]? = some pl4 ∧ L'.kern.I 1 = .init := by
  have hok : AllocSlotStep 0 1 w3 (.ok (allocSlotEff w3 0 pl3 0 ⟨1, 0, false⟩ 1)) :=
    .ok rfl (by decide) rfl rfl
  exact ⟨_, hok, .step w3_reach (.allocSlot hok), rfl, by decide⟩

/-- Contract problem (HandlePool v0.5, D.1: "Les entrées libres sont `Uninit`"): free entries are
not `Uninit` in every library-reachable state. On `w3`, a frame with `Modify` over the pool value
derives from `internal` over slot place 1 (O1, §60) and writes it (O10, §67): slot 0 stays free
while its content is `Init`. -/
theorem free_slot_init :
    ∃ L, PReach K0 hst L ∧ L.pools[0]? = some pl3 ∧ L.kern.I 1 = .init := by
  have h₁ : PStep K0 w3 { w3 with kern := deriveEff w3.kern 3 [1] .modify } :=
    .kernel (.derive (Guarded.ok (by decide)))
  have h₂ : PStep K0 { w3 with kern := deriveEff w3.kern 3 [1] .modify }
      { w3 with kern := write3Eff (deriveEff w3.kern 3 [1] .modify) [1] } :=
    .kernel (.write (a := 4) (Guarded.ok (by decide)))
  exact ⟨_, .step (.step w3_reach h₁) h₂, rfl, by decide⟩

/-! ### `freeSlot` after the transfer of the entry's value to a local (HandlePool v0.5, HP5-2)

From `w4`, the run passes a `Modify` authority over the pool value to a new frame 1, which creates
the local leaf 5 (§72); frame 1 resolves the handle `⟨0, 0, 0⟩` in `Modify`, writes slot place 1
through the entry authority, transfers its value to the local, unresolves, and frees the slot. -/

/-- After `derive(1, [3], Modify)` from the root authority of the pool value (§60): authority 4,
the parameter of the next frame (HandlePool v0.5, HP5-2). -/
def x1 : PState := { w4 with kern := deriveEff w4.kern 1 [3] .modify }

/-- After `enterFrame([4], [(none, 0)])` (§72): frame 1 holds authority 4 and owns the local leaf
5, with its root authority 5 (HandlePool v0.5, HP5-2). -/
def x2 : PState := { x1 with kern := enterEff x1.kern [4] [(none, 0)] }

/-- After `resolve(0, ⟨0, 0, 0⟩, Modify)` in frame 1 (HandlePool v0.5, D.2): the companion 6 over
the storage and the entry authority 7 over slot place 1 (§60). -/
def x3 : PState := { x2 with
  kern := deriveEff (compS x2.kern pl4 .modify) x2.kern.A.length (footprint x2.kern.P 1) .modify
  res := x2.res ++ [⟨pl4.id, pl4.internal, x2.kern.A.length, .modify,
    [(x2.kern.A.length + 1, 0, 0)]⟩] }

/-- After the kernel `write` of slot place 1 through the entry authority 7 (§67; HandlePool v0.5,
HP5-2). -/
def x4 : PState := { x3 with kern := write3Eff x3.kern [1] }

/-- After the kernel `transfer(1, 5)` of the entry's value to the local (§63; HandlePool v0.5,
HP5-2): place 1 is `Moved`, place 5 `Init`. -/
def x5 : PState := { x4 with kern := transferEff x4.kern 1 5 }

/-- After `unresolve(6)` (HandlePool v0.5, D.2): `release` of the entry authority 7, then of the
companion 6 (§62). -/
def x6 : PState := { x5 with kern := releaseEff (releaseEff x5.kern 7) 6 }

/-- After `freeSlot(⟨0, 0, 0⟩)` (HandlePool v0.5, HP5-1): the metadata leaves, the leaves of the
pool value 3, are written (§67); slot 0 is free, of generation 1 (§38). -/
def x7 : PState := freeSlotEff x6 0 pl4 0 ⟨1, 0, true⟩

/-- HandlePool v0.5, HP5-2 (mandatory proof (1) of arbitration Q3 and its follow-up): from
`PState.init hst`, by accepted steps, `newPool`, `allocSlot`, `resolve` in `Modify`, a kernel
`write` of the entry through the entry authority (§67), the kernel `transfer` of the entry's value
to a local of the same shape (§63), `unresolve`, then `freeSlot` accepted. `internal` (authority 3)
is derived from the root authority of the storage (§60) and stored in the pool value, place 3
(§65). The local is place 5, created by `enterFrame` (§72) and owned by the current frame 1. The
transfer is accepted through the exemption of v0.1 §63.4: the entry authority 7, which grounds the
right over the source, its companion 6, `internal` 3 and its origin 0 cover the source from
outside it. `freeSlot` is accepted under the content condition of HP5-1': once 7 and 6 are released,
no active strict descendant of `internal` 3 covers slot place 1. In the arrival state, slot 0 is
free with generation 1, slot place 1 is `Moved` and the local is `Init`. -/
theorem freeSlot_after_transfer :
    NewPoolStep [] 0 3 w2 (.ok w3) ∧ AllocSlotStep 0 4 w3 (.ok w4) ∧
    ResolveStep 0 ⟨0, 0, 0⟩ .modify x2 (.ok x3) ∧ Write3Step 7 [1] x3.kern (.ok x4.kern) ∧
    TransferStep K0 1 5 x4.kern (.ok x5.kern) ∧ UnresolveStep 6 x5 (.ok x6) ∧
    FreeSlotStep 0 ⟨0, 0, 0⟩ x6 (.ok x7) ∧ PReach K0 hst x7 ∧
    x7.kern.A[3]? = some ⟨.modify, some 0, [1, 2], .place 3, true⟩ ∧
    x7.kern.P[5]? = some ⟨none, .frame 1, 0⟩ ∧ x7.kern.top = 1 ∧
    x7.kern.I 1 = .moved ∧ x7.kern.I 5 = .init ∧
    x7.pools[0]? = some ⟨0, 0, 3, [⟨1, 1, false⟩, ⟨2, 0, false⟩]⟩ := by
  have r3 : ResolveStep 0 ⟨0, 0, 0⟩ .modify x2 (.ok x3) :=
    .ok (pl := pl4) (sl := ⟨1, 0, true⟩) rfl (by decide) (by decide) rfl (by decide)
  have w4' : Write3Step 7 [1] x3.kern (.ok x4.kern) := Guarded.ok (by decide)
  have t5 : TransferStep K0 1 5 x4.kern (.ok x5.kern) := Guarded.ok (by decide)
  have hrel : releaseAll x5.kern (unresolveList x5.kern ⟨0, 3, 6, .modify, [(7, 0, 0)]⟩) =
      some x6.kern := by
    have e : unresolveList x5.kern ⟨0, 3, 6, .modify, [(7, 0, 0)]⟩ = [7, 6] := by decide
    have h7 : ReleasePre x5.kern 7 := by decide
    have h6 : ReleasePre (releaseEff x5.kern 7) 6 := by decide
    rw [e]; simp only [releaseAll, h7, h6, ↓reduceIte]; rfl
  have u6 : UnresolveStep 6 x5 (.ok x6) := .ok (r := ⟨0, 3, 6, .modify, [(7, 0, 0)]⟩) rfl hrel
  have f7 : FreeSlotStep 0 ⟨0, 0, 0⟩ x6 (.ok x7) :=
    .ok (pl := pl4) (sl := ⟨1, 0, true⟩) rfl (by decide) (by decide) rfl (by decide)
  have h2 : PReach K0 hst x2 := .step (.step w4_reach (.kernel (.derive (Guarded.ok (by decide)))))
    (.kernel (.enter (Guarded.ok (by decide))))
  have h7 : PReach K0 hst x7 :=
    .step (.step (.step (.step (.step h2 (.resolve r3)) (.kernel (.write w4')))
      (.kernel (.transfer t5))) (.unresolve u6)) (.freeSlot f7)
  exact ⟨w3_step, w4_step, r3, w4', t5, u6, f7, h7, by decide, by decide, rfl, by decide,
    by decide, by decide⟩

/-! ### `freeSlot` after a frame exit (HandlePool v0.5, D.4 (2), HP5-1'; §42, §73)

Statics `cst` (§47): place 0 is the pool storage with leaf children 1 and 2 (`Uninit`); place 3 is
the pool value (`Init`); place 4 is the handle destination; place 5 is a leaf of frame 0. Root
authorities 0 to 3 cover places 0, 3, 4 and 5. Frame 1 resolves the handle in `Modify`; the entry
authority is stored into place 5 of frame 0; at the exit of frame 1 the companion dies and the entry
authority is reanchored to `internal` (§73.4); `freeSlot` is then rejected (HP5-1'). -/

/-- Statics of the run (§47; HandlePool v0.5, D.1). -/
def cst : Statics :=
  [((none, none, 0), false), ((some 0, none, 0), false), ((some 0, none, 0), false),
    ((none, none, 0), true), ((none, none, 0), false), ((none, none, 0), false)]
/-- After `derive(0, [1, 2], Modify)` (§60): `internal` is authority 4 (HandlePool v0.5, D.1). -/
def c1 : PState := { PState.init cst with kern := deriveEff (PState.init cst).kern 0 [1, 2] .modify }
/-- After `store(4, 3)` (§65): `internal` is held by the pool value (HandlePool v0.5, D.1). -/
def c2 : PState := { c1 with kern := storeEff c1.kern 4 3 }
/-- After `newPool(0, 4)` (HandlePool v0.5, D.1; §76). -/
def c3 : PState := newPoolEff c2 0 4
/-- Pool 0 after `newPool` (HandlePool v0.5, D.1; §47). -/
def pA : Pool := ⟨0, 0, 4, [⟨1, 0, false⟩, ⟨2, 0, false⟩]⟩
/-- After `allocSlot(0, 4)`: the handle `⟨0, 0, 0⟩` is written into place 4 (HandlePool v0.5, D.3;
§67). -/
def c4 : PState := allocSlotEff c3 0 pA 0 ⟨1, 0, false⟩ 4
/-- Pool 0 after `allocSlot` (HandlePool v0.5, D.3; §47). -/
def pA4 : Pool := ⟨0, 0, 4, [⟨1, 0, true⟩, ⟨2, 0, false⟩]⟩
/-- After `derive(1, [3], Modify)`: authority 5 over the pool value (§60; HandlePool v0.5). -/
def c5 : PState := { c4 with kern := deriveEff c4.kern 1 [3] .modify }
/-- After `derive(3, [5], Modify)`: authority 6 over place 5 (§60; HandlePool v0.5). -/
def c6 : PState := { c5 with kern := deriveEff c5.kern 3 [5] .modify }
/-- After `enterFrame([5, 6], [])`: frame 1 (§72; HandlePool v0.5). -/
def c7 : PState := { c6 with kern := enterEff c6.kern [5, 6] [] }
/-- After `resolve(0, ⟨0, 0, 0⟩, Modify)` in frame 1: companion 7, entry authority 8 over slot
place 1 (HandlePool v0.5, D.2; §60). -/
def c8 : PState := { c7 with
  kern := deriveEff (compS c7.kern pA4 .modify) c7.kern.A.length (footprint c7.kern.P 1) .modify
  res := c7.res ++ [⟨pA4.id, pA4.internal, c7.kern.A.length, .modify,
    [(c7.kern.A.length + 1, 0, 0)]⟩] }
/-- After `store(8, 5)`: the entry authority is held by place 5 of frame 0 (HandlePool v0.5;
§65). -/
def c9 : PState := { c8 with kern := storeEff c8.kern 8 5 }
/-- After `exitFrame`: the companion 7 dies with frame 1; the entry authority 8 survives,
reanchored to `internal` 4 (§73; HandlePool v0.5). -/
def c10 : PState := { c9 with kern := exitEff c9.kern }
/-- The run of HP5-1' after a frame exit (HandlePool v0.5, D.4 (2), HP5-1'; non-normative library
contract): `c10` is library-reachable; the entry authority 8, recorded for slot 0 at generation 0,
is active `Modify` over slot place 1, held by place 5 of frame 0, with origin `internal` 4
(reanchored, §73.4) while its companion 7 is inactive; it is a strict descendant of `internal`
covering the slot, so `freeSlot(⟨0, 0, 0⟩)` rejects, and `reject` is its only outcome. -/
theorem no_stale_after_exit :
    PReach K0 cst c10 ∧ (⟨0, 4, 7, .modify, [(8, 0, 0)]⟩ : Res) ∈ c10.res ∧
    c10.kern.A[8]? = some ⟨.modify, some 4, [1], .place 5, true⟩ ∧ ¬ c10.kern.Active 7 ∧
    c10.pools[0]? = some pA4 ∧ 4 ∈ c10.kern.ancs 8 ∧
    FreeSlotStep 0 ⟨0, 0, 0⟩ c10 .reject ∧ ∀ o, FreeSlotStep 0 ⟨0, 0, 0⟩ c10 o → o = .reject := by
  have h3 : PReach K0 cst c3 :=
    .step (.step (.step .init (.kernel (.derive (Guarded.ok (by decide)))))
      (.kernel (.store (Guarded.ok (by decide))))) (.newPool (others := []) (Guarded.ok (by decide)))
  have h4 : PReach K0 cst c4 := .step h3 (.allocSlot (.ok (pl := pA) rfl (by decide) rfl rfl))
  have h7 : PReach K0 cst c7 :=
    .step (.step (.step h4 (.kernel (.derive (Guarded.ok (by decide)))))
      (.kernel (.derive (Guarded.ok (by decide))))) (.kernel (.enter (Guarded.ok (by decide))))
  have r8 : ResolveStep 0 ⟨0, 0, 0⟩ .modify c7 (.ok c8) :=
    .ok (pl := pA4) (sl := ⟨1, 0, true⟩) rfl (by decide) (by decide) rfl (by decide)
  have h10 : PReach K0 cst c10 := .step (.step (.step h7 (.resolve r8))
    (.kernel (.store (Guarded.ok (by decide))))) (.kernel (.exit (Guarded.ok (by decide))))
  exact ⟨h10, by decide, by decide, by decide, rfl, by decide,
    pool_freeSlot_content_rejects (sl := ⟨1, 0, true⟩) rfl (by decide) (by decide) rfl
      (by decide)⟩

/-! ### `freeSlot` on a pool value with a `Moved` leaf (HandlePool v0.5, HP5-1, HP5-3; §63, §67)

Statics `vst` (§47): place 0, the pool value, `Init`, with leaves 1 and 2; place 3, the storage,
owned by place 0, with `Uninit` leaves 4 and 5; places 6 and 7, `Uninit` leaves of frame 0, the
latter the handle destination. `internal` is the root authority 1 of the storage, held by its
owner, place 0. -/

/-- Statics of the run (§47; HandlePool v0.5, D.1). -/
def vst : Statics :=
  [((none, none, 0), true), ((some 0, none, 0), true), ((some 0, none, 0), true),
    ((none, some 0, 0), false), ((some 3, some 0, 0), false), ((some 3, some 0, 0), false),
    ((none, none, 0), false), ((none, none, 0), false)]
/-- After `newPool(3, 1)` (HandlePool v0.5, D.1; §76). -/
def m1 : PState := newPoolEff (PState.init vst) 3 1
/-- After the kernel `transfer(1, 6)` of leaf 1 of the pool value to place 6 (HandlePool v0.5;
§63). -/
def m2 : PState := { m1 with kern := transferEff m1.kern 1 6 }
/-- Pool 0 after `newPool` (HandlePool v0.5, D.1; §47). -/
def pv : Pool := ⟨0, 3, 1, [⟨4, 0, false⟩, ⟨5, 0, false⟩]⟩
/-- After `allocSlot(0, 7)` on slot 0: the handle `⟨0, 0, 0⟩` is written into place 7
(HandlePool v0.5, D.3; §67). -/
def m3 : PState := allocSlotEff m2 0 pv 0 ⟨4, 0, false⟩ 7
/-- Pool 0 after `allocSlot` (HandlePool v0.5, D.3; §47). -/
def pv3 : Pool := ⟨0, 3, 1, [⟨4, 0, true⟩, ⟨5, 0, false⟩]⟩
/-- After `freeSlot(⟨0, 0, 0⟩)`: the write of the leaves of the pool value, place 0 (§67), and slot
0 free at generation 1 (HandlePool v0.5, HP5-1). -/
def m4 : PState := freeSlotEff m3 0 pv3 0 ⟨4, 0, true⟩

/-- HandlePool v0.5, HP5-1 and HP5-3 (non-normative library contract): `m2` is library-reachable,
pool 0 has `AdminRight` (§36) and its value, place 0, has the `Moved` leaf 1 (§63); the write of the
leaves of the pool value (§67) that `freeSlot_meta_write` provides is then not the identity on the
kernel state. Continued by `allocSlot(0, 7)` and an accepted `freeSlot(⟨0, 0, 0⟩)`, this is a
conforming case: the arrival kernel state is the write of the leaves of the pool value on the
departure kernel state, it differs from it, and the `Moved` leaf 1 is `Init` after it; slot 0 is
free at generation 1. -/
theorem meta_write_not_identity :
    StaticsOK vst ∧ PReach K0 vst m2 ∧ m2.pools[0]? = some pv ∧ AdminRight m2.kern pv ∧
    Arena.arenaValue m2.kern pv.entry = some 0 ∧ m2.kern.I 1 = .moved ∧
    write3Eff m2.kern (footprint m2.kern.P 0) ≠ m2.kern ∧
    AllocSlotStep 0 7 m2 (.ok m3) ∧ FreeSlotStep 0 ⟨0, 0, 0⟩ m3 (.ok m4) ∧ PReach K0 vst m4 ∧
    Arena.arenaValue m3.kern pv3.entry = some 0 ∧ m3.kern.I 1 = .moved ∧
    m4.kern = write3Eff m3.kern (footprint m3.kern.P 0) ∧ m4.kern ≠ m3.kern ∧
    m4.kern.I 1 = .init ∧ m4.pools[0]? = some ⟨0, 3, 1, [⟨4, 1, false⟩, ⟨5, 0, false⟩]⟩ := by
  have hne : write3Eff m2.kern (footprint m2.kern.P 0) ≠ m2.kern := fun e => by
    have h1 := congrArg (fun s : S3 => s.I 1) e
    have : (write3Eff m2.kern (footprint m2.kern.P 0)).I 1 = .init := by decide
    have h2 : m2.kern.I 1 = .moved := by decide
    rw [this, h2] at h1; cases h1
  have h2 : PReach K0 vst m2 := .step (.step .init (.newPool (others := []) (Guarded.ok
    (by decide)))) (.kernel (.transfer (Guarded.ok (by decide))))
  have a3 : AllocSlotStep 0 7 m2 (.ok m3) := .ok (pl := pv) rfl (by decide) rfl rfl
  have f4 : FreeSlotStep 0 ⟨0, 0, 0⟩ m3 (.ok m4) :=
    .ok (pl := pv3) (sl := ⟨4, 0, true⟩) rfl (by decide) (by decide) rfl (by decide)
  have e4 : m4.kern = write3Eff m3.kern (footprint m3.kern.P 0) :=
    congrArg (write3Eff m3.kern) (by decide : metaLeaves m3.kern pv3 = footprint m3.kern.P 0)
  have i4 : m4.kern.I 1 = .init := by decide
  have i3 : m3.kern.I 1 = .moved := by decide
  exact ⟨by decide, h2, rfl, by decide, by decide, by decide, hne, a3, f4,
    .step (.step h2 (.allocSlot a3)) (.freeSlot f4), by decide, i3, e4,
    fun e => (by rw [e, i3] at i4; cases i4), i4, rfl⟩

end Witness

end Ern.Lib.HandlePool
