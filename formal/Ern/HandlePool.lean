import Ern.MM03

/-!
# Handle pool (jalon 3, step 1)

A library instance of the access discipline, like the arena (MM-03.3 §6): the handle pool of the
jalon-3 material (`ERN_Jalon3_materiel.md` v2, §4). A handle is data and carries no authority. A
resolution is a compound borrow made of kernel operations of `Ern.MM03`, which this module does
not modify: a companion derived from `internal` on the whole storage, then one entry authority per
resolved handle, derived from the companion (`derive` for `resolve`, `split` for `resolveMany`).
`unresolve` is a sequence of `release`, `freeSlot` an `endUse` of the entry content, `allocSlot` a
`write3` of the handle into its destination. The pool entries live beside the kernel state, like
the arena entries of MM-03.3.8 but outside `S3`, so the kernel is unchanged.

`PReach` extends `Reachable` (MM-03.3 §10) with the pool operations; every pool step is a chain of
kernel steps (`pReach_reachable`). Representation choices that the material does not fix are listed
in the jalon-3 report, (f).
-/

namespace Ern.HandlePool

open Ern.MM03

/-! ## State (material §4) -/

/-- Entry of a pool (material §4: `{place, gen : Nat, live : Bool}`): `place` is a part of the
pool storage. -/
structure Slot where
  place : Nat
  gen : Nat
  live : Bool
deriving DecidableEq, Repr

/-- Pool entry (material §4: `{id, storage, internal, slots}`), abstract like the arena entry of
MM-03.3.8. The pool value is not a field: it is the place that holds `internal` (material §4,
"même règle que F1"). -/
structure Pool where
  id : Nat
  storage : Nat
  internal : Nat
  slots : List Slot
deriving DecidableEq, Repr

/-- Handle (material §4: `(id, slot, gen)`): data of fixed size, no authority. -/
structure Handle where
  id : Nat
  slot : Nat
  gen : Nat
deriving DecidableEq, Repr

/-- Ghost record of a resolution (material §4, compound borrow): identity and `internal` of the
pool, the companion, the mode, and the entry authorities, each tagged with its slot and the
resolved generation ("étiquetée de la génération résolue"). Read by no operation except
`unresolve`, which looks up the entries of a companion. -/
structure Res where
  pool : Nat
  internal : Nat
  comp : Nat
  mode : Mode
  entries : List (Nat × Nat × Nat)
deriving DecidableEq, Repr

/-- Kernel state with the pool entries (material §4), the next fresh pool identity ("jamais
réutilisée pendant l'exécution") and the ghost record of resolutions. -/
structure PS where
  s : S3
  pools : List Pool
  nId : Nat
  res : List Res

/-- Outcomes of a pool operation (material §4: `ok | fail | reject`): `fail` is a defined failure
that leaves the state unchanged, as for `alloc` and `issue` (MM-03.3 §3.1). -/
inductive POutcome where
  | ok (ps : PS)
  | fail (ps : PS)
  | reject

/-- The pool read as an arena entry with nothing available or issued, to reuse the metadata right
and the arena invariant of MM-03.3 §6 (`MetaRight`, `ArenaInv`). -/
def Pool.asArena (pl : Pool) : Arena := ⟨pl.storage, pl.internal, [], []⟩

/-- Right to update the pool value (material §4, `allocSlot` and `freeSlot`: "`Modify` exerçable
ou `writeShared` sur métadonnées `SharedMutable`"): the metadata right of the arena (MM-03.3 §6,
`MetaRight`), read on the holder of `internal`. -/
def PoolRight (k : K) (s : S3) (pl : Pool) (via : Nat) : Prop := MetaRight k s pl.asArena via

instance (k : K) [DecidablePred k.SharedMutable] (s : S3) (pl : Pool) (via : Nat) :
    Decidable (PoolRight k s pl via) := by
  unfold PoolRight; infer_instance

/-- Place of slot `i` (0 if the slot does not exist). -/
def slotPlace (pl : Pool) (i : Nat) : Nat := ((pl.slots[i]?).map (·.place)).getD 0

/-- The pool with its slot `i` replaced. -/
def setSlot (pl : Pool) (i : Nat) (sl : Slot) : Pool := { pl with slots := pl.slots.set i sl }

/-- The extended state with its pool `j` replaced. -/
def setPool (ps : PS) (j : Nat) (pl : Pool) : PS := { ps with pools := ps.pools.set j pl }

/-! ## `newPool storage internal` (material §4) -/

/-- Preconditions of `newPool storage internal` (material §4: "préconditions de `newArena` (F1, F2,
J1)"): those of `newArena` (MM-03.3 §6, O17), read literally, so clause 4 speaks of the arenas of
the state. -/
def NewPoolPre (s : S3) (storage internal : Nat) : Prop := NewArenaPre s storage internal

instance (s : S3) (storage internal : Nat) : Decidable (NewPoolPre s storage internal) := by
  unfold NewPoolPre; infer_instance

/-- Effect of `newPool storage internal` (material §4): a pool with a fresh identity, one free
entry of generation 0 per child of the storage (the entries are the parts of `storage`, report (f)),
and the kernel state unchanged. -/
def newPoolEff (ps : PS) (storage internal : Nat) : PS :=
  { ps with
    pools := ps.pools ++ [⟨ps.nId, storage, internal,
      (kids ps.s.P storage).map fun q => ⟨q, 0, false⟩⟩]
    nId := ps.nId + 1 }

/-- `newPool storage internal : ok | reject` as a relation (material §4). -/
def NewPoolStep (storage internal : Nat) (ps : PS) : Outcome3 PS → Prop :=
  Guarded (NewPoolPre ps.s storage internal) (newPoolEff ps storage internal)

/-! ## `allocSlot pool dst` (material §4) -/

/-- First free entry of a list of slots, counted from `i`. -/
def firstFreeF : Nat → List Slot → Option Nat
  | _, [] => none
  | i, sl :: l => if sl.live then firstFreeF (i + 1) l else some i

/-- First free entry of a pool (report (f): the material does not say which free entry). -/
def firstFree (pl : Pool) : Option Nat := firstFreeF 0 pl.slots

/-- Static preconditions of `allocSlot pool dst` (material §4): the right to update the pool value;
`dst` a usable leaf, not `Init`, holding no active authority, under exercisable `Modify`. The size
of a handle is not represented: MM-03 has no sizes (report (f)). -/
def AllocSlotStatic (k : K) (s : S3) (pl : Pool) (via dst : Nat) : Prop :=
  PoolRight k s pl via ∧ s.Usable dst ∧ HasRight s .modify dst ∧ isLeaf s.P dst ∧
    s.I dst ≠ .init ∧
    ∀ j ∈ List.range s.A.length, OptP (s.A[j]?) (fun z => z.active = true → z.holder ≠ .place dst)
      True

instance (k : K) [DecidablePred k.SharedMutable] (s : S3) (pl : Pool) (via dst : Nat) :
    Decidable (AllocSlotStatic k s pl via dst) := by
  unfold AllocSlotStatic; infer_instance

/-- Effect of `allocSlot` on the entry `i` of the pool `j` (material §4): the entry becomes live,
its content is not changed (the material says it stays `Uninit`, which holds when it was `Uninit`:
report, (g)), the handle is written into `dst`, which alone becomes `Init`. -/
def allocSlotEff (ps : PS) (j : Nat) (pl : Pool) (i : Nat) (sl : Slot) (dst : Nat) : PS :=
  { setPool ps j (setSlot pl i { sl with live := true }) with s := write3Eff ps.s [dst] }

/-- The handle written by `allocSlot` into its destination (material §4: `(id, slot, gen)`). -/
def slotHandle (pl : Pool) (i : Nat) : Option Handle :=
  (pl.slots[i]?).map fun sl => ⟨pl.id, i, sl.gen⟩

/-- `allocSlot pool dst : ok | fail | reject` as a relation (material §4): `reject` when a static
precondition fails or the pool does not exist; `fail`, state unchanged, when no entry is free;
`ok` otherwise, on the first free entry. -/
inductive AllocSlotStep (k : K) (j via dst : Nat) (ps : PS) : POutcome → Prop where
  | ok {pl : Pool} {i : Nat} {sl : Slot} : ps.pools[j]? = some pl →
      AllocSlotStatic k ps.s pl via dst → firstFree pl = some i → pl.slots[i]? = some sl →
      AllocSlotStep k j via dst ps (.ok (allocSlotEff ps j pl i sl dst))
  | fail {pl : Pool} : ps.pools[j]? = some pl → AllocSlotStatic k ps.s pl via dst →
      firstFree pl = none → AllocSlotStep k j via dst ps (.fail ps)
  | reject {pl : Pool} : ps.pools[j]? = some pl → ¬ AllocSlotStatic k ps.s pl via dst →
      AllocSlotStep k j via dst ps .reject
  | none : ps.pools[j]? = none → AllocSlotStep k j via dst ps .reject

/-! ## `resolve h m` and `resolveMany hs m` (material §4) -/

/-- The handle designates a live entry of the pool, at its generation (material §4, `resolve`:
`fail` "si `h.id` n'est pas l'identité du pool, si `h.gen` diffère de la génération de l'entrée,
ou si l'entrée est libre"). A slot index outside the pool designates no entry (report (f)). -/
def HandleOK (pl : Pool) (h : Handle) : Prop :=
  h.id = pl.id ∧ OptP (pl.slots[h.slot]?) (fun sl => sl.gen = h.gen ∧ sl.live = true) False

instance (pl : Pool) (h : Handle) : Decidable (HandleOK pl h) := by
  unfold HandleOK; infer_instance

/-- Right of the pool value to exercise `internal` at mode `m` (material §4, `resolve`): the
precondition of `derive` (MM-03.3 §3, O1) of the companion, from `internal`, on the whole storage.
It reads the effective mode of `internal`, so an active `Modify` companion rejects every new
resolution, whatever the handles (material §4, H31a). -/
def ResolveRight (s : S3) (pl : Pool) (m : Mode) : Prop := DerivePre s pl.internal pl.storage m

instance (s : S3) (pl : Pool) (m : Mode) : Decidable (ResolveRight s pl m) := by
  unfold ResolveRight; infer_instance

/-- State after the compound borrow of one entry (material §4): the companion `s.A.length`,
derived from `internal` on the storage, then the entry authority `s.A.length + 1`, derived from the
companion on the place `q` of the entry, both at mode `m`, held by the current frame. -/
def resolveS (s : S3) (pl : Pool) (q : Nat) (m : Mode) : S3 :=
  deriveEff (deriveEff s pl.internal pl.storage m) s.A.length q m

/-- `resolve h m : ok | fail | reject` on the pool `j` as a relation (material §4): `reject` when
the right fails; then `fail`, state unchanged, when the handle is stale, of another pool or names
a free entry; `ok` with the compound borrow, recorded with the resolved generation. The derive of
the entry is a kernel step: its precondition is checked (`noEntry`). -/
inductive ResolveStep (j : Nat) (h : Handle) (m : Mode) (ps : PS) : POutcome → Prop where
  | ok {pl : Pool} {sl : Slot} : ps.pools[j]? = some pl → ResolveRight ps.s pl m → HandleOK pl h →
      pl.slots[h.slot]? = some sl →
      DerivePre (deriveEff ps.s pl.internal pl.storage m) ps.s.A.length sl.place m →
      ResolveStep j h m ps (.ok { ps with
        s := resolveS ps.s pl sl.place m
        res := ps.res ++ [⟨pl.id, pl.internal, ps.s.A.length, m,
          [(ps.s.A.length + 1, h.slot, h.gen)]⟩] })
  | fail {pl : Pool} : ps.pools[j]? = some pl → ResolveRight ps.s pl m → ¬ HandleOK pl h →
      ResolveStep j h m ps (.fail ps)
  | reject {pl : Pool} : ps.pools[j]? = some pl → ¬ ResolveRight ps.s pl m →
      ResolveStep j h m ps .reject
  | noEntry {pl : Pool} {sl : Slot} : ps.pools[j]? = some pl → ResolveRight ps.s pl m →
      HandleOK pl h → pl.slots[h.slot]? = some sl →
      ¬ DerivePre (deriveEff ps.s pl.internal pl.storage m) ps.s.A.length sl.place m →
      ResolveStep j h m ps .reject
  | none : ps.pools[j]? = none → ResolveStep j h m ps .reject

/-- The handles of a batch all designate live entries of the pool at their generation, and pairwise
distinct entries (material §4, `resolveMany`: `fail` "si un handle est périmé ou d'un autre pool,
ou si deux handles désignent la même entrée"). -/
def BatchOK (pl : Pool) (hs : List Handle) : Prop :=
  (∀ h ∈ hs, HandleOK pl h) ∧ (hs.map (·.slot)).Nodup

instance (pl : Pool) (hs : List Handle) : Decidable (BatchOK pl hs) := by
  unfold BatchOK; infer_instance

/-- Regions of the entries of a batch: the footprint of each designated entry. -/
def batchRegions (s : S3) (pl : Pool) (hs : List Handle) : List (List Nat) :=
  hs.map fun h => footprint s.P (slotPlace pl h.slot)

/-- State after the compound borrow of a batch (material §4): the companion `s.A.length`, then one
entry authority per handle by `split` of the companion (MM-03.3 §3, O2). -/
def resolveManyS (s : S3) (pl : Pool) (hs : List Handle) (m : Mode) : S3 :=
  splitEff (deriveEff s pl.internal pl.storage m) s.A.length (batchRegions s pl hs)

/-- Entry authorities of a batch with their slot and generation: the `i`-th split authority has the
identity `c + 1 + i` for the companion `c`. -/
def batchEntries (c : Nat) (hs : List Handle) : List (Nat × Nat × Nat) :=
  mapI (fun i h => (i, h.slot, h.gen)) (c + 1) hs

/-- `resolveMany hs m : ok | fail | reject` on the pool `j` as a relation (material §4): `reject`
when the right fails; then `fail`, state unchanged and no authority created (atomicity), when the
batch is not valid; `ok` with the compound borrow when the `split` of the companion is accepted,
`reject` otherwise (`noSplit`). -/
inductive ResolveManyStep (k : K) (j : Nat) (hs : List Handle) (m : Mode) (ps : PS) :
    POutcome → Prop where
  | ok {pl : Pool} : ps.pools[j]? = some pl → ResolveRight ps.s pl m → BatchOK pl hs →
      SplitPre k (deriveEff ps.s pl.internal pl.storage m) ps.s.A.length
        (batchRegions ps.s pl hs) →
      ResolveManyStep k j hs m ps (.ok { ps with
        s := resolveManyS ps.s pl hs m
        res := ps.res ++ [⟨pl.id, pl.internal, ps.s.A.length, m,
          batchEntries ps.s.A.length hs⟩] })
  | fail {pl : Pool} : ps.pools[j]? = some pl → ResolveRight ps.s pl m → ¬ BatchOK pl hs →
      ResolveManyStep k j hs m ps (.fail ps)
  | reject {pl : Pool} : ps.pools[j]? = some pl → ¬ ResolveRight ps.s pl m →
      ResolveManyStep k j hs m ps .reject
  | noSplit {pl : Pool} : ps.pools[j]? = some pl → ResolveRight ps.s pl m → BatchOK pl hs →
      ¬ SplitPre k (deriveEff ps.s pl.internal pl.storage m) ps.s.A.length
        (batchRegions ps.s pl hs) →
      ResolveManyStep k j hs m ps .reject
  | none : ps.pools[j]? = none → ResolveManyStep k j hs m ps .reject

/-! ## `unresolve` (material §4) -/

/-- Releases the authorities of a list in order (MM-03.3 §3, O3); `none` as soon as a release is
rejected. -/
def releaseAll : S3 → List Nat → Option S3
  | s, [] => some s
  | s, a :: l => if ReleasePre s a then releaseAll (releaseEff s a) l else none

/-- The resolution whose companion is `c`. -/
def findRes (ps : PS) (c : Nat) : Option Res := ps.res.find? fun r => r.comp == c

/-- `unresolve` of the resolution of companion `c` as a relation (material §4: "`release` des
autorités d'entrée, puis de la compagne"): `ok` when every release is accepted, `reject`
otherwise or when `c` is no companion. -/
inductive UnresolveStep (c : Nat) (ps : PS) : POutcome → Prop where
  | ok {r : Res} {s' : S3} : findRes ps c = some r →
      releaseAll ps.s (r.entries.map (·.1) ++ [r.comp]) = some s' →
      UnresolveStep c ps (.ok { ps with s := s' })
  | reject {r : Res} : findRes ps c = some r →
      releaseAll ps.s (r.entries.map (·.1) ++ [r.comp]) = none → UnresolveStep c ps .reject
  | none : findRes ps c = none → UnresolveStep c ps .reject

/-! ## `freeSlot h` (material §4) -/

/-- The handle is current for the pool (material §4, `freeSlot`: `fail` "si `h` est périmé ou d'un
autre pool"): same identity, an existing entry of the same generation. -/
def HandleCur (pl : Pool) (h : Handle) : Prop :=
  h.id = pl.id ∧ OptP (pl.slots[h.slot]?) (fun sl => sl.gen = h.gen) False

instance (pl : Pool) (h : Handle) : Decidable (HandleCur pl h) := by
  unfold HandleCur; infer_instance

/-- An active authority derived from `internal` covers a leaf of the place `q` of an entry
(material §4, `freeSlot`: `reject` "si une autorité active dérivée de `internal` couvre
l'entrée"). -/
def EntryBorrowed (s : S3) (pl : Pool) (q : Nat) : Prop :=
  ∃ j ∈ List.range s.A.length, s.Active j ∧ pl.internal ∈ s.ancs j ∧
    ∃ l ∈ s.afp j, l ∈ footprint s.P q

instance (s : S3) (pl : Pool) (q : Nat) : Decidable (EntryBorrowed s pl q) := by
  unfold EntryBorrowed; infer_instance

/-- Effect of `freeSlot` on the entry `i` of the pool `j` (material §4): the end of the content of
the entry by `endUse` (MM-03.3 §3, O12), then the entry is free and its generation incremented. -/
def freeSlotEff (ps : PS) (j : Nat) (pl : Pool) (i : Nat) (sl : Slot) : PS :=
  { setPool ps j (setSlot pl i ⟨sl.place, sl.gen + 1, false⟩) with
    s := endUseEff ps.s sl.place }

/-- `freeSlot h : ok | fail | reject` on the pool `j` as a relation (material §4), in order:
`reject` without the right to update the pool value; `fail`, state unchanged, for a stale handle
or one of another pool; `reject` when an active authority derived from `internal` covers the
entry; `reject` when a precondition of `endUse` fails; `ok` otherwise. -/
inductive FreeSlotStep (k : K) (j via : Nat) (h : Handle) (ps : PS) : POutcome → Prop where
  | ok {pl : Pool} {sl : Slot} : ps.pools[j]? = some pl → PoolRight k ps.s pl via →
      HandleCur pl h → pl.slots[h.slot]? = some sl → ¬ EntryBorrowed ps.s pl sl.place →
      EndUsePre k ps.s sl.place →
      FreeSlotStep k j via h ps (.ok (freeSlotEff ps j pl h.slot sl))
  | fail {pl : Pool} : ps.pools[j]? = some pl → PoolRight k ps.s pl via → ¬ HandleCur pl h →
      FreeSlotStep k j via h ps (.fail ps)
  | reject {pl : Pool} : ps.pools[j]? = some pl → ¬ PoolRight k ps.s pl via →
      FreeSlotStep k j via h ps .reject
  | borrowed {pl : Pool} {sl : Slot} : ps.pools[j]? = some pl → PoolRight k ps.s pl via →
      HandleCur pl h → pl.slots[h.slot]? = some sl → EntryBorrowed ps.s pl sl.place →
      FreeSlotStep k j via h ps .reject
  | endUse {pl : Pool} {sl : Slot} : ps.pools[j]? = some pl → PoolRight k ps.s pl via →
      HandleCur pl h → pl.slots[h.slot]? = some sl → ¬ EntryBorrowed ps.s pl sl.place →
      ¬ EndUsePre k ps.s sl.place → FreeSlotStep k j via h ps .reject
  | none : ps.pools[j]? = none → FreeSlotStep k j via h ps .reject

/-! ## Reachability extended with the pool (material §4, "intégration à `Reachable`") -/

/-- One step of the extended machine: a step of `Reachable` (MM-03.3 §10, `Step`) on the kernel
state, or an `ok` pool operation (material §4). -/
inductive PStep (k : K) : PS → PS → Prop where
  | kernel {ps : PS} {s' : S3} : Step k ps.s s' → PStep k ps { ps with s := s' }
  | newPool {ps ps' : PS} {st i : Nat} : NewPoolStep st i ps (.ok ps') → PStep k ps ps'
  | allocSlot {ps ps' : PS} {j via dst : Nat} : AllocSlotStep k j via dst ps (.ok ps') →
      PStep k ps ps'
  | resolve {ps ps' : PS} {j : Nat} {h : Handle} {m : Mode} : ResolveStep j h m ps (.ok ps') →
      PStep k ps ps'
  | resolveMany {ps ps' : PS} {j : Nat} {hs : List Handle} {m : Mode} :
      ResolveManyStep k j hs m ps (.ok ps') → PStep k ps ps'
  | unresolve {ps ps' : PS} {c : Nat} : UnresolveStep c ps (.ok ps') → PStep k ps ps'
  | freeSlot {ps ps' : PS} {j via : Nat} {h : Handle} : FreeSlotStep k j via h ps (.ok ps') →
      PStep k ps ps'

/-- Initial extended state: `S3.init statics` (MM-03.3.9), no pool, no resolution. -/
def PS.init (statics : Statics) : PS := ⟨S3.init statics, [], 0, []⟩

/-- States reached from the initial state by kernel, arena and pool steps (material §4, extension of
`Reachable`, MM-03.3 §10). -/
inductive PReach (k : K) (statics : Statics) : PS → Prop where
  | init : ShapeOK 0 (statics.map (·.1)) → PReach k statics (PS.init statics)
  | step {ps ps' : PS} : PReach k statics ps → PStep k ps ps' → PReach k statics ps'

/-! ## Kernel steps keep authorities and footprints (MM-03.3 §3–6) -/

/-- The authorities of `s` remain in `s'` with their mode and footprint; one active in `s'` was
active in `s` and, if it was derived, is still derived. -/
def KeepsAuth (s s' : S3) : Prop :=
  s.A.length ≤ s'.A.length ∧ ∀ (j : Nat) (y' : Authority), s'.A[j]? = some y' → j < s.A.length →
    ∃ y, s.A[j]? = some y ∧ y'.mode = y.mode ∧ y'.footprint = y.footprint ∧
      (y'.active = true → y.active = true ∧ (y.origin ≠ none → y'.origin ≠ none))

theorem KeepsAuth.refl (s : S3) : KeepsAuth s s :=
  ⟨Nat.le_refl _, fun _ y' hy' _ => ⟨y', hy', rfl, rfl, fun ha => ⟨ha, id⟩⟩⟩

theorem KeepsAuth.trans {s s₁ s₂ : S3} (h₁ : KeepsAuth s s₁) (h₂ : KeepsAuth s₁ s₂) :
    KeepsAuth s s₂ := by
  refine ⟨Nat.le_trans h₁.1 h₂.1, fun j y₂ hy₂ hj => ?_⟩
  obtain ⟨y₁, hy₁, m₁, f₁, a₁⟩ := h₂.2 j y₂ hy₂ (Nat.lt_of_lt_of_le hj h₁.1)
  obtain ⟨y, hy, m, f, a⟩ := h₁.2 j y₁ hy₁ hj
  exact ⟨y, hy, m₁.trans m, f₁.trans f, fun ha =>
    ⟨(a (a₁ ha).1).1, fun ho => (a₁ ha).2 ((a (a₁ ha).1).2 ho)⟩⟩

theorem KeepsAuth.of_releases {s s₁ : S3} (h : OnlyReleases s s₁) : KeepsAuth s s₁ :=
  ⟨Nat.le_of_eq h.1.symm, fun j z hz _ => by
    obtain ⟨y, hy, m, o, f, -, a⟩ := h.2 j z hz
    exact ⟨y, hy, m, f, fun ha => ⟨a ha, fun hn => by rw [o]; exact hn⟩⟩⟩

theorem KeepsAuth.app {s s₁ : S3} {l : List Authority} (h : s₁.A = s.A ++ l) : KeepsAuth s s₁ :=
  ⟨by rw [h]; simp, fun j y' hy' hj => ⟨y', by rw [h, List.getElem?_append_left hj] at hy'; exact hy',
    rfl, rfl, fun ha => ⟨ha, id⟩⟩⟩

theorem KeepsAuth.same {s s₁ : S3} (h : s₁.A = s.A) : KeepsAuth s s₁ :=
  KeepsAuth.app (l := []) (by rw [h, List.append_nil])

/-- A kernel step keeps the authorities (MM-03.3 §3–5): it appends, releases, or changes holders;
`exitFrame` re-attaches a surviving derived authority to a surviving ancestor (O7, `ExitPre`). -/
theorem kstep_keeps {k : K} {s s' : S3} (h : KStep k s s') : KeepsAuth s s' := by
  cases h with
  | derive hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact .app rfl
  | split hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact .app rfl
  | release hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact .of_releases (release_releases s _)
  | transfer hs =>
    rename_i src dst
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
    refine ⟨by simp [transferEff], fun j y' hy' _ => ?_⟩
    rw [transfer_A_get] at hy'
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hy'
    refine ⟨y, hy, ?_⟩
    split <;> exact ⟨rfl, rfl, fun ha => ⟨ha, id⟩⟩
  | depend hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact .same rfl
  | read hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact .same rfl
  | write hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact .same rfl
  | writeShared hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact .same rfl
  | pin hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact .same rfl
  | unpin hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact .same rfl
  | enter hs =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
    refine ⟨by simp [enterEff, length_mapI], fun j y' hy' hj => ?_⟩
    rw [enter_lt hj] at hy'
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hy'
    refine ⟨y, hy, ?_⟩
    split <;> exact ⟨rfl, rfl, fun ha => ⟨ha, id⟩⟩
  | exit hs =>
    obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 hs
    unfold ExitPre at hpre
    split at hpre
    · rename_i f F₀ hF
      refine ⟨by rw [exitEff_eq hF]; simp [length_mapI], fun j y' hy' hj => ?_⟩
      rw [exit_A_get hF] at hy'
      obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hy'
      obtain ⟨hm, hf, -⟩ := exitG_same s F₀ j y
      refine ⟨y, hy, hm, hf, fun ha => ⟨exitG_active' hy ha, fun ho => ?_⟩⟩
      rcases exitG_origin (s := s) (F₀ := F₀) (a := j) (y := y) with e | ⟨hsv, -, e⟩
      · rw [e]; exact ho
      · rw [e]
        exact hpre.2.2.1 j (List.mem_range.2 hj) hsv (by simp only [S3.org, hy]; exact ho)
    · exact hpre.elim
  | endUse hs =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
    exact .of_releases ((endUseS_releases s _).trans cleanup_releases)
  | free hs =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
    exact .of_releases ((freeS_releases s _).trans cleanup_releases)
  | alloc hs => cases hs; exact .app rfl
  | store hs =>
    rename_i a p
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
    have sk := store_skel s a p
    refine ⟨Nat.le_of_eq sk.1.symm, fun j y' hy' _ => ?_⟩
    obtain ⟨y, hy, e⟩ := sk.get hy'
    simp only [skel, Prod.mk.injEq] at e
    obtain ⟨hm, ho, hf, ha⟩ := e
    exact ⟨y, hy, hm, hf, fun h => ⟨ha ▸ h, fun hn => by rw [ho]; exact hn⟩⟩

/-- A step of `Reachable` keeps the authorities (MM-03.3 §3–6). -/
theorem step_keeps {k : K} {s s' : S3} (h : Step k s s') : KeepsAuth s s' := by
  cases h with
  | kernel hk => exact kstep_keeps hk
  | newArena hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact .same rfl
  | issue hs =>
    cases hs with
    | ok _ hst =>
      obtain ⟨-, -, -, -, e⟩ := issue_ok_iff.1 hst
      have e1 := congrArg Prod.fst e; simp only at e1; subst e1
      exact .app rfl
  | reset hs =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
    unfold resetAtEff; split <;> exact .same rfl

/-- The places of `s` remain in `s'` with their footprint. -/
def FpStable (s s' : S3) : Prop :=
  s.P.length ≤ s'.P.length ∧ ∀ q < s.P.length, ∀ l, l ∈ footprint s'.P q ↔ l ∈ footprint s.P q

theorem FpStable.same {s s₁ : S3} (h : s₁.P = s.P) : FpStable s s₁ :=
  ⟨by rw [h]; exact Nat.le_refl _, fun _ _ _ => by rw [h]⟩

theorem FpStable.refl (s : S3) : FpStable s s := .same rfl

theorem FpStable.trans {s s₁ s₂ : S3} (h₁ : FpStable s s₁) (h₂ : FpStable s₁ s₂) :
    FpStable s s₂ :=
  ⟨Nat.le_trans h₁.1 h₂.1, fun q hq l =>
    (h₂.2 q (Nat.lt_of_lt_of_le hq h₁.1) l).trans (h₁.2 q hq l)⟩

/-- A kernel step removes no place and changes no footprint of an existing place (MM-03.3 §3–5):
only `transfer` changes places, their owners, and `enterFrame` and `alloc` append places whose
parents are new (`EnterPreBase`, `ShapeOK`). -/
theorem kstep_fp {k : K} {s s' : S3} (h : KStep k s s') : FpStable s s' := by
  cases h with
  | derive hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact .same rfl
  | split hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact .same rfl
  | release hs =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
    exact .same (by unfold releaseEff; split <;> rfl)
  | transfer hs =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
    exact ⟨Nat.le_of_eq (transfer_len s _ _).symm, fun q _ l => by rw [transfer_footprint]⟩
  | depend hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact .same rfl
  | read hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact .same rfl
  | write hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact .same rfl
  | writeShared hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact .same rfl
  | pin hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact .same rfl
  | unpin hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact .same rfl
  | enter hs =>
    obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 hs
    exact ⟨by simp [enterEff, enterP], fun q hq => enter_footprint_old hpre.1 hq⟩
  | exit hs =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
    exact .same (by unfold exitEff; split <;> rfl)
  | endUse hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact .same rfl
  | free hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact .same rfl
  | alloc hs =>
    cases hs with
    | ok hst _ =>
      exact ⟨by simp [allocEff, allocP, shapeP], fun q hq => shape_footprint_old hst.2.2.2.2.2.1 hq⟩
  | store hs =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
    exact .same (by unfold storeEff; split <;> rfl)

/-- A step of `Reachable` removes no place and changes no footprint of an existing place. -/
theorem step_fp {k : K} {s s' : S3} (h : Step k s s') : FpStable s s' := by
  cases h with
  | kernel hk => exact kstep_fp hk
  | newArena hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact .same rfl
  | issue hs =>
    cases hs with
    | ok _ hst =>
      obtain ⟨-, -, -, -, e⟩ := issue_ok_iff.1 hst
      have e1 := congrArg Prod.fst e; simp only at e1; subst e1
      exact .same rfl
  | reset hs =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
    unfold resetAtEff; split <;> exact .same rfl

/-- `Reachable` is closed under its steps (MM-03.3 §10, `Step`). -/
theorem reachable_step {k : K} {statics : Statics} {s s' : S3} (hr : Reachable k statics s)
    (h : Step k s s') : Reachable k statics s' := by
  cases h with
  | kernel hk =>
    cases hk with
    | derive hs => exact .derive hr hs
    | split hs => exact .split hr hs
    | release hs => exact .release hr hs
    | transfer hs => exact .transfer hr hs
    | depend hs => exact .depend hr hs
    | enter hs => exact .enter hr hs
    | exit hs => exact .exit hr hs
    | read hs => exact .read hr hs
    | write hs => exact .write hr hs
    | writeShared hs => exact .writeShared hr hs
    | pin hs => exact .pin hr hs
    | unpin hs => exact .unpin hr hs
    | endUse hs => exact .endUse hr hs
    | free hs => exact .free hr hs
    | alloc hs => exact .alloc hr hs
    | store hs => exact .store hr hs
  | newArena hs => exact .newArena hr hs
  | issue hs => exact .issue hr hs
  | reset hs => exact .reset hr hs

/-- Finite sequences of steps of `Reachable`. -/
inductive Steps (k : K) : S3 → S3 → Prop where
  | refl (s : S3) : Steps k s s
  | tail {s s₁ s₂ : S3} : Steps k s s₁ → Step k s₁ s₂ → Steps k s s₂

theorem Steps.keeps {k : K} {s s' : S3} (h : Steps k s s') : KeepsAuth s s' := by
  induction h with
  | refl => exact .refl _
  | tail _ h ih => exact ih.trans (step_keeps h)

theorem Steps.fp {k : K} {s s' : S3} (h : Steps k s s') : FpStable s s' := by
  induction h with
  | refl => exact .refl _
  | tail _ h ih => exact ih.trans (step_fp h)

theorem reachable_steps {k : K} {statics : Statics} {s s' : S3} (hr : Reachable k statics s)
    (h : Steps k s s') : Reachable k statics s' := by
  induction h with
  | refl => exact hr
  | tail _ h ih => exact reachable_step ih h

theorem Steps.single {k : K} {s s' : S3} (h : Step k s s') : Steps k s s' := .tail (.refl s) h

theorem Steps.trans {k : K} {s s₁ s₂ : S3} (h₁ : Steps k s s₁) (h₂ : Steps k s₁ s₂) :
    Steps k s s₂ := by
  induction h₂ with
  | refl => exact h₁
  | tail _ h ih => exact .tail ih h

/-! ## Pool steps are kernel steps (material §4: "construites sur les opérations du noyau") -/

theorem optP_false_iff {α : Type} {o : Option α} {P : α → Prop} :
    OptP o P False ↔ ∃ y, o = some y ∧ P y := by
  cases o with
  | none => simp [OptP]
  | some y => simp [OptP]

theorem KeepsAuth.get {s s' : S3} (hk : KeepsAuth s s') {x : Nat} {y : Authority}
    (hy : s.A[x]? = some y) : ∃ y', s'.A[x]? = some y' ∧ y'.mode = y.mode ∧
      y'.footprint = y.footprint ∧
      (y'.active = true → y.active = true ∧ (y.origin ≠ none → y'.origin ≠ none)) := by
  have hx := lt_of_getElem? hy
  obtain ⟨y', hy'⟩ : ∃ y', s'.A[x]? = some y' :=
    ⟨_, List.getElem?_eq_some_iff.2 ⟨Nat.lt_of_lt_of_le hx hk.1, rfl⟩⟩
  obtain ⟨y₀, hy₀, h⟩ := hk.2 x y' hy' hx
  rw [hy] at hy₀; cases hy₀
  exact ⟨y', hy', h⟩

theorem KeepsAuth.active {s s' : S3} (hk : KeepsAuth s s') {x : Nat} (hx : x < s.A.length)
    (h : s'.Active x) : s.Active x := by
  obtain ⟨y', hy', ya'⟩ := h
  obtain ⟨y, hy, -, -, a⟩ := hk.2 x y' hy' hx
  exact ⟨y, hy, (a ya').1⟩

/-- The anchors of a usable place, and of the places it is part of, are valid in a state with
`I3` (MM-03.3 §2, I3; parts share the owner and the `dead` mark of their parent, `WF3`). -/
theorem depsValid_of_usable {s : S3} (hw : WF3 s) (h3 : I3 s) {p : Nat} (hu : s.Usable p) :
    DepsValid s p :=
  fun q _ hpq x hx => h3 q (usable_of_part hw hpq hu) x hx

/-- The write of the handle by `allocSlot` is a `write3` (MM-03.3 §5, O10): exercisable `Modify`
with effective `Modify` on the leaf, valid anchors. -/
theorem write_of_right {s : S3} (hw : WF3 s) (h3 : I3 s) {dst : Nat} (hu : s.Usable dst)
    (hr : HasRight s .modify dst) (hl : isLeaf s.P dst) : ∃ a, canWrite3 s a [dst] := by
  obtain ⟨a, -, hex, hall⟩ := hr
  refine ⟨a, hex, fun p hp => ?_⟩
  rw [List.mem_singleton] at hp; subst hp
  have hmem : p ∈ footprint s.P p := mem_footprint.2 ⟨hu.lt, hl, hu.lt, .inl rfl⟩
  have ha := hall p hmem
  refine ⟨?_, depsValid_of_usable hw h3 hu⟩
  unfold Allows OptP at ha
  split at ha
  · rename_i e he
    rcases ha with h | h
    · cases h
    · rw [he, h]
  · exact ha.elim

/-- `unresolve` is a sequence of `release` steps (MM-03.3 §3, O3). -/
theorem releaseAll_steps {k : K} : ∀ {s s' : S3} {l : List Nat}, releaseAll s l = some s' →
    Steps k s s'
  | s, s', [], h => by simp only [releaseAll, Option.some.injEq] at h; subst h; exact .refl s
  | s, s', a :: l, h => by
    simp only [releaseAll] at h
    split at h
    · rename_i hpre
      exact (Steps.single (.kernel (.release (Guarded.ok hpre)))).trans (releaseAll_steps h)
    · cases h

/-- Every pool step is a finite sequence of steps of `Reachable` on the kernel state (material §4:
the pool is built on `derive`, `split`, `release`, `endUse`, and the handle is written by
`write3`). `WF3` and `I3` give the valid anchors of the write of `allocSlot`. -/
theorem pstep_steps {k : K} {ps ps' : PS} (hw : WF3 ps.s) (h3 : I3 ps.s) (h : PStep k ps ps') :
    Steps k ps.s ps'.s := by
  cases h with
  | kernel h => exact .single h
  | newPool h => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; exact .refl _
  | allocSlot h =>
    cases h with
    | ok _ hst _ _ =>
      obtain ⟨-, hu, hr, hl, -, -⟩ := hst
      obtain ⟨a, hw3⟩ := write_of_right hw h3 hu hr hl
      exact .single (.kernel (.write (a := a) (Guarded.ok hw3)))
  | resolve h =>
    cases h with
    | ok _ hR _ _ hE =>
      exact (Steps.single (.kernel (.derive (Guarded.ok hR)))).tail
        (.kernel (.derive (Guarded.ok hE)))
  | resolveMany h =>
    cases h with
    | ok _ hR _ hS =>
      exact (Steps.single (.kernel (.derive (Guarded.ok hR)))).tail
        (.kernel (.split (Guarded.ok hS)))
  | unresolve h =>
    cases h with
    | ok _ hr => exact releaseAll_steps hr
  | freeSlot h =>
    cases h with
    | ok _ _ _ _ _ hE => exact .single (.kernel (.endUse (Guarded.ok hE)))

/-- Integration with `Reachable` (material §4): the kernel state of every state reached with pool
steps is reached by kernel and arena steps (MM-03.3 §10). Under `DDSound k`, used by the invariants
that give the anchors of the write of `allocSlot`. -/
theorem pReach_reachable {k : K} (hdd : DDSound k) {statics : Statics} {ps : PS}
    (h : PReach k statics ps) : Reachable k statics ps.s := by
  induction h with
  | init hsh => exact .init hsh
  | step _ hs ih =>
    obtain ⟨hw, hinv, -⟩ := reachable_invariants hdd ih
    exact reachable_steps ih (pstep_steps hw hinv.1.2.2.1 hs)

/-! ## List helpers -/

theorem mem_set_self' {α : Type} : ∀ {l : List α} {i : Nat} {a x : α}, l[i]? = some a →
    x ∈ l.set i x
  | [], _, _, _, h => by simp at h
  | _ :: _, 0, _, _, _ => by simp
  | _ :: l, i + 1, a, x, h => by
    simp only [List.getElem?_cons_succ] at h
    simp only [List.set_cons_succ, List.mem_cons]; exact .inr (mem_set_self' h)

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

theorem getElem?_set_eq' {α : Type} : ∀ {l : List α} {i : Nat} {a x : α}, l[i]? = some a →
    (l.set i x)[i]? = some x
  | [], _, _, _, h => by simp at h
  | _ :: _, 0, _, _, _ => by simp
  | _ :: l, i + 1, a, x, h => by
    simp only [List.getElem?_cons_succ] at h
    simp only [List.set_cons_succ, List.getElem?_cons_succ]; exact getElem?_set_eq' h

theorem getElem?_set_ne' {α : Type} : ∀ {l : List α} {i n : Nat} {x : α}, n ≠ i →
    (l.set i x)[n]? = l[n]?
  | [], _, _, _, _ => by simp
  | _ :: _, 0, 0, _, h => absurd rfl h
  | _ :: _, 0, _ + 1, _, _ => by simp
  | _ :: _, _ + 1, 0, _, _ => by simp
  | _ :: l, i + 1, n + 1, x, h => by
    simp only [List.set_cons_succ, List.getElem?_cons_succ]
    exact getElem?_set_ne' (l := l) (fun e => h (by rw [e]))

theorem map_set_same {α β : Type} (f : α → β) : ∀ {l : List α} {i : Nat} {a x : α},
    l[i]? = some a → f x = f a → (l.set i x).map f = l.map f
  | [], _, _, _, h, _ => by simp at h
  | b :: l, 0, a, x, h, hf => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h
    simp [hf]
  | b :: l, i + 1, a, x, h, hf => by
    simp only [List.getElem?_cons_succ] at h
    simp only [List.set_cons_succ, List.map_cons, map_set_same f h hf]

theorem eq_of_id_eq : ∀ {l : List Pool} {a b : Pool}, (l.map (·.id)).Nodup → a ∈ l → b ∈ l →
    a.id = b.id → a = b
  | [], _, _, _, ha, _, _ => by simp at ha
  | c :: l, a, b, hn, ha, hb, he => by
    rw [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.1 ha with ha' | ha' <;> rcases List.mem_cons.1 hb with hb' | hb'
    · rw [ha', hb']
    · subst ha'; exact absurd (he ▸ List.mem_map_of_mem (f := (·.id)) hb') hn.1
    · subst hb'; exact absurd (he.symm ▸ List.mem_map_of_mem (f := (·.id)) ha') hn.1
    · exact eq_of_id_eq hn.2 ha' hb' he

theorem firstFreeF_spec : ∀ {i n : Nat} {l : List Slot}, firstFreeF i l = some n →
    i ≤ n ∧ ∃ sl, l[n - i]? = some sl ∧ sl.live = false
  | _, _, [], h => by simp [firstFreeF] at h
  | i, n, sl :: l, h => by
    simp only [firstFreeF] at h
    split at h
    · obtain ⟨h1, sl', h2, h3⟩ := firstFreeF_spec h
      refine ⟨by omega, sl', ?_, h3⟩
      rw [show n - i = (n - (i + 1)) + 1 by omega]; simpa using h2
    · rename_i hl
      simp only [Option.some.injEq] at h; subst h
      exact ⟨Nat.le_refl _, sl, by simp, by simpa using hl⟩

/-- The entry chosen by `allocSlot` is free. -/
theorem firstFree_free {pl : Pool} {i : Nat} {sl : Slot} (h : firstFree pl = some i)
    (hs : pl.slots[i]? = some sl) : sl.live = false := by
  obtain ⟨-, sl', h1, h2⟩ := firstFreeF_spec h
  rw [Nat.sub_zero, hs] at h1; cases h1; exact h2

theorem mem_batchEntries : ∀ {n : Nat} {hs : List Handle} {e : Nat × Nat × Nat},
    e ∈ batchEntries n hs → ∃ h ∈ hs, e.2.1 = h.slot ∧ e.2.2 = h.gen
  | _, [], _, he => by simp [batchEntries, mapI] at he
  | n, h :: hs, e, he => by
    simp only [batchEntries, mapI, List.mem_cons] at he
    rcases he with rfl | he
    · exact ⟨h, List.mem_cons_self .., rfl, rfl⟩
    · obtain ⟨h', hh', e1, e2⟩ := mem_batchEntries (n := n + 1) he
      exact ⟨h', List.mem_cons_of_mem _ hh', e1, e2⟩

/-! ## Invariants of the pool layer -/

/-- Identity, storage, `internal` and entry places of a pool: what `allocSlot` and `freeSlot`
keep. -/
def Pool.shape (pl : Pool) : Nat × Nat × Nat × List Nat :=
  (pl.id, pl.storage, pl.internal, pl.slots.map (·.place))

theorem setSlot_shape {pl : Pool} {i : Nat} {sl x : Slot} (hs : pl.slots[i]? = some sl)
    (hx : x.place = sl.place) : (setSlot pl i x).shape = pl.shape := by
  simp only [Pool.shape, setSlot, map_set_same (·.place) hs hx]

theorem shape_mem {l l' : List Pool} (h : l'.map Pool.shape = l.map Pool.shape) {pl : Pool}
    (hpl : pl ∈ l) : ∃ pl' ∈ l', pl'.shape = pl.shape := by
  have : pl.shape ∈ l'.map Pool.shape := h ▸ List.mem_map_of_mem hpl
  obtain ⟨pl', h1, h2⟩ := List.mem_map.1 this
  exact ⟨pl', h1, h2⟩

theorem shape_ids {l l' : List Pool} (h : l'.map Pool.shape = l.map Pool.shape) :
    l'.map (·.id) = l.map (·.id) := by
  have := congrArg (List.map Prod.fst) h
  simpa [List.map_map, Function.comp_def, Pool.shape] using this

theorem shape_slot {pl pl' : Pool} (h : pl'.shape = pl.shape) {n : Nat} {sl : Slot}
    (hs : pl.slots[n]? = some sl) : ∃ sl', pl'.slots[n]? = some sl' ∧ sl'.place = sl.place := by
  have h4 : pl'.slots.map (·.place) = pl.slots.map (·.place) := by
    simp only [Pool.shape, Prod.mk.injEq] at h; exact h.2.2.2
  have := congrArg (·[n]?) h4
  simp only [List.getElem?_map, hs, Option.map_some] at this
  cases h' : pl'.slots[n]? with
  | none => rw [h'] at this; cases this
  | some sl' => rw [h'] at this; exact ⟨sl', rfl, Option.some.inj this⟩

theorem shape_place {pl pl' : Pool} (h : pl'.shape = pl.shape) {sl' : Slot} (hs : sl' ∈ pl'.slots) :
    ∃ sl ∈ pl.slots, sl.place = sl'.place := by
  have h4 : pl'.slots.map (·.place) = pl.slots.map (·.place) := by
    simp only [Pool.shape, Prod.mk.injEq] at h; exact h.2.2.2
  have : sl'.place ∈ pl.slots.map (·.place) := h4 ▸ List.mem_map_of_mem hs
  obtain ⟨sl, h1, h2⟩ := List.mem_map.1 this
  exact ⟨sl, h1, h2⟩

/-- Ghost well-formedness of the pool layer, kept by every step (`pReach_inv`): pool identities
fresh and distinct (material §4); `internal` a `Modify` authority (F1, through `newArena`); storage
and entries existing places; each resolution of an existing pool, with a companion created after
`internal`, of the mode of the resolution, on the footprint of the storage, and entry authorities
on the footprint of their entry, still derived while active. -/
def PoolWF (ps : PS) : Prop :=
  (∀ pl ∈ ps.pools, pl.id < ps.nId) ∧ (ps.pools.map (·.id)).Nodup ∧
  (∀ pl ∈ ps.pools, OptP (ps.s.A[pl.internal]?) (fun y => y.mode = .modify) False ∧
    pl.storage < ps.s.P.length ∧ ∀ sl ∈ pl.slots, sl.place < ps.s.P.length) ∧
  ∀ r ∈ ps.res, ∃ pl ∈ ps.pools, pl.id = r.pool ∧ pl.internal = r.internal ∧
    r.internal < r.comp ∧
    OptP (ps.s.A[r.comp]?) (fun y => y.mode = r.mode ∧
      ∀ l, l ∈ y.footprint ↔ l ∈ footprint ps.s.P pl.storage) False ∧
    ∀ e ∈ r.entries, ∃ sl, pl.slots[e.2.1]? = some sl ∧
      OptP (ps.s.A[e.1]?) (fun y => (∀ l, l ∈ y.footprint ↔ l ∈ footprint ps.s.P sl.place) ∧
        (y.active = true → y.origin ≠ none)) False

/-- `pool_no_stale_access` as a state predicate (material §4, `PoolInv` second clause for the entry
authorities): an active entry authority carries the current generation of its entry, which is
live. -/
def NoStale (ps : PS) : Prop :=
  ∀ r ∈ ps.res, ∀ e ∈ r.entries, ps.s.Active e.1 → ∃ pl ∈ ps.pools, pl.id = r.pool ∧
    ∃ sl, pl.slots[e.2.1]? = some sl ∧ sl.gen = e.2.2 ∧ sl.live = true

/-- Exclusivity of the companions (material §4, `pool_resolve_modify_exclusive`): two distinct
active companions of a pool are both `Observe`. -/
def CompExcl (ps : PS) : Prop :=
  ∀ r₁ ∈ ps.res, ∀ r₂ ∈ ps.res, r₁.pool = r₂.pool → r₁.comp ≠ r₂.comp →
    ps.s.Active r₁.comp → ps.s.Active r₂.comp → r₁.mode = .observe ∧ r₂.mode = .observe

/-- `PoolWF` carries over a change of the kernel state that keeps authorities and footprints and a
change of pools that keeps their shape. -/
theorem PoolWF.transport {ps : PS} {s' : S3} {pools' : List Pool} (h : PoolWF ps)
    (hk : KeepsAuth ps.s s') (hf : FpStable ps.s s')
    (hp : pools'.map Pool.shape = ps.pools.map Pool.shape) :
    PoolWF ⟨s', pools', ps.nId, ps.res⟩ := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun pl' hpl' => ?_, by rw [shape_ids hp]; exact h2, fun pl' hpl' => ?_, fun r hr => ?_⟩
  · obtain ⟨pl, hpl, e⟩ := shape_mem hp.symm hpl'
    have := h1 pl hpl
    simp only [Pool.shape, Prod.mk.injEq] at e; rw [← e.1]; exact this
  · obtain ⟨pl, hpl, e⟩ := shape_mem hp.symm hpl'
    obtain ⟨hi, hst, hsl⟩ := h3 pl hpl
    have e' := e; simp only [Pool.shape, Prod.mk.injEq] at e'
    obtain ⟨y, hy, hm⟩ := optP_false_iff.1 hi
    obtain ⟨y', hy', hm', -⟩ := hk.get hy
    refine ⟨optP_false_iff.2 ⟨y', by rw [← e'.2.2.1]; exact hy', hm'.trans hm⟩,
      Nat.lt_of_lt_of_le (e'.2.1 ▸ hst) hf.1, fun sl' hsl' => ?_⟩
    obtain ⟨sl, hs, hp'⟩ := shape_place e.symm hsl'
    exact Nat.lt_of_lt_of_le (hp' ▸ hsl sl hs) hf.1
  · obtain ⟨pl, hpl, hid, hint, hlt, hc, he⟩ := h4 r hr
    obtain ⟨pl', hpl', e⟩ := shape_mem hp hpl
    have e' := e; simp only [Pool.shape, Prod.mk.injEq] at e'
    obtain ⟨-, hst, hsl⟩ := h3 pl hpl
    refine ⟨pl', hpl', e'.1.trans hid, e'.2.2.1.trans hint, hlt, ?_, fun en hen => ?_⟩
    · obtain ⟨y, hy, hm, hfp⟩ := optP_false_iff.1 hc
      obtain ⟨y', hy', hm', hf', -⟩ := hk.get hy
      refine optP_false_iff.2 ⟨y', hy', hm'.trans hm, fun l => ?_⟩
      rw [hf', e'.2.1]; exact (hfp l).trans (hf.2 _ hst l).symm
    · obtain ⟨sl, hs, ho⟩ := he en hen
      obtain ⟨sl', hs', hpl''⟩ := shape_slot e hs
      obtain ⟨y, hy, hfp, hor⟩ := optP_false_iff.1 ho
      obtain ⟨y', hy', -, hf', ha⟩ := hk.get hy
      refine ⟨sl', hs', optP_false_iff.2 ⟨y', hy', fun l => ?_, fun hya => ?_⟩⟩
      · rw [hf', hpl'']
        exact (hfp l).trans (hf.2 _ (hsl sl (List.mem_of_getElem? hs)) l).symm
      · exact (ha hya).2 (hor (ha hya).1)

theorem NoStale.transport {ps : PS} {s' : S3} (h : NoStale ps) (hw : PoolWF ps)
    (hk : KeepsAuth ps.s s') : NoStale { ps with s := s' } := by
  intro r hr e he ha
  obtain ⟨pl, _, _, _, _, _, hen⟩ := hw.2.2.2 r hr
  obtain ⟨sl, _, ho⟩ := hen e he
  obtain ⟨y, hy, -⟩ := optP_false_iff.1 ho
  exact h r hr e he (hk.active (lt_of_getElem? hy) ha)

theorem CompExcl.transport {ps : PS} {s' : S3} (h : CompExcl ps) (hw : PoolWF ps)
    (hk : KeepsAuth ps.s s') : CompExcl { ps with s := s' } := by
  intro r₁ hr₁ r₂ hr₂ hp hne ha₁ ha₂
  have lt : ∀ r ∈ ps.res, r.comp < ps.s.A.length := fun r hr => by
    obtain ⟨pl, _, _, _, _, hc, _⟩ := hw.2.2.2 r hr
    obtain ⟨y, hy, -⟩ := optP_false_iff.1 hc
    exact lt_of_getElem? hy
  exact h r₁ hr₁ r₂ hr₂ hp hne (hk.active (lt r₁ hr₁) ha₁) (hk.active (lt r₂ hr₂) ha₂)

/-! ## Preservation by each step -/

/-- An active descendant of `z` covering `l` takes the effective `Modify` on `l` away from `z`
(MM-03.3.5, cases 3 and 4). -/
theorem not_allows_modify_of_desc {s : S3} {j z l : Nat} {y : Authority}
    (hy : s.A[j]? = some y) (ya : y.active = true) (hl : l ∈ y.footprint)
    (hz : z ∈ s.ancs j) : ¬ Allows (effective s z l) .modify := by
  have hd : y.mode ∈ descModes s z l := mem_descModes.2 ⟨j, y, hy, ya, hl, hz, rfl⟩
  have hne : descModes s z l ≠ [] := fun h => by rw [h] at hd; cases hd
  unfold effective
  split
  · split
    · simp only [effOf, hne, ↓reduceIte]
      split
      · exact id
      · intro h; rcases h with h | h <;> cases h
    · exact id
  · exact id

/-- At the creation of a companion (material §4, `resolve`), every active companion of the same
pool and the new one are both `Observe`: an active companion is unrelated to `internal`, which I1
excludes since `internal` is `Modify`, or descends from it, which takes away the effective mode
that the `derive` of the new companion requires (MM-03.3.5; MM-03.3 §2, I1; O1). -/
theorem companion_blocks {s : S3} (hw : WF3 s) (hi1 : I1 s) {pl : Pool} {m : Mode}
    (hR : ResolveRight s pl m) {xi : Authority} (hxi : s.A[pl.internal]? = some xi)
    (hmi : xi.mode = .modify) {c : Nat} {y : Authority} (hc : s.A[c]? = some y)
    (hya : y.active = true) (hlt : pl.internal < c)
    (hfp : ∀ l, l ∈ y.footprint ↔ l ∈ footprint s.P pl.storage) :
    y.mode = .observe ∧ m = .observe := by
  obtain ⟨hact, -, hus, hsub, hall⟩ := hR
  obtain ⟨l, hl⟩ := exists_mem_footprint hw (s.P.length - pl.storage + 1) pl.storage (by omega)
    hus.lt
  have hli : l ∈ xi.footprint := by have := hsub l hl; simpa [S3.afp, hxi] using this
  have hxa : xi.active = true := by
    obtain ⟨z, hz, za⟩ := hact; rw [hxi] at hz; cases hz; exact za
  have hly : l ∈ y.footprint := (hfp l).2 hl
  have hz : pl.internal ∈ s.ancs c := Decidable.byContradiction fun hn => by
    have hn2 : c ∉ s.ancs pl.internal := fun h => absurd (chain_lt h) (by omega)
    have := hi1 pl.internal c xi y l (by omega) hxi hc hxa hya hli hly hn hn2
    rw [hmi] at this; cases this.1
  have hdesc := hall l hl
  cases hm : y.mode with
  | modify =>
    rw [effective_none_of_desc_modify hc hya hly hm hz] at hdesc; exact hdesc.elim
  | observe =>
    refine ⟨rfl, ?_⟩
    cases m with
    | observe => rfl
    | modify => exact absurd hdesc (not_allows_modify_of_desc hc hya hly hz)

/-- After `endUse p` (MM-03.3 §3, O12), a derived authority covering exactly the leaves of `p` is
inactive: its precondition requires it held within `p` or by a holder that dies
(`EndUseAccessOK`). -/
theorem endUse_kills {k : K} {s : S3} {p x : Nat} {y : Authority} (hw : WF3 s)
    (hpre : EndUsePre k s p) (hy : s.A[x]? = some y) (hor : y.active = true → y.origin ≠ none)
    (hfp : ∀ l, l ∈ y.footprint ↔ l ∈ footprint s.P p) : ¬ (endUseEff s p).Active x := by
  rintro ⟨y', hy', ya'⟩
  obtain ⟨l, hl⟩ := exists_mem_footprint hw (s.P.length - p + 1) p (by omega) hpre.1.lt
  have e1 : (endUseEff s p).A[x]? = ((s.A[x]?).map fun y =>
      if heldIn s.P p y.holder then { y with active := false } else y).map
      (fun y => if HolderLive (endUseS s p) y.holder then y else { y with active := false }) := by
    show (cleanup (endUseS s p)).A[x]? = _
    rw [cleanup_get, endUseS_get]
  rw [e1, hy] at hy'
  simp only [Option.map_some, Option.some.injEq] at hy'
  subst hy'
  have hacc := hpre.2.2.1 x (List.mem_range.2 (lt_of_getElem? hy))
  simp only [EndUseAccessOK, hy, OptP] at hacc
  by_cases hh : heldIn s.P p y.holder
  · simp only [hh, ↓reduceIte] at ya'; split at ya' <;> simp at ya'
  · simp only [hh, ↓reduceIte] at ya'
    split at ya'
    · rename_i hlive
      rcases hacc ya' (hor ya') (.inl ⟨l, (hfp l).2 hl, .inl hl⟩) with h | h
      · exact hh h
      · exact h hlive
    · simp at ya'

theorem pinv_kernel {k : K} {ps : PS} {s' : S3} (hwf : PoolWF ps) (hns : NoStale ps)
    (hce : CompExcl ps) (h : Step k ps.s s') :
    PoolWF { ps with s := s' } ∧ NoStale { ps with s := s' } ∧ CompExcl { ps with s := s' } :=
  ⟨hwf.transport (step_keeps h) (step_fp h) rfl, hns.transport hwf (step_keeps h),
    hce.transport hwf (step_keeps h)⟩

theorem pinv_newPool {ps ps' : PS} {st i : Nat} (hwf : PoolWF ps) (hns : NoStale ps)
    (hce : CompExcl ps) (h : NewPoolStep st i ps (.ok ps')) :
    PoolWF ps' ∧ NoStale ps' ∧ CompExcl ps' := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  obtain ⟨-, hu, hint, -⟩ := hpre
  obtain ⟨h1, h2, h3, h4⟩ := hwf
  have mem : ∀ pl ∈ ps.pools, pl ∈ (newPoolEff ps st i).pools := fun pl hpl =>
    List.mem_append_left _ hpl
  refine ⟨⟨fun pl hpl => ?_, ?_, fun pl hpl => ?_, fun r hr => ?_⟩, fun r hr e he ha => ?_, hce⟩
  · rcases List.mem_append.1 hpl with hpl | hpl
    · exact Nat.lt_succ_of_lt (h1 pl hpl)
    · rw [List.mem_singleton.1 hpl]; exact Nat.lt_succ_self _
  · simp only [newPoolEff, List.map_append, List.map_cons, List.map_nil]
    refine List.nodup_append.2 ⟨h2, by simp, fun a ha b hb => ?_⟩
    rw [List.mem_singleton.1 hb]
    obtain ⟨pl, hpl, rfl⟩ := List.mem_map.1 ha
    exact Nat.ne_of_lt (h1 pl hpl)
  · rcases List.mem_append.1 hpl with hpl | hpl
    · exact h3 pl hpl
    · rw [List.mem_singleton.1 hpl]
      obtain ⟨y, hy, -, hm, -⟩ := optP_false_iff.1 hint
      refine ⟨optP_false_iff.2 ⟨y, hy, hm⟩, hu.lt, fun sl hsl => ?_⟩
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hsl
      exact (mem_kids.1 hq).1
  · obtain ⟨pl, hpl, rest⟩ := h4 r hr
    exact ⟨pl, mem pl hpl, rest⟩
  · obtain ⟨pl, hpl, rest⟩ := hns r hr e he ha
    exact ⟨pl, mem pl hpl, rest⟩

theorem pinv_allocSlot {k : K} {ps ps' : PS} {j via dst : Nat} (hwf : PoolWF ps)
    (hns : NoStale ps) (hce : CompExcl ps) (h : AllocSlotStep k j via dst ps (.ok ps')) :
    PoolWF ps' ∧ NoStale ps' ∧ CompExcl ps' := by
  cases h with
  | @ok pl i sl hpj _ hff hsl =>
    have hshape := map_set_same Pool.shape hpj (setSlot_shape (x := { sl with live := true }) hsl rfl)
    refine ⟨hwf.transport (.same rfl) (.same rfl) hshape, fun r hr e he ha => ?_,
      hce.transport hwf (s' := write3Eff ps.s [dst]) (.same rfl)⟩
    obtain ⟨pl0, hpl0, hid, sl0, hs0, hg, hlv⟩ := hns r hr e he ha
    by_cases hp : pl0 = pl
    · subst hp
      refine ⟨_, mem_set_self' hpj, hid, ?_⟩
      by_cases hi : e.2.1 = i
      · rw [hi, hsl] at hs0; cases hs0
        rw [firstFree_free hff hsl] at hlv; cases hlv
      · exact ⟨sl0, by simp only [setSlot]; rw [getElem?_set_ne' hi]; exact hs0, hg, hlv⟩
    · exact ⟨pl0, mem_set_of_ne hpj hpl0 hp, hid, sl0, hs0, hg, hlv⟩

theorem resolveS_comp (s : S3) (pl : Pool) (q : Nat) (m : Mode) :
    (resolveS s pl q m).A[s.A.length]? =
      some ⟨m, some pl.internal, footprint s.P pl.storage, .frame s.top, true⟩ := by
  simp [resolveS, deriveEff, S3.addAuth]

theorem resolveS_entry (s : S3) (pl : Pool) (q : Nat) (m : Mode) :
    (resolveS s pl q m).A[s.A.length + 1]? =
      some ⟨m, some s.A.length, footprint s.P q, .frame s.top, true⟩ := by
  simp [resolveS, deriveEff, S3.addAuth, S3.top]

theorem resolveManyS_comp (s : S3) (pl : Pool) (hs : List Handle) (m : Mode) :
    (resolveManyS s pl hs m).A[s.A.length]? =
      some ⟨m, some pl.internal, footprint s.P pl.storage, .frame s.top, true⟩ := by
  simp [resolveManyS, splitEff, deriveEff, S3.addAuth]

theorem mem_batchEntries' : ∀ {n : Nat} {hs : List Handle} {e : Nat × Nat × Nat},
    e ∈ batchEntries n hs → ∃ i h, hs[i]? = some h ∧ e = (n + 1 + i, h.slot, h.gen)
  | _, [], _, he => by simp [batchEntries, mapI] at he
  | n, h :: hs, e, he => by
    simp only [batchEntries, mapI, List.mem_cons] at he
    rcases he with rfl | he
    · exact ⟨0, h, rfl, rfl⟩
    · obtain ⟨i, h', hh', rfl⟩ := mem_batchEntries' (n := n + 1) he
      exact ⟨i + 1, h', by simpa using hh', by rw [show n + 1 + (i + 1) = n + 1 + 1 + i by omega]⟩

theorem resolveManyS_entry (s : S3) (pl : Pool) (hs : List Handle) (m : Mode) {i : Nat}
    {h : Handle} (hh : hs[i]? = some h) :
    (resolveManyS s pl hs m).A[s.A.length + 1 + i]? =
      some ⟨.modify, some s.A.length, footprint s.P (slotPlace pl h.slot), .frame s.top, true⟩ := by
  simp only [resolveManyS, splitEff, deriveEff, S3.addAuth, batchRegions, S3.top]
  rw [List.getElem?_append_right (by simp)]
  simp [hh]

/-- Common part of `resolve` and `resolveMany`: a new resolution whose companion was derived from
`internal` in `s` under `ResolveRight` keeps `CompExcl`. -/
theorem compExcl_new {ps : PS} {s' : S3} {pl : Pool} {m : Mode} {rn : Res}
    (hw : WF3 ps.s) (hi1 : I1 ps.s) (hwf : PoolWF ps) (hce : CompExcl ps) (hk : KeepsAuth ps.s s')
    (hpl : pl ∈ ps.pools) (hR : ResolveRight ps.s pl m) (hrp : rn.pool = pl.id)
    (hrm : rn.mode = m) :
    CompExcl ⟨s', ps.pools, ps.nId, ps.res ++ [rn]⟩ := by
  obtain ⟨-, h2, h3, h4⟩ := hwf
  obtain ⟨xi, hxi, hmi⟩ := optP_false_iff.1 (h3 pl hpl).1
  have key : ∀ r ∈ ps.res, r.pool = pl.id → ps.s.Active r.comp →
      r.mode = .observe ∧ m = .observe := fun r hr hp ha => by
    obtain ⟨pl0, hpl0, hid, hint, hlt, hc, -⟩ := h4 r hr
    have e : pl0 = pl := eq_of_id_eq h2 hpl0 hpl (hid.trans hp)
    subst e
    obtain ⟨y, hy, hm, hfp⟩ := optP_false_iff.1 hc
    obtain ⟨y', hy', ya⟩ := ha; rw [hy] at hy'; cases hy'
    have := companion_blocks hw hi1 hR hxi hmi hy ya (hint ▸ hlt) hfp
    exact ⟨hm ▸ this.1, this.2⟩
  have lt : ∀ r ∈ ps.res, r.comp < ps.s.A.length := fun r hr => by
    obtain ⟨_, _, _, _, _, hc, _⟩ := h4 r hr
    obtain ⟨y, hy, -⟩ := optP_false_iff.1 hc
    exact lt_of_getElem? hy
  intro r₁ hr₁ r₂ hr₂ hp hne ha₁ ha₂
  rcases List.mem_append.1 hr₁ with hr₁ | hr₁ <;> rcases List.mem_append.1 hr₂ with hr₂ | hr₂
  · exact hce r₁ hr₁ r₂ hr₂ hp hne (hk.active (lt r₁ hr₁) ha₁) (hk.active (lt r₂ hr₂) ha₂)
  · rw [List.mem_singleton.1 hr₂] at hp ⊢
    have := key r₁ hr₁ (hp.trans hrp) (hk.active (lt r₁ hr₁) ha₁)
    exact ⟨this.1, hrm.trans this.2⟩
  · rw [List.mem_singleton.1 hr₁] at hp ⊢
    have := key r₂ hr₂ (hp.symm.trans hrp) (hk.active (lt r₂ hr₂) ha₂)
    exact ⟨hrm.trans this.2, this.1⟩
  · rw [List.mem_singleton.1 hr₁, List.mem_singleton.1 hr₂] at hne; exact absurd rfl hne

theorem pinv_resolve {ps ps' : PS} {j : Nat} {h : Handle} {m : Mode} (hw : WF3 ps.s)
    (hi1 : I1 ps.s) (hwf : PoolWF ps) (hns : NoStale ps) (hce : CompExcl ps)
    (hst : ResolveStep j h m ps (.ok ps')) : PoolWF ps' ∧ NoStale ps' ∧ CompExcl ps' := by
  cases hst with
  | @ok pl sl hpj hR hH hsl _ =>
    have hpl : pl ∈ ps.pools := List.mem_of_getElem? hpj
    have hk : KeepsAuth ps.s (resolveS ps.s pl sl.place m) := KeepsAuth.trans (.app rfl) (.app rfl)
    have hwf' := hwf.transport hk (.same rfl) rfl
    have hns' := hns.transport hwf hk
    obtain ⟨hid, hsl'⟩ := hH
    rw [hsl] at hsl'; obtain ⟨hg, hlv⟩ := hsl'
    refine ⟨⟨hwf'.1, hwf'.2.1, hwf'.2.2.1, fun r hr => ?_⟩, fun r hr e he ha => ?_,
      compExcl_new hw hi1 hwf hce hk hpl hR rfl rfl⟩
    · rcases List.mem_append.1 hr with hr | hr
      · exact hwf'.2.2.2 r hr
      · rw [List.mem_singleton.1 hr]
        obtain ⟨y, hy, -⟩ := optP_false_iff.1 (hwf.2.2.1 pl hpl).1
        refine ⟨pl, hpl, rfl, rfl, lt_of_getElem? hy, ?_, fun e he => ?_⟩
        · rw [resolveS_comp]; exact ⟨rfl, fun _ => Iff.rfl⟩
        · rw [List.mem_singleton.1 he]
          refine ⟨sl, hsl, ?_⟩
          rw [resolveS_entry]; exact ⟨fun _ => Iff.rfl, fun _ => by simp⟩
    · rcases List.mem_append.1 hr with hr | hr
      · exact hns' r hr e he ha
      · rw [List.mem_singleton.1 hr] at he ⊢
        rw [List.mem_singleton.1 he]
        exact ⟨pl, hpl, rfl, sl, hsl, hg, hlv⟩

theorem pinv_resolveMany {k : K} {ps ps' : PS} {j : Nat} {hs : List Handle} {m : Mode}
    (hw : WF3 ps.s) (hi1 : I1 ps.s) (hwf : PoolWF ps) (hns : NoStale ps) (hce : CompExcl ps)
    (hst : ResolveManyStep k j hs m ps (.ok ps')) : PoolWF ps' ∧ NoStale ps' ∧ CompExcl ps' := by
  cases hst with
  | @ok pl hpj hR hB _ =>
    have hpl : pl ∈ ps.pools := List.mem_of_getElem? hpj
    have hk : KeepsAuth ps.s (resolveManyS ps.s pl hs m) := KeepsAuth.trans (.app rfl) (.app rfl)
    have hwf' := hwf.transport hk (.same rfl) rfl
    have hns' := hns.transport hwf hk
    have hok : ∀ h ∈ hs, ∃ sl, pl.slots[h.slot]? = some sl ∧ h.gen = sl.gen ∧ sl.live = true ∧
        slotPlace pl h.slot = sl.place := fun h hh => by
      obtain ⟨-, hsl⟩ := hB.1 h hh
      obtain ⟨sl, hsl, hg, hlv⟩ := optP_false_iff.1 hsl
      exact ⟨sl, hsl, hg.symm, hlv, by simp [slotPlace, hsl]⟩
    refine ⟨⟨hwf'.1, hwf'.2.1, hwf'.2.2.1, fun r hr => ?_⟩, fun r hr e he ha => ?_,
      compExcl_new hw hi1 hwf hce hk hpl hR rfl rfl⟩
    · rcases List.mem_append.1 hr with hr | hr
      · exact hwf'.2.2.2 r hr
      · rw [List.mem_singleton.1 hr]
        obtain ⟨y, hy, -⟩ := optP_false_iff.1 (hwf.2.2.1 pl hpl).1
        refine ⟨pl, hpl, rfl, rfl, lt_of_getElem? hy, ?_, fun e he => ?_⟩
        · rw [resolveManyS_comp]; exact ⟨rfl, fun _ => Iff.rfl⟩
        · obtain ⟨i, h, hh, rfl⟩ := mem_batchEntries' he
          obtain ⟨sl, hsl, -, -, hp⟩ := hok h (List.mem_of_getElem? hh)
          refine ⟨sl, hsl, ?_⟩
          rw [resolveManyS_entry _ _ _ _ hh, hp]; exact ⟨fun _ => Iff.rfl, fun _ => by simp⟩
    · rcases List.mem_append.1 hr with hr | hr
      · exact hns' r hr e he ha
      · rw [List.mem_singleton.1 hr] at he ⊢
        obtain ⟨h, hh, e1, e2⟩ := mem_batchEntries he
        obtain ⟨sl, hsl, hg, hlv, -⟩ := hok h hh
        exact ⟨pl, hpl, rfl, sl, e1 ▸ hsl, e2 ▸ hg.symm, hlv⟩

theorem pinv_unresolve {k : K} {ps ps' : PS} {c : Nat} (hwf : PoolWF ps) (hns : NoStale ps)
    (hce : CompExcl ps) (h : UnresolveStep c ps (.ok ps')) :
    PoolWF ps' ∧ NoStale ps' ∧ CompExcl ps' := by
  cases h with
  | ok _ hr =>
    have hss := releaseAll_steps (k := k) hr
    exact ⟨hwf.transport hss.keeps hss.fp rfl, hns.transport hwf hss.keeps,
      hce.transport hwf hss.keeps⟩

theorem pinv_freeSlot {k : K} {ps ps' : PS} {j via : Nat} {h : Handle} (hw : WF3 ps.s)
    (hwf : PoolWF ps) (hns : NoStale ps) (hce : CompExcl ps)
    (hst : FreeSlotStep k j via h ps (.ok ps')) : PoolWF ps' ∧ NoStale ps' ∧ CompExcl ps' := by
  cases hst with
  | @ok pl sl hpj _ _ hsl _ hE =>
    have hstep : Step k ps.s (endUseEff ps.s sl.place) := .kernel (.endUse (Guarded.ok hE))
    have hk := step_keeps hstep
    have hshape := map_set_same Pool.shape hpj
      (setSlot_shape (x := ⟨sl.place, sl.gen + 1, false⟩) hsl rfl)
    refine ⟨hwf.transport hk (step_fp hstep) hshape, fun r hr e he ha => ?_,
      hce.transport hwf hk⟩
    have hpl : pl ∈ ps.pools := List.mem_of_getElem? hpj
    obtain ⟨_, _, _, _, _, hc, hen⟩ := hwf.2.2.2 r hr
    obtain ⟨_, _, ho⟩ := hen e he
    obtain ⟨y, hy, -⟩ := optP_false_iff.1 ho
    obtain ⟨pl0, hpl0, hid, sl0, hs0, hg, hlv⟩ := hns r hr e he (hk.active (lt_of_getElem? hy) ha)
    by_cases hp : pl0 = pl
    · subst hp
      refine ⟨_, mem_set_self' hpj, hid, ?_⟩
      by_cases hi : e.2.1 = h.slot
      · exfalso
        obtain ⟨pl1, hpl1, hid1, -, -, -, hen1⟩ := hwf.2.2.2 r hr
        have e1 : pl1 = pl0 := eq_of_id_eq hwf.2.1 hpl1 hpl0 (hid1.trans hid.symm)
        subst e1
        obtain ⟨sl1, hs1, ho1⟩ := hen1 e he
        rw [hi, hsl] at hs1; cases hs1
        obtain ⟨y1, hy1, hfp1, hor1⟩ := optP_false_iff.1 ho1
        exact endUse_kills hw hE hy1 hor1 hfp1 ha
      · exact ⟨sl0, by simp only [setSlot]; rw [getElem?_set_ne' hi]; exact hs0, hg, hlv⟩
    · exact ⟨pl0, mem_set_of_ne hpj hpl0 hp, hid, sl0, hs0, hg, hlv⟩

/-- Every pool step keeps the invariants of the pool layer. -/
theorem pstep_inv {k : K} {ps ps' : PS} (hw : WF3 ps.s) (hi1 : I1 ps.s) (hwf : PoolWF ps)
    (hns : NoStale ps) (hce : CompExcl ps) (h : PStep k ps ps') :
    PoolWF ps' ∧ NoStale ps' ∧ CompExcl ps' := by
  cases h with
  | kernel h => exact pinv_kernel hwf hns hce h
  | newPool h => exact pinv_newPool hwf hns hce h
  | allocSlot h => exact pinv_allocSlot hwf hns hce h
  | resolve h => exact pinv_resolve hw hi1 hwf hns hce h
  | resolveMany h => exact pinv_resolveMany hw hi1 hwf hns hce h
  | unresolve h => exact pinv_unresolve (k := k) hwf hns hce h
  | freeSlot h => exact pinv_freeSlot hw hwf hns hce h

/-- Invariants of the states reached with pool steps (material §4), under `DDSound k`
(MM-03.3.8): the kernel state is reached (`pReach_reachable`), the pool layer is well formed,
no entry authority is stale and the companions are exclusive. -/
theorem pReach_inv {k : K} (hdd : DDSound k) {statics : Statics} {ps : PS}
    (h : PReach k statics ps) :
    Reachable k statics ps.s ∧ PoolWF ps ∧ NoStale ps ∧ CompExcl ps := by
  induction h with
  | init hsh =>
    refine ⟨.init hsh, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;> simp [PS.init, NoStale, CompExcl]
  | step _ hs ih =>
    obtain ⟨hr, hwf, hns, hce⟩ := ih
    obtain ⟨hw, hinv, -⟩ := reachable_invariants hdd hr
    exact ⟨reachable_steps hr (pstep_steps hw hinv.1.2.2.1 hs),
      pstep_inv hw hinv.1.1 hwf hns hce hs⟩

/-! ## Entries of a pool are disjoint parts of its storage (`PoolInv`, first clause) -/

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

/-- Two distinct children of a place have disjoint footprints (MM-03.3.2: a leaf has one chain of
parents). -/
theorem kids_disjoint {s : S3} (hw : WF3 s) {st q₁ q₂ : Nat} (h₁ : q₁ ∈ kids s.P st)
    (h₂ : q₂ ∈ kids s.P st) (hne : q₁ ≠ q₂) : ∀ l ∈ footprint s.P q₁, l ∉ footprint s.P q₂ := by
  intro l hl₁ hl₂
  obtain ⟨-, hp₁⟩ := mem_kids.1 h₁
  obtain ⟨-, hp₂⟩ := mem_kids.1 h₂
  have hlt₁ := (hw.parent_lt hp₁).1
  have hlt₂ := (hw.parent_lt hp₂).1
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

theorem range_pairwise_lt : ∀ n, (List.range n).Pairwise (· < ·)
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.pairwise_append]
    exact ⟨range_pairwise_lt n, by simp, fun a ha b hb => by
      rw [List.mem_singleton.1 hb]; exact List.mem_range.1 ha⟩

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

/-- First clause of `PoolInv` (material §4) for every pool: two distinct entries have disjoint
footprints, and every entry lies within the storage. -/
def EntriesDisjoint (ps : PS) : Prop :=
  ∀ pl ∈ ps.pools, (∀ (i₁ i₂ : Nat) (sl₁ sl₂ : Slot), i₁ ≠ i₂ → pl.slots[i₁]? = some sl₁ →
    pl.slots[i₂]? = some sl₂ → ∀ l ∈ footprint ps.s.P sl₁.place, l ∉ footprint ps.s.P sl₂.place) ∧
    ∀ sl ∈ pl.slots, ∀ l ∈ footprint ps.s.P sl.place, l ∈ footprint ps.s.P pl.storage

theorem EntriesDisjoint.transport {ps : PS} {s' : S3} {pools' : List Pool} (h : EntriesDisjoint ps)
    (hwf : PoolWF ps) (hf : FpStable ps.s s') (hp : pools'.map Pool.shape = ps.pools.map Pool.shape) :
    EntriesDisjoint ⟨s', pools', ps.nId, ps.res⟩ := by
  intro pl' hpl'
  obtain ⟨pl, hpl, e⟩ := shape_mem hp.symm hpl'
  obtain ⟨hd, hin⟩ := h pl hpl
  obtain ⟨-, hst, hsl⟩ := hwf.2.2.1 pl hpl
  have e' := e; simp only [Pool.shape, Prod.mk.injEq] at e'
  have fp : ∀ q < ps.s.P.length, ∀ l, l ∈ footprint s'.P q ↔ l ∈ footprint ps.s.P q := hf.2
  refine ⟨fun i₁ i₂ sl₁' sl₂' hne h₁ h₂ l hl₁ hl₂ => ?_, fun sl' hsl' l hl => ?_⟩
  · obtain ⟨sl₁, h₁', p₁⟩ := shape_slot e h₁
    obtain ⟨sl₂, h₂', p₂⟩ := shape_slot e h₂
    rw [← p₁] at hl₁; rw [← p₂] at hl₂
    have hm₁ := hsl sl₁ (List.mem_of_getElem? h₁')
    have hm₂ := hsl sl₂ (List.mem_of_getElem? h₂')
    exact hd i₁ i₂ sl₁ sl₂ hne h₁' h₂' l ((fp _ hm₁ l).1 hl₁) ((fp _ hm₂ l).1 hl₂)
  · obtain ⟨sl, hs, p⟩ := shape_place e.symm hsl'
    rw [← p] at hl
    rw [← e'.2.1]
    exact (fp _ hst l).2 (hin sl hs l ((fp _ (hsl sl hs) l).1 hl))

/-- `EntriesDisjoint` holds on every reached state (material §4, `PoolInv` first clause): the
entries of `newPool` are the children of the storage, and footprints do not change. -/
theorem pool_entries_disjoint {k : K} (hdd : DDSound k) {statics : Statics} {ps : PS}
    (h : PReach k statics ps) : EntriesDisjoint ps := by
  induction h with
  | init => intro pl hpl; simp [PS.init] at hpl
  | step hr hs ih =>
    rename_i ps ps'
    obtain ⟨hreach, hwf, -⟩ := pReach_inv hdd hr
    obtain ⟨hw, hinv, -⟩ := reachable_invariants hdd hreach
    have hss := pstep_steps hw hinv.1.2.2.1 hs
    cases hs with
    | kernel h => exact ih.transport hwf (step_fp h) rfl
    | @newPool ps' st i h =>
      obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
      intro pl hpl
      rcases List.mem_append.1 hpl with hpl | hpl
      · exact ih pl hpl
      · rw [List.mem_singleton.1 hpl]
        have hk : (kids ps.s.P st).Pairwise (· < ·) := (range_pairwise_lt _).filter _
        refine ⟨fun i₁ i₂ sl₁ sl₂ hne h₁ h₂ => ?_, fun sl hsl l hl => ?_⟩
        · simp only [List.getElem?_map] at h₁ h₂
          cases g₁ : (kids ps.s.P st)[i₁]? with
          | none => rw [g₁] at h₁; cases h₁
          | some q₁ =>
            cases g₂ : (kids ps.s.P st)[i₂]? with
            | none => rw [g₂] at h₂; cases h₂
            | some q₂ =>
              rw [g₁] at h₁; rw [g₂] at h₂
              simp only [Option.map_some, Option.some.injEq] at h₁ h₂; subst h₁ h₂
              exact kids_disjoint hw (List.mem_of_getElem? g₁) (List.mem_of_getElem? g₂)
                fun e => hne (index_inj_of_lt hk g₁ (by simp only at e; rw [e]; exact g₂))
        · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hsl
          obtain ⟨hql, hpq⟩ := mem_kids.1 hq
          exact footprint_sub hw ⟨hql, .inr (by
            rw [chain_cons hpq (hw.parent_lt hpq).1]; exact List.mem_cons_self ..)⟩ hl
    | allocSlot h =>
      cases h with
      | @ok pl i sl hpj _ _ hsl =>
        exact ih.transport hwf (.same rfl)
          (map_set_same Pool.shape hpj (setSlot_shape (x := { sl with live := true }) hsl rfl))
    | resolve h => cases h with | ok => exact ih.transport hwf hss.fp rfl
    | resolveMany h => cases h with | ok => exact ih.transport hwf hss.fp rfl
    | unresolve h => cases h with | ok => exact ih.transport hwf hss.fp rfl
    | freeSlot h =>
      cases h with
      | @ok pl sl hpj _ _ hsl _ _ =>
        exact ih.transport hwf hss.fp
          (map_set_same Pool.shape hpj (setSlot_shape (x := ⟨sl.place, sl.gen + 1, false⟩) hsl rfl))

/-! ## Theorems of the material (§4) -/

/-- `pool_resolve_stale_fails` (material §4, generation): with the right of the pool value, a handle
whose generation differs from that of its entry fails, state unchanged. -/
theorem pool_resolve_stale_fails {ps : PS} {j : Nat} {pl : Pool} {h : Handle} {m : Mode}
    {sl : Slot} (hp : ps.pools[j]? = some pl) (hR : ResolveRight ps.s pl m)
    (hsl : pl.slots[h.slot]? = some sl) (hg : sl.gen ≠ h.gen) :
    ResolveStep j h m ps (.fail ps) :=
  .fail hp hR fun ⟨_, ho⟩ => by rw [hsl] at ho; exact hg ho.1

/-- `pool_resolve_other_pool_fails` (material §4, identity of the pool): with the right of the pool
value, a handle of another pool fails, state unchanged. -/
theorem pool_resolve_other_pool_fails {ps : PS} {j : Nat} {pl : Pool} {h : Handle} {m : Mode}
    (hp : ps.pools[j]? = some pl) (hR : ResolveRight ps.s pl m) (hid : h.id ≠ pl.id) :
    ResolveStep j h m ps (.fail ps) :=
  .fail hp hR fun ⟨e, _⟩ => hid e

/-- A failed resolution leaves the state unchanged (material §4, `resolve`: "`fail` (état
inchangé)"). -/
theorem pool_resolve_fail_unchanged {ps ps' : PS} {j : Nat} {h : Handle} {m : Mode}
    (hst : ResolveStep j h m ps (.fail ps')) : ps' = ps := by
  cases hst; rfl

/-- `pool_no_stale_access` (material §4): on every reached state, an active entry authority carries
the current generation of its entry, and the entry is live. -/
theorem pool_no_stale_access {k : K} (hdd : DDSound k) {statics : Statics} {ps : PS}
    (h : PReach k statics ps) : NoStale ps :=
  (pReach_inv hdd h).2.2.1

/-- `pool_resolve_modify_exclusive` (material §4): on every reached state, whatever the sequence of
`resolve`, `resolveMany`, `release`, `store`, `transfer` and `unresolve` (and every other step of
`PReach`), an active `Modify` companion of a pool is the only active companion of that pool: at
most one active `Modify` companion, and then no active `Observe` companion. -/
theorem pool_resolve_modify_exclusive {k : K} (hdd : DDSound k) {statics : Statics} {ps : PS}
    (h : PReach k statics ps) : ∀ r₁ ∈ ps.res, ∀ r₂ ∈ ps.res, r₁.pool = r₂.pool →
      ps.s.Active r₁.comp → ps.s.Active r₂.comp → r₁.mode = .modify → r₁.comp = r₂.comp := by
  intro r₁ hr₁ r₂ hr₂ hp ha₁ ha₂ hm
  refine Decidable.byContradiction fun hne => ?_
  have := (pReach_inv hdd h).2.2.2 r₁ hr₁ r₂ hr₂ hp hne ha₁ ha₂
  rw [hm] at this; cases this.1

/-- `pool_resolveMany_atomic` (material §4): a failed `resolveMany` creates no authority and
leaves the state unchanged; an accepted one creates the companion and all the entry authorities
in one step. -/
theorem pool_resolveMany_atomic {k : K} {ps ps' : PS} {j : Nat} {hs : List Handle} {m : Mode} :
    (ResolveManyStep k j hs m ps (.fail ps') → ps' = ps) ∧
    (ResolveManyStep k j hs m ps (.ok ps') → ∃ pl, ps.pools[j]? = some pl ∧ BatchOK pl hs ∧
      ps'.s = resolveManyS ps.s pl hs m ∧ ps'.s.A.length = ps.s.A.length + 1 + hs.length) := by
  refine ⟨fun h => by cases h; rfl, fun h => ?_⟩
  cases h with
  | @ok pl hp _ hB _ =>
    refine ⟨pl, hp, hB, rfl, ?_⟩
    simp only [resolveManyS, splitEff, deriveEff, S3.addAuth, batchRegions, List.length_append,
      List.length_map, List.length_cons, List.length_nil]

/-- `pool_resolveMany_distinct` (material §4, dynamic distinctness): with the right of the pool
value, two handles of a batch designating the same entry make `resolveMany` fail; an accepted batch
designates pairwise distinct entries. -/
theorem pool_resolveMany_distinct {k : K} {ps ps' : PS} {j : Nat} {pl : Pool} {hs : List Handle}
    {m : Mode} :
    (ps.pools[j]? = some pl → ResolveRight ps.s pl m → ¬ (hs.map (·.slot)).Nodup →
      ResolveManyStep k j hs m ps (.fail ps)) ∧
    (ResolveManyStep k j hs m ps (.ok ps') → (hs.map (·.slot)).Nodup) := by
  refine ⟨fun hp hR hd => .fail hp hR fun hB => hd hB.2, fun h => ?_⟩
  cases h with
  | ok _ _ hB _ => exact hB.2

/-- `pool_freeSlot_ends_content` (material §4): after `freeSlot`, the kernel state is the result of
an accepted `endUse` of the entry (MM-03.3 §3, O12), whose leaves are `Uninit`, and the entry is
free with its generation incremented. -/
theorem pool_freeSlot_ends_content {k : K} {ps ps' : PS} {j via : Nat} {h : Handle}
    (hst : FreeSlotStep k j via h ps (.ok ps')) :
    ∃ pl sl, ps.pools[j]? = some pl ∧ pl.slots[h.slot]? = some sl ∧
      EndUseStep k sl.place ps.s (.ok ps'.s) ∧
      (∀ l ∈ footprint ps.s.P sl.place, ps'.s.I l = .uninit) ∧
      ps'.pools[j]? = some (setSlot pl h.slot ⟨sl.place, sl.gen + 1, false⟩) := by
  cases hst with
  | @ok pl sl hp _ _ hsl _ hE =>
    refine ⟨pl, sl, hp, hsl, Guarded.ok hE, fun l hl => ?_, getElem?_set_eq' hp⟩
    show (cleanup (endUseS ps.s sl.place)).I l = .uninit
    simp [cleanup, endUseS, hl]

/-! ## `PoolInv` read literally (material §4) -/

/-- Second clause of `PoolInv` (material §4), literally, for the pool `pl`: every active authority
derived from a companion of the pool and covering a leaf of an entry "porte la génération courante
de l'entrée": it is, or descends from, an entry authority of that entry tagged with its current
generation; and the entry is live. -/
def PoolInvGen (ps : PS) (pl : Pool) : Prop :=
  ∀ r ∈ ps.res, r.pool = pl.id → ∀ j ∈ List.range ps.s.A.length, ps.s.Active j →
    r.comp ∈ ps.s.ancs j → ∀ i ∈ List.range pl.slots.length,
      (∃ l ∈ ps.s.afp j, l ∈ footprint ps.s.P (slotPlace pl i)) →
      OptP (pl.slots[i]?) (fun sl => sl.live = true ∧ ∃ e ∈ r.entries, e.2.1 = i ∧
        e.2.2 = sl.gen ∧ (e.1 = j ∨ e.1 ∈ ps.s.ancs j)) False

instance (ps : PS) (pl : Pool) : Decidable (PoolInvGen ps pl) := by
  unfold PoolInvGen; infer_instance

/-- Third clause of `PoolInv` (material §4), literally, for the pool `pl`: "toute compagne active a
au plus les autorités d'entrée de sa résolution pour descendants", read on active descendants. -/
def PoolInvDesc (ps : PS) (pl : Pool) : Prop :=
  ∀ r ∈ ps.res, r.pool = pl.id → ps.s.Active r.comp → ∀ j ∈ List.range ps.s.A.length,
    ps.s.Active j → r.comp ∈ ps.s.ancs j → j ∈ r.entries.map (·.1)

instance (ps : PS) (pl : Pool) : Decidable (PoolInvDesc ps pl) := by
  unfold PoolInvDesc; infer_instance

/-- First clause of `PoolInv` (material §4) for the pool `pl`: entries pairwise disjoint and within
the storage. -/
def PoolInvDisj (ps : PS) (pl : Pool) : Prop :=
  (∀ i₁ ∈ List.range pl.slots.length, ∀ i₂ ∈ List.range pl.slots.length, i₁ ≠ i₂ →
    ∀ l ∈ footprint ps.s.P (slotPlace pl i₁), l ∉ footprint ps.s.P (slotPlace pl i₂)) ∧
  ∀ sl ∈ pl.slots, ∀ l ∈ footprint ps.s.P sl.place, l ∈ footprint ps.s.P pl.storage

instance (ps : PS) (pl : Pool) : Decidable (PoolInvDisj ps pl) := by
  unfold PoolInvDisj; infer_instance

/-- `PoolInv` of the material (§4), literally, for every live pool (`internal` active): the three
clauses `PoolInvDisj`, `PoolInvGen` and `PoolInvDesc`. -/
def PoolInv (ps : PS) : Prop :=
  ∀ pl ∈ ps.pools, ps.s.Active pl.internal →
    PoolInvDisj ps pl ∧ PoolInvGen ps pl ∧ PoolInvDesc ps pl

instance (ps : PS) : Decidable (PoolInv ps) := by unfold PoolInv; infer_instance

/-! ## Executable steps

A decidable step function for the extended machine, used by the case files to build reached
states: `prun` runs a list of operations and returns the final state when every step is `ok`
(`prun_reach`). -/

/-- An operation of the extended machine with its arguments: the steps of `Reachable`
(MM-03.3 §3–6) and the pool operations (material §4). -/
inductive Op where
  | derive (src q : Nat) (m : Mode)
  | split (src : Nat) (rs : List (List Nat))
  | release (a : Nat)
  | transfer (src dst : Nat)
  | depend (q x : Nat)
  | enter (ps : List Nat) (ls : List (Option Nat × Option Nat × Nat))
  | exit
  | read (a : Nat) (ls : List Nat)
  | write (a : Nat) (ls : List Nat)
  | writeShared (a : Nat) (ls : List Nat)
  | pin (p : Nat)
  | unpin (p : Nat)
  | endUse (p : Nat)
  | free (p auth : Nat)
  | alloc (pr ow : Nat) (ls : List (Option Nat × Option Nat × Nat))
  | store (a p : Nat)
  | newArena (st i : Nat)
  | issue (i via : Nat) (region : List Nat) (dst : Nat)
  | reset (i via : Nat)
  | newPool (st i : Nat)
  | allocSlot (j via dst : Nat)
  | resolve (j : Nat) (h : Handle) (m : Mode)
  | resolveMany (j : Nat) (hs : List Handle) (m : Mode)
  | unresolve (c : Nat)
  | freeSlot (j via : Nat) (h : Handle)

section Exec
variable (k : K) [∀ r r', Decidable (k.DeclaredDisjoint r r')] [DecidablePred k.SharedMutable]
  [DecidablePred k.Pinned] [DecidablePred k.ExternalDone] [DecidablePred k.Deallocable]
  [∀ p a, Decidable (k.FreeCompat p a)] [∀ p ls s, Decidable (k.Satisfiable p ls s)]

/-- `ok` outcome of a step of `Reachable` (MM-03.3 §3–6), `none` otherwise. -/
def kexec (s : S3) : Op → Option S3
  | .derive src q m => if DerivePre s src q m then some (deriveEff s src q m) else none
  | .split src rs => if SplitPre k s src rs then some (splitEff s src rs) else none
  | .release a => if ReleasePre s a then some (releaseEff s a) else none
  | .transfer src dst => if TransferPre k s src dst then some (transferEff s src dst) else none
  | .depend q x => if DependPre s q x then some (dependEff s q x) else none
  | .enter ps ls => if EnterPre s ps ls then some (enterEff s ps ls) else none
  | .exit => if ExitPre k s then some (exitEff s) else none
  | .read a ls => if canRead3 s a ls then some s else none
  | .write a ls => if canWrite3 s a ls then some (write3Eff s ls) else none
  | .writeShared a ls => if WriteSharedPre k s a ls then some (write3Eff s ls) else none
  | .pin p => if PinPre s p then some (pinEff s p true) else none
  | .unpin p => if UnpinPre k s p then some (pinEff s p false) else none
  | .endUse p => if EndUsePre k s p then some (endUseEff s p) else none
  | .free p auth => if FreePre k s p auth then some (freeEff s p) else none
  | .alloc pr ow ls =>
    if AllocStatic k s pr ow ls ∧ k.Satisfiable pr ls s then some (allocEff s pr ow ls) else none
  | .store a p => if StorePre s a p then some (storeEff s a p) else none
  | .newArena st i => if NewArenaPre s st i then some (newArenaEff s st i) else none
  | .issue i via region dst =>
    match s.arenas[i]? with
    | some ar =>
      if IssueStatic k s ar via region dst ∧ Avail ar region ∧ IssueRight s ar region ∧
          AnchorOrderHeld (issueEff s ar region dst).1 then
        some (arenaSet (issueEff s ar region dst).1 i (issueEff s ar region dst).2)
      else none
    | none => none
  | .reset i via => if ResetAtPre k s i via then some (resetAtEff s i) else none
  | _ => none

/-- `ok` outcome of a step of the extended machine, `none` otherwise. -/
def pexec (ps : PS) : Op → Option PS
  | .newPool st i => if NewPoolPre ps.s st i then some (newPoolEff ps st i) else none
  | .allocSlot j via dst =>
    match ps.pools[j]? with
    | some pl =>
      if AllocSlotStatic k ps.s pl via dst then
        match firstFree pl with
        | some i => (pl.slots[i]?).map fun sl => allocSlotEff ps j pl i sl dst
        | none => none
      else none
    | none => none
  | .resolve j h m =>
    match ps.pools[j]? with
    | some pl =>
      match pl.slots[h.slot]? with
      | some sl =>
        if ResolveRight ps.s pl m ∧ HandleOK pl h ∧
            DerivePre (deriveEff ps.s pl.internal pl.storage m) ps.s.A.length sl.place m then
          some { ps with
            s := resolveS ps.s pl sl.place m
            res := ps.res ++ [⟨pl.id, pl.internal, ps.s.A.length, m,
              [(ps.s.A.length + 1, h.slot, h.gen)]⟩] }
        else none
      | none => none
    | none => none
  | .resolveMany j hs m =>
    match ps.pools[j]? with
    | some pl =>
      if ResolveRight ps.s pl m ∧ BatchOK pl hs ∧
          SplitPre k (deriveEff ps.s pl.internal pl.storage m) ps.s.A.length
            (batchRegions ps.s pl hs) then
        some { ps with
          s := resolveManyS ps.s pl hs m
          res := ps.res ++ [⟨pl.id, pl.internal, ps.s.A.length, m,
            batchEntries ps.s.A.length hs⟩] }
      else none
    | none => none
  | .unresolve c =>
    match findRes ps c with
    | some r => (releaseAll ps.s (r.entries.map (·.1) ++ [r.comp])).map fun s' => { ps with s := s' }
    | none => none
  | .freeSlot j via h =>
    match ps.pools[j]? with
    | some pl =>
      match pl.slots[h.slot]? with
      | some sl =>
        if PoolRight k ps.s pl via ∧ HandleCur pl h ∧ ¬ EntryBorrowed ps.s pl sl.place ∧
            EndUsePre k ps.s sl.place then
          some (freeSlotEff ps j pl h.slot sl)
        else none
      | none => none
    | none => none
  | o => (kexec k ps.s o).map fun s' => { ps with s := s' }

/-- Runs a list of operations; `some` of the final state when every step is `ok`. -/
def prun (ps : PS) : List Op → Option PS
  | [] => some ps
  | o :: os => (pexec k ps o).bind fun ps' => prun ps' os

end Exec

section ExecSound
variable {k : K} [∀ r r', Decidable (k.DeclaredDisjoint r r')] [DecidablePred k.SharedMutable]
  [DecidablePred k.Pinned] [DecidablePred k.ExternalDone] [DecidablePred k.Deallocable]
  [∀ p a, Decidable (k.FreeCompat p a)] [∀ p ls s, Decidable (k.Satisfiable p ls s)]

theorem kexec_step {s s' : S3} {o : Op} (h : kexec k s o = some s') : Step k s s' := by
  cases o <;> simp only [kexec] at h
  all_goals first
    | (split at h
       · rename_i hp; simp only [Option.some.injEq] at h; subst h
         first
           | exact .kernel (.derive (Guarded.ok hp))
           | exact .kernel (.split (Guarded.ok hp))
           | exact .kernel (.release (Guarded.ok hp))
           | exact .kernel (.transfer (Guarded.ok hp))
           | exact .kernel (.depend (Guarded.ok hp))
           | exact .kernel (.enter (Guarded.ok hp))
           | exact .kernel (.exit (Guarded.ok hp))
           | exact .kernel (.read (Guarded.ok hp))
           | exact .kernel (.write (Guarded.ok hp))
           | exact .kernel (.writeShared (Guarded.ok hp))
           | exact .kernel (.pin (Guarded.ok hp))
           | exact .kernel (.unpin (Guarded.ok hp))
           | exact .kernel (.endUse (Guarded.ok hp))
           | exact .kernel (.free (Guarded.ok hp))
           | exact .kernel (.alloc (.ok hp.1 hp.2))
           | exact .kernel (.store (Guarded.ok hp))
           | exact .newArena (Guarded.ok hp)
           | exact .reset (Guarded.ok hp)
       · cases h)
    | cases h
    | (split at h
       · rename_i ar har
         split at h
         · rename_i hp; simp only [Option.some.injEq] at h; subst h
           exact .issue (.ok har (.ok hp.1 hp.2.1 hp.2.2.1 hp.2.2.2))
         · cases h
       · cases h)

theorem pexec_step {ps ps' : PS} {o : Op} (h : pexec k ps o = some ps') : PStep k ps ps' := by
  cases o
  case newPool st i =>
    simp only [pexec] at h; split at h
    · rename_i hp; simp only [Option.some.injEq] at h; subst h; exact .newPool (Guarded.ok hp)
    · cases h
  case allocSlot j via dst =>
    simp only [pexec] at h
    split at h
    · rename_i pl hpl
      split at h
      · rename_i hst
        split at h
        · rename_i i hi
          cases hsl : pl.slots[i]? with
          | none => rw [hsl] at h; cases h
          | some sl =>
            rw [hsl] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h
            exact .allocSlot (.ok hpl hst hi hsl)
        · cases h
      · cases h
    · cases h
  case resolve j hd m =>
    simp only [pexec] at h
    split at h
    · rename_i pl hpl
      split at h
      · rename_i sl hsl
        split at h
        · rename_i hp; simp only [Option.some.injEq] at h; subst h
          exact .resolve (.ok hpl hp.1 hp.2.1 hsl hp.2.2)
        · cases h
      · cases h
    · cases h
  case resolveMany j hs m =>
    simp only [pexec] at h
    split at h
    · rename_i pl hpl
      split at h
      · rename_i hp; simp only [Option.some.injEq] at h; subst h
        exact .resolveMany (.ok hpl hp.1 hp.2.1 hp.2.2)
      · cases h
    · cases h
  case unresolve c =>
    simp only [pexec] at h
    split at h
    · rename_i r hr
      cases hs : releaseAll ps.s (r.entries.map (·.1) ++ [r.comp]) with
      | none => rw [hs] at h; cases h
      | some s' =>
        rw [hs] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h
        exact .unresolve (.ok hr hs)
    · cases h
  case freeSlot j via hd =>
    simp only [pexec] at h
    split at h
    · rename_i pl hpl
      split at h
      · rename_i sl hsl
        split at h
        · rename_i hp; simp only [Option.some.injEq] at h; subst h
          exact .freeSlot (.ok hpl hp.1 hp.2.1 hsl hp.2.2.1 hp.2.2.2)
        · cases h
      · cases h
    · cases h
  all_goals
    simp only [pexec] at h
    cases hk : kexec k ps.s _ with
    | none => rw [hk] at h; cases h
    | some s' =>
      rw [hk] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h
      exact .kernel (kexec_step hk)

theorem prun_reach {statics : Statics} : ∀ {ps ps' : PS} {os : List Op}, PReach k statics ps →
    prun k ps os = some ps' → PReach k statics ps'
  | _, _, [], hr, h => by simp only [prun, Option.some.injEq] at h; subst h; exact hr
  | ps, ps', o :: os, hr, h => by
    simp only [prun] at h
    cases he : pexec k ps o with
    | none => rw [he] at h; cases h
    | some ps₁ => rw [he] at h; exact prun_reach (.step hr (pexec_step he)) h

/-- A run from the initial state that succeeds reaches its final state. -/
theorem prun_init {statics : Statics} {os : List Op} {ps' : PS}
    (hsh : ShapeOK 0 (statics.map (·.1))) (h : prun k (PS.init statics) os = some ps') :
    PReach k statics ps' :=
  prun_reach (.init hsh) h

end ExecSound

theorem some_getD {α : Type} {o : Option α} {d : α} (h : o.isSome = true) :
    o = some (o.getD d) := by
  cases o with
  | none => cases h
  | some a => rfl

/-! ## `PoolInv` is not preserved (material §4, `pool_inv_preserved`)

Two reached runs, kept as counterexamples. In both, a frame has an allocator 0, the pool value 1
and leaves for handles; the storage allocated by 0 for the pool value has two entries, and its root
authority, held by the pool value, is `internal`; entry 0 is allocated (handle `⟨0, 0, 0⟩`) and
resolved `Modify`. -/

namespace PoolInvCex

/-- Pool value 1, handle leaf 2, storage 3 with entries 4 and 5, `internal` 3; companion 4 and entry
authority 5 on the place 4 of entry 0. -/
def ops : List Op :=
  [.enter [] [(none, none, 0), (none, none, 0), (none, none, 0)], .write 0 [0], .write 1 [1],
    .alloc 0 1 [(none, none, 0), (some 3, none, 0), (some 3, none, 0)], .newPool 3 3,
    .allocSlot 0 0 2, .resolve 0 ⟨0, 0, 0⟩ .modify]

def s0 : PS := (prun K0 (PS.init []) ops).getD (PS.init [])

/-- The program derives from the companion 4 an authority 6, `Modify`, on the place 5 of entry 1,
which is free (MM-03.3 §3, O1: accepted by the kernel). -/
def s1 : PS := (pexec K0 s0 (.derive 4 5 .modify)).getD s0

/-- The pool of `s0` and `s1`. -/
def pl : Pool := ⟨0, 3, 3, [⟨4, 0, true⟩, ⟨5, 0, false⟩]⟩

theorem reach0 : PReach K0 [] s0 := prun_init (by decide) (some_getD (by decide))

theorem step01 : PStep K0 s0 s1 := pexec_step (some_getD (by decide))

end PoolInvCex

/-- `pool_inv_preserved` (material §4) is false for `PoolInv` read literally: from a reached state
where it holds, a kernel `derive` from the companion (MM-03.3 §3, O1) gives an active authority
derived from the companion on a free entry (second clause) that is no entry authority (third
clause). The first clause still holds. -/
theorem pool_inv_not_preserved : ∃ ps ps', PReach K0 [] ps ∧ PoolInv ps ∧ PStep K0 ps ps' ∧
    ¬ PoolInv ps' :=
  ⟨_, _, PoolInvCex.reach0, by decide, PoolInvCex.step01, by decide⟩

/-- The clauses of `PoolInv` in the counterexample after the `derive`: the pool is live, entries
disjoint, the second and third clauses false. -/
theorem pool_inv_cex_clauses :
    PoolInvCex.s1.pools = [PoolInvCex.pl] ∧ PoolInvCex.s1.s.Active 3 ∧
    PoolInvDisj PoolInvCex.s1 PoolInvCex.pl ∧ ¬ PoolInvGen PoolInvCex.s1 PoolInvCex.pl ∧
    ¬ PoolInvDesc PoolInvCex.s1 PoolInvCex.pl := by decide

namespace PoolInvCex2

/-- Pool value 1, handle leaf 2, caller leaf 3, storage 4 with entries 5 and 6, `internal` 4;
companion 5 and entry authority 6 on the place 5 of entry 0; the caller derives 7 on its leaf 3 and
calls a frame with the parameters 6 and 7 (G1 holds: the companion is held by the caller). -/
def ops : List Op :=
  [.enter [] [(none, none, 0), (none, none, 0), (none, none, 0), (none, none, 0)], .write 0 [0],
    .write 1 [1], .alloc 0 1 [(none, none, 0), (some 4, none, 0), (some 4, none, 0)],
    .newPool 4 4, .allocSlot 0 0 2, .resolve 0 ⟨0, 0, 0⟩ .modify, .derive 3 3 .modify,
    .enter [6, 7] []]

def s0 : PS := (prun K0 (PS.init []) ops).getD (PS.init [])

/-- The callee derives 8, `Modify`, from the entry authority 6 on the place 5 of entry 0. -/
def s1 : PS := (pexec K0 s0 (.derive 6 5 .modify)).getD s0

/-- The callee stores 8 into the caller leaf 3 (MM-03.3 §3, O8). -/
def s2 : PS := (pexec K0 s1 (.store 8 3)).getD s1

/-- `exitFrame` (O7): the entry authority 6 dies with the callee; 8 survives in the leaf 3 and is
re-attached to its first surviving ancestor, the companion 5. -/
def s3 : PS := (pexec K0 s2 .exit).getD s2

/-- The pool of these states. -/
def pl : Pool := ⟨0, 4, 4, [⟨5, 0, true⟩, ⟨6, 0, false⟩]⟩

theorem reach0 : PReach K0 [] s0 := prun_init (by decide) (some_getD (by decide))
theorem step01 : PStep K0 s0 s1 := pexec_step (some_getD (by decide))
theorem step12 : PStep K0 s1 s2 := pexec_step (some_getD (by decide))
theorem step23 : PStep K0 s2 s3 := pexec_step (some_getD (by decide))

end PoolInvCex2

/-- The third clause of `PoolInv` (read on all active descendants) fails after a `derive` from an
entry authority, the ordinary use of a resolved entry (MM-03.3 §3, O1); the second clause fails after
`exitFrame` re-attaches a surviving derivative of the entry authority to the companion (O7), with no
operation on the companion. -/
theorem pool_inv_cex_entry :
    PReach K0 [] PoolInvCex2.s0 ∧ PoolInv PoolInvCex2.s0 ∧ PStep K0 PoolInvCex2.s0 PoolInvCex2.s1 ∧
    ¬ PoolInvDesc PoolInvCex2.s1 PoolInvCex2.pl ∧
    PStep K0 PoolInvCex2.s1 PoolInvCex2.s2 ∧ PStep K0 PoolInvCex2.s2 PoolInvCex2.s3 ∧
    PoolInvGen PoolInvCex2.s2 PoolInvCex2.pl ∧ ¬ PoolInvGen PoolInvCex2.s3 PoolInvCex2.pl ∧
    PoolInvCex2.s3.pools = [PoolInvCex2.pl] ∧ PoolInvCex2.s3.s.Active 4 ∧
    PoolInvCex2.s3.s.Active 8 ∧ ¬ PoolInvCex2.s3.s.Active 6 ∧ PoolInvCex2.s3.s.org 8 = some 5 :=
  ⟨PoolInvCex2.reach0, by decide, PoolInvCex2.step01, by decide, PoolInvCex2.step12,
    PoolInvCex2.step23, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

end Ern.HandlePool
