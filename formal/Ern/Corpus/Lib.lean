import Ern.Corpus.LibRunner

/-!
# Corpus: library cases (test module)

Library cases of the Jalon 3 material (`ERN_Jalon3_materiel.md`; non-normative design material)
and of the corrected handle-pool contract, run on the reference kernel of
`specs/ERN_Memory_Model_Specification_v0.md` (§60–§75), the arena of Part XIV (§76–§78), the
handle pool of `Ern.Lib.HandlePool` (contract "HandlePool v0.4 annex", non-normative, corrected by
§36 and §56: composite borrow, `resolveMany` in `Observe` without distinctness, `Modify` right on
the pool value, live pool, `newPool` on `Uninit` storage, `freeSlot` exempting `internal` and its
ancestors) and the stack of `Ern.Lib.DataStack` (contract "DS-v1", non-normative). This is a test
module: no model or library module imports it.

* Section G of corpus MM3-H (material §1 G, handles): H30–H34b, H44.
* Cases of the corrected handle-pool contract: stale, other pool, atomic and distinct batches,
  `resolveMany` in `Observe` with a repeated handle, `freeSlot` with a derived `internal`, under the
  `Modify` right only, on a dead pool, of a free slot; `newPool` on written storage; two pools on
  one storage (`pool_two_freeSlot_cross`).
* The guard of §56 across registries: a second administration (arena, pool, stack) on the
  `internal` of a live administration of another registry, or of the same registry for pools.
* The usage scenarios W1 and W2 of material §5b (W3 is in `Ern.Corpus.MM3H`).

Each case is a run from `CState.init statics` (§47) by the combined runner
(`Ern.Corpus.LibRunner`): `CRunsTo k statics os C` states that every step is `ok`, that `C` is
library-reachable and that its kernel state is reached by kernel steps and ends of slot contents.
The verdict of the step under test is stated with the relation of its operation on the projected
state (`ResolveStep`, `FreeSlotStep`, `NewPoolStep`, `NewArenaStep`, `NewStackStep`, `StoreStep`,
`TransferStep`, …) and decided by `decide`. Each docstring gives the expected verdict from the
case's source, the obtained verdict, the class (material §0, rule 5: `Lib` library instance) and
the positive twin of each rejection or `fail` (rule 2: the same sequence without the faulty
element, accepted). A case whose obtained verdict differs from the expected one keeps its expected
verdict and is marked **MISMATCH** with its cause.

Local shapes are lists of (parent, kind) (§71.1, §72); `lf` is a root leaf, `pt p` a part of
place `p`. Places and authorities are list indices (§38): `enterFrame` appends the locals and one
root authority per local; `alloc` appends the shape and one root authority; `derive` and `split`
append the derived authorities; `issue` appends one block authority; `reset` appends one released
authority; `resolve` appends a companion and an entry authority; `resolveMany` a companion and one
entry authority per handle. Pools and stacks are named by their registry index; a handle is
`⟨pool identity, slot index, generation⟩`.
-/

namespace Ern.Corpus.Lib

open Ern.MemoryModel Ern.MemoryModel.Access Ern.MemoryModel.Arena Ern.Corpus Ern.Corpus.LibRunner
  Ern.Lib

/-! ## Test contracts and shapes (§48, §72) -/

/-- The empty test contract (§48): nothing shared, pinned, externally done or deallocable. -/
abbrev K0 : K := KD.toK {}

/-- A root leaf of a local shape (§72, §71.1). -/
abbrev lf : Option Nat × Nat := (none, 0)

/-- A leaf part of place `p` (§72, §71.1). -/
abbrev pt (p : Nat) : Option Nat × Nat := (some p, 0)

/-! ## G. Handles (material §1 G; HandlePool v0.4 annex) -/

/-- Pool base of section G (§72, §71, §67; HandlePool v0.4 annex, D.1): frame 1 with the allocator
0 and the pool value 1, written, and the handle leaves 2 and 3; storage 4 (entries 5 and 6)
allocated, owned by the pool value, its root authority 4 held by it; `newPool 4 4`: pool 0 of
identity 0, slots 5 and 6, free, generation 0. -/
def pb : List COp := [.enter [] [lf, lf, lf, lf], .write 0 [0], .write 1 [1],
  .alloc 0 1 [lf, pt 4, pt 4], .newPool 4 4]

/-- Run of H30 (HandlePool v0.4 annex, D.3): the slot 0 allocated (handle in 2), freed, then
allocated again (handle in 3, generation 1). -/
def h30o : List COp := pb ++ [.allocSlot 0 2, .freeSlot 0 ⟨0, 0, 0⟩, .allocSlot 0 3]
/-- State reached by `h30o` (§57). -/
def h30 : CState := cfinal K0 [] h30o

/-- **H30** (material §1 G, class Lib). Resolution of a handle after the release and the reuse of
its entry. Expected (material, HandlePool contract, generation; §89): `fail`. Obtained: `fail`:
the slot is live at generation 1, the handle carries generation 0 (§89: "a stale identity or
generation leads to defined failure"). Twin, the handle of the reused entry: `resolve` is `ok`. -/
theorem H30 : CRunsTo K0 [] h30o h30 ∧
    h30.pools = [⟨0, 4, 4, [⟨5, 1, true⟩, ⟨6, 0, false⟩]⟩] ∧
    HandlePool.ResolveStep 0 ⟨0, 0, 0⟩ .modify h30.toP .fail ∧
    CRuns K0 [] (h30o ++ [.resolve 0 ⟨0, 0, 1⟩ .modify]) :=
  ⟨crunsTo (by decide), by decide,
    cfails (k := K0) (C := h30) (o := .resolve 0 ⟨0, 0, 0⟩ .modify) (by decide),
    crunsTo (by decide)⟩

/-- Run of H31a and H32 (HandlePool v0.4 annex, D.2): both slots allocated (handles in 2 and 3),
slot 0 resolved in `Modify`: companion 5 over the storage, entry authority 6 over the slot 5. -/
def h31o : List COp := pb ++ [.allocSlot 0 2, .allocSlot 0 3, .resolve 0 ⟨0, 0, 0⟩ .modify]
/-- State reached by `h31o` (§57). -/
def h31 : CState := cfinal K0 [] h31o

/-- **H31a** (material §1 G, class Lib). Two simultaneous `resolve Modify`, whatever the handles.
Expected (material, exclusivity of the pool value): the second `reject`. Obtained: `reject` for
the other entry, for a stale handle and for an `Observe` resolution: the active `Modify` companion
5 leaves `internal` no effective mode on the storage, so the companion of the second resolution
cannot be derived (§43 case 3, §60.2; HandlePool v0.4 annex, D.2: "Une compagne `Modify` active
bloque les nouvelles compagnes"). Twin, after `unresolve` of the first: `ok`. -/
theorem H31a : CRunsTo K0 [] h31o h31 ∧
    HandlePool.ResolveStep 0 ⟨0, 1, 0⟩ .modify h31.toP .reject ∧
    HandlePool.ResolveStep 0 ⟨0, 1, 7⟩ .modify h31.toP .reject ∧
    HandlePool.ResolveStep 0 ⟨0, 0, 0⟩ .observe h31.toP .reject ∧
    CRuns K0 [] (h31o ++ [.unresolve 5, .resolve 0 ⟨0, 1, 0⟩ .modify]) :=
  ⟨crunsTo (by decide),
    crejects (k := K0) (C := h31) (o := .resolve 0 ⟨0, 1, 0⟩ .modify) (by decide),
    crejects (k := K0) (C := h31) (o := .resolve 0 ⟨0, 1, 7⟩ .modify) (by decide),
    crejects (k := K0) (C := h31) (o := .resolve 0 ⟨0, 0, 0⟩ .observe) (by decide),
    crunsTo (by decide)⟩

/-- Run of H31b (HandlePool v0.4 annex, D.3): both slots allocated, handles in 2 and 3. -/
def h31bo : List COp := pb ++ [.allocSlot 0 2, .allocSlot 0 3]
/-- State reached by `h31bo` (§57). -/
def h31b : CState := cfinal K0 [] h31bo

/-- **H31b** (material §1 G, class Lib). `resolveMany Modify` of two handles designating the same
entry. Expected (material, dynamic distinctness; HandlePool v0.4 annex, D.2): `fail`. Obtained:
`fail` (the batch repeats slot 0 in `Modify`). Twin with two distinct entries: `ok`. -/
theorem H31b : CRunsTo K0 [] h31bo h31b ∧
    HandlePool.ResolveManyStep K0 0 [⟨0, 0, 0⟩, ⟨0, 0, 0⟩] .modify h31b.toP .fail ∧
    CRuns K0 [] (h31bo ++ [.resolveMany 0 [⟨0, 0, 0⟩, ⟨0, 1, 0⟩] .modify]) :=
  ⟨crunsTo (by decide),
    cfails (k := K0) (C := h31b) (o := .resolveMany 0 [⟨0, 0, 0⟩, ⟨0, 0, 0⟩] .modify)
      (by decide),
    crunsTo (by decide)⟩

/-- **H32** (material §1 G, class Lib). `freeSlot` while a resolved access on the entry is active.
Expected (material, end of a borrow; HandlePool v0.4 annex, D.3: "aucune descendante active d'une
compagne ne doit subsister sur cette entrée"): `reject`. Obtained: `reject`: the entry authority 6,
a descendant of the companion 5, and the companion itself cover the slot 5 (`ContentEndPre`
fails). The `freeSlot` of the other slot 1 during the same resolution is `reject` as well, the
companion covering the whole storage (material §4: "pendant toute résolution du pool"). Twin, after
`unresolve` of the resolution: both `ok`. -/
theorem H32 : CRunsTo K0 [] h31o h31 ∧
    HandlePool.FreeSlotStep K0 0 ⟨0, 0, 0⟩ h31.toP .reject ∧
    HandlePool.FreeSlotStep K0 0 ⟨0, 1, 0⟩ h31.toP .reject ∧
    CRuns K0 [] (h31o ++ [.unresolve 5, .freeSlot 0 ⟨0, 0, 0⟩]) ∧
    CRuns K0 [] (h31o ++ [.unresolve 5, .freeSlot 0 ⟨0, 1, 0⟩]) :=
  ⟨crunsTo (by decide), crejects (k := K0) (C := h31) (o := .freeSlot 0 ⟨0, 0, 0⟩) (by decide),
    crejects (k := K0) (C := h31) (o := .freeSlot 0 ⟨0, 1, 0⟩) (by decide), crunsTo (by decide),
    crunsTo (by decide)⟩

/-- Run of H33 (§72, §71; HandlePool v0.4 annex, D.1–D.3): frame 1 with the local 0 passes 1,
`Modify` on it, to frame 2, which has the allocator 1, the pool value 2, the handle leaf 3 and the
local 4; storage 5 (entries 6, 7) owned by the pool value, `internal` its root 6; pool 0; slot 0
allocated and resolved: companion 7, entry authority 8. -/
def h33o : List COp := [.enter [] [lf], .derive 0 [0] .modify, .enter [1] [lf, lf, lf, lf],
  .write 2 [1], .write 3 [2], .alloc 1 2 [lf, pt 5, pt 5], .newPool 5 6, .allocSlot 0 3,
  .resolve 0 ⟨0, 0, 0⟩ .modify]
/-- State reached by `h33o` (§57). -/
def h33 : CState := cfinal K0 [] h33o

/-- **H33** (material §1 G, class Lib). A resolved access stored in a value of a frame older than
the pool. Expected (material, anchor order): `reject`. Obtained: `reject`: the effective anchor of
the entry authority 8 is of frame 2, not an ancestor of the frame 1 of the target 0 (§44, §65.4).
Twin, the same `store` into the local 4 of the frame of the pool: `ok`. -/
theorem H33 : CRunsTo K0 [] h33o h33 ∧ StoreStep 8 0 h33.kern .reject ∧
    ¬ EffAnchorOK h33.kern 8 (h33.kern.pframe 0) ∧ CRuns K0 [] (h33o ++ [.store 8 4]) :=
  ⟨crunsTo (by decide), crejects (k := K0) (C := h33) (o := .store 8 0) (by decide), by decide,
    crunsTo (by decide)⟩

/-- **H34** (material §1 G, class Lib). A handle copied (read from 2, written into 3), then two
successive `resolve Modify` of it, with a write of the entry through the first resolution and its
`unresolve` in between. Expected (material): `ok`. Obtained: `ok` at every step (§37, §89: the
handle is data, not an authority; HandlePool v0.4 annex, D.2). -/
theorem H34 : CRuns K0 [] (pb ++ [.allocSlot 0 2, .read 2 [2], .write 3 [3],
    .resolve 0 ⟨0, 0, 0⟩ .modify, .write 6 [5], .unresolve 5, .resolve 0 ⟨0, 0, 0⟩ .modify]) :=
  crunsTo (by decide)

/-- Run of H34b (§71; HandlePool v0.4 annex, D.1): a second storage 7 (entries 8, 9) owned by the
pool value 1, its root 5 the `internal` of pool 1, of identity 1; slot 0 of pool 0 allocated. -/
def h34bo : List COp := pb ++ [.alloc 0 1 [lf, pt 7, pt 7], .newPool 7 5, .allocSlot 0 2]
/-- State reached by `h34bo` (§57). -/
def h34b : CState := cfinal K0 [] h34bo

/-- **H34b** (material §1 G, class Lib). A handle of another pool. Expected (material, identity of
the pool; §89): `fail`. Obtained: `fail`: the handle names identity 0, pool 1 has identity 1. Twin,
the same handle on its own pool: `ok`. -/
theorem H34b : CRunsTo K0 [] h34bo h34b ∧ h34b.pools.map (·.id) = [0, 1] ∧
    HandlePool.ResolveStep 1 ⟨0, 0, 0⟩ .modify h34b.toP .fail ∧
    CRuns K0 [] (h34bo ++ [.resolve 0 ⟨0, 0, 0⟩ .modify]) :=
  ⟨crunsTo (by decide), by decide,
    cfails (k := K0) (C := h34b) (o := .resolve 1 ⟨0, 0, 0⟩ .modify) (by decide),
    crunsTo (by decide)⟩

/-- Run of H44 (§71, §76–§78; HandlePool v0.4 annex, D.1–D.3): frame 1 with the arena value 0,
the allocator 1, the pool value 2 and the handle leaves 3 and 4; storage 5 owned by 0, with the
place 6 holding the nodes 7 (fields 8, 9) and 10 (fields 11, 12); arena on 5 (`internal` 5); the
block 6 over the leaves of 6 issued to the pool value; pool on 6 with the block as `internal`;
each node resolved in turn, its link field written, then unresolved; `endUse` of the pool value;
`reset` of the arena. -/
def h44o : List COp := [.enter [] [lf, lf, lf, lf, lf], .write 1 [1],
  .alloc 1 0 [lf, pt 5, pt 6, pt 7, pt 7, pt 6, pt 10, pt 10], .write 0 [0], .newArena 5 5,
  .issue 0 [8, 9, 11, 12] 2, .newPool 6 6, .allocSlot 0 3, .allocSlot 0 4,
  .resolve 0 ⟨0, 0, 0⟩ .modify, .write 8 [8, 9], .unresolve 7,
  .resolve 0 ⟨0, 1, 0⟩ .modify, .write 10 [11, 12], .unresolve 9, .endUse 2, .reset 0]

/-- **H44** (material §1 G, class Lib). A cyclic graph whose nodes live in a pool placed on an arena
block, linked by handles; temporary resolutions; end of the resolutions, then of the pool value,
then `reset` of the arena, without following the cyclic links. Expected (material): `ok`.
Obtained: `ok` at every step (§89, §37, §78.2; HandlePool v0.4 annex, D.1: the block region was
never written, so `newPool` finds `Uninit` storage). -/
theorem H44 : CRuns K0 [] h44o :=
  crunsTo (by decide)

/-! ## Corrected handle-pool contract (HandlePool v0.4 annex, corrected by §36 and §56) -/

/-- State after the first nine steps of `h44o`: the pool on the arena block, both slots allocated,
nothing resolved (§57). -/
def fdi : CState := cfinal K0 [] (h44o.take 9)

/-- **pool_freeSlot_derived_internal** (corrected handle-pool contract, class Lib). `freeSlot` on a
pool whose `internal` is a derived authority (the arena block 6) held by the pool value, outside
the slot. Expected (HandlePool v0.4 annex, D.3: "aucune autorité active ne couvre l'entrée hors
`internal` et ses ancêtres"; "Le contrôle n'interprète pas `internal` comme un emprunt externe"):
`ok`. Obtained: `ok`; the kernel `endUse` of the slot place 7 is `reject` on the same state
(§69.2: `internal`, active, derived, covering the slot, is held outside it), so the exemption of
`internal` decides the verdict. -/
theorem pool_freeSlot_derived_internal : CRunsTo K0 [] (h44o.take 9) fdi ∧
    ¬ EndUsePre K0 fdi.kern 7 ∧ CRuns K0 [] (h44o.take 9 ++ [.freeSlot 0 ⟨0, 0, 0⟩]) :=
  ⟨crunsTo (by decide), by decide, crunsTo (by decide)⟩

/-- **resolveMany_observe_repeat** (corrected handle-pool contract, class Lib). `resolveMany` in
`Observe` of a repeated valid handle. Expected (HandlePool v0.4 annex, D.2: "sans `split` ni
contrôle de distinction : la répétition du même handle valide est permise"): `ok`. Obtained: `ok`
(one `Observe` companion, two `Observe` entry authorities derived from it, §60). The same batch in
`Modify` is `fail` (`H31b`). -/
theorem resolveMany_observe_repeat :
    CRuns K0 [] (h31bo ++ [.resolveMany 0 [⟨0, 0, 0⟩, ⟨0, 0, 0⟩] .observe]) :=
  crunsTo (by decide)

/-- **resolveMany_atomic** (corrected handle-pool contract, class Lib). `resolveMany Modify` of a
batch with one valid handle and one stale handle. Expected (HandlePool v0.4 annex, D.2: "`fail`
atomique, sans création partielle de droits"): `fail`. Obtained: `fail`, and `fail` is the only
outcome of the relation (no authority is created, §58). Twin without the stale handle (the two
valid handles): `ok`. -/
theorem resolveMany_atomic :
    HandlePool.ResolveManyStep K0 0 [⟨0, 0, 0⟩, ⟨0, 1, 5⟩] .modify h31b.toP .fail ∧
    (∀ o, HandlePool.ResolveManyStep K0 0 [⟨0, 0, 0⟩, ⟨0, 1, 5⟩] .modify h31b.toP o →
      o = .fail) ∧
    CRuns K0 [] (h31bo ++ [.resolveMany 0 [⟨0, 0, 0⟩, ⟨0, 1, 0⟩] .modify]) :=
  ⟨cfails (k := K0) (C := h31b) (o := .resolveMany 0 [⟨0, 0, 0⟩, ⟨0, 1, 5⟩] .modify) (by decide),
    (HandlePool.pool_resolveMany_invalid_fails
      (pl := ⟨0, 4, 4, [⟨5, 0, true⟩, ⟨6, 0, true⟩]⟩) (by decide) (by decide) (by decide)).2,
    crunsTo (by decide)⟩

/-- Run of `pool_newPool_written` (§72, §71, §67): the pool base with the entry 5 written before
`newPool`. -/
def pnwo : List COp := [.enter [] [lf, lf, lf, lf], .write 0 [0], .write 1 [1],
  .alloc 0 1 [lf, pt 4, pt 4], .write 4 [5]]
/-- State reached by `pnwo` (§57). -/
def pnw : CState := cfinal K0 [] pnwo

/-- **pool_newPool_written** (corrected handle-pool contract, class Lib; the draft witness
`pool_allocSlot_content_init`). `newPool` on a storage whose leaf 5 was written. Expected
(HandlePool v0.4 annex, D.1: "`newPool(storage, internal)` exige que toutes les feuilles du
stockage d'entrée soient `Uninit`"): `reject`. Obtained: `reject`; the other preconditions
(those of `newArena`, §76.1–§76.3, §76.5, and the guard of §56) hold. Twin without the write:
`newPool` and `allocSlot` are `ok`. -/
theorem pool_newPool_written : CRunsTo K0 [] pnwo pnw ∧
    HandlePool.NewPoolStep pnw.othersP 4 4 pnw.toP .reject ∧
    NewArenaBase pnw.kern 4 4 ∧ Guard56 (HandlePool.liveInternals pnw.kern pnw.pools ::
      pnw.othersP) 4 ∧
    CRuns K0 [] (pb ++ [.allocSlot 0 2]) :=
  ⟨crunsTo (by decide), crejects (k := K0) (C := pnw) (o := .newPool 4 4) (by decide), by decide,
    by decide, crunsTo (by decide)⟩

/-- State reached by `pb` (§57): a fresh pool, both slots free. -/
def pb0 : CState := cfinal K0 [] pb

/-- **pool_free_entry_handle** (corrected handle-pool contract, class Lib). `freeSlot` of a free
slot whose identity and generation match the handle. Expected (HandlePool v0.4 annex, D.3: "un slot
déjà libre n'est pas rendu libérable par cette seule égalité"): not `ok`; whether `fail` or
`reject` is not stated (to arbitrate). Obtained: `fail` (the handle designates a free slot, as for
`resolve`, D.2: "slot absent ou libre ⇒ `fail`"); `resolveMany` of the same handle is `fail` too.
Twin, the slot allocated first: `freeSlot` is `ok`. **MISMATCH** in form (expected "not `ok`, `fail`
or `reject` to arbitrate", obtained `fail`); cause: open obligation, the contract leaves the
outcome open and the pool module reads it as `fail` (HandlePool reading H-R2). -/
theorem pool_free_entry_handle : CRunsTo K0 [] pb pb0 ∧
    HandlePool.FreeSlotStep K0 0 ⟨0, 0, 0⟩ pb0.toP .fail ∧
    HandlePool.ResolveManyStep K0 0 [⟨0, 0, 0⟩] .modify pb0.toP .fail ∧
    CRuns K0 [] (pb ++ [.allocSlot 0 2, .freeSlot 0 ⟨0, 0, 0⟩]) :=
  ⟨crunsTo (by decide), cfails (k := K0) (C := pb0) (o := .freeSlot 0 ⟨0, 0, 0⟩) (by decide),
    cfails (k := K0) (C := pb0) (o := .resolveMany 0 [⟨0, 0, 0⟩] .modify) (by decide),
    crunsTo (by decide)⟩

/-- Run of `pool_dead` (§69): slot 0 allocated (handle in 2), then `endUse` of the pool value 1,
which releases `internal` (§69 effect: the authorities held by the place end). -/
def pdo : List COp := pb ++ [.allocSlot 0 2, .endUse 1]
/-- State reached by `pdo` (§57). -/
def pd : CState := cfinal K0 [] pdo

/-- **pool_dead** (corrected handle-pool contract, class Lib). `allocSlot` and `freeSlot` on a pool
whose `internal` is no longer active. Expected (HandlePool v0.4 annex, D.3: "`allocSlot(pool, dst)`
exige un pool vivant"; "`freeSlot(h)` exige un pool **vivant**"): `reject`, `reject`. Obtained:
`reject`, `reject`: `internal` 4 is inactive while `MetaRight` (§36, `Modify` over the pool value)
still holds. Twins without the `endUse`: `allocSlot` and `freeSlot` are `ok`. -/
theorem pool_dead : CRunsTo K0 [] pdo pd ∧ ¬ pd.kern.Active 4 ∧
    MetaRight pd.kern ⟨4, 4, [], []⟩ ∧
    HandlePool.AllocSlotStep 0 3 pd.toP .reject ∧
    HandlePool.FreeSlotStep K0 0 ⟨0, 0, 0⟩ pd.toP .reject ∧
    CRuns K0 [] (pb ++ [.allocSlot 0 2, .allocSlot 0 3]) ∧
    CRuns K0 [] (pb ++ [.allocSlot 0 2, .freeSlot 0 ⟨0, 0, 0⟩]) :=
  ⟨crunsTo (by decide), by decide, by decide,
    crejects (k := K0) (C := pd) (o := .allocSlot 0 3) (by decide),
    crejects (k := K0) (C := pd) (o := .freeSlot 0 ⟨0, 0, 0⟩) (by decide), crunsTo (by decide),
    crunsTo (by decide)⟩

/-- Test contract of `pool_shared_right` (§68.1, §80): the pool value 1 is `SharedMutable`. -/
abbrev KSh : K := KD.toK { shared := [1] }

/-- Run of `pool_shared_right` (§60, §72, §68): slot 0 allocated; the caller passes 5, `Observe`
on the pool value, to a callee with the local 7, which updates the pool metadata by
`writeShared`. -/
def psro : List COp := pb ++ [.allocSlot 0 2, .derive 1 [1] .observe, .enter [5] [lf],
  .writeShared 5 [1]]
/-- State reached by `psro` (§57). -/
def psr : CState := cfinal KSh [] psro

/-- **pool_shared_right** (corrected handle-pool contract, class Lib; the draft witness
`pool_freeSlot_shared_right`). A callee that may update the pool metadata only by `writeShared`
calls `allocSlot` and `freeSlot`. Expected (§36: "`MetaRight` requires `Modify` exercisable on the
administering value. The `writeShared` branch alone is insufficient", which overrides the
`writeShared` right of material §4 and of HandlePool v0.4 annex, D.3): `reject`, `reject`.
Obtained: the `writeShared` is `ok` (§68), `allocSlot` and `freeSlot` are `reject` (`¬ MetaRight`).
Twin, the same run with a `Modify` parameter on the pool value: `allocSlot` then `freeSlot` are
`ok` (the `freeSlot` under the `Modify` right). -/
theorem pool_shared_right : CRunsTo KSh [] psro psr ∧ ¬ MetaRight psr.kern ⟨4, 4, [], []⟩ ∧
    HandlePool.AllocSlotStep 0 7 psr.toP .reject ∧
    HandlePool.FreeSlotStep KSh 0 ⟨0, 0, 0⟩ psr.toP .reject ∧
    CRuns KSh [] (pb ++ [.allocSlot 0 2, .derive 1 [1] .modify, .enter [5] [lf],
      .writeShared 5 [1], .allocSlot 0 7, .freeSlot 0 ⟨0, 0, 0⟩]) :=
  ⟨crunsTo (by decide), by decide, crejects (k := KSh) (C := psr) (o := .allocSlot 0 7) (by decide),
    crejects (k := KSh) (C := psr) (o := .freeSlot 0 ⟨0, 0, 0⟩) (by decide), crunsTo (by decide)⟩

/-- Base of `pool_two_freeSlot_cross` (§72, §71, §60, §65; HandlePool v0.4 annex, D.1): frame 1
with the allocator 0, the pool value 1 and the leaves 2, 3, 4; storage 5 (entries 6, 7) owned by
1, pool 0 on it with `internal` its root 5; then 6, `Modify` on the whole storage from 5, stored
into the leaf 4. -/
def pxo : List COp := [.enter [] [lf, lf, lf, lf, lf], .write 0 [0], .write 1 [1],
  .alloc 0 1 [lf, pt 5, pt 5], .newPool 5 5, .derive 5 [6, 7] .modify, .store 6 4]
/-- State reached by `pxo` (§57). -/
def px : CState := cfinal K0 [] pxo
/-- The twin of `pool_two_freeSlot_cross` continued as the draft witness: pool 1 on `internal` 6
over the same storage; slot 0 allocated in each pool; the leaf 6 written through 6; `freeSlot` of
slot 0 of pool 1. -/
def pxto : List COp := pxo ++ [.newPool 5 6, .allocSlot 0 2, .allocSlot 1 3, .write 6 [6],
  .freeSlot 1 ⟨1, 0, 0⟩]
/-- State reached by `pxto` (§57). -/
def pxt : CState := cfinal K0 [] pxto

/-- **pool_two_freeSlot_cross** (corrected handle-pool contract, class Lib). A second pool on the
`internal` 5 of the live pool 0, over the same storage, whose `freeSlot` would end the content of a
live slot of pool 0. Expected (§56; HandlePool v0.4 annex, D.1: "Une autorité ne peut être
`internal` de deux abstractions vivantes"): `reject` at the second `newPool`. Obtained: `reject`;
the other preconditions hold. Twin, the second pool on the distinct `internal` 6 (§56: distinct
identities are not forbidden merely because their footprints overlap): `ok`, and the rest of the
run too. On that twin, the `freeSlot` of pool 1 ends the content of the place 6 (`Init` before,
`Uninit` after), which is the slot 0 of pool 0, still live at generation 0: `internal` 5 of pool 0
is an ancestor of the `internal` 6 of pool 1, hence exempt (D.3). Pool 0 cannot resolve that slot
while pool 1 lives: its `internal` has no effective right on the storage (`reject`, §43 case 3). -/
theorem pool_two_freeSlot_cross : CRunsTo K0 [] pxo px ∧
    HandlePool.NewPoolStep px.othersP 5 5 px.toP .reject ∧ NewArenaBase px.kern 5 5 ∧
    (∀ l ∈ footprint px.kern.P 5, px.kern.I l = .uninit) ∧
    CRunsTo K0 [] pxto pxt ∧ (cfinal K0 [] (pxto.take 11)).kern.I 6 = .init ∧
    pxt.kern.I 6 = .uninit ∧
    pxt.pools = [⟨0, 5, 5, [⟨6, 0, true⟩, ⟨7, 0, false⟩]⟩,
      ⟨1, 5, 6, [⟨6, 1, false⟩, ⟨7, 0, false⟩]⟩] ∧
    HandlePool.ResolveStep 0 ⟨0, 0, 0⟩ .modify pxt.toP .reject :=
  ⟨crunsTo (by decide), crejects (k := K0) (C := px) (o := .newPool 5 5) (by decide), by decide,
    by decide, crunsTo (by decide), by decide, by decide, by decide,
    crejects (k := K0) (C := pxt) (o := .resolve 0 ⟨0, 0, 0⟩ .modify) (by decide)⟩

/-! ## The guard of §56 across registries -/

/-- Common base of the guard cases (§72, §71, §60, §65): frame 1 with the value 0 and the
allocator 1, written, the value 2 and the leaf 3; storage 4 (leaves 5, 6) allocated, owned by 0,
its root authority 4 held by 0; 5, `Modify` on the whole storage from 4, stored into the value 2.
Two candidate `internal` identities, 4 and 5, cover the storage. -/
def g0 : List COp := [.enter [] [lf, lf, lf, lf], .write 1 [1], .alloc 1 0 [lf, pt 4, pt 4],
  .write 0 [0], .derive 4 [5, 6] .modify, .store 5 2]

/-- State after `g0` and `newPool 4 4` (§57). -/
def gp : CState := cfinal K0 [] (g0 ++ [.newPool 4 4])
/-- State after `g0` and `newArena 4 4` (§57). -/
def ga : CState := cfinal K0 [] (g0 ++ [.newArena 4 4])
/-- State after `g0` and `newStack 4 4` (§57). -/
def gs : CState := cfinal K0 [] (g0 ++ [.newStack 4 4])

/-- **pool_two_on_one_internal** (§56 guard, class Lib). A second pool on the `internal` 4 of a
live pool. Expected (§56: "An authority identity may serve as `internal` for at most one live
administrative abstraction"; HandlePool v0.4 annex, D.1): `reject`. Obtained: `reject`; every
other precondition of `newPool` holds. Twin, a distinct `internal` (5) over the same storage:
`ok` (§56). -/
theorem pool_two_on_one_internal : CRunsTo K0 [] (g0 ++ [.newPool 4 4]) gp ∧
    HandlePool.NewPoolStep gp.othersP 4 4 gp.toP .reject ∧ NewArenaBase gp.kern 4 4 ∧
    (∀ l ∈ footprint gp.kern.P 4, gp.kern.I l = .uninit) ∧
    Guard56 gp.othersP 4 ∧ CRuns K0 [] (g0 ++ [.newPool 4 4, .newPool 4 5]) :=
  ⟨crunsTo (by decide), crejects (k := K0) (C := gp) (o := .newPool 4 4) (by decide), by decide,
    by decide, by decide,
    crunsTo (by decide)⟩

/-- **arena_on_pool_internal** (§56 guard, class Lib). An arena on the `internal` 4 of a live pool.
Expected (§56, §76.4: "no **live** administrative abstraction, whether an arena or a library
instance such as a handle pool, already uses this `internal` identity"): `reject`. Obtained:
`reject`; `NewArenaBase` holds and a guard over the arena registry alone would accept (§56:
"checking only an abstraction's own registry is insufficient"). Twin, `internal` 5: `ok`. -/
theorem arena_on_pool_internal : CRunsTo K0 [] (g0 ++ [.newPool 4 4]) gp ∧
    NewArenaStep gp.othersA 4 4 gp.toL .reject ∧ NewArenaPre gp.kern gp.arenas [] 4 4 ∧
    CRuns K0 [] (g0 ++ [.newPool 4 4, .newArena 4 5]) :=
  ⟨crunsTo (by decide), crejects (k := K0) (C := gp) (o := .newArena 4 4) (by decide), by decide,
    crunsTo (by decide)⟩

/-- **pool_on_arena_internal** (§56 guard, class Lib). A pool on the `internal` 4 of a live arena.
Expected (§56; HandlePool v0.4 annex, D.1: the guard "sur les deux registres des abstractions
vivantes"): `reject`. Obtained: `reject`; a guard over the pool registry alone would accept. Twin,
`internal` 5: `ok`. -/
theorem pool_on_arena_internal : CRunsTo K0 [] (g0 ++ [.newArena 4 4]) ga ∧
    HandlePool.NewPoolStep ga.othersP 4 4 ga.toP .reject ∧
    HandlePool.NewPoolPre ga.kern ga.pools [] 4 4 ∧
    CRuns K0 [] (g0 ++ [.newArena 4 4, .newPool 4 5]) :=
  ⟨crunsTo (by decide), crejects (k := K0) (C := ga) (o := .newPool 4 4) (by decide), by decide,
    crunsTo (by decide)⟩

/-- **stack_on_arena_internal** (§56 guard, class Lib; DS-v1). A stack on the `internal` 4 of a
live arena. Expected (§56): `reject`. Obtained: `reject`; a guard over the stack registry alone
would accept. Twin, `internal` 5: `ok`. -/
theorem stack_on_arena_internal : CRunsTo K0 [] (g0 ++ [.newArena 4 4]) ga ∧
    DataStack.NewStackStep ga.othersD 4 4 ga.toD .reject ∧
    DataStack.NewStackPre ga.kern ga.stacks [] 4 4 ∧
    CRuns K0 [] (g0 ++ [.newArena 4 4, .newStack 4 5]) :=
  ⟨crunsTo (by decide), crejects (k := K0) (C := ga) (o := .newStack 4 4) (by decide), by decide,
    crunsTo (by decide)⟩

/-- **arena_on_stack_internal** (§56 guard, class Lib; DS-v1). An arena on the `internal` 4 of a
live stack. Expected (§56, §76.4): `reject`. Obtained: `reject`; a guard over the arena registry
alone would accept. Twin, `internal` 5: `ok`. -/
theorem arena_on_stack_internal : CRunsTo K0 [] (g0 ++ [.newStack 4 4]) gs ∧
    NewArenaStep gs.othersA 4 4 gs.toL .reject ∧ NewArenaPre gs.kern gs.arenas [] 4 4 ∧
    CRuns K0 [] (g0 ++ [.newStack 4 4, .newArena 4 5]) :=
  ⟨crunsTo (by decide), crejects (k := K0) (C := gs) (o := .newArena 4 4) (by decide), by decide,
    crunsTo (by decide)⟩

/-- **stack_on_pool_internal** (§56 guard, class Lib; DS-v1). A stack on the `internal` 4 of a live
pool. Expected (§56): `reject`. Obtained: `reject`; a guard over the stack registry alone would
accept. Twin, `internal` 5: `ok`. -/
theorem stack_on_pool_internal : CRunsTo K0 [] (g0 ++ [.newPool 4 4]) gp ∧
    DataStack.NewStackStep gp.othersD 4 4 gp.toD .reject ∧
    DataStack.NewStackPre gp.kern gp.stacks [] 4 4 ∧
    CRuns K0 [] (g0 ++ [.newPool 4 4, .newStack 4 5]) :=
  ⟨crunsTo (by decide), crejects (k := K0) (C := gp) (o := .newStack 4 4) (by decide), by decide,
    crunsTo (by decide)⟩

/-- **pool_on_stack_internal** (§56 guard, class Lib; DS-v1). A pool on the `internal` 4 of a live
stack. Expected (§56; HandlePool v0.4 annex, D.1): `reject`. Obtained: `reject`; a guard over the
pool registry alone would accept. Twin, `internal` 5: `ok`. -/
theorem pool_on_stack_internal : CRunsTo K0 [] (g0 ++ [.newStack 4 4]) gs ∧
    HandlePool.NewPoolStep gs.othersP 4 4 gs.toP .reject ∧
    HandlePool.NewPoolPre gs.kern gs.pools [] 4 4 ∧
    CRuns K0 [] (g0 ++ [.newStack 4 4, .newPool 4 5]) :=
  ⟨crunsTo (by decide), crejects (k := K0) (C := gs) (o := .newPool 4 4) (by decide), by decide,
    crunsTo (by decide)⟩

/-! ## Usage scenarios W1, W2 (material §5b) -/

/-- Run of W1 (§72, §71, §67; HandlePool v0.4 annex, D.1–D.3): frame 1 with the allocator 0, the
pool value 1 and the handle leaves 2 and 3; storage 4 owned by the pool value, with the nodes 5
(fields `data` 6, `parent` 7, `child` 8) and 9 (fields 10, 11, 12); pool on 4. The two nodes are
linked both ways (the child of the first, the parent of the second), each through a
`resolve Modify`, writes and `unresolve`; then a resolution of the first node to write its data;
then `freeSlot` of the second node, still designated by the child field of the first. -/
def w1o : List COp := [.enter [] [lf, lf, lf, lf], .write 0 [0], .write 1 [1],
  .alloc 0 1 [lf, pt 4, pt 5, pt 5, pt 5, pt 4, pt 9, pt 9, pt 9], .newPool 4 4,
  .allocSlot 0 2, .allocSlot 0 3,
  .resolve 0 ⟨0, 0, 0⟩ .modify, .write 6 [6, 8], .unresolve 5,
  .resolve 0 ⟨0, 1, 0⟩ .modify, .write 8 [10, 11], .unresolve 7,
  .resolve 0 ⟨0, 0, 0⟩ .modify, .write 10 [6], .unresolve 9,
  .freeSlot 0 ⟨0, 1, 0⟩]
/-- State reached by `w1o` (§57). -/
def w1 : CState := cfinal K0 [] w1o
/-- W1 continued by a resolution of the first node (companion 11, entry 12) (§57). -/
def w1bo : List COp := w1o ++ [.resolve 0 ⟨0, 0, 0⟩ .modify]
/-- State reached by `w1bo` (§57). -/
def w1b : CState := cfinal K0 [] w1bo

/-- **W1** (material §5b, scene graph; class Lib, not given by the material). Expected (material):
every step `ok`; `resolve` of the stale handle of the freed node `fail`; `freeSlot` during an
active resolution `reject`. Obtained: every step `ok` (the `freeSlot` of the second node ends its
written content: its fields are `Init` before and `Uninit` after, HandlePool v0.4 annex, D.3);
`resolve` of the stale handle `fail` (§89); `freeSlot` of the first node while it is resolved
`reject` (D.3). Twins: the handle of the live first node resolves (`ok`); after `unresolve`, the
`freeSlot` is `ok`. -/
theorem W1 : CRunsTo K0 [] w1o w1 ∧
    w1.pools = [⟨0, 4, 4, [⟨5, 0, true⟩, ⟨9, 1, false⟩]⟩] ∧
    (cfinal K0 [] (w1o.take 16)).kern.I 10 = .init ∧ w1.kern.I 10 = .uninit ∧
    HandlePool.ResolveStep 0 ⟨0, 1, 0⟩ .modify w1.toP .fail ∧
    CRunsTo K0 [] w1bo w1b ∧ HandlePool.FreeSlotStep K0 0 ⟨0, 0, 0⟩ w1b.toP .reject ∧
    CRuns K0 [] (w1bo ++ [.unresolve 11, .freeSlot 0 ⟨0, 0, 0⟩]) :=
  ⟨crunsTo (by decide), by decide, by decide, by decide,
    cfails (k := K0) (C := w1) (o := .resolve 0 ⟨0, 1, 0⟩ .modify) (by decide),
    crunsTo (by decide), crejects (k := K0) (C := w1b) (o := .freeSlot 0 ⟨0, 0, 0⟩) (by decide),
    crunsTo (by decide)⟩

/-- Run of W2 (§72, §71, §61, §60, §66, §67, §62; HandlePool v0.4 annex, D.2): frame 1 with the
allocator 0, the owners 1 and 2 of two archetypes, the entity pool value 3 and the handle leaves
4, 5, 6. Archetype 7 (columns 8 with rows 9, 10 and 11 with rows 12, 13) owned by 1; archetype 14
(columns 15 with 16, 17 and 18 with 19, 20) owned by 2; entity storage 21 (entries 22, 23, 24)
owned by 3, pool on it. `split` of archetype 7 into its columns (authorities 10 and 11); system B
writes column 2 and takes a read view 12 on it; system A writes column 1 while B reads through
its view; `resolveMany Modify` of three distinct entities (companion 13, entries 14–16);
system A, done, releases its column authority 10. -/
def w2o : List COp := [.enter [] [lf, lf, lf, lf, lf, lf, lf], .write 0 [0], .write 1 [1],
  .write 2 [2], .write 3 [3],
  .alloc 0 1 [lf, pt 7, pt 8, pt 8, pt 7, pt 11, pt 11],
  .alloc 0 2 [lf, pt 14, pt 15, pt 15, pt 14, pt 18, pt 18],
  .alloc 0 3 [lf, pt 21, pt 21, pt 21], .newPool 21 9,
  .allocSlot 0 4, .allocSlot 0 5, .allocSlot 0 6,
  .split 7 [[9, 10], [12, 13]], .write 11 [12, 13], .derive 11 [12, 13] .observe,
  .write 10 [9, 10], .read 12 [12, 13], .resolveMany 0 [⟨0, 0, 0⟩, ⟨0, 1, 0⟩, ⟨0, 2, 0⟩] .modify,
  .release 10]
/-- State reached by `w2o` (§57). -/
def w2 : CState := cfinal K0 [] w2o
/-- State after `w2o` and the release of the read view 12 (§57). -/
def w2a : CState := cfinal K0 [] (w2o ++ [.release 12])

/-- **W2** (material §5b, ECS archetype and sparse set; class Lib, not given by the material).
Expected (material): disjoint reads and writes `ok`; `resolveMany` `ok`; the move of a row (the
transfers of its fields) while a column view is active `reject`; after its release `ok`.
Obtained: disjoint accesses and `resolveMany` `ok`; the transfer of the field 12 into 19 while the
view lives `reject` (§63.4: the active derived 12 covers the source). After the release of the
read view 12 alone, still `reject`: the column authority 11 of the `split` covers the field
(§63.4, `ActiveDerivedOutside`); after the release of 12 and 11, the move (transfers 9 → 16 and
12 → 19) is `ok`. **MISMATCH** on the reading where "the column view" is the read view 12 alone
(after its release: expected `ok`, obtained `reject`); cause: case defect, the material does not
say whether the view is the read view or the column authority with its read view; with the latter
reading the expected verdicts are obtained. -/
theorem W2 : CRunsTo K0 [] w2o w2 ∧ TransferStep K0 12 19 w2.kern .reject ∧
    CRunsTo K0 [] (w2o ++ [.release 12]) w2a ∧ TransferStep K0 12 19 w2a.kern .reject ∧
    ActiveDerivedOutside w2a.kern 12 11 ∧
    CRuns K0 [] (w2o ++ [.release 12, .release 11, .transfer 9 16, .transfer 12 19]) :=
  ⟨crunsTo (by decide), crejects (k := K0) (C := w2) (o := .transfer 12 19) (by decide),
    crunsTo (by decide), crejects (k := K0) (C := w2a) (o := .transfer 12 19) (by decide),
    by decide, crunsTo (by decide)⟩

end Ern.Corpus.Lib
