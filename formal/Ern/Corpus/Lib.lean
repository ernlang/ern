import Ern.Corpus.LibRunner
import Ern.MemoryModel.Access.TransferSource

/-!
# Corpus: library cases (test module)

Library cases of the Jalon 3 material (`ERN_Jalon3_materiel.md`; non-normative design material)
and of the handle-pool contract, run on the reference kernel of
`specs/ERN_Memory_Model_Specification_v0.1.md` (§60–§75), the arena of Part XIV (§76–§78), the
handle pool of `Ern.Lib.HandlePool` (contract "HandlePool v0.5", non-normative: the HandlePool v0.4
annex corrected by §36 and §56 and amended by HP5-1 to HP5-7, HP5-1' and HP5-1'') and the stack of
`Ern.Lib.DataStack` (contract "DS-v2", non-normative). This is a test module: no model or library
module imports it.

* Section G of corpus MM3-H (material §1 G, handles): H30–H34b, H44.
* Cases of the handle-pool contract: stale, other pool, atomic and distinct batches, `resolveMany`
  in `Observe` with a repeated handle, `freeSlot` with a derived `internal`, under the `Modify`
  right only, on a dead pool, of a free slot; `newPool` on written storage; two pools on one
  storage (`pool_two_freeSlot_cross`).
* The guard of §56 across registries: a second administration (arena, pool, stack) on the
  `internal` of a live administration of another registry, or of the same registry for pools.
* The usage scenarios W1 and W2 of material §5b (W3 is in `Ern.Corpus.MM3H`); W2 also checks
  decision Q17 (2026-11-06) on its move (`Ern.MemoryModel.Access.TransferSource`).

Each case is a run from `CState.init statics` (§47) by the combined runner
(`Ern.Corpus.LibRunner`): `CRunsTo k statics os C` states that every step is `ok`, that `C` is
library-reachable and that its kernel state is reachable by O1–O16 (§57; the kernel part of
`freeSlot` is the write of its metadata leaves, the leaves of the pool value, §67; HandlePool v0.5,
HP5-1 with the Q3 decision of 2026-11-06). The verdict of the step under test is stated with the
relation of its operation on the projected state (`ResolveStep`, `FreeSlotStep`, `NewPoolStep`,
`NewArenaStep`, `NewStackStep`, `StoreStep`, `TransferStep`, …) and decided by `decide`. Each
docstring gives the expected verdict from the case's source, the obtained verdict, the class
(material §0, rule 5: `Lib` library instance) and the positive twin of each rejection or `fail`
(rule 2: the same sequence without the faulty element, accepted). Where spec v0.1, HandlePool v0.5
or DS-v2 changes the verdict the source gave, the docstring records the historical expected
verdict, its justification, the new expected verdict and the clause or contract item that decides
it (arbitration Q21). A case whose obtained verdict differs from the expected one keeps its
expected verdict and is marked **MISMATCH** with its cause.

Twins that are not literally the same sequence without one faulty step:
* another handle, entry, target, parameter or identity in place of the faulty one: H30 (the handle
  of generation 1), H31b (two distinct entries), H33 (the local 4), H34b (pool 0),
  `resolveMany_atomic` (the valid handle `⟨0, 1, 0⟩`), `pool_shared_right` (a `Modify` parameter),
  `pool_two_freeSlot_cross` at `newPool` (`internal` 6), `pool_two_on_one_internal`,
  `arena_on_pool_internal`, `pool_on_arena_internal`, `stack_on_arena_internal`,
  `arena_on_stack_internal`, `stack_on_pool_internal`, `pool_on_stack_internal` (`internal` 5), W1
  `fail` (the handle of the live first node);
* further steps that lift the blocking before the step under test: H31a (`unresolve 5`, for the
  other entry and for the `Observe` resolution) and H32 (`unresolve`), `pool_free_entry_handle`
  (`allocSlot` first), W1 `reject` (`unresolve`), W1 historical `freeSlot` (the removal of the
  value, arbitration Q21), W2 (`release` of 12 and 11, and the transfer 9 → 16);
* a faulty element of several steps, removed: `pool_two_freeSlot_cross` at `resolve` (the
  authority 6 and the steps that use it; removing pool 1 alone leaves the `reject`);
* two faults removed together (arbitration Q19): the `fail` of H31a for the stale handle
  `⟨0, 1, 7⟩` during the resolution; its twin is the resolution of `⟨0, 1, 0⟩` after `unresolve 5`
  (conjunct 5 of H31a), the stale generation and the active companion both removed.

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

/-! ## G. Handles (material §1 G; HandlePool v0.5) -/

/-- Pool base of section G (§72, §71, §67; HandlePool v0.5, D.1): frame 1 with the allocator
0 and the pool value 1, written, and the handle leaves 2 and 3; storage 4 (entries 5 and 6)
allocated, owned by the pool value, its root authority 4 held by it; `newPool 4 4`: pool 0 of
identity 0, slots 5 and 6, free, generation 0. -/
def pb : List COp := [.enter [] [lf, lf, lf, lf], .write 0 [0], .write 1 [1],
  .alloc 0 1 [lf, pt 4, pt 4], .newPool 4 4]

/-- Run of H30 (HandlePool v0.5, D.3, HP5-1): the slot 0 allocated (handle in 2), freed (its
entry was never written, so no leaf is `Init`), then allocated again (handle in 3, generation 1). -/
def h30o : List COp := pb ++ [.allocSlot 0 2, .freeSlot 0 ⟨0, 0, 0⟩, .allocSlot 0 3]
/-- State reached by `h30o` (§57). -/
def h30 : CState := cfinal K0 [] h30o

/-- **H30** (material §1 G, class Lib). Resolution of a handle after the release and the reuse of
its entry. Expected (material, HandlePool contract, generation; §89): `fail`. Obtained: `fail`:
the slot is live at generation 1, the handle carries generation 0 (§89: a stale generation leads to
defined failure; HandlePool v0.5, HP5-5: checked before the right). Twin, the handle of the reused
entry: `resolve` is `ok`. -/
theorem H30 : CRunsTo K0 [] h30o h30 ∧
    h30.pools = [⟨0, 4, 4, [⟨5, 1, true⟩, ⟨6, 0, false⟩]⟩] ∧
    HandlePool.ResolveStep 0 ⟨0, 0, 0⟩ .modify h30.toP .fail ∧
    CRuns K0 [] (h30o ++ [.resolve 0 ⟨0, 0, 1⟩ .modify]) :=
  ⟨crunsTo (by decide), by decide,
    cfails (k := K0) (C := h30) (o := .resolve 0 ⟨0, 0, 0⟩ .modify) (by decide),
    crunsTo (by decide)⟩

/-- Run of H31a and H32 (HandlePool v0.5, D.2): both slots allocated (handles in 2 and 3),
slot 0 resolved in `Modify`: companion 5 over the storage, entry authority 6 over the slot 5. -/
def h31o : List COp := pb ++ [.allocSlot 0 2, .allocSlot 0 3, .resolve 0 ⟨0, 0, 0⟩ .modify]
/-- State reached by `h31o` (§57). -/
def h31 : CState := cfinal K0 [] h31o

/-- State reached by `h31o` and the `unresolve` of the companion 5 (HandlePool v0.5, D.2; §57):
the twin state of the H31a rejections. -/
def h31u : CState := cfinal K0 [] (h31o ++ [.unresolve 5])

/-- **H31a** (material §1 G, class Lib). Two simultaneous `resolve Modify`. Expected (material,
exclusivity of the pool value): the second `reject`. Obtained: `reject` for the other entry and for
an `Observe` resolution: the active `Modify` companion 5 leaves `internal` no effective mode on the
storage, so the companion of the second resolution cannot be derived (§43 case 3, §60.2;
HandlePool v0.5, D.2: "Une compagne `Modify` active bloque les nouvelles compagnes"). Twins, after
`unresolve 5` of the first: the resolution of the other entry, `ok` (conjunct 5); the `Observe`
resolution of `⟨0, 0, 0⟩`, `ok`.

The stale handle `⟨0, 1, 7⟩` during the resolution. Historical expected verdict: `reject` (the
second resolution meets the active companion, whatever its handle). New expected verdict: `fail`
(HandlePool v0.5, HP5-5, arbitration Q5: "la validation du handle précède le contrôle du droit";
§89: a stale generation leads to defined failure). Obtained: `fail`, and `fail` again after
`unresolve 5` (state `h31u`, last conjunct): the companion takes no part in the outcome. Twin, the
stale generation and the active companion both removed: the resolution of `⟨0, 1, 0⟩` after
`unresolve 5` (conjunct 5), `ok`; arbitration Q19 accepts this multi-step twin. -/
theorem H31a : CRunsTo K0 [] h31o h31 ∧
    HandlePool.ResolveStep 0 ⟨0, 1, 0⟩ .modify h31.toP .reject ∧
    HandlePool.ResolveStep 0 ⟨0, 1, 7⟩ .modify h31.toP .fail ∧
    HandlePool.ResolveStep 0 ⟨0, 0, 0⟩ .observe h31.toP .reject ∧
    CRuns K0 [] (h31o ++ [.unresolve 5, .resolve 0 ⟨0, 1, 0⟩ .modify]) ∧
    CRuns K0 [] (h31o ++ [.unresolve 5, .resolve 0 ⟨0, 0, 0⟩ .observe]) ∧
    CRunsTo K0 [] (h31o ++ [.unresolve 5]) h31u ∧
    HandlePool.ResolveStep 0 ⟨0, 1, 7⟩ .modify h31u.toP .fail :=
  ⟨crunsTo (by decide),
    crejects (k := K0) (C := h31) (o := .resolve 0 ⟨0, 1, 0⟩ .modify) (by decide),
    cfails (k := K0) (C := h31) (o := .resolve 0 ⟨0, 1, 7⟩ .modify) (by decide),
    crejects (k := K0) (C := h31) (o := .resolve 0 ⟨0, 0, 0⟩ .observe) (by decide),
    crunsTo (by decide), crunsTo (by decide), crunsTo (by decide),
    cfails (k := K0) (C := h31u) (o := .resolve 0 ⟨0, 1, 7⟩ .modify) (by decide)⟩

/-- Run of H31b (HandlePool v0.5, D.3): both slots allocated, handles in 2 and 3. -/
def h31bo : List COp := pb ++ [.allocSlot 0 2, .allocSlot 0 3]
/-- State reached by `h31bo` (§57). -/
def h31b : CState := cfinal K0 [] h31bo

/-- **H31b** (material §1 G, class Lib). `resolveMany Modify` of two handles designating the same
entry. Expected (material, dynamic distinctness; HandlePool v0.5, D.2, HP5-5): `fail`. Obtained:
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
compagne ne doit subsister sur cette entrée"; HandlePool v0.5, HP5-1': no active strict descendant
of the pool's `internal` covers the entry): `reject`. Obtained: `reject`: the companion 5 and the
entry authority 6, active strict descendants of `internal` 4, cover the slot 5 (`NoInternalDesc`
fails; the handle is valid and the administration right holds, HP5-1''). The `freeSlot` of the
other slot 1 during the same resolution is `reject` as well, the companion covering the whole
storage (material §4: "pendant toute résolution du pool"). Twin, after `unresolve` of the
resolution: both `ok` (the entries were never written, so no leaf is `Init`, HP5-1). -/
theorem H32 : CRunsTo K0 [] h31o h31 ∧
    HandlePool.FreeSlotStep 0 ⟨0, 0, 0⟩ h31.toP .reject ∧
    HandlePool.FreeSlotStep 0 ⟨0, 1, 0⟩ h31.toP .reject ∧
    CRuns K0 [] (h31o ++ [.unresolve 5, .freeSlot 0 ⟨0, 0, 0⟩]) ∧
    CRuns K0 [] (h31o ++ [.unresolve 5, .freeSlot 0 ⟨0, 1, 0⟩]) :=
  ⟨crunsTo (by decide), crejects (k := K0) (C := h31) (o := .freeSlot 0 ⟨0, 0, 0⟩) (by decide),
    crejects (k := K0) (C := h31) (o := .freeSlot 0 ⟨0, 1, 0⟩) (by decide), crunsTo (by decide),
    crunsTo (by decide)⟩

/-- Run of H33 (§72, §71; HandlePool v0.5, D.1–D.3): frame 1 with the local 0 passes 1,
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
handle is data, not an authority; HandlePool v0.5, D.2). -/
theorem H34 : CRuns K0 [] (pb ++ [.allocSlot 0 2, .read 2 [2], .write 3 [3],
    .resolve 0 ⟨0, 0, 0⟩ .modify, .write 6 [5], .unresolve 5, .resolve 0 ⟨0, 0, 0⟩ .modify]) :=
  crunsTo (by decide)

/-- Run of H34b (§71; HandlePool v0.5, D.1): a second storage 7 (entries 8, 9) owned by the
pool value 1, its root 5 the `internal` of pool 1, of identity 1; slot 0 of pool 0 allocated. -/
def h34bo : List COp := pb ++ [.alloc 0 1 [lf, pt 7, pt 7], .newPool 7 5, .allocSlot 0 2]
/-- State reached by `h34bo` (§57). -/
def h34b : CState := cfinal K0 [] h34bo

/-- **H34b** (material §1 G, class Lib). A handle of another pool. Expected (material, identity of
the pool; §89; HandlePool v0.5, HP5-5): `fail`. Obtained: `fail`: the handle names identity 0,
pool 1 has identity 1. Twin, the same handle on its own pool: `ok`. -/
theorem H34b : CRunsTo K0 [] h34bo h34b ∧ h34b.pools.map (·.id) = [0, 1] ∧
    HandlePool.ResolveStep 1 ⟨0, 0, 0⟩ .modify h34b.toP .fail ∧
    CRuns K0 [] (h34bo ++ [.resolve 0 ⟨0, 0, 0⟩ .modify]) :=
  ⟨crunsTo (by decide), by decide,
    cfails (k := K0) (C := h34b) (o := .resolve 1 ⟨0, 0, 0⟩ .modify) (by decide),
    crunsTo (by decide)⟩

/-- Run of H44 (§71, §76–§78; HandlePool v0.5, D.1–D.3): frame 1 with the arena value 0,
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
Obtained: `ok` at every step (§89, §37, §78.2; HandlePool v0.5, D.1: the block region was never
written, so `newPool` finds `Uninit` storage). -/
theorem H44 : CRuns K0 [] h44o :=
  crunsTo (by decide)

/-! ## Handle-pool contract (HandlePool v0.5) -/

/-- State after the first nine steps of `h44o`: the pool on the arena block, both slots allocated,
nothing resolved (§57). -/
def fdi : CState := cfinal K0 [] (h44o.take 9)

/-- **pool_freeSlot_derived_internal** (handle-pool contract, class Lib). `freeSlot` on a pool
whose `internal` is a derived authority (the arena block 6) held by the pool value, outside the
slot. Expected (HandlePool v0.4 annex, D.3: "aucune autorité active ne couvre l'entrée hors
`internal` et ses ancêtres"; "Le contrôle n'interprète pas `internal` comme un emprunt externe";
HandlePool v0.5, HP5-1': only strict descendants of `internal` block): `ok`. Obtained: `ok` (the
entry was never written and no active strict descendant of `internal` 6 covers it).

The kernel `endUse` of the slot place 7 on the same state. Historical verdict: `reject` (spec v0
§69.2: `internal` 6, active, derived, covering the slot, is held outside it; the exemption of
`internal` then decided the `freeSlot` verdict of the v0.4 annex, whose `freeSlot` ended the
content). New verdict: `ok` (v0.1 §69.2, the exemption of the authority on which the `Modify`
right over the place rests and of its origin chain: that right over the place 7 rests on 6).
Obtained: `ok` (`EndUsePre`). Under HandlePool v0.5 `freeSlot` has no end-of-use effect (HP5-1),
so the two verdicts no longer depend on each other. -/
theorem pool_freeSlot_derived_internal : CRunsTo K0 [] (h44o.take 9) fdi ∧
    EndUsePre K0 fdi.kern 7 ∧ CRuns K0 [] (h44o.take 9 ++ [.freeSlot 0 ⟨0, 0, 0⟩]) :=
  ⟨crunsTo (by decide), by decide, crunsTo (by decide)⟩

/-- **resolveMany_observe_repeat** (handle-pool contract, class Lib). `resolveMany` in
`Observe` of a repeated valid handle. Expected (HandlePool v0.5, D.2: "sans `split` ni
contrôle de distinction : la répétition du même handle valide est permise"): `ok`. Obtained: `ok`
(one `Observe` companion, two `Observe` entry authorities derived from it, §60). The same batch in
`Modify` is `fail` (`H31b`). -/
theorem resolveMany_observe_repeat :
    CRuns K0 [] (h31bo ++ [.resolveMany 0 [⟨0, 0, 0⟩, ⟨0, 0, 0⟩] .observe]) :=
  crunsTo (by decide)

/-- **resolveMany_atomic** (handle-pool contract, class Lib). `resolveMany Modify` of a batch with
one valid handle and one stale handle. Expected (HandlePool v0.5, D.2: "`fail` atomique, sans
création partielle de droits"; HP5-5): `fail`. Obtained: `fail`, and `fail` is the only outcome of
the relation (no authority is created, §58). Twin without the stale handle (the two valid
handles): `ok`. -/
theorem resolveMany_atomic :
    HandlePool.ResolveManyStep K0 0 [⟨0, 0, 0⟩, ⟨0, 1, 5⟩] .modify h31b.toP .fail ∧
    (∀ o, HandlePool.ResolveManyStep K0 0 [⟨0, 0, 0⟩, ⟨0, 1, 5⟩] .modify h31b.toP o →
      o = .fail) ∧
    CRuns K0 [] (h31bo ++ [.resolveMany 0 [⟨0, 0, 0⟩, ⟨0, 1, 0⟩] .modify]) :=
  ⟨cfails (k := K0) (C := h31b) (o := .resolveMany 0 [⟨0, 0, 0⟩, ⟨0, 1, 5⟩] .modify) (by decide),
    (HandlePool.pool_resolveMany_invalid_fails (k := K0) (L := h31b.toP) (j := 0)
      (pl := ⟨0, 4, 4, [⟨5, 0, true⟩, ⟨6, 0, true⟩]⟩) (hs := [⟨0, 0, 0⟩, ⟨0, 1, 5⟩])
      (m := .modify) (by decide) (by decide)).2,
    crunsTo (by decide)⟩

/-- Run of `pool_newPool_written` (§72, §71, §67): the pool base with the entry 5 written before
`newPool`. -/
def pnwo : List COp := [.enter [] [lf, lf, lf, lf], .write 0 [0], .write 1 [1],
  .alloc 0 1 [lf, pt 4, pt 4], .write 4 [5]]
/-- State reached by `pnwo` (§57). -/
def pnw : CState := cfinal K0 [] pnwo

/-- **pool_newPool_written** (handle-pool contract, class Lib; the draft witness
`pool_allocSlot_content_init`). `newPool` on a storage whose leaf 5 was written. Expected
(HandlePool v0.5, D.1: "`newPool(storage, internal)` exige que toutes les feuilles du stockage
d'entrée soient `Uninit`"): `reject`. Obtained: `reject`; the other preconditions (those of
`newArena`, §76.1–§76.3, §76.5, §76.6, and the guard of §56) hold. Twin without the write:
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

/-- **pool_free_entry_handle** (handle-pool contract, class Lib). `freeSlot` of a free slot whose
identity and generation match the handle. Historical expected verdict: not `ok`, `fail` or `reject`
to arbitrate (HandlePool v0.4 annex, D.3: "un slot déjà libre n'est pas rendu libérable par cette
seule égalité"; the pool module read it as `fail`, HandlePool reading H-R2, a mismatch in form).
New expected verdict: `fail` (HandlePool v0.5, HP5-6, arbitration Q12: "un handle d'entrée libre
est périmé : fail"; HP5-1'': `fail` on an invalid handle). Obtained: `fail`; `resolveMany` of the
same handle is `fail` too (HP5-5, HP5-6). Twins, the slot allocated first: `freeSlot` is `ok`;
`resolveMany` is `ok`. -/
theorem pool_free_entry_handle : CRunsTo K0 [] pb pb0 ∧
    HandlePool.FreeSlotStep 0 ⟨0, 0, 0⟩ pb0.toP .fail ∧
    HandlePool.ResolveManyStep K0 0 [⟨0, 0, 0⟩] .modify pb0.toP .fail ∧
    CRuns K0 [] (pb ++ [.allocSlot 0 2, .freeSlot 0 ⟨0, 0, 0⟩]) ∧
    CRuns K0 [] (pb ++ [.allocSlot 0 2, .resolveMany 0 [⟨0, 0, 0⟩] .modify]) :=
  ⟨crunsTo (by decide), cfails (k := K0) (C := pb0) (o := .freeSlot 0 ⟨0, 0, 0⟩) (by decide),
    cfails (k := K0) (C := pb0) (o := .resolveMany 0 [⟨0, 0, 0⟩] .modify) (by decide),
    crunsTo (by decide), crunsTo (by decide)⟩

/-- Run of `pool_dead` (§69): slot 0 allocated (handle in 2), then `endUse` of the pool value 1,
which releases `internal` (§69 effect: the authorities held by the place end). -/
def pdo : List COp := pb ++ [.allocSlot 0 2, .endUse 1]
/-- State reached by `pdo` (§57). -/
def pd : CState := cfinal K0 [] pdo

/-- **pool_dead** (handle-pool contract, class Lib). `allocSlot` and `freeSlot` on a pool whose
`internal` is no longer active; `internal` 4 is inactive while `MetaRight` (§36, `Modify` over the
pool value) still holds. `allocSlot`: expected (HandlePool v0.5, D.3: "`allocSlot(pool, dst)` exige
un pool vivant") `reject`; obtained `reject`. `freeSlot`: historical expected verdict `reject`
(HandlePool v0.4 annex, D.3: "`freeSlot(h)` exige un pool **vivant**", a precondition checked
before the handle); new expected verdict `fail` (HandlePool v0.5, HP5-1'', arbitration Q5 extended
to `freeSlot`: "le handle d'un pool mort donne fail"); obtained `fail`. Twins without the `endUse`:
`allocSlot` and `freeSlot` are `ok`. -/
theorem pool_dead : CRunsTo K0 [] pdo pd ∧ ¬ pd.kern.Active 4 ∧
    MetaRight pd.kern ⟨4, 4, [], []⟩ ∧
    HandlePool.AllocSlotStep 0 3 pd.toP .reject ∧
    HandlePool.FreeSlotStep 0 ⟨0, 0, 0⟩ pd.toP .fail ∧
    CRuns K0 [] (pb ++ [.allocSlot 0 2, .allocSlot 0 3]) ∧
    CRuns K0 [] (pb ++ [.allocSlot 0 2, .freeSlot 0 ⟨0, 0, 0⟩]) :=
  ⟨crunsTo (by decide), by decide, by decide,
    crejects (k := K0) (C := pd) (o := .allocSlot 0 3) (by decide),
    cfails (k := K0) (C := pd) (o := .freeSlot 0 ⟨0, 0, 0⟩) (by decide), crunsTo (by decide),
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

/-- **pool_shared_right** (handle-pool contract, class Lib; the draft witness
`pool_freeSlot_shared_right`). A callee that may update the pool metadata only by `writeShared`
calls `allocSlot` and `freeSlot`. Expected (§36: `MetaRight` requires `Modify` exercisable on the
administering value, the `writeShared` branch alone is insufficient; this overrides the
`writeShared` right of material §4 and of HandlePool v0.4 annex, D.3): `reject`, `reject`.
Obtained: the `writeShared` is `ok` (§68), `allocSlot` and `freeSlot` are `reject` (`¬ MetaRight`;
the handle of `freeSlot` is valid, so the right decides, HandlePool v0.5, HP5-1''). Twin, the same
run with a `Modify` parameter on the pool value: `allocSlot` then `freeSlot` are `ok` (the
`freeSlot` under the `Modify` right). -/
theorem pool_shared_right : CRunsTo KSh [] psro psr ∧ ¬ MetaRight psr.kern ⟨4, 4, [], []⟩ ∧
    HandlePool.AllocSlotStep 0 7 psr.toP .reject ∧
    HandlePool.FreeSlotStep 0 ⟨0, 0, 0⟩ psr.toP .reject ∧
    CRuns KSh [] (pb ++ [.allocSlot 0 2, .derive 1 [1] .modify, .enter [5] [lf],
      .writeShared 5 [1], .allocSlot 0 7, .freeSlot 0 ⟨0, 0, 0⟩]) :=
  ⟨crunsTo (by decide), by decide, crejects (k := KSh) (C := psr) (o := .allocSlot 0 7) (by decide),
    crejects (k := KSh) (C := psr) (o := .freeSlot 0 ⟨0, 0, 0⟩) (by decide), crunsTo (by decide)⟩

/-- Base of `pool_two_freeSlot_cross` (§72, §71, §60, §65; HandlePool v0.5, D.1): frame 1 with
the allocator 0, the pool value 1 and the leaves 2, 3, 4; storage 5 (entries 6, 7) owned by 1,
pool 0 on it with `internal` its root 5; then 6, `Modify` on the whole storage from 5, stored into
the leaf 4. -/
def pxo : List COp := [.enter [] [lf, lf, lf, lf, lf], .write 0 [0], .write 1 [1],
  .alloc 0 1 [lf, pt 5, pt 5], .newPool 5 5, .derive 5 [6, 7] .modify, .store 6 4]
/-- State reached by `pxo` (§57). -/
def px : CState := cfinal K0 [] pxo
/-- The twin of `pool_two_freeSlot_cross` continued as the draft witness, up to its `freeSlot`:
pool 1 on `internal` 6 over the same storage; slot 0 allocated in each pool (the place 6 in both);
the leaf 6 written through 6. -/
def pxwo : List COp := pxo ++ [.newPool 5 6, .allocSlot 0 2, .allocSlot 1 3, .write 6 [6]]
/-- State reached by `pxwo` (§57). -/
def pxw : CState := cfinal K0 [] pxwo
/-- The same continuation without the write, then `freeSlot` of slot 0 of pool 1 (HandlePool
v0.5, HP5-1). -/
def pxto : List COp := pxo ++ [.newPool 5 6, .allocSlot 0 2, .allocSlot 1 3, .freeSlot 1 ⟨1, 0, 0⟩]
/-- State reached by `pxto` (§57). -/
def pxt : CState := cfinal K0 [] pxto

/-- **pool_two_freeSlot_cross** (handle-pool contract, class Lib). A second pool on the `internal`
5 of the live pool 0, over the same storage. Expected (§56; HandlePool v0.5, D.1: "Une autorité ne
peut être `internal` de deux abstractions vivantes"): `reject` at the second `newPool`. Obtained:
`reject`; the other preconditions hold. Twin, the second pool on the distinct `internal` 6 (§56:
distinct identities over overlapping footprints are not forbidden): `ok`.

That twin continued as the draft witness: each pool allocates its slot 0, the place 6; the leaf 6
is written through 6; then `freeSlot` of slot 0 of pool 1. Historical verdict of this `freeSlot`:
`ok`, ending the content of the place 6, a live slot of pool 0 (HandlePool v0.4 annex, D.3: the
`internal` 5 of pool 0, an ancestor of the `internal` 6 of pool 1, is exempt). New verdict:
`reject` (HandlePool v0.5, HP5-1: no leaf of the entry may be `Init`; the leaf 6 is `Init`).
Obtained: `reject`. Twin without the write: `ok`; the leaf 6 stays `Uninit` and the slot 0 of
pool 0 stays live at generation 0 (the kernel write of `freeSlot` covers only the leaf 4, the value
of pool 1, which holds its `internal` 6; HandlePool v0.5, HP5-1 with the Q3 decision of
2026-11-06). On that state pool 0 cannot resolve its slot while the `internal` 6 of pool 1 is
active: its own `internal` 5 has no effective right on the storage (`reject`, §43 case 3). Twin of
that `reject`: the same sequence without the authority 6 (its `derive` and `store`) and the steps
that use it (pool 1, its slot, its `freeSlot`): `allocSlot` then `resolve` in pool 0, `ok`.
Dropping only the steps of pool 1 does not lift the `reject`: 6 is active from its `derive` on,
before pool 1 exists. -/
theorem pool_two_freeSlot_cross : CRunsTo K0 [] pxo px ∧
    HandlePool.NewPoolStep px.othersP 5 5 px.toP .reject ∧ NewArenaBase px.kern 5 5 ∧
    (∀ l ∈ footprint px.kern.P 5, px.kern.I l = .uninit) ∧
    CRunsTo K0 [] pxwo pxw ∧ pxw.kern.I 6 = .init ∧
    HandlePool.FreeSlotStep 1 ⟨1, 0, 0⟩ pxw.toP .reject ∧
    CRunsTo K0 [] pxto pxt ∧ pxt.kern.I 6 = .uninit ∧
    pxt.pools = [⟨0, 5, 5, [⟨6, 0, true⟩, ⟨7, 0, false⟩]⟩,
      ⟨1, 5, 6, [⟨6, 1, false⟩, ⟨7, 0, false⟩]⟩] ∧
    HandlePool.ResolveStep 0 ⟨0, 0, 0⟩ .modify pxt.toP .reject ∧
    CRuns K0 [] (pxo.take 5 ++ [.allocSlot 0 2, .resolve 0 ⟨0, 0, 0⟩ .modify]) :=
  ⟨crunsTo (by decide), crejects (k := K0) (C := px) (o := .newPool 5 5) (by decide), by decide,
    by decide, crunsTo (by decide), by decide,
    crejects (k := K0) (C := pxw) (o := .freeSlot 1 ⟨1, 0, 0⟩) (by decide),
    crunsTo (by decide), by decide, by decide,
    crejects (k := K0) (C := pxt) (o := .resolve 0 ⟨0, 0, 0⟩ .modify) (by decide),
    crunsTo (by decide)⟩

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
administrative abstraction"; HandlePool v0.5, D.1): `reject`. Obtained: `reject`; every
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
Expected (§56; HandlePool v0.5, D.1: the guard "sur les deux registres des abstractions
vivantes"): `reject`. Obtained: `reject`; a guard over the pool registry alone would accept. Twin,
`internal` 5: `ok`. -/
theorem pool_on_arena_internal : CRunsTo K0 [] (g0 ++ [.newArena 4 4]) ga ∧
    HandlePool.NewPoolStep ga.othersP 4 4 ga.toP .reject ∧
    HandlePool.NewPoolPre ga.kern ga.pools [] 4 4 ∧
    CRuns K0 [] (g0 ++ [.newArena 4 4, .newPool 4 5]) :=
  ⟨crunsTo (by decide), crejects (k := K0) (C := ga) (o := .newPool 4 4) (by decide), by decide,
    crunsTo (by decide)⟩

/-- **stack_on_arena_internal** (§56 guard, class Lib; DS-v2). A stack on the `internal` 4 of a
live arena. Expected (§56): `reject`. Obtained: `reject`; a guard over the stack registry alone
would accept. Twin, `internal` 5: `ok`. -/
theorem stack_on_arena_internal : CRunsTo K0 [] (g0 ++ [.newArena 4 4]) ga ∧
    DataStack.NewStackStep ga.othersD 4 4 ga.toD .reject ∧
    DataStack.NewStackPre ga.kern ga.stacks [] 4 4 ∧
    CRuns K0 [] (g0 ++ [.newArena 4 4, .newStack 4 5]) :=
  ⟨crunsTo (by decide), crejects (k := K0) (C := ga) (o := .newStack 4 4) (by decide), by decide,
    crunsTo (by decide)⟩

/-- **arena_on_stack_internal** (§56 guard, class Lib; DS-v2). An arena on the `internal` 4 of a
live stack. Expected (§56, §76.4): `reject`. Obtained: `reject`; a guard over the arena registry
alone would accept. Twin, `internal` 5: `ok`. -/
theorem arena_on_stack_internal : CRunsTo K0 [] (g0 ++ [.newStack 4 4]) gs ∧
    NewArenaStep gs.othersA 4 4 gs.toL .reject ∧ NewArenaPre gs.kern gs.arenas [] 4 4 ∧
    CRuns K0 [] (g0 ++ [.newStack 4 4, .newArena 4 5]) :=
  ⟨crunsTo (by decide), crejects (k := K0) (C := gs) (o := .newArena 4 4) (by decide), by decide,
    crunsTo (by decide)⟩

/-- **stack_on_pool_internal** (§56 guard, class Lib; DS-v2). A stack on the `internal` 4 of a live
pool. Expected (§56): `reject`. Obtained: `reject`; a guard over the stack registry alone would
accept. Twin, `internal` 5: `ok`. -/
theorem stack_on_pool_internal : CRunsTo K0 [] (g0 ++ [.newPool 4 4]) gp ∧
    DataStack.NewStackStep gp.othersD 4 4 gp.toD .reject ∧
    DataStack.NewStackPre gp.kern gp.stacks [] 4 4 ∧
    CRuns K0 [] (g0 ++ [.newPool 4 4, .newStack 4 5]) :=
  ⟨crunsTo (by decide), crejects (k := K0) (C := gp) (o := .newStack 4 4) (by decide), by decide,
    crunsTo (by decide)⟩

/-- **pool_on_stack_internal** (§56 guard, class Lib; DS-v2). A pool on the `internal` 4 of a live
stack. Expected (§56; HandlePool v0.5, D.1): `reject`. Obtained: `reject`; a guard over the
pool registry alone would accept. Twin, `internal` 5: `ok`. -/
theorem pool_on_stack_internal : CRunsTo K0 [] (g0 ++ [.newStack 4 4]) gs ∧
    HandlePool.NewPoolStep gs.othersP 4 4 gs.toP .reject ∧
    HandlePool.NewPoolPre gs.kern gs.pools [] 4 4 ∧
    CRuns K0 [] (g0 ++ [.newStack 4 4, .newPool 4 5]) :=
  ⟨crunsTo (by decide), crejects (k := K0) (C := gs) (o := .newPool 4 4) (by decide), by decide,
    crunsTo (by decide)⟩

/-! ## Usage scenarios W1, W2 (material §5b) -/

/-- Run of W1 (§72, §71, §67, §63; HandlePool v0.5, D.1–D.3, HP5-1): frame 1 with the allocator
0, the pool value 1, the handle leaves 2 and 3, and two locals of the shape of a node, 4 (fields 5,
6, 7) and 8 (fields 9, 10, 11); storage 12 owned by the pool value, with the nodes 13 (fields
`data` 14, `parent` 15, `child` 16) and 17 (fields 18, 19, 20); pool on 12, its `internal` the
root authority 6 of the storage. The two nodes are linked both ways (the child of the first, the
parent of the second), each through a `resolve Modify`, writes and `unresolve`; then a resolution
of the first node to write its data. The value of the second node is then removed (arbitration
Q21, along the path of the Q3 witness): `resolve Modify` (companion 13, entry 14), write of its
last field not yet written (20), `transfer` of the entry to the local 4, `unresolve`. Last,
`freeSlot` of the second node, still designated by the child field of the first. -/
def w1o : List COp := [.enter [] [lf, lf, lf, lf, lf, pt 4, pt 4, pt 4, lf, pt 8, pt 8, pt 8],
  .write 0 [0], .write 1 [1],
  .alloc 0 1 [lf, pt 12, pt 13, pt 13, pt 13, pt 12, pt 17, pt 17, pt 17], .newPool 12 6,
  .allocSlot 0 2, .allocSlot 0 3,
  .resolve 0 ⟨0, 0, 0⟩ .modify, .write 8 [14, 16], .unresolve 7,
  .resolve 0 ⟨0, 1, 0⟩ .modify, .write 10 [18, 19], .unresolve 9,
  .resolve 0 ⟨0, 0, 0⟩ .modify, .write 12 [14], .unresolve 11,
  .resolve 0 ⟨0, 1, 0⟩ .modify, .write 14 [20], .transfer 17 4, .unresolve 13,
  .freeSlot 0 ⟨0, 1, 0⟩]
/-- State reached by `w1o` (§57). -/
def w1 : CState := cfinal K0 [] w1o
/-- State of the historical run of W1 just before its `freeSlot`: the first 16 steps of `w1o`,
the value of the second node not removed (§57). -/
def w1l : CState := cfinal K0 [] (w1o.take 16)
/-- W1 continued by a resolution of the first node (companion 15, entry 16), the write of its
field 15 and the `transfer` of its value to the local 8, the resolution still active (arbitration
Q21; §57). -/
def w1bo : List COp := w1o ++ [.resolve 0 ⟨0, 0, 0⟩ .modify, .write 16 [15], .transfer 13 8]
/-- State reached by `w1bo` (§57). -/
def w1b : CState := cfinal K0 [] w1bo

/-- **W1** (material §5b, scene graph; class Lib, not given by the material). Expected (material):
every step `ok`; `resolve` of the stale handle of the freed node `fail`; `freeSlot` during an
active resolution `reject`.

Historical run: the `freeSlot` of the second node right after its fields were written, `ok`,
ending its written content (HandlePool v0.4 annex, D.3). Under HandlePool v0.5 that `freeSlot` is
`reject` (HP5-1: no leaf of the entry may be `Init`; the fields 18 and 19 are), stated on the state
`w1l`. Arbitration Q21 revises the case: the value is removed before `freeSlot`, by
`resolve Modify`, write, `transfer` of the entry to a local and `unresolve` (the path of the Q3
witness, HandlePool v0.5, HP5-2); the same removal precedes the `freeSlot` of the first node. New
expected verdicts: every step of the revised run `ok`; the other verdicts unchanged. For the
`transfer` 17 → 4 the verdict is decided by v0.1 §63.4: the companion 13 and the entry 14, active
derived authorities held outside the source, cover it, but the `Modify` right over 17 rests on 14,
whose origin chain contains 13, so both are exempt (spec v0 §63.4, without the exemption, rejects
that `transfer`); the same exemption decides the `transfer` 13 → 8 of `w1bo` (the right rests on
the entry 16, the companion 15 on its origin chain). For the `freeSlot` it is decided by
HandlePool v0.5, HP5-1 and HP5-1' (no leaf of the entry `Init`; no active strict descendant of
`internal` 6 covers it).

Obtained: every step `ok`; after the run the fields of the second node are `Moved` and the local 4
is `Init` (§63 effect). `resolve` of the stale handle `fail` (§89; HandlePool v0.5, HP5-5, HP5-6:
the slot is free at generation 1). `freeSlot` of the first node while it is resolved, its value
already moved to the local 8, `reject` (HP5-1': its companion 15 and entry 16, active strict
descendants of `internal` 6, cover it; the resolution is the only fault). Twins: the handle of the
live first node resolves (`ok`, the first step after `w1o` in `w1bo`); after `unresolve 15`, the
`freeSlot` is `ok`; the twin of the historical `reject` is the revised run. -/
theorem W1 : CRunsTo K0 [] w1o w1 ∧
    w1.pools = [⟨0, 12, 6, [⟨13, 0, true⟩, ⟨17, 1, false⟩]⟩] ∧
    CRunsTo K0 [] (w1o.take 16) w1l ∧ w1l.kern.I 18 = .init ∧
    HandlePool.FreeSlotStep 0 ⟨0, 1, 0⟩ w1l.toP .reject ∧
    (∀ l ∈ footprint w1.kern.P 17, w1.kern.I l = .moved) ∧
    (∀ l ∈ footprint w1.kern.P 4, w1.kern.I l = .init) ∧
    HandlePool.ResolveStep 0 ⟨0, 1, 0⟩ .modify w1.toP .fail ∧
    CRunsTo K0 [] w1bo w1b ∧ HandlePool.FreeSlotStep 0 ⟨0, 0, 0⟩ w1b.toP .reject ∧
    CRuns K0 [] (w1bo ++ [.unresolve 15, .freeSlot 0 ⟨0, 0, 0⟩]) :=
  ⟨crunsTo (by decide), by decide, crunsTo (by decide), by decide,
    crejects (k := K0) (C := w1l) (o := .freeSlot 0 ⟨0, 1, 0⟩) (by decide), by decide, by decide,
    cfails (k := K0) (C := w1) (o := .resolve 0 ⟨0, 1, 0⟩ .modify) (by decide),
    crunsTo (by decide), crejects (k := K0) (C := w1b) (o := .freeSlot 0 ⟨0, 0, 0⟩) (by decide),
    crunsTo (by decide)⟩

/-- Run of W2 (§72, §71, §61, §60, §66, §67, §62; HandlePool v0.5, D.2): frame 1 with the
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
/-- Kernel state after the first transfer of the move from `w2a`, the field 9 into 16 (§63 `ok`
effect). -/
def w2b : S3 := transferEff w2a.kern 9 16
/-- Kernel state after the move from `w2a`: the transfer 9 → 16, then 12 → 19 (§63 `ok`
effect). -/
def w2m : S3 := transferEff w2b 12 19

/-- **W2** (material §5b, ECS archetype and sparse set; class Lib, not given by the material).
Expected (material): disjoint reads and writes `ok`; `resolveMany` `ok`; the move of a row (the
transfers of its fields) while a column view is active `reject`; after its release `ok`.
Arbitration Q21 makes the variant the case: the column view is the column authority 11 with its
read view 12, and its release is the release of 12 and 11. Obtained: disjoint accesses and
`resolveMany` `ok`; the transfer of the field 12 into 19 while the view lives `reject` (the read
view 12, an active `Observe` derivative of 11, leaves no authority with effective `Modify` on the
field: §43 case 4, §63.1); after the release of 12 and 11, the move (transfers 9 → 16 and
12 → 19) is `ok`.

Re-evaluation under the exemption of v0.1 §63.4 (follow-up answer to Q3), on the state `w2a` after
the release of the read view 12 alone: the column authority 11 still covers the field from outside
the source (`ActiveDerivedOutside`), but it is the authority on which the `Modify` right over the
field rests (`Grounds`). In the case (the variant) the column view is then still active, so the
verdict of the move in `w2a` changes with v0.1. Historical expected verdict: `reject` (material:
the move of a row while a column view is active; spec v0 §63.4: 11, active, derived and held
outside the field, covers it; the v0 edition obtained `reject`). New expected verdict: `ok`,
decided by v0.1 §63.4 ("except the authorities through which the step exercises its `Modify` right
over `source`: the exercisable authority on which that right rests and its origin chain"): 11 and
its origins are exempt, the read view 12 is released and the authorities of `resolveMany` cover
the entity storage only. Obtained: `ok`. Limit of the case: in this run of one frame the move
exercises its right through the column authority 11 itself, so the variant no longer expresses a
move by another system while the view lives. On the literal reading (the view = the read view 12
alone, expected `ok` after its release), spec v0 rejected this move, the MISMATCH of the v0
edition; under v0.1 that reading obtains its expected verdicts as well.

Decision Q17, validated by the owner on 2026-11-06: the exemption of v0.1 §63.4 is accepted. The
expected property of the move in `w2a` is reformulated accordingly. For each transfer of the move,
with the authority grounding its `Modify` right over the source in the state before it (`Grounds`:
the root 7 for 9 → 16 from `w2a`, the column authority 10 being released; 11 for 12 → 19 from
`w2b`), in the state after the transfer: (a) no active authority outside the grounding chain
(`RightChain`: 7 for the field 9, 7 having no origin; 11 and its origin 7 for the field 12) covers
a source leaf; (b) every access of that chain to a source leaf is rejected. Obtained, by
`transfer_source_q17` on these reachable states (§57; §63.4, §43, §50): (a) holds; (b) holds for
reads, through every authority (the source leaves are `Moved`: §66.1, §41, §53), and for writes
and shared writes through a strict origin-chain ancestor of the grounding authority (7 on the
field 12, §67.1, §68.2, §43 case 3; the root 7 has none). A write through the grounding authority
itself is `ok` after the move, a re-initialization of the `Moved` leaf: 11 on the field 12, and 7
on the field 9 (§67 has no `Init` precondition and `Moved` forbids reads only, §41, §53; the
finding of `TransferSourceWitness.write_through_ground_accepted`). For these two writes the
obtained `ok` differs from (b) as worded (every access of the chain rejected): **MISMATCH**, cause:
Q17 (b) and §67, §68 disagree on writes through the grounding authority itself; the resolution
(restricting Q17 (b) to reads and to strict ancestors, or a spec rule) is left to the owner. The
case is not reclassified. -/
theorem W2 : CRunsTo K0 [] w2o w2 ∧ TransferStep K0 12 19 w2.kern .reject ∧
    CRuns K0 [] (w2o ++ [.release 12, .release 11, .transfer 9 16, .transfer 12 19]) ∧
    CRunsTo K0 [] (w2o ++ [.release 12]) w2a ∧ ActiveDerivedOutside w2a.kern 12 11 ∧
    Grounds w2a.kern .modify 12 11 ∧
    CRuns K0 [] (w2o ++ [.release 12, .transfer 9 16, .transfer 12 19]) ∧
    TransferStep K0 9 16 w2a.kern (.ok w2b) ∧ Grounds w2a.kern .modify 9 7 ∧ w2b.ancs 7 = [] ∧
    TransferStep K0 12 19 w2b (.ok w2m) ∧ Grounds w2b .modify 12 11 ∧ w2m.ancs 11 = [7] ∧
    Reachable K0 [] w2b ∧ Reachable K0 [] w2m ∧
    ((∀ (x : Nat) (y : Authority) (l : Nat), w2b.A[x]? = some y → y.active = true →
        l ∈ y.footprint → l ∈ footprint w2b.P 9 → RightChain w2b 7 x) ∧
      ∀ (ls : List Nat) (l : Nat), l ∈ ls → l ∈ footprint w2b.P 9 →
        (∀ (a : Nat) (o : Outcome3 S3), Read3Step a ls w2b o → o = .reject) ∧
        (∀ x ∈ w2b.ancs 7, ∀ o : Outcome3 S3, Write3Step x ls w2b o → o = .reject) ∧
        (∀ x ∈ w2b.ancs 7, ∀ o : Outcome3 S3, WriteSharedStep K0 x ls w2b o → o = .reject)) ∧
    ((∀ (x : Nat) (y : Authority) (l : Nat), w2m.A[x]? = some y → y.active = true →
        l ∈ y.footprint → l ∈ footprint w2m.P 12 → RightChain w2m 11 x) ∧
      ∀ (ls : List Nat) (l : Nat), l ∈ ls → l ∈ footprint w2m.P 12 →
        (∀ (a : Nat) (o : Outcome3 S3), Read3Step a ls w2m o → o = .reject) ∧
        (∀ x ∈ w2m.ancs 11, ∀ o : Outcome3 S3, Write3Step x ls w2m o → o = .reject) ∧
        (∀ x ∈ w2m.ancs 11, ∀ o : Outcome3 S3, WriteSharedStep K0 x ls w2m o → o = .reject)) ∧
    w2m.I 9 = .moved ∧ w2m.I 12 = .moved ∧ Write3Step 11 [12] w2m (.ok (write3Eff w2m [12])) ∧
    Write3Step 7 [9] w2m (.ok (write3Eff w2m [9])) := by
  have ha : CRunsTo K0 [] (w2o ++ [.release 12]) w2a := crunsTo (by decide)
  have hb : TransferStep K0 9 16 w2a.kern (.ok w2b) := .ok (by decide)
  have hm : TransferStep K0 12 19 w2b (.ok w2m) := .ok (by decide)
  have hrb : Reachable K0 [] w2b := .step ha.reach (.transfer hb)
  have hst : StaticsOK [] := by decide
  exact ⟨crunsTo (by decide), crejects (k := K0) (C := w2) (o := .transfer 12 19) (by decide),
    crunsTo (by decide), ha, by decide, by decide, crunsTo (by decide), hb, by decide, by decide,
    hm, by decide, by decide, hrb, .step hrb (.transfer hm),
    transfer_source_q17 (KD.ddSound {}) hst ha.reach hb (by decide),
    transfer_source_q17 (KD.ddSound {}) hst hrb hm (by decide),
    by decide, by decide, .ok (by decide), .ok (by decide)⟩

end Ern.Corpus.Lib
