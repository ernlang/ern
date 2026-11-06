import Ern.Corpus.Runner
import Ern.Lib.HandlePool
import Ern.Lib.DataStack

/-!
# Combined library runner (test module)

A computable executor for the library corpus cases of
`specs/ERN_Memory_Model_Specification_v0.1.md`, over one combined library state: the kernel state
`S₃` shared by the arena registry of `Ern.MemoryModel.Arena` (Part XIV, §46), the pool registry of
`Ern.Lib.HandlePool` (contract "HandlePool v0.5", non-normative) and the stack registry of
`Ern.Lib.DataStack` (contract "DS-v2", non-normative), with the fresh pool identity, the ghost
resolutions and the fresh mark identifier of those modules (§38: administrative states of library
abstractions are separate from `S₃`). This module is a test module: no model or library module
imports it.

* `COp`: the kernel operations O1–O16 (§60–§75), the arena operations O17–O19 (§76–§78), the pool
  operations and the stack operations, with their arguments; `unpin` takes the identity of a
  dynamic pinning obligation (§74, §75).
* `CRel k C o`: the relation of `o`, read on the projection of `C` it acts on (`toL`, `toP`, `toD`):
  the relation of `Ern.Corpus.OpRel` for O1–O16, `issue`, `reset`; `NewArenaStep`, `NewPoolStep`,
  `NewStackStep` with the internals of all other live registries as their guard parameter (§56,
  §76.4); the pool and stack relations of the library modules.
* `cstep k C o`: the computed outcome (§58); `cstep_sound`: it is an outcome of `CRel`, `ok`,
  `reject` and `fail` alike.
* `crun`, `cfinal`, `CRunsTo`: a run from `CState.init statics` (§47) whose steps are all `ok`
  reaches a library-reachable state (`CReach`) whose kernel state is reachable by O1–O16 (§57):
  the kernel part of every library step is a finite sequence of kernel steps (HandlePool v0.5,
  HP5-7): `allocSlot` is a kernel `write` (§67) when some authority can write its destination, and
  `freeSlot` a kernel `write` of its metadata leaves, the leaves of the pool value (HP5-1, Q3
  decision of 2026-11-06), when some authority can write them, which `crun` checks.
-/

namespace Ern.Corpus.LibRunner

open Ern.MemoryModel Ern.MemoryModel.Access Ern.MemoryModel.Arena Ern.Corpus Ern.Lib

/-! ## Combined library state (§38, §46, §47, §56) -/

/-- The combined library state (§38, §46): the kernel state `S₃`, the arena registry (§46), the
pool registry, the next fresh pool identity and the ghost resolutions (HandlePool v0.5, D.1,
D.2), the stack registry and the next fresh mark identifier (DS-v2). -/
structure CState where
  kern : S3
  arenas : List ArenaEntry
  pools : List HandlePool.Pool
  nId : Nat
  res : List HandlePool.Res
  stacks : List DataStack.Stack
  fresh : Nat

/-- Initial combined state (§47): the initial kernel state and empty registries. -/
def CState.init (statics : Statics) : CState := ⟨S3.init statics, [], [], 0, [], [], 0⟩

/-- The arena library state of `C` (§46). -/
def CState.toL (C : CState) : LState := ⟨C.kern, C.arenas⟩

/-- The pool library state of `C` (§38; HandlePool v0.5, D.1). -/
def CState.toP (C : CState) : HandlePool.PState := ⟨C.kern, C.pools, C.nId, C.res⟩

/-- The stack library state of `C` (§38; DS-v2). -/
def CState.toD (C : CState) : DataStack.DState := ⟨C.kern, C.stacks, C.fresh⟩

/-- `C` with its kernel state and arena registry replaced (§46). -/
def CState.setL (C : CState) (L : LState) : CState := { C with kern := L.kern, arenas := L.arenas }

/-- `C` with its kernel state and pool library state replaced (§38; HandlePool v0.5). -/
def CState.setP (C : CState) (P : HandlePool.PState) : CState :=
  { C with kern := P.kern, pools := P.pools, nId := P.nId, res := P.res }

/-- `C` with its kernel state and stack library state replaced (§38; DS-v2). -/
def CState.setD (C : CState) (D : DataStack.DState) : CState :=
  { C with kern := D.kern, stacks := D.stacks, fresh := D.fresh }

/-- The registries of live administrations other than the arena registry (§56, §76.4): the live
pools (HandlePool v0.5, D.1) and the live stacks (DS-v2). -/
def CState.othersA (C : CState) : List (List Nat) :=
  [HandlePool.liveInternals C.kern C.pools, DataStack.stackInternals C.kern C.stacks]

/-- The registries of live administrations other than the pool registry (§56; HandlePool v0.5,
D.1): the live arenas (§46) and the live stacks (DS-v2). -/
def CState.othersP (C : CState) : List (List Nat) :=
  [Arena.liveInternals C.kern C.arenas, DataStack.stackInternals C.kern C.stacks]

/-- The registries of live administrations other than the stack registry (§56; DS-v2): the live
arenas (§46) and the live pools (HandlePool v0.5, D.1). -/
def CState.othersD (C : CState) : List (List Nat) :=
  [Arena.liveInternals C.kern C.arenas, HandlePool.liveInternals C.kern C.pools]

/-! ## Operations and their relations (§58, §60–§78; HandlePool v0.5; DS-v2) -/

/-- An operation of a library run: the kernel operations O1–O16 (§60–§75), the arena operations
O17–O19 (§76–§78), the pool operations (HandlePool v0.5, D.1–D.3; pools and slots named by
their registry index) and the stack operations (DS-v2; stacks named by their registry index);
`unpin` takes the identity of a dynamic pinning obligation, its index in `S3.pins` (§74, §75). -/
inductive COp where
  | derive (src : Nat) (region : List Nat) (m : Mode)
  | split (src : Nat) (rs : List (List Nat))
  | release (a : Nat)
  | transfer (src dst : Nat)
  | depend (q x : Nat)
  | enter (ps : List Nat) (ls : LocalShape)
  | exit
  | read (a : Nat) (ls : List Nat)
  | write (a : Nat) (ls : List Nat)
  | writeShared (a : Nat) (ls : List Nat)
  | pin (p : Nat)
  | unpin (o : Nat)
  | endUse (p : Nat)
  | free (p auth : Nat)
  | alloc (provider owner : Nat) (ls : LocalShape)
  | store (a p : Nat)
  | newArena (storage internal : Nat)
  | issue (i : Nat) (region : List Nat) (dst : Nat)
  | reset (i : Nat)
  | newPool (storage internal : Nat)
  | allocSlot (j dst : Nat)
  | resolve (j : Nat) (h : HandlePool.Handle) (m : Mode)
  | resolveMany (j : Nat) (hs : List HandlePool.Handle) (m : Mode)
  | unresolve (c : Nat)
  | freeSlot (j : Nat) (h : HandlePool.Handle)
  | newStack (storage internal : Nat)
  | push (j size dst : Nat)
  | mark (j : Nat)
  | rewind (j : Nat) (m : DataStack.Mark)
  | grow (j b extra : Nat)

/-- An outcome of a projected library state read on the combined state (§58): `ok` through the
embedding `emb`, `reject` and `fail` unchanged. -/
def liftO {σ : Type} (emb : σ → CState) : Outcome3 σ → Outcome3 CState
  | .ok x => .ok (emb x)
  | .reject => .reject
  | .fail => .fail

/-- A relation on a projected library state read on combined outcomes (§58): `ok C'` when `C'` is
the embedding of an `ok` state of the relation; `reject`, `fail` as the relation. -/
def LiftR {σ : Type} (R : Outcome3 σ → Prop) (emb : σ → CState) : Outcome3 CState → Prop
  | .ok C' => ∃ x, R (.ok x) ∧ C' = emb x
  | .reject => R .reject
  | .fail => R .fail

/-- The relation of `o` from `C` (§58, §60–§78; HandlePool v0.5; DS-v2), on the projection
it acts on: `OpRel` of `Ern.Corpus` for O1–O16, `issue` and `reset`; `newArena`, `newPool`,
`newStack` with the internals of every other live registry as their guard parameter (§56,
§76.4); the relations of the pool and stack modules. -/
def CRel (k : K) (C : CState) : COp → Outcome3 CState → Prop
  | .derive a r m => LiftR (OpRel k C.toL (.derive a r m)) C.setL
  | .split a rs => LiftR (OpRel k C.toL (.split a rs)) C.setL
  | .release a => LiftR (OpRel k C.toL (.release a)) C.setL
  | .transfer a b => LiftR (OpRel k C.toL (.transfer a b)) C.setL
  | .depend q x => LiftR (OpRel k C.toL (.depend q x)) C.setL
  | .enter ps ls => LiftR (OpRel k C.toL (.enter ps ls)) C.setL
  | .exit => LiftR (OpRel k C.toL .exit) C.setL
  | .read a ls => LiftR (OpRel k C.toL (.read a ls)) C.setL
  | .write a ls => LiftR (OpRel k C.toL (.write a ls)) C.setL
  | .writeShared a ls => LiftR (OpRel k C.toL (.writeShared a ls)) C.setL
  | .pin p => LiftR (OpRel k C.toL (.pin p)) C.setL
  | .unpin o => LiftR (OpRel k C.toL (.unpin o)) C.setL
  | .endUse p => LiftR (OpRel k C.toL (.endUse p)) C.setL
  | .free p a => LiftR (OpRel k C.toL (.free p a)) C.setL
  | .alloc pr ow ls => LiftR (OpRel k C.toL (.alloc pr ow ls)) C.setL
  | .store a p => LiftR (OpRel k C.toL (.store a p)) C.setL
  | .newArena st i => LiftR (NewArenaStep C.othersA st i C.toL) C.setL
  | .issue i r d => LiftR (OpRel k C.toL (.issue i r d)) C.setL
  | .reset i => LiftR (OpRel k C.toL (.reset i)) C.setL
  | .newPool st i => LiftR (HandlePool.NewPoolStep C.othersP st i C.toP) C.setP
  | .allocSlot j d => LiftR (HandlePool.AllocSlotStep j d C.toP) C.setP
  | .resolve j h m => LiftR (HandlePool.ResolveStep j h m C.toP) C.setP
  | .resolveMany j hs m => LiftR (HandlePool.ResolveManyStep k j hs m C.toP) C.setP
  | .unresolve c => LiftR (HandlePool.UnresolveStep c C.toP) C.setP
  | .freeSlot j h => LiftR (HandlePool.FreeSlotStep j h C.toP) C.setP
  | .newStack st i => LiftR (DataStack.NewStackStep C.othersD st i C.toD) C.setD
  | .push j n d => LiftR (DataStack.PushStep k j n d C.toD) C.setD
  | .mark j => LiftR (DataStack.MarkStep j C.toD) C.setD
  | .rewind j m => LiftR (DataStack.RewindStep k j m C.toD) C.setD
  | .grow j b e => LiftR (DataStack.GrowStep k j b e C.toD) C.setD

/-! ## Executor -/

/-- The first free slot of a slot list and its index (HandlePool v0.5, D.3: "`ok` choisit un
slot libre"; the lowest index is chosen, one of the outcomes the relation allows). -/
def firstFree : List HandlePool.Slot → Option (Nat × HandlePool.Slot)
  | [] => none
  | sl :: l => if sl.live then (firstFree l).map fun p => (p.1 + 1, p.2) else some (0, sl)

/-- An authority that can write the leaf `dst` (§67), searched among the authorities of `s`. -/
def writer (s : S3) (dst : Nat) : Option Nat :=
  (List.range s.A.length).find? fun a => decide (Write3Pre s a [dst])

/-- The kernel-side check of a step of `crun` (§67; HandlePool v0.5, D.3, HP5-1 with the Q3
decision of 2026-11-06): the handle write of `allocSlot` and the metadata write of `freeSlot` are
kernel `write`s by some authority. -/
def COp.kok (C : CState) : COp → Bool
  | .allocSlot _ dst => (writer C.kern dst).isSome
  | .freeSlot j _ => match C.pools[j]? with
    | some pl => decide (∃ a ∈ List.range C.kern.A.length,
        Write3Pre C.kern a (HandlePool.metaLeaves C.kern pl))
    | none => true
  | _ => true

section Exec
variable (k : K) [∀ r r', Decidable (k.DeclaredDisjoint r r')] [DecidablePred k.SharedMutable]
  [DecidablePred k.Pinned] [DecidablePred k.ExternalDone] [DecidablePred k.Deallocable]
  [∀ p a, Decidable (k.FreeCompat p a)] [∀ p ls s, Decidable (k.Satisfiable p ls s)]

/-- Computed outcome of `allocSlot(pool j, dst)` (HandlePool v0.5, D.3; §58). -/
def allocSlotOut (P : HandlePool.PState) (j dst : Nat) : Outcome3 HandlePool.PState :=
  match P.pools[j]? with
  | none => .reject
  | some pl =>
    if HandlePool.AllocSlotStatic P.kern pl dst then
      match firstFree pl.slots with
      | some (i, sl) => .ok (HandlePool.allocSlotEff P j pl i sl dst)
      | none => .fail
    else .reject

/-- Computed outcome of `resolve(h, m)` on pool `j` (HandlePool v0.5, D.2, HP5-5: the handle is
checked before the right; §58). -/
def resolveOut (P : HandlePool.PState) (j : Nat) (h : HandlePool.Handle) (m : Mode) :
    Outcome3 HandlePool.PState :=
  match P.pools[j]? with
  | none => .reject
  | some pl =>
    if HandlePool.HandleOK P.kern pl h then
      if HandlePool.ResolveRight P.kern pl m then
        match pl.slots[h.slot]? with
        | some sl =>
          if DerivePre (HandlePool.compS P.kern pl m) P.kern.A.length
              (footprint P.kern.P sl.place) m then
            .ok { P with
              kern := deriveEff (HandlePool.compS P.kern pl m) P.kern.A.length
                (footprint P.kern.P sl.place) m
              res := P.res ++ [⟨pl.id, pl.internal, P.kern.A.length, m,
                [(P.kern.A.length + 1, h.slot, h.gen)]⟩] }
          else .reject
        | none => .reject
      else .reject
    else .fail

/-- Computed outcome of `resolveMany(hs, m)` on pool `j` (HandlePool v0.5, D.2, HP5-5: the batch
is checked before the right; §58). -/
def resolveManyOut (P : HandlePool.PState) (j : Nat) (hs : List HandlePool.Handle) (m : Mode) :
    Outcome3 HandlePool.PState :=
  match P.pools[j]? with
  | none => .reject
  | some pl =>
    if HandlePool.BatchOK P.kern pl hs m then
      if HandlePool.ResolveRight P.kern pl m then
        if HandlePool.EntriesPre k m (HandlePool.compS P.kern pl m) P.kern.A.length
            (HandlePool.entryRegions P.kern pl hs) then
          .ok { P with
            kern := HandlePool.entriesEff m (HandlePool.compS P.kern pl m) P.kern.A.length
              (HandlePool.entryRegions P.kern pl hs)
            res := P.res ++ [⟨pl.id, pl.internal, P.kern.A.length, m,
              HandlePool.batchEntries P.kern.A.length hs⟩] }
        else .reject
      else .reject
    else .fail

/-- Computed outcome of `unresolve(c)` (HandlePool v0.5, D.2; §58). -/
def unresolveOut (P : HandlePool.PState) (c : Nat) : Outcome3 HandlePool.PState :=
  match HandlePool.findRes P c with
  | none => .reject
  | some r =>
    match HandlePool.releaseAll P.kern (HandlePool.unresolveList P.kern r) with
    | none => .reject
    | some s' => .ok { P with kern := s' }

/-- Computed outcome of `freeSlot(h)` on pool `j` (HandlePool v0.5, D.3, HP5-1, HP5-1': the
content conditions; outcome order of HP5-1'': the handle, pool liveness included, before the
administration right; §58). -/
def freeSlotOut (P : HandlePool.PState) (j : Nat) (h : HandlePool.Handle) :
    Outcome3 HandlePool.PState :=
  match P.pools[j]? with
  | none => .reject
  | some pl =>
    if HandlePool.HandleOK P.kern pl h then
      if HandlePool.AdminRight P.kern pl then
        match pl.slots[h.slot]? with
        | some sl =>
          if HandlePool.FreeContentOK P pl sl.place then
            .ok (HandlePool.freeSlotEff P j pl h.slot sl)
          else .reject
        | none => .reject
      else .reject
    else .fail

/-- Computed outcome of `push(j, size, dst)` (DS-v2; Part XIV, §77; §58). -/
def pushOut (D : DataStack.DState) (j size dst : Nat) : Outcome3 DataStack.DState :=
  match D.stacks[j]? with
  | none => .reject
  | some st =>
    if IssueStatic D.kern st.entry (DataStack.cellsOf st st.top size) dst then
      if st.top + size ≤ st.cells.length then
        if SplitPre k D.kern st.internal [DataStack.cellsOf st st.top size] then
          if StorePre (splitEff D.kern st.internal [DataStack.cellsOf st st.top size])
              D.kern.A.length dst then
            .ok ⟨storeEff (splitEff D.kern st.internal [DataStack.cellsOf st st.top size])
              D.kern.A.length dst,
              D.stacks.set j (DataStack.pushMeta st size D.kern.A.length dst), D.fresh⟩
          else .reject
        else .reject
      else .fail
    else .reject

/-- Computed outcome of `mark(j)` (DS-v2, DS2-1: `AdminRight` required, §36; §58). -/
def markOut (D : DataStack.DState) (j : Nat) : Outcome3 DataStack.DState :=
  match D.stacks[j]? with
  | none => .reject
  | some st =>
    if DataStack.AdminRight D.kern st then
      .ok ⟨D.kern, D.stacks.set j (DataStack.markMeta j st D.fresh), D.fresh + 1⟩
    else .reject

/-- Computed outcome of `rewind(j, m)` (DS-v2, DS2-3, DS2-4, DS2-6: a missing stack and a dead or
foreign mark `fail` before the right; Part XIV, §78; §58). -/
def rewindOut (D : DataStack.DState) (j : Nat) (m : DataStack.Mark) :
    Outcome3 DataStack.DState :=
  match D.stacks[j]? with
  | none => .fail
  | some st =>
    if DataStack.LiveMark D.kern j st m then
      if DataStack.AdminRight D.kern st then
        if SplitPre k D.kern st.internal [DataStack.above st m] then
          if ReleasePre (splitEff D.kern st.internal [DataStack.above st m])
              D.kern.A.length then
            .ok ⟨releaseEff (splitEff D.kern st.internal [DataStack.above st m])
              D.kern.A.length, D.stacks.set j (DataStack.rewindMeta st m), D.fresh⟩
          else .reject
        else .reject
      else .reject
    else .fail

/-- Computed outcome of `grow(j, b, extra)` (DS-v2, DS2-2: into the place that holds `b`; DS2-5:
`extra` may be zero; Part XIV, §77; §58). -/
def growOut (D : DataStack.DState) (j b extra : Nat) : Outcome3 DataStack.DState :=
  match D.stacks[j]? with
  | none => .reject
  | some st =>
    match st.block b with
    | none => .reject
    | some x =>
      if ReleasePre D.kern b then
        match DataStack.holderPlace D.kern b with
        | none => .reject
        | some d =>
          if IssueStatic (releaseEff D.kern b) st.entry
              (DataStack.cellsOf st x.base (x.size + extra)) d then
            if DataStack.InPlace st x extra then
              if SplitPre k (releaseEff D.kern b) st.internal
                  [DataStack.cellsOf st x.base (x.size + extra)] then
                if StorePre (splitEff (releaseEff D.kern b) st.internal
                    [DataStack.cellsOf st x.base (x.size + extra)])
                    (releaseEff D.kern b).A.length d then
                  .ok ⟨storeEff (splitEff (releaseEff D.kern b) st.internal
                      [DataStack.cellsOf st x.base (x.size + extra)])
                      (releaseEff D.kern b).A.length d,
                    D.stacks.set j (DataStack.growMeta st x extra (releaseEff D.kern b).A.length d),
                    D.fresh⟩
                else .reject
              else .reject
            else .fail
          else .reject
      else .reject

/-- The computed outcome of `o` from `C` (§58, §60–§78; HandlePool v0.5; DS-v2): the
executor of `Ern.Corpus` on the arena projection for O1–O16, `issue` and `reset`; the guard of §56
over all registries for the creation operations; the pool and stack executors above. -/
def cstep (C : CState) : COp → Outcome3 CState
  | .derive a r m => liftO C.setL (lstep k C.toL (.derive a r m))
  | .split a rs => liftO C.setL (lstep k C.toL (.split a rs))
  | .release a => liftO C.setL (lstep k C.toL (.release a))
  | .transfer a b => liftO C.setL (lstep k C.toL (.transfer a b))
  | .depend q x => liftO C.setL (lstep k C.toL (.depend q x))
  | .enter ps ls => liftO C.setL (lstep k C.toL (.enter ps ls))
  | .exit => liftO C.setL (lstep k C.toL .exit)
  | .read a ls => liftO C.setL (lstep k C.toL (.read a ls))
  | .write a ls => liftO C.setL (lstep k C.toL (.write a ls))
  | .writeShared a ls => liftO C.setL (lstep k C.toL (.writeShared a ls))
  | .pin p => liftO C.setL (lstep k C.toL (.pin p))
  | .unpin o => liftO C.setL (lstep k C.toL (.unpin o))
  | .endUse p => liftO C.setL (lstep k C.toL (.endUse p))
  | .free p a => liftO C.setL (lstep k C.toL (.free p a))
  | .alloc pr ow ls => liftO C.setL (lstep k C.toL (.alloc pr ow ls))
  | .store a p => liftO C.setL (lstep k C.toL (.store a p))
  | .newArena st i =>
    if NewArenaPre C.kern C.arenas C.othersA st i then .ok (C.setL (newArenaEff C.toL st i))
    else .reject
  | .issue i r d => liftO C.setL (lstep k C.toL (.issue i r d))
  | .reset i => liftO C.setL (lstep k C.toL (.reset i))
  | .newPool st i =>
    if HandlePool.NewPoolPre C.kern C.pools C.othersP st i then
      .ok (C.setP (HandlePool.newPoolEff C.toP st i))
    else .reject
  | .allocSlot j d => liftO C.setP (allocSlotOut C.toP j d)
  | .resolve j h m => liftO C.setP (resolveOut C.toP j h m)
  | .resolveMany j hs m => liftO C.setP (resolveManyOut k C.toP j hs m)
  | .unresolve c => liftO C.setP (unresolveOut C.toP c)
  | .freeSlot j h => liftO C.setP (freeSlotOut C.toP j h)
  | .newStack st i =>
    if DataStack.NewStackPre C.kern C.stacks C.othersD st i then
      .ok (C.setD (DataStack.newStackEff C.toD st i))
    else .reject
  | .push j n d => liftO C.setD (pushOut k C.toD j n d)
  | .mark j => liftO C.setD (markOut C.toD j)
  | .rewind j m => liftO C.setD (rewindOut k C.toD j m)
  | .grow j b e => liftO C.setD (growOut k C.toD j b e)

/-- The state after `o` from `C` when it is `ok`; `C` otherwise (§58). -/
def cnext (C : CState) (o : COp) : CState :=
  match cstep k C o with
  | .ok C' => C'
  | _ => C

/-- The state reached by `os` from `C` when every step is `ok` and every `allocSlot` handle write
and every `freeSlot` metadata write is a kernel write (§58, §67); `none` otherwise. -/
def crun (C : CState) : List COp → Option CState
  | [] => some C
  | o :: os =>
    match cstep k C o with
    | .ok C' => if o.kok C then crun C' os else none
    | _ => none

/-- The state reached by `os` from `CState.init statics` (§47); `CState.init statics` when the run
does not complete (used only under `(crun …).isSome = true`, see `crunsTo`). -/
def cfinal (statics : Statics) (os : List COp) : CState :=
  (crun k (CState.init statics) os).getD (CState.init statics)

end Exec

/-- Combined library states reachable from `CState.init statics` (§47) by `ok` steps of the kernel
and of the three libraries (Part XIV; HandlePool v0.5; DS-v2). -/
inductive CReach (k : K) (statics : Statics) : CState → Prop where
  | init : CReach k statics (CState.init statics)
  | step {C C' : CState} {o : COp} : CReach k statics C → CRel k C o (.ok C') →
      CReach k statics C'

section Runs
variable (k : K) [∀ r r', Decidable (k.DeclaredDisjoint r r')] [DecidablePred k.SharedMutable]
  [DecidablePred k.Pinned] [DecidablePred k.ExternalDone] [DecidablePred k.Deallocable]
  [∀ p a, Decidable (k.FreeCompat p a)] [∀ p ls s, Decidable (k.Satisfiable p ls s)]

/-- A run of `os` from `CState.init statics` (§47) has only `ok` steps and reaches `C`; `C` is
library-reachable, and its kernel state is reachable by O1–O16 (§57; HandlePool v0.5, HP5-7). -/
structure CRunsTo (statics : Statics) (os : List COp) (C : CState) : Prop where
  /-- Every step is `ok` and the run ends in `C`. -/
  run : crun k (CState.init statics) os = some C
  /-- `C` is library-reachable. -/
  creach : CReach k statics C
  /-- The kernel state of `C` is reachable from `S3.init statics` by O1–O16 (§57). -/
  reach : Reachable k statics C.kern

/-- The run of `os` from `CState.init statics` has only `ok` steps (§47, §57). -/
abbrev CRuns (statics : Statics) (os : List COp) : Prop :=
  CRunsTo k statics os (cfinal k statics os)

end Runs

/-! ## Step soundness (§58) -/

/-- A computed outcome of a projected relation is an outcome of its lift (§58). -/
theorem liftR_liftO {σ : Type} {R : Outcome3 σ → Prop} {emb : σ → CState} {o : Outcome3 σ}
    (h : R o) : LiftR R emb (liftO emb o) := by
  cases o with
  | ok x => exact ⟨x, h, rfl⟩
  | reject => exact h
  | fail => exact h

/-- An outcome of a guarded projected step read on combined outcomes (§58). -/
theorem liftR_guarded {σ : Type} {p : Prop} [Decidable p] {x : σ} {emb : σ → CState} :
    LiftR (Guarded p x) emb (if p then .ok (emb x) else .reject) := by
  split
  · next h => exact ⟨x, .ok h, rfl⟩
  · next h => exact .reject h

/-- `firstFree` finds a free slot at its index (HandlePool v0.5, D.3). -/
theorem firstFree_some : ∀ {l : List HandlePool.Slot} {i : Nat} {sl : HandlePool.Slot},
    firstFree l = some (i, sl) → l[i]? = some sl ∧ sl.live = false
  | [], _, _, h => by simp [firstFree] at h
  | x :: l, i, sl, h => by
    unfold firstFree at h
    split at h
    · cases e : firstFree l with
      | none => rw [e] at h; cases h
      | some p =>
        rw [e] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simpa using firstFree_some e
    · next hx =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, by simpa using hx⟩

/-- When `firstFree` finds nothing, every slot is live (HandlePool v0.5, D.3). -/
theorem firstFree_none : ∀ {l : List HandlePool.Slot}, firstFree l = none →
    ∀ sl ∈ l, sl.live = true
  | [], _, _, h => by cases h
  | x :: l, h, sl, hm => by
    unfold firstFree at h
    split at h
    · next hx =>
      cases e : firstFree l with
      | none =>
        rcases List.mem_cons.1 hm with rfl | hm
        · exact hx
        · exact firstFree_none e sl hm
      | some p => rw [e] at h; cases h
    · cases h

/-- A computed `writer` writes its destination (§67). -/
theorem writer_sound {s : S3} {dst a : Nat} (h : writer s dst = some a) :
    Write3Pre s a [dst] := by
  have := List.find?_some h
  simpa using this

section Sound
variable {k : K} [∀ r r', Decidable (k.DeclaredDisjoint r r')] [DecidablePred k.SharedMutable]
  [DecidablePred k.Pinned] [DecidablePred k.ExternalDone] [DecidablePred k.Deallocable]
  [∀ p a, Decidable (k.FreeCompat p a)] [∀ p ls s, Decidable (k.Satisfiable p ls s)]

/-- `allocSlotOut` is an outcome of `AllocSlotStep` (HandlePool v0.5, D.3; §58). -/
theorem allocSlotOut_sound (P : HandlePool.PState) (j dst : Nat) :
    HandlePool.AllocSlotStep j dst P (allocSlotOut P j dst) := by
  unfold allocSlotOut
  split
  · next hj => exact .noPool hj
  · next pl hj =>
    split
    · next hs =>
      split
      · next i sl he => obtain ⟨h1, h2⟩ := firstFree_some he; exact .ok hj hs h1 h2
      · next he => exact .fail hj hs (firstFree_none he)
    · next hs => exact .static hj hs

/-- `resolveOut` is an outcome of `ResolveStep` (HandlePool v0.5, D.2; §58). -/
theorem resolveOut_sound (P : HandlePool.PState) (j : Nat) (h : HandlePool.Handle) (m : Mode) :
    HandlePool.ResolveStep j h m P (resolveOut P j h m) := by
  unfold resolveOut
  split
  · next hj => exact .noPool hj
  · next pl hj =>
    split
    · next hok =>
      split
      · next hr =>
        split
        · next sl hsl =>
          split
          · next hd => exact .ok hj hok hr hsl hd
          · next hd => exact .noEntry hj hok hr hsl hd
        · next hsl =>
          exfalso
          have := hok.2.2
          rw [hsl] at this
          exact this
      · next hr => exact .noRight hj hok hr
    · next hok => exact .fail hj hok

omit [DecidablePred k.SharedMutable] [DecidablePred k.Pinned] [DecidablePred k.ExternalDone]
  [DecidablePred k.Deallocable] [∀ p a, Decidable (k.FreeCompat p a)]
  [∀ p ls s, Decidable (k.Satisfiable p ls s)] in
/-- `resolveManyOut` is an outcome of `ResolveManyStep` (HandlePool v0.5, D.2; §58). -/
theorem resolveManyOut_sound (P : HandlePool.PState) (j : Nat) (hs : List HandlePool.Handle)
    (m : Mode) : HandlePool.ResolveManyStep k j hs m P (resolveManyOut k P j hs m) := by
  unfold resolveManyOut
  split
  · next hj => exact .noPool hj
  · next pl hj =>
    split
    · next hb =>
      split
      · next hr =>
        split
        · next he => exact .ok hj hb hr he
        · next he => exact .noEntries hj hb hr he
      · next hr => exact .noRight hj hb hr
    · next hb => exact .fail hj hb

/-- `unresolveOut` is an outcome of `UnresolveStep` (HandlePool v0.5, D.2; §58). -/
theorem unresolveOut_sound (P : HandlePool.PState) (c : Nat) :
    HandlePool.UnresolveStep c P (unresolveOut P c) := by
  unfold unresolveOut
  split
  · next hf => exact .none hf
  · next r hf =>
    split
    · next hr => exact .reject hf hr
    · next s' hr => exact .ok hf hr

/-- `freeSlotOut` is an outcome of `FreeSlotStep` (HandlePool v0.5, D.3, HP5-1''; §58). -/
theorem freeSlotOut_sound (P : HandlePool.PState) (j : Nat) (h : HandlePool.Handle) :
    HandlePool.FreeSlotStep j h P (freeSlotOut P j h) := by
  unfold freeSlotOut
  split
  · next hj => exact .noPool hj
  · next pl hj =>
    split
    · next hok =>
      split
      · next hr =>
        split
        · next sl hsl =>
          split
          · next hc => exact .ok hj hok hr hsl hc
          · next hc => exact .noContent hj hok hr hsl hc
        · next hsl =>
          exfalso
          have := hok.2.2
          rw [hsl] at this
          exact this
      · next hr => exact .noRight hj hok hr
    · next hok => exact .fail hj hok

omit [DecidablePred k.SharedMutable] [DecidablePred k.Pinned] [DecidablePred k.ExternalDone]
  [DecidablePred k.Deallocable] [∀ p a, Decidable (k.FreeCompat p a)]
  [∀ p ls s, Decidable (k.Satisfiable p ls s)] in
/-- `pushOut` is an outcome of `PushStep` (DS-v2; §58). -/
theorem pushOut_sound (D : DataStack.DState) (j size dst : Nat) :
    DataStack.PushStep k j size dst D (pushOut k D j size dst) := by
  unfold pushOut
  split
  · next hj => exact .noStack hj
  · next st hj =>
    split
    · next hs =>
      split
      · next hn =>
        split
        · next h1 =>
          split
          · next h2 => exact .ok hj hs hn (.ok h1) (.ok h2)
          · next h2 => exact .store hj hs hn (.ok h1) (.reject h2)
        · next h1 => exact .split hj hs hn (.reject h1)
      · next hn => exact .fail hj hs hn
    · next hs => exact .static hj hs

/-- `markOut` is an outcome of `MarkStep` (DS-v2; §58). -/
theorem markOut_sound (D : DataStack.DState) (j : Nat) :
    DataStack.MarkStep j D (markOut D j) := by
  unfold markOut
  split
  · next hj => exact .noStack hj
  · next st hj =>
    split
    · next ha => exact .ok hj ha
    · next ha => exact .static hj ha

omit [DecidablePred k.SharedMutable] [DecidablePred k.Pinned] [DecidablePred k.ExternalDone]
  [DecidablePred k.Deallocable] [∀ p a, Decidable (k.FreeCompat p a)]
  [∀ p ls s, Decidable (k.Satisfiable p ls s)] in
/-- `rewindOut` is an outcome of `RewindStep` (DS-v2; §58). -/
theorem rewindOut_sound (D : DataStack.DState) (j : Nat) (m : DataStack.Mark) :
    DataStack.RewindStep k j m D (rewindOut k D j m) := by
  unfold rewindOut
  split
  · next hj => exact .noStack hj
  · next st hj =>
    split
    · next hl =>
      split
      · next ha =>
        split
        · next h1 =>
          split
          · next h2 => exact .ok hj hl ha (.ok h1) (.ok h2)
          · next h2 => exact .release hj hl ha (.ok h1) (.reject h2)
        · next h1 => exact .split hj hl ha (.reject h1)
      · next ha => exact .static hj hl ha
    · next hl => exact .dead hj hl

omit [DecidablePred k.SharedMutable] [DecidablePred k.Pinned] [DecidablePred k.ExternalDone]
  [DecidablePred k.Deallocable] [∀ p a, Decidable (k.FreeCompat p a)]
  [∀ p ls s, Decidable (k.Satisfiable p ls s)] in
/-- `growOut` is an outcome of `GrowStep` (DS-v2; §58). -/
theorem growOut_sound (D : DataStack.DState) (j b extra : Nat) :
    DataStack.GrowStep k j b extra D (growOut k D j b extra) := by
  unfold growOut
  split
  · next hj => exact .noStack hj
  · next st hj =>
    split
    · next hb => exact .noBlock hj hb
    · next x hb =>
      split
      · next h0 =>
        split
        · next hh => exact .noHolder hj hb (.ok h0) hh
        · next d hh =>
          split
          · next hs =>
            split
            · next hi =>
              split
              · next h1 =>
                split
                · next h2 => exact .ok hj hb (.ok h0) hh hs hi (.ok h1) (.ok h2)
                · next h2 => exact .store hj hb (.ok h0) hh hs hi (.ok h1) (.reject h2)
              · next h1 => exact .split hj hb (.ok h0) hh hs hi (.reject h1)
            · next hi => exact .fail hj hb (.ok h0) hh hs hi
          · next hs => exact .static hj hb (.ok h0) hh hs
      · next h0 => exact .release hj hb (.reject h0)

/-- **Step soundness** (§58, §60–§78; HandlePool v0.5; DS-v2): the computed outcome of `o`
from `C` is an outcome of the relation of `o` on the projected state, `ok`, `reject` and `fail`
alike. -/
theorem cstep_sound (C : CState) (o : COp) : CRel k C o (cstep k C o) := by
  cases o with
  | newArena st i => exact liftR_guarded
  | newPool st i => exact liftR_guarded
  | newStack st i => exact liftR_guarded
  | allocSlot j d => exact liftR_liftO (allocSlotOut_sound _ _ _)
  | resolve j h m => exact liftR_liftO (resolveOut_sound _ _ _ _)
  | resolveMany j hs m => exact liftR_liftO (resolveManyOut_sound _ _ _ _)
  | unresolve c => exact liftR_liftO (unresolveOut_sound _ _)
  | freeSlot j h => exact liftR_liftO (freeSlotOut_sound _ _ _)
  | push j n d => exact liftR_liftO (pushOut_sound _ _ _ _)
  | mark j => exact liftR_liftO (markOut_sound _ _)
  | rewind j m => exact liftR_liftO (rewindOut_sound _ _ _)
  | grow j b e => exact liftR_liftO (growOut_sound _ _ _ _)
  | _ => exact liftR_liftO (lstep_sound _ _)

/-- A computed `reject` is a `reject` outcome of the relation (§58). -/
theorem crejects {C : CState} {o : COp} (h : verdictOf (cstep k C o) = .reject) :
    CRel k C o .reject := by
  have hs := cstep_sound (k := k) C o
  revert hs h
  cases cstep k C o with
  | ok => intro h; cases h
  | reject => intro _ hs; exact hs
  | fail => intro h; cases h

/-- A computed `fail` is a `fail` outcome of the relation (§58). -/
theorem cfails {C : CState} {o : COp} (h : verdictOf (cstep k C o) = .fail) :
    CRel k C o .fail := by
  have hs := cstep_sound (k := k) C o
  revert hs h
  cases cstep k C o with
  | ok => intro h; cases h
  | reject => intro h; cases h
  | fail => intro _ hs; exact hs

/-- A computed `ok` is the `ok` outcome of the relation to `cnext k C o` (§58). -/
theorem coks {C : CState} {o : COp} (h : verdictOf (cstep k C o) = .ok) :
    CRel k C o (.ok (cnext k C o)) := by
  have hs := cstep_sound (k := k) C o
  unfold cnext
  revert hs h
  cases cstep k C o with
  | ok => intro _ hs; exact hs
  | reject => intro h; cases h
  | fail => intro h; cases h

end Sound

/-! ## Kernel side of library steps (§57; Part XIV; HandlePool v0.5, HP5-7; DS-v2) -/

/-- The kernel part of an arena library step is a sequence of kernel steps (Part XIV, §57:
`newArena` changes no kernel component, `issue` is `split` then `store`, `reset` is `derive` then
`release`). -/
theorem LStep.kseq {k : K} {L L' : LState} (h : LStep k L L') :
    HandlePool.KSeq k L.kern L'.kern := by
  cases h with
  | kernel hk => exact .single hk
  | newArena hs => rw [newArena_kernel hs]; exact .refl _
  | issue hs =>
    cases hs with
    | ok _ _ _ hsp hst => exact (HandlePool.KSeq.single (.split hsp)).tail (.store hst)
  | reset hs =>
    cases hs with
    | ok _ hd hrl _ => exact (HandlePool.KSeq.single (.derive hd)).tail (.release hrl)

/-- The kernel part of an `ok` step of the combined library (§57; Part XIV; HandlePool v0.5,
D.2, D.3, HP5-7; DS-v2): a finite sequence of kernel steps O1–O16 when the step passes the check
`kok` (`allocSlot` and `freeSlot` are then a `write`, §67; HandlePool v0.5, HP5-1 with the Q3
decision of 2026-11-06); `newPool`, `newStack` and `mark` are the identity. -/
theorem crel_kside {k : K} {C C' : CState} {o : COp} (h : CRel k C o (.ok C'))
    (hw : o.kok C = true) : HandlePool.KSeq k C.kern C'.kern := by
  cases o with
  | newPool st i =>
    obtain ⟨x, hx, rfl⟩ := h
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hx
    exact .refl _
  | allocSlot j d =>
    obtain ⟨x, hx, rfl⟩ := h
    cases hx with
    | ok =>
      simp only [COp.kok, Option.isSome_iff_exists] at hw
      obtain ⟨a, ha⟩ := hw
      exact .single (.write (a := a) (Guarded.ok (writer_sound ha)))
  | resolve j h m =>
    obtain ⟨x, hx, rfl⟩ := h
    cases hx with
    | ok _ _ hR _ hE =>
      exact (HandlePool.KSeq.single (.derive (Guarded.ok hR))).tail (.derive (Guarded.ok hE))
  | resolveMany j hs m =>
    obtain ⟨x, hx, rfl⟩ := h
    cases hx with
    | ok _ _ hR hE =>
      exact (HandlePool.KSeq.single (.derive (Guarded.ok hR))).trans
        (HandlePool.entries_kseq hE)
  | unresolve c =>
    obtain ⟨x, hx, rfl⟩ := h
    cases hx with
    | ok _ hr => exact HandlePool.releaseAll_kseq hr
  | freeSlot j h =>
    obtain ⟨x, hx, rfl⟩ := h
    cases hx with
    | @ok pl _ hj _ _ _ _ =>
      have hj' : C.pools[j]? = some pl := hj
      simp only [COp.kok, hj'] at hw
      obtain ⟨a, -, ha⟩ := of_decide_eq_true hw
      exact .single (.write (a := a) (Guarded.ok ha))
  | newStack st i =>
    obtain ⟨x, hx, rfl⟩ := h
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hx
    exact .refl _
  | push j n d =>
    obtain ⟨x, hx, rfl⟩ := h
    cases hx with
    | ok _ _ _ hsp hst => exact (HandlePool.KSeq.single (.split hsp)).tail (.store hst)
  | mark j =>
    obtain ⟨x, hx, rfl⟩ := h
    cases hx with
    | ok _ _ => exact .refl _
  | rewind j m =>
    obtain ⟨x, hx, rfl⟩ := h
    cases hx with
    | ok _ _ _ hsp hrl => exact (HandlePool.KSeq.single (.split hsp)).tail (.release hrl)
  | grow j b e =>
    obtain ⟨x, hx, rfl⟩ := h
    cases hx with
    | ok _ _ hrl _ _ _ hsp hst =>
      exact ((HandlePool.KSeq.single (.release hrl)).tail (.split hsp)).tail (.store hst)
  | newArena st i =>
    obtain ⟨x, hx, rfl⟩ := h
    exact LStep.kseq (.newArena hx)
  | _ =>
    obtain ⟨x, hx, rfl⟩ := h
    exact LStep.kseq (opRel_ok hx)

section RunSound
variable {k : K} [∀ r r', Decidable (k.DeclaredDisjoint r r')] [DecidablePred k.SharedMutable]
  [DecidablePred k.Pinned] [DecidablePred k.ExternalDone] [DecidablePred k.Deallocable]
  [∀ p a, Decidable (k.FreeCompat p a)] [∀ p ls s, Decidable (k.Satisfiable p ls s)]

/-- A completed run from a library-reachable state whose kernel state is reachable ends in such a
state (§57; Part XIV; HandlePool v0.5, HP5-7; DS-v2). -/
theorem crun_reach {statics : Statics} :
    ∀ {C C' : CState} {os : List COp}, CReach k statics C →
      Reachable k statics C.kern → crun k C os = some C' →
      CReach k statics C' ∧ Reachable k statics C'.kern
  | _, _, [], hC, hr, h => by cases h; exact ⟨hC, hr⟩
  | C, _, o :: os, hC, hr, h => by
    unfold crun at h
    have hs := cstep_sound (k := k) C o
    cases e : cstep k C o with
    | ok C₁ =>
      rw [e] at h hs
      dsimp only at h
      split at h
      · next hw => exact crun_reach (.step hC hs) ((crel_kside hs hw).reachable hr) h
      · cases h
    | reject => rw [e] at h; cases h
    | fail => rw [e] at h; cases h

/-- **Run soundness** (§47, §57; Part XIV; HandlePool v0.5; DS-v2): when the run of `os` from
`CState.init statics` completes, it reaches `cfinal k statics os`, which is library-reachable and
whose kernel state is reachable by O1–O16. -/
theorem crunsTo {statics : Statics} {os : List COp}
    (h : (crun k (CState.init statics) os).isSome = true) : CRuns k statics os := by
  have hr : crun k (CState.init statics) os = some (cfinal k statics os) := by
    unfold cfinal
    cases e : crun k (CState.init statics) os with
    | none => rw [e] at h; cases h
    | some C => rfl
  obtain ⟨hc, hk⟩ := crun_reach .init .init hr
  exact ⟨hr, hc, hk⟩

end RunSound

end Ern.Corpus.LibRunner
