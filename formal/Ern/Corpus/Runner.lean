import Ern.MemoryModel.Arena

/-!
# Corpus runner (test module)

A computable executor for the corpus cases of `specs/ERN_Memory_Model_Specification.md`: the
kernel operations O1–O16 (§60–§75) and the arena operations O17–O19 of Part XIV (§76–§78), over
the library state of `Ern.MemoryModel.Arena` (§46: the kernel state `S₃` and, separately, the arena
registry). This module is a test module: no model module imports it.

* `Op`: one constructor per operation, with its arguments.
* `lstep k L o`: the outcome (§58) of `o` from `L`, computed from the decidable preconditions.
* `OpRel k L o`: the relation of the operation: the kernel relation `XStep` (§60–§75) with the
  registry unchanged; `NewArenaStep`, `IssueD`, `ResetD` (Part XIV) for the arena operations.
* `lstep_sound`: the computed outcome is an outcome of the relation, `ok`, `reject` and `fail`
  alike; `lstep_ok`: an `ok` step is a library step `LStep`.
* `lrun`, `final`, `RunsTo`: a run from `LState.init statics` (§47) whose steps are all `ok` reaches
  a library-reachable state (`LReach`) whose kernel state is reachable (`Reachable`, §57).

`newArena` consults the arena registry and no other registry (§56: `others = []`): the library
states of these runs hold no administration other than arenas.
-/

namespace Ern.Corpus

open Ern.MemoryModel.Access Ern.MemoryModel.Arena

/-! ## Test contracts (§48, §80) -/

/-- A test contract `K` given by lists (§48): the `SharedMutable`, `Pinned`, `ExternalDone` and
`Deallocable` sets, and the `FreeCompat` pairs; `ExternalDone` lists identities of dynamic pinning
obligations (§75). Nothing is declared disjoint; every allocation request is satisfiable. -/
structure KD where
  shared : List Nat := []
  pinned : List Nat := []
  done : List Nat := []
  dealloc : List Nat := []
  compat : List (Nat × Nat) := []

/-- The contract `K` (§48) described by a `KD`. -/
def KD.toK (d : KD) : K :=
  ⟨fun _ _ => False, (· ∈ d.shared), (· ∈ d.pinned), (· ∈ d.done), (· ∈ d.dealloc),
    fun p a => (p, a) ∈ d.compat, fun _ _ _ => True⟩

/-- Decidability of `DeclaredDisjoint` for a test contract (§48). -/
instance (d : KD) : ∀ r r', Decidable (d.toK.DeclaredDisjoint r r') :=
  fun _ _ => inferInstanceAs (Decidable False)
/-- Decidability of `SharedMutable` for a test contract (§48). -/
instance (d : KD) : DecidablePred d.toK.SharedMutable :=
  fun l => inferInstanceAs (Decidable (l ∈ d.shared))
/-- Decidability of `Pinned` for a test contract (§48). -/
instance (d : KD) : DecidablePred d.toK.Pinned :=
  fun l => inferInstanceAs (Decidable (l ∈ d.pinned))
/-- Decidability of `ExternalDone`, on obligation identities, for a test contract (§48, §75). -/
instance (d : KD) : DecidablePred d.toK.ExternalDone :=
  fun p => inferInstanceAs (Decidable (p ∈ d.done))
/-- Decidability of `Deallocable` for a test contract (§48). -/
instance (d : KD) : DecidablePred d.toK.Deallocable :=
  fun p => inferInstanceAs (Decidable (p ∈ d.dealloc))
/-- Decidability of `FreeCompat` for a test contract (§48). -/
instance (d : KD) : ∀ p a, Decidable (d.toK.FreeCompat p a) :=
  fun p a => inferInstanceAs (Decidable ((p, a) ∈ d.compat))
/-- Decidability of `Satisfiable` for a test contract (§48). -/
instance (d : KD) : ∀ p ls s, Decidable (d.toK.Satisfiable p ls s) :=
  fun _ _ _ => inferInstanceAs (Decidable True)

/-- Test contracts satisfy `DDSound` (§61, §80): nothing is declared disjoint. -/
theorem KD.ddSound (d : KD) : DDSound d.toK := fun _ _ h => h.elim

/-! ## Operations and outcomes (§58, §60–§78) -/

/-- An operation of a corpus run: the kernel operations O1–O16 (§60–§75) and the arena operations
O17–O19 (§76–§78), with their arguments; `unpin` takes the identity of a dynamic pinning
obligation, its index in `S3.pins` (§74, §75). -/
inductive Op where
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

/-- The verdict of an outcome (§58): `ok`, `reject` or `fail`, without the state. -/
inductive Verdict where
  | ok
  | reject
  | fail
deriving DecidableEq, Repr

/-- The verdict of an outcome (§58). -/
def verdictOf {σ : Type} : Outcome3 σ → Verdict
  | .ok _ => .ok
  | .reject => .reject
  | .fail => .fail

/-- A kernel relation (§60–§75) read on library outcomes: the kernel outcome, with the arena
registry `A` unchanged on `ok` (Part XIV: kernel steps of non-administrative code). -/
def KRel (R : Outcome3 S3 → Prop) (A : List ArenaEntry) : Outcome3 LState → Prop
  | .ok L' => R (.ok L'.kern) ∧ L'.arenas = A
  | .reject => R .reject
  | .fail => R .fail

/-- The relation of operation `o` from `L` (§60–§78): the kernel relation of O1–O16 with the
registry unchanged; `NewArenaStep` with no other registry (§76, §56), the derived `IssueD` (§77)
and `ResetD` (§78). -/
def OpRel (k : K) (L : LState) : Op → Outcome3 LState → Prop
  | .derive src r m => KRel (DeriveStep src r m L.kern) L.arenas
  | .split src rs => KRel (SplitStep k src rs L.kern) L.arenas
  | .release a => KRel (ReleaseStep a L.kern) L.arenas
  | .transfer src dst => KRel (TransferStep k src dst L.kern) L.arenas
  | .depend q x => KRel (DependStep q x L.kern) L.arenas
  | .enter ps ls => KRel (EnterStep ps ls L.kern) L.arenas
  | .exit => KRel (ExitStep k L.kern) L.arenas
  | .read a ls => KRel (Read3Step a ls L.kern) L.arenas
  | .write a ls => KRel (Write3Step a ls L.kern) L.arenas
  | .writeShared a ls => KRel (WriteSharedStep k a ls L.kern) L.arenas
  | .pin p => KRel (PinStep p L.kern) L.arenas
  | .unpin o => KRel (UnpinStep k o L.kern) L.arenas
  | .endUse p => KRel (EndUseStep k p L.kern) L.arenas
  | .free p auth => KRel (FreeStep k p auth L.kern) L.arenas
  | .alloc pr ow ls => KRel (AllocStep k pr ow ls L.kern) L.arenas
  | .store a p => KRel (StoreStep a p L.kern) L.arenas
  | .newArena st i => NewArenaStep [] st i L
  | .issue i r d => IssueD k i r d L
  | .reset i => ResetD i L

/-! ## Executor -/

section Exec
variable (k : K) [∀ r r', Decidable (k.DeclaredDisjoint r r')] [DecidablePred k.SharedMutable]
  [DecidablePred k.Pinned] [DecidablePred k.ExternalDone] [DecidablePred k.Deallocable]
  [∀ p a, Decidable (k.FreeCompat p a)] [∀ p ls s, Decidable (k.Satisfiable p ls s)]

/-- A guarded kernel step (§58) on a library state: `ok` with the effect and the registry
unchanged when the preconditions hold, `reject` otherwise. -/
def kg (L : LState) (p : Prop) [Decidable p] (s : S3) : Outcome3 LState :=
  if p then .ok ⟨s, L.arenas⟩ else .reject

/-- The computed outcome of operation `o` from `L` (§58, §60–§78). `issue` follows `IssueD`
(static checks, availability `fail`, `split`, `store`); `reset` follows `ResetD` (`derive`,
`release`, §78.3). -/
def lstep (L : LState) : Op → Outcome3 LState
  | .derive src r m => kg L (DerivePre L.kern src r m) (deriveEff L.kern src r m)
  | .split src rs => kg L (SplitPre k L.kern src rs) (splitEff L.kern src rs)
  | .release a => kg L (ReleasePre L.kern a) (releaseEff L.kern a)
  | .transfer src dst => kg L (TransferPre k L.kern src dst) (transferEff L.kern src dst)
  | .depend q x => kg L (DependPre L.kern q x) (dependEff L.kern q x)
  | .enter ps ls => kg L (EnterPre L.kern ps ls) (enterEff L.kern ps ls)
  | .exit => kg L (ExitPre k L.kern) (exitEff L.kern)
  | .read a ls => kg L (Read3Pre L.kern a ls) L.kern
  | .write a ls => kg L (Write3Pre L.kern a ls) (write3Eff L.kern ls)
  | .writeShared a ls => kg L (WriteSharedPre k L.kern a ls) (write3Eff L.kern ls)
  | .pin p => kg L (PinPre L.kern p) (pinEff L.kern p)
  | .unpin o => kg L (UnpinPre k L.kern o) (unpinEff L.kern o)
  | .endUse p => kg L (EndUsePre k L.kern p) (endUseEff L.kern p)
  | .free p auth => kg L (FreePre k L.kern p auth) (freeEff L.kern p)
  | .alloc pr ow ls =>
    if AllocStatic k L.kern pr ow ls then
      if k.Satisfiable pr ls L.kern then .ok ⟨allocEff L.kern ow ls, L.arenas⟩ else .fail
    else .reject
  | .store a p => kg L (StorePre L.kern a p) (storeEff L.kern a p)
  | .newArena st i =>
    if NewArenaPre L.kern L.arenas [] st i then .ok (newArenaEff L st i) else .reject
  | .issue i r d =>
    match L.arenas[i]? with
    | none => .reject
    | some E =>
      if IssueStatic L.kern E r d then
        if Avail E r then
          if SplitPre k L.kern E.internal [r] then
            if StorePre (splitEff L.kern E.internal [r]) L.kern.A.length d then
              .ok ⟨storeEff (splitEff L.kern E.internal [r]) L.kern.A.length d,
                L.arenas.set i (issueMeta L.kern E r)⟩
            else .reject
          else .reject
        else .fail
      else .reject
  | .reset i =>
    match L.arenas[i]? with
    | none => .reject
    | some E =>
      if DerivePre L.kern E.internal (footprint L.kern.P E.storage) .modify then
        if ReleasePre (deriveEff L.kern E.internal (footprint L.kern.P E.storage) .modify)
            L.kern.A.length then
          if ResetNoDeps L.kern E then
            .ok ⟨releaseEff (deriveEff L.kern E.internal (footprint L.kern.P E.storage) .modify)
              L.kern.A.length, L.arenas.set i (resetMeta L.kern E)⟩
          else .reject
        else .reject
      else .reject

/-- The state after `o` from `L` when it is `ok`; `L` otherwise (§58). -/
def next (L : LState) (o : Op) : LState :=
  match lstep k L o with
  | .ok L' => L'
  | _ => L

/-- The state reached by the operations `os` from `L` when every step is `ok` (§58); `none` as soon
as a step is not `ok`. -/
def lrun (L : LState) : List Op → Option LState
  | [] => some L
  | o :: os =>
    match lstep k L o with
    | .ok L' => lrun L' os
    | _ => none

/-- The state reached by `os` from `LState.init statics` (§47); `LState.init statics` when a step is
not `ok` (used only under `(lrun …).isSome = true`, see `runsTo`). -/
def final (statics : Statics) (os : List Op) : LState :=
  (lrun k (LState.init statics) os).getD (LState.init statics)

/-- A run of `os` from `LState.init statics` (§47) has only `ok` steps and reaches `L`; `L` is
library-reachable (Part XIV) and its kernel state is reachable (§57). -/
structure RunsTo (statics : Statics) (os : List Op) (L : LState) : Prop where
  /-- Every step of the run is `ok` and the run ends in `L`. -/
  run : lrun k (LState.init statics) os = some L
  /-- `L` is library-reachable (Part XIV, §46). -/
  lreach : LReach k statics L
  /-- The kernel state of `L` is reachable from `S3.init statics` by O1–O16 (§57). -/
  reach : Reachable k statics L.kern

/-- The run of `os` from `LState.init statics` has only `ok` steps (§47, §57, Part XIV). -/
abbrev Runs (statics : Statics) (os : List Op) : Prop :=
  RunsTo k statics os (final k statics os)

end Exec

/-! ## Soundness -/

/-- An `ok` outcome of a relation of `OpRel` is a library step (Part XIV, §57): a kernel step
O1–O16 with the registry unchanged, `newArena`, the derived `issue` or the derived `reset`. -/
theorem opRel_ok {k : K} {L L' : LState} : ∀ {o : Op}, OpRel k L o (.ok L') → LStep k L L'
  | .derive .., h | .split .., h | .release .., h | .transfer .., h | .depend .., h
  | .enter .., h | .exit, h | .read .., h | .write .., h | .writeShared .., h | .pin .., h
  | .unpin .., h | .endUse .., h | .free .., h | .alloc .., h | .store .., h => by
    obtain ⟨h, e⟩ := h
    have hL : L' = ⟨L'.kern, L.arenas⟩ := by rw [← e]
    rw [hL]
    first
      | exact .kernel (.derive h) | exact .kernel (.split h) | exact .kernel (.release h)
      | exact .kernel (.transfer h) | exact .kernel (.depend h) | exact .kernel (.enter h)
      | exact .kernel (.exit h) | exact .kernel (.read h) | exact .kernel (.write h)
      | exact .kernel (.writeShared h) | exact .kernel (.pin h) | exact .kernel (.unpin h)
      | exact .kernel (.endUse h) | exact .kernel (.free h) | exact .kernel (.alloc h)
      | exact .kernel (.store h)
  | .newArena .., h => .newArena h
  | .issue .., h => .issue h
  | .reset .., h => .reset h

section Sound
variable {k : K} [∀ r r', Decidable (k.DeclaredDisjoint r r')] [DecidablePred k.SharedMutable]
  [DecidablePred k.Pinned] [DecidablePred k.ExternalDone] [DecidablePred k.Deallocable]
  [∀ p a, Decidable (k.FreeCompat p a)] [∀ p ls s, Decidable (k.Satisfiable p ls s)]

/-- A guarded kernel step computed by `kg` is an outcome of its relation (§58). -/
theorem kg_sound {L : LState} {p : Prop} [Decidable p] {s : S3} :
    KRel (Guarded p s) L.arenas (kg L p s) := by
  unfold kg
  split
  · next h => exact ⟨.ok h, rfl⟩
  · next h => exact .reject h

/-- **Step soundness** (§58, §60–§78): the computed outcome of `o` from `L` is an outcome of the
relation of `o`, `ok`, `reject` and `fail` alike. -/
theorem lstep_sound (L : LState) (o : Op) : OpRel k L o (lstep k L o) := by
  cases o with
  | derive => exact kg_sound
  | split => exact kg_sound
  | release => exact kg_sound
  | transfer => exact kg_sound
  | depend => exact kg_sound
  | enter => exact kg_sound
  | exit => exact kg_sound
  | read => exact kg_sound
  | write => exact kg_sound
  | writeShared => exact kg_sound
  | pin => exact kg_sound
  | unpin => exact kg_sound
  | endUse => exact kg_sound
  | free => exact kg_sound
  | store => exact kg_sound
  | alloc pr ow ls =>
    show KRel (AllocStep k pr ow ls L.kern) L.arenas _
    dsimp only [lstep]
    split
    · next h =>
      split
      · next hs => exact ⟨.ok h hs, rfl⟩
      · next hs => exact .fail h hs
    · next h => exact .reject h
  | newArena st i =>
    show NewArenaStep [] st i L _
    dsimp only [lstep]
    split
    · next h => exact .ok h
    · next h => exact .reject h
  | issue i r d =>
    show IssueD k i r d L _
    dsimp only [lstep]
    split
    · next hE => exact .noEntry hE
    · next E hE =>
      split
      · next h1 =>
        split
        · next h2 =>
          split
          · next h3 =>
            split
            · next h4 => exact .ok hE h1 h2 (.ok h3) (.ok h4)
            · next h4 => exact .store hE h1 h2 (.ok h3) (.reject h4)
          · next h3 => exact .split hE h1 h2 (.reject h3)
        · next h2 => exact .fail hE h1 h2
      · next h1 => exact .static hE h1
  | reset i =>
    show ResetD i L _
    dsimp only [lstep]
    split
    · next hE => exact .noEntry hE
    · next E hE =>
      split
      · next h1 =>
        split
        · next h2 =>
          split
          · next h3 => exact .ok hE (.ok h1) (.ok h2) h3
          · next h3 => exact .contract hE (.ok h1) (.ok h2) h3
        · next h2 => exact .release hE (.ok h1) (.reject h2)
      · next h1 => exact .derive hE (.reject h1)

/-- An `ok` computed step is a library step (Part XIV, §58). -/
theorem lstep_ok {L L' : LState} {o : Op} (h : lstep k L o = .ok L') : LStep k L L' :=
  opRel_ok (h ▸ lstep_sound L o)

/-- A run whose steps are all `ok`, from a library-reachable state, ends in a library-reachable
state (Part XIV, §46). -/
theorem lrun_reach {statics : Statics} :
    ∀ {L L' : LState} {os : List Op}, LReach k statics L → lrun k L os = some L' →
      LReach k statics L'
  | _, _, [], hL, h => by cases h; exact hL
  | L, _, o :: os, hL, h => by
    unfold lrun at h
    cases hs : lstep k L o with
    | ok L₁ => rw [hs] at h; exact lrun_reach (.step hL (lstep_ok hs)) h
    | reject => rw [hs] at h; cases h
    | fail => rw [hs] at h; cases h

/-- **Run soundness** (§47, §57, Part XIV): when every step of `os` from `LState.init statics` is
`ok`, the run reaches `final k statics os`, which is library-reachable and whose kernel state is
reachable by O1–O16. -/
theorem runsTo {statics : Statics} {os : List Op}
    (h : (lrun k (LState.init statics) os).isSome = true) : Runs k statics os := by
  have hr : lrun k (LState.init statics) os = some (final k statics os) := by
    unfold final
    cases e : lrun k (LState.init statics) os with
    | none => rw [e] at h; cases h
    | some L => rfl
  have hl := lrun_reach .init hr
  exact ⟨hr, hl, hl.ng.reachable⟩

/-- A computed `reject` is a `reject` outcome of the relation (§58). -/
theorem rejects {L : LState} {o : Op} (h : verdictOf (lstep k L o) = .reject) :
    OpRel k L o .reject := by
  have hs := lstep_sound (k := k) L o
  revert hs h
  cases lstep k L o with
  | ok => intro h; cases h
  | reject => intro _ hs; exact hs
  | fail => intro h; cases h

/-- A computed `fail` is a `fail` outcome of the relation (§58). -/
theorem fails {L : LState} {o : Op} (h : verdictOf (lstep k L o) = .fail) :
    OpRel k L o .fail := by
  have hs := lstep_sound (k := k) L o
  revert hs h
  cases lstep k L o with
  | ok => intro h; cases h
  | reject => intro h; cases h
  | fail => intro _ hs; exact hs

/-- A computed `ok` is the `ok` outcome of the relation to `next k L o` (§58). -/
theorem oks {L : LState} {o : Op} (h : verdictOf (lstep k L o) = .ok) :
    OpRel k L o (.ok (next k L o)) := by
  have hs := lstep_sound (k := k) L o
  unfold next
  revert hs h
  cases lstep k L o with
  | ok => intro _ hs; exact hs
  | reject => intro h; cases h
  | fail => intro h; cases h

end Sound

end Ern.Corpus
