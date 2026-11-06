import Ern.Corpus.Runner
import Ern.MemoryModel.RefinementArena

/-!
# Corpus MM23-H: refinement (test module)

The cases of corpus MM23-H of the Jalon 3 material (`ERN_Jalon3_materiel.md`, §3; non-normative
design material), replayed on the reference refinement of
`specs/ERN_Memory_Model_Specification_v0.1.md` (§82, Part XIV). This is a test module: no model or
library module imports it.

Each case is a run from the initial state (§47) translated into the elementary memory machine with
the contract, the deallocation compatibility (equality of tokens), the read and write obligations
and the parameters fixed once for the run (§20.3 ¶3, §82): the test layout `piOf` of
`Ern.MemoryModel.Refinement.Runs` (each root place in its own allocation, each leaf 8 bytes at 8
times its rank, `LayoutWF` established by `Repr`), the placement `topPlacement`, the tokens
`100 + r`, the 8-byte reference encoding `pe8`. Runs of kernel operations only are kernel
simulation runs (`SimRun`, built by `srun`, conclusions by `simulation`); runs with an arena are
library simulation runs (`LSimRun`, built by the runner `lsrun` below, conclusions by
`lsimulation`), in which `issue` is the derived library operation (`split` then `store`) and
`reset` the derived reset (`derive` then `release`). The reached states are those of these runs
(material §0, rule 3). The obtained result is stated with the kernel relation of the step under
test, the machine relations of its realized raw operations (`ReadStep`, `WriteStep`,
`DeallocStep`, `Exec`) and the bytes read back, all decided by `decide`.

Each docstring gives the expected verdict of the material, the obtained one, the class (material
§0, rule 5: `R` refinement) and the positive twin of each rejection or `fail` (rule 2). A case
whose obtained verdict differs from its expected one, or whose expected verdict has no spec v0.1
source, is kept with its expected verdict and classified; no case is corrected. No expected
verdict of this corpus changes under v0.1.

Address rules of references (`Refinement.ptrAddr`): a region whose leaves all have zero physical
size, the empty region included, has the base of the allocation of the effective anchor of its
authority, with that allocation as provenance (§82.2, last sentence); a region with a leaf of
nonzero size has the lowest address among its leaves of nonzero size (a decision of the user's
brief, recorded for §82.3, not stated by v0.1); the destination leaf has the size of a
reference (`pe8.size = 8`).

Not encoded (classified, material §3 and §6; non-blocking by the user's arbitration Q20):
* MM23-H14, a raw pointer formed before a call and used during the call on the footprint of a
  `Modify` parameter: undefined behavior that no safe program constructs; class spec 3 (strong
  protection of parameters during the invocation, §72 last paragraph, §81) with the boundary of
  §19 (reconstruction of accesses from raw addresses).
* MM23-H17, a reference stored into a leaf of zero size: a conditional obligation of specs 4 and
  11 (a reference occupies a leaf of pointer size), not a guarantee of the refinement; class
  specs 4 and 11 (§81, §82.3 "a single logical leaf with an appropriate representation"). The
  pointer-size rule is a hypothesis of `Refinement.pointer_sound_store`.

Open boundaries of the spec (non-blocking by arbitration Q22): MM23-H04 and MM23-H13 (propagation
of provenance through copies, §10 ¶4, §19) and MM23-H09 (deallocation of automatic storage at
exit, §9 ¶2, §73), for which `Refinement.exitRoots` is the reference realization.
-/

namespace Ern.Corpus.MM23H

open Ern.MemoryModel Ern.MemoryModel.Access Ern.MemoryModel.Arena Ern.MemoryModel.Refinement
  Ern.MemoryModel.RefinementArena Ern.Corpus
open Ern.MemoryModel.Refinement.Runs (piOf piOf_ok obR obW wv decodedAt kernelRun sinit)

/-! ## Test contracts (§48, §80) -/

/-- Test contract (§48): the `SharedMutable`, `Pinned`, `ExternalDone` (on identities of dynamic
pinning obligations, §75), `Deallocable` and `FreeCompat` lists of a `KD`; `DeclaredDisjoint` is
leaf disjointness (§23) when `dd` holds and declares nothing otherwise; `Satisfiable` (§71) is
`sat` for every request. -/
def KT (d : KD) (dd sat : Bool) : K :=
  ⟨fun r r' => dd = true ∧ ∀ l ∈ r, l ∉ r', (· ∈ d.shared), (· ∈ d.pinned), (· ∈ d.done),
    (· ∈ d.dealloc), fun p a => (p, a) ∈ d.compat, fun _ _ _ => sat = true⟩

/-- Decidability of `DeclaredDisjoint` for a test contract (§48). -/
instance (d : KD) (dd sat : Bool) : ∀ r r', Decidable ((KT d dd sat).DeclaredDisjoint r r') :=
  fun r r' => inferInstanceAs (Decidable (dd = true ∧ ∀ l ∈ r, l ∉ r'))
/-- Decidability of `SharedMutable` for a test contract (§48). -/
instance (d : KD) (dd sat : Bool) : DecidablePred (KT d dd sat).SharedMutable :=
  fun l => inferInstanceAs (Decidable (l ∈ d.shared))
/-- Decidability of `Pinned` for a test contract (§48). -/
instance (d : KD) (dd sat : Bool) : DecidablePred (KT d dd sat).Pinned :=
  fun l => inferInstanceAs (Decidable (l ∈ d.pinned))
/-- Decidability of `ExternalDone` for a test contract (§48, §75). -/
instance (d : KD) (dd sat : Bool) : DecidablePred (KT d dd sat).ExternalDone :=
  fun o => inferInstanceAs (Decidable (o ∈ d.done))
/-- Decidability of `Deallocable` for a test contract (§48). -/
instance (d : KD) (dd sat : Bool) : DecidablePred (KT d dd sat).Deallocable :=
  fun p => inferInstanceAs (Decidable (p ∈ d.dealloc))
/-- Decidability of `FreeCompat` for a test contract (§48). -/
instance (d : KD) (dd sat : Bool) : ∀ p a, Decidable ((KT d dd sat).FreeCompat p a) :=
  fun p a => inferInstanceAs (Decidable ((p, a) ∈ d.compat))
/-- Decidability of `Satisfiable` for a test contract (§48). -/
instance (d : KD) (dd sat : Bool) : ∀ p ls s, Decidable ((KT d dd sat).Satisfiable p ls s) :=
  fun _ _ _ => inferInstanceAs (Decidable (sat = true))

/-- Test contracts satisfy `DDSound` (§61, §80): what they declare disjoint has disjoint leaves
(§23). -/
theorem KT.ddSound (d : KD) (dd sat : Bool) : DDSound (KT d dd sat) := fun _ _ h => h.2

/-- A root leaf of a local shape (§72, §71.1). -/
abbrev lf : Option Nat × Nat := (none, 0)

/-- A leaf part of the place `p` in a local shape (§72, §71.1). -/
abbrev pt (p : Nat) : Option Nat × Nat := (some p, 0)

/-! ## Translated runs (§82 preamble, §82.7) -/

/-- The obligations of the initial state of a translated run (§47, §82; `SimRun.init`,
`LSimRun.init`): well-formed statics, the layout of the static places, the obligations of the
creations and writes of the statics. -/
def InitOK (statics : Statics) (π : Params Unit) : Prop :=
  StaticsOK statics ∧
    NewLayout π.L (S3.init statics).P 0 0 π.geom (rootIdx (statics.map (·.1))) ∧
    OblAlong obR obW (run Machine.State.empty (allocOps (Ty := Unit) π.pl π.geom π.rtok 0
      Machine.State.empty (rootIdx (statics.map (·.1))))) (writeOps (run Machine.State.empty
        (allocOps (Ty := Unit) π.pl π.geom π.rtok 0 Machine.State.empty
          (rootIdx (statics.map (·.1))))) π.L π.ty π.ival (initLeaves statics))

/-- Decidability of `InitOK` (§47, §82). -/
instance (statics : Statics) (π : Params Unit) : Decidable (InitOK statics π) := by
  unfold InitOK; infer_instance

section Runner

variable (k : K) [∀ r r', Decidable (k.DeclaredDisjoint r r')] [DecidablePred k.SharedMutable]
  [DecidablePred k.Pinned] [DecidablePred k.ExternalDone] [DecidablePred k.Deallocable]
  [∀ p a, Decidable (k.FreeCompat p a)] [∀ p ls s, Decidable (k.Satisfiable p ls s)]

/-- Final kernel and memory states of the translated kernel run of `ops` from `S3.init statics`
(§82 preamble; `srun`); the initial states when a step is not `ok`. -/
def kfin (statics : Statics) (π : Params Unit) (ops : List KOp) : S3 × Machine.State :=
  (srun k (· = ·) obR obW π (sinit statics π) ops).getD (sinit statics π)

/-- The state after an `ok` library operation from `L` (Part XIV, §58, §60–§78): the effect of a
kernel operation whose preconditions hold, registry unchanged; the effect of `newArena` under its
preconditions (§76); the `ok` state of the derived `issue` and `reset` computed by the corpus
runner (§77, §78). `none` otherwise. -/
def lnext (L : LState) : LOp → Option LState
  | .kernel op => if OpPre k op L.kern then some ⟨opEff3 op L.kern, L.arenas⟩ else none
  | .newArena others st i =>
    if NewArenaPre L.kern L.arenas others st i then some (newArenaEff L st i) else none
  | .issue i r d =>
    match lstep k L (.issue i r d) with
    | .ok L' => some L'
    | _ => none
  | .reset i =>
    match lstep k L (.reset i) with
    | .ok L' => some L'
    | _ => none

variable (π : Params Unit)

/-- One translated library step (§82.7, `LSimRun.step`): when the library operation is `ok` and
the obligations of its kernel steps hold, the next library state and the memory state after the
raw operations of its kernel steps. -/
def lsstep (st : LState × Machine.State) (lop : LOp) : Option (LState × Machine.State) :=
  match lnext k st.1 lop with
  | some L' =>
    if KObl k (· = ·) obR obW π (kexp lop st.1) st.2 then
      some (L', run st.2 (lopsOf π lop st.1 st.2))
    else none
  | none => none

/-- A translated library run of a list of operations, in order (§82.7). -/
def lsrun : LState × Machine.State → List LOp → Option (LState × Machine.State)
  | st, [] => some st
  | st, lop :: lops => (lsstep k π st lop).bind fun st' => lsrun st' lops

end Runner

/-- Initial library and memory states of a translated library run (§47, §82;
`LSimRun.init`). -/
def linit (statics : Statics) (π : Params Unit) : LState × Machine.State :=
  (LState.init statics, minit π statics)

/-- Final library and memory states of the translated library run of `lops` (§82.7); the initial
states when a step is not `ok`. -/
def lfin (k : K) [∀ r r', Decidable (k.DeclaredDisjoint r r')] [DecidablePred k.SharedMutable]
    [DecidablePred k.Pinned] [DecidablePred k.ExternalDone] [DecidablePred k.Deallocable]
    [∀ p a, Decidable (k.FreeCompat p a)] [∀ p ls s, Decidable (k.Satisfiable p ls s)]
    (statics : Statics) (π : Params Unit) (lops : List LOp) : LState × Machine.State :=
  (lsrun k π (linit statics π) lops).getD (linit statics π)

/-- The kernel operation of a library operation, if any (Part XIV, §60–§75). -/
def kernelOf : LOp → Option KOp
  | .kernel op => some op
  | _ => none

/-- The places at the end of a library run, computed from its kernel operations without checks
(§82): `newArena`, `issue` and `reset` create no place (§76–§78). The layout parameter is fixed
once from them. -/
def placesOf (statics : Statics) (lops : List LOp) : List Place :=
  (kernelRun (S3.init statics) (lops.filterMap kernelOf)).P

section Sound

variable {k : K} [∀ r r', Decidable (k.DeclaredDisjoint r r')] [DecidablePred k.SharedMutable]
  [DecidablePred k.Pinned] [DecidablePred k.ExternalDone] [DecidablePred k.Deallocable]
  [∀ p a, Decidable (k.FreeCompat p a)] [∀ p ls s, Decidable (k.Satisfiable p ls s)]

/-- A computed next library state is the `ok` step of the library operation (Part XIV, §58,
§76–§78). -/
theorem lnext_sound {L L' : LState} {lop : LOp} (h : lnext k L lop = some L') :
    LOpStep k lop L L' := by
  cases lop with
  | kernel op =>
    simp only [lnext] at h
    split at h
    · next hp => cases h; exact ⟨opStep_of_pre hp, rfl⟩
    · cases h
  | newArena others st i =>
    simp only [lnext] at h
    split at h
    · next hp => cases h; exact .ok hp
    · cases h
  | issue i r d =>
    have hs := lstep_sound (k := k) L (.issue i r d)
    simp only [lnext] at h
    split at h
    · next L₁ he => cases h; rw [he] at hs; exact hs
    · cases h
  | reset i =>
    have hs := lstep_sound (k := k) L (.reset i)
    simp only [lnext] at h
    split at h
    · next L₁ he => cases h; rw [he] at hs; exact hs
    · cases h

/-- A successful translated library run extends a library simulation run (§82.7). -/
theorem lsrun_sound {statics : Statics} {π : Params Unit} :
    ∀ (lops : List LOp) (st st' : LState × Machine.State),
      LSimRun k (· = ·) obR obW statics π st.1 st.2 → lsrun k π st lops = some st' →
      LSimRun k (· = ·) obR obW statics π st'.1 st'.2
  | [], st, st', h, he => by
    simp only [lsrun, Option.some.injEq] at he; subst he; exact h
  | lop :: lops, st, st', h, he => by
    simp only [lsrun] at he
    cases hs : lsstep k π st lop with
    | none => rw [hs] at he; cases he
    | some st₁ =>
      rw [hs] at he
      simp only [Option.bind_some] at he
      unfold lsstep at hs
      split at hs
      · next L' hn =>
        split at hs
        · next hc =>
          simp only [Option.some.injEq] at hs; subst hs
          exact lsrun_sound lops _ st' (.step h (lnext_sound hn) hc) he
        · cases hs
      · cases hs

/-- A successful translated kernel run from `S3.init statics` is a kernel simulation run (§82
preamble). -/
theorem ksim {statics : Statics} {π : Params Unit} {ops : List KOp} (hi : InitOK statics π)
    (h : (srun k (· = ·) obR obW π (sinit statics π) ops).isSome = true) :
    SimRun k (· = ·) obR obW statics π (kfin k statics π ops).1 (kfin k statics π ops).2 :=
  srun_sound ops (sinit statics π) _ (.init hi.1 hi.2.1 hi.2.2) (some_getD _ h)

/-- A successful translated library run from `LState.init statics` is a library simulation run
(§82.7). -/
theorem lsim {statics : Statics} {π : Params Unit} {lops : List LOp} (hi : InitOK statics π)
    (h : (lsrun k π (linit statics π) lops).isSome = true) :
    LSimRun k (· = ·) obR obW statics π (lfin k statics π lops).1 (lfin k statics π lops).2 :=
  lsrun_sound lops (linit statics π) _ (.init hi.1 hi.2.1 hi.2.2) (some_getD _ h)

end Sound

/-- The raw operations realizing a kernel step from a state of a kernel simulation run are an
execution of `ok` raw steps (§82 preamble, `r6_reachable`), under `DDSound(K)` (§80), when the
preconditions of the step and its obligations hold. -/
theorem kexec {k : K} {statics : Statics} {π : Params Unit} {s3 : S3} {s2 : Machine.State}
    {op : KOp} (hdd : DDSound k)
    (hπ : ParamsOK (· = ·) π) (h : SimRun k (· = ·) obR obW statics π s3 s2)
    (hc : OpPre k op s3 ∧ StepObl k (· = ·) obR obW π op s3 s2) :
    Machine.Exec (· = ·) obR obW (opsOf π op s3 s2) s2 (run s2 (opsOf π op s3 s2)) :=
  have hs := simulation hdd hπ h
  (r6_reachable hdd h.staticsOK hs.2.2 hπ hs.2.1 (opStep_of_pre hc.1) hc.2).1

/-! ## Raw operations and bytes read back (§9, §15–§17, §20) -/

/-- The allocation a raw operation reads, writes or deallocates (§15, §16, §17); none for a
creation. -/
def opAlloc {Ty : Type} : Machine.Op Ty → Option Nat
  | .read ac _ => some ac.prov
  | .write ac _ _ => some ac.prov
  | .dealloc i _ => some i
  | .alloc .. => none

/-- The kind of a raw operation (§20.1): 0 read, 1 write, 2 deallocation, 3 creation. -/
def opKind {Ty : Type} : Machine.Op Ty → Nat
  | .read .. => 0
  | .write .. => 1
  | .dealloc .. => 2
  | .alloc .. => 3

/-- The size of a raw creation (§9 ¶1, §9 ¶11). -/
def opSize {Ty : Type} : Machine.Op Ty → Option Nat
  | .alloc _ _ size _ _ => some size
  | _ => none

/-- The allocation and presented authority of a raw deallocation (§17). -/
def opDealloc {Ty : Type} : Machine.Op Ty → Option (Nat × Nat)
  | .dealloc i auth => some (i, auth)
  | _ => none

/-- Liveness of the allocation `i` of `s`, if registered (§9 ¶1, §17 ¶3). -/
def liveOf (s : Machine.State) (i : Nat) : Option Bool := (s.allocs i).map (·.live)

/-- The bytes returned by a raw read through `ac` (§20.2 ¶1): the accessed range of the allocation
of its provenance; empty when the provenance names no allocation. -/
def readVal (s : Machine.State) (ac : Machine.Access) : List Machine.AByte :=
  ((s.allocs ac.prov).map fun a => a.bytesAt (ac.addr - a.base) ac.len).getD []

/-- A raw read meeting the kernel read conditions and the decidable read obligation of the runs is
`ok` and returns `readVal` (§15, §20.1 ¶2, §20.2 ¶1; the static obligation of the runs is
`True`). -/
theorem readStep_of {s : Machine.State} {ac : Machine.Access}
    (h : Machine.CanRead s ac ∧ obR.dec s ac ()) :
    Machine.ReadStep obR ac () s (.ok (readVal s ac)) := by
  obtain ⟨a, ha, -⟩ := h.1
  have e : readVal s ac = a.bytesAt (ac.addr - a.base) ac.len := by simp [readVal, ha]
  rw [e]
  exact .ok ha ⟨h.1, h.2, trivial⟩

/-! ## Reached states and their simulation (§82 preamble, §82.7) -/

/-- A reached state of a kernel run and the conclusions of `simulation` (§82 preamble, §57,
§9 ¶9): a translated run from `S3.init statics` reaches `s`; its memory state is reached from the
empty state by an execution of `ok` raw steps and is related to the kernel state by `Repr` (so the
layout satisfies `LayoutWF`); the kernel state is reachable. -/
def Sim (k : K) (statics : Statics) (π : Params Unit) (s : S3 × Machine.State) : Prop :=
  SimRun k (· = ·) obR obW statics π s.1 s.2 ∧
    (∃ os, Machine.Exec (· = ·) obR obW os Machine.State.empty s.2) ∧
    Refinement.Repr π.L π.rtok s.1 s.2 ∧ Access.Reachable k statics s.1

/-- A reached state of a library run and the conclusions of `lsimulation` (§82.7, Part XIV): a
translated library run from `LState.init statics` reaches `st`; its memory state is reached from
the empty state by an execution of `ok` raw steps and is related to the kernel state by `Repr`;
the library state is library-reachable. -/
def LSim (k : K) (statics : Statics) (π : Params Unit) (st : LState × Machine.State) : Prop :=
  LSimRun k (· = ·) obR obW statics π st.1 st.2 ∧
    (∃ os, Machine.Exec (· = ·) obR obW os Machine.State.empty st.2) ∧
    Refinement.Repr π.L π.rtok st.1.kern st.2 ∧ LReach k statics st.1

section Reached

variable {k : K} [∀ r r', Decidable (k.DeclaredDisjoint r r')] [DecidablePred k.SharedMutable]
  [DecidablePred k.Pinned] [DecidablePred k.ExternalDone] [DecidablePred k.Deallocable]
  [∀ p a, Decidable (k.FreeCompat p a)] [∀ p ls s, Decidable (k.Satisfiable p ls s)]

/-- A successful translated kernel run reaches its final states, with the conclusions of
`simulation` under `DDSound(K)` (§82 preamble, §80). -/
theorem sim {statics : Statics} {P : List Place} {z : List Nat} {ops : List KOp}
    (hdd : DDSound k) (hi : InitOK statics (piOf P z))
    (h : (srun k (· = ·) obR obW (piOf P z) (sinit statics (piOf P z)) ops).isSome = true) :
    Sim k statics (piOf P z) (kfin k statics (piOf P z) ops) :=
  have hs := ksim hi h
  ⟨hs, simulation hdd (piOf_ok P z) hs⟩

/-- A successful translated library run reaches its final states, with the conclusions of
`lsimulation` under `DDSound(K)` (§82.7, §80). -/
theorem lsimOf {statics : Statics} {P : List Place} {z : List Nat} {lops : List LOp}
    (hdd : DDSound k) (hi : InitOK statics (piOf P z))
    (h : (lsrun k (piOf P z) (linit statics (piOf P z)) lops).isSome = true) :
    LSim k statics (piOf P z) (lfin k statics (piOf P z) lops) :=
  have hs := lsim hi h
  ⟨hs, lsimulation hdd (piOf_ok P z) hs⟩

end Reached

/-- Initialization state of the range of leaf `l` in `s`, if its allocation is registered (§10,
§15.3). -/
def initOf (s : Machine.State) (L : Layout) (l : Nat) : Option Bool :=
  (s.allocs (L l).alloc).map fun a => decide (a.InitRange (L l).off (L l).len)

/-! ## Run R1: owned storage, pinning, transfer, leak, exit (H03, H04, H07, H08, H09) -/

/-- Contract of R1 (§48, §75): `ExternalDone` for the pinning obligation 0, the one `pin 3`
installs (§74: its identity is its index among the obligations of the state). -/
abbrev K1 : K := KT { done := [0] } false true

/-- Run R1 (§72, §67, §71, §74, §63, §75, §69, §73): frame 1 with the provider 0 and the values
`v` (1) and `w` (2), 0 and 1 written; storage 3 (one leaf) allocated from 0 for `v` (root
authority 3 held by `v`) and written; 3 pinned (`pin 3` installs the obligation 0, §74);
`transfer(v, w)`; 3 unpinned (`unpin` designates the obligation 0, §75); `endUse(w)`; exit. -/
def r1 : List KOp := [.enter [] [lf, lf, lf], .write 0 [0] wv, .write 1 [1] wv, .alloc 0 1 [lf],
  .write 3 [3] wv, .pin 3, .transfer 1 2, .unpin 0, .endUse 2, .exit]

/-- Parameters of R1, fixed once from its final places (§82). -/
def π1 : Params Unit := piOf (kernelRun (S3.init []) r1).P []

/-- State of R1 after its first `n` steps (§82). -/
def st1 (n : Nat) : S3 × Machine.State := kfin K1 [] π1 (r1.take n)

/-- The raw operations realizing `transfer(v, w)` in R1 (§82, §63). -/
def t1 : List (Machine.Op Unit) := opsOf π1 (.transfer 1 2) (st1 6).1 (st1 6).2

/-- **MM23-H03** (material §3, class R). Transfer of a value whose owned storage is pinned.
Expected (material): no machine step on the storage, address unchanged. Obtained: the same.
After six steps of R1 (reached, `Sim`) the storage leaf 3 is pinned by the active obligation 0
(§74); `transfer(v, w)` is `ok` (§63.5: storage merely owned by the source does not prevent it,
§87; §63.9: `w` is usable afterwards); its raw operations are an execution of `ok` steps (§82),
none reads, writes or deallocates the allocation of 3, which is live before and after them at the
same address (§82.6, §74). No rejection, no twin. -/
theorem H03 : Sim K1 [] π1 (st1 6) ∧ (st1 6).1.pin 3 = true ∧
    TransferStep K1 1 2 (st1 6).1 (.ok (transferEff (st1 6).1 1 2)) ∧
    Machine.Exec (· = ·) obR obW t1 (st1 6).2 (run (st1 6).2 t1) ∧
    (∀ o ∈ t1, opAlloc o ≠ some (π1.L 3).alloc) ∧
    liveOf (st1 6).2 (π1.L 3).alloc = some true ∧
    liveOf (run (st1 6).2 t1) (π1.L 3).alloc = some true ∧
    leafAddr (run (st1 6).2 t1) π1.L 3 = leafAddr (st1 6).2 π1.L 3 :=
  have h := sim (KT.ddSound _ _ _) (by decide) (by decide)
  ⟨h, by decide, .ok (by decide), kexec (KT.ddSound _ _ _) (piOf_ok _ _) h.1 (by decide), by decide,
    by decide, by decide, by decide⟩

/-- **MM23-H04** (material §3, class R). Transfer of a value in place. Expected (material): a read
then a write of the bytes, provenance kept; the source `Moved` and unreadable, its bytes still
initialized. Obtained: the same. From the reached state of H03, the raw operations of
`transfer(v, w)` are a read of the range of `v` then a write of the range of `w` (§82, §63); after
them the range of `w` holds the bytes of `v`, value and provenance (§16 ¶2, §20.2 ¶1), and the
range of `v` is unchanged and initialized; in the kernel the leaf of `v` is `Moved` (§63 effect)
and every read of it is rejected (§66.1). Twin of the rejected read, the same run without the
transfer: the read of `v` is `ok`. The provenance is kept because the realization writes the
bytes it read, provenance included (§16 ¶2, §20.2 ¶1); propagation of provenance through copies is
not fixed by spec v0.1 at the level of the language (§10 ¶4, §19): open boundary of the spec,
non-blocking (arbitration Q22), not a mismatch. -/
theorem H04 : Sim K1 [] π1 (st1 6) ∧ t1.map opKind = [0, 1] ∧
    t1.map opAlloc = [some (π1.L 1).alloc, some (π1.L 2).alloc] ∧
    (∀ i < 8, bytesOf (run (st1 6).2 t1) π1.L 2 i = bytesOf (st1 6).2 π1.L 1 i) ∧
    (∀ i < 8, bytesOf (run (st1 6).2 t1) π1.L 1 i = bytesOf (st1 6).2 π1.L 1 i) ∧
    initOf (run (st1 6).2 t1) π1.L 1 = some true ∧
    (transferEff (st1 6).1 1 2).I 1 = .moved ∧
    (∀ a, Read3Step a [1] (transferEff (st1 6).1 1 2) .reject) ∧
    Read3Step 1 [1] (st1 6).1 (.ok (st1 6).1) :=
  ⟨sim (KT.ddSound _ _ _) (by decide) (by decide), by decide, by decide, by decide, by decide,
    by decide, by decide,
    fun _ => .reject fun hp => absurd (hp.init 1 (List.mem_singleton_self _)) (by decide),
    .ok (by decide)⟩

/-- **MM23-H08** (material §3, class R). `endUse` of a value whose owned storage is not freed.
Expected (material): no machine step; the allocation stays live (a leak). Obtained: the same.
After eight steps of R1 (reached; the `unpin` of step 8 ended the pinning obligation 0 of the
storage leaf, §75, §69.4), `endUse(w)` is `ok` and realized by no raw operation (§82.5,
§69 effect "does not automatically trigger physical deallocation"); in the kernel the storage 3
is dead and unusable, in the machine its allocation is live, and still live at the end of R1. -/
theorem H08 : Sim K1 [] π1 (st1 8) ∧ Sim K1 [] π1 (st1 10) ∧
    EndUseStep K1 2 (st1 8).1 (.ok (endUseEff (st1 8).1 2)) ∧
    opsOf π1 (.endUse 2) (st1 8).1 (st1 8).2 = [] ∧
    (endUseEff (st1 8).1 2).dead 3 = true ∧ ¬ (endUseEff (st1 8).1 2).Usable 3 ∧
    liveOf (st1 8).2 (π1.L 3).alloc = some true ∧ liveOf (st1 10).2 (π1.L 3).alloc = some true :=
  ⟨sim (KT.ddSound _ _ _) (by decide) (by decide), sim (KT.ddSound _ _ _) (by decide) (by decide),
    .ok (by decide), rfl, by decide, by decide, by decide, by decide⟩

/-- The raw operations realizing the exit of frame 1 in R1 (§82, §73). -/
def x1 : List (Machine.Op Unit) := opsOf π1 .exit (st1 9).1 (st1 9).2

/-- **MM23-H09** (material §3, class R). Frame exit. Expected (material): one deallocation per
automatic allocation, none for the owned storage. Obtained: the same for the realization of the
reference (`exitOps`): after nine steps of R1 (reached), the exit is realized by one `ok`
deallocation of the allocation of each root local 0, 1, 2 of the frame with its recorded token
(§17, §82.5), dead afterwards, and none for the storage 3, live afterwards. **Open boundary of the
spec** (non-blocking, arbitration Q22): spec v0.1 does not require the first half: §9 ¶2 ("storage
with static or automatic duration, whose particular rules will be defined later") and §73
("Exiting does not entail automatic physical deallocation of all dead places") leave the
deallocation of automatic storage at exit undetermined; `exitOps`, which deallocates
`Refinement.exitRoots`, is the reference realization retained by Q22, not a spec v0.1
guarantee. -/
theorem H09 : Sim K1 [] π1 (st1 9) ∧ Sim K1 [] π1 (st1 10) ∧
    x1.map opDealloc = [some ((π1.L 0).alloc, 100), some ((π1.L 1).alloc, 101),
      some ((π1.L 2).alloc, 102)] ∧
    Machine.Exec (· = ·) obR obW x1 (st1 9).2 (run (st1 9).2 x1) ∧
    (∀ r ∈ [0, 1, 2], liveOf (run (st1 9).2 x1) (π1.L r).alloc = some false) ∧
    liveOf (run (st1 9).2 x1) (π1.L 3).alloc = some true :=
  have h := sim (KT.ddSound _ _ _) (by decide) (by decide)
  ⟨h, sim (KT.ddSound _ _ _) (by decide) (by decide), by decide,
    kexec (KT.ddSound _ _ _) (piOf_ok _ _) h.1 (by decide), by decide, by decide⟩

/-- The raw operations realizing the allocation of R1 (§82.4, §71). -/
def a1 : List (Machine.Op Unit) := opsOf π1 (.alloc 0 1 [lf]) (st1 3).1 (st1 3).2

/-! ## Run R7: allocation of zero physical size, failed allocation (H07) -/

/-- Contract of R7 (§48): every request satisfiable. -/
abbrev K7 : K := KT {} false true

/-- Contract of the failed allocation (§48, §71): no request satisfiable. -/
abbrev K7f : K := KT {} false false

/-- Run R7 (§72, §67, §71): frame 1 with the provider 0 and `x` (1), both written; storage 2 (one
leaf) allocated from 0 for `x`. -/
def r7 : List KOp := [.enter [] [lf, lf], .write 0 [0] wv, .write 1 [1] wv, .alloc 0 1 [lf]]

/-- Parameters of R7 (§82): the storage 2 laid out with zero physical size (§71.1, §82.4). -/
def π7 : Params Unit := piOf (kernelRun (S3.init []) r7).P [2]

/-- State of R7 after its first `n` steps (§82). -/
def st7 (n : Nat) : S3 × Machine.State := kfin K7 [] π7 (r7.take n)

/-- State of R7 after its first three steps under the contract `K7f` (§82). -/
def st7f : S3 × Machine.State := kfin K7f [] π7 (r7.take 3)

/-- The raw operations realizing the allocation of R7 (§82.4, §71.1). -/
def a7 : List (Machine.Op Unit) := opsOf π7 (.alloc 0 1 [lf]) (st7 3).1 (st7 3).2

/-- **MM23-H07** (material §3, class R). `alloc` `ok`, `fail`, of zero size. Expected (material):
`AllocStep` / no step / `AllocStep` of size 0. Obtained: the same. `ok` (R1 after three steps,
reached): realized by one raw creation of 8 bytes, an `ok` step (§71, §82.4). Zero size (R7 with
the storage laid out with size zero, reached): one raw creation of size 0, `ok` (§71.1, §9 ¶3,
§82.4), and the run reaches its end. `fail` (R7 after three steps under `K7f`, reached): the
static preconditions hold and `Satisfiable` does not, so the outcome is `fail` (§71 outcomes); no
`ok` step exists, the realization has no raw operation and the memory state stays related by
`Repr` (§58, §82.4). Twin of the `fail`: the same state under `K7`, where the request is
satisfiable, gives the `ok` allocation of size 0. -/
theorem H07 : Sim K1 [] π1 (st1 3) ∧ a1.map opSize = [some 8] ∧
    Machine.Exec (· = ·) obR obW a1 (st1 3).2 (run (st1 3).2 a1) ∧
    Sim K7 [] π7 (st7 3) ∧ Sim K7 [] π7 (st7 4) ∧ a7.map opSize = [some 0] ∧
    Machine.Exec (· = ·) obR obW a7 (st7 3).2 (run (st7 3).2 a7) ∧
    Sim K7f [] π7 st7f ∧ AllocStep K7f 0 1 [lf] st7f.1 .fail ∧
    (∀ s', ¬ OpStep K7f (.alloc 0 1 [lf]) st7f.1 s') ∧
    Machine.Exec (· = ·) obR obW ([] : List (Machine.Op Unit)) st7f.2 st7f.2 ∧
    Refinement.Repr π7.L π7.rtok st7f.1 st7f.2 := by
  have h1 : Sim K1 [] π1 (st1 3) := sim (KT.ddSound _ _ _) (by decide) (by decide)
  have h7 : Sim K7 [] π7 (st7 3) := sim (KT.ddSound _ _ _) (by decide) (by decide)
  have hf : Sim K7f [] π7 st7f := sim (KT.ddSound _ _ _) (by decide) (by decide)
  have hfail : AllocStep K7f 0 1 [lf] st7f.1 .fail := .fail (by decide) (by decide)
  refine ⟨h1, by decide, kexec (KT.ddSound _ _ _) (piOf_ok _ _) h1.1 (by decide), h7,
    sim (KT.ddSound _ _ _) (by decide) (by decide), by decide,
    kexec (KT.ddSound _ _ _) (piOf_ok _ _) h7.1 (by decide), hf, hfail, fun s' h => ?_,
    r6_alloc_fail hf.2.2.1 hfail⟩
  cases (h : AllocStep K7f 0 1 [lf] st7f.1 (.ok s')) with
  | ok _ hs => exact absurd hs (by decide)

/-! ## Run R2: arena, block written, transferred, read, ended, reset (H02, H06, H13) -/

/-- Contract of R2 (§48, §70.2): the storage 4 and the block region leaf 5 deallocable with the
authority 104, so that only the structural clause of `free` can reject. -/
abbrev K2 : K := KT { dealloc := [4, 5], compat := [(4, 104), (5, 104)] } false true

/-- Run R2 (§72, §67, §71, §76, §77, §63, §66, §69, §78): frame 1 with the arena value 0, the
provider 1, the values `v` (2) and `q` (3); storage 4 (leaves 5, 6) owned by 0, its root authority
4 the `internal` of the arena; block 5 on `[5]` issued to `v` (the reference to leaf 5 written
into `v`); leaf 5 written through block 5; `transfer(v, q)`; `read(q)`; `endUse(q)`; `reset`. -/
def l2 : List LOp := [.kernel (.enter [] [lf, lf, lf, lf]), .kernel (.write 1 [1] wv),
  .kernel (.alloc 1 0 [lf, pt 4, pt 4]), .kernel (.write 0 [0] wv), .newArena [] 4 4,
  .issue 0 [5] 2, .kernel (.write 5 [5] wv), .kernel (.transfer 2 3), .kernel (.read 3 [3]),
  .kernel (.endUse 3), .reset 0]

/-- Parameters of R2, fixed once from its final places (§82). -/
def π2 : Params Unit := piOf (placesOf [] l2) []

/-- State of R2 after its first `n` steps (§82.7). -/
def lt2 (n : Nat) : LState × Machine.State := lfin K2 [] π2 (l2.take n)

/-- The arena entry of R2 before the reset (§46): storage 4, `internal` 4, leaf 6 available,
block 5 issued on `[5]`. -/
def E2 : ArenaEntry := ⟨4, 4, [6], [([5], 5)]⟩

/-- The library state after the `reset` of R2 (§78), as computed by the corpus runner. -/
def l2r : LState := next K2 (lt2 10).1 (.reset 0)

/-- **MM23-H02** (material §3, class R). `reset` of an arena, then access through an old block
authority. Expected (material): no safe program reaches it; the memory machine would accept it
(the allocation is live). Obtained: the same. R2 is reached up to the end of `q` and through the
`reset` (`LSim`); the `reset` is `ok` (§78) and its state library-reachable; block 5 is inactive
there and a read through it is rejected (§66.2); along every continuation of the library run, no
kernel step uses block 5 (`reset_no_access`, §82.7, §78, §86; no step reactivates an authority).
In the memory machine the allocation of the storage is live, the range of leaf 5 still holds the
bytes written through block 5, and a raw read of it is `ok`. Twin of the rejected read, the same
run without the end of the block and the `reset`: the read through block 5 is `ok`. The draft
lemma stating that no authority derived from `internal` remains active after `reset` is false
under spec v0.1 (§78 effect: "an empty-footprint derivative may remain active"); the statement used
is restricted to authorities covering a leaf of the storage (§78.2). -/
theorem H02 : LSim K2 [] π2 (lt2 10) ∧ LSim K2 [] π2 (lt2 11) ∧
    (lt2 10).1.arenas[0]? = some E2 ∧ ResetD 0 (lt2 10).1 (.ok l2r) ∧ LReach K2 [] l2r ∧
    ¬ l2r.kern.Active 5 ∧ Read3Step 5 [5] l2r.kern .reject ∧
    (∀ t L₂, LPath K2 l2r t L₂ → ∀ q ∈ ltrace t, usedAuth q.1 ≠ some 5) ∧
    liveOf (lt2 11).2 (π2.L 5).alloc = some true ∧
    (∀ i < 8, bytesOf (lt2 11).2 π2.L 5 i = wv 5 i) ∧
    Machine.ReadStep obR (leafAcc (lt2 11).2 π2.L .read 5) () (lt2 11).2
      (.ok (readVal (lt2 11).2 (leafAcc (lt2 11).2 π2.L .read 5))) ∧
    Read3Step 5 [5] (lt2 9).1.kern (.ok (lt2 9).1.kern) := by
  have h10 : LSim K2 [] π2 (lt2 10) := lsimOf (KT.ddSound _ _ _) (by decide) (by decide)
  have hE : (lt2 10).1.arenas[0]? = some E2 := by decide
  have hr : ResetD 0 (lt2 10).1 (.ok l2r) := oks (k := K2) (o := .reset 0) (by decide)
  exact ⟨h10, lsimOf (KT.ddSound _ _ _) (by decide) (by decide), hE, hr,
    .step h10.2.2.2 (.reset hr), by decide, .reject (by decide),
    fun _ _ hp => reset_no_access hE hr hp (by decide) (by decide), by decide, by decide,
    readStep_of (by decide), .ok (by decide)⟩

/-- **MM23-H06** (material §3, class R). `free` of an arena block. Expected (material):
impossible, not an allocation. Obtained: the same. On R2 after the end of `q` (reached), with the
block region leaf 5 declared deallocable and compatible, `free` of 5 is rejected: 5 is a part of
the storage, not an `OwnedRoot` (§70.1), and its range lies in the allocation of the storage 4
(§9: subplaces returned by an arena are not new allocations). Twin: on the same state, `free` of
the allocated storage 4 is `ok`, realized by one `ok` raw deallocation with the recorded token
(§70, §82.4). -/
theorem H06 : LSim K2 [] π2 (lt2 10) ∧ K2.Deallocable 5 ∧ K2.FreeCompat 5 104 ∧
    ¬ OwnedRoot (lt2 10).1.kern 5 ∧ FreeStep K2 5 104 (lt2 10).1.kern .reject ∧
    (π2.L 5).alloc = (π2.L 4).alloc ∧
    FreeStep K2 4 104 (lt2 10).1.kern (.ok (freeEff (lt2 10).1.kern 4)) ∧
    opsOf π2 (.free 4 104) (lt2 10).1.kern (lt2 10).2 = [.dealloc (π2.L 4).alloc 104] ∧
    Machine.DeallocStep (· = ·) (π2.L 4).alloc 104 (lt2 10).2
      (.ok ((lt2 10).2.dealloc (π2.L 4).alloc)) :=
  ⟨lsimOf (KT.ddSound _ _ _) (by decide) (by decide), by decide, by decide, by decide,
    .reject (by decide), by decide, .ok (by decide), rfl, .ok (by decide)⟩

/-- **MM23-H13** (material §3, class R). A value containing a pointer, transferred then read.
Expected (material): provenance kept. Obtained: the same. On R2 (reached before the transfer,
after it and after the read), the derived `issue` wrote into `v` the reference to leaf 5: it
decodes to the address of leaf 5, every byte with the provenance of the storage allocation
(§82.3); after `transfer(v, q)` the range of `q` holds the same bytes (§63, §16 ¶2); `read(q)` is
`ok` in the kernel, realized by one raw read of the range of `q`, `ok`, which returns the bytes
written into `v`, provenance included, and they decode to the address of leaf 5 (§20.2 ¶1,
§82.2). No rejection, no twin. As in H04, the copy keeps provenance by the choice of the
realization; propagation through copies stays open in spec v0.1 (§10 ¶4, §19): open boundary,
non-blocking (arbitration Q22). -/
theorem H13 : LSim K2 [] π2 (lt2 7) ∧ LSim K2 [] π2 (lt2 8) ∧ LSim K2 [] π2 (lt2 9) ∧
    decodedAt π2 (lt2 7).2 2 = leafAddr (lt2 7).2 π2.L 5 ∧
    (∀ i < 8, (bytesOf (lt2 7).2 π2.L 2 i).2 = some (π2.L 4).alloc) ∧
    (∀ i < 8, bytesOf (lt2 8).2 π2.L 3 i = bytesOf (lt2 7).2 π2.L 2 i) ∧
    Read3Step 3 [3] (lt2 8).1.kern (.ok (lt2 8).1.kern) ∧
    lopsOf π2 (.kernel (.read 3 [3])) (lt2 8).1 (lt2 8).2 =
      [.read (leafAcc (lt2 8).2 π2.L .read 3) ()] ∧
    Machine.ReadStep obR (leafAcc (lt2 8).2 π2.L .read 3) () (lt2 8).2
      (.ok (readVal (lt2 8).2 (leafAcc (lt2 8).2 π2.L .read 3))) ∧
    readVal (lt2 8).2 (leafAcc (lt2 8).2 π2.L .read 3) =
      readVal (lt2 7).2 (leafAcc (lt2 7).2 π2.L .read 2) ∧
    decodedAt π2 (lt2 8).2 3 = leafAddr (lt2 8).2 π2.L 5 :=
  ⟨lsimOf (KT.ddSound _ _ _) (by decide) (by decide),
    lsimOf (KT.ddSound _ _ _) (by decide) (by decide),
    lsimOf (KT.ddSound _ _ _) (by decide) (by decide), by decide, by decide, by decide,
    .ok (by decide), rfl, readStep_of (by decide), by decide, by decide⟩

/-! ## Run R3: statics, read, `writeShared`, free, exit (H05, H10, H11, H12) -/

/-- Contract of R3 (§48): the leaf 3 `SharedMutable`; the storage 4 deallocable with the authority
104. -/
abbrev K3 : K := KT { shared := [3], dealloc := [4], compat := [(4, 104)] } false true

/-- One static leaf, `Init` (§47). -/
def stZ : Statics := [((none, none, 0), true)]

/-- Run R3 (§66, §72, §67, §60, §68, §71, §70, §73): the base frame reads the static 0; frame 1
with the provider 1, `x` (2) and the `SharedMutable` leaf 3, 1 and 2 written; 4, `Observe` on 3,
writes it by `writeShared`; storage 4 allocated from 1 for `x`, then freed with the authority 104;
exit. -/
def r3 : List KOp := [.read 0 [0], .enter [] [lf, lf, lf], .write 1 [1] wv, .write 2 [2] wv,
  .derive 3 [3] .observe, .writeShared 4 [3] wv, .alloc 1 2 [lf], .free 4 104, .exit]

/-- Parameters of R3, fixed once from its final places (§82). -/
def π3 : Params Unit := piOf (kernelRun (S3.init stZ) r3).P []

/-- State of R3 after its first `n` steps (§82). -/
def st3 (n : Nat) : S3 × Machine.State := kfin K3 stZ π3 (r3.take n)

/-- **MM23-H05** (material §3, class R). `free` of an allocated root. Expected (material): one
`DeallocStep`, compatible authority. Obtained: the same. After seven steps of R3 (reached),
`free(4, 104)` is `ok` (§70); it is realized by one raw deallocation of the allocation of 4 with
the authority 104, compatible with the recorded token (`FreeCompatInst`, §17.2, §80, §82.4); the
`DeallocStep` is `ok` and the allocation is dead afterwards (§17). -/
theorem H05 : Sim K3 stZ π3 (st3 7) ∧ Sim K3 stZ π3 (st3 9) ∧
    FreeStep K3 4 104 (st3 7).1 (.ok (freeEff (st3 7).1 4)) ∧
    opsOf π3 (.free 4 104) (st3 7).1 (st3 7).2 = [.dealloc (π3.L 4).alloc 104] ∧
    FreeCompatInst (· = ·) π3.rtok 4 104 ∧
    ((st3 7).2.allocs (π3.L 4).alloc).map (·.freeAuth) = some (some 104) ∧
    Machine.DeallocStep (· = ·) (π3.L 4).alloc 104 (st3 7).2
      (.ok ((st3 7).2.dealloc (π3.L 4).alloc)) ∧
    liveOf ((st3 7).2.dealloc (π3.L 4).alloc) (π3.L 4).alloc = some false :=
  ⟨sim (KT.ddSound _ _ _) (by decide) (by decide), sim (KT.ddSound _ _ _) (by decide) (by decide),
    .ok (by decide), rfl, by decide, by decide, .ok (by decide), by decide⟩

/-- **MM23-H10** (material §3, class R). Static storage. Expected (material): its allocation is
never deallocated. Obtained: the same: every prefix of R3 is a successful translated run and the
allocation of the static 0 is live after each of them, the frame exit included (§47: the static is
owned by the base frame, which does not exit; §73; §82.6). -/
theorem H10 : Sim K3 stZ π3 (st3 9) ∧ ∀ n ∈ List.range (r3.length + 1),
    (srun K3 (· = ·) obR obW π3 (sinit stZ π3) (r3.take n)).isSome = true ∧
    liveOf (st3 n).2 (π3.L 0).alloc = some true :=
  ⟨sim (KT.ddSound _ _ _) (by decide) (by decide), by decide⟩

/-- **MM23-H11** (material §3, class R). Read of an `Init` leaf. Expected (material): `ReadStep`
`ok`. Obtained: the same. On the initial state of R3 (reached), the read of the static leaf 0 by
the base frame is `ok` (§66); it is realized by one raw read of the range of 0 (§82.2), `ok`
(§15), and the range holds the declared initial bytes (§47, §10 ¶5). -/
theorem H11 : Sim K3 stZ π3 (st3 0) ∧ Read3Step 0 [0] (st3 0).1 (.ok (st3 0).1) ∧
    opsOf π3 (.read 0 [0]) (st3 0).1 (st3 0).2 = [.read (leafAcc (st3 0).2 π3.L .read 0) ()] ∧
    Machine.ReadStep obR (leafAcc (st3 0).2 π3.L .read 0) () (st3 0).2
      (.ok (readVal (st3 0).2 (leafAcc (st3 0).2 π3.L .read 0))) ∧
    (∀ i < 8, bytesOf (st3 0).2 π3.L 0 i = π3.ival 0 i) :=
  ⟨sim (KT.ddSound _ _ _) (by decide) (by decide), .ok (by decide), rfl, readStep_of (by decide),
    by decide⟩

/-- **MM23-H12** (material §3, class R). `writeShared`. Expected (material): an ordinary
`WriteStep`, sequential. Obtained: the same. After five steps of R3 (reached), `writeShared` of
the `SharedMutable` leaf 3 through the `Observe` authority 4 is `ok` (§68); it is realized by one
ordinary raw write of the range of 3 (§82.2), `ok` (§16). Sequential fragment only (§18, §29). -/
theorem H12 : Sim K3 stZ π3 (st3 5) ∧ K3.SharedMutable 3 ∧
    ((st3 5).1.A[4]?).map (·.mode) = some .observe ∧
    WriteSharedStep K3 4 [3] (st3 5).1 (.ok (write3Eff (st3 5).1 [3])) ∧
    opsOf π3 (.writeShared 4 [3] wv) (st3 5).1 (st3 5).2 =
      [.write (leafAcc (st3 5).2 π3.L .write 3) () (wv 3)] ∧
    Machine.WriteStep obW (leafAcc (st3 5).2 π3.L .write 3) () (wv 3) (st3 5).2
      (.ok ((st3 5).2.write (leafAcc (st3 5).2 π3.L .write 3) (wv 3))) :=
  ⟨sim (KT.ddSound _ _ _) (by decide) (by decide), by decide, by decide, .ok (by decide), rfl,
    .ok ⟨by decide, by decide, trivial⟩⟩

/-! ## Run R4: declared disjointness (H01) -/

/-- Contract of R4 (§23, §48): `DeclaredDisjoint` is leaf disjointness. -/
abbrev K4 : K := KT {} true true

/-- Run R4 (§72, §61): frame 1 with the structure 0 of the leaf parts 1 and 2; `split` of its
root into the regions `[1]` and `[2]`. -/
def r4 : List KOp := [.enter [] [lf, pt 0, pt 0], .split 0 [[1], [2]]]

/-- Parameters of R4, fixed once from its final places (§82). -/
def π4 : Params Unit := piOf (kernelRun (S3.init []) r4).P []

/-- State of R4 after its first `n` steps (§82). -/
def st4 (n : Nat) : S3 × Machine.State := kfin K4 [] π4 (r4.take n)

/-- **MM23-H01** (material §3, class R). Declared disjointness of two regions sharing a leaf.
Expected (material): rejected by `DDSound` (instantiation by leaf disjointness); declared regions
have disjoint bytes. Obtained: the same. A contract declaring `[1, 2]` and `[2]` disjoint violates
`DDSound` (§80, §23: the normative condition is leaf disjointness); under the contract of R4
(`DDSound`, leaf instantiation), after the entry of frame 1 (reached), the `split` of the root
into `[1, 2]` and `[2]` is rejected (§61.3). Twin: the `split` into `[1]` and `[2]`, declared
disjoint, is `ok` and the run is translated with `Repr`; in its memory state, under `LayoutWF`,
every two declared regions of existing leaves have disjoint bytes (§23, §82.1), `[1]` and `[2]`
among them. -/
theorem H01 : (∀ k : K, k.DeclaredDisjoint [1, 2] [2] → ¬ DDSound k) ∧ DDSound K4 ∧
    ¬ K4.DeclaredDisjoint [1, 2] [2] ∧ Sim K4 [] π4 (st4 1) ∧
    SplitStep K4 0 [[1, 2], [2]] (st4 1).1 .reject ∧ K4.DeclaredDisjoint [1] [2] ∧
    Sim K4 [] π4 (st4 2) ∧
    (∀ r r', K4.DeclaredDisjoint r r' → (∀ l ∈ r, l < (st4 2).1.P.length ∧ isLeaf (st4 2).1.P l) →
      (∀ l ∈ r', l < (st4 2).1.P.length ∧ isLeaf (st4 2).1.P l) → ByteDisjoint π4.L r r') ∧
    ByteDisjoint π4.L [1] [2] := by
  have h2 : Sim K4 [] π4 (st4 2) := sim (KT.ddSound _ _ _) (by decide) (by decide)
  have hb : ∀ r r', K4.DeclaredDisjoint r r' →
      (∀ l ∈ r, l < (st4 2).1.P.length ∧ isLeaf (st4 2).1.P l) →
      (∀ l ∈ r', l < (st4 2).1.P.length ∧ isLeaf (st4 2).1.P l) → ByteDisjoint π4.L r r' :=
    fun _ _ hd hr hr' => declaredDisjoint_bytes (KT.ddSound _ _ _) h2.2.2.1.layout hd hr hr'
  exact ⟨fun k hd hs => hs _ _ hd 2 (by decide) (by decide), KT.ddSound _ _ _, by decide,
    sim (KT.ddSound _ _ _) (by decide) (by decide), .reject (by decide), by decide, h2, hb,
    hb _ _ (by decide) (by decide) (by decide)⟩

/-! ## Run R5: references to empty regions (H15) -/

/-- Contract of R5 and R6 (§48): nothing declared. -/
abbrev K5 : K := KT {} false true

/-- Run R5 (§72, §67, §71, §76, §77, §61, §65): frame 1 with the arena value 0, the provider 1,
the leaves 2, 3, 4; storage 5 (leaf 6) owned by 0, its root authority 5 the `internal` of the
arena; the derived `issue` of the empty region to 2 (block 6: `split` of 5 into `[[]]`, then
`store` into 2); `split` of the root of 3 into `[[]]` (authority 7), then `store` of 7 into 4. -/
def l5 : List LOp := [.kernel (.enter [] [lf, lf, lf, lf, lf]), .kernel (.write 1 [1] wv),
  .kernel (.alloc 1 0 [lf, pt 5]), .kernel (.write 0 [0] wv), .newArena [] 5 5, .issue 0 [] 2,
  .kernel (.split 3 [[]]), .kernel (.store 7 4)]

/-- Parameters of R5, fixed once from its final places (§82). -/
def π5 : Params Unit := piOf (placesOf [] l5) []

/-- State of R5 after its first `n` steps (§82.7). -/
def lt5 (n : Nat) : LState × Machine.State := lfin K5 [] π5 (l5.take n)

/-- **MM23-H15** (material §3, class R). Reference to an empty region, by `issue []` and by
`split` into `[]` then `store`. Expected (material): address the base of the allocation of the
effective anchor; provenance that allocation. Obtained: the same; the case passes. R5 is reached
(`LSim`), the issue being the derived library operation: its raw operations are one write, of the
destination 2 (`split` realizes none, §77, §82.7). Block 6 has the empty region, effective anchor
5 (the root of the storage), recorded in the arena entry; the range of 2 decodes to the base of
the allocation of 5, nonzero, every byte with that allocation as provenance. Authority 7 has the
empty region, effective anchor 3; the range of 4 decodes to the base of the allocation of 3,
nonzero, with that provenance. Both destinations have the size of a reference (8 bytes). Source of
the expected verdict: v0.1 §82.2, last sentence (a region whose leaves all have zero physical
size, the empty region included). Under v0 the same verdict rested on a decision of the brief
recorded for §82.3; v0.1 gives it a spec source without changing it. -/
theorem H15 : LSim K5 [] π5 (lt5 5) ∧ LSim K5 [] π5 (lt5 8) ∧
    (lopsOf π5 (.issue 0 [] 2) (lt5 5).1 (lt5 5).2).map opKind = [1] ∧
    (lopsOf π5 (.issue 0 [] 2) (lt5 5).1 (lt5 5).2).map opAlloc = [some (π5.L 2).alloc] ∧
    (lt5 8).1.arenas = [⟨5, 5, [6], [([], 6)]⟩] ∧
    (lt5 8).1.kern.afp 6 = [] ∧ (lt5 8).1.kern.effAnchor 6 = 5 ∧
    anchorAlloc π5.L (lt5 8).1.kern 6 = (π5.L 5).alloc ∧
    decodedAt π5 (lt5 8).2 2 = baseOf (lt5 8).2 (π5.L 5).alloc ∧
    (∀ i < 8, (bytesOf (lt5 8).2 π5.L 2 i).2 = some (π5.L 5).alloc) ∧
    baseOf (lt5 8).2 (π5.L 5).alloc ≠ 0 ∧
    (lt5 8).1.kern.afp 7 = [] ∧ (lt5 8).1.kern.effAnchor 7 = 3 ∧
    anchorAlloc π5.L (lt5 8).1.kern 7 = (π5.L 3).alloc ∧
    decodedAt π5 (lt5 8).2 4 = baseOf (lt5 8).2 (π5.L 3).alloc ∧
    (∀ i < 8, (bytesOf (lt5 8).2 π5.L 4 i).2 = some (π5.L 3).alloc) ∧
    baseOf (lt5 8).2 (π5.L 3).alloc ≠ 0 ∧ (π5.L 2).len = 8 ∧ (π5.L 4).len = 8 :=
  ⟨lsimOf (KT.ddSound _ _ _) (by decide) (by decide),
    lsimOf (KT.ddSound _ _ _) (by decide) (by decide), by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide⟩

/-! ## Run R6: a region whose head is not its lowest leaf (H16) -/

/-- Run R6 (§72, §67, §71, §76, §77): frame 1 with the arena value 0, the provider 1, the leaf 2;
storage 3 (leaves 4 at offset 0 and 5 at offset 8) owned by 0, its root authority 3 the `internal`
of the arena; the derived `issue` of the region `[5, 4]` to 2 (block 4). -/
def l6 : List LOp := [.kernel (.enter [] [lf, lf, lf]), .kernel (.write 1 [1] wv),
  .kernel (.alloc 1 0 [lf, pt 3, pt 3]), .kernel (.write 0 [0] wv), .newArena [] 3 3,
  .issue 0 [5, 4] 2]

/-- Parameters of R6, fixed once from its final places (§82). -/
def π6 : Params Unit := piOf (placesOf [] l6) []

/-- State of R6 after its first `n` steps (§82.7). -/
def lt6 (n : Nat) : LState × Machine.State := lfin K5 [] π6 (l6.take n)

/-- **MM23-H16** (material §3, class R). Reference to a region whose first listed leaf does not
have the lowest offset. Expected (material): the lowest address among the nonempty leaves.
Obtained: the same; the case passes. R6 is reached (`LSim`), the issue being the derived library
operation, realized by one write of the destination 2. Block 4 has the region `[5, 4]`, recorded
in the arena entry; both leaves have nonzero size, leaf 4 at offset 0 below the head 5 at offset
8; the range of 2 decodes to the address of leaf 4, not to that of the head, every byte with the
storage allocation as provenance. Source of the expected verdict: a decision of the user's brief
recorded for §82.3 (lowest-address rule), not stated by spec v0.1: §82.2 decides only regions
whose leaves all have zero physical size, and §81 leaves encodings to Spec 11. -/
theorem H16 : LSim K5 [] π6 (lt6 5) ∧ LSim K5 [] π6 (lt6 6) ∧
    (lopsOf π6 (.issue 0 [5, 4] 2) (lt6 5).1 (lt6 5).2).map opKind = [1] ∧
    (lopsOf π6 (.issue 0 [5, 4] 2) (lt6 5).1 (lt6 5).2).map opAlloc = [some (π6.L 2).alloc] ∧
    (lt6 6).1.arenas = [⟨3, 3, [], [([5, 4], 4)]⟩] ∧ (lt6 6).1.kern.afp 4 = [5, 4] ∧
    (π6.L 4).off = 0 ∧ (π6.L 5).off = 8 ∧ 0 < (π6.L 4).len ∧ 0 < (π6.L 5).len ∧
    leafAddr (lt6 6).2 π6.L 4 < leafAddr (lt6 6).2 π6.L 5 ∧
    decodedAt π6 (lt6 6).2 2 = leafAddr (lt6 6).2 π6.L 4 ∧
    decodedAt π6 (lt6 6).2 2 ≠ leafAddr (lt6 6).2 π6.L 5 ∧
    (∀ i < 8, (bytesOf (lt6 6).2 π6.L 2 i).2 = some (π6.L 3).alloc) ∧ (π6.L 2).len = 8 :=
  ⟨lsimOf (KT.ddSound _ _ _) (by decide) (by decide),
    lsimOf (KT.ddSound _ _ _) (by decide) (by decide), by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide⟩

end Ern.Corpus.MM23H
