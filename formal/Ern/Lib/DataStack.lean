import Ern.MemoryModel.Arena
import Ern.MemoryModel.Refinement

/-!
# DataStack: a library administrative abstraction (contract DS-v1, non-normative)

A `DataStack` instance of `specs/ERN_Memory_Model_Specification_v0.md`. The spec does not define
its contract (Part XIV preamble: "The contracts of `HandlePool` and `DataStack` belong to their
library abstractions and are not defined here"). The contract formalized here is the library
contract **DS-v1**, which is **not normative**: every definition below that encodes a DS-v1 item
says so. The normative clauses that constrain it are §36 (`MetaRight` requires `Modify` exercisable
on the stack value; the abstraction adds no rights to the kernel), §38 and §46 (library state
separate from `S₃`), §47 (empty initial registry), §56 (guard over all registries of live
administrations) and §58 (outcomes).

DS-v1: marks carry the stack identity and a fresh mark identifier; the stack keeps the ordered list
of live marks; `rewind m` fails on a dead or foreign mark, rejects if an active authority derived
from `internal` covers a cell above `m`, otherwise returns those cells to available and removes `m`
and every mark above it; `push` and `grow` use the derived `issue` of Part XIV (`Arena.IssueD`: its
static checks, the availability `fail`, then `split` of `internal` and `store` of the block); `grow`
is in place only (same base, extension into the space directly after the block, `fail` otherwise).

Every `ok` step of the library is a sequence of kernel steps O1–O16 (`DReach.reachable`), so the
abstraction adds no rights to the kernel (§36).
-/

namespace Ern.Lib.DataStack

open Ern.MemoryModel Ern.MemoryModel.Access Ern.MemoryModel.Arena

/-! ## Library state (DS-v1; §38, §46, §47) -/

/-- A block issued by a stack (DS-v1, non-normative; recorded like the issuances of §46): position
`base` of its first cell and number `size` of cells among the ordered cells of the stack, block
authority `auth`, destination `dst` that received it. -/
structure Blk where
  base : Nat
  size : Nat
  auth : Nat
  dst : Nat
deriving DecidableEq, Repr

/-- A mark (DS-v1, non-normative: "marks carry stack identity and a fresh mark identifier";
library metadata of an administrative abstraction, §36, §38): the identity of its stack, its fresh
identifier, the top of the stack when it was taken. -/
structure Mark where
  stack : Nat
  id : Nat
  top : Nat
deriving DecidableEq, Repr

/-- A stack (DS-v1, non-normative; library state, §38, §46): administered storage, `internal`
authority held by the stack value (§36), ordered cells (the leaves of the storage at creation),
top (the cells at positions `≥ top` are available), issued blocks (oldest first), and the ordered
list of live marks (DS-v1: "the stack keeps the ordered list of live marks"). -/
structure Stack where
  storage : Nat
  internal : Nat
  cells : List Nat
  top : Nat
  blocks : List Blk
  marks : List Mark
deriving DecidableEq, Repr

/-- State of the stack library (DS-v1, non-normative; §38: administrative states of library
abstractions are separate from `S₃`): the kernel state, the stack registry (a stack is identified
by its index; stacks are never removed) and the next fresh mark identifier. -/
structure DState where
  kern : S3
  stacks : List Stack
  fresh : Nat

/-- Initial state (§47: the kernel's initial state; the library registry starts empty; DS-v1,
non-normative: no mark identifier given out). -/
def DState.init (statics : Statics) : DState := ⟨S3.init statics, [], 0⟩

/-- The `n` cells from position `b` of the stack, leaves of the administered storage (§46; DS-v1,
non-normative). -/
def cellsOf (st : Stack) (b n : Nat) : List Nat := (st.cells.drop b).take n

/-- The cells above mark `m` (DS-v1, non-normative, "a cell above m"; reading recorded; §46
available leaves): the positions from the top of `m` to the current top, those that `rewind m`
returns to available. -/
def above (st : Stack) (m : Mark) : List Nat := cellsOf st m.top (st.top - m.top)

/-- The stack seen as an administration entry (§46, §36; DS-v1, non-normative): storage,
`internal`, available cells (positions `≥ top`) and issued blocks. Used for `MetaRight` and the
static checks of the derived `issue`, which read only the storage and `internal`. -/
def Stack.entry (st : Stack) : ArenaEntry :=
  ⟨st.storage, st.internal, st.cells.drop st.top,
    st.blocks.map fun x => (cellsOf st x.base x.size, x.auth)⟩

/-- The block of the stack whose authority is `b` (§46 issuances; DS-v1, non-normative). -/
def Stack.block (st : Stack) (b : Nat) : Option Blk := st.blocks.find? fun y => decide (y.auth = b)

/-- A live mark of stack `j` (DS-v1, non-normative: a mark that is neither dead nor foreign; it
decides the `fail` case of `rewind`, §58): it names stack `j` and belongs to its list of live
marks. -/
def LiveMark (j : Nat) (st : Stack) (m : Mark) : Prop := m.stack = j ∧ m ∈ st.marks

/-- Decidability of `LiveMark` (§58; DS-v1). -/
instance (j : Nat) (st : Stack) (m : Mark) : Decidable (LiveMark j st m) := by
  unfold LiveMark; infer_instance

/-- The administrative right of §36 for a stack (DS-v1, non-normative, with §36 and §46 read for a
stack): the stack is live (`internal` is active) and `MetaRight`, `Modify` exercisable on the stack
value, the place holding `internal`. -/
def AdminRight (s : S3) (st : Stack) : Prop := s.Active st.internal ∧ MetaRight s st.entry

/-- Decidability of `AdminRight` (§36; DS-v1). -/
instance (s : S3) (st : Stack) : Decidable (AdminRight s st) := by
  unfold AdminRight; infer_instance

/-! ## `newStack` and the guard of §56 -/

/-- The stack registry as a registry of live administrations (§56; DS-v1, non-normative): the
`internal` identities of its live stacks. -/
def stackInternals (s : S3) (stacks : List Stack) : List Nat :=
  (stacks.filter fun st => decide (s.Active st.internal)).map (·.internal)

/-- Preconditions of `newStack(storage, internal)` (DS-v1, non-normative; §56): those of `newArena`
other than its guard (`NewArenaBase`, §76.1–§76.3 and §76.5 read for a stack), and the guard of §56
over the stack registry and every other registry of live administrations `others`. -/
structure NewStackPre (s : S3) (stacks : List Stack) (others : List (List Nat))
    (storage internal : Nat) : Prop where
  /-- §76.1–§76.3, §76.5, read for a stack (DS-v1). -/
  base : NewArenaBase s storage internal
  /-- §56: no live administration of any registry uses `internal`. -/
  guard : Guard56 (stackInternals s stacks :: others) internal

/-- Decidability of `NewStackPre` (§56; DS-v1). -/
instance (s : S3) (stacks : List Stack) (others : List (List Nat)) (storage internal : Nat) :
    Decidable (NewStackPre s stacks others storage internal) :=
  decidable_of_iff (NewArenaBase s storage internal ∧
    Guard56 (stackInternals s stacks :: others) internal)
    ⟨fun ⟨a, b⟩ => ⟨a, b⟩, fun ⟨a, b⟩ => ⟨a, b⟩⟩

/-- Effect of `newStack` (DS-v1, non-normative; §36: registration adds no rights): a stack whose
cells are the leaves of the storage, top 0, no block, no mark; the kernel state is unchanged. -/
def newStackEff (D : DState) (storage internal : Nat) : DState :=
  { D with stacks := D.stacks ++ [⟨storage, internal, footprint D.kern.P storage, 0, [], []⟩] }

/-- `newStack` as a relation (DS-v1, non-normative; §56, §58): `ok` or `reject`. -/
def NewStackStep (others : List (List Nat)) (storage internal : Nat) (D : DState) :
    Outcome3 DState → Prop :=
  Guarded (NewStackPre D.kern D.stacks others storage internal) (newStackEff D storage internal)

/-! ## `push` (DS-v1: the derived `issue`, Part XIV, §77) -/

/-- Metadata after `push` (DS-v1, non-normative; as the `ok` effect of §77 on §46 metadata): the
cells leave the available part (the top rises by `size`), the block is recorded. -/
def pushMeta (st : Stack) (size a dst : Nat) : Stack :=
  { st with top := st.top + size, blocks := st.blocks ++ [⟨st.top, size, a, dst⟩] }

/-- `push(j, size, dst)` (DS-v1, non-normative: "push uses the derived issue"): the derived `issue`
of Part XIV (`Arena.IssueD`) of the `size` cells at the top into `dst`, on the stack seen as an
entry: its static checks (`IssueStatic`, §77.1, §77.2, with `MetaRight` of §36), then `fail`, the
state unchanged, when fewer than `size` cells are left (availability, §77.4; reading recorded),
then `split` of `internal` on the cells (O2) and `store` of the block, of fresh identity `|A|`, into
`dst` (O8). -/
inductive PushStep (k : K) (j size dst : Nat) (D : DState) : Outcome3 DState → Prop where
  | noStack : D.stacks[j]? = none → PushStep k j size dst D .reject
  | static {st : Stack} : D.stacks[j]? = some st →
      ¬ IssueStatic D.kern st.entry (cellsOf st st.top size) dst → PushStep k j size dst D .reject
  | fail {st : Stack} : D.stacks[j]? = some st →
      IssueStatic D.kern st.entry (cellsOf st st.top size) dst →
      ¬ st.top + size ≤ st.cells.length → PushStep k j size dst D .fail
  | split {st : Stack} : D.stacks[j]? = some st →
      IssueStatic D.kern st.entry (cellsOf st st.top size) dst →
      st.top + size ≤ st.cells.length →
      SplitStep k st.internal [cellsOf st st.top size] D.kern .reject →
      PushStep k j size dst D .reject
  | store {st : Stack} {s₁ : S3} : D.stacks[j]? = some st →
      IssueStatic D.kern st.entry (cellsOf st st.top size) dst →
      st.top + size ≤ st.cells.length →
      SplitStep k st.internal [cellsOf st st.top size] D.kern (.ok s₁) →
      StoreStep D.kern.A.length dst s₁ .reject → PushStep k j size dst D .reject
  | ok {st : Stack} {s₁ s₂ : S3} : D.stacks[j]? = some st →
      IssueStatic D.kern st.entry (cellsOf st st.top size) dst →
      st.top + size ≤ st.cells.length →
      SplitStep k st.internal [cellsOf st st.top size] D.kern (.ok s₁) →
      StoreStep D.kern.A.length dst s₁ (.ok s₂) →
      PushStep k j size dst D
        (.ok ⟨s₂, D.stacks.set j (pushMeta st size D.kern.A.length dst), D.fresh⟩)

/-! ## `mark` (DS-v1) -/

/-- Metadata after `mark` (DS-v1, non-normative; library metadata, §36, §38): a mark naming stack
`j`, with the fresh identifier `fresh` and the current top, is appended to the live marks. -/
def markMeta (j : Nat) (st : Stack) (fresh : Nat) : Stack :=
  { st with marks := st.marks ++ [⟨j, fresh, st.top⟩] }

/-- `mark(j)` (DS-v1, non-normative; §58 outcomes; §36: metadata only, no right created): `ok`
on an existing stack; the identifier is fresh. -/
inductive MarkStep (j : Nat) (D : DState) : Outcome3 DState → Prop where
  | noStack : D.stacks[j]? = none → MarkStep j D .reject
  | ok {st : Stack} : D.stacks[j]? = some st →
      MarkStep j D (.ok ⟨D.kern, D.stacks.set j (markMeta j st D.fresh), D.fresh + 1⟩)

/-! ## `rewind` (DS-v1) -/

/-- Metadata after `rewind m` (DS-v1, non-normative; as the `ok` effect of §78 on §46 metadata):
the cells above `m` return to available (the top returns to the top of `m`), the blocks from that
top are forgotten, `m` and every later mark are removed. -/
def rewindMeta (st : Stack) (m : Mark) : Stack :=
  { st with
    top := m.top
    blocks := st.blocks.filter fun x => decide (x.base < m.top)
    marks := st.marks.takeWhile fun x => decide (x ≠ m) }

/-- `rewind(j, m)` (DS-v1, non-normative): `fail`, the state unchanged, on a dead or foreign mark;
`reject` without the administrative right of §36; then the derived `reset` of Part XIV on the cells
above `m` (reading recorded): `split` of `internal` on them (O2), which rejects when an active
authority derived from `internal` covers one of them (`rewind_rejects_live_above`), and `release`
of the derived authority (O3); `ok`: the cells return to available, `m` and the later marks are
removed. -/
inductive RewindStep (k : K) (j : Nat) (m : Mark) (D : DState) : Outcome3 DState → Prop where
  | noStack : D.stacks[j]? = none → RewindStep k j m D .reject
  | dead {st : Stack} : D.stacks[j]? = some st → ¬ LiveMark j st m → RewindStep k j m D .fail
  | static {st : Stack} : D.stacks[j]? = some st → LiveMark j st m → ¬ AdminRight D.kern st →
      RewindStep k j m D .reject
  | split {st : Stack} : D.stacks[j]? = some st → LiveMark j st m → AdminRight D.kern st →
      SplitStep k st.internal [above st m] D.kern .reject → RewindStep k j m D .reject
  | release {st : Stack} {s₁ : S3} : D.stacks[j]? = some st → LiveMark j st m →
      AdminRight D.kern st → SplitStep k st.internal [above st m] D.kern (.ok s₁) →
      ReleaseStep D.kern.A.length s₁ .reject → RewindStep k j m D .reject
  | ok {st : Stack} {s₁ s₂ : S3} : D.stacks[j]? = some st → LiveMark j st m →
      AdminRight D.kern st → SplitStep k st.internal [above st m] D.kern (.ok s₁) →
      ReleaseStep D.kern.A.length s₁ (.ok s₂) →
      RewindStep k j m D (.ok ⟨s₂, D.stacks.set j (rewindMeta st m), D.fresh⟩)

/-! ## `grow` (DS-v1: in place, the derived `issue`) -/

/-- In-place extension (DS-v1, non-normative: "extension into the space directly after the
block"; the availability check of the derived `issue`, §77.4): the block ends at the top, and
`extra` available cells follow it. -/
def InPlace (st : Stack) (x : Blk) (extra : Nat) : Prop :=
  x.base + x.size = st.top ∧ st.top + extra ≤ st.cells.length

/-- Decidability of `InPlace` (§77.4; DS-v1). -/
instance (st : Stack) (x : Blk) (extra : Nat) : Decidable (InPlace st x extra) := by
  unfold InPlace; infer_instance

/-- The grown block (DS-v1, non-normative: same base, `extra` more cells, new authority `a`, same
destination; an issuance of §46). -/
def growBlk (x : Blk) (extra a : Nat) : Blk := ⟨x.base, x.size + extra, a, x.dst⟩

/-- Metadata after `grow` (DS-v1, non-normative; as the `ok` effect of §77 on §46 metadata): the
top rises by `extra`; the block is replaced by the grown block. -/
def growMeta (st : Stack) (x : Blk) (extra a : Nat) : Stack :=
  { st with
    top := st.top + extra
    blocks := st.blocks.map fun y => if y.auth = x.auth then growBlk x extra a else y }

/-- `grow(j, b, extra)` (DS-v1, non-normative: in place only, using the derived `issue`): `reject`
when `b` is not a block of the stack or `extra` is zero (reading recorded); `release` of `b` (O3);
then the derived `issue` of Part XIV (`Arena.IssueD`) of the region of the same base and of size
`size + extra` into the recorded destination, on the released state: its static checks
(`IssueStatic`, §77.1, §77.2), `fail`, the state unchanged, unless the extension is in place
(DS-v1 "fail otherwise", availability §77.4), `split` of `internal` (O2) and `store` of the new
block (O8). -/
inductive GrowStep (k : K) (j b extra : Nat) (D : DState) : Outcome3 DState → Prop where
  | noStack : D.stacks[j]? = none → GrowStep k j b extra D .reject
  | noBlock {st : Stack} : D.stacks[j]? = some st → st.block b = none →
      GrowStep k j b extra D .reject
  | noExtra {st : Stack} {x : Blk} : D.stacks[j]? = some st → st.block b = some x → extra = 0 →
      GrowStep k j b extra D .reject
  | release {st : Stack} {x : Blk} : D.stacks[j]? = some st → st.block b = some x → 0 < extra →
      ReleaseStep b D.kern .reject → GrowStep k j b extra D .reject
  | static {st : Stack} {x : Blk} {s₁ : S3} : D.stacks[j]? = some st → st.block b = some x →
      0 < extra → ReleaseStep b D.kern (.ok s₁) →
      ¬ IssueStatic s₁ st.entry (cellsOf st x.base (x.size + extra)) x.dst →
      GrowStep k j b extra D .reject
  | fail {st : Stack} {x : Blk} {s₁ : S3} : D.stacks[j]? = some st → st.block b = some x →
      0 < extra → ReleaseStep b D.kern (.ok s₁) →
      IssueStatic s₁ st.entry (cellsOf st x.base (x.size + extra)) x.dst →
      ¬ InPlace st x extra → GrowStep k j b extra D .fail
  | split {st : Stack} {x : Blk} {s₁ : S3} : D.stacks[j]? = some st → st.block b = some x →
      0 < extra → ReleaseStep b D.kern (.ok s₁) →
      IssueStatic s₁ st.entry (cellsOf st x.base (x.size + extra)) x.dst → InPlace st x extra →
      SplitStep k st.internal [cellsOf st x.base (x.size + extra)] s₁ .reject →
      GrowStep k j b extra D .reject
  | store {st : Stack} {x : Blk} {s₁ s₂ : S3} : D.stacks[j]? = some st → st.block b = some x →
      0 < extra → ReleaseStep b D.kern (.ok s₁) →
      IssueStatic s₁ st.entry (cellsOf st x.base (x.size + extra)) x.dst → InPlace st x extra →
      SplitStep k st.internal [cellsOf st x.base (x.size + extra)] s₁ (.ok s₂) →
      StoreStep s₁.A.length x.dst s₂ .reject → GrowStep k j b extra D .reject
  | ok {st : Stack} {x : Blk} {s₁ s₂ s₃ : S3} : D.stacks[j]? = some st → st.block b = some x →
      0 < extra → ReleaseStep b D.kern (.ok s₁) →
      IssueStatic s₁ st.entry (cellsOf st x.base (x.size + extra)) x.dst → InPlace st x extra →
      SplitStep k st.internal [cellsOf st x.base (x.size + extra)] s₁ (.ok s₂) →
      StoreStep s₁.A.length x.dst s₂ (.ok s₃) →
      GrowStep k j b extra D (.ok ⟨s₃, D.stacks.set j (growMeta st x extra s₁.A.length), D.fresh⟩)

/-! ## Library runs (DS-v1; §36, §56, §57) -/

/-- One `ok` step of the stack library (DS-v1, non-normative): a kernel step O1–O16 of
non-administrative code, the registry unchanged; `newStack` with the guard of §56 against the other
registries `others`; `push`, `mark`, `rewind`, `grow`. -/
inductive DStep (k : K) : DState → DState → Prop where
  | kernel {D : DState} {s' : S3} : KStep k D.kern s' → DStep k D ⟨s', D.stacks, D.fresh⟩
  | newStack {D D' : DState} {others : List (List Nat)} {storage i : Nat} :
      NewStackStep others storage i D (.ok D') → DStep k D D'
  | push {D D' : DState} {j size dst : Nat} : PushStep k j size dst D (.ok D') → DStep k D D'
  | mark {D D' : DState} {j : Nat} : MarkStep j D (.ok D') → DStep k D D'
  | rewind {D D' : DState} {j : Nat} {m : Mark} : RewindStep k j m D (.ok D') → DStep k D D'
  | grow {D D' : DState} {j b extra : Nat} : GrowStep k j b extra D (.ok D') → DStep k D D'

/-- States reachable from the initial state by library steps (DS-v1, non-normative; §47). -/
inductive DReach (k : K) (statics : Statics) : DState → Prop where
  | init : DReach k statics (DState.init statics)
  | step {D D' : DState} : DReach k statics D → DStep k D D' → DReach k statics D'

/-- Finite sequences of library steps (DS-v1, non-normative; §58 `ok` transitions). -/
inductive DRun (k : K) : DState → DState → Prop where
  | refl (D : DState) : DRun k D D
  | tail {D D' D'' : DState} : DRun k D D' → DStep k D' D'' → DRun k D D''

/-- The kernel part of a library step is reached by kernel steps (§36: the abstraction adds no
rights to the kernel; Part XIV: `issue` is `split` then `store`, the reset part of `rewind` is
`split` then `release`; DS-v1). -/
theorem DStep.reachable {k : K} {statics : Statics} {D D' : DState}
    (hr : Reachable k statics D.kern) (h : DStep k D D') : Reachable k statics D'.kern := by
  cases h with
  | kernel hk => exact .step hr hk
  | newStack hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact hr
  | push hs =>
    cases hs with
    | ok _ _ _ hsp hst => exact .step (.step hr (.split hsp)) (.store hst)
  | mark hs => cases hs with | ok _ => exact hr
  | rewind hs =>
    cases hs with
    | ok _ _ _ hsp hrl => exact .step (.step hr (.split hsp)) (.release hrl)
  | grow hs =>
    cases hs with
    | ok _ _ _ hrl _ _ hsp hst =>
      exact .step (.step (.step hr (.release hrl)) (.split hsp)) (.store hst)

/-- The kernel state of every library-reachable state is kernel-reachable (§36, §57; DS-v1). -/
theorem DReach.reachable {k : K} {statics : Statics} {D : DState} (h : DReach k statics D) :
    Reachable k statics D.kern := by
  induction h with
  | init => exact .init
  | step _ hs ih => exact hs.reachable ih

/-! ## Helper lemmas (lists, kernel effects) -/

/-- Reading a list after `set` (support for the §46 metadata updates of DS-v1). -/
theorem getElem?_set_cases {α : Type} {l : List α} {j i : Nat} {v x : α}
    (h : (l.set j v)[i]? = some x) : (i = j ∧ x = v) ∨ (i ≠ j ∧ l[i]? = some x) := by
  rw [List.getElem?_set] at h
  by_cases hij : j = i
  · subst hij; simp only [↓reduceIte] at h; split at h
    · cases h; exact .inl ⟨rfl, rfl⟩
    · cases h
  · simp only [hij, ↓reduceIte] at h; exact .inr ⟨Ne.symm hij, h⟩

/-- Reading a list after appending one element (support for the §46 metadata updates of
DS-v1). -/
theorem getElem?_append_single {α : Type} {l : List α} {x y : α} {i : Nat}
    (h : (l ++ [x])[i]? = some y) : l[i]? = some y ∨ y = x := by
  rw [List.getElem?_append] at h
  split at h
  · exact .inl h
  · cases hc : i - l.length with
    | zero => rw [hc] at h; simp at h; exact .inr h.symm
    | succ n => rw [hc] at h; simp at h

/-- `takeWhile (· ≠ m)` stops at the first occurrence of `m` (support for the §46 metadata of
DS-v1 `rewind`). -/
theorem takeWhile_ne_append {m : Mark} : ∀ {pre : List Mark} (post : List Mark), m ∉ pre →
    (pre ++ m :: post).takeWhile (fun x => decide (x ≠ m)) = pre
  | [], post, _ => by simp
  | a :: pre, post, h => by
    have ha : a ≠ m := fun e => h (e ▸ List.mem_cons_self ..)
    have ih := takeWhile_ne_append (pre := pre) post (fun h' => h (List.mem_cons_of_mem _ h'))
    rw [List.cons_append, List.takeWhile_cons]
    simp only [ha, ne_eq, not_false_eq_true, decide_true, ↓reduceIte, ih]

/-- A prefix of `take` (support for DS-v1 `grow`, §46 metadata: the old cells are a prefix of the
new ones). -/
theorem take_prefix_take_add {α : Type} : ∀ (l : List α) (n e : Nat), l.take n <+: l.take (n + e)
  | [], n, e => ⟨[], by rw [List.take_nil, List.take_nil]; rfl⟩
  | _ :: _, 0, _ => ⟨_, List.nil_append _⟩
  | a :: l, n + 1, e => by
    obtain ⟨t, ht⟩ := take_prefix_take_add l n e
    exact ⟨t, by rw [Nat.add_right_comm, List.take_succ_cons, List.take_succ_cons,
      List.cons_append, ht]⟩

/-- The cells of a block are a prefix of the cells of the block grown from the same base (DS-v1,
non-normative, "same base"; §46 issued regions). -/
theorem cellsOf_prefix (st : Stack) (b n e : Nat) : cellsOf st b n <+: cellsOf st b (n + e) :=
  take_prefix_take_add _ _ _

/-- `release` keeps the identities of the authorities (§62, `ok` effect; support for DS-v1). -/
theorem releaseEff_len (s : S3) (a : Nat) : (releaseEff s a).A.length = s.A.length := by
  unfold releaseEff; split <;> simp

/-- `release` changes no initialization (§62, `ok` effect; support for DS-v1). -/
theorem releaseEff_I (s : S3) (a : Nat) : (releaseEff s a).I = s.I := by
  unfold releaseEff; split <;> rfl

/-- `release` changes no place (§62, `ok` effect; support for DS-v1). -/
theorem releaseEff_P (s : S3) (a : Nat) : (releaseEff s a).P = s.P := by
  unfold releaseEff; split <;> rfl

/-- The leaf `dst` of a usable place belongs to its own footprint (§40; support for DS-v1). -/
theorem mem_footprint_self {s : S3} {d : Nat} (hu : s.Usable d) (hl : isLeaf s.P d) :
    d ∈ footprint s.P d :=
  mem_footprint.2 ⟨hu.lt, hl, hu.lt, .inl rfl⟩

/-! ## `rewind` (DS-v1) -/

/-- `rewind_rejects_live_above` (DS-v1, non-normative: "rewind m … rejects if an active authority
derived from internal covers a cell above m"): for a live mark `m` of an existing stack, if an
active authority derived from `internal` covers a cell above `m`, `rewind m` has the outcome
`reject` and no other: either the administrative right of §36 fails, or `split` of `internal` on
the cells above `m` is rejected, since `internal` no longer has effective `Modify` on that cell
(§43, §61.1). -/
theorem rewind_rejects_live_above {k : K} {D : DState} {j : Nat} {st : Stack} {m : Mark}
    (hst : D.stacks[j]? = some st) (hm : LiveMark j st m) {x l : Nat} {y : Authority}
    (hy : D.kern.A[x]? = some y) (ya : y.active = true) (hx : st.internal ∈ D.kern.ancs x)
    (hly : l ∈ y.footprint) (hl : l ∈ above st m) :
    RewindStep k j m D .reject ∧ ∀ o, RewindStep k j m D o → o = .reject := by
  have hn : ¬ SplitPre k D.kern st.internal [above st m] := fun h =>
    no_desc_of_modify hy ya hly hx (h.modifyOn _ (List.mem_singleton_self _) l hl)
  refine ⟨?_, fun o ho => ?_⟩
  · by_cases ha : AdminRight D.kern st
    · exact .split hst hm ha (.reject hn)
    · exact .static hst hm ha
  · cases ho with
    | noStack => rfl
    | dead h hd => rw [hst] at h; cases h; exact absurd hm hd
    | static => rfl
    | split => rfl
    | release => rfl
    | ok h _ _ hsp =>
      rw [hst] at h; cases h
      exact absurd (Guarded.ok_iff.1 hsp).1 hn

/-- `rewind_keeps_older_marks` (DS-v1, non-normative: "otherwise returns those cells to available
and removes m and every mark above it"; §46 metadata, §62 `ok` effect): after an `ok` of
`rewind m`, the marks of the stack are exactly those older than `m`, its top is the top of `m`
(the cells above `m` are available again), the other stacks are unchanged, and no initialization
changes. -/
theorem rewind_keeps_older_marks {k : K} {D D' : DState} {j : Nat} {m : Mark}
    (h : RewindStep k j m D (.ok D')) {st : Stack} (hst : D.stacks[j]? = some st)
    {pre post : List Mark} (hs : st.marks = pre ++ m :: post) (hpre : m ∉ pre) :
    (∃ st', D'.stacks[j]? = some st' ∧ st'.marks = pre ∧ st'.top = m.top) ∧
      (∀ i, i ≠ j → D'.stacks[i]? = D.stacks[i]?) ∧ D'.kern.I = D.kern.I := by
  cases h with
  | ok hst₀ _ _ hsp hrl =>
    rw [hst] at hst₀; cases hst₀
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hsp
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hrl
    refine ⟨⟨_, List.getElem?_set_self (lt_of_getElem? hst), ?_, rfl⟩,
      fun i hi => List.getElem?_set_ne (Ne.symm hi), ?_⟩
    · simp only [rewindMeta]; rw [hs]; exact takeWhile_ne_append post hpre
    · rw [releaseEff_I]; rfl

/-! ## Marks are never reused (`mark_no_aba`) -/

/-- Well-formed marks (DS-v1, non-normative, "marks carry stack identity and a fresh mark
identifier"; support; library metadata, §38): the live marks of stack `i` are pairwise distinct,
name stack `i`, and have identifiers already given out. -/
def MarksWF (D : DState) : Prop :=
  ∀ (i : Nat) (st : Stack), D.stacks[i]? = some st →
    st.marks.Nodup ∧ ∀ m ∈ st.marks, m.stack = i ∧ m.id < D.fresh

/-- A removed mark (DS-v1, non-normative; support; library metadata, §38): its identifier was
given out and it is live in no stack. -/
def Gone (D : DState) (m : Mark) : Prop :=
  m.id < D.fresh ∧ ∀ (i : Nat) (st : Stack), D.stacks[i]? = some st → m ∉ st.marks

/-- The initial state has well-formed marks (DS-v1, §47). -/
theorem marksWF_init (statics : Statics) : MarksWF (DState.init statics) := fun i st h => by
  simp [DState.init] at h

/-- Replacing stack `j` by a stack whose marks are a sublist keeps `MarksWF` when no identifier is
taken back (DS-v1; §38 library metadata). -/
theorem marksWF_set {D D' : DState} {j : Nat} {st st' : Stack} (hw : MarksWF D)
    (hst : D.stacks[j]? = some st) (hs : D'.stacks = D.stacks.set j st')
    (hsub : st'.marks.Sublist st.marks) (hf : D.fresh ≤ D'.fresh) : MarksWF D' := by
  intro i st'' h
  rw [hs] at h
  rcases getElem?_set_cases h with ⟨rfl, rfl⟩ | ⟨-, h⟩
  · exact ⟨(hw _ st hst).1.sublist hsub, fun m hm => by
      have := (hw _ st hst).2 m (hsub.subset hm); exact ⟨this.1, by omega⟩⟩
  · exact ⟨(hw i st'' h).1, fun m hm => by
      have := (hw i st'' h).2 m hm; exact ⟨this.1, by omega⟩⟩

/-- Replacing stack `j` by a stack whose marks are a sublist keeps a removed mark removed (DS-v1;
§38 library metadata). -/
theorem gone_set {D D' : DState} {j : Nat} {st st' : Stack} {m : Mark} (hg : Gone D m)
    (hst : D.stacks[j]? = some st) (hs : D'.stacks = D.stacks.set j st')
    (hsub : ∀ x ∈ st'.marks, x ∈ st.marks) (hf : D.fresh ≤ D'.fresh) : Gone D' m := by
  refine ⟨by have := hg.1; omega, fun i st'' h hm => ?_⟩
  rw [hs] at h
  rcases getElem?_set_cases h with ⟨rfl, rfl⟩ | ⟨-, h⟩
  · exact hg.2 _ st hst (hsub m hm)
  · exact hg.2 i st'' h hm

/-- Every library step keeps `MarksWF` (DS-v1; §38 library metadata). -/
theorem DStep.marksWF {k : K} {D D' : DState} (h : DStep k D D') (hw : MarksWF D) :
    MarksWF D' := by
  cases h with
  | kernel => exact hw
  | newStack hs =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
    intro i st h
    rcases getElem?_append_single h with h | rfl
    · exact hw i st h
    · exact ⟨List.nodup_nil, fun m hm => by simp at hm⟩
  | push hs =>
    cases hs with
    | ok hst => exact marksWF_set hw hst rfl (List.Sublist.refl _) (Nat.le_refl _)
  | rewind hs =>
    cases hs with
    | ok hst => exact marksWF_set hw hst rfl (List.takeWhile_sublist _) (Nat.le_refl _)
  | grow hs =>
    cases hs with
    | ok hst => exact marksWF_set hw hst rfl (List.Sublist.refl _) (Nat.le_refl _)
  | mark hs =>
    cases hs with
    | ok hst =>
      rename_i st
      intro i st' h
      rcases getElem?_set_cases h with ⟨rfl, rfl⟩ | ⟨-, h⟩
      · obtain ⟨hnd, hms⟩ := hw _ st hst
        refine ⟨List.nodup_append.2 ⟨hnd, List.nodup_cons.2 ⟨by simp, List.nodup_nil⟩,
          fun a ha b hb e => ?_⟩, fun m hm => ?_⟩
        · rw [List.mem_singleton] at hb; subst hb; subst e
          exact Nat.lt_irrefl _ (hms _ ha).2
        · rcases List.mem_append.1 hm with hm | hm
          · exact ⟨(hms m hm).1, Nat.lt_succ_of_lt (hms m hm).2⟩
          · rw [List.mem_singleton] at hm; subst hm; exact ⟨rfl, Nat.lt_succ_self _⟩
      · exact ⟨(hw i st' h).1, fun m hm =>
          ⟨((hw i st' h).2 m hm).1, Nat.lt_succ_of_lt ((hw i st' h).2 m hm).2⟩⟩

/-- Every library-reachable state has well-formed marks (DS-v1; §47 initial state). -/
theorem DReach.marksWF {k : K} {statics : Statics} {D : DState} (h : DReach k statics D) :
    MarksWF D := by
  induction h with
  | init => exact marksWF_init statics
  | step _ hs ih => exact hs.marksWF ih

/-- Every library step keeps a removed mark removed: identifiers are fresh (DS-v1; §38 library
metadata). -/
theorem DStep.gone {k : K} {D D' : DState} {m : Mark} (h : DStep k D D') (hg : Gone D m) :
    Gone D' m := by
  cases h with
  | kernel => exact hg
  | newStack hs =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
    refine ⟨hg.1, fun i st h hm => ?_⟩
    rcases getElem?_append_single h with h | rfl
    · exact hg.2 i st h hm
    · simp at hm
  | push hs => cases hs with | ok hst => exact gone_set hg hst rfl (fun _ h => h) (Nat.le_refl _)
  | rewind hs =>
    cases hs with
    | ok hst => exact gone_set hg hst rfl (fun _ h => List.takeWhile_subset _ h) (Nat.le_refl _)
  | grow hs => cases hs with | ok hst => exact gone_set hg hst rfl (fun _ h => h) (Nat.le_refl _)
  | mark hs =>
    cases hs with
    | ok hst =>
      rename_i st
      refine ⟨Nat.lt_succ_of_lt hg.1, fun i st' h hm => ?_⟩
      rcases getElem?_set_cases h with ⟨rfl, rfl⟩ | ⟨-, h⟩
      · rcases List.mem_append.1 hm with hm | hm
        · exact hg.2 _ st hst hm
        · rw [List.mem_singleton] at hm; rw [hm] at hg; exact Nat.lt_irrefl _ hg.1
      · exact hg.2 i st' h hm

/-- Every run keeps a removed mark removed (DS-v1; §38 library metadata). -/
theorem DRun.gone {k : K} {D D' : DState} {m : Mark} (h : DRun k D D') (hg : Gone D m) :
    Gone D' m := by
  induction h with
  | refl => exact hg
  | tail _ hs ih => exact hs.gone ih

/-- `rewind` of a mark live in no stack fails, with no other outcome, on every existing stack
(DS-v1, non-normative: "rewind m fails on a dead or foreign mark"; §58 `fail`). -/
theorem rewind_dead_fails {k : K} {D : DState} {i : Nat} {st : Stack} {m : Mark}
    (hst : D.stacks[i]? = some st) (hm : m ∉ st.marks) :
    RewindStep k i m D .fail ∧ ∀ o, RewindStep k i m D o → o = .fail := by
  refine ⟨.dead hst fun h => hm h.2, fun o ho => ?_⟩
  cases ho with
  | noStack h => rw [hst] at h; cases h
  | dead => rfl
  | static h hl => rw [hst] at h; cases h; exact absurd hl.2 hm
  | split h hl => rw [hst] at h; cases h; exact absurd hl.2 hm
  | release h hl => rw [hst] at h; cases h; exact absurd hl.2 hm
  | ok h hl => rw [hst] at h; cases h; exact absurd hl.2 hm

/-- `mark_no_aba` (DS-v1, non-normative: marks carry a fresh identifier; `rewind m` removes `m` and
every mark above it): every mark removed by an `ok` of `rewind m`, `m` and every later mark of the
stack, is live in no stack after any later run, even when the top returns to its position, and its
`rewind` fails, with no other outcome (§58), on every existing stack. Under `MarksWF`, which holds
on every library-reachable state (`DReach.marksWF`). -/
theorem mark_no_aba {k : K} {D D₁ D' : DState} {j : Nat} {m : Mark} (hw : MarksWF D)
    (hr : RewindStep k j m D (.ok D₁)) (hrun : DRun k D₁ D') {st : Stack}
    (hst : D.stacks[j]? = some st) {pre post : List Mark} (hs : st.marks = pre ++ m :: post)
    {m' : Mark} (hm' : m' ∈ m :: post) :
    (∀ (i : Nat) (st' : Stack), D'.stacks[i]? = some st' → m' ∉ st'.marks) ∧
      ∀ (i : Nat) (st' : Stack), D'.stacks[i]? = some st' →
        RewindStep k i m' D' .fail ∧ ∀ o, RewindStep k i m' D' o → o = .fail := by
  obtain ⟨hnd, hms⟩ := hw j st hst
  rw [hs] at hnd
  have hdisj := (List.nodup_append.1 hnd).2.2
  have hmpre : m ∉ pre := fun h => hdisj m h m (List.mem_cons_self ..) rfl
  have hm'st : m' ∈ st.marks := by rw [hs]; exact List.mem_append_right _ hm'
  obtain ⟨⟨st₁, hst₁, hpre₁, -⟩, hother, -⟩ := rewind_keeps_older_marks hr hst hs hmpre
  have hf : D₁.fresh = D.fresh := by cases hr; rfl
  have hg : Gone D₁ m' := by
    refine ⟨by rw [hf]; exact (hms m' hm'st).2, fun i st'' h hin => ?_⟩
    by_cases hij : i = j
    · subst hij; rw [hst₁] at h; cases h; rw [hpre₁] at hin
      exact hdisj m' hin m' hm' rfl
    · rw [hother i hij] at h
      exact hij (((hw i st'' h).2 m' hin).1.symm.trans (hms m' hm'st).1)
  have hg' := hrun.gone hg
  exact ⟨hg'.2, fun i st' h => rewind_dead_fails h (hg'.2 i st' h)⟩

/-! ## `grow` (DS-v1) -/

/-- `grow_same_base` (DS-v1, non-normative: "grow is in place only (same base, extension into the
space directly after the block)"): an `ok` of `grow b extra` grows the block of authority `b` of
the stack in place: `extra` is positive and the extension is in place; the metadata records the
grown block of the same base, `extra` more cells, the new authority and the same destination; in
the arrival state that authority, of fresh identity, is an active `Modify` derived from `internal`
covering the cells from the same base and held by the destination (§61, §65 `ok` effects); the old
cells are a prefix of the new ones; `b` is inactive (§62). -/
theorem grow_same_base {k : K} {D D' : DState} {j b extra : Nat}
    (h : GrowStep k j b extra D (.ok D')) :
    ∃ st x, D.stacks[j]? = some st ∧ st.block b = some x ∧ 0 < extra ∧ InPlace st x extra ∧
      D'.stacks[j]? = some (growMeta st x extra D.kern.A.length) ∧
      growBlk x extra D.kern.A.length ∈ (growMeta st x extra D.kern.A.length).blocks ∧
      D'.kern.A[D.kern.A.length]? =
        some ⟨.modify, some st.internal, cellsOf st x.base (x.size + extra), .place x.dst, true⟩ ∧
      cellsOf st x.base x.size <+: cellsOf st x.base (x.size + extra) ∧
      ¬ D'.kern.Active b := by
  cases h with
  | @ok st x s₁ s₂ s₃ hst hx hpos hrl hstat hin hsp hsto =>
    obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 hrl
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hsp
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hsto
    have hlen := releaseEff_len D.kern b
    obtain ⟨yb, hyb, -⟩ := hpre.active
    have hbl : b < D.kern.A.length := lt_of_getElem? hyb
    have hblk := split_block (releaseEff D.kern b) st.internal (cellsOf st x.base (x.size + extra))
    rw [hlen] at hblk ⊢
    have hxb : x.auth = b := by simpa using List.find?_some hx
    refine ⟨st, x, hst, hx, hpos, hin, List.getElem?_set_self (lt_of_getElem? hst),
      List.mem_map.2 ⟨x, List.mem_of_find?_eq_some hx, by simp⟩, ?_, cellsOf_prefix st _ _ _, ?_⟩
    · rw [storeEff_eq hblk]
      simp only
      rw [List.getElem?_set_self (by simp [splitEff, hlen])]
    · rintro ⟨y, hy, ya⟩
      rw [storeEff_eq hblk] at hy
      simp only at hy
      rw [List.getElem?_set_ne (by omega)] at hy
      simp only [splitEff, List.map_cons, List.map_nil] at hy
      rw [List.getElem?_append_left (by rw [hlen]; exact hbl), releaseEff_eq hyb,
        List.getElem?_set_self hbl] at hy
      cases hy; simp at ya

/-- `grow_keeps_prefix_init` (DS-v1, non-normative; §62, §61, §65 `ok` effects): `grow` changes the
initialization of no cell of the old block: `release` and `split` change no initialization, and
`store` initializes only the destination, which the new block does not cover (§65.3). -/
theorem grow_keeps_prefix_init {k : K} {D D' : DState} {j b extra : Nat}
    (h : GrowStep k j b extra D (.ok D')) {st : Stack} {x : Blk} (hst : D.stacks[j]? = some st)
    (hx : st.block b = some x) : ∀ l ∈ cellsOf st x.base x.size, D'.kern.I l = D.kern.I l := by
  cases h with
  | ok hst₀ hx₀ _ hrl _ _ hsp hsto =>
    rw [hst] at hst₀; cases hst₀; rw [hx] at hx₀; cases hx₀
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hrl
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hsp
    obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 hsto
    intro l hl
    have hblk := split_block (releaseEff D.kern b) st.internal (cellsOf st x.base (x.size + extra))
    have hlr : l ∈ (splitEff (releaseEff D.kern b) st.internal
        [cellsOf st x.base (x.size + extra)]).afp (releaseEff D.kern b).A.length := by
      simp only [S3.afp, hblk]; exact (cellsOf_prefix st x.base x.size extra).subset hl
    have hne : l ≠ x.dst := fun he =>
      (hpre.noCover l hlr).1 (by rw [he]; exact mem_footprint_self hpre.usable hpre.leaf)
    rw [storeEff_eq hblk]
    simp only [hne, ↓reduceIte]
    show (releaseEff D.kern b).I l = _; rw [releaseEff_I]

/-! ## Bytes of the old block after `grow` (refinement, §82) -/

/-- A raw write into the range of leaf `d` leaves the bytes of the range of a leaf `l` in another
allocation or with a disjoint range unchanged (§16 ¶3, §82.1; support for DS-v1 `grow`). -/
theorem bytesOf_write_other {s2 : Machine.State} {L : Refinement.Layout} {l d : Nat}
    {w : Nat → UInt8 × Option Nat}
    (hd : (L l).alloc ≠ (L d).alloc ∨
      Machine.RangeDisjoint (L l).off (L l).len (L d).off (L d).len)
    {i : Nat} (hi : i < (L l).len) :
    Refinement.bytesOf (s2.write (Refinement.leafAcc s2 L .write d) w) L l i =
      Refinement.bytesOf s2 L l i := by
  unfold Refinement.bytesOf
  rw [Refinement.write_allocs]
  by_cases heq : (L l).alloc = (L d).alloc
  · have hr := hd.resolve_left (· heq)
    simp only [Refinement.leafAcc, heq, ↓reduceIte]
    cases ha : s2.allocs (L d).alloc with
    | none => rfl
    | some a =>
      simp only [Option.map_some, Refinement.leafAddr, Refinement.baseOf_of ha,
        Nat.add_sub_cancel_left]
      rw [Machine.Alloc.write_bytes_out]
      intro ⟨h1, h2⟩
      exact hr ((L l).off + i) (Nat.le_add_right _ _) (Nat.add_lt_add_left hi _) h1 h2
  · simp only [Refinement.leafAcc, heq, ↓reduceIte]

/-- `grow_keeps_prefix_bytes` (DS-v1, non-normative; through the refinement of Part XVII, §82): an
`ok` of `grow b extra` is the kernel steps `release(b)`, `split(internal, [region])` and
`store(|A|, dst)`; their realization in the memory machine (`Refinement.opsOf`) has no raw
operation for `release` and `split` (§62, §61), and the raw operations of `store` (one write into
the range of the destination, §82.3) leave the bytes, values and provenances, of every cell of the
old block unchanged, for every layout satisfying the layout interface `LayoutWF` (§82.1, §23) in
the state before the step. -/
theorem grow_keeps_prefix_bytes {Ty : Type} {k : K} {D D' : DState} {j b extra : Nat}
    (h : GrowStep k j b extra D (.ok D')) {st : Stack} {x : Blk} (hst : D.stacks[j]? = some st)
    (hx : st.block b = some x) :
    ∃ s₁ s₂, Refinement.OpStep k (.release b) D.kern s₁ ∧
      Refinement.OpStep k (.split st.internal [cellsOf st x.base (x.size + extra)]) s₁ s₂ ∧
      Refinement.OpStep k (.store D.kern.A.length x.dst) s₂ D'.kern ∧
      ∀ (π : Refinement.Params Ty) (s2 : Machine.State), Refinement.LayoutWF π.L D.kern s2 →
        Refinement.opsOf π (.release b) D.kern s2 = [] ∧
        Refinement.opsOf π (.split st.internal [cellsOf st x.base (x.size + extra)]) s₁ s2 = [] ∧
        ∀ l ∈ cellsOf st x.base x.size, ∀ i < (π.L l).len,
          Refinement.bytesOf
            (Refinement.run s2 (Refinement.opsOf π (.store D.kern.A.length x.dst) s₂ s2)) π.L l i =
          Refinement.bytesOf s2 π.L l i := by
  cases h with
  | @ok st₀ x₀ s₁ s₂ s₃ hst₀ hx₀ hpos hrl hstat hin hsp hsto =>
    rw [hst] at hst₀; cases hst₀; rw [hx] at hx₀; cases hx₀
    have hlen : s₁.A.length = D.kern.A.length := by
      rw [(Guarded.ok_iff.1 hrl).2]; exact releaseEff_len D.kern b
    have hP₁ : s₁.P = D.kern.P := by rw [(Guarded.ok_iff.1 hrl).2]; exact releaseEff_P D.kern b
    have hP₂ : s₂.P = D.kern.P := by rw [(Guarded.ok_iff.1 hsp).2, ← hP₁]; rfl
    rw [hlen] at hsto
    refine ⟨s₁, s₂, hrl, hsp, hsto, fun π s2 hlw => ⟨rfl, rfl, fun l hl i hi => ?_⟩⟩
    obtain ⟨hpre, -⟩ := Guarded.ok_iff.1 hsto
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hsp
    have hblk := split_block s₁ st.internal (cellsOf st x.base (x.size + extra))
    rw [hlen] at hblk
    have hlr' : l ∈ cellsOf st x.base (x.size + extra) :=
      (cellsOf_prefix st x.base x.size extra).subset hl
    have hlr : l ∈ (splitEff s₁ st.internal [cellsOf st x.base (x.size + extra)]).afp
        D.kern.A.length := by simp only [S3.afp, hblk]; exact hlr'
    have hne : l ≠ x.dst := fun he =>
      (hpre.noCover l hlr).1 (by rw [he]; exact mem_footprint_self hpre.usable hpre.leaf)
    obtain ⟨hlP, hlleaf, -⟩ := mem_footprint.1 (hstat.regionIn l hlr')
    rw [hP₁] at hlP hlleaf
    have hdP : x.dst < D.kern.P.length := hP₂ ▸ hpre.usable.lt
    have hdleaf : isLeaf D.kern.P x.dst := hP₂ ▸ hpre.leaf
    have hdis : (π.L l).alloc ≠ (π.L x.dst).alloc ∨
        Machine.RangeDisjoint (π.L l).off (π.L l).len (π.L x.dst).off (π.L x.dst).len := by
      by_cases ha : (π.L l).alloc = (π.L x.dst).alloc
      · exact .inr (hlw.disjoint l x.dst hlP hdP hlleaf hdleaf hne ha)
      · exact .inl ha
    simp only [Refinement.opsOf, Refinement.storeOps]
    split
    · exact bytesOf_write_other hdis hi
    · rfl

/-! ## Non-vacuity: a concrete run (DS-v1)

A run from `DState.init wst` under the test contract `Access.Examples.K0` (§48). Statics (§47):
leaf 0 (`Init`) is the stack value; place 1 is the storage, with the cells 2 and 3; leaves 4 and 5
are destinations; root authorities 0, 1, 2, 3 on the roots 0, 1, 4, 5, held by frame 0. Every
precondition is decided by `decide`. -/

namespace Witness

open Examples

/-- The statics of the run (§47; DS-v1 non-vacuity): stack value 0, storage 1 with cells 2 and 3,
destinations 4 and 5. -/
def wst : Statics :=
  [((none, none, 0), true), ((none, none, 0), false), ((some 1, none, 0), false),
    ((some 1, none, 0), false), ((none, none, 0), false), ((none, none, 0), false)]

/-- Initial state (§47; DS-v1 non-vacuity). -/
def d0 : DState := DState.init wst
/-- `derive(1, [2, 3], Modify)`: authority 4, held by frame 0 (§60; DS-v1 non-vacuity). -/
def d1 : DState := ⟨deriveEff d0.kern 1 [2, 3] .modify, d0.stacks, d0.fresh⟩
/-- `store(4, 0)`: authority 4 becomes `internal`, held by the stack value 0 (§65; DS-v1
non-vacuity). -/
def d2 : DState := ⟨storeEff d1.kern 4 0, d1.stacks, d1.fresh⟩
/-- `newStack(1, 4)` (DS-v1, §56). -/
def d3 : DState := newStackEff d2 1 4
/-- The stack registered by `newStack(1, 4)` (DS-v1, §46). -/
def st3 : Stack := ⟨1, 4, footprint d2.kern.P 1, 0, [], []⟩
/-- `mark(0)`: mark `⟨0, 0, 0⟩` (DS-v1, §58). -/
def d4 : DState := ⟨d3.kern, d3.stacks.set 0 (markMeta 0 st3 d3.fresh), d3.fresh + 1⟩
/-- The stack after the first mark (DS-v1, §46). -/
def st4 : Stack := markMeta 0 st3 d3.fresh
/-- `push(0, 1, 4)`: `split(4, [[2]])`, `store(5, 4)` (DS-v1, Part XIV, §77). -/
def d5 : DState :=
  ⟨storeEff (splitEff d4.kern st4.internal [cellsOf st4 st4.top 1]) d4.kern.A.length 4,
    d4.stacks.set 0 (pushMeta st4 1 d4.kern.A.length 4), d4.fresh⟩
/-- The stack after the first push: block `⟨0, 1, 5, 4⟩` (DS-v1, §46). -/
def st5 : Stack := pushMeta st4 1 d4.kern.A.length 4
/-- `mark(0)`: mark `⟨0, 1, 1⟩` (DS-v1, §58). -/
def d6 : DState := ⟨d5.kern, d5.stacks.set 0 (markMeta 0 st5 d5.fresh), d5.fresh + 1⟩
/-- The stack after the second mark (DS-v1, §46). -/
def st6 : Stack := markMeta 0 st5 d5.fresh
/-- `push(0, 1, 5)`: `split(4, [[3]])`, `store(6, 5)` (DS-v1, Part XIV, §77). -/
def d7 : DState :=
  ⟨storeEff (splitEff d6.kern st6.internal [cellsOf st6 st6.top 1]) d6.kern.A.length 5,
    d6.stacks.set 0 (pushMeta st6 1 d6.kern.A.length 5), d6.fresh⟩
/-- The stack after the second push: blocks `⟨0, 1, 5, 4⟩`, `⟨1, 1, 6, 5⟩` (DS-v1, §46). -/
def st7 : Stack := pushMeta st6 1 d6.kern.A.length 5
/-- `release(6)` by the program (§62; DS-v1 non-vacuity). -/
def d8 : DState := ⟨releaseEff d7.kern 6, d7.stacks, d7.fresh⟩
/-- The second mark (DS-v1, §58). -/
def m1 : Mark := ⟨0, 1, 1⟩
/-- `rewind(0, ⟨0, 1, 1⟩)`: `split(4, [[3]])`, `release(7)` (DS-v1, §61, §62). -/
def d9 : DState :=
  ⟨releaseEff (splitEff d8.kern st7.internal [above st7 m1]) d8.kern.A.length,
    d8.stacks.set 0 (rewindMeta st7 m1), d8.fresh⟩
/-- The stack after the rewind (DS-v1, §46). -/
def st9 : Stack := rewindMeta st7 m1
/-- The block of authority 5 (DS-v1, §46). -/
def x5 : Blk := ⟨0, 1, 5, 4⟩
/-- `grow(0, 5, 1)`: `release(5)`, `split(4, [[2, 3]])`, `store(8, 4)` (DS-v1, Part XIV,
§77). -/
def d10 : DState :=
  ⟨storeEff (splitEff (releaseEff d9.kern 5) st9.internal [cellsOf st9 x5.base (x5.size + 1)])
      (releaseEff d9.kern 5).A.length x5.dst,
    d9.stacks.set 0 (growMeta st9 x5 1 (releaseEff d9.kern 5).A.length), d9.fresh⟩

/-- The run up to the second push is library-reachable (DS-v1; §47, Part XIV derived `issue`,
§77). -/
theorem d7_reach : DReach K0 wst d7 := by
  have r1 : DReach K0 wst d1 := .step .init (.kernel (.derive (.ok (by decide))))
  have r2 : DReach K0 wst d2 := .step r1 (.kernel (.store (.ok (by decide))))
  have r3 : DReach K0 wst d3 := .step r2 (.newStack (others := []) (.ok (by decide)))
  have r4 : DReach K0 wst d4 := .step r3 (.mark (.ok (st := st3) (by decide)))
  have r5 : DReach K0 wst d5 := .step r4
    (.push (.ok (st := st4) (by decide) (by decide) (by decide) (.ok (by decide))
      (.ok (by decide))))
  have r6 : DReach K0 wst d6 := .step r5 (.mark (.ok (st := st5) (by decide)))
  exact .step r6
    (.push (.ok (st := st6) (by decide) (by decide) (by decide) (.ok (by decide))
      (.ok (by decide))))

/-- The run up to the rewind is library-reachable (DS-v1; §62, Part XIV derived `reset`, §78). -/
theorem d9_reach : DReach K0 wst d9 :=
  .step (.step d7_reach (.kernel (.release (.ok (by decide)))))
    (.rewind (.ok (st := st7) (by decide) (by decide) (by decide) (.ok (by decide))
      (.ok (by decide))))

/-- **Non-vacuity of the DS-v1 operations** (§58 outcomes). In `d7`, `rewind ⟨0, 1, 1⟩` is
rejected: block 6, derived from `internal` 4, covers cell 3 above the mark
(`rewind_rejects_live_above`); `grow` of block 5, which is not at the top, fails (DS-v1 "fail
otherwise"). After the program releases 6, `rewind ⟨0, 1, 1⟩` is `ok`: the top returns to 1,
the older mark stays; the removed mark then fails (`mark_no_aba`). `grow` of block 5 by one cell
is then `ok` in place: block `⟨0, 2, 8, 4⟩`, whose authority 8 covers the cells 2 and 3. -/
theorem run_ok :
    DReach K0 wst d10 ∧
    RewindStep K0 0 m1 d7 .reject ∧ GrowStep K0 0 5 1 d7 .fail ∧
    d9.stacks = [⟨1, 4, [2, 3], 1, [x5], [⟨0, 0, 0⟩]⟩] ∧ RewindStep K0 0 m1 d9 .fail ∧
    d10.stacks = [⟨1, 4, [2, 3], 2, [⟨0, 2, 8, 4⟩], [⟨0, 0, 0⟩]⟩] ∧ d10.kern.afp 8 = [2, 3] := by
  have r10 : DReach K0 wst d10 := .step d9_reach
    (.grow (.ok (st := st9) (x := x5) (by decide) (by decide) (by decide) (.ok (by decide))
      (by decide) (by decide) (.ok (by decide)) (.ok (by decide))))
  have hrej := (rewind_rejects_live_above (k := K0) (D := d7) (j := 0) (st := st7) (m := m1)
    (x := 6) (l := 3) (y := ⟨.modify, some 4, [3], .place 5, true⟩) (by decide) (by decide)
    (by decide) rfl (by decide) (by decide) (by decide)).1
  have hfail : GrowStep K0 0 5 1 d7 .fail :=
    .fail (st := st7) (x := x5) (by decide) (by decide) (by decide) (.ok (by decide)) (by decide)
      (by decide)
  exact ⟨r10, hrej, hfail, by decide, (rewind_dead_fails (st := st9) (by decide) (by decide)).1,
    by decide, by decide⟩

/-! ### Readings with a changed verdict (DS-v1)

Each theorem below shows, on a library-reachable state, a program whose verdict depends on a
reading of DS-v1 recorded in the readings: the verdict of the reading formalized here, and the
facts that make the other reading give another verdict. -/

/-- `release(5)` by the program, after the rewind (§62; DS-v1 non-vacuity). -/
def d11 : DState := ⟨releaseEff d9.kern 5, d9.stacks, d9.fresh⟩
/-- `derive(4, [3], Modify)` by the program: authority 8 on cell 3, above the current top (§60;
DS-v1 reading of "above"). -/
def d12 : DState := ⟨deriveEff d11.kern 4 [3] .modify, d11.stacks, d11.fresh⟩
/-- The first mark (DS-v1, §58). -/
def m0 : Mark := ⟨0, 0, 0⟩
/-- A callee frame with no parameter and no local, entered after the rewind (§72; DS-v1 reading
of the order of `fail` and the right of §36). -/
def d13 : DState := ⟨enterEff d9.kern [] [], d9.stacks, d9.fresh⟩

/-- **Reading of "a cell above m"** (DS-v1, §46). In `d12`, authority 8, active and derived from
`internal` 4, covers cell 3, at a position above the top of mark `⟨0, 0, 0⟩` but above the current
top too, hence not among the cells `rewind` returns (`above`): `rewind ⟨0, 0, 0⟩` is `ok`. Under the
reading "any cell at a position at or above the top of `m`", it is rejected. -/
theorem reading_above :
    DReach K0 wst d12 ∧ d12.kern.A[8]? = some ⟨.modify, some 4, [3], .frame 0, true⟩ ∧
    st9.internal ∈ d12.kern.ancs 8 ∧ 3 ∈ st9.cells.drop m0.top ∧ 3 ∉ above st9 m0 ∧
    ∃ D', RewindStep K0 0 m0 d12 (.ok D') := by
  have r11 : DReach K0 wst d11 := .step d9_reach (.kernel (.release (.ok (by decide))))
  have r12 : DReach K0 wst d12 := .step r11 (.kernel (.derive (.ok (by decide))))
  exact ⟨r12, by decide, by decide, by decide, by decide,
    ⟨_, .ok (st := st9) (by decide) (by decide) (by decide) (.ok (by decide)) (.ok (by decide))⟩⟩

/-- **Readings of the order of checks and of `extra = 0`** (DS-v1, §58, §36). (1) In `d13`, a callee
with no right on the stack value (`¬ AdminRight`) rewinds to the removed mark `⟨0, 1, 1⟩`: the
outcome is `fail` (dead mark checked first); with the right of §36 checked first it is `reject`.
(2) In `d9`, `grow(0, 5, 0)` is rejected (`extra = 0`), while the sequence `release`, static checks,
in-place check, `split`, `store` of the same region would be `ok`. (3) In `d3`, `push(0, 3, 4)` asks
for more cells than the storage has: `fail` (availability), although the requested cells are not all
in the storage. -/
theorem reading_order :
    DReach K0 wst d13 ∧ ¬ AdminRight d13.kern st9 ∧ RewindStep K0 0 m1 d13 .fail ∧
    GrowStep K0 0 5 0 d9 .reject ∧
    ReleaseStep 5 d9.kern (.ok (releaseEff d9.kern 5)) ∧
    IssueStatic (releaseEff d9.kern 5) st9.entry (cellsOf st9 x5.base (x5.size + 0)) x5.dst ∧
    InPlace st9 x5 0 ∧
    SplitStep K0 st9.internal [cellsOf st9 x5.base (x5.size + 0)] (releaseEff d9.kern 5)
      (.ok (splitEff (releaseEff d9.kern 5) st9.internal [cellsOf st9 x5.base (x5.size + 0)])) ∧
    StoreStep (releaseEff d9.kern 5).A.length x5.dst
      (splitEff (releaseEff d9.kern 5) st9.internal [cellsOf st9 x5.base (x5.size + 0)])
      (.ok (storeEff (splitEff (releaseEff d9.kern 5) st9.internal
        [cellsOf st9 x5.base (x5.size + 0)]) (releaseEff d9.kern 5).A.length x5.dst)) ∧
    PushStep K0 0 3 4 d3 .fail := by
  have r13 : DReach K0 wst d13 := .step d9_reach (.kernel (.enter (.ok (by decide))))
  exact ⟨r13, by decide, .dead (st := st9) (by decide) (by decide),
    .noExtra (st := st9) (x := x5) (by decide) (by decide) rfl, .ok (by decide), by decide,
    by decide, .ok (by decide), .ok (by decide),
    .fail (st := st3) (by decide) (by decide) (by decide)⟩

end Witness

end Ern.Lib.DataStack
