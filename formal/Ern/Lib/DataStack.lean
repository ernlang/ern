import Ern.MemoryModel.Arena
import Ern.MemoryModel.Refinement

/-!
# DataStack: a library administrative abstraction (contract DS-v2, non-normative)

A `DataStack` instance of `specs/ERN_Memory_Model_Specification_v0.1.md`. The spec does not define
its contract (Part XIV preamble: "The contracts of `HandlePool` and `DataStack` belong to their
library abstractions and are not defined here"). The contract formalized here is the library
contract **DS-v2**, which is **not normative**: every definition below that encodes a DS-v2 item
says so. The normative clauses that constrain it are §36 (`MetaRight` requires `Modify` exercisable
on the stack value; the abstraction adds no rights to the kernel), §38 and §46 (library state
separate from `S₃`), §47 (empty initial registry), §56 (guard over all registries of live
administrations) and §58 (outcomes).

DS-v2 is DS-v1 with three changes. DS-v1: marks carry the stack identity and a fresh mark
identifier; the stack keeps the ordered list of live marks; `rewind m` fails on a dead or foreign
mark, rejects if an active authority derived from `internal` covers a cell above `m`, otherwise
returns those cells to available and removes `m` and every mark above it; `push` and `grow` use the
derived `issue` of Part XIV (`Arena.IssueD`: its static checks, the availability `fail`, then
`split` of `internal` and `store` of the block); `grow` is in place only (same base, extension into
the space directly after the block, `fail` otherwise). DS2-1: `mark` requires the administrative
right of §36 (`AdminRight`), else `reject`. DS2-2: `grow` stores the new block authority into the
place that currently holds the block authority `b`. DS2-3: a dead stack (`internal` inactive)
invalidates its marks, so `rewind` of a mark of a dead stack is `fail`, checked with the dead or
foreign mark, before the right. Also part of DS-v2: `push` without room is `fail`; `grow` of a `b`
that is no block of the stack is `reject`; §76.5 applies to `newStack`; the dead or foreign mark is
checked before the right of §36; §36 applies to `rewind`.

Every `ok` step of the library is a sequence of kernel steps O1–O16 (`DReach.reachable`), so the
abstraction adds no rights to the kernel (§36).
-/

namespace Ern.Lib.DataStack

open Ern.MemoryModel Ern.MemoryModel.Access Ern.MemoryModel.Arena

/-! ## Library state (DS-v2; §38, §46, §47) -/

/-- A block issued by a stack (DS-v2, non-normative; recorded like the issuances of §46): position
`base` of its first cell and number `size` of cells among the ordered cells of the stack, block
authority `auth`, destination `dst` that received it (at `push`, or at the `grow` that issued it,
DS2-2). -/
structure Blk where
  base : Nat
  size : Nat
  auth : Nat
  dst : Nat
deriving DecidableEq, Repr

/-- A mark (DS-v2, non-normative: "marks carry stack identity and a fresh mark identifier";
library metadata of an administrative abstraction, §36, §38): the identity of its stack, its fresh
identifier, the top of the stack when it was taken. -/
structure Mark where
  stack : Nat
  id : Nat
  top : Nat
deriving DecidableEq, Repr

/-- A stack (DS-v2, non-normative; library state, §38, §46): administered storage, `internal`
authority held by the stack value (§36), ordered cells (the leaves of the storage at creation),
top (the cells at positions `≥ top` are available), issued blocks (oldest first), and the ordered
list of live marks (DS-v2: "the stack keeps the ordered list of live marks"). -/
structure Stack where
  storage : Nat
  internal : Nat
  cells : List Nat
  top : Nat
  blocks : List Blk
  marks : List Mark
deriving DecidableEq, Repr

/-- State of the stack library (DS-v2, non-normative; §38: administrative states of library
abstractions are separate from `S₃`): the kernel state, the stack registry (a stack is identified
by its index; stacks are never removed) and the next fresh mark identifier. -/
structure DState where
  kern : S3
  stacks : List Stack
  fresh : Nat

/-- Initial state (§47: the kernel's initial state; the library registry starts empty; DS-v2,
non-normative: no mark identifier given out). -/
def DState.init (statics : Statics) : DState := ⟨S3.init statics, [], 0⟩

/-- The `n` cells from position `b` of the stack, leaves of the administered storage (§46; DS-v2,
non-normative). -/
def cellsOf (st : Stack) (b n : Nat) : List Nat := (st.cells.drop b).take n

/-- The cells above mark `m` (DS-v2, non-normative, "a cell above m"; reading DS-R1; §46
available leaves): the positions from the top of `m` to the current top, those that `rewind m`
returns to available. -/
def above (st : Stack) (m : Mark) : List Nat := cellsOf st m.top (st.top - m.top)

/-- The stack seen as an administration entry (§46, §36; DS-v2, non-normative): storage,
`internal`, available cells (positions `≥ top`) and issued blocks. Used for `MetaRight` and the
static checks of the derived `issue`, which read only the storage and `internal`. -/
def Stack.entry (st : Stack) : ArenaEntry :=
  ⟨st.storage, st.internal, st.cells.drop st.top,
    st.blocks.map fun x => (cellsOf st x.base x.size, x.auth)⟩

/-- The block of the stack whose authority is `b` (§46 issuances; DS-v2, non-normative). -/
def Stack.block (st : Stack) (b : Nat) : Option Blk := st.blocks.find? fun y => decide (y.auth = b)

/-- A live mark of stack `j` (DS-v2, non-normative: a mark that is neither dead nor foreign; it
decides the `fail` case of `rewind`, §58): the stack is live (`internal` is active, §46 read for a
stack; DS2-3: a dead stack invalidates its marks), the mark names stack `j` and it belongs to the
list of live marks of the stack. -/
def LiveMark (s : S3) (j : Nat) (st : Stack) (m : Mark) : Prop :=
  s.Active st.internal ∧ m.stack = j ∧ m ∈ st.marks

/-- Decidability of `LiveMark` (§58; DS-v2). -/
instance (s : S3) (j : Nat) (st : Stack) (m : Mark) : Decidable (LiveMark s j st m) := by
  unfold LiveMark; infer_instance

/-- The administrative right of §36 for a stack (DS-v2, non-normative, with §36 and §46 read for a
stack): the stack is live (`internal` is active) and `MetaRight`, `Modify` exercisable on the stack
value, the place holding `internal`. -/
def AdminRight (s : S3) (st : Stack) : Prop := s.Active st.internal ∧ MetaRight s st.entry

/-- Decidability of `AdminRight` (§36; DS-v2). -/
instance (s : S3) (st : Stack) : Decidable (AdminRight s st) := by
  unfold AdminRight; infer_instance

/-! ## `newStack` and the guard of §56 -/

/-- The stack registry as a registry of live administrations (§56; DS-v2, non-normative): the
`internal` identities of its live stacks. -/
def stackInternals (s : S3) (stacks : List Stack) : List Nat :=
  (stacks.filter fun st => decide (s.Active st.internal)).map (·.internal)

/-- Preconditions of `newStack(storage, internal)` (DS-v2, non-normative; §56): those of `newArena`
other than its guard (`NewArenaBase`, §76.1–§76.3, §76.5 and §76.6 read for a stack), and the guard
of §56 over the stack registry and every other registry of live administrations `others`. -/
structure NewStackPre (s : S3) (stacks : List Stack) (others : List (List Nat))
    (storage internal : Nat) : Prop where
  /-- §76.1–§76.3, §76.5, §76.6, read for a stack (DS-v2). -/
  base : NewArenaBase s storage internal
  /-- §56: no live administration of any registry uses `internal`. -/
  guard : Guard56 (stackInternals s stacks :: others) internal

/-- Decidability of `NewStackPre` (§56; DS-v2). -/
instance (s : S3) (stacks : List Stack) (others : List (List Nat)) (storage internal : Nat) :
    Decidable (NewStackPre s stacks others storage internal) :=
  decidable_of_iff (NewArenaBase s storage internal ∧
    Guard56 (stackInternals s stacks :: others) internal)
    ⟨fun ⟨a, b⟩ => ⟨a, b⟩, fun ⟨a, b⟩ => ⟨a, b⟩⟩

/-- Effect of `newStack` (DS-v2, non-normative; §36: registration adds no rights): a stack whose
cells are the leaves of the storage, top 0, no block, no mark; the kernel state is unchanged. -/
def newStackEff (D : DState) (storage internal : Nat) : DState :=
  { D with stacks := D.stacks ++ [⟨storage, internal, footprint D.kern.P storage, 0, [], []⟩] }

/-- `newStack` as a relation (DS-v2, non-normative; §56, §58): `ok` or `reject`. -/
def NewStackStep (others : List (List Nat)) (storage internal : Nat) (D : DState) :
    Outcome3 DState → Prop :=
  Guarded (NewStackPre D.kern D.stacks others storage internal) (newStackEff D storage internal)

/-! ## `push` (DS-v2: the derived `issue`, Part XIV, §77) -/

/-- Metadata after `push` (DS-v2, non-normative; as the `ok` effect of §77 on §46 metadata): the
cells leave the available part (the top rises by `size`), the block is recorded. -/
def pushMeta (st : Stack) (size a dst : Nat) : Stack :=
  { st with top := st.top + size, blocks := st.blocks ++ [⟨st.top, size, a, dst⟩] }

/-- `push(j, size, dst)` (DS-v2, non-normative: "push uses the derived issue"): the derived `issue`
of Part XIV (`Arena.IssueD`) of the `size` cells at the top into `dst`, on the stack seen as an
entry: its static checks (`IssueStatic`, §77.1, §77.2, with `MetaRight` of §36), then `fail`, the
state unchanged, when fewer than `size` cells are left (availability, §77.4; DS-v2, Q11 (a)),
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

/-! ## `mark` (DS-v2) -/

/-- Metadata after `mark` (DS-v2, non-normative; library metadata, §36, §38): a mark naming stack
`j`, with the fresh identifier `fresh` and the current top, is appended to the live marks. -/
def markMeta (j : Nat) (st : Stack) (fresh : Nat) : Stack :=
  { st with marks := st.marks ++ [⟨j, fresh, st.top⟩] }

/-- `mark(j)` (DS-v2, non-normative; §58 outcomes): `reject` on a missing stack; `reject` without
the administrative right of §36 (DS2-1); otherwise `ok`, metadata only (no right created, §36), the
identifier is fresh. -/
inductive MarkStep (j : Nat) (D : DState) : Outcome3 DState → Prop where
  | noStack : D.stacks[j]? = none → MarkStep j D .reject
  | static {st : Stack} : D.stacks[j]? = some st → ¬ AdminRight D.kern st → MarkStep j D .reject
  | ok {st : Stack} : D.stacks[j]? = some st → AdminRight D.kern st →
      MarkStep j D (.ok ⟨D.kern, D.stacks.set j (markMeta j st D.fresh), D.fresh + 1⟩)

/-- `mark_rejects_without_right` (DS-v2, non-normative, DS2-1: `mark` requires `AdminRight` on the
stack, else `reject`; §36, §58): on an existing stack without the administrative right of §36,
`mark` has the outcome `reject` and no other. -/
theorem mark_rejects_without_right {j : Nat} {D : DState} {st : Stack}
    (hst : D.stacks[j]? = some st) (ha : ¬ AdminRight D.kern st) :
    MarkStep j D .reject ∧ ∀ o, MarkStep j D o → o = .reject := by
  refine ⟨.static hst ha, fun o ho => ?_⟩
  cases ho with
  | noStack => rfl
  | static => rfl
  | ok h ha' => rw [hst] at h; cases h; exact absurd ha' ha

/-! ## `rewind` (DS-v2) -/

/-- Metadata after `rewind m` (DS-v2, non-normative; as the `ok` effect of §78 on §46 metadata):
the cells above `m` return to available (the top returns to the top of `m`), the blocks from that
top are forgotten, `m` and every later mark are removed. -/
def rewindMeta (st : Stack) (m : Mark) : Stack :=
  { st with
    top := m.top
    blocks := st.blocks.filter fun x => decide (x.base < m.top)
    marks := st.marks.takeWhile fun x => decide (x ≠ m) }

/-- `rewind(j, m)` (DS-v2, non-normative): `reject` on a missing stack; `fail`, the state
unchanged, on a dead or foreign mark, a mark of a dead stack included (DS2-3), before the right;
`reject` without the administrative right of §36; then the derived `reset` of Part XIV on the cells
above `m`: `split` of `internal` on them (O2), which rejects when an active authority derived from
`internal` covers one of them (`rewind_rejects_live_above`), and `release` of the derived authority
(O3); `ok`: the cells return to available, `m` and the later marks are removed. -/
inductive RewindStep (k : K) (j : Nat) (m : Mark) (D : DState) : Outcome3 DState → Prop where
  | noStack : D.stacks[j]? = none → RewindStep k j m D .reject
  | dead {st : Stack} : D.stacks[j]? = some st → ¬ LiveMark D.kern j st m →
      RewindStep k j m D .fail
  | static {st : Stack} : D.stacks[j]? = some st → LiveMark D.kern j st m →
      ¬ AdminRight D.kern st → RewindStep k j m D .reject
  | split {st : Stack} : D.stacks[j]? = some st → LiveMark D.kern j st m → AdminRight D.kern st →
      SplitStep k st.internal [above st m] D.kern .reject → RewindStep k j m D .reject
  | release {st : Stack} {s₁ : S3} : D.stacks[j]? = some st → LiveMark D.kern j st m →
      AdminRight D.kern st → SplitStep k st.internal [above st m] D.kern (.ok s₁) →
      ReleaseStep D.kern.A.length s₁ .reject → RewindStep k j m D .reject
  | ok {st : Stack} {s₁ s₂ : S3} : D.stacks[j]? = some st → LiveMark D.kern j st m →
      AdminRight D.kern st → SplitStep k st.internal [above st m] D.kern (.ok s₁) →
      ReleaseStep D.kern.A.length s₁ (.ok s₂) →
      RewindStep k j m D (.ok ⟨s₂, D.stacks.set j (rewindMeta st m), D.fresh⟩)

/-- `rewind` has one outcome (§58: a guarded transition has one outcome; DS-v2, non-normative):
the cases of `RewindStep` exclude each other, and `split` and `release` are deterministic
(`Guarded.det`). With `rewind_ok_iff`, an `ok` rewind is never also `reject` or `fail`. -/
theorem RewindStep.det {k : K} {j : Nat} {m : Mark} {D : DState} {o₁ o₂ : Outcome3 DState}
    (h₁ : RewindStep k j m D o₁) (h₂ : RewindStep k j m D o₂) : o₁ = o₂ := by
  cases h₁ with
  | noStack h =>
    cases h₂ with
    | noStack _ => rfl
    | dead h' _ => rw [h] at h'; cases h'
    | static _ _ _ => rfl
    | split _ _ _ _ => rfl
    | release _ _ _ _ _ => rfl
    | ok h' _ _ _ _ => rw [h] at h'; cases h'
  | dead h hl =>
    cases h₂ with
    | noStack h' => rw [h] at h'; cases h'
    | dead _ _ => rfl
    | static h' hl' _ => rw [h] at h'; cases h'; exact absurd hl' hl
    | split h' hl' _ _ => rw [h] at h'; cases h'; exact absurd hl' hl
    | release h' hl' _ _ _ => rw [h] at h'; cases h'; exact absurd hl' hl
    | ok h' hl' _ _ _ => rw [h] at h'; cases h'; exact absurd hl' hl
  | static h hl ha =>
    cases h₂ with
    | noStack _ => rfl
    | dead h' hl' => rw [h] at h'; cases h'; exact absurd hl hl'
    | static _ _ _ => rfl
    | split _ _ _ _ => rfl
    | release _ _ _ _ _ => rfl
    | ok h' _ ha' _ _ => rw [h] at h'; cases h'; exact absurd ha' ha
  | split h hl _ hs =>
    cases h₂ with
    | noStack _ => rfl
    | dead h' hl' => rw [h] at h'; cases h'; exact absurd hl hl'
    | static _ _ _ => rfl
    | split _ _ _ _ => rfl
    | release _ _ _ _ _ => rfl
    | ok h' _ _ hs' _ => rw [h] at h'; cases h'; cases Guarded.det hs hs'
  | release h hl _ hs hr =>
    cases h₂ with
    | noStack _ => rfl
    | dead h' hl' => rw [h] at h'; cases h'; exact absurd hl hl'
    | static _ _ _ => rfl
    | split _ _ _ _ => rfl
    | release _ _ _ _ _ => rfl
    | ok h' _ _ hs' hr' =>
      rw [h] at h'; cases h'; cases Guarded.det hs hs'; cases Guarded.det hr hr'
  | ok h hl ha hs hr =>
    cases h₂ with
    | noStack h' => rw [h] at h'; cases h'
    | dead h' hl' => rw [h] at h'; cases h'; exact absurd hl hl'
    | static h' _ ha' => rw [h] at h'; cases h'; exact absurd ha ha'
    | split h' _ _ hs' => rw [h] at h'; cases h'; cases Guarded.det hs hs'
    | release h' _ _ hs' hr' =>
      rw [h] at h'; cases h'; cases Guarded.det hs hs'; cases Guarded.det hr hr'
    | ok h' _ _ hs' hr' =>
      rw [h] at h'; cases h'; cases Guarded.det hs hs'; cases Guarded.det hr hr'; rfl

/-! ## `grow` (DS-v2: in place, the derived `issue`) -/

/-- In-place extension (DS-v2, non-normative: "extension into the space directly after the
block"; the availability check of the derived `issue`, §77.4): the block ends at the top, and
`extra` available cells follow it. -/
def InPlace (st : Stack) (x : Blk) (extra : Nat) : Prop :=
  x.base + x.size = st.top ∧ st.top + extra ≤ st.cells.length

/-- Decidability of `InPlace` (§77.4; DS-v2). -/
instance (st : Stack) (x : Blk) (extra : Nat) : Decidable (InPlace st x extra) := by
  unfold InPlace; infer_instance

/-- The grown block (DS-v2, non-normative: same base, `extra` more cells, new authority `a`,
destination `d`, the place that held the authority of the block, DS2-2; an issuance of §46). -/
def growBlk (x : Blk) (extra a d : Nat) : Blk := ⟨x.base, x.size + extra, a, d⟩

/-- Metadata after `grow` (DS-v2, non-normative; as the `ok` effect of §77 on §46 metadata): the
top rises by `extra`; the block is replaced by the grown block. -/
def growMeta (st : Stack) (x : Blk) (extra a d : Nat) : Stack :=
  { st with
    top := st.top + extra
    blocks := st.blocks.map fun y => if y.auth = x.auth then growBlk x extra a d else y }

/-- The place that holds authority `a`, if a place holds it (§42: holder; DS-v2, non-normative,
DS2-2: the destination of `grow` is the place that currently holds the block authority). -/
def holderPlace (s : S3) (a : Nat) : Option Nat :=
  match s.A[a]? with
  | some y => match y.holder with
    | .place v => some v
    | .frame _ => none
  | none => none

/-- `grow(j, b, extra)` (DS-v2, non-normative: in place only, using the derived `issue`): `reject`
when `b` is not a block of the stack or `extra` is zero; `release` of `b` (O3); then the derived
`issue` of Part XIV (`Arena.IssueD`) of the region of the same base and of size `size + extra` into
the place `d` that holds `b` when `grow` starts (DS2-2), on the released state: `reject` when no
place holds `b` (there is no destination, §77.2; never on library-reachable states,
`DReach.grow_holder`), its static checks (`IssueStatic`, §77.1, §77.2), `fail`, the state
unchanged, unless the extension is in place (DS-v1 "fail otherwise", availability §77.4), `split`
of `internal` (O2) and `store` of the new block into `d` (O8). -/
inductive GrowStep (k : K) (j b extra : Nat) (D : DState) : Outcome3 DState → Prop where
  | noStack : D.stacks[j]? = none → GrowStep k j b extra D .reject
  | noBlock {st : Stack} : D.stacks[j]? = some st → st.block b = none →
      GrowStep k j b extra D .reject
  | noExtra {st : Stack} {x : Blk} : D.stacks[j]? = some st → st.block b = some x → extra = 0 →
      GrowStep k j b extra D .reject
  | release {st : Stack} {x : Blk} : D.stacks[j]? = some st → st.block b = some x → 0 < extra →
      ReleaseStep b D.kern .reject → GrowStep k j b extra D .reject
  | noHolder {st : Stack} {x : Blk} {s₁ : S3} : D.stacks[j]? = some st → st.block b = some x →
      0 < extra → ReleaseStep b D.kern (.ok s₁) → holderPlace D.kern b = none →
      GrowStep k j b extra D .reject
  | static {st : Stack} {x : Blk} {s₁ : S3} {d : Nat} : D.stacks[j]? = some st →
      st.block b = some x → 0 < extra → ReleaseStep b D.kern (.ok s₁) →
      holderPlace D.kern b = some d →
      ¬ IssueStatic s₁ st.entry (cellsOf st x.base (x.size + extra)) d →
      GrowStep k j b extra D .reject
  | fail {st : Stack} {x : Blk} {s₁ : S3} {d : Nat} : D.stacks[j]? = some st →
      st.block b = some x → 0 < extra → ReleaseStep b D.kern (.ok s₁) →
      holderPlace D.kern b = some d →
      IssueStatic s₁ st.entry (cellsOf st x.base (x.size + extra)) d →
      ¬ InPlace st x extra → GrowStep k j b extra D .fail
  | split {st : Stack} {x : Blk} {s₁ : S3} {d : Nat} : D.stacks[j]? = some st →
      st.block b = some x → 0 < extra → ReleaseStep b D.kern (.ok s₁) →
      holderPlace D.kern b = some d →
      IssueStatic s₁ st.entry (cellsOf st x.base (x.size + extra)) d → InPlace st x extra →
      SplitStep k st.internal [cellsOf st x.base (x.size + extra)] s₁ .reject →
      GrowStep k j b extra D .reject
  | store {st : Stack} {x : Blk} {s₁ s₂ : S3} {d : Nat} : D.stacks[j]? = some st →
      st.block b = some x → 0 < extra → ReleaseStep b D.kern (.ok s₁) →
      holderPlace D.kern b = some d →
      IssueStatic s₁ st.entry (cellsOf st x.base (x.size + extra)) d → InPlace st x extra →
      SplitStep k st.internal [cellsOf st x.base (x.size + extra)] s₁ (.ok s₂) →
      StoreStep s₁.A.length d s₂ .reject → GrowStep k j b extra D .reject
  | ok {st : Stack} {x : Blk} {s₁ s₂ s₃ : S3} {d : Nat} : D.stacks[j]? = some st →
      st.block b = some x → 0 < extra → ReleaseStep b D.kern (.ok s₁) →
      holderPlace D.kern b = some d →
      IssueStatic s₁ st.entry (cellsOf st x.base (x.size + extra)) d → InPlace st x extra →
      SplitStep k st.internal [cellsOf st x.base (x.size + extra)] s₁ (.ok s₂) →
      StoreStep s₁.A.length d s₂ (.ok s₃) →
      GrowStep k j b extra D
        (.ok ⟨s₃, D.stacks.set j (growMeta st x extra s₁.A.length d), D.fresh⟩)

/-! ## Library runs (DS-v2; §36, §56, §57) -/

/-- One `ok` step of the stack library (DS-v2, non-normative): a kernel step O1–O16 of
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

/-- States reachable from the initial state by library steps (DS-v2, non-normative; §47). -/
inductive DReach (k : K) (statics : Statics) : DState → Prop where
  | init : DReach k statics (DState.init statics)
  | step {D D' : DState} : DReach k statics D → DStep k D D' → DReach k statics D'

/-- Finite sequences of library steps (DS-v2, non-normative; §58 `ok` transitions). -/
inductive DRun (k : K) : DState → DState → Prop where
  | refl (D : DState) : DRun k D D
  | tail {D D' D'' : DState} : DRun k D D' → DStep k D' D'' → DRun k D D''

/-- The kernel part of a library step is reached by kernel steps (§36: the abstraction adds no
rights to the kernel; Part XIV: `issue` is `split` then `store`, the reset part of `rewind` is
`split` then `release`; DS-v2). -/
theorem DStep.reachable {k : K} {statics : Statics} {D D' : DState}
    (hr : Reachable k statics D.kern) (h : DStep k D D') : Reachable k statics D'.kern := by
  cases h with
  | kernel hk => exact .step hr hk
  | newStack hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact hr
  | push hs =>
    cases hs with
    | ok _ _ _ hsp hst => exact .step (.step hr (.split hsp)) (.store hst)
  | mark hs => cases hs with | ok _ _ => exact hr
  | rewind hs =>
    cases hs with
    | ok _ _ _ hsp hrl => exact .step (.step hr (.split hsp)) (.release hrl)
  | grow hs =>
    cases hs with
    | ok _ _ _ hrl _ _ _ hsp hst =>
      exact .step (.step (.step hr (.release hrl)) (.split hsp)) (.store hst)

/-- The kernel state of every library-reachable state is kernel-reachable (§36, §57; DS-v2). -/
theorem DReach.reachable {k : K} {statics : Statics} {D : DState} (h : DReach k statics D) :
    Reachable k statics D.kern := by
  induction h with
  | init => exact .init
  | step _ hs ih => exact hs.reachable ih

/-! ## Helper lemmas (lists, kernel effects) -/

/-- Reading a list after `set` (support for the §46 metadata updates of DS-v2). -/
theorem getElem?_set_cases {α : Type} {l : List α} {j i : Nat} {v x : α}
    (h : (l.set j v)[i]? = some x) : (i = j ∧ x = v) ∨ (i ≠ j ∧ l[i]? = some x) := by
  rw [List.getElem?_set] at h
  by_cases hij : j = i
  · subst hij; simp only [↓reduceIte] at h; split at h
    · cases h; exact .inl ⟨rfl, rfl⟩
    · cases h
  · simp only [hij, ↓reduceIte] at h; exact .inr ⟨Ne.symm hij, h⟩

/-- Reading a list after appending one element (support for the §46 metadata updates of
DS-v2). -/
theorem getElem?_append_single {α : Type} {l : List α} {x y : α} {i : Nat}
    (h : (l ++ [x])[i]? = some y) : l[i]? = some y ∨ y = x := by
  rw [List.getElem?_append] at h
  split at h
  · exact .inl h
  · cases hc : i - l.length with
    | zero => rw [hc] at h; simp at h; exact .inr h.symm
    | succ n => rw [hc] at h; simp at h

/-- `takeWhile (· ≠ m)` stops at the first occurrence of `m` (support for the §46 metadata of
DS-v2 `rewind`). -/
theorem takeWhile_ne_append {m : Mark} : ∀ {pre : List Mark} (post : List Mark), m ∉ pre →
    (pre ++ m :: post).takeWhile (fun x => decide (x ≠ m)) = pre
  | [], post, _ => by simp
  | a :: pre, post, h => by
    have ha : a ≠ m := fun e => h (e ▸ List.mem_cons_self ..)
    have ih := takeWhile_ne_append (pre := pre) post (fun h' => h (List.mem_cons_of_mem _ h'))
    rw [List.cons_append, List.takeWhile_cons]
    simp only [ha, ne_eq, not_false_eq_true, decide_true, ↓reduceIte, ih]

/-- A prefix of `take` (support for DS-v2 `grow`, §46 metadata: the old cells are a prefix of the
new ones). -/
theorem take_prefix_take_add {α : Type} : ∀ (l : List α) (n e : Nat), l.take n <+: l.take (n + e)
  | [], n, e => ⟨[], by rw [List.take_nil, List.take_nil]; rfl⟩
  | _ :: _, 0, _ => ⟨_, List.nil_append _⟩
  | a :: l, n + 1, e => by
    obtain ⟨t, ht⟩ := take_prefix_take_add l n e
    exact ⟨t, by rw [Nat.add_right_comm, List.take_succ_cons, List.take_succ_cons,
      List.cons_append, ht]⟩

/-- The cells of a block are a prefix of the cells of the block grown from the same base (DS-v2,
non-normative, "same base"; §46 issued regions). -/
theorem cellsOf_prefix (st : Stack) (b n e : Nat) : cellsOf st b n <+: cellsOf st b (n + e) :=
  take_prefix_take_add _ _ _

/-- `release` keeps the identities of the authorities (§62, `ok` effect; support for DS-v2). -/
theorem releaseEff_len (s : S3) (a : Nat) : (releaseEff s a).A.length = s.A.length := by
  unfold releaseEff; split <;> simp

/-- `release` changes no initialization (§62, `ok` effect; support for DS-v2). -/
theorem releaseEff_I (s : S3) (a : Nat) : (releaseEff s a).I = s.I := by
  unfold releaseEff; split <;> rfl

/-- `release` changes no place (§62, `ok` effect; support for DS-v2). -/
theorem releaseEff_P (s : S3) (a : Nat) : (releaseEff s a).P = s.P := by
  unfold releaseEff; split <;> rfl

/-- The leaf `dst` of a usable place belongs to its own footprint (§40; support for DS-v2). -/
theorem mem_footprint_self {s : S3} {d : Nat} (hu : s.Usable d) (hl : isLeaf s.P d) :
    d ∈ footprint s.P d :=
  mem_footprint.2 ⟨hu.lt, hl, hu.lt, .inl rfl⟩

/-! ## `rewind` (DS-v2) -/

/-- `rewind_rejects_live_above` (DS-v2, non-normative: "rewind m … rejects if an active authority
derived from internal covers a cell above m"): for a live mark `m` of an existing stack (its stack
live, DS2-3), if an active authority derived from `internal` covers a cell above `m`, `rewind m`
has the outcome `reject` and no other: either the administrative right of §36 fails, or `split` of
`internal` on the cells above `m` is rejected, since `internal` no longer has effective `Modify` on
that cell (§43, §61.1). -/
theorem rewind_rejects_live_above {k : K} {D : DState} {j : Nat} {st : Stack} {m : Mark}
    (hst : D.stacks[j]? = some st) (hm : LiveMark D.kern j st m) {x l : Nat} {y : Authority}
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

/-- `rewind_keeps_older_marks` (DS-v2, non-normative: "otherwise returns those cells to available
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

/-! ## When `rewind` is `ok` (DS-v2) -/

/-- Anchors name existing authorities (support for DS-v2, non-normative, `rewind`; §44: `D(q)`
holds authority identities; §42: identities index `A`): every anchor of every place is an index of
`A`. -/
def DBound (s : S3) : Prop := ∀ q, ∀ x ∈ s.D q, x < s.A.length

/-- Every kernel step keeps `DBound` (support for DS-v2, non-normative; §60–§75 `ok` effects on
`D`, §42): each effect keeps, drops or moves existing anchors, adds an active authority (§64,
§65), or replaces an anchor by an element of its origin chain (§73); `A` never shrinks. -/
theorem kstep_dBound {k : K} {s s' : S3} (h : KStep k s s') (hb : DBound s) : DBound s' := by
  have hA := kstep_akeep h
  suffices H : ∀ q, ∀ x ∈ s'.D q, x < s.A.length from fun q x hx => hA.lt (H q x hx)
  cases h with
  | derive hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact hb
  | split hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact hb
  | release hs =>
    obtain ⟨hp, rfl⟩ := Guarded.ok_iff.1 hs
    obtain ⟨x, hx, -⟩ := hp.active
    rw [releaseEff_eq hx]; intro q z hz
    simp only at hz; split at hz
    · exact hb q z (List.mem_filter.1 hz).1
    · exact hb q z hz
  | transfer hs =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
    intro q z hz; simp only [transferEff] at hz; split at hz
    · cases hz
    · rcases List.mem_append.1 hz with hz | hz
      · exact hb q z hz
      · simp only [movedTo, List.mem_flatMap] at hz
        obtain ⟨r, -, hr⟩ := hz; exact hb r z hr
  | depend hs =>
    obtain ⟨hp, rfl⟩ := Guarded.ok_iff.1 hs
    intro q z hz; simp only [dependEff] at hz; split at hz
    · rcases List.mem_append.1 hz with hz | hz
      · exact hb _ z hz
      · rw [List.mem_singleton.1 hz]; obtain ⟨y, hy, -⟩ := hp.anchorActive; exact lt_of_getElem? hy
    · exact hb q z hz
  | enter hs =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
    intro q z hz; simp only [enterEff] at hz; split at hz
    · cases hz
    · exact hb q z hz
  | exit hs =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
    intro q z hz; simp only [exitEff, List.mem_map] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    have hxl := hb q x hx
    cases hf : firstSurv s s.F.tail (x :: s.ancs x) with
    | none => exact hxl
    | some w =>
      rcases List.mem_cons.1 (List.mem_of_find?_eq_some hf) with rfl | hw
      · exact hxl
      · exact Nat.lt_trans (chain_lt hw) hxl
  | read hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact hb
  | write hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact hb
  | writeShared hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact hb
  | pin hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact hb
  | unpin hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact hb
  | endUse hs =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
    intro q z hz; simp only [endUseEff, cleanup, endUseS] at hz; split at hz
    · cases hz
    · exact hb q z hz
  | free hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact hb
  | alloc hs =>
    cases hs with
    | ok =>
      intro q z hz; simp only [allocEff] at hz; split at hz
      · cases hz
      · exact hb q z hz
  | @store a p hs =>
    obtain ⟨hp, rfl⟩ := Guarded.ok_iff.1 hs
    have hd := hp.derivedHeld
    cases hy : s.A[a]? with
    | none => rw [hy] at hd; exact hd.elim
    | some y =>
      rw [storeEff_eq hy]; intro q z hz; simp only at hz; split at hz
      · rcases List.mem_append.1 hz with hz | hz
        · exact hb _ z hz
        · rw [List.mem_singleton.1 hz]; exact lt_of_getElem? hy
      · exact hb q z hz

/-- Every kernel-reachable state satisfies `DBound` (support for DS-v2, non-normative; §47: no
anchor initially; §57 reachable states). -/
theorem dBound_of_reachable {k : K} {statics : Statics} {s : S3} (h : Reachable k statics s) :
    DBound s := by
  induction h with
  | init => intro q x hx; simp [S3.init] at hx
  | step _ hs ih => exact kstep_dBound hs ih

/-- Shape of the `internal` authority of every stack (DS-v2, non-normative; §76.2: own mode
`Modify`; §76.3: its footprint contains the footprint of the storage, the cells of the stack; §42:
modes and footprints never change): it exists, has own mode `Modify` and covers every cell. -/
def StackShape (D : DState) : Prop :=
  ∀ (i : Nat) (st : Stack), D.stacks[i]? = some st →
    ∃ y : Authority, D.kern.A[st.internal]? = some y ∧ y.mode = .modify ∧
    ∀ c ∈ st.cells, c ∈ y.footprint

/-- The kernel part of a library step keeps every authority (DS-v2, non-normative; §42, `AKeep`;
Part XIV: the steps of `push`, `rewind`, `grow` are kernel steps). -/
theorem DStep.akeep {k : K} {D D' : DState} (h : DStep k D D') : AKeep D.kern D'.kern := by
  cases h with
  | kernel hk => exact kstep_akeep hk
  | newStack hs =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact akeep_append (List.append_nil _).symm
  | push hs =>
    cases hs with
    | ok _ _ _ hsp hst => exact (kstep_akeep (.split hsp)).trans (kstep_akeep (k := k) (.store hst))
  | mark hs => cases hs with | ok _ _ => exact akeep_append (List.append_nil _).symm
  | rewind hs =>
    cases hs with
    | ok _ _ _ hsp hrl =>
      exact (kstep_akeep (.split hsp)).trans (kstep_akeep (k := k) (.release hrl))
  | grow hs =>
    cases hs with
    | ok _ _ _ hrl _ _ _ hsp hst =>
      exact ((kstep_akeep (k := k) (.release hrl)).trans (kstep_akeep (.split hsp))).trans
        (kstep_akeep (k := k) (.store hst))

/-- `StackShape` is kept when the authorities are kept and each stack keeps its `internal` and
its cells (DS-v2, non-normative; §42, §46). -/
theorem stackShape_keep {D D' : DState} (hA : AKeep D.kern D'.kern) (hw : StackShape D)
    (hs : ∀ (i : Nat) (st' : Stack), D'.stacks[i]? = some st' →
      ∃ st : Stack, D.stacks[i]? = some st ∧ st'.internal = st.internal ∧ st'.cells = st.cells) :
    StackShape D' := by
  intro i st' h
  obtain ⟨st, hst, hi, hc⟩ := hs i st' h
  obtain ⟨y, hy, hm, hf⟩ := hw i st hst
  obtain ⟨y', hy', hm', hf', -⟩ := hA _ y hy
  exact ⟨y', hi ▸ hy', hm'.trans hm, fun c hc' => hf' ▸ hf c (hc ▸ hc')⟩

/-- Replacing stack `j` by a stack with the same `internal` and cells (DS-v2, non-normative; §46
metadata updates of `push`, `mark`, `rewind`, `grow`). -/
theorem set_keeps {l : List Stack} {j : Nat} {st st₀ : Stack} (hst : l[j]? = some st₀)
    (hi : st.internal = st₀.internal) (hc : st.cells = st₀.cells) :
    ∀ (i : Nat) (st' : Stack), (l.set j st)[i]? = some st' →
      ∃ st'' : Stack, l[i]? = some st'' ∧ st'.internal = st''.internal ∧
        st'.cells = st''.cells := by
  intro i st' h
  rcases getElem?_set_cases h with ⟨rfl, rfl⟩ | ⟨-, h⟩
  · exact ⟨st₀, hst, hi, hc⟩
  · exact ⟨st', h, rfl, rfl⟩

/-- Every library step keeps `StackShape` (DS-v2, non-normative; §76.2, §76.3 at `newStack`,
§42 afterwards). -/
theorem DStep.stackShape {k : K} {D D' : DState} (h : DStep k D D') (hw : StackShape D) :
    StackShape D' := by
  have hA := h.akeep
  cases h with
  | kernel => exact stackShape_keep hA hw fun i st' h => ⟨st', h, rfl, rfl⟩
  | @newStack _ _ _ int hs =>
    obtain ⟨hp, rfl⟩ := Guarded.ok_iff.1 hs
    intro i st' h
    rcases getElem?_append_single h with h | rfl
    · exact hw i st' h
    · have hi := hp.base.internalAuth
      cases hy : D.kern.A[int]? with
      | none => rw [hy] at hi; exact hi.elim
      | some y =>
        rw [hy] at hi
        refine ⟨y, hy, hi.2, fun c hc => ?_⟩
        have := hp.base.fpSup c hc; simpa [S3.afp, hy] using this
  | push hs => cases hs with | ok hst => exact stackShape_keep hA hw (set_keeps hst rfl rfl)
  | mark hs => cases hs with | ok hst => exact stackShape_keep hA hw (set_keeps hst rfl rfl)
  | rewind hs => cases hs with | ok hst => exact stackShape_keep hA hw (set_keeps hst rfl rfl)
  | grow hs => cases hs with | ok hst => exact stackShape_keep hA hw (set_keeps hst rfl rfl)

/-- Every library-reachable state satisfies `StackShape` (DS-v2, non-normative; §47: no stack
initially; §76.2, §76.3, §42). -/
theorem DReach.stackShape {k : K} {statics : Statics} {D : DState} (h : DReach k statics D) :
    StackShape D := by
  induction h with
  | init => intro i st h; simp [DState.init] at h
  | step _ hs ih => exact hs.stackShape ih

/-! ## The authority of every block is held by a place (DS-v2, DS2-2) -/

/-- The block authority issued by `split` of `src` on one region then `store` into `d` (§61, §65
`ok` effects; support for DS-v2, Part XIV derived `issue`): of fresh identity `|A|`, an active
`Modify` derived from `src` on the region, held by `d`. -/
theorem issued_block (s : S3) (src d : Nat) (R : List Nat) :
    (storeEff (splitEff s src [R]) s.A.length d).A[s.A.length]? =
      some ⟨.modify, some src, R, .place d, true⟩ := by
  rw [storeEff_eq (split_block s src R)]
  simp only
  rw [List.getElem?_set_self (by simp [splitEff])]

/-- Every block authority recorded by a stack is held by a place (support for DS-v2,
non-normative, DS2-2: `grow` stores into the place that holds the block authority; §42 holders;
§65 `ok` effect at `push` and `grow`). -/
def BlocksHeld (D : DState) : Prop :=
  ∀ (i : Nat) (st : Stack), D.stacks[i]? = some st → ∀ x ∈ st.blocks,
    ∃ y, D.kern.A[x.auth]? = some y ∧ y.holder.isPlace = true

/-- An authority held by a place stays held by a place (§42, `AKeep`; support for DS-v2). -/
theorem placeHeld_keep {s s' : S3} (hA : AKeep s s') {a : Nat}
    (h : ∃ y, s.A[a]? = some y ∧ y.holder.isPlace = true) :
    ∃ y, s'.A[a]? = some y ∧ y.holder.isPlace = true := by
  obtain ⟨y, hy, hp⟩ := h
  obtain ⟨y', hy', -, -, -, hp', -⟩ := hA a y hy
  refine ⟨y', hy', ?_⟩
  cases h : y'.holder.isPlace with
  | false => rw [hp' h] at hp; cases hp
  | true => rfl

/-- Every library step keeps `BlocksHeld` (DS-v2, non-normative; §42; §65 `ok` effect: `push` and
`grow` store the new block authority into a place). -/
theorem DStep.blocksHeld {k : K} {D D' : DState} (h : DStep k D D') (hw : BlocksHeld D) :
    BlocksHeld D' := by
  have keep : ∀ (i : Nat) (st : Stack), D.stacks[i]? = some st → ∀ x ∈ st.blocks,
      ∃ y, D'.kern.A[x.auth]? = some y ∧ y.holder.isPlace = true :=
    fun i st hst x hx => placeHeld_keep h.akeep (hw i st hst x hx)
  cases h with
  | kernel => exact keep
  | newStack hs =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
    intro i st h x hx
    rcases getElem?_append_single h with h | rfl
    · exact keep i st h x hx
    · simp at hx
  | push hs =>
    cases hs with
    | @ok st s₁ s₂ hst _ _ hsp hsto =>
      intro i st' h x hx
      rcases getElem?_set_cases h with ⟨rfl, rfl⟩ | ⟨-, h⟩
      · rcases List.mem_append.1 hx with hx | hx
        · exact keep _ st hst x hx
        · rw [List.mem_singleton.1 hx]
          obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hsp
          obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hsto
          exact ⟨_, issued_block _ _ _ _, rfl⟩
      · exact keep i st' h x hx
  | mark hs =>
    cases hs with
    | @ok st hst _ =>
      intro i st' h x hx
      rcases getElem?_set_cases h with ⟨rfl, rfl⟩ | ⟨-, h⟩
      · exact keep _ st hst x hx
      · exact keep i st' h x hx
  | rewind hs =>
    cases hs with
    | @ok st _ _ hst =>
      intro i st' h x hx
      rcases getElem?_set_cases h with ⟨rfl, rfl⟩ | ⟨-, h⟩
      · exact keep _ st hst x (List.mem_filter.1 hx).1
      · exact keep i st' h x hx
  | grow hs =>
    cases hs with
    | @ok st x₀ s₁ s₂ s₃ d hst _ _ _ _ _ _ hsp hsto =>
      intro i st' h x hx
      rcases getElem?_set_cases h with ⟨rfl, rfl⟩ | ⟨-, h⟩
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        by_cases hxy : y.auth = x₀.auth
        · simp only [hxy, ↓reduceIte]
          obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hsp
          obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hsto
          exact ⟨_, issued_block _ _ _ _, rfl⟩
        · simp only [hxy, ↓reduceIte]
          exact keep _ st hst y hy
      · exact keep i st' h x hx

/-- Every library-reachable state satisfies `BlocksHeld` (DS-v2, non-normative; §47: no stack
initially). -/
theorem DReach.blocksHeld {k : K} {statics : Statics} {D : DState} (h : DReach k statics D) :
    BlocksHeld D := by
  induction h with
  | init => intro i st h; simp [DState.init] at h
  | step _ hs ih => exact hs.blocksHeld ih

/-- On library-reachable states a place holds the authority of every block of a stack, so `grow`
always has a destination and `GrowStep.noHolder` never applies there (DS-v2, non-normative, DS2-2;
§42, §65). -/
theorem DReach.grow_holder {k : K} {statics : Statics} {D : DState} (h : DReach k statics D)
    {j b : Nat} {st : Stack} {x : Blk} (hst : D.stacks[j]? = some st) (hx : st.block b = some x) :
    ∃ d, holderPlace D.kern b = some d := by
  have hxb : x.auth = b := by simpa using List.find?_some hx
  obtain ⟨y, hy, hp⟩ := h.blocksHeld j st hst x (List.mem_of_find?_eq_some hx)
  rw [hxb] at hy
  unfold holderPlace; rw [hy]
  cases hh : y.holder with
  | place v => exact ⟨v, by simp [hh]⟩
  | frame f => rw [hh] at hp; cases hp

/-- The authority added by `split` of `src` on one region can be released at once (support for
DS-v2, non-normative, `rewind`; §62): it is active, derived, held by the current frame (§62.1,
§62.2), has no descendant (§62.3: origins precede, §42) and, under `DBound`, anchors no place
(§62.3, §62.4). -/
theorem release_after_split {s : S3} {src : Nat} {R : List Nat} (hb : DBound s) :
    ReleasePre (splitEff s src [R]) s.A.length := by
  have hy₀ := split_block s src R
  refine ⟨⟨_, hy₀, rfl⟩, by rw [hy₀]; simp [OptP], by rw [hy₀]; exact rfl,
    fun j hj hn => ?_, fun q _ _ hx => absurd (hb q _ hx) (Nat.lt_irrefl _)⟩
  have := chain_lt hn
  have := List.mem_range.1 hj; simp [splitEff] at this; omega

/-- `rewind_ok_iff` (DS-v2, non-normative: "rewind m fails on a dead or foreign mark, rejects if an
active authority derived from internal covers a cell above m, otherwise returns those cells to
available"; §36; §61.1, §61.3, §62 through Part XIV). On a library-reachable state (`DReach`, a
state invariant), for an existing stack, `rewind m` is `ok` exactly when `m` is a live mark of the
stack (DS-v2: its stack is live, DS2-3), the administrative right of §36 holds (`AdminRight`,
DS-v2, Q27 (a)), and no active authority derived from `internal` covers a cell above `m` (DS-v2).
The model has no explicit check of the last condition: it is the effective `Modify` of `internal`
required by `split` (§61.1, with the effective mode of §43). The other checks of `split` and
`release` never reject there: `internal` has own mode `Modify` and covers the cells
(`DReach.stackShape`, §76.2, §76.3), and anchors name existing authorities
(`dBound_of_reachable`). With `RewindStep.det`, `ok` is then the only outcome. -/
theorem rewind_ok_iff {k : K} {statics : Statics} {D : DState} (hr : DReach k statics D)
    {j : Nat} {st : Stack} (hst : D.stacks[j]? = some st) {m : Mark} :
    (∃ D', RewindStep k j m D (.ok D')) ↔
      LiveMark D.kern j st m ∧ AdminRight D.kern st ∧
        ∀ (x l : Nat) (y : Authority), D.kern.A[x]? = some y → y.active = true →
          st.internal ∈ D.kern.ancs x → l ∈ y.footprint → l ∉ above st m := by
  constructor
  · rintro ⟨D', h⟩
    cases h with
    | ok h hm ha hsp =>
      rw [hst] at h; cases h
      have hp := (Guarded.ok_iff.1 hsp).1
      exact ⟨hm, ha, fun x l y hy ya hx hly hl =>
        no_desc_of_modify hy ya hly hx (hp.modifyOn _ (List.mem_singleton_self _) l hl)⟩
  · rintro ⟨hm, ha, hno⟩
    obtain ⟨yi, hyi, hmi, hci⟩ := hr.stackShape j st hst
    have yia : yi.active = true := by
      obtain ⟨y, hy, ya⟩ := ha.1; rw [hyi] at hy; cases hy; exact ya
    have hab : ∀ l ∈ above st m, l ∈ yi.footprint :=
      fun l hl => hci l (List.mem_of_mem_drop (List.mem_of_mem_take hl))
    have hmod : ∀ l ∈ above st m, effective D.kern st.internal l = some .modify := by
      intro l hl
      have hd : descModes D.kern st.internal l = [] := by
        apply nil_of_forall_not_mem; intro e he
        obtain ⟨x, y, hy, ya, hly, hx, -⟩ := mem_descModes.1 he
        exact hno x l y hy ya hx hly hl
      rw [effective_eq hyi yia (hab l hl), hd]; simp [effOf, hmi]
    have hex : D.kern.ExercisableAt st.internal .modify := by
      have hmr := ha.2
      simp only [MetaRight, arenaValue, Stack.entry, hyi] at hmr
      cases hv : yi.holder with
      | frame f => rw [hv] at hmr; exact hmr.elim
      | place v =>
        rw [hv] at hmr
        obtain ⟨b, -, hb, hall⟩ := hmr
        exact .held hyi yia (.inr hmi) hv hb hall
    have hsp : SplitPre k D.kern st.internal [above st m] := by
      refine ⟨ha.1, hex, fun r hr p hp => ?_, fun r hr p hp => ?_, List.pairwise_singleton _ _,
        fun r hr p hp x _ hd => ?_⟩
      · rw [List.mem_singleton.1 hr] at hp; exact hmod p hp
      · rw [List.mem_singleton.1 hr] at hp
        exact ⟨by simp only [S3.afp, hyi]; exact hab p hp, by rw [hmod p hp]; simp⟩
      · rw [List.mem_singleton.1 hr] at hp
        unfold DistribExcl at hd
        cases hx : D.kern.A[x]? with
        | none => rw [hx] at hd; exact hd
        | some y =>
          rw [hx] at hd; obtain ⟨ya, hanc, hpy, -⟩ := hd; exact hno x p y hx ya hanc hpy hp
    exact ⟨_, .ok hst hm ha (.ok hsp)
      (.ok (release_after_split (dBound_of_reachable hr.reachable)))⟩

/-! ## Marks are never reused (`mark_no_aba`) -/

/-- Well-formed marks (DS-v2, non-normative, "marks carry stack identity and a fresh mark
identifier"; support; library metadata, §38): the live marks of stack `i` are pairwise distinct,
name stack `i`, and have identifiers already given out. -/
def MarksWF (D : DState) : Prop :=
  ∀ (i : Nat) (st : Stack), D.stacks[i]? = some st →
    st.marks.Nodup ∧ ∀ m ∈ st.marks, m.stack = i ∧ m.id < D.fresh

/-- A removed mark (DS-v2, non-normative; support; library metadata, §38): its identifier was
given out and it is live in no stack. -/
def Gone (D : DState) (m : Mark) : Prop :=
  m.id < D.fresh ∧ ∀ (i : Nat) (st : Stack), D.stacks[i]? = some st → m ∉ st.marks

/-- The initial state has well-formed marks (DS-v2, §47). -/
theorem marksWF_init (statics : Statics) : MarksWF (DState.init statics) := fun i st h => by
  simp [DState.init] at h

/-- Replacing stack `j` by a stack whose marks are a sublist keeps `MarksWF` when no identifier is
taken back (DS-v2; §38 library metadata). -/
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

/-- Replacing stack `j` by a stack whose marks are a sublist keeps a removed mark removed (DS-v2;
§38 library metadata). -/
theorem gone_set {D D' : DState} {j : Nat} {st st' : Stack} {m : Mark} (hg : Gone D m)
    (hst : D.stacks[j]? = some st) (hs : D'.stacks = D.stacks.set j st')
    (hsub : ∀ x ∈ st'.marks, x ∈ st.marks) (hf : D.fresh ≤ D'.fresh) : Gone D' m := by
  refine ⟨by have := hg.1; omega, fun i st'' h hm => ?_⟩
  rw [hs] at h
  rcases getElem?_set_cases h with ⟨rfl, rfl⟩ | ⟨-, h⟩
  · exact hg.2 _ st hst (hsub m hm)
  · exact hg.2 i st'' h hm

/-- Every library step keeps `MarksWF` (DS-v2; §38 library metadata). -/
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
    | @ok st hst _ =>
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

/-- Every library-reachable state has well-formed marks (DS-v2; §47 initial state). -/
theorem DReach.marksWF {k : K} {statics : Statics} {D : DState} (h : DReach k statics D) :
    MarksWF D := by
  induction h with
  | init => exact marksWF_init statics
  | step _ hs ih => exact hs.marksWF ih

/-- Every library step keeps a removed mark removed: identifiers are fresh (DS-v2; §38 library
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
    | @ok st hst _ =>
      refine ⟨Nat.lt_succ_of_lt hg.1, fun i st' h hm => ?_⟩
      rcases getElem?_set_cases h with ⟨rfl, rfl⟩ | ⟨-, h⟩
      · rcases List.mem_append.1 hm with hm | hm
        · exact hg.2 _ st hst hm
        · rw [List.mem_singleton] at hm; rw [hm] at hg; exact Nat.lt_irrefl _ hg.1
      · exact hg.2 i st' h hm

/-- Every run keeps a removed mark removed (DS-v2; §38 library metadata). -/
theorem DRun.gone {k : K} {D D' : DState} {m : Mark} (h : DRun k D D') (hg : Gone D m) :
    Gone D' m := by
  induction h with
  | refl => exact hg
  | tail _ hs ih => exact hs.gone ih

/-- `rewind` of a mark that is not live for an existing stack (dead, foreign, or of a dead stack)
fails, with no other outcome, whatever the rights of the current frame (DS-v2, non-normative:
"rewind m fails on a dead or foreign mark", checked before the right of §36; §58 `fail`). -/
theorem rewind_dead_fails {k : K} {D : DState} {i : Nat} {st : Stack} {m : Mark}
    (hst : D.stacks[i]? = some st) (hm : ¬ LiveMark D.kern i st m) :
    RewindStep k i m D .fail ∧ ∀ o, RewindStep k i m D o → o = .fail := by
  refine ⟨.dead hst hm, fun o ho => ?_⟩
  cases ho with
  | noStack h => rw [hst] at h; cases h
  | dead => rfl
  | static h hl => rw [hst] at h; cases h; exact absurd hl hm
  | split h hl => rw [hst] at h; cases h; exact absurd hl hm
  | release h hl => rw [hst] at h; cases h; exact absurd hl hm
  | ok h hl => rw [hst] at h; cases h; exact absurd hl hm

/-- `rewind_dead_stack_fails` (DS-v2, non-normative, DS2-3: a dead stack invalidates its marks;
§46 read for a stack: the stack is live if `internal` is active; §58 `fail`): on an existing stack
whose `internal` is inactive, `rewind m` fails, with no other outcome, for every mark `m` and
whatever the rights of the current frame. -/
theorem rewind_dead_stack_fails {k : K} {D : DState} {j : Nat} {st : Stack} {m : Mark}
    (hst : D.stacks[j]? = some st) (hd : ¬ D.kern.Active st.internal) :
    RewindStep k j m D .fail ∧ ∀ o, RewindStep k j m D o → o = .fail :=
  rewind_dead_fails hst fun h => hd h.1

/-- `mark_no_aba` (DS-v2, non-normative: marks carry a fresh identifier; `rewind m` removes `m` and
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
  exact ⟨hg'.2, fun i st' h => rewind_dead_fails h fun hl => hg'.2 i st' h hl.2.2⟩

/-! ## `grow` (DS-v2) -/

/-- `grow_same_base` (DS-v2, non-normative: "grow is in place only (same base, extension into the
space directly after the block)"; DS2-2: the new block authority goes to the place that currently
holds `b`): an `ok` of `grow b extra` grows the block of authority `b` of the stack in place:
`extra` is positive and the extension is in place; the metadata records the grown block of the
same base, `extra` more cells, the new authority and, as destination, the place `d` that held `b`
when `grow` started; in the arrival state that authority, of fresh identity, is an active `Modify`
derived from `internal` covering the cells from the same base and held by `d` (§61, §65 `ok`
effects); the old cells are a prefix of the new ones; `b` is inactive (§62). -/
theorem grow_same_base {k : K} {D D' : DState} {j b extra : Nat}
    (h : GrowStep k j b extra D (.ok D')) :
    ∃ st x d, D.stacks[j]? = some st ∧ st.block b = some x ∧ 0 < extra ∧ InPlace st x extra ∧
      holderPlace D.kern b = some d ∧
      D'.stacks[j]? = some (growMeta st x extra D.kern.A.length d) ∧
      growBlk x extra D.kern.A.length d ∈ (growMeta st x extra D.kern.A.length d).blocks ∧
      D'.kern.A[D.kern.A.length]? =
        some ⟨.modify, some st.internal, cellsOf st x.base (x.size + extra), .place d, true⟩ ∧
      cellsOf st x.base x.size <+: cellsOf st x.base (x.size + extra) ∧
      ¬ D'.kern.Active b := by
  cases h with
  | @ok st x s₁ s₂ s₃ d hst hx hpos hrl hd hstat hin hsp hsto =>
    obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 hrl
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hsp
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hsto
    have hlen := releaseEff_len D.kern b
    obtain ⟨yb, hyb, -⟩ := hpre.active
    have hbl : b < D.kern.A.length := lt_of_getElem? hyb
    have hblk := split_block (releaseEff D.kern b) st.internal (cellsOf st x.base (x.size + extra))
    have hnew :=
      issued_block (releaseEff D.kern b) st.internal d (cellsOf st x.base (x.size + extra))
    rw [hlen] at hblk hnew ⊢
    refine ⟨st, x, d, hst, hx, hpos, hin, hd, List.getElem?_set_self (lt_of_getElem? hst),
      List.mem_map.2 ⟨x, List.mem_of_find?_eq_some hx, by simp⟩, hnew, cellsOf_prefix st _ _ _, ?_⟩
    rintro ⟨y, hy, ya⟩
    rw [storeEff_eq hblk] at hy
    simp only at hy
    rw [List.getElem?_set_ne (by omega)] at hy
    simp only [splitEff, List.map_cons, List.map_nil] at hy
    rw [List.getElem?_append_left (by rw [hlen]; exact hbl), releaseEff_eq hyb,
      List.getElem?_set_self hbl] at hy
    cases hy; simp at ya

/-- `grow_keeps_prefix_init` (DS-v2, non-normative; §62, §61, §65 `ok` effects): `grow` changes the
initialization of no cell of the old block: `release` and `split` change no initialization, and
`store` initializes only its destination, the place that held `b` (DS2-2), which the new block does
not cover (§65.3). -/
theorem grow_keeps_prefix_init {k : K} {D D' : DState} {j b extra : Nat}
    (h : GrowStep k j b extra D (.ok D')) {st : Stack} {x : Blk} (hst : D.stacks[j]? = some st)
    (hx : st.block b = some x) : ∀ l ∈ cellsOf st x.base x.size, D'.kern.I l = D.kern.I l := by
  cases h with
  | @ok _ _ _ _ _ d hst₀ hx₀ _ hrl _ _ _ hsp hsto =>
    rw [hst] at hst₀; cases hst₀; rw [hx] at hx₀; cases hx₀
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hrl
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hsp
    obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 hsto
    intro l hl
    have hblk := split_block (releaseEff D.kern b) st.internal (cellsOf st x.base (x.size + extra))
    have hlr : l ∈ (splitEff (releaseEff D.kern b) st.internal
        [cellsOf st x.base (x.size + extra)]).afp (releaseEff D.kern b).A.length := by
      simp only [S3.afp, hblk]; exact (cellsOf_prefix st x.base x.size extra).subset hl
    have hne : l ≠ d := fun he =>
      (hpre.noCover l hlr).1 (by rw [he]; exact mem_footprint_self hpre.usable hpre.leaf)
    rw [storeEff_eq hblk]
    simp only [hne, ↓reduceIte]
    show (releaseEff D.kern b).I l = _; rw [releaseEff_I]

/-! ## Bytes of the old block after `grow` (refinement, §82) -/

/-- A raw write into the range of leaf `d` leaves the bytes of the range of a leaf `l` in another
allocation or with a disjoint range unchanged (§16 ¶3, §82.1; support for DS-v2 `grow`). -/
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

/-- `grow_keeps_prefix_bytes` (DS-v2, non-normative; through the refinement of Part XVII, §82): an
`ok` of `grow b extra` is the kernel steps `release(b)`, `split(internal, [region])` and
`store(|A|, d)`, `d` the place that held `b` (DS2-2); their realization in the memory machine
(`Refinement.opsOf`) has no raw operation for `release` and `split` (§62, §61), and the raw
operations of `store` (one write into the range of `d`, §82.3) leave the bytes, values and
provenances, of every cell of the old block unchanged, for every layout satisfying the layout
interface `LayoutWF` (§82.1, §23) in the state before the step. -/
theorem grow_keeps_prefix_bytes {Ty : Type} {k : K} {D D' : DState} {j b extra : Nat}
    (h : GrowStep k j b extra D (.ok D')) {st : Stack} {x : Blk} (hst : D.stacks[j]? = some st)
    (hx : st.block b = some x) :
    ∃ s₁ s₂ d, holderPlace D.kern b = some d ∧ Refinement.OpStep k (.release b) D.kern s₁ ∧
      Refinement.OpStep k (.split st.internal [cellsOf st x.base (x.size + extra)]) s₁ s₂ ∧
      Refinement.OpStep k (.store D.kern.A.length d) s₂ D'.kern ∧
      ∀ (π : Refinement.Params Ty) (s2 : Machine.State), Refinement.LayoutWF π.L D.kern s2 →
        Refinement.opsOf π (.release b) D.kern s2 = [] ∧
        Refinement.opsOf π (.split st.internal [cellsOf st x.base (x.size + extra)]) s₁ s2 = [] ∧
        ∀ l ∈ cellsOf st x.base x.size, ∀ i < (π.L l).len,
          Refinement.bytesOf
            (Refinement.run s2 (Refinement.opsOf π (.store D.kern.A.length d) s₂ s2)) π.L l i =
          Refinement.bytesOf s2 π.L l i := by
  cases h with
  | @ok st₀ x₀ s₁ s₂ s₃ d hst₀ hx₀ hpos hrl hd hstat hin hsp hsto =>
    rw [hst] at hst₀; cases hst₀; rw [hx] at hx₀; cases hx₀
    have hlen : s₁.A.length = D.kern.A.length := by
      rw [(Guarded.ok_iff.1 hrl).2]; exact releaseEff_len D.kern b
    have hP₁ : s₁.P = D.kern.P := by rw [(Guarded.ok_iff.1 hrl).2]; exact releaseEff_P D.kern b
    have hP₂ : s₂.P = D.kern.P := by rw [(Guarded.ok_iff.1 hsp).2, ← hP₁]; rfl
    rw [hlen] at hsto
    refine ⟨s₁, s₂, d, hd, hrl, hsp, hsto, fun π s2 hlw => ⟨rfl, rfl, fun l hl i hi => ?_⟩⟩
    obtain ⟨hpre, -⟩ := Guarded.ok_iff.1 hsto
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hsp
    have hblk := split_block s₁ st.internal (cellsOf st x.base (x.size + extra))
    rw [hlen] at hblk
    have hlr' : l ∈ cellsOf st x.base (x.size + extra) :=
      (cellsOf_prefix st x.base x.size extra).subset hl
    have hlr : l ∈ (splitEff s₁ st.internal [cellsOf st x.base (x.size + extra)]).afp
        D.kern.A.length := by simp only [S3.afp, hblk]; exact hlr'
    have hne : l ≠ d := fun he =>
      (hpre.noCover l hlr).1 (by rw [he]; exact mem_footprint_self hpre.usable hpre.leaf)
    obtain ⟨hlP, hlleaf, -⟩ := mem_footprint.1 (hstat.regionIn l hlr')
    rw [hP₁] at hlP hlleaf
    have hdP : d < D.kern.P.length := hP₂ ▸ hpre.usable.lt
    have hdleaf : isLeaf D.kern.P d := hP₂ ▸ hpre.leaf
    have hdis : (π.L l).alloc ≠ (π.L d).alloc ∨
        Machine.RangeDisjoint (π.L l).off (π.L l).len (π.L d).off (π.L d).len := by
      by_cases ha : (π.L l).alloc = (π.L d).alloc
      · exact .inr (hlw.disjoint l d hlP hdP hlleaf hdleaf hne ha)
      · exact .inl ha
    simp only [Refinement.opsOf, Refinement.storeOps, Refinement.writeOps, List.map_cons,
      List.map_nil, Refinement.run, Refinement.opEff]
    exact bytesOf_write_other hdis hi

/-! ## Non-vacuity: a concrete run (DS-v2)

A run from `DState.init wst` under the test contract `Access.Examples.K0` (§48). Statics (§47):
leaf 0 (`Init`) is the stack value; place 1 is the storage, with the cells 2 and 3; leaves 4 and 5
are destinations; root authorities 0, 1, 2, 3 on the roots 0, 1, 4, 5, held by frame 0. Every
precondition is decided by `decide`. -/

namespace Witness

open Examples

/-- The statics of the run (§47; DS-v2 non-vacuity): stack value 0, storage 1 with cells 2 and 3,
destinations 4 and 5. -/
def wst : Statics :=
  [((none, none, 0), true), ((none, none, 0), false), ((some 1, none, 0), false),
    ((some 1, none, 0), false), ((none, none, 0), false), ((none, none, 0), false)]

/-- Initial state (§47; DS-v2 non-vacuity). -/
def d0 : DState := DState.init wst
/-- `derive(1, [2, 3], Modify)`: authority 4, held by frame 0 (§60; DS-v2 non-vacuity). -/
def d1 : DState := ⟨deriveEff d0.kern 1 [2, 3] .modify, d0.stacks, d0.fresh⟩
/-- `store(4, 0)`: authority 4 becomes `internal`, held by the stack value 0 (§65; DS-v2
non-vacuity). -/
def d2 : DState := ⟨storeEff d1.kern 4 0, d1.stacks, d1.fresh⟩
/-- `newStack(1, 4)` (DS-v2, §56). -/
def d3 : DState := newStackEff d2 1 4
/-- The stack registered by `newStack(1, 4)` (DS-v2, §46). -/
def st3 : Stack := ⟨1, 4, footprint d2.kern.P 1, 0, [], []⟩
/-- `mark(0)`: mark `⟨0, 0, 0⟩` (DS-v2, §58). -/
def d4 : DState := ⟨d3.kern, d3.stacks.set 0 (markMeta 0 st3 d3.fresh), d3.fresh + 1⟩
/-- The stack after the first mark (DS-v2, §46). -/
def st4 : Stack := markMeta 0 st3 d3.fresh
/-- `push(0, 1, 4)`: `split(4, [[2]])`, `store(5, 4)` (DS-v2, Part XIV, §77). -/
def d5 : DState :=
  ⟨storeEff (splitEff d4.kern st4.internal [cellsOf st4 st4.top 1]) d4.kern.A.length 4,
    d4.stacks.set 0 (pushMeta st4 1 d4.kern.A.length 4), d4.fresh⟩
/-- The stack after the first push: block `⟨0, 1, 5, 4⟩` (DS-v2, §46). -/
def st5 : Stack := pushMeta st4 1 d4.kern.A.length 4
/-- `mark(0)`: mark `⟨0, 1, 1⟩` (DS-v2, §58). -/
def d6 : DState := ⟨d5.kern, d5.stacks.set 0 (markMeta 0 st5 d5.fresh), d5.fresh + 1⟩
/-- The stack after the second mark (DS-v2, §46). -/
def st6 : Stack := markMeta 0 st5 d5.fresh
/-- `push(0, 1, 5)`: `split(4, [[3]])`, `store(6, 5)` (DS-v2, Part XIV, §77). -/
def d7 : DState :=
  ⟨storeEff (splitEff d6.kern st6.internal [cellsOf st6 st6.top 1]) d6.kern.A.length 5,
    d6.stacks.set 0 (pushMeta st6 1 d6.kern.A.length 5), d6.fresh⟩
/-- The stack after the second push: blocks `⟨0, 1, 5, 4⟩`, `⟨1, 1, 6, 5⟩` (DS-v2, §46). -/
def st7 : Stack := pushMeta st6 1 d6.kern.A.length 5
/-- `release(6)` by the program (§62; DS-v2 non-vacuity). -/
def d8 : DState := ⟨releaseEff d7.kern 6, d7.stacks, d7.fresh⟩
/-- The second mark (DS-v2, §58). -/
def m1 : Mark := ⟨0, 1, 1⟩
/-- `rewind(0, ⟨0, 1, 1⟩)`: `split(4, [[3]])`, `release(7)` (DS-v2, §61, §62). -/
def d9 : DState :=
  ⟨releaseEff (splitEff d8.kern st7.internal [above st7 m1]) d8.kern.A.length,
    d8.stacks.set 0 (rewindMeta st7 m1), d8.fresh⟩
/-- The stack after the rewind (DS-v2, §46). -/
def st9 : Stack := rewindMeta st7 m1
/-- The block of authority 5 (DS-v2, §46). -/
def x5 : Blk := ⟨0, 1, 5, 4⟩
/-- `grow(0, 5, 1)`: `release(5)`, `split(4, [[2, 3]])`, `store(8, 4)` into place 4, which holds
block authority 5 (DS-v2, DS2-2, Part XIV, §77). -/
def d10 : DState :=
  ⟨storeEff (splitEff (releaseEff d9.kern 5) st9.internal [cellsOf st9 x5.base (x5.size + 1)])
      (releaseEff d9.kern 5).A.length 4,
    d9.stacks.set 0 (growMeta st9 x5 1 (releaseEff d9.kern 5).A.length 4), d9.fresh⟩

/-- The run up to `newStack` is library-reachable (DS-v2; §47, §60, §65, §56). -/
theorem d3_reach : DReach K0 wst d3 :=
  .step (.step (.step .init (.kernel (.derive (.ok (by decide)))))
    (.kernel (.store (.ok (by decide))))) (.newStack (others := []) (.ok (by decide)))

/-- The run up to the first push is library-reachable (DS-v2, DS2-1: `mark` with the right of §36;
Part XIV derived `issue`, §77). -/
theorem d5_reach : DReach K0 wst d5 :=
  .step (.step d3_reach (.mark (.ok (st := st3) (by decide) (by decide))))
    (.push (.ok (st := st4) (by decide) (by decide) (by decide) (.ok (by decide))
      (.ok (by decide))))

/-- The run up to the second push is library-reachable (DS-v2; §47, Part XIV derived `issue`,
§77). -/
theorem d7_reach : DReach K0 wst d7 :=
  .step (.step d5_reach (.mark (.ok (st := st5) (by decide) (by decide))))
    (.push (.ok (st := st6) (by decide) (by decide) (by decide) (.ok (by decide))
      (.ok (by decide))))

/-- The run up to the rewind is library-reachable (DS-v2; §62, Part XIV derived `reset`, §78). -/
theorem d9_reach : DReach K0 wst d9 :=
  .step (.step d7_reach (.kernel (.release (.ok (by decide)))))
    (.rewind (.ok (st := st7) (by decide) (by decide) (by decide) (.ok (by decide))
      (.ok (by decide))))

/-- **Non-vacuity of the DS-v2 operations** (§58 outcomes). In `d7`, `rewind ⟨0, 1, 1⟩` is
rejected: block 6, derived from `internal` 4, covers cell 3 above the mark
(`rewind_rejects_live_above`); `grow` of block 5, which is not at the top, fails (DS-v1 "fail
otherwise"). After the program releases 6, `rewind ⟨0, 1, 1⟩` is `ok`: the top returns to 1,
the older mark stays; the removed mark then fails (`mark_no_aba`). `grow` of block 5 by one cell
is then `ok` in place: block `⟨0, 2, 8, 4⟩`, whose authority 8 covers the cells 2 and 3 and is
held by place 4, the holder of block authority 5. -/
theorem run_ok :
    DReach K0 wst d10 ∧
    RewindStep K0 0 m1 d7 .reject ∧ GrowStep K0 0 5 1 d7 .fail ∧
    d9.stacks = [⟨1, 4, [2, 3], 1, [x5], [⟨0, 0, 0⟩]⟩] ∧ RewindStep K0 0 m1 d9 .fail ∧
    d10.stacks = [⟨1, 4, [2, 3], 2, [⟨0, 2, 8, 4⟩], [⟨0, 0, 0⟩]⟩] ∧ d10.kern.afp 8 = [2, 3] := by
  have r10 : DReach K0 wst d10 := .step d9_reach
    (.grow (.ok (st := st9) (x := x5) (d := 4) (by decide) (by decide) (by decide)
      (.ok (by decide)) (by decide) (by decide) (by decide) (.ok (by decide)) (.ok (by decide))))
  have hrej := (rewind_rejects_live_above (k := K0) (D := d7) (j := 0) (st := st7) (m := m1)
    (x := 6) (l := 3) (y := ⟨.modify, some 4, [3], .place 5, true⟩) (by decide) (by decide)
    (by decide) rfl (by decide) (by decide) (by decide)).1
  have hfail : GrowStep K0 0 5 1 d7 .fail :=
    .fail (st := st7) (x := x5) (d := 4) (by decide) (by decide) (by decide) (.ok (by decide))
      (by decide) (by decide) (by decide)
  exact ⟨r10, hrej, hfail, by decide, (rewind_dead_fails (st := st9) (by decide) (by decide)).1,
    by decide, by decide⟩

/-! ### Examples of DS-v2 and the remaining readings

Each theorem below shows, on a library-reachable state, a program whose verdict or arrival state
is fixed by a DS-v2 item (DS2-1 to DS2-3, or an item of DS-v1 decided by the arbitration), or, for
the theorems named `reading_*`, depends on a reading of DS-v2 whose status is open: Q23 says that
Q11, Q27 and Q28 decide DS-R1 to DS-R13, but none of their items names DS-R1 or DS-R4, and both
readings change a verdict. Each such theorem shows the verdict of the draft reading formalized here,
and the facts that make the other reading give another one. -/

/-- `release(5)` by the program, after the rewind (§62; DS-v2 non-vacuity). -/
def d11 : DState := ⟨releaseEff d9.kern 5, d9.stacks, d9.fresh⟩
/-- `derive(4, [3], Modify)` by the program: authority 8 on cell 3, above the current top (§60;
DS-v2 reading of "above"). -/
def d12 : DState := ⟨deriveEff d11.kern 4 [3] .modify, d11.stacks, d11.fresh⟩
/-- The first mark (DS-v2, §58). -/
def m0 : Mark := ⟨0, 0, 0⟩
/-- A callee frame with no parameter and no local, entered after the rewind (§72; DS-v2 order of
the dead-mark `fail` and of the right of §36). -/
def d13 : DState := ⟨enterEff d9.kern [] [], d9.stacks, d9.fresh⟩

/-- The run up to the program's `release(5)` is library-reachable (DS-v2; §62). -/
theorem d11_reach : DReach K0 wst d11 := .step d9_reach (.kernel (.release (.ok (by decide))))

/-- The callee of `d13` is library-reachable (DS-v2; §72). -/
theorem d13_reach : DReach K0 wst d13 := .step d9_reach (.kernel (.enter (.ok (by decide))))

/-- **Reading of "a cell above m"** (DS-v2, non-normative; reading DS-R1, open: no item of Q11,
Q27 or Q28 names it; §46). In `d12`, authority 8, active and derived from `internal` 4, covers cell 3, at a
position above the top of mark `⟨0, 0, 0⟩` but above the current top too, hence not among the
cells `rewind` returns (`above`): `rewind ⟨0, 0, 0⟩` is `ok`. Under the reading "any cell at a
position at or above the top of `m`", it is rejected. -/
theorem reading_above :
    DReach K0 wst d12 ∧ d12.kern.A[8]? = some ⟨.modify, some 4, [3], .frame 0, true⟩ ∧
    st9.internal ∈ d12.kern.ancs 8 ∧ 3 ∈ st9.cells.drop m0.top ∧ 3 ∉ above st9 m0 ∧
    ∃ D', RewindStep K0 0 m0 d12 (.ok D') :=
  ⟨.step d11_reach (.kernel (.derive (.ok (by decide)))), by decide, by decide, by decide,
    by decide,
    ⟨_, .ok (st := st9) (by decide) (by decide) (by decide) (.ok (by decide)) (.ok (by decide))⟩⟩

/-- **The dead or foreign mark is checked before the right** (DS-v2, non-normative: DS-v1 decided
by Q11 (f); §36, §58). In `d13`, a callee with no right on the stack value (`¬ AdminRight`)
rewinds to the removed mark `⟨0, 1, 1⟩`: the outcome is `fail` and no other. -/
theorem dead_mark_before_right :
    DReach K0 wst d13 ∧ ¬ AdminRight d13.kern st9 ∧
    RewindStep K0 0 m1 d13 .fail ∧ ∀ o, RewindStep K0 0 m1 d13 o → o = .fail :=
  ⟨d13_reach, by decide, rewind_dead_fails (st := st9) (by decide) (by decide)⟩

/-- **`push` without room fails** (DS-v2, non-normative: DS-v1 decided by Q11 (a); availability,
§77.4). In `d3`, `push(0, 3, 4)` asks for more cells than the storage has: `fail`, although the
requested cells are not all in the storage. -/
theorem push_no_room : DReach K0 wst d3 ∧ PushStep K0 0 3 4 d3 .fail :=
  ⟨d3_reach, .fail (st := st3) (by decide) (by decide) (by decide)⟩

/-- **Reading of `grow` with `extra = 0`** (DS-v2, non-normative; reading DS-R4, open: no item of Q11,
Q27 or Q28 names it; §58). In `d9`, `grow(0, 5, 0)` is rejected (`extra = 0`), while the sequence `release`,
static checks into place 4, the holder of block authority 5 (DS2-2), in-place check, `split` and
`store` of the same region would be `ok`. -/
theorem reading_grow_zero :
    DReach K0 wst d9 ∧ GrowStep K0 0 5 0 d9 .reject ∧ holderPlace d9.kern 5 = some 4 ∧
    ReleaseStep 5 d9.kern (.ok (releaseEff d9.kern 5)) ∧
    IssueStatic (releaseEff d9.kern 5) st9.entry (cellsOf st9 x5.base (x5.size + 0)) 4 ∧
    InPlace st9 x5 0 ∧
    SplitStep K0 st9.internal [cellsOf st9 x5.base (x5.size + 0)] (releaseEff d9.kern 5)
      (.ok (splitEff (releaseEff d9.kern 5) st9.internal [cellsOf st9 x5.base (x5.size + 0)])) ∧
    StoreStep (releaseEff d9.kern 5).A.length 4
      (splitEff (releaseEff d9.kern 5) st9.internal [cellsOf st9 x5.base (x5.size + 0)])
      (.ok (storeEff (splitEff (releaseEff d9.kern 5) st9.internal
        [cellsOf st9 x5.base (x5.size + 0)]) (releaseEff d9.kern 5).A.length 4)) :=
  ⟨d9_reach, .noExtra (st := st9) (x := x5) (by decide) (by decide) rfl, by decide,
    .ok (by decide), by decide, by decide, .ok (by decide), .ok (by decide)⟩

/-- **`mark` requires the right of §36** (DS-v2, non-normative: DS2-1, Q11 (d); §36, §58). In
`d13`, a callee frame with no right on the stack value 0 (`¬ AdminRight`) marks stack 0: `reject`,
and no other outcome. -/
theorem mark_without_right :
    DReach K0 wst d13 ∧ d13.stacks[0]? = some st9 ∧ ¬ AdminRight d13.kern st9 ∧
    MarkStep 0 d13 .reject ∧ ∀ o, MarkStep 0 d13 o → o = .reject :=
  ⟨d13_reach, by decide, by decide, mark_rejects_without_right (st := st9) (by decide) (by decide)⟩

/-- `transfer(4, 5)` by the program after the first push: the block value, holding block authority
5, moves from place 4 to place 5, and place 4 becomes `Moved` (§63; DS-v2, DS2-2). -/
def d14 : DState := ⟨transferEff d5.kern 4 5, d5.stacks, d5.fresh⟩

/-- The kernel state of `grow(0, 5, 1)` in `d14` after `release(5)` and `split(4, [[2, 3]])`
(§62, §61; DS-v2, DS2-2). -/
def s14 : S3 :=
  splitEff (releaseEff d14.kern 5) st5.internal [cellsOf st5 x5.base (x5.size + 1)]

/-- `grow(0, 5, 1)` in `d14`: `release(5)`, `split(4, [[2, 3]])`, `store(6, 5)` into place 5,
which holds block authority 5 since the transfer (DS-v2, DS2-2, Part XIV, §77). -/
def d15 : DState :=
  ⟨storeEff s14 (releaseEff d14.kern 5).A.length 5,
    d14.stacks.set 0 (growMeta st5 x5 1 (releaseEff d14.kern 5).A.length 5), d14.fresh⟩

/-- **`grow` follows the current holder of the block** (DS-v2, non-normative: DS2-2, Q11 (e); §63,
§65, §77). In `d14`, the block value of block 5, recorded with destination 4, was transferred to
place 5, which now holds authority 5, and place 4 is `Moved`. `grow(0, 5, 1)` is `ok`: it stores
the new block authority 6 into place 5, the grown block records destination 5, and place 4 stays
`Moved`. -/
theorem grow_follows_holder :
    DReach K0 wst d14 ∧ d14.stacks[0]? = some st5 ∧ st5.block 5 = some x5 ∧ x5.dst = 4 ∧
    holderPlace d14.kern 5 = some 5 ∧ d14.kern.I 4 = .moved ∧
    GrowStep K0 0 5 1 d14 (.ok d15) ∧
    d15.kern.A[d14.kern.A.length]?.map (·.holder) = some (.place 5) ∧
    (d15.stacks[0]?).map (·.blocks) = some [⟨0, 2, 6, 5⟩] ∧ d15.kern.I 4 = .moved :=
  ⟨.step d5_reach (.kernel (.transfer (.ok (by decide)))), by decide, by decide, rfl, by decide,
    by decide,
    .ok (st := st5) (x := x5) (d := 5) (by decide) (by decide) (by decide) (.ok (by decide))
      (by decide) (by decide) (by decide) (.ok (by decide)) (.ok (by decide)),
    by decide, by decide, by decide⟩

/-- Statics of the `newStack` example (§47; DS-v2, §76.5): leaf 0, `Uninit`, owned by frame 0, is
the stack value; leaf 1, owned by static 0, is the storage, whose root authority 1 is held by
place 0. -/
def wsu : Statics := [((none, none, 0), false), ((none, some 0, 0), false)]

/-- **§76.5 applies to `newStack`** (DS-v2, non-normative: DS-v1 decided by Q11 (c); §76.5). In the
initial state of `wsu`, `newStack(1, 1)` is rejected; the stack value 0, the place holding
`internal` 1, is `Uninit`. -/
theorem newStack_value_uninit :
    DReach K0 wsu (DState.init wsu) ∧ NewStackStep [] 1 1 (DState.init wsu) .reject ∧
    (DState.init wsu).kern.A[1]? = some ⟨.modify, none, [1], .place 0, true⟩ ∧
    (DState.init wsu).kern.I 0 = .uninit ∧ ¬ LeavesInit (DState.init wsu).kern (.place 0) :=
  ⟨.init, .reject (by decide), by decide, by decide, by decide⟩

/-- A callee frame with no parameter and no local, entered after the program's `release(5)` that
follows the rewind (§72; DS-v2, non-normative: §36 applies to `rewind`). -/
def d16 : DState := ⟨enterEff d11.kern [] [], d11.stacks, d11.fresh⟩

/-- **§36 applies to `rewind`** (DS-v2, non-normative: DS-v1 decided by Q27 (a); §36). In `d16`,
mark `⟨0, 0, 0⟩` is live for stack 0 and no active authority derived from `internal` 4 covers the
cell 2 above it (blocks 5, 6 and 7 are released): every condition DS-v1 lists for the `ok` case
holds. The callee has no right on the stack value (`¬ AdminRight`, §36), so `rewind ⟨0, 0, 0⟩` is
`reject` and nothing else (`rewind_ok_iff`, `RewindStep.det`). -/
theorem rewind_needs_right :
    DReach K0 wst d16 ∧ d16.stacks[0]? = some st9 ∧ LiveMark d16.kern 0 st9 m0 ∧
    (∀ (x l : Nat) (y : Authority), d16.kern.A[x]? = some y → y.active = true →
      st9.internal ∈ d16.kern.ancs x → l ∈ y.footprint → l ∉ above st9 m0) ∧
    ¬ AdminRight d16.kern st9 ∧
    RewindStep K0 0 m0 d16 .reject ∧ ∀ o, RewindStep K0 0 m0 d16 o → o = .reject := by
  have hst : d16.stacks[0]? = some st9 := by decide
  have hna : ¬ AdminRight d16.kern st9 := by decide
  have hb : ∀ x ∈ List.range d16.kern.A.length, OptP (d16.kern.A[x]?) (fun y => y.active = true →
      st9.internal ∈ d16.kern.ancs x → ∀ l ∈ above st9 m0, l ∉ y.footprint) True := by decide
  have hrej : RewindStep K0 0 m0 d16 .reject := .static hst (by decide) hna
  refine ⟨.step d11_reach (.kernel (.enter (.ok (by decide)))), hst, by decide,
    fun x l y hy ya hx hly hl => ?_, hna, hrej, fun o ho => RewindStep.det ho hrej⟩
  have := hb x (List.mem_range.2 (lt_of_getElem? hy))
  rw [hy] at this
  exact this ya hx l hl hly

/-- The program's `release(4)` of `internal` 4 after the program's `release(5)` that follows the
rewind: stack 0 is dead (§62, §46; DS-v2, DS2-3). -/
def d17 : DState := ⟨releaseEff d11.kern 4, d11.stacks, d11.fresh⟩

/-- **A dead stack invalidates its marks** (DS-v2, non-normative: DS2-3, Q28 (c); §46, §58). In
`d17`, `internal` 4 of stack 0 is inactive; mark `⟨0, 0, 0⟩` is still recorded for stack 0, and
the current frame has no administrative right (`AdminRight` needs `internal` active). `rewind ⟨0,
0, 0⟩` is `fail` and no other outcome: the mark is dead, checked before the right. -/
theorem dead_stack_marks_fail :
    DReach K0 wst d17 ∧ d17.stacks[0]? = some st9 ∧ m0 ∈ st9.marks ∧
    ¬ d17.kern.Active st9.internal ∧ ¬ AdminRight d17.kern st9 ∧
    RewindStep K0 0 m0 d17 .fail ∧ ∀ o, RewindStep K0 0 m0 d17 o → o = .fail := by
  have hst : d17.stacks[0]? = some st9 := by decide
  have hd : ¬ d17.kern.Active st9.internal := by decide
  exact ⟨.step d11_reach (.kernel (.release (.ok (by decide)))), hst, by decide, hd,
    fun h => hd h.1, rewind_dead_stack_fails hst hd⟩

end Witness

end Ern.Lib.DataStack
