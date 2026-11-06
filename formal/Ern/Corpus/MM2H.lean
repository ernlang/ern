import Ern.MemoryModel.Machine

/-!
# Corpus MM2-H on the memory machine (test module, spec v0.1 Parts II–III, §8–§20)

Test module. It states no semantics: it runs the MM2-H corpus (non-normative validation
material, 17 identifiers, H13 split into H13a and H13b, 18 scenarios) on the relations of
`Ern.MemoryModel.Machine`.

Each case gives a state reached from the empty state, an admissible initial state (§9 ¶9), by an
execution of `ok` steps (`Exec`, §20.3 ¶3), and the outcome of the normative relation at that
state (`ReadStep`, `WriteStep`, `DeallocStep`, `AllocStep`, §20.1), proved by `decide` or by the
machine lemmas. Each `ub` case has a separate `_twin` theorem for the corpus's positive twin.
The docstring of each theorem states the expected verdict from the corpus, the obtained verdict,
and the class (rule "classement" of the corpus: `N2` = memory machine). Where the obtained
verdict differs from the expected one, the docstring says "Mismatch" and the case is kept as
written, not corrected.

Context of every execution (§20.3 ¶1, §20.3 ¶3: explicit context parameters): compatibility is
equality of the presented authority with the recorded token (§17 ¶4); read and write
obligations are the machine's explicit test instances `Witness.obR` and `Witness.obW` (both parts
`True`), except in H14, which needs a false static part.

Open boundaries of the spec, classified non-blocking and not declared passed: H10 address
formation (§14 ¶4, §19), H13a at language level (§10 ¶4, §19), H13b (§19).
-/

namespace Ern.Corpus.MM2H

open Ern.MemoryModel.Machine

/-! ## Run builders -/

section Builders

variable {Ty : Type} {C : Nat → Nat → Prop} {R : ReadOblSpec Ty} {W : WriteOblSpec Ty}

/-- An execution extended by one `ok` step at its end is an execution (§20.1 ¶2, §20.3 ¶3). -/
theorem exec_snoc {ops : List (Op Ty)} {op : Op Ty} {s₀ s s' : State}
    (h : Exec C R W ops s₀ s) (hs : Step C R W op s s') : Exec C R W (ops ++ [op]) s₀ s' := by
  induction h with
  | nil => exact .cons hs (.nil _)
  | cons h₀ _ ih => exact .cons h₀ (ih hs)

/-- Appending an `ok` raw creation to an execution from the empty state. The decidable form
`AllocPreDec` suffices because every reached state satisfies freshness (§9 ¶7, §9 ¶9, §9 ¶11). -/
theorem run_alloc {ops : List (Op Ty)} {s : State} {space base size align : Nat}
    {freeAuth : Option Nat} (h : Exec C R W ops State.empty s)
    (hp : AllocPreDec s space base size align) :
    Exec C R W (ops ++ [.alloc space base size align freeAuth]) State.empty
      (s.alloc space base size align freeAuth) :=
  exec_snoc h (.alloc (.ok ((allocPreDec_iff (h.admissible admissible_empty).wf).1 hp)))

/-- Appending an `ok` raw write to an execution from the empty state (§16, §20.2 ¶2). -/
theorem run_write {ops : List (Op Ty)} {s : State} {ac : Access} {t : Ty}
    {w : Nat → UInt8 × Option Nat} (h : Exec C R W ops State.empty s) (hc : CanWrite s ac)
    (hd : W.dec s ac t w) (hs : W.stat s ac t w) :
    Exec C R W (ops ++ [.write ac t w]) State.empty (s.write ac w) :=
  exec_snoc h (.write (.ok ⟨hc, hd, hs⟩))

/-- Appending an `ok` raw deallocation to an execution from the empty state (§17, §20.2 ¶2). -/
theorem run_dealloc {ops : List (Op Ty)} {s : State} {id auth : Nat}
    (h : Exec C R W ops State.empty s) (hc : CanDealloc C s id auth) :
    Exec C R W (ops ++ [.dealloc id auth]) State.empty (s.dealloc id) :=
  exec_snoc h (.dealloc (.ok hc))

/-- Appending an `ok` raw read to an execution from the empty state; the state is unchanged
(§15, §20.2 ¶1). -/
theorem run_read {ops : List (Op Ty)} {s : State} {ac : Access} {t : Ty} {v : List AByte}
    (h : Exec C R W ops State.empty s) (hr : ReadStep R ac t s (.ok v)) :
    Exec C R W (ops ++ [.read ac t]) State.empty s :=
  exec_snoc h (.read hr)

/-- At a state reached from the empty state, a creation whose decidable preconditions fail is
`ub` (§9 ¶11, §20.1 ¶2). -/
theorem allocStep_ub {ops : List (Op Ty)} {s : State} {space base size align : Nat}
    {freeAuth : Option Nat} (h : Exec C R W ops State.empty s)
    (hn : ¬ AllocPreDec s space base size align) :
    AllocStep space base size align freeAuth s .ub :=
  .ub (mt (allocPreDec_iff (h.admissible admissible_empty).wf).2 hn)

/-- At a state reached from the empty state, a creation whose decidable preconditions hold is
`ok` with the creation effect (§9 ¶11, §20.1 ¶2). -/
theorem allocStep_ok {ops : List (Op Ty)} {s : State} {space base size align : Nat}
    {freeAuth : Option Nat} (h : Exec C R W ops State.empty s)
    (hp : AllocPreDec s space base size align) :
    AllocStep space base size align freeAuth s (.ok (s.alloc space base size align freeAuth)) :=
  .ok ((allocPreDec_iff (h.admissible admissible_empty).wf).1 hp)

end Builders

/-! ## Context and common states -/

/-- Read obligations of the corpus context: the machine's explicit test instance, both parts
`True` (§20.3 ¶1). -/
abbrev ctxR : ReadOblSpec Unit := Witness.obR.toSpec

/-- Write obligations of the corpus context: the machine's explicit test instance, both parts
`True` (§20.3 ¶1). -/
abbrev ctxW : WriteOblSpec Unit := Witness.obW.toSpec

/-- Executions of the corpus context from the empty state (§9 ¶9, §20.3 ¶3): compatibility is
equality of presented authority and recorded token (§17 ¶2, §17 ¶4), obligations `ctxR`,
`ctxW`. -/
abbrev Run (ops : List (Op Unit)) (s : State) : Prop :=
  Exec (· = ·) ctxR ctxW ops State.empty s

/-- A read whose interpreter result is `o` has the relational outcome `o` (§20.3 ¶3, by
`read_sound`). -/
theorem readStep_of {ac : Access} {s : State} {o : ReadOutcome}
    (h : read Witness.obR ac () s trivial = o) : ReadStep ctxR ac () s o :=
  read_sound h

/-- Write access to `[96, 104)` with provenance `p` (§12 ¶1). -/
def wr (p : Nat) : Access := ⟨96, p, 8, .write⟩

/-- Read access to `[96, 104)` with provenance `p` (§12 ¶1). -/
def rd (p : Nat) : Access := ⟨96, p, 8, .read⟩

/-- One live allocation: identity `0`, space `0`, base `96`, size `8`, alignment `8`,
deallocation token `7` (§9 ¶1, §9 ¶11). -/
abbrev a8 : State := State.empty.alloc 0 96 8 8 (some 7)

/-- `a8` after a write of `Witness.w₀` (value `i + 1`, no provenance) over its whole range
(§16 ¶2). -/
abbrev a8w : State := a8.write (wr 0) Witness.w₀

/-- `a8` after deallocation of allocation `0` (§17 ¶3). -/
abbrev a8d : State := a8.dealloc 0

/-- The empty state is reached by the empty execution (§9 ¶9). -/
theorem run_empty : Run [] State.empty :=
  .nil _

/-- `a8` is reached by one `ok` creation (§9 ¶11). -/
theorem run_a8 : Run [.alloc 0 96 8 8 (some 7)] a8 :=
  run_alloc (.nil _) (by decide)

/-- `a8w` is reached by a creation and an `ok` write (§9 ¶11, §16). -/
theorem run_a8w : Run [.alloc 0 96 8 8 (some 7), .write (wr 0) () Witness.w₀] a8w :=
  run_write run_a8 (by decide) trivial trivial

/-- `a8d` is reached by a creation and an `ok` deallocation (§9 ¶11, §17). -/
theorem run_a8d : Run [.alloc 0 96 8 8 (some 7), .dealloc 0 7] a8d :=
  run_dealloc run_a8 (by decide)

/-! ## H01 — address reuse after deallocation -/

/-- State of H01: `a8w`, deallocation of `0`, then a new allocation at the same base `96`,
which receives identity `1` (§13 ¶1, §13 ¶2). -/
abbrev h01 : State := (a8w.dealloc 0).alloc 0 96 8 8 (some 7)

/-- Operations reaching `h01` (§9 ¶11, §16, §17). -/
abbrev h01Ops : List (Op Unit) :=
  [.alloc 0 96 8 8 (some 7), .write (wr 0) () Witness.w₀, .dealloc 0 7, .alloc 0 96 8 8 (some 7)]

/-- `h01` is reached, and the new allocation lies at the old base `96` (§13 ¶2). -/
theorem run_h01 : Run h01Ops h01 ∧ ∃ b, h01.allocs 1 = some b ∧ b.live = true ∧ b.base = 96 :=
  ⟨run_alloc (run_dealloc run_a8w (by decide)) (by decide), _, rfl, rfl, rfl⟩

/-- H01. Free, allocate at the same base, read through the old access. Expected `ub`;
obtained `ub`: the old provenance designates the dead allocation `0` (§12 ¶3, §13 ¶2, §15.1,
§17 ¶3). Class N2. -/
theorem H01 : Run h01Ops h01 ∧ ReadStep ctxR (rd 0) () h01 .ub :=
  ⟨run_h01.1, readStep_of (by decide)⟩

/-- H01 twin, as revised by the material owner: a write through the new access, then the read.
Expected `ok`; obtained `ok` with the written bytes (§16 ¶2, §16 ¶5). The twin as first written
read the new allocation without writing it first, which is `ub` by §10 ¶5 and §15.3, not by the
address reuse. Class N2. -/
theorem H01_twin :
    Run (h01Ops ++ [.write (wr 1) () Witness.w₀]) (h01.write (wr 1) Witness.w₀) ∧
    ReadStep ctxR (rd 1) () (h01.write (wr 1) Witness.w₀) (.ok (writtenBytes Witness.w₀ 0 8)) :=
  ⟨run_write run_h01.1 (by decide) trivial trivial, readStep_of (by decide)⟩

/-! ## H02, H03 — deallocation -/

/-- H02. Double deallocation. Expected `ub`; obtained `ub`: the allocation is dead (§17.1,
§17 ¶3). Class N2. -/
theorem H02 : Run [.alloc 0 96 8 8 (some 7), .dealloc 0 7] a8d ∧
    DeallocStep (· = ·) 0 7 a8d .ub :=
  ⟨run_a8d, .ub (by decide)⟩

/-- H02 twin: a single deallocation. Expected `ok`; obtained `ok` (§17.1, §17.2). Class N2. -/
theorem H02_twin : Run [.alloc 0 96 8 8 (some 7)] a8 ∧ DeallocStep (· = ·) 0 7 a8 (.ok a8d) :=
  ⟨run_a8, .ok (by decide)⟩

/-- H03. Deallocation with an authority (`8`) not compatible with the token (`7`) under the
context relation. Expected `ub`; obtained `ub` (§17.2, §17 ¶4, §20.3 ¶3). Class N2. -/
theorem H03 : Run [.alloc 0 96 8 8 (some 7)] a8 ∧ DeallocStep (· = ·) 0 8 a8 .ub :=
  ⟨run_a8, .ub (by decide)⟩

/-- H03 twin: compatible authority `7`. Expected `ok`; obtained `ok` (§17.2). Class N2. -/
theorem H03_twin : Run [.alloc 0 96 8 8 (some 7)] a8 ∧ DeallocStep (· = ·) 0 7 a8 (.ok a8d) :=
  H02_twin

/-! ## H04, H05, H06 — read conditions -/

/-- H04. Read of uninitialized bytes, right after creation. Expected `ub`; obtained `ub`
(§10 ¶5, §15.3). Class N2. -/
theorem H04 : Run [.alloc 0 96 8 8 (some 7)] a8 ∧ ReadStep ctxR (rd 0) () a8 .ub :=
  ⟨run_a8, readStep_of (by decide)⟩

/-- H04 twin: write, then read. Expected `ok`; obtained `ok` with the written bytes (§16 ¶2,
§16 ¶5). Class N2. -/
theorem H04_twin : Run [.alloc 0 96 8 8 (some 7), .write (wr 0) () Witness.w₀] a8w ∧
    ReadStep ctxR (rd 0) () a8w (.ok (writtenBytes Witness.w₀ 0 8)) :=
  ⟨run_a8w, readStep_of (by decide)⟩

/-- H05. Read of `[101, 105)`, one byte past the end `104`. Expected `ub`; obtained `ub`
(§15 ¶1, §15.2). Class N2. -/
theorem H05 : Run [.alloc 0 96 8 8 (some 7), .write (wr 0) () Witness.w₀] a8w ∧
    ReadStep ctxR ⟨101, 0, 4, .read⟩ () a8w .ub :=
  ⟨run_a8w, readStep_of (by decide)⟩

/-- H05 twin: read of `[100, 104)`, ending at the end. Expected `ok`; obtained `ok` with the
written bytes (§15 ¶1, §16 ¶5). Class N2. -/
theorem H05_twin : Run [.alloc 0 96 8 8 (some 7), .write (wr 0) () Witness.w₀] a8w ∧
    ReadStep ctxR ⟨100, 0, 4, .read⟩ () a8w (.ok (writtenBytes Witness.w₀ 4 4)) :=
  ⟨run_a8w, readStep_of (by decide)⟩

/-- Zero-length read access at address `104`, just after the end of `[96, 104)` (§15 ¶3). -/
def rz : Access := ⟨104, 0, 0, .read⟩

/-- H06. Zero-length read just after the end of a dead allocation. Expected `ub`; obtained
`ub` (§15.1, §15 ¶3, §17 ¶3). Class N2. -/
theorem H06 : Run [.alloc 0 96 8 8 (some 7), .dealloc 0 7] a8d ∧ ReadStep ctxR rz () a8d .ub :=
  ⟨run_a8d, readStep_of (by decide)⟩

/-- H06 twin: same access, allocation live. Expected `ok`; obtained `ok` with no bytes: the
spatial condition admits address `b + s` and no initialized byte is required (§15 ¶3).
Class N2. -/
theorem H06_twin : Run [.alloc 0 96 8 8 (some 7)] a8 ∧ ReadStep ctxR rz () a8 (.ok []) :=
  ⟨run_a8, readStep_of (by decide)⟩

/-! ## H07, H08 — creation preconditions -/

/-- H07. Creation of `[100, 108)` in space `0`, overlapping the live `[96, 104)` of the same
space. Expected `ub`; obtained `ub` (§9 ¶3, §9 ¶11). Class N2. -/
theorem H07 : Run [.alloc 0 96 8 8 (some 7)] a8 ∧ AllocStep 0 100 8 4 none a8 .ub :=
  ⟨run_a8, allocStep_ub run_a8 (by decide)⟩

/-- H07 twins: the same creation in another space (`1`), or in space `0` after the
overlapped allocation died. Expected `ok`; obtained `ok` (§9 ¶3, §9 ¶11). Class N2. -/
theorem H07_twin : AllocStep 1 100 8 4 none a8 (.ok (a8.alloc 1 100 8 4 none)) ∧
    Run [.alloc 0 96 8 8 (some 7), .dealloc 0 7] a8d ∧
    AllocStep 0 100 8 4 none a8d (.ok (a8d.alloc 0 100 8 4 none)) :=
  ⟨allocStep_ok run_a8 (by decide), run_a8d, allocStep_ok run_a8d (by decide)⟩

/-- H08. From the empty state (admissible, §9 ¶9): alignment `3`, not a power of two, with
base `96` a multiple of `3`; and base `100` not a multiple of alignment `8`. Expected `ub`;
obtained `ub` for both (§9 ¶4, §9 ¶11). Class N2. -/
theorem H08 : AllocStep 0 96 8 3 none State.empty .ub ∧ AllocStep 0 100 8 8 none State.empty .ub :=
  ⟨allocStep_ub run_empty (by decide), allocStep_ub run_empty (by decide)⟩

/-- H08 twins: valid alignment `4` for each faulty creation. Expected `ok`; obtained `ok`
(§9 ¶4, §9 ¶11). Class N2. -/
theorem H08_twin :
    AllocStep 0 96 8 4 none State.empty (.ok (State.empty.alloc 0 96 8 4 none)) ∧
    AllocStep 0 100 8 4 none State.empty (.ok (State.empty.alloc 0 100 8 4 none)) :=
  ⟨allocStep_ok run_empty (by decide), allocStep_ok run_empty (by decide)⟩

/-! ## H09, H10 — write authority, derivation -/

/-- H09. Write through an access whose elementary authority is `read`. Expected `ub`;
obtained `ub` (§12 ¶4, §16.3). Class N2. -/
theorem H09 : Run [.alloc 0 96 8 8 (some 7)] a8 ∧
    WriteStep ctxW ⟨96, 0, 8, .read⟩ () Witness.w₀ a8 .ub :=
  ⟨run_a8, .ub fun h => absurd h.1 (by decide)⟩

/-- H09 twin: write authority. Expected `ok`; obtained `ok` (§16.3). Class N2. -/
theorem H09_twin : Run [.alloc 0 96 8 8 (some 7)] a8 ∧
    WriteStep ctxW (wr 0) () Witness.w₀ a8 (.ok a8w) :=
  ⟨run_a8, .ok ⟨by decide, trivial, trivial⟩⟩

/-- Source access of H10: write access to `[96, 100)` of allocation `0` (§12 ¶1). -/
def h10src : Access := ⟨96, 0, 4, .write⟩

/-- Access formed outside the source range and outside the allocation: `[104, 108)`
(§14 ¶4). -/
def h10past : Access := ⟨104, 0, 4, .write⟩

/-- Restrictive derivation of `h10src` inside its range: `[98, 100)` (§14 ¶1). -/
def h10in : Access := ⟨98, 0, 2, .write⟩

/-- H10, as revised by the material owner: use of an access formed outside the source range that
leaves the allocation. Expected `ub` for the use; obtained `ub` (§15 ¶1, §16.2). The formation
itself has no transition in the machine and no verdict: an open boundary of the spec (§14 ¶4,
§19), classified non-blocking. Class N2. -/
theorem H10 : Run [.alloc 0 96 8 8 (some 7)] a8 ∧ ¬ Derive h10src h10past ∧
    WriteStep ctxW h10past () Witness.w₀ a8 .ub :=
  ⟨run_a8, fun h => absurd h.2.1 (by decide), .ub fun h => absurd h.1 (by decide)⟩

/-- H10 twin: a restrictive derivation inside the source range, then use. Expected `ok`;
obtained `ok` (§14 ¶1, §16). Class N2. -/
theorem H10_twin : Run [.alloc 0 96 8 8 (some 7)] a8 ∧ Derive h10src h10in ∧
    WriteStep ctxW h10in () Witness.w₀ a8 (.ok (a8.write h10in Witness.w₀)) :=
  ⟨run_a8, ⟨by decide, by decide, rfl, by decide⟩, .ok ⟨by decide, trivial, trivial⟩⟩

/-! ## H11, H12 — read-after-write and non-interference -/

/-- H11. Write `[96, 104)`, read the contained subrange `[98, 101)`. Expected: the written
sub-contents; obtained `ok` with positions `2..4` of the written representation (§16 ¶5).
Class N2. -/
theorem H11 : Run [.alloc 0 96 8 8 (some 7), .write (wr 0) () Witness.w₀] a8w ∧
    ReadStep ctxR ⟨98, 0, 3, .read⟩ () a8w (.ok (writtenBytes Witness.w₀ 2 3)) :=
  ⟨run_a8w, readStep_of (by decide)⟩

/-- Second written representation of H12: byte `170`, no provenance, at every position
(§10 ¶2). -/
def w₁ : Nat → UInt8 × Option Nat := fun _ => (170, none)

/-- State of H12: allocations `0` (`[96, 104)`) and `1` (`[128, 136)`, same space), and
`[96, 100)` written with `Witness.w₀` (§9 ¶3, §16 ¶2). -/
abbrev h12 : State := (a8.alloc 0 128 8 8 none).write ⟨96, 0, 4, .write⟩ Witness.w₀

/-- Operations reaching `h12` (§9 ¶11, §16). -/
abbrev h12Ops : List (Op Unit) :=
  [.alloc 0 96 8 8 (some 7), .alloc 0 128 8 8 none, .write ⟨96, 0, 4, .write⟩ () Witness.w₀]

/-- `h12` is reached (§9 ¶11, §16). -/
theorem run_h12 : Run h12Ops h12 :=
  run_write (run_alloc run_a8 (by decide)) (by decide) trivial trivial

/-- H12. After `h12`, a write of a disjoint range of the same allocation (`[100, 104)`), or a
write of the other allocation, leaves the read of `[96, 100)` unchanged. Expected: contents
unchanged; obtained: the same `ok` bytes before and after each write (§16 ¶3, §16 ¶5).
Class N2. -/
theorem H12 : Run h12Ops h12 ∧
    ReadStep ctxR ⟨96, 0, 4, .read⟩ () h12 (.ok (writtenBytes Witness.w₀ 0 4)) ∧
    Run (h12Ops ++ [.write ⟨100, 0, 4, .write⟩ () w₁]) (h12.write ⟨100, 0, 4, .write⟩ w₁) ∧
    ReadStep ctxR ⟨96, 0, 4, .read⟩ () (h12.write ⟨100, 0, 4, .write⟩ w₁)
      (.ok (writtenBytes Witness.w₀ 0 4)) ∧
    Run (h12Ops ++ [.write ⟨128, 1, 8, .write⟩ () w₁]) (h12.write ⟨128, 1, 8, .write⟩ w₁) ∧
    ReadStep ctxR ⟨96, 0, 4, .read⟩ () (h12.write ⟨128, 1, 8, .write⟩ w₁)
      (.ok (writtenBytes Witness.w₀ 0 4)) :=
  ⟨run_h12, readStep_of (by decide), run_write run_h12 (by decide) trivial trivial,
    readStep_of (by decide), run_write run_h12 (by decide) trivial trivial,
    readStep_of (by decide)⟩

/-! ## H13a, H13b — pointer bytes -/

/-- Representation written as a pointer: byte values of the address `64` (low byte first) and
provenance `0`, the allocation at `64`, on every byte. The byte encoding is a choice of this
test; the provenance comes from the written representation (§10 ¶4, §16 ¶2). -/
def ptrRep : Nat → UInt8 × Option Nat := fun i => (if i = 0 then 64 else 0, some 0)

/-- State of H13a before the copy: allocations `0` (`[64, 72)`), `1` (`[96, 104)`, source)
and `2` (`[128, 136)`, destination); `ptrRep` written over the source (§9 ¶11, §16 ¶2). -/
abbrev h13Src : State :=
  (((State.empty.alloc 0 64 8 8 none).alloc 0 96 8 8 none).alloc 0 128 8 8 none).write
    ⟨96, 1, 8, .write⟩ ptrRep

/-- Read access to source byte `k` (§12 ¶1). -/
def srcByte (k : Nat) : Access := ⟨96 + k, 1, 1, .read⟩

/-- Write access to destination byte `k` (§12 ¶1). -/
def dstByte (k : Nat) : Access := ⟨128 + k, 2, 1, .write⟩

/-- Representation supplied by the copy of byte `k`: the value and provenance of source byte
`k` (§16 ¶2). `cp_reads` shows that it is the abstract byte the copy read (§20.2 ¶1). -/
def copyRep (k : Nat) : Nat → UInt8 × Option Nat := fun _ => ptrRep k

/-- State after copying the first `k` bytes, one byte per write (§16 ¶2). -/
def cp : Nat → State
  | 0 => h13Src
  | k + 1 => (cp k).write (dstByte k) (copyRep k)

/-- Operations reaching `cp k`: set-up, then for each byte a read of the source byte and a
write of the destination byte (§15, §16). -/
def cpOps : Nat → List (Op Unit)
  | 0 => [.alloc 0 64 8 8 none, .alloc 0 96 8 8 none, .alloc 0 128 8 8 none,
      .write ⟨96, 1, 8, .write⟩ () ptrRep]
  | k + 1 => cpOps k ++ [.read (srcByte k) ()] ++ [.write (dstByte k) () (copyRep k)]

/-- Before copying byte `k`, the read of source byte `k` is `ok` and returns exactly the value
and provenance that `copyRep k` supplies (§15, §16 ¶5, §20.2 ¶1). -/
theorem cp_reads : ∀ k, k < 8 →
    read Witness.obR (srcByte k) () (cp k) trivial = .ok [.init (ptrRep k).1 (ptrRep k).2] := by
  decide

/-- Before copying byte `k`, the write of destination byte `k` satisfies the kernel write
conditions (§16.1–§16.3). -/
theorem cp_writes : ∀ k, k < 8 → CanWrite (cp k) (dstByte k) := by
  decide

/-- The copy of the first `k ≤ 8` bytes is an execution of `ok` steps from the empty state
(§20.3 ¶3). -/
theorem run_cp : ∀ k, k ≤ 8 → Run (cpOps k) (cp k)
  | 0, _ =>
    run_write (run_alloc (run_alloc (run_alloc (.nil _) (by decide)) (by decide)) (by decide))
      (by decide) trivial trivial
  | k + 1, hk =>
    run_write (run_read (run_cp k (Nat.le_of_succ_le hk)) (read_sound (cp_reads k hk)))
      (cp_writes k hk) trivial trivial

/-- The eight abstract bytes of `ptrRep`, each with provenance `0` (§10 ¶2). -/
def ptrBytes : List AByte :=
  [.init 64 (some 0), .init 0 (some 0), .init 0 (some 0), .init 0 (some 0),
    .init 0 (some 0), .init 0 (some 0), .init 0 (some 0), .init 0 (some 0)]

/-- H13a. Pointer bytes copied byte by byte, each write supplying the abstract byte just read.
Expected: the provenance of each byte is kept. Obtained, at relation level: every copy read is
`ok` with the byte's value and provenance, and after the copy the destination reads exactly
the source bytes, provenance `0` on each (§16 ¶2, §16 ¶5, §20.2 ¶1). Open obligation, not
declared passed: whether a byte copy of the language supplies the read provenance is not fixed
(§10 ¶4, §19 ¶3). Class N2. -/
theorem H13a : Run (cpOps 8) (cp 8) ∧
    (∀ k, k < 8 → ReadStep ctxR (srcByte k) () (cp k) (.ok [.init (ptrRep k).1 (ptrRep k).2])) ∧
    ReadStep ctxR ⟨128, 2, 8, .read⟩ () (cp 8) (.ok ptrBytes) ∧
    ReadStep ctxR ⟨96, 1, 8, .read⟩ () (cp 8) (.ok ptrBytes) :=
  ⟨run_cp 8 (Nat.le_refl _), fun k hk => read_sound (cp_reads k hk),
    readStep_of (by decide +kernel), readStep_of (by decide +kernel)⟩

/-- H13b. Rebuilding a usable access from the copied bytes or from the integer `64`.
Expected: to be arbitrated. Obtained: no verdict; the machine has no conversion from an integer
or from bytes to an access, and an access to address `64` gets `ok` or `ub` according to the
provenance a conversion rule would give it: `0` (the provenance stored in the copied bytes)
gives `ok`, `2` (the allocation holding the copied bytes) gives `ub`. Open obligation, not
declared passed (§19.2, §19.3, §19 ¶3). Class N2. -/
theorem H13b_open :
    WriteStep ctxW ⟨64, 0, 1, .write⟩ () w₁ (cp 8) (.ok ((cp 8).write ⟨64, 0, 1, .write⟩ w₁)) ∧
    WriteStep ctxW ⟨64, 2, 1, .write⟩ () w₁ (cp 8) .ub :=
  ⟨.ok ⟨by decide, trivial, trivial⟩, .ub fun h => absurd h.1 (by decide)⟩

/-! ## H14 — false static obligation -/

/-- Read obligations whose decidable part is `True` and whose static part is `P` at every read
(§20.3 ¶1, §20.3 ¶2): an explicit context with a false (`P = False`) or true (`P = True`)
static obligation. -/
def obStat (P : Prop) : ReadObl Unit :=
  { dec := fun _ _ _ => True, stat := fun _ _ _ => P, decInst := fun _ _ _ => instDecidableTrue }

/-- H14. Read of initialized bytes satisfying every kernel condition, under a context whose
static obligation is false. Expected: relation `ub`, interpreter not callable. Obtained: the
relation is `ub` (§20.1 ¶2, "including when the obligation is static"), and no proof of the
static part exists, so `read (obStat False) (rd 0) () a8w` cannot be applied (§20.3 ¶3).
Class N2. -/
theorem H14 :
    Exec (· = ·) (obStat False).toSpec ctxW [.alloc 0 96 8 8 (some 7), .write (wr 0) () Witness.w₀]
      State.empty a8w ∧
    CanRead a8w (rd 0) ∧ ReadStep (obStat False).toSpec (rd 0) () a8w .ub ∧
    ¬ (obStat False).stat a8w (rd 0) () :=
  ⟨run_write (run_alloc (.nil _) (by decide)) (by decide) trivial trivial, by decide,
    .ub fun h => h.2.2, id⟩

/-- H14 twin: same access, static obligation true. Expected `ok`; obtained `ok` by the
relation and by the interpreter, with the same bytes (§20.1 ¶2, §20.3 ¶3). Class N2. -/
theorem H14_twin :
    Exec (· = ·) (obStat True).toSpec ctxW [.alloc 0 96 8 8 (some 7), .write (wr 0) () Witness.w₀]
      State.empty a8w ∧
    ReadStep (obStat True).toSpec (rd 0) () a8w (.ok (writtenBytes Witness.w₀ 0 8)) ∧
    read (obStat True) (rd 0) () a8w trivial = .ok (writtenBytes Witness.w₀ 0 8) :=
  have hr : read (obStat True) (rd 0) () a8w trivial = .ok (writtenBytes Witness.w₀ 0 8) := by
    decide
  ⟨run_write (run_alloc (.nil _) (by decide)) (by decide) trivial trivial, read_sound hr, hr⟩

/-! ## H15, H16 — zero-size allocations, deallocation with a live access -/

/-- State of H15: two allocations of size `0` at base `96` in space `0` (§9 ¶3). -/
abbrev h15 : State := (State.empty.alloc 0 96 0 8 none).alloc 0 96 0 8 none

/-- H15. Two zero-size allocations live at the same base. Expected `ok`, distinct identities;
obtained: both creations `ok`, the state is admissible, identities `0` and `1` are both live
at base `96` with size `0` (§9 ¶3, §9 ¶8, §13 ¶1). Class N2. -/
theorem H15 : Run [.alloc 0 96 0 8 none, .alloc 0 96 0 8 none] h15 ∧ Admissible h15 ∧
    (∃ a, h15.allocs 0 = some a ∧ a.live = true ∧ a.base = 96 ∧ a.size = 0) ∧
    (∃ b, h15.allocs 1 = some b ∧ b.live = true ∧ b.base = 96 ∧ b.size = 0) :=
  have hr : Run [.alloc 0 96 0 8 none, .alloc 0 96 0 8 none] h15 :=
    run_alloc (run_alloc (.nil _) (by decide)) (by decide)
  ⟨hr, hr.admissible admissible_empty, ⟨_, rfl, rfl, rfl, rfl⟩, ⟨_, rfl, rfl, rfl, rfl⟩⟩

/-- State of H16: `a8w` (written through `wr 0`), then deallocation of `0` (§17 ¶3). -/
abbrev h16 : State := a8w.dealloc 0

/-- H16. Deallocation while the access `wr 0` designates the allocation, then use of that
access. Expected `ok`, then `ub`; obtained: the deallocation is `ok` (its conditions do not
mention existing accesses, §17.1, §17.2), then the write and the read through provenance `0`
are `ub` (§15.1, §16.1, §17 ¶3). Prevention belongs to the access discipline. Class N2. -/
theorem H16 :
    Run [.alloc 0 96 8 8 (some 7), .write (wr 0) () Witness.w₀, .dealloc 0 7] h16 ∧
    DeallocStep (· = ·) 0 7 a8w (.ok h16) ∧
    WriteStep ctxW (wr 0) () Witness.w₀ h16 .ub ∧ ReadStep ctxR (rd 0) () h16 .ub :=
  ⟨run_dealloc run_a8w (by decide), .ok (by decide), .ub fun h => absurd h.1 (by decide),
    readStep_of (by decide)⟩

/-! ## H17 — relation and interpreter -/

/-- On a state, every outcome of the read relation is the interpreter's result and conversely
(§20.3 ¶3, `read_sound`, `read_complete`). -/
theorem read_agree (ac : Access) (s : State) (o : ReadOutcome) :
    ReadStep ctxR ac () s o ↔ read Witness.obR ac () s trivial = o :=
  ⟨fun h => read_complete h trivial, read_sound⟩

/-- H17. Read by the relation and by the interpreter on admissible reached states. Expected:
same outcome, same value. Obtained: on `a8w` both give `ok` with the written bytes, on `a8`
both give `ub`, and the outcome sets coincide (§9 ¶8, §20.1, §20.2 ¶1, §20.3 ¶3). Class N2. -/
theorem H17 :
    Run [.alloc 0 96 8 8 (some 7), .write (wr 0) () Witness.w₀] a8w ∧ Admissible a8w ∧
    (∀ o, ReadStep ctxR (rd 0) () a8w o ↔ read Witness.obR (rd 0) () a8w trivial = o) ∧
    ReadStep ctxR (rd 0) () a8w (.ok (writtenBytes Witness.w₀ 0 8)) ∧
    read Witness.obR (rd 0) () a8w trivial = .ok (writtenBytes Witness.w₀ 0 8) ∧
    Run [.alloc 0 96 8 8 (some 7)] a8 ∧ Admissible a8 ∧
    (∀ o, ReadStep ctxR (rd 0) () a8 o ↔ read Witness.obR (rd 0) () a8 trivial = o) ∧
    ReadStep ctxR (rd 0) () a8 .ub ∧ read Witness.obR (rd 0) () a8 trivial = .ub :=
  ⟨run_a8w, run_a8w.admissible admissible_empty, read_agree _ _, H04_twin.2, by decide,
    run_a8, run_a8.admissible admissible_empty, read_agree _ _, H04.2, by decide⟩

end Ern.Corpus.MM2H
