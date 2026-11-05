import Ern.Corpus.Runner
import Ern.Lib.DataStack

/-!
# Corpus DataStack: the stack library (test module)

Cases of the library instance `DataStack` of `specs/ERN_Memory_Model_Specification_v0.md`, run on
the reference kernel (§60–§75) through the library of `Ern.Lib.DataStack`. The spec does not define
the contract (Part XIV preamble: "The contracts of `HandlePool` and `DataStack` belong to their
library abstractions and are not defined here"); the contract is DS-v1, non-normative, quoted in the
module docstring of `Ern.Lib.DataStack`. This is a test module: no model or library module imports
it.

* `DOp`: a kernel operation O1–O16 of the corpus runner (`Ern.Corpus.Runner`), or a stack
  operation `newStack`, `push`, `mark`, `rewind`, `grow` (DS-v1).
* `dstep k D o`: the computed outcome (§58); `dstep_sound`: it is an outcome of the relation of the
  operation (`DOpRel`: the kernel relation with the stack metadata unchanged, `NewStackStep`,
  `PushStep`, `MarkStep`, `RewindStep`, `GrowStep`), `ok`, `reject` and `fail` alike.
* `druns`: a run from `DState.init statics` (§47) whose steps are all `ok` reaches a state that is
  library-reachable (`DReach`) and whose kernel state is reachable by O1–O16 (§57,
  `DReach.reachable`).
* `newStack` consults the stack registry and no other (§56, `others = []`): the library states of
  these runs hold no administration other than stacks.

Each case states the reached state with `DRunsTo`, the verdict of the step under test with the
relation of its operation on that state (decided by `decide`; `rewind_dead_fails` adds that `fail`
is the only outcome), and its positive twin (the same sequence without the faulty element,
accepted). Its docstring gives the expected verdict from its source (DS-v1; the brief; the draft
DataStack cases of the derivability material, non-normative, which settle no verdict alone), the
obtained verdict, the class (`Lib`: library instance) and the twin. A case whose obtained verdict
differs from the expected one is kept with its expected verdict and marked **MISMATCH**. Two
verdicts have no settling source and are marked to arbitrate (expected verdict from the source:
none; **MISMATCH** in form, as `pool_free_entry_handle` in `Ern.Corpus.Lib`): DS05 (`push` without
room, reading DS-R7) and the third conjunct of DS03 (`grow` of a block that is no block of the
stack, reading DS-R5).

Readings of DS-v1 (recorded with `Ern.Lib.DataStack`) on which a verdict depends: DS-R5 (`grow` of
a live block that is not the last one: `fail`; the draft rejected) in DS04, and (a `b` that is no
block: `reject`) in DS03; DS-R7 (`push` without room: `fail`) in DS05. Every run uses the
representation readings R3 (`rewind` as `split` and `release` of `internal`, with the right of
§36) and R5 (`newStack`: the preconditions of `newArena` other than its guard, and the guard of
§56). The other verdicts are the same under the alternatives
of DS-R1, DS-R2, DS-R3, DS-R6 and R4: the covering authorities lie between the top of the mark and
the top; the administrative right of §36 holds where a mark is dead or foreign; a foreign mark is
in no list of the stack; every block grown can be released; the mark removed with an older one is
both later in the list and of a higher top.

Not encoded: the draft `case_rewind_reading` (re-encoded with the library, `Witness.reading_above`);
the draft `case_static_before_fail` other than its `push` without room (its `Init`-destination
conjuncts are changed by §77.2); the kernel `newArena` conjuncts of the draft `case_stacks` (the
stack-library state holds no arena registry; the cross-registry cases of §56 are another module).
-/

namespace Ern.Corpus.DataStack

open Ern.MemoryModel.Access Ern.MemoryModel.Arena Ern.Corpus Ern.Lib.DataStack

/-- The kernel operations O1–O16 among the operations of the corpus runner (§60–§75): every
operation but the arena operations O17–O19 of Part XIV, which are not steps of the stack library
(DS-v1). -/
def kernelOp : Op → Bool
  | .newArena .. | .issue .. | .reset .. => false
  | _ => true

/-- An operation of a stack-library run (DS-v1, non-normative): a kernel operation O1–O16
(§60–§75) of non-administrative code, or a stack operation `newStack`, `push`, `mark`, `rewind`,
`grow`, with its arguments. -/
inductive DOp where
  | kernel (o : Op) (h : kernelOp o = true := by decide)
  | newStack (storage internal : Nat)
  | push (j size dst : Nat)
  | mark (j : Nat)
  | rewind (j : Nat) (m : Mark)
  | grow (j b extra : Nat)

/-- A kernel relation (§60–§75) read on stack-library outcomes (DS-v1): the kernel outcome, with
the stack registry and the fresh mark identifier unchanged on `ok`. -/
def KRelD (R : Outcome3 S3 → Prop) (D : DState) : Outcome3 DState → Prop
  | .ok D' => R (.ok D'.kern) ∧ D'.stacks = D.stacks ∧ D'.fresh = D.fresh
  | .reject => R .reject
  | .fail => R .fail

/-- The relation of a kernel operation O1–O16 (§60–§75); none for the arena operations, which are
not steps of the stack library (DS-v1). -/
def kRel (k : K) (s : S3) : Op → Outcome3 S3 → Prop
  | .derive src r m => DeriveStep src r m s
  | .split src rs => SplitStep k src rs s
  | .release a => ReleaseStep a s
  | .transfer src dst => TransferStep k src dst s
  | .depend q x => DependStep q x s
  | .enter ps ls => EnterStep ps ls s
  | .exit => ExitStep k s
  | .read a ls => Read3Step a ls s
  | .write a ls => Write3Step a ls s
  | .writeShared a ls => WriteSharedStep k a ls s
  | .pin p => PinStep p s
  | .unpin p => UnpinStep k p s
  | .endUse p => EndUseStep k p s
  | .free p auth => FreeStep k p auth s
  | .alloc pr ow ls => AllocStep k pr ow ls s
  | .store a p => StoreStep a p s
  | .newArena .. | .issue .. | .reset .. => fun _ => False

/-- The relation of a stack-library operation from `D` (DS-v1, non-normative; §58): the kernel
relation of O1–O16 with the stack metadata unchanged; `NewStackStep` with no other registry
(§56: the library states of these runs hold stacks only), `PushStep`, `MarkStep`, `RewindStep`,
`GrowStep`. -/
def DOpRel (k : K) (D : DState) : DOp → Outcome3 DState → Prop
  | .kernel o _ => KRelD (kRel k D.kern o) D
  | .newStack st i => NewStackStep [] st i D
  | .push j size dst => PushStep k j size dst D
  | .mark j => MarkStep j D
  | .rewind j m => RewindStep k j m D
  | .grow j b extra => GrowStep k j b extra D

section Exec
variable (k : K) [∀ r r', Decidable (k.DeclaredDisjoint r r')] [DecidablePred k.SharedMutable]
  [DecidablePred k.Pinned] [DecidablePred k.ExternalDone] [DecidablePred k.Deallocable]
  [∀ p a, Decidable (k.FreeCompat p a)] [∀ p ls s, Decidable (k.Satisfiable p ls s)]

/-- A kernel outcome computed by the corpus runner, read on stack-library states (§58; DS-v1):
the stack metadata unchanged on `ok`. -/
def liftK (D : DState) : Outcome3 LState → Outcome3 DState
  | .ok L => .ok ⟨L.kern, D.stacks, D.fresh⟩
  | .reject => .reject
  | .fail => .fail

/-- The computed outcome of a stack-library operation from `D` (DS-v1, non-normative; §58): the
kernel operations by the corpus runner on the kernel state; the stack operations by the order of
the checks of their relations. -/
def dstep (D : DState) : DOp → Outcome3 DState
  | .kernel o _ => liftK D (lstep k ⟨D.kern, []⟩ o)
  | .newStack st i =>
    if NewStackPre D.kern D.stacks [] st i then .ok (newStackEff D st i) else .reject
  | .push j size dst =>
    match D.stacks[j]? with
    | none => .reject
    | some st =>
      if IssueStatic D.kern st.entry (cellsOf st st.top size) dst then
        if st.top + size ≤ st.cells.length then
          if SplitPre k D.kern st.internal [cellsOf st st.top size] then
            if StorePre (splitEff D.kern st.internal [cellsOf st st.top size]) D.kern.A.length
                dst then
              .ok ⟨storeEff (splitEff D.kern st.internal [cellsOf st st.top size])
                  D.kern.A.length dst,
                D.stacks.set j (pushMeta st size D.kern.A.length dst), D.fresh⟩
            else .reject
          else .reject
        else .fail
      else .reject
  | .mark j =>
    match D.stacks[j]? with
    | none => .reject
    | some st => .ok ⟨D.kern, D.stacks.set j (markMeta j st D.fresh), D.fresh + 1⟩
  | .rewind j m =>
    match D.stacks[j]? with
    | none => .reject
    | some st =>
      if LiveMark j st m then
        if AdminRight D.kern st then
          if SplitPre k D.kern st.internal [above st m] then
            if ReleasePre (splitEff D.kern st.internal [above st m]) D.kern.A.length then
              .ok ⟨releaseEff (splitEff D.kern st.internal [above st m]) D.kern.A.length,
                D.stacks.set j (rewindMeta st m), D.fresh⟩
            else .reject
          else .reject
        else .reject
      else .fail
  | .grow j b extra =>
    match D.stacks[j]? with
    | none => .reject
    | some st =>
      match st.block b with
      | none => .reject
      | some x =>
        if 0 < extra then
          if ReleasePre D.kern b then
            if IssueStatic (releaseEff D.kern b) st.entry (cellsOf st x.base (x.size + extra))
                x.dst then
              if InPlace st x extra then
                if SplitPre k (releaseEff D.kern b) st.internal
                    [cellsOf st x.base (x.size + extra)] then
                  if StorePre (splitEff (releaseEff D.kern b) st.internal
                      [cellsOf st x.base (x.size + extra)]) (releaseEff D.kern b).A.length
                      x.dst then
                    .ok ⟨storeEff (splitEff (releaseEff D.kern b) st.internal
                        [cellsOf st x.base (x.size + extra)]) (releaseEff D.kern b).A.length x.dst,
                      D.stacks.set j (growMeta st x extra (releaseEff D.kern b).A.length),
                      D.fresh⟩
                  else .reject
                else .reject
              else .fail
            else .reject
          else .reject
        else .reject

/-- The state reached by the operations `os` from `D` when every step is `ok` (§58; DS-v1);
`none` as soon as a step is not `ok`. -/
def drun (D : DState) : List DOp → Option DState
  | [] => some D
  | o :: os =>
    match dstep k D o with
    | .ok D' => drun D' os
    | _ => none

/-- The state reached by `os` from `DState.init statics` (§47; DS-v1); `DState.init statics` when a
step is not `ok` (used only under `(drun …).isSome = true`, see `druns`). -/
def dfinal (statics : Statics) (os : List DOp) : DState :=
  (drun k (DState.init statics) os).getD (DState.init statics)

/-- A run of `os` from `DState.init statics` (§47; DS-v1) has only `ok` steps and reaches `D`; `D`
is library-reachable (`DReach`) and its kernel state is reachable (§57). -/
structure DRunsTo (statics : Statics) (os : List DOp) (D : DState) : Prop where
  /-- Every step of the run is `ok` and the run ends in `D`. -/
  run : drun k (DState.init statics) os = some D
  /-- `D` is reachable by library steps (DS-v1). -/
  dreach : DReach k statics D
  /-- The kernel state of `D` is reachable from `S3.init statics` by O1–O16 (§36, §57). -/
  reach : Reachable k statics D.kern

/-- The run of `os` from `DState.init statics` has only `ok` steps (§47, §57; DS-v1). -/
abbrev DRuns (statics : Statics) (os : List DOp) : Prop :=
  DRunsTo k statics os (dfinal k statics os)

end Exec

/-! ## Soundness -/

/-- An `ok` outcome of the relation of a stack-library operation is a library step (DS-v1;
§57): a kernel step O1–O16 with the stack metadata unchanged, or a stack operation. -/
theorem dopRel_ok {k : K} {D D' : DState} : ∀ {o : DOp}, DOpRel k D o (.ok D') → DStep k D D'
  | .kernel o _, h => by
    obtain ⟨h, e1, e2⟩ := h
    have hD : D' = ⟨D'.kern, D.stacks, D.fresh⟩ := by rw [← e1, ← e2]
    rw [hD]
    refine .kernel ?_
    cases o with
    | derive => exact .derive h
    | split => exact .split h
    | release => exact .release h
    | transfer => exact .transfer h
    | depend => exact .depend h
    | enter => exact .enter h
    | exit => exact .exit h
    | read => exact .read h
    | write => exact .write h
    | writeShared => exact .writeShared h
    | pin => exact .pin h
    | unpin => exact .unpin h
    | endUse => exact .endUse h
    | free => exact .free h
    | alloc => exact .alloc h
    | store => exact .store h
    | newArena => exact h.elim
    | issue => exact h.elim
    | reset => exact h.elim
  | .newStack .., h => .newStack h
  | .push .., h => .push h
  | .mark .., h => .mark h
  | .rewind .., h => .rewind h
  | .grow .., h => .grow h

section Sound
variable {k : K} [∀ r r', Decidable (k.DeclaredDisjoint r r')] [DecidablePred k.SharedMutable]
  [DecidablePred k.Pinned] [DecidablePred k.ExternalDone] [DecidablePred k.Deallocable]
  [∀ p a, Decidable (k.FreeCompat p a)] [∀ p ls s, Decidable (k.Satisfiable p ls s)]

/-- A kernel outcome of the corpus runner, read on stack-library states, is an outcome of the
kernel relation with the stack metadata unchanged (§58; DS-v1). -/
theorem liftK_sound {R : Outcome3 S3 → Prop} {D : DState} {out : Outcome3 LState}
    (h : KRel R [] out) : KRelD R D (liftK D out) := by
  cases out with
  | ok L => exact ⟨h.1, rfl, rfl⟩
  | reject => exact h
  | fail => exact h

/-- **Step soundness** (§58, §60–§75; DS-v1): the computed outcome of `o` from `D` is an outcome
of the relation of `o`, `ok`, `reject` and `fail` alike. -/
theorem dstep_sound (D : DState) (o : DOp) : DOpRel k D o (dstep k D o) := by
  cases o with
  | kernel o h =>
    have hs := lstep_sound (k := k) ⟨D.kern, []⟩ o
    cases o <;> first | exact liftK_sound hs | simp [kernelOp] at h
  | newStack st i =>
    show NewStackStep [] st i D _
    dsimp only [dstep]
    split
    · next h => exact .ok h
    · next h => exact .reject h
  | mark j =>
    show MarkStep j D _
    dsimp only [dstep]
    split
    · next h => exact .noStack h
    · next st h => exact .ok h
  | push j size dst =>
    show PushStep k j size dst D _
    dsimp only [dstep]
    split
    · next h => exact .noStack h
    · next st h =>
      split
      · next h1 =>
        split
        · next h2 =>
          split
          · next h3 =>
            split
            · next h4 => exact .ok h h1 h2 (.ok h3) (.ok h4)
            · next h4 => exact .store h h1 h2 (.ok h3) (.reject h4)
          · next h3 => exact .split h h1 h2 (.reject h3)
        · next h2 => exact .fail h h1 h2
      · next h1 => exact .static h h1
  | rewind j m =>
    show RewindStep k j m D _
    dsimp only [dstep]
    split
    · next h => exact .noStack h
    · next st h =>
      split
      · next h1 =>
        split
        · next h2 =>
          split
          · next h3 =>
            split
            · next h4 => exact .ok h h1 h2 (.ok h3) (.ok h4)
            · next h4 => exact .release h h1 h2 (.ok h3) (.reject h4)
          · next h3 => exact .split h h1 h2 (.reject h3)
        · next h2 => exact .static h h1 h2
      · next h1 => exact .dead h h1
  | grow j b extra =>
    show GrowStep k j b extra D _
    dsimp only [dstep]
    split
    · next h => exact .noStack h
    · next st h =>
      split
      · next hb => exact .noBlock h hb
      · next x hb =>
        split
        · next h0 =>
          split
          · next h1 =>
            split
            · next h2 =>
              split
              · next h3 =>
                split
                · next h4 =>
                  split
                  · next h5 => exact .ok h hb h0 (.ok h1) h2 h3 (.ok h4) (.ok h5)
                  · next h5 => exact .store h hb h0 (.ok h1) h2 h3 (.ok h4) (.reject h5)
                · next h4 => exact .split h hb h0 (.ok h1) h2 h3 (.reject h4)
              · next h3 => exact .fail h hb h0 (.ok h1) h2 h3
            · next h2 => exact .static h hb h0 (.ok h1) h2
          · next h1 => exact .release h hb h0 (.reject h1)
        · next h0 => exact .noExtra h hb (by omega)

/-- An `ok` computed step is a library step (DS-v1; §58). -/
theorem dstep_ok {D D' : DState} {o : DOp} (h : dstep k D o = .ok D') : DStep k D D' :=
  dopRel_ok (h ▸ dstep_sound D o)

/-- A run whose steps are all `ok`, from a library-reachable state, ends in a library-reachable
state (DS-v1; §47). -/
theorem drun_reach {statics : Statics} :
    ∀ {D D' : DState} {os : List DOp}, DReach k statics D → drun k D os = some D' →
      DReach k statics D'
  | _, _, [], hD, h => by cases h; exact hD
  | D, _, o :: os, hD, h => by
    unfold drun at h
    cases hs : dstep k D o with
    | ok D₁ => rw [hs] at h; exact drun_reach (.step hD (dstep_ok hs)) h
    | reject => rw [hs] at h; cases h
    | fail => rw [hs] at h; cases h

/-- **Run soundness** (§47, §57; DS-v1): when every step of `os` from `DState.init statics` is
`ok`, the run reaches `dfinal k statics os`, which is library-reachable and whose kernel state is
reachable by O1–O16 (`DReach.reachable`). -/
theorem druns {statics : Statics} {os : List DOp}
    (h : (drun k (DState.init statics) os).isSome = true) : DRuns k statics os := by
  have hr : drun k (DState.init statics) os = some (dfinal k statics os) := by
    unfold dfinal
    cases e : drun k (DState.init statics) os with
    | none => rw [e] at h; cases h
    | some D => rfl
  have hd := drun_reach .init hr
  exact ⟨hr, hd, hd.reachable⟩

/-- A computed `reject` is a `reject` outcome of the relation (§58; DS-v1). -/
theorem drejects {D : DState} {o : DOp} (h : verdictOf (dstep k D o) = .reject) :
    DOpRel k D o .reject := by
  have hs := dstep_sound (k := k) D o
  revert hs h
  cases dstep k D o with
  | ok => intro h; cases h
  | reject => intro _ hs; exact hs
  | fail => intro h; cases h

/-- A computed `fail` is a `fail` outcome of the relation (§58; DS-v1). -/
theorem dfails {D : DState} {o : DOp} (h : verdictOf (dstep k D o) = .fail) :
    DOpRel k D o .fail := by
  have hs := dstep_sound (k := k) D o
  revert hs h
  cases dstep k D o with
  | ok => intro h; cases h
  | reject => intro h; cases h
  | fail => intro _ hs; exact hs

end Sound

/-! ## Test contract and shapes (§48, §72) -/

/-- The empty test contract (§48): nothing shared, pinned, externally done or deallocable. -/
abbrev K0 : K := KD.toK {}

/-- A root leaf of a local shape (§72, §71.1). -/
abbrev lf : Option Nat × Nat := (none, 0)

/-- A leaf part of the shape element `p` (§72, §71.1). -/
abbrev pt (p : Nat) : Option Nat × Nat := (some p, 0)

/-- One stack (DS-v1, §72, §60, §65, §76 read for a stack): frame 1 with the stack value 0, the
storage 1 with the cells 2, 3, 4, and the destinations 5, 6, 7 (root authorities 0 on 0, 1 on 1,
2 on 5, 3 on 6, 4 on 7); `internal` 5, `Modify` derived from the root of the storage on its cells,
stored into the stack value; stack 0 created on 1 with `internal` 5. -/
def setup1 : List DOp :=
  [.kernel (.enter [] [lf, lf, pt 1, pt 1, pt 1, lf, lf, lf]),
    .kernel (.derive 1 [2, 3, 4] .modify), .kernel (.store 5 0), .newStack 1 5]

/-! ## One stack: `rewind`, marks, `grow`, `push` (DS-v1) -/

/-- Run of DS01 (DS-v1): mark `⟨0, 0, 0⟩`; `push` of 2 cells into 5 (block 6 on `[2, 3]`); mark
`⟨0, 1, 2⟩`; `push` of 1 cell into 6 (block 7 on `[4]`). -/
def ds01o : List DOp := setup1 ++ [.mark 0, .push 0 2 5, .mark 0, .push 0 1 6]
/-- State reached by `ds01o` (§57; DS-v1). -/
def ds01 : DState := dfinal K0 [] ds01o

/-- **DS01** (draft `case_rewind`; DS-v1 "rewind m … rejects if an active authority derived from
internal covers a cell above m, otherwise returns those cells to available and removes m and every
mark above it"; class Lib). `rewind ⟨0, 1, 2⟩` while block 7, active and derived from `internal`
5, covers cell 4 above the mark; then after the program releases 7. Expected (DS-v1, draft):
`reject`, then `ok` with top 2, block 6 kept, mark `⟨0, 0, 0⟩` kept. Obtained: `reject` (`split` of
`internal` on `[4]` rejected, §43 case 3, §61.1), then `ok` with that metadata (§62, §61). Twins:
the same sequence without the second `push`, `ok`; and the run with `release(7)` before the
`rewind`, `ok`. -/
theorem DS01 : DRunsTo K0 [] ds01o ds01 ∧
    ds01.kern.A[7]? = some ⟨.modify, some 5, [4], .place 6, true⟩ ∧
    RewindStep K0 0 ⟨0, 1, 2⟩ ds01 .reject ∧
    DRuns K0 [] (setup1 ++ [.mark 0, .push 0 2 5, .mark 0, .rewind 0 ⟨0, 1, 2⟩]) ∧
    DRuns K0 [] (ds01o ++ [.kernel (.release 7), .rewind 0 ⟨0, 1, 2⟩]) ∧
    (dfinal K0 [] (ds01o ++ [.kernel (.release 7), .rewind 0 ⟨0, 1, 2⟩])).stacks =
      [⟨1, 5, [2, 3, 4], 2, [⟨0, 2, 6, 5⟩], [⟨0, 0, 0⟩]⟩] :=
  ⟨druns (by decide), by decide, drejects (k := K0) (o := .rewind 0 ⟨0, 1, 2⟩) (by decide),
    druns (by decide), druns (by decide), by decide⟩

/-- Run of DS02 (DS-v1): the run of DS01, `release(7)`, `rewind ⟨0, 1, 2⟩` (top back to 2), then a
new mark at the same top: `⟨0, 2, 2⟩`. -/
def ds02o : List DOp := ds01o ++ [.kernel (.release 7), .rewind 0 ⟨0, 1, 2⟩, .mark 0]
/-- State reached by `ds02o` (§57; DS-v1). -/
def ds02 : DState := dfinal K0 [] ds02o

/-- **DS02** (draft `case_aba`; DS-v1 "marks carry stack identity and a fresh mark identifier";
"rewind m fails on a dead … mark"; class Lib). ABA: the top is back at 2, the top of the removed
mark `⟨0, 1, 2⟩`, and a new mark `⟨0, 2, 2⟩` is live there. Expected (DS-v1, draft): `rewind` of the
removed mark `fail`, of the new mark `ok`. Obtained: `fail`, with no other outcome (§58;
`rewind_dead_fails`), and `ok`. Twin of the `fail`: `rewind` of the new mark at the same position,
`ok`. -/
theorem DS02 : DRunsTo K0 [] ds02o ds02 ∧
    ds02.stacks = [⟨1, 5, [2, 3, 4], 2, [⟨0, 2, 6, 5⟩], [⟨0, 0, 0⟩, ⟨0, 2, 2⟩]⟩] ∧
    (RewindStep K0 0 ⟨0, 1, 2⟩ ds02 .fail ∧ ∀ o, RewindStep K0 0 ⟨0, 1, 2⟩ ds02 o → o = .fail) ∧
    DRuns K0 [] (ds02o ++ [.rewind 0 ⟨0, 2, 2⟩]) :=
  ⟨druns (by decide), by decide,
    rewind_dead_fails (st := ⟨1, 5, [2, 3, 4], 2, [⟨0, 2, 6, 5⟩], [⟨0, 0, 0⟩, ⟨0, 2, 2⟩]⟩)
      (by decide) (by decide),
    druns (by decide)⟩

/-- Run of DS03 (DS-v1): the run of DS02, then `grow` of block 6 (`[2, 3]`, at the top) by one
cell. -/
def ds03o : List DOp := ds02o ++ [.grow 0 6 1]
/-- State reached by `ds03o` (§57; DS-v1). -/
def ds03 : DState := dfinal K0 [] ds03o

/-- **DS03** (draft `case_grow`; DS-v1 "grow is in place only (same base, extension into the space
directly after the block, fail otherwise)"; class Lib). `grow(6, 1)` with one cell after the block;
then `grow(9, 1)` with no cell left; then `grow(6, 1)` of the replaced block. Expected (DS-v1):
`ok` (block `⟨0, 3, 9, 5⟩` of the same base and destination, authority 9 on `[2, 3, 4]`), `fail`;
for the replaced block, none from the source, to arbitrate: DS-v1 says nothing of a `b` that is no
block of the stack (the `reject` of the draft `case_grow` is module behaviour, not a source).
Obtained: `ok` (`release`, `split`, `store`, §62, §61, §65) with that block and footprint; `fail`
(no room, availability §77.4; readings DS-R5, DS-R6); `reject` (6 is no block of the stack;
reading DS-R5, which records no alternative for it). Twin of the `fail` and of the `reject`:
`grow(6, 1)` with one cell after the block, the `ok` step of this run. **MISMATCH** in form for the
replaced block (expected "to arbitrate", obtained `reject`); cause: open obligation, DS-v1 leaves
the outcome open and the stack module reads it as `reject` (DataStack reading DS-R5). -/
theorem DS03 : DRunsTo K0 [] ds03o ds03 ∧
    ds03.stacks = [⟨1, 5, [2, 3, 4], 3, [⟨0, 3, 9, 5⟩], [⟨0, 0, 0⟩, ⟨0, 2, 2⟩]⟩] ∧
    ds03.kern.afp 9 = [2, 3, 4] ∧
    GrowStep K0 0 9 1 ds03 .fail ∧ GrowStep K0 0 6 1 ds03 .reject :=
  ⟨druns (by decide), by decide, by decide, dfails (k := K0) (o := .grow 0 9 1) (by decide),
    drejects (k := K0) (o := .grow 0 6 1) (by decide)⟩

/-- **DS04** (DS-v1 "grow is in place only (…, extension into the space directly after the block,
fail otherwise)"; class Lib). In the state of DS01, `grow(6, 1)` of block 6 (`[2, 3]`), live but not
the last one: block 7 occupies cell 4 after it. Expected (DS-v1): `fail` (the draft's `grow`, which
handled the last block only, rejected; reading DS-R5). Obtained: `fail` (release of 6, static
checks, then `InPlace` fails, §77.4). Twin: the same sequence without the second `push`, `ok`. -/
theorem DS04 : DRunsTo K0 [] ds01o ds01 ∧ GrowStep K0 0 6 1 ds01 .fail ∧
    DRuns K0 [] (setup1 ++ [.mark 0, .push 0 2 5, .mark 0, .grow 0 6 1]) :=
  ⟨druns (by decide), dfails (k := K0) (o := .grow 0 6 1) (by decide), druns (by decide)⟩

/-- State reached by `setup1` (§57; DS-v1): stack 0 with 3 cells, top 0. -/
def ds05 : DState := dfinal K0 [] setup1

/-- **DS05** (draft `case_static_before_fail`, `push 0 4 5`; DS-v1 "push and grow use the derived
issue"; class Lib). `push` of 4 cells into 5 on a stack of 3 cells. Expected: none from the source,
to arbitrate: DS-v1 does not settle a `push` without room; reading DS-R7 gives `fail`
(availability, §77.4), its recorded alternative `reject` ("region belongs to the administered
storage", §77.2, static). Obtained: `fail` (static checks of §77.1, §77.2 hold, then no room;
availability §77.4, reading DS-R7). Twin: `push` of the 3 cells, `ok`. **MISMATCH** in form
(expected "to arbitrate", obtained `fail`); cause: open obligation, DS-v1 leaves the outcome open
and the stack module reads it as `fail` (DataStack reading DS-R7). -/
theorem DS05 : DRunsTo K0 [] setup1 ds05 ∧ PushStep K0 0 4 5 ds05 .fail ∧
    DRuns K0 [] (setup1 ++ [.push 0 3 5]) :=
  ⟨druns (by decide), dfails (k := K0) (o := .push 0 4 5) (by decide), druns (by decide)⟩

/-- Run of DS06 (DS-v1): mark `⟨0, 0, 0⟩`, `push` of one cell into 5 (block 6), mark `⟨0, 1, 1⟩`,
`release(6)`, `rewind ⟨0, 0, 0⟩`. -/
def ds06o : List DOp :=
  setup1 ++ [.mark 0, .push 0 1 5, .mark 0, .kernel (.release 6), .rewind 0 ⟨0, 0, 0⟩]
/-- State reached by `ds06o` (§57; DS-v1). -/
def ds06 : DState := dfinal K0 [] ds06o

/-- **DS06** (brief "rewind of a dead mark (fail)"; DS-v1 "rewind m fails on a dead … mark" and
"removes m and every mark above it"; class Lib). `rewind ⟨0, 1, 1⟩` after `rewind ⟨0, 0, 0⟩`
removed it as a later mark. Expected (DS-v1): `fail`. Obtained: `fail`, with no other outcome (§58;
`rewind_dead_fails`); both marks are gone. Twin: the same sequence without `rewind ⟨0, 0, 0⟩`:
`rewind ⟨0, 1, 1⟩`, `ok`. -/
theorem DS06 : DRunsTo K0 [] ds06o ds06 ∧ ds06.stacks = [⟨1, 5, [2, 3, 4], 0, [], []⟩] ∧
    (RewindStep K0 0 ⟨0, 1, 1⟩ ds06 .fail ∧ ∀ o, RewindStep K0 0 ⟨0, 1, 1⟩ ds06 o → o = .fail) ∧
    DRuns K0 [] (setup1 ++ [.mark 0, .push 0 1 5, .mark 0, .kernel (.release 6),
      .rewind 0 ⟨0, 1, 1⟩]) :=
  ⟨druns (by decide), by decide,
    rewind_dead_fails (st := ⟨1, 5, [2, 3, 4], 0, [], []⟩) (by decide) (by decide),
    druns (by decide)⟩

/-! ## Several stacks (DS-v1; §56) -/

/-- Two stacks (DS-v1, §72, §60, §65, §76 read for a stack): frame 1 with the stack values 0 and 8,
the storages 1 (cells 2, 3, 4) and 9 (cells 10, 11), the destinations 5, 6, 7, 12 (root
authorities 0 on 0, 1 on 1, 2 on 5, 3 on 6, 4 on 7, 5 on 8, 6 on 9, 7 on 12); `internal` 8 on the
cells of 1, stored into 0, stack 0; `internal` 9 on the cells of 9, stored into 8, stack 1. -/
def setup2 : List DOp :=
  [.kernel (.enter [] [lf, lf, pt 1, pt 1, pt 1, lf, lf, lf, lf, lf, pt 9, pt 9, lf]),
    .kernel (.derive 1 [2, 3, 4] .modify), .kernel (.store 8 0), .newStack 1 8,
    .kernel (.derive 6 [10, 11] .modify), .kernel (.store 9 8), .newStack 9 9]
/-- State reached by `setup2` (§57; DS-v1). -/
def ds07 : DState := dfinal K0 [] setup2

/-- **DS07** (draft `case_stacks`, first part; §56 "An authority identity may serve as `internal`
for at most one live administrative abstraction"; class Lib). A second `newStack` with `internal`
8, already the `internal` of the live stack 0. Expected (§56, draft): `reject`. Obtained: `reject`
by the guard of §56 alone: the other preconditions (`NewArenaBase`, §76.1–§76.3, §76.5 read for a
stack) hold. Twin: the same sequence without the first registration of 8, `ok`. The draft's
conjuncts on a kernel `newArena` have no counterpart here: the stack-library state holds no arena
registry (cross-registry cases of §56 belong to another module). -/
theorem DS07 : DRunsTo K0 [] setup2 ds07 ∧ NewStackStep [] 1 8 ds07 .reject ∧
    NewArenaBase ds07.kern 1 8 ∧ ¬ Guard56 [stackInternals ds07.kern ds07.stacks] 8 ∧
    DRuns K0 [] [.kernel (.enter [] [lf, lf, pt 1, pt 1, pt 1, lf, lf, lf, lf, lf, pt 9, pt 9,
      lf]), .kernel (.derive 1 [2, 3, 4] .modify), .kernel (.store 8 0),
      .kernel (.derive 6 [10, 11] .modify), .kernel (.store 9 8), .newStack 9 9, .newStack 1 8] :=
  ⟨druns (by decide), drejects (k := K0) (o := .newStack 1 8) (by decide), by decide, by decide,
    druns (by decide)⟩

/-- Run of DS08 (DS-v1): on the two stacks, mark `⟨0, 0, 0⟩`; `push` of one cell of stack 0 into 5
(block 10 on `[2]`); `push` of one cell of stack 1 into 12 (block 11 on `[10]`); mark
`⟨1, 1, 1⟩`. -/
def ds08o : List DOp := setup2 ++ [.mark 0, .push 0 1 5, .push 1 1 12, .mark 1]
/-- State reached by `ds08o` (§57; DS-v1). -/
def ds08 : DState := dfinal K0 [] ds08o

/-- **DS08** (draft `case_stacks`, second part; brief "rewind … of a foreign mark (fail)"; DS-v1
"marks carry stack identity"; "rewind m fails on a dead or foreign mark"; class Lib). Each stack
has its own top, blocks and marks. `rewind ⟨0, 0, 0⟩` of stack 0 while block 10 lives; `rewind` of
stack 0 to the mark `⟨1, 1, 1⟩` of stack 1; `rewind` of stack 1 to its mark, then a new `push` on
it. Expected (draft, DS-v1): `reject`, `fail`, `ok`. Obtained: `reject` (§43 case 3, §61.1),
`fail` with no other outcome (§58; `rewind_dead_fails`), `ok`. Twins: after `release(10)`,
`rewind ⟨0, 0, 0⟩` of stack 0, `ok`; the foreign mark rewound on its own stack, `ok`. -/
theorem DS08 : DRunsTo K0 [] ds08o ds08 ∧
    ds08.stacks = [⟨1, 8, [2, 3, 4], 1, [⟨0, 1, 10, 5⟩], [⟨0, 0, 0⟩]⟩,
      ⟨9, 9, [10, 11], 1, [⟨0, 1, 11, 12⟩], [⟨1, 1, 1⟩]⟩] ∧
    RewindStep K0 0 ⟨0, 0, 0⟩ ds08 .reject ∧
    DRuns K0 [] (ds08o ++ [.kernel (.release 10), .rewind 0 ⟨0, 0, 0⟩]) ∧
    (RewindStep K0 0 ⟨1, 1, 1⟩ ds08 .fail ∧ ∀ o, RewindStep K0 0 ⟨1, 1, 1⟩ ds08 o → o = .fail) ∧
    DRuns K0 [] (ds08o ++ [.rewind 1 ⟨1, 1, 1⟩, .push 1 1 6]) :=
  ⟨druns (by decide), by decide, drejects (k := K0) (o := .rewind 0 ⟨0, 0, 0⟩) (by decide),
    druns (by decide),
    rewind_dead_fails (st := ⟨1, 8, [2, 3, 4], 1, [⟨0, 1, 10, 5⟩], [⟨0, 0, 0⟩]⟩) (by decide)
      (by decide),
    druns (by decide)⟩

/-! ## Multi-stack frame scenario (DS-v1; §36, §69, §72, §73) -/

/-- Entry of DS09 (§72, §60; DS-v1): on the two stacks, the caller pushes one cell of stack 0 into
5 (block 10), derives 11 (`Modify` on the stack value 0) and 12 (`Modify` on the stack value 8),
and enters frame 2 with the parameters 11 and 12 and the locals 13 and 14 (root authorities 13,
14). -/
def ds09e : List DOp :=
  setup2 ++ [.push 0 1 5, .kernel (.derive 0 [0] .modify), .kernel (.derive 5 [8] .modify),
    .kernel (.enter [11, 12] [lf, lf])]
/-- Run of DS09 up to the exit (DS-v1): the callee marks both stacks at entry (`⟨0, 0, 1⟩`,
`⟨1, 1, 0⟩`), pushes one cell of stack 0 into its local 13 (block 15 on `[3]`) and two cells of
stack 1 into its local 14 (block 16 on `[10, 11]`). -/
def ds09o : List DOp := ds09e ++ [.mark 0, .mark 1, .push 0 1 13, .push 1 2 14]
/-- State reached by `ds09o` (§57; DS-v1). -/
def ds09 : DState := dfinal K0 [] ds09o
/-- The exit of DS09 (§69, §73; DS-v1): `endUse` of the locals 13 and 14 (their blocks are
released), `rewind` of both stacks to the entry marks, `exitFrame`. -/
def ds09x : List DOp :=
  ds09o ++ [.kernel (.endUse 13), .kernel (.endUse 14), .rewind 0 ⟨0, 0, 1⟩, .rewind 1 ⟨1, 1, 0⟩,
    .kernel .exit]

/-- **DS09** (brief, multi-stack frame scenario; draft `case_frame`, one stack; DS-v1 `mark`,
`push`, `rewind`; §36 `Modify` on each stack value, §69, §72, §73; class Lib). A callee frame marks
two stacks at entry, pushes into its locals from both, and at exit ends its locals, rewinds both
stacks to the entry marks and exits. Expected (brief, draft): every step `ok`, the stacks ending as
at entry; `rewind` before the end of the locals `reject` (draft `case_frame`). Obtained: every step
`ok`; after the exit the stack metadata equal those at entry (block 10 of the caller kept, the
callee's blocks and marks removed); `rewind ⟨0, 0, 1⟩` before `endUse` `reject` (block 15 covers
cell 3 above the mark, §43 case 3, §61.1). Twin of the `reject`: after `endUse` of the local 13,
the same `rewind`, `ok` (the run `ds09x`). -/
theorem DS09 : DRunsTo K0 [] ds09o ds09 ∧
    ds09.stacks = [⟨1, 8, [2, 3, 4], 2, [⟨0, 1, 10, 5⟩, ⟨1, 1, 15, 13⟩], [⟨0, 0, 1⟩]⟩,
      ⟨9, 9, [10, 11], 2, [⟨0, 2, 16, 14⟩], [⟨1, 1, 0⟩]⟩] ∧
    RewindStep K0 0 ⟨0, 0, 1⟩ ds09 .reject ∧ DRuns K0 [] ds09x ∧
    (dfinal K0 [] ds09x).stacks = (dfinal K0 [] ds09e).stacks :=
  ⟨druns (by decide), by decide, drejects (k := K0) (o := .rewind 0 ⟨0, 0, 1⟩) (by decide),
    druns (by decide), by decide⟩

/-- Run of DS10 (DS-v1; §72): as DS09, but the callee receives only 11 (`Modify` on the stack value
0) and no right on the stack value 8; it marks stack 0 and pushes one cell of it into its local 13
(block 14). -/
def ds10o : List DOp :=
  setup2 ++ [.push 0 1 5, .kernel (.derive 0 [0] .modify), .kernel (.enter [11] [lf, lf]),
    .mark 0, .push 0 1 13]
/-- State reached by `ds10o` (§57; DS-v1). -/
def ds10 : DState := dfinal K0 [] ds10o

/-- **DS10** (multi-stack frame scenario, right on each stack value; §36 "`MetaRight` requires
`Modify` exercisable on the administering value", §77.1; DS-v1 "push … use[s] the derived issue";
class Lib). The callee, without a right on the stack value 8, pushes two cells of stack 1 into its
local 14. Expected (§36, §77.1): `reject`. Obtained: `reject`: `MetaRight` fails for stack 1, while
the callee has `Modify` on the destination 14. Twin: the same sequence with the parameter 12
(`Modify` on the stack value 8) passed at entry, `ok`. -/
theorem DS10 : DRunsTo K0 [] ds10o ds10 ∧ PushStep K0 1 2 14 ds10 .reject ∧
    ds10.stacks[1]? = some ⟨9, 9, [10, 11], 0, [], []⟩ ∧
    ¬ MetaRight ds10.kern (Stack.entry ⟨9, 9, [10, 11], 0, [], []⟩) ∧
    HasRight ds10.kern .modify 14 ∧
    DRuns K0 [] (ds09e ++ [.mark 0, .push 0 1 13, .push 1 2 14]) :=
  ⟨druns (by decide), drejects (k := K0) (o := .push 1 2 14) (by decide), by decide, by decide,
    by decide, druns (by decide)⟩

end Ern.Corpus.DataStack
