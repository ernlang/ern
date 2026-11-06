import Ern.Corpus.Runner

/-!
# Corpus MM3-H: access discipline, sections A–F, H, I (test module)

The cases of corpus MM3-H of the Jalon 3 material (`ERN_Jalon3_materiel.md`, §1; non-normative
design material), run on the reference kernel and arena of
`specs/ERN_Memory_Model_Specification_v0.1.md` (§60–§78), plus new cases fixed by spec clauses and
the usage scenario W3 (material §5b). This is a test module: no model module imports it.

Each case is a run from `LState.init statics` (§47) by the runner (`Ern.Corpus.Runner`):
`RunsTo k statics os L` states that every step is `ok` and that `L` is library-reachable and its
kernel state `Reachable` (§57). The verdict of the step under test is stated with the relation of
its operation (`DeriveStep`, `TransferStep`, `IssueD`, `ResetD`, …) on the reached state and
decided by `decide`. Each docstring gives the expected verdict from the case's source (the
material, or the spec clause for new cases), the obtained verdict, the class (material §0, rule 5:
`N3` kernel, `Lib` library instance, `spec 3` another specification) and the positive twin (rule 2:
the same sequence without the faulty element, accepted). A case whose obtained verdict differs from
the expected one is kept with its expected verdict and marked **MISMATCH** with its cause; no case
is corrected. Where spec v0.1 or an arbitration of the corpus owner changes the expected verdict a
case had under spec v0 (H21, H49, H50, H51), its docstring gives the historical expected verdict,
its justification, the new expected verdict and the v0.1 clause that decides it; H16 gives the
same history for its spec v0 mismatch, which v0.1 closes.

Twins that are not literally the same sequence without one faulty step:
* another destination, target, parameter or identity in place of the faulty one: H04 (the other
  element), H13 (`z`), H18 (the local leaf 3), H21 (a `Modify` parameter), H25 (a `Modify`
  parameter on the static), H29 (a `Modify` parameter), H50 `transfer` (the stored authority on
  the local 4), H50 `issue` (the value 2), H51 direct form (the view on `u`), S63_8 (the stored
  authority on the local 6), S56 (`internal` 5), S77_2 (the destination 3 outside the region,
  `fail`; the available region `[6]`, `ok`), B45 (the pin of `S` removed, so the obligation of
  `pin(f1)` has identity 0 and `ExternalDone` names 0);
* further steps that lift the blocking before the step under test: H11 (`endUse` of `v2` and of
  the leaf 6), H17 (`endUse` of the block value, then `free` of the storage 4 instead of the leaf
  5), H19 (`endUse` of the child value), H26 second twin (the contract with `ExternalDone` on the
  obligation, then `unpin`), H27b (three `release`), W3 (`endUse` of the structure);
* a pairing given by the material: H05 (its own twin), H21b (H37);
* a faulty element of several steps, removed: H03, S77_6 (`derive` and `store`), H51 through a
  helper (the view, or its `store`), H49 `endUse` of the block values (the six steps of the cycle);
* no twin, by arbitration: the `reset` `reject` in the state `h49` of H49, which persists without
  the cycle (on `fao` the blocks are still held by the values 2 and 3, §78.2).

Local shapes are lists of (parent, kind) (§72, §71.1); `lf` is a root leaf, `pt p` a part of `p`.
Place and authority identities are list indices (§38): `enterFrame` appends the locals and one
root authority per root local; `alloc` appends the shape and one root authority; `derive` and
`split` append the derived authorities; `issue` appends one block authority; `reset` appends one
(released) authority.

Not encoded here:
* section G (H30–H34b, H44, handle pools) and the usage scenarios W1, W2 (they use a handle pool):
  `Ern.Corpus.Lib`;
* the cross-registry cases of §56 (a pool and an arena, or two pools, on one `internal`):
  `Ern.Corpus.Lib`; only the arena registry exists here (`S56`);
* section J, out of the kernel, classified by the material: H38 get-or-insert cache (spec 3,
  flow-sensitive liveness, §25, §32); H39 suspended coroutine holding a `Modify` parameter
  (specs 2 and 3, §29, §81); H40 raw pointer used during a call (spec 3 and the boundary of §19,
  §81); H41 concurrent `writeShared` (spec 2, §18, §24, §68); H42 `defer free(x)` then
  `transfer(x)` (spec 3, `defer` is outside the kernel, §73, §81); H43 resource with a release
  obligation (resource specification, §7).
-/

namespace Ern.Corpus.MM3H

open Ern.MemoryModel.Access Ern.MemoryModel.Arena Ern.Corpus

/-! ## Test contracts and shapes (§48, §72) -/

/-- The empty test contract (§48): nothing shared, pinned, externally done or deallocable. -/
abbrev K0 : K := KD.toK {}

/-- A root leaf of a local shape (§72, §71.1). -/
abbrev lf : Option Nat × Nat := (none, 0)

/-- A leaf part of the shape element `p` (§72, §71.1). -/
abbrev pt (p : Nat) : Option Nat × Nat := (some p, 0)

/-- A structure 0 with the parts 1 and 2 (§40, §72). -/
def S2 : LocalShape := [lf, pt 0, pt 0]

/-- A write of `ls` rejected for every authority of the state is rejected for every authority
(§67.1: the writing authority is exercisable, hence exists, §43). -/
theorem write_rejected {s : S3} {ls : List Nat}
    (h : ∀ a ∈ List.range s.A.length, ¬ Write3Pre s a ls) (a : Nat) :
    Write3Step a ls s .reject :=
  .reject fun hp => h a (List.mem_range.2 (exercisable_lt hp.exercisable)) hp

/-- A read of `ls` rejected for every authority of the state is rejected for every authority
(§66.2: the reading authority is exercisable, hence exists, §43). -/
theorem read_rejected {s : S3} {ls : List Nat}
    (h : ∀ a ∈ List.range s.A.length, ¬ Read3Pre s a ls) (a : Nat) :
    Read3Step a ls s .reject :=
  .reject fun hp => h a (List.mem_range.2 (exercisable_lt hp.exercisable)) hp

/-- The preconditions §63.1–§63.7 of `transfer`, the fields of `TransferPre` but `noSelfLock`
(§63.8) and `dstUsableAfter` (§63.9): used to show which of §63.8 and §63.9 rejects a transfer. -/
def TransferPre637 (k : K) (s : S3) (src dst : Nat) : Prop :=
  s.Usable src ∧ s.Usable dst ∧ HasRight s .modify src ∧ HasRight s .modify dst ∧
    SameShape s.P src dst ∧ (∀ l ∈ footprint s.P src, s.I l = .init) ∧
    (∀ l ∈ footprint s.P dst, s.I l ≠ .init) ∧ ¬ overlap s.P src dst ∧
    (∃ g ∈ List.range s.A.length, Grounds s .modify src g ∧
      ∀ j ∈ List.range s.A.length, ActiveDerivedOutside s src j → RightChain s g j) ∧
    (∀ l ∈ footprint s.P src, ¬ k.Pinned l ∧ s.pin l = false) ∧
    (∀ x ∈ movedDeps s src, s.Active x) ∧ AnchorOrder (transferEff s src dst) ∧
    (∀ x ∈ List.range s.A.length, AnchorMoves s src x →
      ∀ q ∈ List.range s.P.length, (transferEff s src dst).Usable q →
        OptP ((transferEff s src dst).A[x]?) (fun y => y.active = true → y.holder = .place q →
          EffAnchorOK (transferEff s src dst) x ((transferEff s src dst).pframe q)) True)

/-- Decidability of `TransferPre637` (§63). -/
instance (k : K) [DecidablePred k.Pinned] (s : S3) (src dst : Nat) :
    Decidable (TransferPre637 k s src dst) := by
  unfold TransferPre637; infer_instance

/-- §69.2, last sentence: no authority that the effect of `endUse(p)` makes inactive has an active
descendant that the effect does not make inactive; the field `keptDesc` of `EndUsePre`. -/
def EndUseKeptDesc (s : S3) (p : Nat) : Prop :=
  ∀ a ∈ List.range s.A.length, ∀ j ∈ List.range s.A.length, s.Active a →
    ¬ (endUseEff s p).Active a → a ∈ s.ancs j → ¬ (endUseEff s p).Active j

/-- Decidability of `EndUseKeptDesc` (§69.2). -/
instance (s : S3) (p : Nat) : Decidable (EndUseKeptDesc s p) := by
  unfold EndUseKeptDesc; infer_instance

/-- The static preconditions of `issue` other than local self-blocking prevention (§77.1, §77.2),
the fields of `IssueStatic` but `dstNotIn`: used to show that this clause alone rejects. -/
def IssueStaticBut (s : S3) (E : ArenaEntry) (region : List Nat) (dst : Nat) : Prop :=
  s.Active E.internal ∧ MetaRight s E ∧ (∀ l ∈ region, l ∈ footprint s.P E.storage) ∧
    s.Usable dst ∧ isLeaf s.P dst ∧
    (∀ j ∈ List.range s.A.length,
      OptP (s.A[j]?) (fun z => z.active = true → z.holder ≠ .place dst) True) ∧
    HasRight s .modify dst

/-- Decidability of `IssueStaticBut` (§77). -/
instance (s : S3) (E : ArenaEntry) (region : List Nat) (dst : Nat) :
    Decidable (IssueStaticBut s E region dst) := by
  unfold IssueStaticBut; infer_instance

/-! ## A. Exclusivity and indirect aliasing -/

/-- Run of H01 (§72, §60): frame 1 with structure 0 (parts 1, 2, root authority 0);
`derive(0, [1, 2], Modify)` gives the first parameter, authority 1. -/
def h01o : List Op := [.enter [] S2, .derive 0 [1, 2] .modify]
/-- State reached by `h01o` (§57). -/
def h01 : LState := final K0 [] h01o

/-- **H01** (material §1 A, class N3). Two parameters derived from one local, `Modify` on the
whole, then `Observe` on a part. Expected (material): `reject`. Obtained: `reject`: the root has no
effective mode on the part, covered by the active `Modify` descendant 1 (§43 case 3), so the
`Observe` derivation exceeds it (§60.2). Twin without the first parameter: the `derive` is `ok`;
and the call with the first parameter alone is `ok` (§72). -/
theorem H01 : RunsTo K0 [] h01o h01 ∧ DeriveStep 0 [1] .observe h01.kern .reject ∧
    Runs K0 [] [.enter [] S2, .derive 0 [1] .observe] ∧ Runs K0 [] (h01o ++ [.enter [1] []]) :=
  ⟨runsTo (by decide), .reject (by decide), runsTo (by decide), runsTo (by decide)⟩

/-- Run of H02 (§72, §60): frame 1 with structure 0; authority 1, `Observe` on the whole. -/
def h02o : List Op := [.enter [] S2, .derive 0 [1, 2] .observe]
/-- State reached by `h02o` (§57). -/
def h02 : LState := final K0 [] h02o

/-- **H02** (material §1 A, class N3). `Observe` on the whole, then `Modify` on a part of the same
local. Expected (material): `reject`. Obtained: `reject`: the effective mode of the root on the
part is `Observe` (§43 case 4), below the requested `Modify` (§60.2). Twin without the
observation: `ok`. -/
theorem H02 : RunsTo K0 [] h02o h02 ∧ DeriveStep 0 [1] .modify h02.kern .reject ∧
    Runs K0 [] [.enter [] S2, .derive 0 [1] .modify] :=
  ⟨runsTo (by decide), .reject (by decide), runsTo (by decide)⟩

/-- Run of H03 (§72, §60, §65): frame 1 with X (0, parts `p` = 1 and 2) and Y (leaf 3);
authority 2, `Modify` on `p`, stored into Y. -/
def h03o : List Op := [.enter [] (S2 ++ [lf]), .derive 0 [1] .modify, .store 2 3]
/-- State reached by `h03o` (§57). -/
def h03 : LState := final K0 [] h03o

/-- **H03** (material §1 A, class N3). The value of Y holds (by `store`) a `Modify` derived on the
part `p` of X; a write of `p` through the root of X. Expected (material): `reject`. Obtained:
`reject`: the root has no effective mode on `p` (§43 case 3, §67.1). Twin without the stored
authority: `ok`. -/
theorem H03 : RunsTo K0 [] h03o h03 ∧ Write3Step 0 [1] h03.kern .reject ∧
    Runs K0 [] [.enter [] (S2 ++ [lf]), .write 0 [1]] :=
  ⟨runsTo (by decide), .reject (by decide), runsTo (by decide)⟩

/-- Run of H04, second half (§72, §60): array 0 (elements 1, 2); authority 1, `Modify` on element
1. -/
def h04o : List Op := [.enter [] S2, .derive 0 [1] .modify]
/-- State reached by `h04o` (§57). -/
def h04 : LState := final K0 [] h04o

/-- **H04** (material §1 A, class N3). Swap of two elements: by `split` then two writes, `ok`; by
two `derive Modify` of the same element, the second `reject`. Expected (material): `ok` /
`reject`. Obtained: `ok` (§61, §67) / `reject` (§43 case 3, §60.2, §85: a second derivation over
the same leaf is not legal merely by having a distinct name). Twin of the rejection: `derive
Modify` of the other element, `ok`. -/
theorem H04 : Runs K0 [] [.enter [] S2, .split 0 [[1], [2]], .write 1 [1], .write 2 [2]] ∧
    RunsTo K0 [] h04o h04 ∧ DeriveStep 0 [1] .modify h04.kern .reject ∧
    Runs K0 [] (h04o ++ [.derive 0 [2] .modify]) :=
  ⟨runsTo (by decide), runsTo (by decide), .reject (by decide), runsTo (by decide)⟩

/-- Run of H05 (§72, §67): structure `x` (0, fields `f` = 1 and 2) and `tmp` (leaf 3); `x`
written. -/
def h05o : List Op := [.enter [] (S2 ++ [lf]), .write 0 [1, 2]]
/-- State reached by `h05o` (§57). -/
def h05 : LState := final K0 [] h05o

/-- **H05** (material §1 A, class N3). `transfer(x, x.f)`; twin `transfer(x.f, tmp)` then
`transfer(tmp, x.f)`, the destination `Moved` and of the same shape. Expected (material):
`reject` / `ok`. Obtained: `reject` (§63.2 shapes differ; §63.3 the destination is `Init` and the
footprints overlap) / `ok`. -/
theorem H05 : RunsTo K0 [] h05o h05 ∧ TransferStep K0 0 1 h05.kern .reject ∧
    Runs K0 [] (h05o ++ [.transfer 1 3, .transfer 3 1]) :=
  ⟨runsTo (by decide), .reject (by decide), runsTo (by decide)⟩

/-- **H06** (material §1 A, class N3). `derive Modify`, `derive Observe` below it, `release` of
both, then a write through the root. Expected (material): `ok`. Obtained: `ok` at every step
(§60, §62 effect: effective modes of the origins are recomputed, §43, §67). -/
theorem H06 : Runs K0 [] [.enter [] [lf], .derive 0 [0] .modify, .derive 1 [0] .observe,
    .release 2, .release 1, .write 0 [0]] :=
  runsTo (by decide)

/-! ## B. Lifetime and escape -/

/-- One static leaf, `Uninit` (§47). -/
def stS : Statics := [((none, none, 0), false)]

/-- Prefix of H07 (§60, §72, §67): the base frame passes 1, `Modify` on the static 0, to frame 1;
frame 1 writes its local `L` (1), derives 3, `Observe` on `L`, and calls frame 2 with `[1, 3]`;
frame 2 writes its local `W` (2). -/
def h07p : List Op := [.derive 0 [0] .modify, .enter [1] [lf], .write 2 [1],
  .derive 2 [1] .observe, .enter [1, 3] [lf], .write 4 [2]]
/-- Run of H07 (§64): `W` depends on 3, anchored on the caller's local `L`. -/
def h07o : List Op := h07p ++ [.depend 2 3]
/-- State reached by `h07o` (§57). -/
def h07 : LState := final K0 stS h07o

/-- **H07** (material §1 B, class N3). The callee stores into a static, through its `Modify`
parameter on it, a value anchored on a local of the caller. Expected (material): `reject` at the
`transfer`. Obtained: `reject`: in the resulting state the anchor of the static has an effective
anchor of frame 1, not an ancestor of the frame 0 of the static (§44 `AnchorOrder`, §63.6). Twin
without the anchor: `ok`. -/
theorem H07 : RunsTo K0 stS h07o h07 ∧ TransferStep K0 2 0 h07.kern .reject ∧
    Runs K0 stS (h07p ++ [.transfer 2 0]) :=
  ⟨runsTo (by decide), .reject (by decide), runsTo (by decide)⟩

/-- Prefix of H08 and H09 (§72, §60): frame 1 with `X` (0), written, and the result `R` (1);
parameters 2 (`Modify` on `X`) and 3 (`Modify` on `R`) passed to frame 2, which has `W` (2) and
`Lc` (3), roots 4 and 5. -/
def h89 : List Op := [.enter [] [lf, lf], .write 0 [0], .derive 0 [0] .modify,
  .derive 1 [1] .modify, .enter [2, 3] [lf, lf]]

/-- **H08** (material §1 B, class N3). A return anchored on a derivation (7) of a derivation (6)
of the parameter 2: `transfer` of `W` into `R`, then `exitFrame`. Expected (material): `ok`.
Obtained: `ok` (§44, §63.6, §73.4 reanchoring, §79). -/
theorem H08 : Runs K0 [] (h89 ++ [.derive 2 [0] .observe, .derive 6 [0] .observe, .write 4 [2],
    .depend 2 7, .transfer 2 1, .exit]) :=
  runsTo (by decide)

/-- Run of H09 (§60, §64): `W` depends on 7, derived from 6, derived from the root 5 of the
callee's local `Lc`. -/
def h09o : List Op := h89 ++ [.derive 5 [3] .observe, .derive 6 [3] .observe, .write 4 [2],
  .depend 2 7]
/-- State reached by `h09o` (§57). -/
def h09 : LState := final K0 [] h09o

/-- **H09** (material §1 B, class N3). A return anchored on a local of the callee through two
derivations. Expected (material): `reject`. Obtained: `reject`: the effective anchor of the moved
anchor is of frame 2, not an ancestor of the frame 1 of `R` (§44, §63.6). Twin without the
anchor: `ok`. -/
theorem H09 : RunsTo K0 [] h09o h09 ∧ TransferStep K0 2 1 h09.kern .reject ∧
    Runs K0 [] (h89 ++ [.derive 5 [3] .observe, .derive 6 [3] .observe, .write 4 [2],
      .transfer 2 1]) :=
  ⟨runsTo (by decide), .reject (by decide), runsTo (by decide)⟩

/-- Prefix of H10 (§60, §64, §65, §67): frame 1 with `X` (0), the container `C` (1, parts 2 and
3) and `T` (4); `A` (3) is `Observe` on `X`; 4, derived from `A`, is stored into the part 2; `C`
depends on `A`. -/
def h10p : List Op := [.enter [] [lf, lf, pt 1, pt 1, lf], .write 0 [0], .derive 0 [0] .observe,
  .derive 3 [0] .observe, .store 4 2, .depend 1 3, .write 1 [3]]
/-- Run of H10 (§63, §69): the part 2 is transferred into `T`, then the container ends. -/
def h10o : List Op := h10p ++ [.transfer 2 4, .endUse 1]
/-- State reached by `h10o` (§57). -/
def h10 : LState := final K0 [] h10o

/-- **H10** (material §1 B, class N3). A part holding an access derived from the anchor `A` of its
container is transferred, the container ends, then `A` ends. Expected (material): `reject` at the
end of `A`. Obtained: `reject`: the transferred access 4, now held by `T`, is an active descendant
of `A` (§62.3; §44: the dependencies of the container do not follow a part transferred in
isolation). Twin without the transfer: the access ends with the container and `release(A)` is
`ok`. -/
theorem H10 : RunsTo K0 [] h10o h10 ∧ ReleaseStep 3 h10.kern .reject ∧
    Runs K0 [] (h10p ++ [.endUse 1, .release 3]) :=
  ⟨runsTo (by decide), .reject (by decide), runsTo (by decide)⟩

/-- Run of H11 (§71, §76, §77, §63): frame 1 with arena value 0, allocator 1, values `v1` (2) and
`v2` (3); storage 4 (leaves 5, 6) owned by 0, `internal` its root authority 4; blocks 5 on `[5]`
to `v1` and 6 on `[6]` to `v2`; `v1` transferred into the leaf 6 of the block of `v2`. -/
def h11o : List Op := [.enter [] [lf, lf, lf, lf], .write 1 [1], .alloc 1 0 [lf, pt 4, pt 4],
  .write 0 [0], .newArena 4 4, .issue 0 [5] 2, .issue 0 [6] 3, .transfer 2 6]
/-- State reached by `h11o` (§57). -/
def h11 : LState := final K0 [] h11o

/-- **H11** (material §1 B, class Lib). An arena buffer stored into another block of the same
arena. Expected (material): `transfer` `ok`; `reset` `reject` while one lives. Obtained: the
`transfer` is `ok` (§63; §63.8 holds: block 5 covers 5, not the new holder 6); `reset` is `reject`
(§78.2: block 5 is active and covers leaf 5; `derive` of `internal` over the storage exceeds its
effective right, Part XIV). Twin: after `endUse` of `v2` and of the leaf 6, `reset` is `ok`. -/
theorem H11 : RunsTo K0 [] h11o h11 ∧ ResetD 0 h11 .reject ∧
    Runs K0 [] (h11o ++ [.endUse 3, .endUse 6, .reset 0]) :=
  ⟨runsTo (by decide), rejects (k := K0) (o := .reset 0) (by decide), runsTo (by decide)⟩

/-- Prefix of H12 (§60, §65): frame 1 with `X` (0) and `W` (2) written and `H` (1); 3,
`Observe` on `X`, stored into `H`. -/
def h12p : List Op := [.enter [] [lf, lf, lf], .write 0 [0], .write 2 [2],
  .derive 0 [0] .observe, .store 3 1]
/-- Run of H12 (§64): `W` depends on 3, held by `H`. -/
def h12o : List Op := h12p ++ [.depend 2 3]
/-- State reached by `h12o` (§57). -/
def h12 : LState := final K0 [] h12o

/-- **H12** (material §1 B, class N3). `endUse` of the holder of an anchor while a dependent
lives. Expected (material): `reject`. Obtained: `reject` (§69.3: the usable `W` depends on an
authority held by `H`; §52). Twin without the dependent: `ok`. -/
theorem H12 : RunsTo K0 [] h12o h12 ∧ EndUseStep K0 1 h12.kern .reject ∧
    Runs K0 [] (h12p ++ [.endUse 1]) :=
  ⟨runsTo (by decide), .reject (by decide), runsTo (by decide)⟩

/-! ## C. Ownership and release -/

/-- Run of H13 (§72, §71): frame 1 with allocator 0, `x` (1) and `z` (2), `x` written; `y` (3)
allocated, owned by `x`, its root authority 3 held by `x`. -/
def h13o : List Op := [.enter [] [lf, lf, lf], .write 0 [0], .write 1 [1], .alloc 0 1 [lf]]
/-- State reached by `h13o` (§57). -/
def h13 : LState := final K0 [] h13o

/-- **H13** (material §1 C, class N3). Ownership cycle: `x` owns `y`, then `y` receives `x` by
transfer. Expected (material): `reject`. Obtained: `reject` by §63.8 and §63.9 (§63.1–§63.7
hold): the root authority 3 of `y`, held by `x`, would be held by `corr(x) = y` and covers the leaf
`y` (§63.8, §88); `y` would own itself, so it is not usable in the resulting state (§63.9, §40).
Twin: the transfer of `x` into `z` is `ok`. -/
theorem H13 : RunsTo K0 [] h13o h13 ∧ TransferStep K0 1 3 h13.kern .reject ∧
    TransferPre637 K0 h13.kern 1 3 ∧ ¬ NoLocalSelfLock h13.kern 1 3 ∧
    ¬ (transferEff h13.kern 1 3).Usable 3 ∧ Runs K0 [] (h13o ++ [.transfer 1 2]) :=
  ⟨runsTo (by decide), .reject (by decide), by decide, by decide, by decide, runsTo (by decide)⟩

/-- Test contract of H14, H15 (§70.2, §80): place 2 deallocable by the authority 7. -/
abbrev KF2 : K := KD.toK { dealloc := [2], compat := [(2, 7)] }

/-- Prefix of H14, H15, H26 (§72, §71): frame 1 with allocator 0 and `x` (1), written; storage 2
allocated, owned by `x`. -/
def h14p : List Op := [.enter [] [lf, lf], .write 0 [0], .write 1 [1], .alloc 0 1 [lf]]
/-- Run of H14 (§70): the first `free` of the storage 2. -/
def h14o : List Op := h14p ++ [.free 2 7]
/-- State reached by `h14o` (§57). -/
def h14 : LState := final KF2 [] h14o

/-- **H14** (material §1 C, class N3). `free` twice. Expected (material): the second `reject`.
Obtained: `reject` (§70.3: the root of the freed storage is inactive, §70 effect, so no exercisable
`Modify`). Twin, the run without the second `free`: the first `free` is `ok`. -/
theorem H14 : RunsTo KF2 [] h14o h14 ∧ FreeStep KF2 2 7 h14.kern .reject :=
  ⟨runsTo (by decide), .reject (by decide)⟩

/-- Run of H15 (§71, §60): storage 3 allocated, owned by the storage 2; 4, `Observe` on 3, held by
the frame. -/
def h15o : List Op := h14p ++ [.alloc 0 2 [lf], .derive 3 [3] .observe]
/-- State reached by `h15o` (§57). -/
def h15 : LState := final KF2 [] h15o

/-- **H15** (material §1 C, class N3). `free` of a storage whose owned sub-storage is the origin
of an access held elsewhere. Expected (material): `reject`. Obtained: `reject` (§70.3: an active
derivative over the freed footprint is held by the surviving frame). Twin without the access:
`ok`. -/
theorem H15 : RunsTo KF2 [] h15o h15 ∧ FreeStep KF2 2 7 h15.kern .reject ∧
    Runs KF2 [] (h14p ++ [.alloc 0 2 [lf], .free 2 7]) :=
  ⟨runsTo (by decide), .reject (by decide), runsTo (by decide)⟩

/-- Test contract of H16 (§70.2, §80): place 3 deallocable by the authority 7. -/
abbrev KF3 : K := KD.toK { dealloc := [3], compat := [(3, 7)] }

/-- Prefix of H16 (§72, §71, §60): frame 1 with allocator 0, `x` (1) and the result `R` (2);
storage 3 owned by `x`, written; parameters 4 (`Modify` on `x`) and 5 (`Modify` on `R`) passed to
frame 2, which has the local 4. -/
def h16p : List Op := [.enter [] [lf, lf, lf], .write 0 [0], .write 1 [1], .alloc 0 1 [lf],
  .write 3 [3], .derive 1 [1] .modify, .derive 2 [2] .modify, .enter [4, 5] [lf]]
/-- State reached by `h16p` (§57). -/
def h16a : LState := final KF3 [] h16p
/-- Run of H16 (§63, §70, §73): the callee receives `x` by `transfer` into its local 4, frees the
storage 3 now owned by that local, returns the value by `transfer` into `R` through the parameter
5, then exits. -/
def h16o : List Op := h16p ++ [.transfer 1 4, .free 3 7, .transfer 4 2, .exit]
/-- State reached by `h16o` (§57). -/
def h16 : LState := final KF3 [] h16o

/-- **H16** (material §1 C, class spec 3 by arbitration: reception by value is a calling
convention of Spec 3, §45, §81; non-blocking). The callee receives by transfer a value owning a
storage, frees it, returns the value; the caller reads that storage. Expected (material): `ok`,
then `reject`. Historical (spec v0): same expected verdict; the reception, `transfer` of `x` into
the callee's local, was obtained `reject`, the parameter 4 being an active derived authority
covering `x` held outside it (§63.4 before its v0.1 amendment); **MISMATCH**, case defect. Spec
v0.1 decides the reception `ok`: the parameter 4 is the exercisable authority on which the
`Modify` right over `x` rests, exempt from the check with its origin chain (v0.1 §63.4); the
expected verdict, unchanged, is now the spec's and the mismatch is closed. Obtained: the
reception, the `free` of the storage through the callee's local (§70), the return into `R` (§63)
and the exit (§73) are `ok`; the caller's read of the storage is `reject` for every authority
(§66.1: the leaf belongs to no usable place, §70 effect). Twin without the `free`: the read is
`ok`. -/
theorem H16 : RunsTo KF3 [] h16p h16a ∧ ActiveDerivedOutside h16a.kern 1 4 ∧
    Grounds h16a.kern .modify 1 4 ∧ RunsTo KF3 [] h16o h16 ∧
    (∀ a, Read3Step a [3] h16.kern .reject) ∧
    Runs KF3 [] (h16p ++ [.transfer 1 4, .transfer 4 2, .exit, .read 3 [3]]) :=
  ⟨runsTo (by decide), by decide, by decide, runsTo (by decide), read_rejected (by decide),
    runsTo (by decide)⟩

/-- Test contract of H17 (§70.2, §80): the storage 4 and the region leaf 5 deallocable by the
authority 7, so that only the structural clause can reject. -/
abbrev KF45 : K := KD.toK { dealloc := [4, 5], compat := [(4, 7), (5, 7)] }

/-- Run of H17, H18 (§72, §71, §76, §77): frame 1 with arena value 0, allocator 1, values 2 and 3;
storage 4 (leaves 5, 6) owned by 0; arena on 4 with `internal` 4; block 5 on `[5]` issued to 2. -/
def h17p : List Op := [.enter [] [lf, lf, lf, lf], .write 1 [1], .alloc 1 0 [lf, pt 4, pt 4],
  .write 0 [0], .newArena 4 4, .issue 0 [5] 2]
/-- State reached by `h17p` under `KF45` (§57). -/
def h17 : LState := final KF45 [] h17p

/-- **H17** (material §1 C, class Lib). `free` of an arena block. Expected (material): `reject`.
Obtained: `reject`, even with the region declared deallocable: the leaf 5 is a part of the storage,
not an `OwnedRoot` (§70.1; §9: subplaces returned by an arena are not new allocations). Twin: after
the end of the block (`endUse` of its value), `free` of the allocated storage 4 is `ok`. -/
theorem H17 : RunsTo KF45 [] h17p h17 ∧ FreeStep KF45 5 7 h17.kern .reject ∧
    ¬ OwnedRoot h17.kern 5 ∧ Runs KF45 [] (h17p ++ [.endUse 2, .free 4 7]) :=
  ⟨runsTo (by decide), .reject (by decide), by decide, runsTo (by decide)⟩

/-! ## D. Arenas -/

/-- State reached by `h17p` under `K0` (§57). -/
def h18 : LState := final K0 [] h17p

/-- **H18** (material §1 D, class Lib). The arena value transferred into a block of its own
storage. Expected (material): `reject`. Obtained: `reject`: §63.8 fails, `internal` (the root of
the storage, held by the arena value) would be held by `corr(0) = 5` and covers the leaf 5 (§40,
§88); §63.6 fails as well, the storage becoming owned by its own leaf (no frame for the anchor of
the value 2); §63.9 fails too, that ownership cycle making the leaf 5 unusable in the resulting
state (§40). Twin: the transfer of the arena value into the local leaf 3 is `ok`. -/
theorem H18 : RunsTo K0 [] h17p h18 ∧ TransferStep K0 0 5 h18.kern .reject ∧
    ¬ NoLocalSelfLock h18.kern 0 5 ∧ ¬ (transferEff h18.kern 0 5).Usable 5 ∧
    Runs K0 [] (h17p ++ [.transfer 0 3]) :=
  ⟨runsTo (by decide), .reject (by decide), by decide, by decide, runsTo (by decide)⟩

/-- Run of H19 (§76, §77): storage 4 (leaf 5) owned by the arena value 0; parent arena on 4; block
5 on `[5]` issued to 2; child arena on the leaf 5 with `internal` the block 5, its arena value 2. -/
def h19o : List Op := [.enter [] [lf, lf, lf, lf], .write 1 [1], .alloc 1 0 [lf, pt 4],
  .write 0 [0], .newArena 4 4, .issue 0 [5] 2, .newArena 5 5]
/-- State reached by `h19o` (§57). -/
def h19 : LState := final K0 [] h19o

/-- **H19** (material §1 D, class Lib). Nested arena: `reset` of the parent while the child
lives, then after `endUse` of the child value. Expected (material): `reject`, then `ok`. Obtained:
`reject` (§78.2: the child's `internal`, block 5, is active and covers leaf 5), then `ok` (§69
effect releases it; §78). -/
theorem H19 : RunsTo K0 [] h19o h19 ∧ ResetD 0 h19 .reject ∧
    Runs K0 [] (h19o ++ [.endUse 2, .reset 0]) :=
  ⟨runsTo (by decide), rejects (k := K0) (o := .reset 0) (by decide), runsTo (by decide)⟩

/-- **H20** (material §1 D, class Lib). `alloc`, `newArena`, `issue`, `endUse`, `reset`, then
`issue` of the same region. Expected (material): all `ok`. Obtained: all `ok` (§76–§78, §46,
§86). -/
theorem H20 : Runs K0 [] [.enter [] [lf, lf, lf], .write 1 [1], .alloc 1 0 [lf, pt 3],
    .write 0 [0], .newArena 3 3, .issue 0 [4] 2, .endUse 2, .reset 0, .issue 0 [4] 2] :=
  runsTo (by decide)

/-- Test contract of H21 (§68.1, §80): the arena value 0 is `SharedMutable`. -/
abbrev KA : K := KD.toK { shared := [0] }

/-- Prefix of H21 (§71, §76): frame 1 with arena value 0, allocator 1, buffer 2; storage 3
(leaves 4, 5) owned by 0; arena on 3 with `internal` 3. -/
def h21p : List Op := [.enter [] [lf, lf, lf], .write 1 [1], .alloc 1 0 [lf, pt 3, pt 3],
  .write 0 [0], .newArena 3 3]
/-- Run of H21 (§60, §72, §68): the caller passes 4, `Observe` on the arena value, and 5,
`Modify` on its buffer; the callee (local 6) updates the arena metadata by `writeShared`. -/
def h21o : List Op := h21p ++ [.derive 0 [0] .observe, .derive 2 [2] .modify, .enter [4, 5] [lf],
  .writeShared 4 [0]]
/-- State reached by `h21o` (§57). -/
def h21 : LState := final KA [] h21o

/-- **H21** (material §1 D, class Lib). A callee that only observes the arena issues a block to a
local, then returns the block. Historical expected verdict (material): `ok`, which the Jalon 3
draft obtained through a `writeShared` branch of `MetaRight`; under spec v0 the case was a
**MISMATCH** (expected `ok`, obtained `reject`). New expected verdict (spec v0.1, by arbitration
the obtained one): `reject` at the `issue`, decided by §36 and §77.1: `MetaRight` requires
exercisable `Modify` on the arena value and `writeShared` alone does not satisfy it (v0.1 §36 keeps
this rule; its amendment concerns `alloc` only). Obtained: the `writeShared` on the metadata is
`ok` (§68), the `issue` is `reject`. Twin, the same run with a `Modify` parameter on the arena
value: `issue`, `transfer` of the block value to the caller and `exitFrame` are `ok`. -/
theorem H21 : RunsTo KA [] h21o h21 ∧ IssueD KA 0 [4] 6 h21 .reject ∧
    OptP (h21.arenas[0]?) (fun E => ¬ MetaRight h21.kern E) False ∧
    Runs KA [] (h21p ++ [.derive 0 [0] .modify, .derive 2 [2] .modify, .enter [4, 5] [lf],
      .writeShared 4 [0], .issue 0 [4] 6, .transfer 6 2, .exit]) :=
  ⟨runsTo (by decide), rejects (o := .issue 0 [4] 6) (by decide), by decide, runsTo (by decide)⟩

/-- Run of H21b (§72, §60, §65, §76): frame 1 with the result 0 passes 1, `Modify` on it, to
frame 2, which has the arena value 1 and the local buffer 2 (parts 3, 4); the callee derives 4,
`Modify` on the buffer, stores it into the arena value and creates the arena. -/
def h21bo : List Op := [.enter [] [lf], .derive 0 [0] .modify,
  .enter [1] [lf, lf, pt 2, pt 2], .derive 3 [3, 4] .modify, .store 4 1, .newArena 2 4]
/-- State reached by `h21bo` (§57). -/
def h21b : LState := final K0 [] h21bo

/-- **H21b** (material §1 D, class Lib). An arena on a local buffer, transferred to the caller.
Expected (material): `reject` at the `transfer`. Obtained: `reject`: `internal`, moved to the
caller's place with its anchor, has its effective anchor on the callee's local buffer, so §63.6
(`AnchorOrder`) and §63.7 (`AnchorOrderHeld`) fail in the resulting state (§44, §79). Twin
(material pairing): `H37`, the arena on an allocated storage owned by its value, is `ok`. -/
theorem H21b : RunsTo K0 [] h21bo h21b ∧ TransferStep K0 1 0 h21b.kern .reject ∧
    ¬ AnchorOrderHeld (transferEff h21b.kern 1 0) :=
  ⟨runsTo (by decide), .reject (by decide), by decide⟩

/-! ## E. Pinning and static storage -/

/-- Run of H22 (§72, §74): frame 1 with `x` (0), written and pinned, and `y` (1). -/
def h22o : List Op := [.enter [] [lf, lf], .write 0 [0], .pin 0]
/-- State reached by `h22o` (§57). -/
def h22 : LState := final K0 [] h22o

/-- **H22** (material §1 E, class N3). Transfer of a value whose in-place leaf is pinned / of a
value whose owned storage only is pinned. Expected (material): `reject` / `ok`. Obtained:
`reject` (§63.5) / `ok` (§63.5: owned storage not moved does not prevent the transfer; §87). Twin
of the rejection, without the pin: `ok`. -/
theorem H22 : RunsTo K0 [] h22o h22 ∧ TransferStep K0 0 1 h22.kern .reject ∧
    Runs K0 [] [.enter [] [lf, lf], .write 0 [0], .transfer 0 1] ∧
    Runs K0 [] [.enter [] [lf, lf, lf], .write 0 [0], .write 1 [1], .alloc 0 1 [lf], .pin 3,
      .transfer 1 2] :=
  ⟨runsTo (by decide), .reject (by decide), runsTo (by decide), runsTo (by decide)⟩

/-- Run of H23 (§72, §74): frame 1 calls frame 2, whose local 1 is pinned. -/
def h23o : List Op := [.enter [] [lf], .enter [] [lf], .pin 1]
/-- State reached by `h23o` (§57). -/
def h23 : LState := final K0 [] h23o

/-- **H23** (material §1 E, class N3). Exit of a frame whose local is pinned. Expected (material):
`reject`. Obtained: `reject` (§73.3). Twin without the pin: `ok`. -/
theorem H23 : RunsTo K0 [] h23o h23 ∧ ExitStep K0 h23.kern .reject ∧
    Runs K0 [] [.enter [] [lf], .enter [] [lf], .exit] :=
  ⟨runsTo (by decide), .reject (by decide), runsTo (by decide)⟩

/-- Statics of H24 (§47): the MMIO leaf 0, `Init`, and the leaf 1, `Uninit`. -/
def stM : Statics := [((none, none, 0), true), ((none, none, 0), false)]
/-- Test contract of H24 (§74, §75, §80): the static leaf 0 is `K.Pinned`. -/
abbrev KM : K := KD.toK { pinned := [0] }

/-- **H24** (material §1 E, class N3). A static MMIO region pinned by `K.Pinned`, directly owned
by the base frame (`StaticPinnedBottom`, §75): `transfer` and `endUse`. Expected (material):
`reject`, `reject`. Obtained: `reject` (§63.5), `reject` (§69.4). Twin, the same static not
pinned: both `ok`. -/
theorem H24 : Runs KM stM [] ∧ StaticPinnedBottom KM stM ∧
    TransferStep KM 0 1 (S3.init stM) .reject ∧ EndUseStep KM 0 (S3.init stM) .reject ∧
    Runs K0 stM [.transfer 0 1] ∧ Runs K0 stM [.endUse 0] :=
  ⟨runsTo (by decide), by unfold StaticPinnedBottom; decide, .reject (by decide),
    .reject (by decide), runsTo (by decide), runsTo (by decide)⟩

/-- One static leaf, `Init` (§47). -/
def stW : Statics := [((none, none, 0), true)]
/-- Run of H25 (§72): a call without parameter. -/
def h25o : List Op := [.enter [] []]
/-- State reached by `h25o` (§57). -/
def h25 : LState := final K0 stW h25o

/-- **H25** (material §1 E, class N3). A static written by a callee without parameter. Expected
(material): `reject`. Obtained: `reject` for every authority: the root of the static is held by
the base frame, not the current one, and the callee holds nothing (§43, §28, §90). Twin with a
`Modify` parameter on the static: `ok`. -/
theorem H25 : RunsTo K0 stW h25o h25 ∧ (∀ a, Write3Step a [0] h25.kern .reject) ∧
    Runs K0 stW [.derive 0 [0] .modify, .enter [1] [], .write 1 [0]] :=
  ⟨runsTo (by decide), write_rejected (by decide), runsTo (by decide)⟩

/-- Test contract of H26 (§70.2, §80): place 2 deallocable by the authority 7. -/
abbrev KP : K := KD.toK { dealloc := [2], compat := [(2, 7)] }
/-- Test contract of the twin of H26 (§75, §80): the same, with `ExternalDone` on the pinning
obligation 0. -/
abbrev KPd : K := KD.toK { done := [0], dealloc := [2], compat := [(2, 7)] }
/-- Run of H26 (§74): the allocated storage 2 pinned by the obligation 0, the first installed. -/
def h26o : List Op := h14p ++ [.pin 2]
/-- State reached by `h26o` (§57). -/
def h26 : LState := final KP [] h26o

/-- **H26** (material §1 E, class N3). `free` of a pinned storage; `unpin` without `ExternalDone`.
Expected (material): `reject`, `reject`. Obtained: `reject` (§70.4), `reject` (§75: `unpin` of the
obligation 0, installed by the `pin` of the storage, without `K.ExternalDone` on it). Twins: `free`
without the pin, `ok`; with `ExternalDone` on the obligation 0, `unpin` then `free`, `ok`. -/
theorem H26 : RunsTo KP [] h26o h26 ∧ FreeStep KP 2 7 h26.kern .reject ∧
    UnpinStep KP 0 h26.kern .reject ∧ Runs KP [] (h14p ++ [.free 2 7]) ∧
    Runs KPd [] (h14p ++ [.pin 2, .unpin 0, .free 2 7]) :=
  ⟨runsTo (by decide), .reject (by decide), .reject (by decide), runsTo (by decide),
    runsTo (by decide)⟩

/-- Test contract of B45 (§75, §80): `ExternalDone` on the pinning obligation 1. -/
abbrev KB : K := KD.toK { done := [1] }
/-- Test contract of the twin of B45 (§75, §80): `ExternalDone` on the pinning obligation 0. -/
abbrev KBt : K := KD.toK { done := [0] }
/-- Run of B45 (§72, §67, §74, §75): frame 1 with the structure `S` (0), its part `f1` (1) and the
leaf `d` (2); `f1` written; `pin S` installs obligation 0, `pin f1` obligation 1, both on leaf 1;
`unpin` of obligation 1. -/
def b45o : List Op := [.enter [] [lf, pt 0, lf], .write 0 [1], .pin 0, .pin 1, .unpin 1]
/-- State reached by `b45o` (§57). -/
def b45 : LState := final KB [] b45o

/-- **B45** (new case fixed by spec v0.1 §74, §75; arbitration Q23, B#45; class N3). `pin(S)`,
`pin(f1)`, `unpin` of the obligation of `pin(f1)`, then `transfer(f1, d)`. Historical verdict
(spec v0, per-leaf pin flags, reading B#45): `ok`, the `unpin` of `f1` cleared the flag of leaf 1
although `pin(S)` had pinned it. Expected (v0.1 §75: `unpin` ends the designated obligation only,
and a leaf stays pinned while another active obligation covers it; §74: `transfer` is rejected on
a pinned leaf): `reject`. Obtained: `reject`; leaf 1 is still pinned by the active obligation 0.
Twin, without `pin(S)` (the obligation of `pin(f1)` is then 0, under `KBt`): `transfer` `ok`. -/
theorem B45 : RunsTo KB [] b45o b45 ∧
    b45.kern.pins = [⟨0, [1], true⟩, ⟨1, [1], false⟩] ∧ b45.kern.pin 1 = true ∧
    TransferStep KB 1 2 b45.kern .reject ∧
    Runs KBt [] [.enter [] [lf, pt 0, lf], .write 0 [1], .pin 1, .unpin 0, .transfer 1 2] :=
  ⟨runsTo (by decide), by decide, by decide, .reject (by decide), runsTo (by decide)⟩

/-! ## F. Calls -/

/-- Prefix of H27a (§72, §60): frame 1 with the local 0, written, passes 1, `Modify` on it. -/
def h27ap : List Op := [.enter [] [lf], .write 0 [0], .derive 0 [0] .modify, .enter [1] []]
/-- Run of H27a (§62): the callee releases its parameter. -/
def h27ao : List Op := h27ap ++ [.release 1]
/-- State reached by `h27ao` (§57). -/
def h27a : LState := final K0 [] h27ao

/-- **H27a** (material §1 F, class N3). The callee releases its `Modify` parameter, then tries to
write the caller's local by another path, with no blocking authority in between. Expected
(material): `reject`. Obtained: `reject` for every authority: the root of the local is held by the
caller's frame (§43, §28, §72 last paragraph). Twin, the write through the parameter before its
release: `ok`. -/
theorem H27a : RunsTo K0 [] h27ao h27a ∧ (∀ a, Write3Step a [0] h27a.kern .reject) ∧
    Runs K0 [] (h27ap ++ [.write 1 [0]]) :=
  ⟨runsTo (by decide), write_rejected (by decide), runsTo (by decide)⟩

/-- Prefix of H27b (§72, §71, §60, §65): frame 1 with structure `a` (0, parts 1, 2), structure `b`
(3, parts 4, 5) and allocator 6; storage 7 allocated, owned by `a`, its root authority 3 held by
`a`; 4, `Modify` on 7 from that root; 5, `Modify` on `a`; 6 and 7, `Modify` on 1 and 2 from 5,
stored into 4 and 5; 8, `Modify` on `b`; the call passes 4, 5 and 8. -/
def h27bp : List Op := [.enter [] [lf, pt 0, pt 0, lf, pt 3, pt 3, lf], .write 2 [6],
  .alloc 6 0 [lf], .derive 3 [7] .modify, .derive 0 [1, 2] .modify, .derive 5 [1] .modify,
  .derive 5 [2] .modify, .derive 1 [4, 5] .modify, .store 6 4, .store 7 5, .enter [4, 5, 8] []]
/-- State reached by `h27bp` (§57). -/
def h27b : LState := final K0 [] h27bp

/-- **H27b** (material §1 F, class spec 3). The same attempt after releasing the authorities that
blocked the origin: the callee releases its parameter 4 on the owned storage 7, then the
authorities 6 and 7 that kept its parameter 5 from exercising the root of `a`; the write of 7
through that storage's root 3 is then accepted. Expected (material): `ok` in the kernel, strong
protection deferred to Spec 3. Obtained: at entry the write is `reject` (§72.3); after the
releases, `ok` (§72 last paragraph: entry protection only, the rest deferred to Spec 3). The
storage is allocated (§71) and owned by `a`, since locals are owned directly by their frame (§39,
§72). -/
theorem H27b : RunsTo K0 [] h27bp h27b ∧ Write3Step 3 [7] h27b.kern .reject ∧
    Runs K0 [] (h27bp ++ [.release 4, .release 6, .release 7, .write 3 [7]]) :=
  ⟨runsTo (by decide), .reject (by decide), runsTo (by decide)⟩

/-- First run of H27c (§72, §60): frame 1 with the local 0; 1, `Modify` on it; 2, `Modify` derived
from 1. -/
def h27c1o : List Op := [.enter [] [lf], .derive 0 [0] .modify, .derive 1 [0] .modify]
/-- State reached by `h27c1o` (§57). -/
def h27c1 : LState := final K0 [] h27c1o
/-- Second run of H27c (§72, §71, §60): frame 1 with allocator 0 and `v` (1); storage 2 owned by
`v`; 3, `Modify` on `v`; 4, `Modify` on the storage. -/
def h27c2o : List Op := [.enter [] [lf, lf], .write 0 [0], .write 1 [1], .alloc 0 1 [lf],
  .derive 1 [1] .modify, .derive 2 [2] .modify]
/-- State reached by `h27c2o` (§57). -/
def h27c2 : LState := final K0 [] h27c2o

/-- **H27c** (material §1 F, class N3). Passing `&mut x` and a derivative of `x`; passing `&mut v`
and an access to the storage owned by `v`. Expected (material): `reject` at `enterFrame`.
Obtained: both calls `reject` (§72.3: the direct origin of a `Modify` parameter stays exercisable
through the other parameter). Twins, each call with the first parameter alone: `ok`. -/
theorem H27c : RunsTo K0 [] h27c1o h27c1 ∧ EnterStep [1, 2] [] h27c1.kern .reject ∧
    Runs K0 [] (h27c1o ++ [.enter [1] []]) ∧
    RunsTo K0 [] h27c2o h27c2 ∧ EnterStep [3, 4] [] h27c2.kern .reject ∧
    Runs K0 [] (h27c2o ++ [.enter [3] []]) :=
  ⟨runsTo (by decide), .reject (by decide), runsTo (by decide), runsTo (by decide),
    .reject (by decide), runsTo (by decide)⟩

/-- **H28** (material §1 F, class N3). `Observe` and `Modify` parameters on two disjoint parts of
one structure. Expected (material): `ok`. Obtained: `ok` (§43, leaf-local effect; §72). -/
theorem H28 : Runs K0 [] [.enter [] S2, .derive 0 [1] .observe, .derive 0 [2] .modify,
    .enter [1, 2] []] :=
  runsTo (by decide)

/-- Prefix of H29 (§72, §60, §65): frame 1 with `V` (0) and `X` (1), written; 2, `Observe` on
`X`, stored into `V`. -/
def h29p : List Op := [.enter [] [lf, lf], .write 0 [0], .write 1 [1], .derive 1 [1] .observe,
  .store 2 0]
/-- Run of H29 (§72): the callee receives 3, `Observe` on `V`. -/
def h29o : List Op := h29p ++ [.derive 0 [0] .observe, .enter [3] []]
/-- State reached by `h29o` (§57). -/
def h29 : LState := final K0 [] h29o

/-- **H29** (material §1 F, class N3). The callee, with `Observe` only, releases an authority held
by a caller value. Expected (material): `reject`. Obtained: `reject` (§62.2: no exercisable
`Modify` on the holding place). Twin with a `Modify` parameter: `ok`. -/
theorem H29 : RunsTo K0 [] h29o h29 ∧ ReleaseStep 2 h29.kern .reject ∧
    Runs K0 [] (h29p ++ [.derive 0 [0] .modify, .enter [3] [], .release 2]) :=
  ⟨runsTo (by decide), .reject (by decide), runsTo (by decide)⟩

/-- **H29b** (material §1 F, class Lib). The arena value passed `Observe`, and a `Modify`
parameter derived from a block held by a caller value: storage 3 (leaf 4) owned by the arena
value 0, block 4 issued to 2, parameters 6 (`Observe` on 0) and 5 (`Modify` from the block).
Expected (material): `ok`. Obtained: `ok` (§72.3: the block, held by 2, is exercisable in no mode
by the callee). -/
theorem H29b : Runs K0 [] [.enter [] [lf, lf, lf], .write 1 [1], .alloc 1 0 [lf, pt 3],
    .write 0 [0], .newArena 3 3, .issue 0 [4] 2, .derive 4 [4] .modify, .derive 0 [0] .observe,
    .enter [6, 5] []] :=
  runsTo (by decide)

/-! ## H. Abusive rejections (the model must accept) -/

/-- **H35** (material §1 H, class N3). SoA: two columns written after `split`. Expected
(material): `ok`. Obtained: `ok` (§61, §85). -/
theorem H35 : Runs K0 [] [.enter [] S2, .split 0 [[1], [2]], .write 1 [1], .write 2 [2]] :=
  runsTo (by decide)

/-- **H36** (material §1 H, class N3). A local ended by `endUse`, then written again and read.
Expected (material): `ok`. Obtained: `ok` (§69 effect: the place remains usable and may be
reinitialized; §67, §66). -/
theorem H36 : Runs K0 [] [.enter [] [lf], .write 0 [0], .endUse 0, .write 0 [0], .read 0 [0]] :=
  runsTo (by decide)

/-- **H37** (material §1 H, class Lib). An arena created by the callee on a storage allocated for
its value (local 2, storage 3 with leaf 4, `internal` its root 5), and returned to the caller's
result 0, then `exitFrame`. Expected (material): `ok`; negative twin `H21b`. Obtained: `ok` at
every step (§71, §76.1, §63, §73). -/
theorem H37 : Runs K0 [] [.enter [] [lf, lf], .write 1 [1], .derive 0 [0] .modify,
    .derive 1 [1] .modify, .enter [2, 3] [lf], .alloc 1 2 [lf, pt 3], .write 4 [2],
    .newArena 3 5, .transfer 2 0, .exit] :=
  runsTo (by decide)

/-- **H45** (material §1 H, class Lib). Two arena nodes `A` (5: data 6, link 7) and `B` (8: data
9, link 10) in the storage 4, issued to 2 and 3; `A.link` holds a view (7) on `B.data`, `B.link`
holds a view (8) on `A.data`; teardown (`release` of both views, `endUse` of both node values),
then `reset`. Expected (material): `ok` throughout. Obtained: `ok` at every step (§65, §62, §69,
§78, §88). -/
theorem H45 : Runs K0 [] [.enter [] [lf, lf, lf, lf], .write 1 [1],
    .alloc 1 0 [lf, pt 4, pt 5, pt 5, pt 4, pt 8, pt 8], .write 0 [0], .newArena 4 4,
    .issue 0 [6, 7] 2, .issue 0 [9, 10] 3, .derive 6 [9] .modify, .store 7 7,
    .derive 5 [6] .modify, .store 8 10, .release 7, .release 8, .endUse 2, .endUse 3,
    .reset 0] :=
  runsTo (by decide)

/-- **H46** (material §1 H, class N3). A view on a local array (0: 1, 2) stored into a field (4)
of a local structure (3), read, then released. Expected (material): `ok`. Obtained: `ok` (§65,
§66, §62). -/
theorem H46 : Runs K0 [] [.enter [] [lf, pt 0, pt 0, lf, pt 3], .write 0 [1, 2],
    .derive 0 [1, 2] .observe, .store 2 4, .read 2 [1], .release 2] :=
  runsTo (by decide)

/-- **H47** (material §1 H, class N3). Field-by-field transfer of a partially initialized
aggregate: the written field 1 of structure 0 is transferred into the field 4 of structure 3.
Expected (material): `ok`. Obtained: `ok` (§63 last paragraph). -/
theorem H47 : Runs K0 [] [.enter [] [lf, pt 0, pt 0, lf, pt 3, pt 3], .write 0 [1],
    .transfer 1 4] :=
  runsTo (by decide)

/-! ## I. Progress -/

/-- Common arena of section I (§71, §76, §77): frame 1 with arena value 0, allocator 1, values 2
and 3; storage 4 (nodes 5, 6) owned by 0, `internal` 4; block 5 on `[5]` to 2 and block 6 on
`[6]` to 3. -/
def fao : List Op := [.enter [] [lf, lf, lf, lf], .write 1 [1], .alloc 1 0 [lf, pt 4, pt 4],
  .write 0 [0], .newArena 4 4, .issue 0 [5] 2, .issue 0 [6] 3]
/-- Run of H48 (§60, §65): 7, `Modify` on `B` (6) from its block, stored into `A` (5); 8,
`Modify` on `A` from its block. -/
def h48o : List Op := fao ++ [.derive 6 [6] .modify, .store 7 5, .derive 5 [5] .modify]
/-- State reached by `h48o` (§57). -/
def h48 : LState := final K0 [] h48o

/-- **H48** (material §1 I, class N3). A cycle of two authorities on whole nodes by direct
`store`. Expected (material): `reject`. Obtained: `reject`: in the resulting state the target 6
would no longer be under exercisable `Modify` (§65.5). Twin without the first `store`: `ok`. -/
theorem H48 : RunsTo K0 [] h48o h48 ∧ StoreStep 8 6 h48.kern .reject ∧
    Runs K0 [] (fao ++ [.derive 6 [6] .modify, .derive 5 [5] .modify, .store 8 6]) :=
  ⟨runsTo (by decide), .reject (by decide), runsTo (by decide)⟩

/-- Run of H49 (§60, §65, §62): the cycle of H48 closed through the helper 9, `Modify` on 6 from
7, then the helper released. -/
def h49o : List Op := h48o ++ [.derive 7 [6] .modify, .store 8 6, .release 9]
/-- State reached by `h49o` (§57). -/
def h49 : LState := final K0 [] h49o

/-- **H49** (material §1 I, class N3; regression test). The same cycle, closed through a helper
authority, then `release` of the helper. Historical expected verdict (material): to arbitrate;
under spec v0 the obtained verdict was `ok` with a residual blocking: after the `endUse` of the
block values 2 and 3, `ok`, the authorities 7 and 8 stayed active and exercisable in no mode and
`reset` was `reject` (§78.2), a **MISMATCH** in form; the arbitration of the corpus owner keeps H49
as a regression test with that obtained verdict as its baseline and its residual blocking
documented. New expected verdict (spec v0.1, derived from its text, not from the obtained outcome):
the cycle is reached (`ok` at every step: §60, §65, §62), the authorities 7 and 8 are exercisable
in no mode, `reset` is `reject` (§78.2: the blocks 5 and 6 are active and cover the leaves 5 and
6), as in that baseline; the `endUse` of the block values 2 and 3 is `reject`, against the `ok` of
that baseline, decided by the v0.1 amendment of §69.2 (last sentence: the block 5, made inactive by
the `endUse` of 2, keeps its active descendant 8, held by the leaf 6; the block 6 keeps 7, held by
the leaf 5), which overrides the baseline for these two steps. This residual blocking
is allowed: `NoLock` is not adopted (§65 last paragraph, §27) and indirect blocking compatible with
safety may remain (§88). Obtained: the same. Twin of the two `endUse` rejections: the same sequence
without the cycle (the six steps after `fao`), then both `endUse` and `reset`, `ok`. The `reset`
`reject` in `h49` persists in that twin (on `fao` the blocks 5 and 6 are still held by the values 2
and 3, §78.2); by arbitration it is exempt from a positive twin. -/
theorem H49 : RunsTo K0 [] h49o h49 ∧ ¬ h49.kern.ExercisableAt 7 .observe ∧
    ¬ h49.kern.ExercisableAt 8 .observe ∧ ResetD 0 h49 .reject ∧
    EndUseStep K0 2 h49.kern .reject ∧ ¬ EndUseKeptDesc h49.kern 2 ∧
    EndUseStep K0 3 h49.kern .reject ∧ ¬ EndUseKeptDesc h49.kern 3 ∧
    Runs K0 [] (fao ++ [.endUse 2, .endUse 3, .reset 0]) :=
  ⟨runsTo (by decide), by decide, by decide, rejects (k := K0) (o := .reset 0) (by decide),
    .reject (by decide), by decide, .reject (by decide), by decide, runsTo (by decide)⟩

/-- Run of H50, `transfer` part (§72, §60, §65): structure 0 (field 1), structure 2 (field 3),
local 4; 3, `Modify` on the field 3, stored into the field 1. -/
def h50to : List Op := [.enter [] [lf, pt 0, lf, pt 2, lf], .derive 1 [3] .modify, .store 3 1]
/-- State reached by `h50to` (§57). -/
def h50t : LState := final K0 [] h50to

/-- **H50**, `transfer` part (material §1 I, class N3). An authority transferred into the place
it covers: structure 0 is transferred into structure 2 while its field 1 holds 3, which covers
the field 3 = `corr(1)`. Historical expected verdict (material): to arbitrate; under spec v0 a
**MISMATCH** in form (obtained `reject`). New expected verdict (spec v0.1, by arbitration the
obtained one): `reject`, decided by §63.8 (local self-blocking prevention, §88). Obtained: `reject`
by §63.8 alone (§63.1–§63.7 and §63.9 hold). Twin, the stored authority covering the local 4
instead: `ok`. -/
theorem H50_transfer : RunsTo K0 [] h50to h50t ∧ TransferStep K0 0 2 h50t.kern .reject ∧
    TransferPre637 K0 h50t.kern 0 2 ∧ (transferEff h50t.kern 0 2).Usable 2 ∧
    ¬ NoLocalSelfLock h50t.kern 0 2 ∧
    Runs K0 [] [.enter [] [lf, pt 0, lf, pt 2, lf], .derive 2 [4] .modify, .store 3 1,
      .transfer 0 2] :=
  ⟨runsTo (by decide), .reject (by decide), by decide, by decide, by decide, runsTo (by decide)⟩

/-- State after the first five steps of `fao`, the arena created and nothing issued (§57). -/
def h50i : LState := final K0 [] (fao.take 5)

/-- **H50**, `issue` part (material §1 I, class Lib). A block issued into a leaf of its own region
(`issue(0, [5], 5)`, the region available). Historical expected verdict (material): to arbitrate;
under spec v0 a **MISMATCH** in form (obtained `reject`). New expected verdict (spec v0.1, by
arbitration the obtained one): `reject`, decided by §77.2 (local self-blocking prevention, §88).
Obtained: `reject`, static, by local self-blocking prevention alone: the other static
preconditions hold and the destination is in the region. Twin, the same issue into the value 2:
`ok`. -/
theorem H50_issue : RunsTo K0 [] (fao.take 5) h50i ∧ IssueD K0 0 [5] 5 h50i .reject ∧
    OptP (h50i.arenas[0]?) (fun E => IssueStaticBut h50i.kern E [5] 5 ∧
      ¬ IssueStatic h50i.kern E [5] 5) False ∧
    Runs K0 [] (fao.take 5 ++ [.issue 0 [5] 2]) :=
  ⟨runsTo (by decide), rejects (o := .issue 0 [5] 5) (by decide), by decide, runsTo (by decide)⟩

/-- Prefix of H51 (§72, §71): frame 1 with allocator 0, `v` (1) and `u` (2), written; storage 3
(element 4) owned by `v`, its root authority 3 held by `v`. -/
def h51p : List Op := [.enter [] [lf, lf, lf], .write 0 [0], .write 1 [1], .write 2 [2],
  .alloc 0 1 [lf, pt 3]]
/-- Run of H51, direct form (§60): 4, `Observe` on `v`. -/
def h51no : List Op := h51p ++ [.derive 1 [1] .observe]
/-- State reached by `h51no` (§57). -/
def h51n : LState := final K0 [] h51no
/-- Run of H51 through a helper (§60, §65, §62): 4, `Modify` on the element, held by the frame;
5, `Observe` on `v`, stored into the element; the helper released. -/
def h51o : List Op := h51p ++ [.derive 3 [4] .modify, .derive 1 [1] .observe, .store 5 4,
  .release 4]
/-- State reached by `h51o` (§57). -/
def h51 : LState := final K0 [] h51o

/-- **H51** (material §1 I, class N3). An element of a storage owned by `v` holds a view on `v`.
Historical expected verdict (material): to arbitrate; under spec v0 a **MISMATCH** in form
(obtained `reject` / `ok`). New expected verdicts (spec v0.1, by arbitration the obtained ones),
decided by §65.2, §67.1, §62.2, §69.1 and §88, clauses v0.1 leaves unchanged: the direct `store`
is `reject`: the view takes away the frame's `Modify` on `v`, hence on the storage it owns (§43
case 4, §65.2, §65.5); twin with the view on another value `u`: `ok`. Through a helper on the
element, then its `release`, the configuration is reached (`ok`); then `v` can be neither written,
nor relieved of the view, nor ended (`reject`, §67.1, §62.2, §69.1), while the view stays
exercisable in `Observe`; the exit of the frame is `ok` (§88: residual blocking). Obtained: the
same. Twins of these three rejections: the same sequence without the view on `v` (its `derive`
and its `store`), then the write of `v` through its root, `ok`, or its `endUse`, `ok`; the same
sequence without the `store` of the view, then its `release`, `ok`. With only the `store` dropped,
the write and the `endUse` stay `reject` for a different cause: the view, then held by the frame,
is active on `v` (§43 case 4, §67.1, §69.1) and releasable. -/
theorem H51 : RunsTo K0 [] h51no h51n ∧ StoreStep 4 4 h51n.kern .reject ∧
    Runs K0 [] (h51p ++ [.derive 2 [2] .observe, .store 4 4]) ∧
    RunsTo K0 [] h51o h51 ∧ (∀ a, Write3Step a [1] h51.kern .reject) ∧
    ReleaseStep 5 h51.kern .reject ∧ EndUseStep K0 1 h51.kern .reject ∧
    h51.kern.ExercisableAt 5 .observe ∧ Runs K0 [] (h51o ++ [.exit]) ∧
    Runs K0 [] (h51p ++ [.derive 3 [4] .modify, .release 4, .write 1 [1]]) ∧
    Runs K0 [] (h51p ++ [.derive 3 [4] .modify, .derive 1 [1] .observe, .release 4, .release 5]) ∧
    Runs K0 [] (h51p ++ [.derive 3 [4] .modify, .release 4, .endUse 1]) :=
  ⟨runsTo (by decide), .reject (by decide), runsTo (by decide), runsTo (by decide),
    write_rejected (by decide), .reject (by decide), .reject (by decide), by decide,
    runsTo (by decide), runsTo (by decide), runsTo (by decide), runsTo (by decide)⟩

/-! ## New cases fixed by spec clauses -/

/-- Prefix of `S63_8` (§72): structure 0 with the part 1, itself with the leaf 2; structure 3
with the part 4, itself with the leaf 5; local 6. -/
def s638p : List Op := [.enter [] [lf, pt 0, pt 1, lf, pt 3, pt 4, lf]]
/-- Run of `S63_8` (§60, §65): 3, `Modify` on the leaf 5, stored into the leaf 2. -/
def s638o : List Op := s638p ++ [.derive 1 [5] .modify, .store 3 2]
/-- State reached by `s638o` (§57). -/
def s638 : LState := final K0 [] s638o

/-- **S63.8** (new case, §63.8; class N3). Transfer self-blocking through a nested part: structure
0 is transferred into structure 3 while its leaf 2 holds 3, which covers the leaf 5 =
`corr(2)`. Expected (§63.8, §88): `reject`. Obtained: `reject` by local self-blocking prevention
alone (§63.1–§63.7 and §63.9 hold). Twin, the stored authority covering the local 6 instead:
`ok`. -/
theorem S63_8 : RunsTo K0 [] s638o s638 ∧ corr s638.kern.P 0 3 2 = some 5 ∧
    TransferStep K0 0 3 s638.kern .reject ∧ TransferPre637 K0 s638.kern 0 3 ∧
    (transferEff s638.kern 0 3).Usable 3 ∧ ¬ NoLocalSelfLock s638.kern 0 3 ∧
    Runs K0 [] (s638p ++ [.derive 2 [6] .modify, .store 3 2, .transfer 0 3]) :=
  ⟨runsTo (by decide), by decide, .reject (by decide), by decide, by decide, by decide,
    runsTo (by decide)⟩

/-- State after the first six steps of `fao`: block 5 on `[5]` issued to 2, so the leaf 5 is not
available (§46, §77). -/
def s772 : LState := final K0 [] (fao.take 6)

/-- **S77.2** (new case, §77.2; class Lib). Issue into a leaf of the region when the region is
unavailable. Expected (§77.2: the condition is static and checked before an availability `fail`):
`reject`. Obtained: `reject` (`issue(0, [5], 5)`: the other static preconditions hold, the
destination is in the region and the region is unavailable). Twin without the faulty element,
the destination 3 outside the region: `fail` (§77.4), as prescribed for an unavailable region;
with an available region (`issue(0, [6], 3)`): `ok`. -/
theorem S77_2 : RunsTo K0 [] (fao.take 6) s772 ∧ IssueD K0 0 [5] 5 s772 .reject ∧
    OptP (s772.arenas[0]?) (fun E => IssueStaticBut s772.kern E [5] 5 ∧
      ¬ IssueStatic s772.kern E [5] 5 ∧ ¬ Avail E [5]) False ∧
    IssueD K0 0 [5] 3 s772 .fail ∧ Runs K0 [] fao :=
  ⟨runsTo (by decide), rejects (o := .issue 0 [5] 5) (by decide), by decide,
    fails (o := .issue 0 [5] 3) (by decide), runsTo (by decide)⟩

/-- Run of `S77_6` (§60, §65): 5, `Modify` on the value 2 from its root, stored into the storage
leaf 5; the frame's `Modify` on 2 now goes through 5, held by the leaf 5. -/
def s776o : List Op := fao.take 5 ++ [.derive 2 [2] .modify, .store 5 5]
/-- State reached by `s776o` (§57). -/
def s776 : LState := final K0 [] s776o

/-- **S77.6** (new case, §77.6; class Lib). Issue into a destination that would no longer be
exercisable in `Modify`: `issue(0, [5], 2)`. Expected (§77.6, §65.5, §88): `reject`. Obtained:
`reject`; the static checks, availability and the effective right of `internal` hold, but in the
resulting state the block on the leaf 5 makes the frame's only path to 2 (through 5, held by the
leaf 5) circular, so 2 is not under exercisable `Modify`. Twin without the `derive` and `store` of
5: `ok`. -/
theorem S77_6 : RunsTo K0 [] s776o s776 ∧ IssueD K0 0 [5] 2 s776 .reject ∧
    OptP (s776.arenas[0]?) (fun E => IssueStatic s776.kern E [5] 2 ∧ Avail E [5] ∧
      IssueRight s776.kern E [5] ∧ ¬ HasRight (issueKEff s776.kern E [5] 2) .modify 2) False ∧
    Runs K0 [] (fao.take 6) :=
  ⟨runsTo (by decide), rejects (o := .issue 0 [5] 2) (by decide), by decide, runsTo (by decide)⟩

/-- Run of `S56` (§60, §65): from the arena of `fao` (live, `internal` 4), 5, `Modify` on the
whole storage from `internal`, stored into the value 2. -/
def s56o : List Op := fao.take 5 ++ [.derive 4 [5, 6] .modify, .store 5 2]
/-- State reached by `s56o` (§57). -/
def s56 : LState := final K0 [] s56o

/-- **S56** (new case, §56, §76.4; class Lib). A second arena on the `internal` of a live arena.
Expected (§56, §76.4): `reject`. Obtained: `reject`: every other precondition of `newArena`
holds, the identity 4 is in the arena registry of live administrations. Twin, a distinct
`internal` (5) over the same storage: `ok` (§56: distinct identities are not forbidden merely
because their footprints overlap). The cross-registry cases (a pool and an arena on one
`internal`) belong to the handle-pool wave. -/
theorem S56 : RunsTo K0 [] s56o s56 ∧ NewArenaStep [] 4 4 s56 .reject ∧
    NewArenaBase s56.kern 4 4 ∧ ¬ Guard56 [liveInternals s56.kern s56.arenas] 4 ∧
    Runs K0 [] (s56o ++ [.newArena 4 5]) :=
  ⟨runsTo (by decide), rejects (k := K0) (o := .newArena 4 4) (by decide), by decide, by decide,
    runsTo (by decide)⟩

/-! ## Usage scenario W3 (material §5b) -/

/-- Run of W3 (§71, §76, §77, §60, §65): frame 1 with arena value 0, allocator 1 and structure 2
(fields 3 to 8); storage 9 (leaves 10, 11, 12) owned by 0, `internal` 3; blocks 4, 5, 6 issued
into the fields 3, 4, 5; views 7, 8, 9, `Observe` on the blocks, stored into the fields 6, 7, 8. -/
def w3o : List Op := [.enter [] [lf, lf, lf, pt 2, pt 2, pt 2, pt 2, pt 2, pt 2], .write 1 [1],
  .alloc 1 0 [lf, pt 9, pt 9, pt 9], .write 0 [0], .newArena 9 3, .issue 0 [10] 3,
  .issue 0 [11] 4, .issue 0 [12] 5, .derive 4 [10] .observe, .derive 5 [11] .observe,
  .derive 6 [12] .observe, .store 7 6, .store 8 7, .store 9 8]
/-- State reached by `w3o` (§57). -/
def w3 : LState := final K0 [] w3o

/-- **W3** (material §5b, frame arena; class Lib, not given by the material). `alloc`,
`newArena`, three `issue`, three views stored into a local structure; `reset` while the views
live; `endUse` of the structure; `reset`; reissue. The material does not say which values hold the
blocks; by arbitration the case issues them into fields of the structure (the literal reading,
blocks issued to separate locals, kept `reset` `reject` after the `endUse` of the structure: a case
defect under spec v0). Expected (material): `reset` during the views `reject`; after `endUse` of
the structure `ok`; reissue `ok`. Obtained: the same (§78.2; §69 effect: the `endUse` of the
structure ends the blocks and the views it holds; §77). Twin of the `reject`: the `endUse` of the
structure, then `reset`, `ok`. -/
theorem W3 : RunsTo K0 [] w3o w3 ∧ ResetD 0 w3 .reject ∧
    Runs K0 [] (w3o ++ [.endUse 2, .reset 0, .issue 0 [10] 3]) :=
  ⟨runsTo (by decide), rejects (k := K0) (o := .reset 0) (by decide), runsTo (by decide)⟩

end Ern.Corpus.MM3H
