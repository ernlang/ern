import Ern.HandlePool

/-!
# MM3-H: adversarial corpus of the access discipline (jalon 3, step 2)

The cases of the jalon-3 material (`ERN_Jalon3_materiel.md` v2), §1 sections A to I, and the usage
scenarios W1 to W3 of §5b. Each case is a run from the initial state `S3.init statics`
(MM-03.3.9) by `ok` steps of the extended machine (`Ern.HandlePool.PReach`), checked by `prun`;
the verdict of the step under test is stated with the relation of its operation (MM-03.3 §3–6,
material §4) and decided on the reached state. The expected verdict comes from the source named in
the material, never from the module (material §0, rule 1). Every rejection has a twin: the same
run without the faulty element, where the same step is accepted (rule 2). The class (rule 5) is in
each docstring; the jalon-3 report, (a), gathers expected and obtained verdicts. Section J is not
encoded (report, (a)); `J_H42_expansion` keeps the one straight-line expansion that the kernel can
run.

Local shapes are lists of (parent, owning local, kind), as for `enterFrame` (MM-03.3 §4, O6);
`lf` is a root leaf.
-/

namespace Ern.MM03.Horrors

open Ern.MM03 Ern.HandlePool

section Run
variable (k : K) [∀ r r', Decidable (k.DeclaredDisjoint r r')] [DecidablePred k.SharedMutable]
  [DecidablePred k.Pinned] [DecidablePred k.ExternalDone] [DecidablePred k.Deallocable]
  [∀ p a, Decidable (k.FreeCompat p a)] [∀ p ls s, Decidable (k.Satisfiable p ls s)]

/-- The state reached by the operations `os` from `S3.init statics`, or that initial state when a
step is not `ok` (then `run_reach` cannot be used). -/
def run (statics : Statics) (os : List Op) : PS :=
  (prun k (PS.init statics) os).getD (PS.init statics)

end Run

section RunSound
variable {k : K} [∀ r r', Decidable (k.DeclaredDisjoint r r')] [DecidablePred k.SharedMutable]
  [DecidablePred k.Pinned] [DecidablePred k.ExternalDone] [DecidablePred k.Deallocable]
  [∀ p a, Decidable (k.FreeCompat p a)] [∀ p ls s, Decidable (k.Satisfiable p ls s)]

/-- A run whose steps are all `ok` reaches its final state (material §0, rule 3). -/
theorem run_reach {statics : Statics} {os : List Op} (hsh : ShapeOK 0 (statics.map (·.1)))
    (h : (prun k (PS.init statics) os).isSome = true) : PReach k statics (run k statics os) :=
  prun_init hsh (some_getD h)

end RunSound

/-- A read rejected for every authority of the state is rejected for every authority (MM-03.3 §5,
`canRead3`: the reading authority exists). -/
theorem read_rejected {s : S3} {ls : List Nat} (h : ∀ a ∈ List.range s.A.length, ¬ canRead3 s a ls)
    (a : Nat) : Read3Step a ls s .reject :=
  .reject fun hc => by
    by_cases ha : a < s.A.length
    · exact h a (List.mem_range.2 ha) hc
    · cases hc.1 with
      | base hy => exact ha (lt_of_getElem? hy)
      | held hy => exact ha (lt_of_getElem? hy)

/-- A write rejected for every authority of the state is rejected for every authority (MM-03.3 §5,
`canWrite3`). -/
theorem write_rejected {s : S3} {ls : List Nat} (h : ∀ a ∈ List.range s.A.length, ¬ canWrite3 s a ls)
    (a : Nat) : Write3Step a ls s .reject :=
  .reject fun hc => by
    by_cases ha : a < s.A.length
    · exact h a (List.mem_range.2 ha) hc
    · cases hc.1 with
      | base hy => exact ha (lt_of_getElem? hy)
      | held hy => exact ha (lt_of_getElem? hy)

/-- A root leaf of a shape. -/
abbrev lf : Option Nat × Option Nat × Nat := (none, none, 0)

/-- A structure 0 with the parts 1 and 2. -/
def S2 : List (Option Nat × Option Nat × Nat) := [lf, (some 0, none, 0), (some 0, none, 0)]

/-! ## A. Exclusivity and indirect aliasing -/

/-- H01, structure and first parameter: frame 1, structure 0 with the parts 1 and 2, root 0; the
frame derives 1, `Modify` on 0. -/
def h01 : PS := run K0 [] [.enter [] S2, .derive 0 0 .modify]
/-- Twin of H01: the same frame without the first parameter. -/
def h01t : PS := run K0 [] [.enter [] S2]

/-- **H01** (A; I1, A3, G1; class N3). Two parameters derived from the same local, `Modify` on the
whole then `Observe` on a part: the second `derive` from the root is rejected, the root having no
effective mode on the part (MM-03.3.5; O1.3). Expected: reject; obtained: reject. Twin without the
first parameter: the same `derive` is accepted, and the call with the first parameter alone is
accepted. -/
theorem H01 : PReach K0 [] h01 ∧ DeriveStep 0 1 .observe h01.s .reject ∧ PReach K0 [] h01t ∧
    DeriveStep 0 1 .observe h01t.s (.ok (deriveEff h01t.s 0 1 .observe)) ∧
    EnterStep [1] [] h01.s (.ok (enterEff h01.s [1] [])) :=
  ⟨run_reach (by decide) (by decide), .reject (by decide), run_reach (by decide) (by decide),
    .ok (by decide), .ok (by decide)⟩

/-- H01, reading where the `Observe` parameter is derived from the `Modify` one (report, (b)): the
only construction that reaches `enterFrame` with both parameters. Expected (H01 row): reject;
obtained: the call is accepted. G1 constrains the direct origin of a `Modify` parameter only (O6.3),
and the two authorities are related by derivation (I1). -/
theorem H01_reborrow : PReach K0 [] (run K0 [] [.enter [] S2, .derive 0 0 .modify,
    .derive 1 1 .observe, .enter [1, 2] []]) :=
  run_reach (by decide) (by decide)

/-- H02, frame 1 with the structure of H01 and an `Observe` authority 1 on the whole. -/
def h02 : PS := run K0 [] [.enter [] S2, .derive 0 0 .observe]

/-- **H02** (A; I1, effective mode; N3). `Observe` on the whole, then `Modify` on a part: rejected,
the effective mode of the root on the part being `Observe` (MM-03.3.5). Expected: reject; obtained:
reject. Twin without the observation: accepted. -/
theorem H02 : PReach K0 [] h02 ∧ DeriveStep 0 1 .modify h02.s .reject ∧
    DeriveStep 0 1 .modify h01t.s (.ok (deriveEff h01t.s 0 1 .modify)) :=
  ⟨run_reach (by decide) (by decide), .reject (by decide), .ok (by decide)⟩

/-- H03: frame 1, structure X (0) with the parts `p` (1) and 2, leaf Y (3); the frame derives 2,
`Modify` on `p`, and stores it into Y. -/
def h03o : List Op := [.enter [] (S2 ++ [lf]), .derive 0 1 .modify, .store 2 3]
def h03 : PS := run K0 [] h03o
def h03t : PS := run K0 [] [.enter [] (S2 ++ [lf])]

/-- **H03** (A; I1, F4; N3). The value of Y holds a `Modify` derived on the part `p` of X; a write
of `p` through the root of X is rejected (no effective mode, MM-03.3.5; O10). Expected: reject;
obtained: reject. Twin without the stored authority: accepted. The `store` is not what makes the
write fail: after the `derive` alone, the write is already rejected (I1, effective mode), so the case
does not exercise F4 itself. -/
theorem H03 : PReach K0 [] h03 ∧ Write3Step 0 [1] h03.s .reject ∧
    Write3Step 0 [1] h03t.s (.ok (write3Eff h03t.s [1])) :=
  ⟨run_reach (by decide) (by decide), .reject (by decide), .ok (by decide)⟩

/-- H04: frame 1, array 0 with the elements 1 and 2, and an authority 1, `Modify` on element 1. -/
def h04 : PS := run K0 [] [.enter [] S2, .derive 0 1 .modify]

/-- **H04** (A; O2, I1; N3). Swap of two elements: by `split` of the array, two writes, all `ok`;
by two `derive Modify` of the same element, the second is rejected. Expected: `ok` / reject;
obtained: `ok` / reject. Twin of the rejection: `derive Modify` of the other element, accepted. -/
theorem H04 : PReach K0 [] (run K0 [] [.enter [] S2, .split 0 [[1], [2]], .write 1 [1],
      .write 2 [2]]) ∧
    PReach K0 [] h04 ∧ DeriveStep 0 1 .modify h04.s .reject ∧
    DeriveStep 0 2 .modify h04.s (.ok (deriveEff h04.s 0 2 .modify)) :=
  ⟨run_reach (by decide) (by decide), run_reach (by decide) (by decide), .reject (by decide),
    .ok (by decide)⟩

/-- H05: frame 1, structure `x` (0) with the fields `f` (1) and 2, leaf `tmp` (3); `x` written. -/
def h05 : PS := run K0 [] [.enter [] (S2 ++ [lf]), .write 0 [1, 2]]

/-- **H05** (A; F5, J1; N3; covered pass 6). `transfer(x, x.f)` is rejected (destination `Init`,
footprints overlapping). Expected: reject; obtained: reject. Twin: `transfer(x.f, tmp)` then
`transfer(tmp, x.f)`, the destination `Moved` and of the same shape: accepted. -/
theorem H05 : PReach K0 [] h05 ∧ TransferStep K0 0 1 h05.s .reject ∧
    PReach K0 [] (run K0 [] [.enter [] (S2 ++ [lf]), .write 0 [1, 2], .transfer 1 3,
      .transfer 3 1]) :=
  ⟨run_reach (by decide) (by decide), .reject (by decide), run_reach (by decide) (by decide)⟩

/-- **H06** (A; O3, effective mode; N3). `derive Modify`, `derive Observe` below it, `release` of
both, then a write through the root: every step `ok`. Expected: `ok`; obtained: `ok`. -/
theorem H06 : PReach K0 [] (run K0 [] [.enter [] [lf], .derive 0 0 .modify, .derive 1 0 .observe,
    .release 2, .release 1, .write 0 [0]]) :=
  run_reach (by decide) (by decide)

/-! ## B. Lifetime and escape -/

/-- One static leaf, `Uninit`. -/
def stS : Statics := [((none, none, 0), false)]

/-- H07: the base frame derives 1, `Modify` on the static 0, and calls frame 1 with it; frame 1 has
the local `L` (1), written, derives 3, `Observe` on `L`, and calls frame 2 with `[1, 3]`; frame 2
writes its local `W` (2). -/
def h07p : List Op := [.derive 0 0 .modify, .enter [1] [lf], .write 2 [1], .derive 2 1 .observe,
  .enter [1, 3] [lf], .write 4 [2]]
/-- H07: `W` depends on the authority 3, anchored on the caller's local `L`. -/
def h07 : PS := run K0 stS (h07p ++ [.depend 2 3])
def h07t : PS := run K0 stS h07p

/-- **H07** (B; C1, G4; N3). The callee stores into the static, through its `Modify` parameter on
it, a value anchored on a local of the caller: the `transfer` is rejected, the effective anchor
being of frame 1, not an ancestor of the frame 0 of the static (C1, `EffAnchorOK`). Expected: reject
at the `transfer`; obtained: reject. Twin without the anchor: accepted. The stored value is a local
of the callee, which the material leaves open. -/
theorem H07 : PReach K0 stS h07 ∧ TransferStep K0 2 0 h07.s .reject ∧ PReach K0 stS h07t ∧
    TransferStep K0 2 0 h07t.s (.ok (transferEff h07t.s 2 0)) :=
  ⟨run_reach (by decide) (by decide), .reject (by decide), run_reach (by decide) (by decide),
    .ok (by decide)⟩

/-- H08/H09: frame 1 with `X` (0), written, and the result `R` (1); it derives 2, `Modify` on `X`,
and 3, `Modify` on `R`, and calls frame 2 with them; frame 2 has `W` (2) and `Lc` (3). -/
def h89 : List Op := [.enter [] [lf, lf], .write 0 [0], .derive 0 0 .modify, .derive 1 1 .modify,
  .enter [2, 3] [lf, lf]]

/-- **H08** (B; C1; N3; covered pass 2). A return anchored on a derivation (7) of a derivation (6)
of the parameter 2: the `transfer` of `W` into `R` and the exit are accepted. Expected: `ok`;
obtained: `ok`. -/
theorem H08 : PReach K0 [] (run K0 [] (h89 ++ [.derive 2 0 .observe, .derive 6 0 .observe,
    .write 4 [2], .depend 2 7, .transfer 2 1, .exit])) :=
  run_reach (by decide) (by decide)

/-- H09: `W` depends on 7, derived from 6, derived from the root of the callee's local `Lc`. -/
def h09 : PS := run K0 [] (h89 ++ [.derive 5 3 .observe, .derive 6 3 .observe, .write 4 [2],
  .depend 2 7])
def h09t : PS := run K0 [] (h89 ++ [.derive 5 3 .observe, .derive 6 3 .observe, .write 4 [2]])

/-- **H09** (B; C1; N3; covered pass 2). A return anchored on a local of the callee through two
derivations: the `transfer` into `R` is rejected (C1). Expected: reject; obtained: reject. Twin
without the anchor: accepted. -/
theorem H09 : PReach K0 [] h09 ∧ TransferStep K0 2 1 h09.s .reject ∧ PReach K0 [] h09t ∧
    TransferStep K0 2 1 h09t.s (.ok (transferEff h09t.s 2 1)) :=
  ⟨run_reach (by decide) (by decide), .reject (by decide), run_reach (by decide) (by decide),
    .ok (by decide)⟩

/-- H10: frame 1, `X` (0), the container `C` (1) with the parts 2 and 3, `T` (4); `A` (3) is
`Observe` on `X`, 4 is derived from `A` and stored into the part 2; `C` depends on `A`. -/
def h10p : List Op := [.enter [] [lf, lf, (some 1, none, 0), (some 1, none, 0), lf], .write 0 [0],
  .derive 0 0 .observe, .derive 3 0 .observe, .store 4 2, .depend 1 3, .write 1 [3]]
/-- H10 after the transfer of the part 2 into `T` and the end of the container. -/
def h10 : PS := run K0 [] (h10p ++ [.transfer 2 4, .endUse 1])

/-- **H10** (B; §1.6, B10; N3). The part holding an access derived from the anchor `A` of its
container is transferred, the container ends, then `release` of `A` is rejected: the transferred
access is an active descendant (O3.2). Expected: reject at the end of `A`; obtained: reject. Twin
without the transfer of the part: the access dies with the container, and `A` is released. -/
theorem H10 : PReach K0 [] h10 ∧ ReleaseStep 3 h10.s .reject ∧
    PReach K0 [] (run K0 [] (h10p ++ [.endUse 1, .release 3])) :=
  ⟨run_reach (by decide) (by decide), .reject (by decide), run_reach (by decide) (by decide)⟩

/-- H11: frame 1, arena value 0, allocator 1, values `v1` (2) and `v2` (3); storage 4 with the
leaves 5 and 6, owned by 0, `internal` 4; blocks 5 on `[5]` to `v1` and 6 on `[6]` to `v2`; `v1`
is transferred into the leaf 6 of the block of `v2`. -/
def h11p : List Op := [.enter [] [lf, lf, lf, lf], .write 1 [1],
  .alloc 1 0 [lf, (some 4, none, 0), (some 4, none, 0)], .write 0 [0], .newArena 4 4,
  .issue 0 0 [5] 2, .issue 0 0 [6] 3, .transfer 2 6]
def h11 : PS := run K0 [] h11p

/-- **H11** (B; usage, A10; Lib). An arena buffer stored into another block of the same arena: the
`transfer` is accepted, `reset` is rejected while a block lives. Expected: `transfer` `ok`, `reset`
reject; obtained: the same. Twin: after the end of both blocks (`endUse` of `v2`, then of the leaf
6), `reset` is accepted. -/
theorem H11 : PReach K0 [] h11 ∧ ResetAtStep K0 0 0 h11.s .reject ∧
    PReach K0 [] (run K0 [] (h11p ++ [.endUse 3, .endUse 6, .reset 0 0])) :=
  ⟨run_reach (by decide) (by decide), .reject (by decide), run_reach (by decide) (by decide)⟩

/-- H12: frame 1, `X` (0) and `W` (2) written, `H` (1); 3, `Observe` on `X`, stored into `H`. -/
def h12p : List Op := [.enter [] [lf, lf, lf], .write 0 [0], .write 2 [2], .derive 0 0 .observe,
  .store 3 1]
def h12 : PS := run K0 [] (h12p ++ [.depend 2 3])

/-- **H12** (B; I3, A6; N3; covered pass 2). `endUse` of the holder `H` of an anchor while `W`
depends on it: rejected (`EndUseAnchorOK`). Expected: reject; obtained: reject. Twin without the
dependent: accepted. -/
theorem H12 : PReach K0 [] h12 ∧ EndUseStep K0 1 h12.s .reject ∧
    PReach K0 [] (run K0 [] (h12p ++ [.endUse 1])) :=
  ⟨run_reach (by decide) (by decide), .reject (by decide), run_reach (by decide) (by decide)⟩

/-! ## C. Ownership and release -/

/-- H13: frame 1, allocator 0, `x` (1) and `z` (2) written; `y` (3) allocated, owned by `x`. -/
def h13 : PS := run K0 [] [.enter [] [lf, lf, lf], .write 0 [0], .write 1 [1], .alloc 0 1 [lf]]

/-- **H13** (C; A5, `Usable`; N3). An ownership cycle: `y`, owned by `x`, receives `x` by
transfer; rejected, the destination would own itself and stop being usable. Expected: reject;
obtained: reject. Twin: the transfer of `x` into `z` is accepted. -/
theorem H13 : PReach K0 [] h13 ∧ TransferStep K0 1 3 h13.s .reject ∧
    ¬ (transferEff h13.s 1 3).Usable 3 ∧ TransferStep K0 1 2 h13.s (.ok (transferEff h13.s 1 2)) :=
  ⟨run_reach (by decide) (by decide), .reject (by decide), by decide, .ok (by decide)⟩

/-- Contracts with the place 2 deallocable by the authority 7. -/
abbrev KF2 : K := KT [] [] [] [2] [(2, 7)]

/-- H14/H15: frame 1, allocator 0 and `x` (1) written; storage 2 allocated, owned by `x`. -/
def h14p : List Op := [.enter [] [lf, lf], .write 0 [0], .write 1 [1], .alloc 0 1 [lf]]
def h14 : PS := run KF2 [] (h14p ++ [.free 2 7])

/-- **H14** (C; A6; N3). `free` twice: the second is rejected (the place is dead). Expected: second
reject; obtained: reject. Twin: the first `free` alone is accepted. -/
theorem H14 : PReach KF2 [] h14 ∧ FreeStep KF2 2 7 h14.s .reject :=
  ⟨run_reach (by decide) (by decide), .reject (by decide)⟩

/-- H15: storage 3 allocated with owner the storage 2; 4, `Observe` on 3, held by the frame. -/
def h15 : PS := run KF2 [] (h14p ++ [.alloc 0 2 [lf], .derive 3 3 .observe])

/-- **H15** (C; O3.2, A6; N3; covered pass 2). `free` of a storage whose owned sub-storage is the
origin of an access held elsewhere: rejected (`FreeAccessOK`). Expected: reject; obtained: reject.
Twin without the access: accepted. -/
theorem H15 : PReach KF2 [] h15 ∧ FreeStep KF2 2 7 h15.s .reject ∧
    PReach KF2 [] (run KF2 [] (h14p ++ [.alloc 0 2 [lf], .free 2 7])) :=
  ⟨run_reach (by decide) (by decide), .reject (by decide), run_reach (by decide) (by decide)⟩

/-- Contracts with the place 3 deallocable by the authority 7. -/
abbrev KF3 : K := KT [] [] [] [3] [(3, 7)]

/-- H16: frame 1, allocator 0, `x` (1) written, result `R` (2); storage 3 owned by `x`, written; the
caller derives 4, `Modify` on `x`, and 5, `Modify` on `R`, and calls frame 2, with the local 4. -/
def h16p : List Op := [.enter [] [lf, lf, lf], .write 0 [0], .write 1 [1], .alloc 0 1 [lf],
  .write 3 [3], .derive 1 1 .modify, .derive 2 2 .modify, .enter [4, 5] [lf]]
def h16a : PS := run KF3 [] h16p
/-- H16 as it can run: the callee frees the storage through its parameter on `x`, then returns. -/
def h16 : PS := run KF3 [] (h16p ++ [.free 3 7, .exit])
/-- Twin of H16: the callee returns without freeing. -/
def h16t : PS := run KF3 [] (h16p ++ [.exit])

/-- **H16** (C; A5, A6; N3). The callee receives by transfer a value owning a storage, frees it,
returns the value; the caller reads that storage. Expected: `ok`, then reject. Obtained (report,
(b)): the reception is rejected, a parameter being an active derived authority on the source held
outside it (O4.4, `ActiveDerivedOutside`), so the callee cannot take a value of the caller. With
the free made through the parameter on `x`, the callee's steps are `ok` and the caller's read of the
storage is rejected for every authority. Twin without the `free`: the read is accepted. -/
theorem H16 : PReach KF3 [] h16a ∧ TransferStep KF3 1 4 h16a.s .reject ∧
    ActiveDerivedOutside h16a.s 1 4 ∧ PReach KF3 [] h16 ∧ (∀ a, Read3Step a [3] h16.s .reject) ∧
    PReach KF3 [] h16t ∧ Read3Step 3 [3] h16t.s (.ok h16t.s) :=
  ⟨run_reach (by decide) (by decide), .reject (by decide), by decide,
    run_reach (by decide) (by decide), read_rejected (by decide), run_reach (by decide) (by decide),
    .ok (by decide)⟩

/-- Contracts with the place 4 deallocable by the authority 7. -/
abbrev KF4 : K := KT [] [] [] [4] [(4, 7)]

/-- H17: frame 1, arena value 0, allocator 1, 2 and 3; storage 4 with the leaves 5 and 6, owned by
0; `newArena 4 4`. -/
def h17p : List Op := [.enter [] [lf, lf, lf, lf], .write 1 [1],
  .alloc 1 0 [lf, (some 4, none, 0), (some 4, none, 0)], .write 0 [0], .newArena 4 4]
def h17 : PS := run KF4 [] (h17p ++ [.issue 0 0 [5] 2])
/-- Twin of H17: the same run, the block ended with its value 2. -/
def h17t : PS := run KF4 [] (h17p ++ [.issue 0 0 [5] 2, .endUse 2])
/-- Contracts declaring deallocable, with the authority 7, both the storage 4 and the region 5. -/
abbrev KF45 : K := KT [] [] [] [4, 5] [(4, 7), (5, 7)]
def h17d : PS := run KF45 [] (h17p ++ [.issue 0 0 [5] 2])

/-- **H17** (C; A6, `Deallocable`; Lib; covered pass 2). `free` of the block on `[5]`: rejected,
the region is a part of the storage, not an owned root, nor deallocable under `KF4`; with the region
declared deallocable (`KF45`), the `free` is still rejected (`OwnedRoot`). Expected: reject;
obtained: reject. Twin: in the same run, the block ended, the `free` of the allocated storage 4 is
accepted. -/
theorem H17 : PReach KF4 [] h17 ∧ FreeStep KF4 5 7 h17.s .reject ∧
    PReach KF45 [] h17d ∧ ¬ OwnedRoot h17d.s 5 ∧ FreeStep KF45 5 7 h17d.s .reject ∧
    PReach KF4 [] h17t ∧ FreeStep KF4 4 7 h17t.s (.ok (freeEff h17t.s 4)) :=
  ⟨run_reach (by decide) (by decide), .reject (by decide), run_reach (by decide) (by decide),
    by decide, .reject (by decide), run_reach (by decide) (by decide), .ok (by decide)⟩

/-! ## D. Arenas -/

/-- H18: the arena of H17 under `K0`, the block on `[5]` issued to 2. -/
def h18 : PS := run K0 [] (h17p ++ [.issue 0 0 [5] 2])

/-- **H18** (D; A5; Lib). The arena value transferred into a block of its own storage: rejected,
the storage would be owned by one of its parts. Expected: reject; obtained: reject. Twin: the
transfer of the arena value into the local leaf 3 is accepted. -/
theorem H18 : PReach K0 [] h18 ∧ TransferStep K0 0 5 h18.s .reject ∧
    ¬ (transferEff h18.s 0 5).Usable 5 ∧ TransferStep K0 0 3 h18.s (.ok (transferEff h18.s 0 3)) :=
  ⟨run_reach (by decide) (by decide), .reject (by decide), by decide, .ok (by decide)⟩

/-- H19: frame 1, arena value 0, allocator 1, values 2 and 3; storage 4 with the leaf 5; parent
arena on 4; block 5 on `[5]` issued to 2; child arena on the leaf 5 with `internal` the block 5. -/
def h19p : List Op := [.enter [] [lf, lf, lf, lf], .write 1 [1], .alloc 1 0 [lf, (some 4, none, 0)],
  .write 0 [0], .newArena 4 4, .issue 0 0 [5] 2, .newArena 5 5]
def h19 : PS := run K0 [] h19p

/-- **H19** (D; F1; Lib; covered pass 6). `reset` of the parent while the child lives: rejected;
after `endUse` of the child value 2: accepted. Expected: reject, then `ok`; obtained: the same. -/
theorem H19 : PReach K0 [] h19 ∧ ResetAtStep K0 0 0 h19.s .reject ∧
    PReach K0 [] (run K0 [] (h19p ++ [.endUse 2, .reset 0 0])) :=
  ⟨run_reach (by decide) (by decide), .reject (by decide), run_reach (by decide) (by decide)⟩

/-- **H20** (D; A10, `arena_reuse_safe`; Lib). `alloc`, `newArena`, `issue`, `endUse`, `reset`, then
`issue` of the same region: every step `ok`. Expected: `ok`; obtained: `ok`. -/
theorem H20 : PReach K0 [] (run K0 [] [.enter [] [lf, lf, lf], .write 1 [1],
    .alloc 1 0 [lf, (some 3, none, 0)], .write 0 [0], .newArena 3 3, .issue 0 0 [4] 2, .endUse 2,
    .reset 0 0, .issue 0 0 [4] 2]) :=
  run_reach (by decide) (by decide)

/-- **H21** (D; case 16; Lib; covered pass 5). The arena of case 16, with a `SharedMutable` arena
value 0 (`KA`): frame 1 passes 4, `Observe` on the arena value, and 5, `Modify` on its buffer 2;
the callee issues `[4]` to its local 6 through `writeShared` on the metadata, transfers 6 to 2 and
exits. Expected: `ok`; obtained: `ok` at each step. -/
theorem H21 : PReach KA [] (run KA [] [.enter [] [lf, lf, lf], .write 1 [1],
    .alloc 1 0 [lf, (some 3, none, 0), (some 3, none, 0)], .write 0 [0], .newArena 3 3,
    .derive 0 0 .observe, .derive 2 2 .modify, .enter [4, 5] [lf], .issue 0 4 [4] 6,
    .transfer 6 2, .exit]) :=
  run_reach (by decide) (by decide)

/-- H21b: frame 1, result 0, derives 1, `Modify` on it, and calls frame 2 with the arena value 1 and
the local buffer 2 with the parts 3 and 4; the callee derives 4, `Modify` on the buffer, stores it
into the arena value, and creates the arena. -/
def h21b : PS := run K0 [] [.enter [] [lf], .derive 0 0 .modify,
  .enter [1] [lf, lf, (some 2, none, 0), (some 2, none, 0)], .derive 3 2 .modify, .store 4 1,
  .newArena 2 4]

/-- **H21b** (D; F2, G4; Lib; covered passes 6 and 7). An arena on a local buffer, transferred to
the caller: rejected at the `transfer` by `AnchorOrderHeld` in the arrival state (G4). Expected:
reject; obtained: reject. Twin: H37, the arena on an allocated storage owned by its value. -/
theorem H21b : PReach K0 [] h21b ∧ TransferStep K0 1 0 h21b.s .reject ∧
    ¬ AnchorOrderHeld (transferEff h21b.s 1 0) :=
  ⟨run_reach (by decide) (by decide), .reject (by decide), by decide⟩

/-! ## E. Pinning and static storage -/

/-- H22: frame 1, `x` (0) written and pinned, `y` (1). -/
def h22 : PS := run K0 [] [.enter [] [lf, lf], .write 0 [0], .pin 0]
def h22t : PS := run K0 [] [.enter [] [lf, lf], .write 0 [0]]

/-- **H22** (E; A8; N3; covered pass 2). The transfer of a value whose in-place leaf is pinned is
rejected; the transfer of a value whose owned storage only is pinned is accepted. Expected:
reject / `ok`; obtained: the same. Twin of the rejection: without the pin, accepted. -/
theorem H22 : PReach K0 [] h22 ∧ TransferStep K0 0 1 h22.s .reject ∧ PReach K0 [] h22t ∧
    TransferStep K0 0 1 h22t.s (.ok (transferEff h22t.s 0 1)) ∧
    PReach K0 [] (run K0 [] [.enter [] [lf, lf, lf], .write 0 [0], .write 1 [1], .alloc 0 1 [lf],
      .pin 3, .transfer 1 2]) :=
  ⟨run_reach (by decide) (by decide), .reject (by decide), run_reach (by decide) (by decide),
    .ok (by decide), run_reach (by decide) (by decide)⟩

/-- H23: frame 1 calls frame 2 with the local 1, pinned. -/
def h23 : PS := run K0 [] [.enter [] [lf], .enter [] [lf], .pin 1]

/-- **H23** (E; B4; N3; covered pass 3). Exit of a frame whose local is pinned: rejected. Expected:
reject; obtained: reject. Twin without the pin: accepted. -/
theorem H23 : PReach K0 [] h23 ∧ ExitStep K0 h23.s .reject ∧
    PReach K0 [] (run K0 [] [.enter [] [lf], .enter [] [lf], .exit]) :=
  ⟨run_reach (by decide) (by decide), .reject (by decide), run_reach (by decide) (by decide)⟩

/-- Statics: the MMIO leaf 0, `Init`, and the leaf 1. -/
def stM : Statics := [((none, none, 0), true), ((none, none, 0), false)]
/-- Contracts with the static leaf 0 pinned. -/
abbrev KM : K := KT [] [0] [] [] []

/-- **H24** (E; C5, D1; N3; covered pass 5). A static MMIO region, pinned by `K.Pinned` (and
directly owned by the base frame, `StaticPinnedBottom`): `transfer` and `endUse` rejected.
Expected: reject, reject; obtained: the same. Twin with a static not pinned: both accepted. -/
theorem H24 : PReach KM stM (PS.init stM) ∧ StaticPinnedBottom KM (PS.init stM).s ∧
    TransferStep KM 0 1 (PS.init stM).s .reject ∧ EndUseStep KM 0 (PS.init stM).s .reject ∧
    TransferStep K0 0 1 (PS.init stM).s (.ok (transferEff (PS.init stM).s 0 1)) ∧
    EndUseStep K0 0 (PS.init stM).s (.ok (endUseEff (PS.init stM).s 0)) :=
  ⟨.init (by decide), fun l hl => by
    obtain rfl : l = 0 := List.mem_singleton.1 hl
    exact ⟨0, ⟨none, .frame 0, 0⟩, by decide, by decide, by decide⟩,
    .reject (by decide), .reject (by decide), .ok (by decide), .ok (by decide)⟩

/-- One static leaf, `Init`. -/
def stW : Statics := [((none, none, 0), true)]
def h25 : PS := run K0 stW [.enter [] []]
def h25t : PS := run K0 stW [.derive 0 0 .modify, .enter [1] []]

/-- **H25** (E; A2, D1; N3; covered pass 5). A static written by a callee without parameter:
rejected for every authority (the root is held by the base frame). Expected: reject; obtained:
reject. Twin with a `Modify` parameter on the static: accepted. -/
theorem H25 : PReach K0 stW h25 ∧ (∀ a, Write3Step a [0] h25.s .reject) ∧ PReach K0 stW h25t ∧
    Write3Step 1 [0] h25t.s (.ok (write3Eff h25t.s [0])) :=
  ⟨run_reach (by decide) (by decide), write_rejected (by decide), run_reach (by decide) (by decide),
    .ok (by decide)⟩

/-- Contracts with the place 2 deallocable by 7; the same with `ExternalDone` on 2. -/
abbrev KP : K := KT [] [] [] [2] [(2, 7)]
abbrev KPd : K := KT [] [] [2] [2] [(2, 7)]
def h26 : PS := run KP [] (h14p ++ [.pin 2])

/-- **H26** (E; B6, A8; N3; covered pass 3). `free` of a pinned storage: rejected; `unpin` without
`ExternalDone`: rejected. Expected: reject, reject; obtained: the same. Twins: `free` without the pin
accepted; with `ExternalDone`, `unpin` then `free` accepted. -/
theorem H26 : PReach KP [] h26 ∧ FreeStep KP 2 7 h26.s .reject ∧ UnpinStep KP 2 h26.s .reject ∧
    PReach KP [] (run KP [] (h14p ++ [.free 2 7])) ∧
    PReach KPd [] (run KPd [] (h14p ++ [.pin 2, .unpin 2, .free 2 7])) :=
  ⟨run_reach (by decide) (by decide), .reject (by decide), .reject (by decide),
    run_reach (by decide) (by decide), run_reach (by decide) (by decide)⟩

/-! ## F. Calls -/

def h27a : PS := run K0 [] [.enter [] [lf], .write 0 [0], .derive 0 0 .modify, .enter [1] [],
  .release 1]
def h27at : PS := run K0 [] [.enter [] [lf], .write 0 [0], .derive 0 0 .modify, .enter [1] []]

/-- **H27a** (F; A2, G1; N3; covered pass 7). The callee releases its `Modify` parameter, then tries
to write the caller's local by another path, with no blocking authority in between: rejected for
every authority. Expected: reject; obtained: reject. Twin: the write through the parameter, before
its release, is accepted. -/
theorem H27a : PReach K0 [] h27a ∧ (∀ a, Write3Step a [0] h27a.s .reject) ∧ PReach K0 [] h27at ∧
    Write3Step 1 [0] h27at.s (.ok (write3Eff h27at.s [0])) :=
  ⟨run_reach (by decide) (by decide), write_rejected (by decide), run_reach (by decide) (by decide),
    .ok (by decide)⟩

/-- H27b: the run of the pass-7 witness `ub` (`call_protects_params_safe_fails_unblock`). -/
def h27b : PS := run K0 [] [.enter [] [lf, (some 0, none, 0), (some 0, none, 0), (none, some 0, 0),
  lf, (some 4, none, 0), (some 4, none, 0)], .derive 1 3 .modify, .derive 0 0 .modify,
  .derive 4 1 .modify, .derive 4 2 .modify, .derive 2 4 .modify, .store 5 5, .store 6 6,
  .enter [3, 4, 7] [], .release 3, .release 5, .release 6]

/-- **H27b** (F; J2; class spec 3; covered pass 7). The same attempt after releasing the authorities
that blocked the origin: the write of the leaf 3 of the parameter's footprint through its origin 1
is accepted by the kernel. Expected: `ok` in the kernel, strong protection deferred to spec 3;
obtained: `ok`. -/
theorem H27b : PReach K0 [] h27b ∧ Write3Step 1 [3] h27b.s (.ok (write3Eff h27b.s [3])) :=
  ⟨run_reach (by decide) (by decide), .ok (by decide)⟩

def h27c1 : PS := run K0 [] [.enter [] [lf], .derive 0 0 .modify, .derive 1 0 .modify]
def h27c2 : PS := run K0 [] [.enter [] [lf, lf], .write 0 [0], .write 1 [1], .alloc 0 1 [lf],
  .derive 1 1 .modify, .derive 2 2 .modify]

/-- **H27c** (F; G1; N3; covered pass 7, `cp0`, `co0`). Passing `&mut x` and a derivation of `x`;
passing `&mut v` and an access to the storage owned by `v`: both calls rejected at `enterFrame`
(G1). Expected: reject; obtained: reject. Twins: each call with the first parameter alone,
accepted. -/
theorem H27c : PReach K0 [] h27c1 ∧ EnterStep [1, 2] [] h27c1.s .reject ∧
    EnterStep [1] [] h27c1.s (.ok (enterEff h27c1.s [1] [])) ∧
    PReach K0 [] h27c2 ∧ EnterStep [3, 4] [] h27c2.s .reject ∧
    EnterStep [3] [] h27c2.s (.ok (enterEff h27c2.s [3] [])) :=
  ⟨run_reach (by decide) (by decide), .reject (by decide), .ok (by decide),
    run_reach (by decide) (by decide), .reject (by decide), .ok (by decide)⟩

/-- **H28** (F; MM-03.1.3; N3). `Observe` and `Modify` parameters on two disjoint parts of a
structure: the call is accepted. Expected: `ok`; obtained: `ok`. -/
theorem H28 : PReach K0 [] (run K0 [] [.enter [] S2, .derive 0 1 .observe, .derive 0 2 .modify,
    .enter [1, 2] []]) :=
  run_reach (by decide) (by decide)

/-- H29: frame 1, `V` (0) and `X` (1) written; 2, `Observe` on `X`, stored into `V`. -/
def h29p : List Op := [.enter [] [lf, lf], .write 0 [0], .write 1 [1], .derive 1 1 .observe,
  .store 2 0]
def h29 : PS := run K0 [] (h29p ++ [.derive 0 0 .observe, .enter [3] []])

/-- **H29** (F; C4; N3; covered pass 4, `rq1`). The callee, with an `Observe` parameter on `V`,
releases the authority held by `V`: rejected (`HolderRight`). Expected: reject; obtained: reject.
Twin with a `Modify` parameter: accepted. -/
theorem H29 : PReach K0 [] h29 ∧ ReleaseStep 2 h29.s .reject ∧
    PReach K0 [] (run K0 [] (h29p ++ [.derive 0 0 .modify, .enter [3] [], .release 2])) :=
  ⟨run_reach (by decide) (by decide), .reject (by decide), run_reach (by decide) (by decide)⟩

/-- H29b: frame 1, arena value 0, allocator 1, value 2; storage 3 with the leaf 4; the block 4 on
`[4]` issued to 2; 5, `Modify` from the block; 6, `Observe` on the arena value; the call. -/
def h29bo : List Op := [.enter [] [lf, lf, lf], .write 1 [1], .alloc 1 0 [lf, (some 3, none, 0)],
  .write 0 [0], .newArena 3 3, .issue 0 0 [4] 2, .derive 4 4 .modify, .derive 0 0 .observe,
  .enter [6, 5] []]

/-- **H29b** (F; G1; Lib; covered pass 7). The arena value passed `Observe` and a `Modify` parameter
derived from a block held by a value of the caller: the call is accepted. Expected: `ok`;
obtained: `ok`. -/
theorem H29b : PReach K0 [] (run K0 [] h29bo) :=
  run_reach (by decide) (by decide)

/-! ## G. Handles (material §4, `Ern.HandlePool`) -/

/-- Pool base: frame 1, allocator 0, pool value 1, handle leaves 2 and 3; storage 4 with the entries
5 and 6, owned by the pool value, `internal` the root 4; `newPool 4 4`. -/
def pb : List Op := [.enter [] [lf, lf, lf, lf], .write 0 [0], .write 1 [1],
  .alloc 0 1 [lf, (some 4, none, 0), (some 4, none, 0)], .newPool 4 4]

def h30 : PS := run K0 [] (pb ++ [.allocSlot 0 0 2, .freeSlot 0 0 ⟨0, 0, 0⟩, .allocSlot 0 0 3])

/-- **H30** (G; §4, generation; Lib). Resolution of a handle after `freeSlot` and reuse of its
entry: `fail`, state unchanged. Expected: `fail`; obtained: `fail`. The handle of the reused entry
resolves. -/
theorem H30 : PReach K0 [] h30 ∧
    ResolveStep 0 ⟨0, 0, 0⟩ .modify h30 (.fail h30) ∧
    (pexec K0 h30 (.resolve 0 ⟨0, 0, 1⟩ .modify)).isSome = true :=
  ⟨run_reach (by decide) (by decide),
    .fail (pl := ⟨0, 4, 4, [⟨5, 1, true⟩, ⟨6, 0, false⟩]⟩) (by decide) (by decide) (by decide),
    by decide⟩

/-- H31: two entries allocated (handles in 2 and 3), entry 0 resolved `Modify` (companion 5). -/
def h31o : List Op := pb ++ [.allocSlot 0 0 2, .allocSlot 0 0 3, .resolve 0 ⟨0, 0, 0⟩ .modify]
def h31 : PS := run K0 [] h31o
/-- The pool of H31 and H32. -/
def plA : Pool := ⟨0, 4, 4, [⟨5, 0, true⟩, ⟨6, 0, true⟩]⟩

/-- **H31a** (G; §4, exclusivity of the pool value; Lib). Two simultaneous `resolve Modify`: the
second is rejected, whatever the handle (another entry, a stale handle), and so is a `resolve
Observe`. Expected: reject; obtained: reject. Twin: after `unresolve` of the first, accepted. -/
theorem H31a : PReach K0 [] h31 ∧ h31.pools = [plA] ∧
    ResolveStep 0 ⟨0, 1, 0⟩ .modify h31 .reject ∧ ResolveStep 0 ⟨0, 1, 7⟩ .modify h31 .reject ∧
    ResolveStep 0 ⟨0, 0, 0⟩ .observe h31 .reject ∧
    PReach K0 [] (run K0 [] (h31o ++ [.unresolve 5, .resolve 0 ⟨0, 1, 0⟩ .modify])) :=
  ⟨run_reach (by decide) (by decide), by decide, .reject (pl := plA) (by decide) (by decide),
    .reject (pl := plA) (by decide) (by decide), .reject (pl := plA) (by decide) (by decide),
    run_reach (by decide) (by decide)⟩

def h31b : PS := run K0 [] (pb ++ [.allocSlot 0 0 2, .allocSlot 0 0 3])

/-- **H31b** (G; §4, dynamic distinctness; Lib). `resolveMany Modify` of two handles designating the
same entry: `fail`, state unchanged. Expected: `fail`; obtained: `fail`. Twin with two distinct
entries: accepted. -/
theorem H31b : PReach K0 [] h31b ∧
    ResolveManyStep K0 0 [⟨0, 0, 0⟩, ⟨0, 0, 0⟩] .modify h31b (.fail h31b) ∧
    (pexec K0 h31b (.resolveMany 0 [⟨0, 0, 0⟩, ⟨0, 1, 0⟩] .modify)).isSome = true :=
  ⟨run_reach (by decide) (by decide), .fail (pl := plA) (by decide) (by decide) (by decide),
    by decide⟩

/-- `resolveMany Observe` is rejected (report, (g)): the material builds the entries by `split` of
the companion, and `split` requires `Modify` (MM-03.3 §3, O2). -/
theorem resolveMany_observe_rejected :
    ResolveManyStep K0 0 [⟨0, 0, 0⟩, ⟨0, 1, 0⟩] .observe h31b .reject :=
  .noSplit (pl := plA) (by decide) (by decide) (by decide) (by decide)

/-- **H32** (G; §4, O3.2; Lib). `freeSlot` while a resolved access on the entry is active:
rejected. Expected: reject; obtained: reject. Twin after `unresolve`: accepted. -/
theorem H32 : FreeSlotStep K0 0 0 ⟨0, 0, 0⟩ h31 .reject ∧
    PReach K0 [] (run K0 [] (h31o ++ [.unresolve 5, .freeSlot 0 0 ⟨0, 0, 0⟩])) :=
  ⟨.borrowed (pl := plA) (sl := ⟨5, 0, true⟩) (by decide) (by decide) (by decide) (by decide)
    (by decide), run_reach (by decide) (by decide)⟩

/-- H33: frame 1, leaf 0, derives 1, `Modify` on it, and calls frame 2 with the allocator 1, the
pool value 2, the handle leaf 3 and the leaf 4; the pool is created in frame 2 on the storage 5
(entries 6 and 7, `internal` 6); entry 0 resolved, entry authority 8. -/
def h33 : PS := run K0 [] [.enter [] [lf], .derive 0 0 .modify, .enter [1] [lf, lf, lf, lf],
  .write 2 [1], .write 3 [2], .alloc 1 2 [lf, (some 5, none, 0), (some 5, none, 0)], .newPool 5 6,
  .allocSlot 0 0 3, .resolve 0 ⟨0, 0, 0⟩ .modify]

/-- **H33** (G; G4; Lib). A resolved access stored in a value of a frame older than the pool:
rejected (`EffAnchorOK`). Expected: reject; obtained: reject. Twin: stored into a value of the
frame of the pool, accepted. -/
theorem H33 : PReach K0 [] h33 ∧ StoreStep 8 0 h33.s .reject ∧
    StoreStep 8 4 h33.s (.ok (storeEff h33.s 8 4)) :=
  ⟨run_reach (by decide) (by decide), .reject (by decide), .ok (by decide)⟩

/-- **H34** (G; §4; Lib). A handle copied (read from 2, written into 3), then two successive
`resolve Modify` of it, with a write of the entry in between: every step `ok`. Expected: `ok`;
obtained: `ok`. -/
theorem H34 : PReach K0 [] (run K0 [] (pb ++ [.allocSlot 0 0 2, .read 2 [2], .write 3 [3],
    .resolve 0 ⟨0, 0, 0⟩ .modify, .write 6 [5], .unresolve 5, .resolve 0 ⟨0, 0, 0⟩ .modify])) :=
  run_reach (by decide) (by decide)

/-- H34b: a second pool, on the storage 7 (entries 8 and 9, `internal` 5). -/
def h34b : PS := run K0 [] (pb ++ [.alloc 0 1 [lf, (some 7, none, 0), (some 7, none, 0)],
  .newPool 7 5, .allocSlot 0 0 2])

/-- **H34b** (G; §4, identity of the pool; Lib). A handle of another pool: `fail`. Expected:
`fail`; obtained: `fail`. On its own pool, the handle resolves. -/
theorem H34b : PReach K0 [] h34b ∧ h34b.pools.map (·.id) = [0, 1] ∧
    ResolveStep 1 ⟨0, 0, 0⟩ .modify h34b (.fail h34b) ∧
    (pexec K0 h34b (.resolve 0 ⟨0, 0, 0⟩ .modify)).isSome = true :=
  ⟨run_reach (by decide) (by decide), by decide,
    .fail (pl := ⟨1, 7, 5, [⟨8, 0, false⟩, ⟨9, 0, false⟩]⟩) (by decide) (by decide) (by decide),
    by decide⟩

/-- H44: the run described below. -/
def h44o : List Op := [.enter [] [lf, lf, lf, lf, lf], .write 1 [1],
  .alloc 1 0 [lf, (some 5, none, 0), (some 6, none, 0), (some 7, none, 0), (some 7, none, 0),
    (some 6, none, 0), (some 10, none, 0), (some 10, none, 0)], .write 0 [0], .newArena 5 5,
  .issue 0 0 [8, 9, 11, 12] 2, .newPool 6 6, .allocSlot 0 0 3, .allocSlot 0 0 4,
  .resolve 0 ⟨0, 0, 0⟩ .modify, .write 8 [8, 9], .unresolve 7,
  .resolve 0 ⟨0, 1, 0⟩ .modify, .write 10 [11, 12], .unresolve 9, .endUse 2, .reset 0 0]

/-- **H44** (G; §4, A10; Lib). Frame 1: arena value 0, allocator 1, pool value 2, handle leaves 3 and
4; storage 5 owned by 0, with the place 6 holding the nodes 7 (fields 8, 9) and 10 (fields 11, 12);
arena on 5; the block on the footprint of 6 issued to the pool value; pool on 6 with that block as
`internal`. Each node resolved in turn, its link written (the handle of the other node), then
unresolved; `endUse` of the pool value; `reset` of the arena, without reading the links. Expected:
`ok`; obtained: `ok` at each step. -/
theorem H44 : PReach K0 [] (run K0 [] h44o) :=
  run_reach (by decide) (by decide)

/-! ## H. Abusive rejections (the model must accept) -/

/-- H35: frame 1, structure 0 with the columns 1 and 2, split and written. -/
def h35o : List Op := [.enter [] S2, .split 0 [[1], [2]], .write 1 [1], .write 2 [2]]

/-- **H35** (H; MM-03.1.3; N3; covered jalon 1, case 15). SoA: two columns written after `split`.
Expected: `ok`; obtained: `ok`. -/
theorem H35 : PReach K0 [] (run K0 [] h35o) :=
  run_reach (by decide) (by decide)

/-- H36: a local written, ended, written again and read. -/
def h36o : List Op := [.enter [] [lf], .write 0 [0], .endUse 0, .write 0 [0], .read 0 [0]]

/-- **H36** (H; C8; N3; covered pass 4). A local ended by `endUse`, then written again and read.
Expected: `ok`; obtained: `ok`. -/
theorem H36 : PReach K0 [] (run K0 [] h36o) :=
  run_reach (by decide) (by decide)

/-- H37: frame 1, result 0, allocator 1 written; it passes 2 (`Modify` on 0) and 3 (`Modify` on 1);
the callee allocates the storage 3 (leaf 4) owned by its arena value 2, of root 5, creates the arena,
transfers its value to the result and exits. -/
def h37o : List Op := [.enter [] [lf, lf], .write 1 [1], .derive 0 0 .modify, .derive 1 1 .modify,
  .enter [2, 3] [lf], .alloc 1 2 [lf, (some 3, none, 0)], .write 4 [2], .newArena 3 5,
  .transfer 2 0, .exit]

/-- **H37** (H; A5; Lib; covered pass 2). An arena created by the callee on a storage allocated for
its value, and returned: every step `ok`. Expected: `ok`; obtained: `ok`. Negative twin: H21b. -/
theorem H37 : PReach K0 [] (run K0 [] h37o) := run_reach (by decide) (by decide)

/-- H45: the run of the pass-6 witness `fb`, then `reset`. -/
def h45o : List Op := [.enter [] [lf, lf, lf, lf], .write 1 [1],
  .alloc 1 0 [lf, (some 4, none, 0), (some 5, none, 0), (some 5, none, 0), (some 4, none, 0),
    (some 8, none, 0), (some 8, none, 0)], .write 0 [0], .newArena 4 4,
  .issue 0 0 [6, 7] 2, .issue 0 0 [9, 10] 3, .derive 6 9 .modify, .store 7 7,
  .derive 5 6 .modify, .store 8 10, .release 7, .release 8, .endUse 2, .endUse 3, .reset 0 0]

/-- **H45** (H; F7 (b); Lib; covered pass 6, `progress_cycle_disjoint_fields`). Two arena nodes,
`A.link` holding a view on `B.data` and `B.link` on `A.data`; teardown (`release` of both views,
`endUse` of both node values), then `reset`. Expected: `ok` throughout; obtained: `ok`. -/
theorem H45 : PReach K0 [] (run K0 [] h45o) :=
  run_reach (by decide) (by decide)

/-- H46: array 0 (leaves 1, 2), structure 3 (field 4); a view stored, read, released. -/
def h46o : List Op := [.enter [] [lf, (some 0, none, 0), (some 0, none, 0), lf, (some 3, none, 0)],
  .write 0 [1, 2], .derive 0 0 .observe, .store 2 4, .read 2 [1], .release 2]

/-- **H46** (H; F4; N3; covered pass 6). A view on a local array, stored into a field of a local
structure, read, then released. Expected: `ok`; obtained: `ok`. -/
theorem H46 : PReach K0 [] (run K0 [] h46o) :=
  run_reach (by decide) (by decide)

/-- H47: structures 0 (fields 1, 2) and 3 (fields 4, 5); the field 1 written and transferred. -/
def h47o : List Op := [.enter [] [lf, (some 0, none, 0), (some 0, none, 0), lf, (some 3, none, 0),
  (some 3, none, 0)], .write 0 [1], .transfer 1 4]

/-- **H47** (H; J1; N3; covered pass 8). Field-by-field transfer of a partially initialised
aggregate: the written field is transferred. Expected: `ok`; obtained: `ok`. -/
theorem H47 : PReach K0 [] (run K0 [] h47o) :=
  run_reach (by decide) (by decide)

/-! ## I. Progress (`NoLock`, material §5) -/

/-- Pass-7 arena `fa`: frame 1, arena value 0, allocator 1, values 2 and 3; storage 4 with the nodes
5 and 6; blocks 5 on `[5]` to 2 and 6 on `[6]` to 3. -/
def fao : List Op := [.enter [] [lf, lf, lf, lf], .write 1 [1],
  .alloc 1 0 [lf, (some 4, none, 0), (some 4, none, 0)], .write 0 [0], .newArena 4 4,
  .issue 0 0 [5] 2, .issue 0 0 [6] 3]
/-- H48: 7, `Modify` on B from its block, stored into A; 8, `Modify` on A from its block. -/
def h48o : List Op := fao ++ [.derive 6 6 .modify, .store 7 5, .derive 5 5 .modify]
def h48 : PS := run K0 [] h48o
def h48t : PS := run K0 [] (fao ++ [.derive 6 6 .modify, .derive 5 5 .modify])

/-- **H48** (I; G2; N3; covered pass 7, `progress_cycle_whole_nodes`). A cycle of two authorities on
whole nodes by direct `store`: the closing `store` is rejected by its arrival clause. Expected:
reject; obtained: reject. Twin without the first `store`: accepted. -/
theorem H48 : PReach K0 [] h48 ∧ StoreStep 8 6 h48.s .reject ∧ PReach K0 [] h48t ∧
    StoreStep 8 6 h48t.s (.ok (storeEff h48t.s 8 6)) :=
  ⟨run_reach (by decide) (by decide), .reject (by decide), run_reach (by decide) (by decide),
    .ok (by decide)⟩

/-- H49: the cycle of H48 closed with the helper 9, then released (pass-7 `f7a_cycle_by_release`). -/
def h49o : List Op := h48o ++ [.derive 7 6 .modify, .store 8 6, .release 9]
def h49 : PS := run K0 [] h49o

/-- **H49** (I; §5; N3; covered pass 7). The same cycle, closed through a helper authority then its
`release`: accepted; the authorities 7 and 8 are then exercisable at no mode and `reset` is
rejected. Expected: to arbitrate (§5); obtained: `ok`, with a residual blocking. -/
theorem H49 : PReach K0 [] h49 ∧ ¬ h49.s.ExercisableAt 7 .observe ∧
    ¬ h49.s.ExercisableAt 8 .observe ∧ ResetAtStep K0 0 0 h49.s .reject :=
  ⟨run_reach (by decide) (by decide), by decide, by decide, .reject (by decide)⟩

/-- H50, `transfer`: frame 1, structure 0 with the field 1, structure 2 with the field 3; 2,
`Modify` on 3, stored into 1; 0 transferred into 2 (pass-7 `held_unexercisable_by_transfer`). -/
def h50ao : List Op := [.enter [] [lf, (some 0, none, 0), lf, (some 2, none, 0)],
  .derive 1 3 .modify, .store 2 1, .transfer 0 2]
def h50a : PS := run K0 [] h50ao
/-- H50, `issue`: the block on the node 5 issued to the node 5 itself (pass-7
`held_unexercisable_by_issue`). -/
def h50bo : List Op := fao.take 5 ++ [.issue 0 0 [5] 5]
def h50b : PS := run K0 [] h50bo

/-- **H50** (I; §5; N3, Lib; covered pass 7). An authority transferred or issued into the place it
covers: accepted, and then exercisable at no mode. Expected: to arbitrate (§5); obtained: `ok`,
with a residual blocking. -/
theorem H50 : PReach K0 [] h50a ∧ ¬ h50a.s.ExercisableAt 2 .observe ∧
    PReach K0 [] h50b ∧ ¬ h50b.s.ExercisableAt 5 .observe :=
  ⟨run_reach (by decide) (by decide), by decide, run_reach (by decide) (by decide), by decide⟩

/-- H51: frame 1, allocator 0, `v` (1) written; storage 2 with the element 3, owned by `v`, of root 2
held by `v`; the helper 3, `Modify` on the storage; 4, `Observe` on `v`, stored into the element 3;
the helper released. -/
def h51o : List Op := [.enter [] [lf, lf], .write 0 [0], .write 1 [1],
  .alloc 0 1 [lf, (some 2, none, 0)], .derive 2 2 .modify, .derive 1 1 .observe, .store 4 3,
  .release 3]
def h51 : PS := run K0 [] h51o
/-- H51 without the helper: 3, `Observe` on `v`. -/
def h51n : PS := run K0 [] [.enter [] [lf, lf], .write 0 [0], .write 1 [1],
  .alloc 0 1 [lf, (some 2, none, 0)], .derive 1 1 .observe]

/-- **H51** (I; §5; N3). An element of a storage owned by `v` holds a view on `v`. The direct `store`
is rejected: the view already takes away the frame's `Modify` on `v`, hence on the storage `v` owns
(`HasRight` before the step, B2), and the arrival clause of G2 fails too; with a helper on the
storage, then its `release`, the configuration is reached. Then `v` can be neither written, ended by `endUse`, nor relieved of the view (`release`
rejected), while the view stays exercisable at `Observe`; the exit of the frame releases it.
Expected: to arbitrate (§5); obtained: `ok`, with a residual blocking until the exit. -/
theorem H51 : PReach K0 [] h51n ∧ StoreStep 3 3 h51n.s .reject ∧ PReach K0 [] h51 ∧
    Write3Step 1 [1] h51.s .reject ∧ ReleaseStep 4 h51.s .reject ∧ EndUseStep K0 1 h51.s .reject ∧
    h51.s.ExercisableAt 4 .observe ∧ ExitStep K0 h51.s (.ok (exitEff h51.s)) :=
  ⟨run_reach (by decide) (by decide), .reject (by decide), run_reach (by decide) (by decide),
    .reject (by decide), .reject (by decide), .reject (by decide), by decide, .ok (by decide)⟩

/-! ## Usage scenarios (material §5b) -/

/-- W1: frame 1, allocator 0, pool value 1, handle leaves 2 and 3; storage 4 owned by the pool
value, with the nodes 5 (fields `data` 6, `parent` 7, `child` 8) and 9 (10, 11, 12); pool on 4. The
two nodes are linked both ways (the child of the first, the parent of the second), each through a
`resolve Modify`, writes, `unresolve`; then a resolution of the first node to write its data; then
`freeSlot` of the second, still designated by the child field of the first. -/
def w1o : List Op := [.enter [] [lf, lf, lf, lf], .write 0 [0], .write 1 [1],
  .alloc 0 1 [lf, (some 4, none, 0), (some 5, none, 0), (some 5, none, 0), (some 5, none, 0),
    (some 4, none, 0), (some 9, none, 0), (some 9, none, 0), (some 9, none, 0)], .newPool 4 4,
  .allocSlot 0 0 2, .allocSlot 0 0 3,
  .resolve 0 ⟨0, 0, 0⟩ .modify, .write 6 [6, 8], .unresolve 5,
  .resolve 0 ⟨0, 1, 0⟩ .modify, .write 8 [10, 11], .unresolve 7,
  .resolve 0 ⟨0, 0, 0⟩ .modify, .write 10 [6], .unresolve 9,
  .freeSlot 0 0 ⟨0, 1, 0⟩]
def w1 : PS := run K0 [] w1o
/-- The pool of W1 after the `freeSlot`. -/
def plW : Pool := ⟨0, 4, 4, [⟨5, 0, true⟩, ⟨9, 1, false⟩]⟩
def w1b : PS := run K0 [] (w1o ++ [.resolve 0 ⟨0, 0, 0⟩ .modify])

/-- **W1** (§5b, scene graph; Lib). Every step `ok`; `resolve` of the stale handle of the freed
node: `fail`; `freeSlot` during an active resolution: reject. Expected: the same; obtained: the
same. Twin of the rejection: after `unresolve`, `freeSlot` accepted. -/
theorem W1 : PReach K0 [] w1 ∧ w1.pools = [plW] ∧ ResolveStep 0 ⟨0, 1, 0⟩ .modify w1 (.fail w1) ∧
    PReach K0 [] w1b ∧ FreeSlotStep K0 0 0 ⟨0, 0, 0⟩ w1b .reject ∧
    PReach K0 [] (run K0 [] (w1o ++ [.resolve 0 ⟨0, 0, 0⟩ .modify, .unresolve 11,
      .freeSlot 0 0 ⟨0, 0, 0⟩])) :=
  ⟨run_reach (by decide) (by decide), by decide,
    .fail (pl := plW) (by decide) (by decide) (by decide), run_reach (by decide) (by decide),
    .borrowed (pl := plW) (sl := ⟨5, 0, true⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide), run_reach (by decide) (by decide)⟩

/-- W2: frame 1, allocator 0, owners 1 and 2 of two archetypes, entity pool value 3, handle leaves
4, 5, 6. Archetype 7 (columns 8 with 9, 10 and 11 with 12, 13) owned by 1; archetype 14 (columns
15 with 16, 17 and 18 with 19, 20) owned by 2; entity storage 21 (entries 22, 23, 24) owned by 3,
pool on it. `split` of the archetype into the columns (10 and 11), the second written, a read view
12 on it; system A writes the first column while system B reads through the view; `resolveMany
Modify` of three distinct entities. -/
def w2o : List Op := [.enter [] [lf, lf, lf, lf, lf, lf, lf], .write 0 [0], .write 1 [1],
  .write 2 [2], .write 3 [3],
  .alloc 0 1 [lf, (some 7, none, 0), (some 8, none, 0), (some 8, none, 0), (some 7, none, 0),
    (some 11, none, 0), (some 11, none, 0)],
  .alloc 0 2 [lf, (some 14, none, 0), (some 15, none, 0), (some 15, none, 0), (some 14, none, 0),
    (some 18, none, 0), (some 18, none, 0)],
  .alloc 0 3 [lf, (some 21, none, 0), (some 21, none, 0), (some 21, none, 0)], .newPool 21 9,
  .allocSlot 0 0 4, .allocSlot 0 0 5, .allocSlot 0 0 6,
  .split 7 [[9, 10], [12, 13]], .write 11 [12, 13], .derive 11 11 .observe,
  .write 10 [9, 10], .read 12 [12, 13], .resolveMany 0 [⟨0, 0, 0⟩, ⟨0, 1, 0⟩, ⟨0, 2, 0⟩] .modify]
def w2 : PS := run K0 [] w2o
def w2a : PS := run K0 [] (w2o ++ [.release 12])

/-- **W2** (§5b, ECS archetype and sparse set; Lib). Expected: disjoint reads and writes `ok`;
`resolveMany` `ok`; the move of a field of the row while the column view is active: reject; after
its release: `ok`. Obtained: disjoint accesses, `resolveMany` and the rejection during the view as
expected. After the release: if "the view of the column" is the read view 12, the move is still
rejected, by the column authority 11 given by `split` (O4.4; report, (b)); if it is the column
authority itself, the move is accepted after its release (and that of the first column authority,
which covers the other field of the row). -/
theorem W2 : PReach K0 [] w2 ∧ TransferStep K0 12 19 w2.s .reject ∧ PReach K0 [] w2a ∧
    TransferStep K0 12 19 w2a.s .reject ∧ ActiveDerivedOutside w2a.s 12 11 ∧
    PReach K0 [] (run K0 [] (w2o ++ [.release 12, .release 11, .release 10, .transfer 9 16,
      .transfer 12 19])) :=
  ⟨run_reach (by decide) (by decide), .reject (by decide), run_reach (by decide) (by decide),
    .reject (by decide), by decide, run_reach (by decide) (by decide)⟩

/-- W3, literal reading: frame 1, arena value 0, allocator 1, block values 2, 3, 4, structure 5
with the fields 6, 7, 8; storage 9 (leaves 10, 11, 12) owned by 0, `internal` 6; three blocks
issued to 2, 3, 4; three views (10, 11, 12), `Observe` on the blocks, stored into the fields. -/
def w3o : List Op := [.enter [] [lf, lf, lf, lf, lf, lf, (some 5, none, 0), (some 5, none, 0),
    (some 5, none, 0)], .write 1 [1],
  .alloc 1 0 [lf, (some 9, none, 0), (some 9, none, 0), (some 9, none, 0)], .write 0 [0],
  .newArena 9 6, .issue 0 0 [10] 2, .issue 0 0 [11] 3, .issue 0 0 [12] 4,
  .derive 7 10 .observe, .derive 8 11 .observe, .derive 9 12 .observe, .store 10 6, .store 11 7,
  .store 12 8]
def w3 : PS := run K0 [] w3o
def w3e : PS := run K0 [] (w3o ++ [.endUse 5])
/-- W3, reading where the blocks are issued into fields of the structure: structure 2 with the
fields 3 to 8; storage 9 (leaves 10, 11, 12), `internal` 3; the blocks 4, 5, 6 issued into the
fields 3, 4, 5; the views 7, 8, 9 derived from them and stored into the fields 6, 7, 8. -/
def w3vo : List Op := [.enter [] [lf, lf, lf, (some 2, none, 0), (some 2, none, 0),
    (some 2, none, 0), (some 2, none, 0), (some 2, none, 0), (some 2, none, 0)], .write 1 [1],
  .alloc 1 0 [lf, (some 9, none, 0), (some 9, none, 0), (some 9, none, 0)], .write 0 [0],
  .newArena 9 3, .issue 0 0 [10] 3, .issue 0 0 [11] 4, .issue 0 0 [12] 5,
  .derive 4 10 .observe, .derive 5 11 .observe, .derive 6 12 .observe, .store 7 6, .store 8 7,
  .store 9 8]

/-- **W3** (§5b, frame arena; Lib). Expected: `reset` while the views live: reject; after `endUse`
of the structure: `ok`; reissue `ok`. Obtained, literal reading (report, (b)): reject while the
views live; after `endUse` of the structure, `reset` is still rejected, the three blocks being held
by the values 2, 3, 4 (MM-03.3 §6, O19.2); after their end, `reset` and the reissue are accepted.
With the blocks issued into fields of the structure and the views stored into others, the expected
verdicts are obtained. -/
theorem W3 : PReach K0 [] w3 ∧ ResetAtStep K0 0 0 w3.s .reject ∧ PReach K0 [] w3e ∧
    ResetAtStep K0 0 0 w3e.s .reject ∧
    PReach K0 [] (run K0 [] (w3o ++ [.endUse 5, .endUse 2, .endUse 3, .endUse 4, .reset 0 0,
      .issue 0 0 [10] 2])) ∧
    PReach K0 [] (run K0 [] w3vo) ∧ ResetAtStep K0 0 0 (run K0 [] w3vo).s .reject ∧
    PReach K0 [] (run K0 [] (w3vo ++ [.endUse 2, .reset 0 0, .issue 0 0 [10] 3])) :=
  ⟨run_reach (by decide) (by decide), .reject (by decide), run_reach (by decide) (by decide),
    .reject (by decide), run_reach (by decide) (by decide), run_reach (by decide) (by decide),
    .reject (by decide), run_reach (by decide) (by decide)⟩

/-! ## Observations on the contract of the pool (report, (g))

Reached runs that bear on the reading of material §4, kept as witnesses. -/

/-- The prefix of H44: a pool on an arena block, both entries allocated, nothing resolved, nothing
pinned. -/
def ob1 : PS := run K0 [] (h44o.take 9)

/-- `freeSlot` on a pool whose `internal` is derived (here the block 6) is rejected by the
preconditions of `endUse` (material §4: "reject si une précondition d'`endUse` échoue"):
`internal` itself is an active derived authority on the entry, held outside it (`EndUseAccessOK`,
A6). -/
theorem pool_freeSlot_derived_internal : PReach K0 [] ob1 ∧ ob1.res = [] ∧
    FreeSlotStep K0 0 0 ⟨0, 0, 0⟩ ob1 .reject ∧ ¬ EndUseAccessOK ob1.s 7 6 ∧ ob1.s.org 6 = some 5 :=
  ⟨run_reach (by decide) (by decide), by decide,
    .endUse (pl := ⟨0, 6, 6, [⟨7, 0, true⟩, ⟨10, 0, true⟩]⟩) (sl := ⟨7, 0, true⟩) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), by decide, by decide⟩

/-- Contracts with the leaf 1 (the pool value of `pb`) `SharedMutable`. -/
abbrev KSh : K := KT [1] [] [] [] []
/-- A callee with an `Observe` parameter (5) on the pool value of `pb`, entry 0 allocated. -/
def ob2 : PS := run KSh [] (pb ++ [.allocSlot 0 0 2, .derive 1 1 .observe, .enter [5] [lf]])

/-- With the right to update the pool value by `writeShared` on its `SharedMutable` metadata
(material §4), `allocSlot` is accepted while `freeSlot` is rejected: `endUse` asks `Modify` on the
entry (A2). -/
theorem pool_freeSlot_shared_right : PReach KSh [] ob2 ∧ ¬ HasRight ob2.s .modify 1 ∧
    PoolRight KSh ob2.s ⟨0, 4, 4, [⟨5, 0, true⟩, ⟨6, 0, false⟩]⟩ 5 ∧
    (pexec KSh ob2 (.allocSlot 0 5 7)).isSome = true ∧
    FreeSlotStep KSh 0 5 ⟨0, 0, 0⟩ ob2 .reject ∧ ¬ HasRight ob2.s .modify 5 :=
  ⟨run_reach (by decide) (by decide), by decide, by decide, by decide,
    .endUse (pl := ⟨0, 4, 4, [⟨5, 0, true⟩, ⟨6, 0, false⟩]⟩) (sl := ⟨5, 0, true⟩) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), by decide⟩

/-- Two pools on the same storage and `internal` 5 (`newPool` reads the arenas only, O17.4): pool 0
frees its entry 0 and allocates it again; the handle of pool 1 on the same place still resolves. -/
def ob3o : List Op := [.enter [] [lf, lf, lf, lf, lf], .write 0 [0], .write 1 [1],
  .alloc 0 1 [lf, (some 5, none, 0), (some 5, none, 0)], .newPool 5 5, .newPool 5 5,
  .allocSlot 0 0 2, .allocSlot 1 0 3, .freeSlot 0 0 ⟨0, 0, 0⟩, .allocSlot 0 0 4]

theorem pool_two_on_one_internal : PReach K0 [] (run K0 [] ob3o) ∧
    (run K0 [] ob3o).pools = [⟨0, 5, 5, [⟨6, 1, true⟩, ⟨7, 0, false⟩]⟩,
      ⟨1, 5, 5, [⟨6, 0, true⟩, ⟨7, 0, false⟩]⟩] ∧
    PReach K0 [] (run K0 [] (ob3o ++ [.resolve 1 ⟨1, 0, 0⟩ .modify])) :=
  ⟨run_reach (by decide) (by decide), by decide, run_reach (by decide) (by decide)⟩

/-- Two pools on the same `internal`: the `freeSlot` of pool 1 ends the content of the entry 0 of
pool 0, written and live. -/
def ob3b : List Op := pb ++ [.newPool 4 4, .allocSlot 0 0 2, .allocSlot 1 0 3, .write 4 [5],
  .freeSlot 1 0 ⟨1, 0, 0⟩]

theorem pool_two_freeSlot_cross : PReach K0 [] (run K0 [] ob3b) ∧
    (run K0 [] (ob3b.take 9)).s.I 5 = .init ∧ (run K0 [] ob3b).s.I 5 = .uninit ∧
    (run K0 [] ob3b).pools.map (fun pl => pl.slots.map (·.live)) = [[true, false], [false, false]] :=
  ⟨run_reach (by decide) (by decide), by decide, by decide, by decide⟩

/-- The mirror: `newArena` on the `internal` of a live pool is accepted (O17.4 reads arenas). -/
theorem arena_on_pool_internal :
    PReach K0 [] (run K0 [] (pb ++ [.allocSlot 0 0 2, .newArena 4 4])) :=
  run_reach (by decide) (by decide)

/-- "Périmé" read twice (report, (f)): on a fresh pool, `resolveMany` of the handle of a free entry at
its current generation fails (the entry is free), while `freeSlot` of the same handle is accepted
(only the identity and the generation are read). -/
theorem pool_free_entry_handle : PReach K0 [] (run K0 [] pb) ∧
    ResolveManyStep K0 0 [⟨0, 0, 0⟩] .modify (run K0 [] pb) (.fail (run K0 [] pb)) ∧
    (pexec K0 (run K0 [] pb) (.freeSlot 0 0 ⟨0, 0, 0⟩)).isSome = true :=
  ⟨run_reach (by decide) (by decide),
    .fail (pl := ⟨0, 4, 4, [⟨5, 0, false⟩, ⟨6, 0, false⟩]⟩) (by decide) (by decide) (by decide),
    by decide⟩

/-- `allocSlot` leaves the content of the entry as it is (material §4: "son contenu reste
`Uninit`"): a storage written before `newPool` gives a live entry whose content is `Init`. -/
theorem pool_allocSlot_content_init : PReach K0 [] (run K0 [] [.enter [] [lf, lf, lf, lf],
      .write 0 [0], .write 1 [1], .alloc 0 1 [lf, (some 4, none, 0), (some 4, none, 0)],
      .write 4 [5], .newPool 4 4, .allocSlot 0 0 2]) ∧
    (run K0 [] [.enter [] [lf, lf, lf, lf], .write 0 [0], .write 1 [1],
      .alloc 0 1 [lf, (some 4, none, 0), (some 4, none, 0)], .write 4 [5], .newPool 4 4,
      .allocSlot 0 0 2]).s.I 5 = .init :=
  ⟨run_reach (by decide) (by decide), by decide⟩

/-! ## J. Out of kernel (material §1 J): the one expressible expansion -/

/-- Contracts with the place 3 deallocable by the authority 7. -/
abbrev KJ : K := KT [] [] [] [3] [(3, 7)]

/-- H42 (`defer free(x)` then `transfer(x)` before an exit) has no `defer` in the kernel; its
straight-line expansion, `transfer` of the value `x` (1) owning the storage 3 into `y` (2), then the
deferred `free` of that storage, runs: the kernel accepts the `free` of the storage now owned by
`y` (report, (a), section J). -/
theorem J_H42_expansion : PReach KJ [] (run KJ [] [.enter [] [lf, lf, lf], .write 0 [0],
    .write 1 [1], .alloc 0 1 [lf], .transfer 1 2, .free 3 7]) :=
  run_reach (by decide) (by decide)

end Ern.MM03.Horrors
