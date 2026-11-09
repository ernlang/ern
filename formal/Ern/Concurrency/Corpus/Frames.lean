import Ern.Concurrency.Corpus.MX

/-!
# Corpus of milestone 3, frames and contexts

`corpus-spec2-m3.md` §1 S1a, S1b, S4 (negative twin), S13, S14: frame exit, reparenting,
by-value spawn, conflicting and compatible accesses across contexts (WC4 C4–C8; Spec 1 §43, §50,
§60–§62, §66, §67, §72, §73). One theorem per verdict, written from `corpus-spec2-m3.md`;
preconditions checked by `decide`. The positive case of S4 is
`Ern.Concurrency.Traces.s4_trace`, `s4_detached_child` and
`Ern.Concurrency.RealizeWitness.s4_realized`.
-/

namespace Ern.Concurrency.Corpus

open Ern.MemoryModel.Access Ern.MemoryModel.Access.Examples Ern.Concurrency

/-- The contract of this module: no `SharedMutable` leaf. -/
abbrev KF : K := KC []

/-! ## S1a (`corpus-spec2-m3.md` §1 S1a) -/

/-- No static (Spec 1 §47). -/
def nost : Statics := []

/-- Initial state: the base frame 0 alone. -/
def p0 : SC := SC.ofS3 (S3.init nost)
/-- `c0 : enterFrame f1` with the local `X` (place 0, root authority 0): frame 1 (O6). -/
def p1 : SC := enterEffC p0 0 [] [(none, 0)]
/-- `X` becomes `Init` (O10 via `root_X`). -/
def p2 : SC := p1.set (write3Eff (p1.view 0) [0])
/-- `a := derive(root_X, Modify)`, authority 1, held by frame 1 (O1). -/
def p3 : SC := p2.set (deriveEff (p2.view 0) 0 [0] .modify)
/-- `spawn c1` yielding `a` (WC4 C4): context 1, initial frame 2, parent frame 1. -/
def p4 : SC := spawnEff p3 0 [1] []

/-- The setup of S1a: `enterFrame f1` with `X`, `write3(X)`, `derive`, `spawn c1` yielding `a`. -/
theorem s1a_setup : opStepC KF (.enter [] [(none, 0)]) 0 p0 (.ok p1) ∧
    opStepC KF (.write 0 [0]) 0 p1 (.ok p2) ∧ opStepC KF (.derive 0 [0] .modify) 0 p2 (.ok p3) ∧
    SpawnStep p3 0 [1] [] (.ok p4) :=
  ⟨⟨by decide, .ok (by decide)⟩, ⟨by decide, _, .ok (by decide), rfl⟩,
    ⟨by decide, _, .ok (by decide), rfl⟩, ⟨by decide, .ok (by decide)⟩⟩

/-- `corpus-spec2-m3.md` §1 S1a, `reject` (O7.2: an active authority is attached to a dying local;
WC4 C6): `exitFrameC(f1)` by context 0 while context 1 holds `a`; the surviving `a` has no
surviving origin (§73.4). -/
theorem S1a_1_reject : opStepC KF .exit 0 p4 .reject ∧
    firstSurv (p4.view 0) (p4.view 0).F.tail ((p4.view 0).ancs 1) = none :=
  ⟨⟨by decide, .reject (by decide)⟩, by decide⟩

/-- `c1 : release(a)` (O3). -/
def p5 : SC := p4.set (releaseEff (p4.view 1) 1)
/-- `c1 : terminate` (WC4 C7). -/
def p6 : SC := termEffC p5 1
/-- `c0 : exitFrameC(f1)` (O7, WC4 C6). -/
def p7 : SC := exitEffC p6 0

/-- `corpus-spec2-m3.md` §1 S1a, positive twin, `ok`: `c1 : release(a)` (O3); `c1 : terminate`;
`c0 : join(c1)` (WC4 C8); `c0 : exitFrameC(f1)`. -/
theorem S1a_2_ok : opStepC KF (.release 1) 1 p4 (.ok p5) ∧ TermStep KF p5 1 (.ok p6) ∧
    JoinStep p6 0 1 (.ok p6) ∧ opStepC KF .exit 0 p6 (.ok p7) :=
  ⟨⟨by decide, _, .ok (by decide), rfl⟩, ⟨by decide, .ok (by decide)⟩,
    .ok (by decide) (by decide), ⟨by decide, .ok (by decide)⟩⟩

/-! ## S1b (`corpus-spec2-m3.md` §1 S1b) -/

/-- Statics (Spec 1 §47): `0` the local `Y` of the base frame, `Init`; root authority `0`. -/
def yst : Statics := [((none, none, 0), true)]

/-- Initial state of S1b. -/
def b0 : SC := SC.ofS3 (S3.init yst)
/-- `q := derive(root_Y, Modify)`, authority 1 (O1). -/
def b1 : SC := b0.set (deriveEff (b0.view 0) 0 [0] .modify)
/-- `enterFrame f1` yielding `q` (O6): frame 1. -/
def b2 : SC := enterEffC b1 0 [1] []
/-- In `f1`: `a := derive(q, Modify)`, authority 2 (O1). -/
def b3 : SC := b2.set (deriveEff (b2.view 0) 1 [0] .modify)
/-- `spawn c1` yielding `a` (WC4 C4): context 1, initial frame 2, parent frame 1. -/
def b4 : SC := spawnEff b3 0 [2] []
/-- `c0 : exitFrameC(f1)` (O7, WC4 C6). -/
def b5 : SC := exitEffC b4 0

/-- `corpus-spec2-m3.md` §1 S1b, `ok` (O7.4: `q` is released, `a` survives and is reanchored on
`root_Y`; O7.5: the effective anchor is in frame 0, ancestor of the initial frame of context 1
after its reparenting on frame 0, WC4 C6.3): `exitFrameC(f1)` by context 0. -/
theorem S1b_1_ok : opStepC KF (.derive 0 [0] .modify) 0 b0 (.ok b1) ∧
    opStepC KF (.enter [1] []) 0 b1 (.ok b2) ∧ opStepC KF (.derive 1 [0] .modify) 0 b2 (.ok b3) ∧
    SpawnStep b3 0 [2] [] (.ok b4) ∧ opStepC KF .exit 0 b4 (.ok b5) ∧
    ¬ b5.flat.Active 1 ∧ b5.flat.org 2 = some 0 ∧ b5.ctxParent 1 = some 0 ∧
    b5.ancestorC 0 2 :=
  ⟨⟨by decide, _, .ok (by decide), rfl⟩, ⟨by decide, .ok (by decide)⟩,
    ⟨by decide, _, .ok (by decide), rfl⟩, ⟨by decide, .ok (by decide)⟩,
    ⟨by decide, .ok (by decide)⟩, by decide, by decide, by decide, by decide⟩

/-- `corpus-spec2-m3.md` §1 S1b, `reject` (Spec 1 §43.3: an active `Modify` descendant): after the
exit, `write3(Y)` via `root_Y` by context 0. The negative twin of S1b is S1a. -/
theorem S1b_2_reject : opStepC KF (.write 0 [0]) 0 b5 .reject :=
  ⟨by decide, _, .reject (by decide), rfl⟩

/-! ## S4, negative twin (`corpus-spec2-m3.md` §1 S4) -/

open Ern.Concurrency.Traces in
/-- `a := derive(root_p, Modify)` by context 0 in frame 1 of S4, authority 4 (O1). -/
def q4a : SC := Traces.q4.set (deriveEff (Traces.q4.view 0) 2 [2] .modify)

open Ern.Concurrency.Traces in
/-- The by-value composite of S4 yielding also `a` (WC4 C5). -/
def q5a : SC := spawnValEff q4a 0 [4] [(none, 0)] [(1, 4)]

/-- `corpus-spec2-m3.md` §1 S4, negative twin, `reject` (O7.2, as S1a): the composite of S4
yielding also `a := derive(root_p, Modify)` is `ok`, then `exitFrameC(f1)` by context 0 is
rejected, `a` surviving in context 1 without a surviving origin. The positive case is
`Ern.Concurrency.Traces.s4_trace`. -/
theorem S4_2_reject : opStepC K0 (.derive 2 [2] .modify) 0 Traces.q4 (.ok q4a) ∧
    SpawnValStep K0 q4a 0 [4] [(none, 0)] [(1, 4)] (.ok q5a) ∧ opStepC K0 .exit 0 q5a .reject :=
  ⟨⟨by decide, _, .ok (by decide), rfl⟩, ⟨by decide, .ok (by decide)⟩,
    ⟨by decide, .reject (by decide)⟩⟩

/-! ## S13 (`corpus-spec2-m3.md` §1 S13) -/

/-- Statics (Spec 1 §47): `0` the local `X` of the base frame, with the leaves `1` (`left`) and `2`
(`right`), `Init`; root authority `0`. -/
def xst : Statics :=
  [((none, none, 0), false), ((some 0, none, 0), true), ((some 0, none, 0), true)]

/-- Initial state of S13. -/
def t0 : SC := SC.ofS3 (S3.init xst)
/-- `a := derive(root_X, Modify)`, authority 1 (O1). -/
def t1 : SC := t0.set (deriveEff (t0.view 0) 0 [1, 2] .modify)
/-- `spawn c1` yielding `a` (WC4 C4): context 1, initial frame 1. -/
def t2 : SC := spawnEff t1 0 [1] []

/-- `corpus-spec2-m3.md` §1 S13, `reject` (O10.1: no effective mode, Spec 1 §43.3): after
`spawn c1` yielding `a := derive(root_X, Modify)`, `write3(X)` via `root_X` by context 0. -/
theorem S13_1_reject : opStepC KF (.derive 0 [1, 2] .modify) 0 t0 (.ok t1) ∧
    SpawnStep t1 0 [1] [] (.ok t2) ∧ opStepC KF (.write 0 [1, 2]) 0 t2 .reject :=
  ⟨⟨by decide, _, .ok (by decide), rfl⟩, ⟨by decide, .ok (by decide)⟩,
    ⟨by decide, _, .reject (by decide), rfl⟩⟩

/-- `c1 : release(a)` (O3). -/
def t3 : SC := t2.set (releaseEff (t2.view 1) 1)
/-- `c1 : terminate` (WC4 C7). -/
def t4 : SC := termEffC t3 1
/-- `c0 : write3(X)` via `root_X` (O10). -/
def t5 : SC := t4.set (write3Eff (t4.view 0) [1, 2])

/-- `corpus-spec2-m3.md` §1 S13, twin (a), `ok` (Spec 1 §32): `c1 : release(a)`, `terminate`;
`c0 : join(c1)`; `write3(X)` via `root_X`. -/
theorem S13_2_ok : opStepC KF (.release 1) 1 t2 (.ok t3) ∧ TermStep KF t3 1 (.ok t4) ∧
    JoinStep t4 0 1 (.ok t4) ∧ opStepC KF (.write 0 [1, 2]) 0 t4 (.ok t5) :=
  ⟨⟨by decide, _, .ok (by decide), rfl⟩, ⟨by decide, .ok (by decide)⟩,
    .ok (by decide) (by decide), ⟨by decide, _, .ok (by decide), rfl⟩⟩

/-- `split(root_X, [left], [right])`: `a1`, authority 1, and `a2`, authority 2 (O2). -/
def u1 : SC := t0.set (splitEff (t0.view 0) 0 [[1], [2]])
/-- `spawn c1` yielding `a1` (WC4 C4). -/
def u2 : SC := spawnEff u1 0 [1] []
/-- `c0 : write3(right)` via `a2` (O10). -/
def u3 : SC := u2.set (write3Eff (u2.view 0) [2])

/-- `corpus-spec2-m3.md` §1 S13, twin (b), `ok` (O2, structural disjointness; Spec 1 §23, §85):
`split(root_X, [left], [right])`, `spawn c1` yielding `a1`, then `write3(right)` via `a2` by
context 0. -/
theorem S13_3_ok : opStepC KF (.split 0 [[1], [2]]) 0 t0 (.ok u1) ∧ SpawnStep u1 0 [1] [] (.ok u2) ∧
    opStepC KF (.write 2 [2]) 0 u2 (.ok u3) :=
  ⟨⟨by decide, _, .ok (by decide), rfl⟩, ⟨by decide, .ok (by decide)⟩,
    ⟨by decide, _, .ok (by decide), rfl⟩⟩

/-! ## S14 (`corpus-spec2-m3.md` §1 S14) -/

/-- Initial state of S14: the local `X` (place 0), `Init`, root authority 0 (statics of S1b). -/
def v0 : SC := SC.ofS3 (S3.init yst)
/-- `o1 := derive(root_X, Observe)`, authority 1 (O1). -/
def v1 : SC := v0.set (deriveEff (v0.view 0) 0 [0] .observe)
/-- `o2 := derive(root_X, Observe)`, authority 2 (O1). -/
def v2 : SC := v1.set (deriveEff (v1.view 0) 0 [0] .observe)
/-- `spawn c1` yielding `o1` (WC4 C4): context 1, initial frame 1. -/
def v3 : SC := spawnEff v2 0 [1] []

/-- The setup of S14. -/
theorem s14_setup : opStepC KF (.derive 0 [0] .observe) 0 v0 (.ok v1) ∧
    opStepC KF (.derive 0 [0] .observe) 0 v1 (.ok v2) ∧ SpawnStep v2 0 [1] [] (.ok v3) :=
  ⟨⟨by decide, _, .ok (by decide), rfl⟩, ⟨by decide, _, .ok (by decide), rfl⟩,
    ⟨by decide, .ok (by decide)⟩⟩

/-- `corpus-spec2-m3.md` §1 S14, step 1, `ok` (O9, Spec 1 §21, §50): `read3(X)` via `o2` by
context 0. -/
theorem S14_1_ok : opStepC KF (.read 2 [0]) 0 v3 (.ok (v3.set (v3.view 0))) :=
  ⟨by decide, _, .ok (by decide), rfl⟩

/-- `corpus-spec2-m3.md` §1 S14, step 2, `ok` (O9, Spec 1 §21, §50): `read3(X)` via `o1` by
context 1. -/
theorem S14_2_ok : opStepC KF (.read 1 [0]) 1 v3 (.ok (v3.set (v3.view 1))) :=
  ⟨by decide, _, .ok (by decide), rfl⟩

/-- `corpus-spec2-m3.md` §1 S14, negative twin, `reject` (O1.2: the effective mode of `root_X` is
reduced to `Observe`, Spec 1 §43.4; O1.3, I1): `derive(root_X, Modify)` by context 0 while `o1` is
active. -/
theorem S14_3_reject : opStepC KF (.derive 0 [0] .modify) 0 v3 .reject ∧
    effective v3.flat 0 0 = some .observe :=
  ⟨⟨by decide, _, .reject (by decide), rfl⟩, by decide⟩

end Ern.Concurrency.Corpus
