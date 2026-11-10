import Ern.Concurrency.Realize

/-!
# Corpus of milestone 3, block MX

`corpus-spec2-m3.md` §0 block MX, §1 S2, S5, S7, S8, S9, S11, S12, S15, §2 W-C22.2.

States of the reference mutex of `corpus-spec2-m3.md` §0, block MX, built by labelled steps from
the initial state of Spec 1 §47, and one theorem per verdict of the cases of §1 on these states
(named `S<case>_<n>_<ok|reject|fail|wait|encap>`, twins in this module). Verdicts are written from
`corpus-spec2-m3.md`; preconditions are checked by `decide`. Verdict encodings (§4 of the corpus):
`ok` and `reject` are outcomes of the step relation; `non habilité` (`wait`) is the absence of an
`ok` outcome of a library operation that defines only `ok` (`∀ st', ¬ Op … st'`); for `unlock` and
`resetLock`, which also define only `ok` (WC4 C17, C18), `reject` is the absence of an `ok`
outcome together with the failing clause named by the corpus.

Contract: `KC [lock]`, the test contract of `Ern.MemoryModel.Access.Examples.K0` except that only
the controller leaves are `K.SharedMutable` (`corpus-spec2-m3.md` §0: `K.SharedMutable lock`; §1
S5a: `T` not `SharedMutable`).
-/

namespace Ern.Concurrency.Corpus

open Ern.MemoryModel.Access Ern.MemoryModel.Access.Examples Ern.Concurrency
open Ern.Concurrency.Traces (L0)

/-! ## Contract -/

/-- Test contract of the corpus (Spec 1 §48): no declared disjointness, the leaves of `sm` are
`SharedMutable`, nothing statically pinned, every external use done, every place deallocable,
every deallocation compatible, every allocation satisfiable. -/
def KC (sm : List Nat) : K :=
  ⟨fun _ _ => False, fun l => l ∈ sm, fun _ => False, fun _ => True, fun _ => True,
    fun _ _ => True, fun _ _ _ => True⟩

instance (sm : List Nat) : ∀ r r', Decidable ((KC sm).DeclaredDisjoint r r') :=
  fun _ _ => inferInstanceAs (Decidable False)
instance (sm : List Nat) : DecidablePred (KC sm).SharedMutable :=
  fun l => inferInstanceAs (Decidable (l ∈ sm))
instance (sm : List Nat) : DecidablePred (KC sm).Pinned :=
  fun _ => inferInstanceAs (Decidable False)
instance (sm : List Nat) : DecidablePred (KC sm).ExternalDone :=
  fun _ => inferInstanceAs (Decidable True)
instance (sm : List Nat) : DecidablePred (KC sm).Deallocable :=
  fun _ => inferInstanceAs (Decidable True)
instance (sm : List Nat) : ∀ p a, Decidable ((KC sm).FreeCompat p a) :=
  fun _ _ => inferInstanceAs (Decidable True)
instance (sm : List Nat) : ∀ p ls s, Decidable ((KC sm).Satisfiable p ls s) :=
  fun _ _ _ => inferInstanceAs (Decidable True)

/-- `DDSound` of the corpus contract (Spec 1 §80): nothing is declared disjoint. -/
theorem ddKC (sm : List Nat) : DDSound (KC sm) := fun _ _ h => h.elim

/-! ## Block MX (`corpus-spec2-m3.md` §0) -/

/-- Statics (Spec 1 §47): `0` the mutex value `M`, `1` its field `slot` (`Uninit`), `2` its field
`lock` (`Init`), `3` the protected root `T` (`Init`), owned by `M`; `4` the mutex-shaped value `M′`
with fields `5` (`slot′`) and `6` (`lock′`), `Uninit`. Root authorities: `0` of `M` (frame 0), `1`
of `T` (held by `M`), `2` of `M′` (frame 0). -/
def mxst : Statics :=
  [((none, none, 0), false), ((some 0, none, 0), false), ((some 0, none, 0), true),
   ((none, some 0, 0), true), ((none, none, 0), false), ((some 4, none, 0), false),
   ((some 4, none, 0), false)]

/-- The statics are well formed (Spec 1 §47). -/
theorem mxst_ok : StaticsOK mxst := by decide

/-- The corpus contract of block MX: `lock` (place 2) is the only `SharedMutable` leaf. -/
abbrev KM : K := KC [2]

/-- Initial single-context state (Spec 1 §47). -/
def x0 : SC := SC.ofS3 (S3.init mxst)
/-- MX step 1: `guarded := derive(root_T, Modify, footprint(T))`, authority 3 (O1). -/
def x1 : SC := x0.set (deriveEff (x0.view 0) 1 [3] .modify)
/-- MX step 2: `store(guarded, slot)` (O8); `slot` becomes `Init`. -/
def x2 : SC := storeEffC x1 0 3 1
/-- MX step 3: the registry after `newMutex(guarded)`, entry `e` (WC4 C13). -/
def regX : SyncReg := [⟨3, none⟩]
/-- MX step 4: `o1 := derive(root_M, Observe, {slot, lock})`, authority 4 (O1). -/
def x3 : SC := x2.set (deriveEff (x2.view 0) 0 [1, 2] .observe)
/-- MX step 4: `spawn c1` yielding `o1` (WC4 C4): context 1, initial frame 1, parent frame 0. -/
def x4 : SC := spawnEff x3 0 [4] []

/-- The steps of block MX (`corpus-spec2-m3.md` §0): each is an `ok` step; `ControlOf(e)` is
`lock`. -/
theorem mx_steps : opStepC KM (.derive 1 [3] .modify) 0 x0 (.ok x1) ∧
    opStepC KM (.store 3 1) 0 x1 (.ok x2) ∧ NewMutexOk KM L0 [] x2 [] 0 3 (x2, regX) ∧
    ControlOf L0 x2 ⟨3, none⟩ = some 2 ∧
    opStepC KM (.derive 0 [1, 2] .observe) 0 x2 (.ok x3) ∧ SpawnStep x3 0 [4] [] (.ok x4) :=
  ⟨⟨by decide, _, .ok (by decide), rfl⟩, ⟨by decide, .ok (by decide)⟩, ⟨by decide, by decide, rfl⟩,
    by decide, ⟨by decide, _, .ok (by decide), rfl⟩, ⟨by decide, .ok (by decide)⟩⟩

/-- `MX₃` (`corpus-spec2-m3.md` §0) is reached from the initial state by an `EncapsulatedTrace`
(WC4 C22, C23). -/
theorem mx3_trace : EncapsulatedTrace KM L0 (x0, [], [])
    [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 3 1), .newMutex 0 3] (x2, regX, []) :=
  .cons (fun e he => by cases he) (.kernel mx_steps.1) <|
  .cons trivial (.kernel mx_steps.2.1) <| .cons trivial (.newMutex mx_steps.2.2.1) .nil

/-- `MX₄` (`corpus-spec2-m3.md` §0) is reached from the initial state by an `EncapsulatedTrace`
(WC4 C22, C23). -/
theorem mx4_trace : EncapsulatedTrace KM L0 (x0, [], [])
    [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 3 1), .newMutex 0 3,
     .kernel 0 (.derive 0 [1, 2] .observe), .spawn 0 [4] []] (x4, regX, []) :=
  .cons (fun e he => by cases he) (.kernel mx_steps.1) <|
  .cons trivial (.kernel mx_steps.2.1) <| .cons trivial (.newMutex mx_steps.2.2.1) <|
  .cons (by decide : ∀ e ∈ regX, e.Live x2 → 0 ≠ e.guarded) (.kernel mx_steps.2.2.2.2.1) <|
  .cons trivial (.spawn mx_steps.2.2.2.2.2) .nil

/-- In `MX₄`, `root_M` has effective mode `Observe` on `slot` and `lock` (Spec 1 §43.4) and
`CtrlRight` holds for frame 0 and for the initial frame 1 of context 1 (`corpus-spec2-m3.md` §0,
step 4). -/
theorem mx4_facts : effective x4.flat 0 1 = some .observe ∧ effective x4.flat 0 2 = some .observe ∧
    CtrlRight L0 x4 ⟨3, none⟩ 0 ∧ CtrlRight L0 x4 ⟨3, none⟩ 1 := by decide

/-! ## S2 (`corpus-spec2-m3.md` §1 S2) -/

/-- `c1 : acquire(e)`: grant `g`, authority 5, held by frame 1 (WC4 C16). -/
def x5 : SC := deriveSyncEff x4 1 3
/-- The registry with the grant `g` recorded (WC4 C16). -/
def regG : SyncReg := [⟨3, some 5⟩]
/-- `c1 : write3(T)` via `g` (O10). -/
def x6 : SC := x5.set (write3Eff (x5.view 1) [3])
/-- `c1 : unlock(e)`: `g` released (O3, WC4 C17). -/
def x7 : SC := x6.set (releaseEff (x6.view 1) 5)

/-- `corpus-spec2-m3.md` §1 S2, step 1, `ok` (WC4 C16): from `MX₄`, `acquire(e)` by context 1. -/
theorem S2_1_ok : AcquireOk KM L0 x4 regX 1 0 (x5, regG) :=
  ⟨by decide, ⟨3, none⟩, rfl, by decide, by decide, rfl⟩

/-- `corpus-spec2-m3.md` §1 S2, step 2, `ok` (O10): `write3(T)` via `g` by context 1, whose current
frame holds `g` with effective mode `Modify`. -/
theorem S2_2_ok : opStepC KM (.write 5 [3]) 1 x5 (.ok x6) := ⟨by decide, _, .ok (by decide), rfl⟩

/-- `corpus-spec2-m3.md` §1 S2, step 3, `ok` (WC4 C17): `unlock(e)` by context 1. -/
theorem S2_3_ok : UnlockOk L0 x6 regG 1 0 (x7, regX) :=
  ⟨by decide, ⟨3, some 5⟩, 5, rfl, by decide, rfl, by decide, by decide, rfl⟩

/-- `corpus-spec2-m3.md` §1 S2, negative twin, `non habilité` (WC4 C14.2: `grant ≠ none`): while
`g` is active, `acquire(e)` by context 0 has no `ok` outcome. The other negative twin, two active
grants on `footprint(T)`, is excluded by `grants_exclusive` (T6). -/
theorem S2_4_wait : ∀ st', ¬ AcquireOk KM L0 x5 regG 0 0 st' := by
  rintro st' ⟨-, e, he, ⟨-, hg, -⟩, -⟩
  cases he; cases hg

/-- The steps of S2 continue the encapsulated trace of `MX₄` (WC4 C22, C23). -/
theorem s2_trace : EncapsulatedTrace KM L0 (x0, [], [])
    [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 3 1), .newMutex 0 3,
     .kernel 0 (.derive 0 [1, 2] .observe), .spawn 0 [4] [], .acquire 1 0,
     .kernel 1 (.write 5 [3]), .unlock 1 0] (x7, regX, []) := by
  have h := mx4_trace.snoc (lbl := .acquire 1 0) (st' := (x5, regG, [])) trivial (.acquire S2_1_ok)
  have h := h.snoc (lbl := .kernel 1 (.write 5 [3])) (st' := (x6, regG, [])) trivial
    (.kernel S2_2_ok)
  exact h.snoc (lbl := .unlock 1 0) (st' := (x7, regX, [])) trivial (.unlock S2_3_ok)

/-! ## S5 (`corpus-spec2-m3.md` §1 S5a, S5b) -/

/-- `corpus-spec2-m3.md` §1 S5a, `reject` (O11.1: `T` is not `SharedMutable`): from `MX₄` with
`g` held by context 1, `writeShared(T)` via `g`. Positive twin: `S2_2_ok`. -/
theorem S5a_1_reject : opStepC KM (.writeShared 5 [3]) 1 x5 .reject :=
  ⟨by decide, _, .reject (by decide), rfl⟩

/-- `c1 : writeShared(lock)` via `o1` (O11). -/
def x4w : SC := x4.set (write3Eff (x4.view 1) [2])

/-- `corpus-spec2-m3.md` §1 S5b, `ok noyau` (O11.1, O11.2), outside C22.4 and classed under OB-C05:
from `MX₄`, `writeShared(lock)` via `o1` by context 1 outside `acquire`/`unlock` is an `ok` kernel
step and `Encap` admits it (WC4 C22.4, the controller-write protocol, is a realization/interface
obligation not represented in `S_C`). Positive twin: `S2_1_ok`, `S2_3_ok`. -/
theorem S5b_1_ok : opStepC KM (.writeShared 4 [2]) 1 x4 (.ok x4w) ∧
    Encap L0 (x4, regX) (.kernel 1 (.writeShared 4 [2])) :=
  ⟨⟨by decide, _, .ok (by decide), rfl⟩, trivial⟩

/-! ## S7, negative twin (`corpus-spec2-m3.md` §1 S7) -/

/-- `corpus-spec2-m3.md` §1 S7, negative twin, `reject` (Spec 1 §63.1: frame 0 no longer has
effective `Modify` over `M`; §63.4): from `MX₄`, `transfer(M, M′)` by context 0. The positive
case is `Ern.Concurrency.EncapTraces.traceA`, `traceB`. -/
theorem S7_2_reject : opStepC KM (.transfer 0 4) 0 x4 .reject ∧
    ¬ HasRight (x4.view 0) .modify 0 ∧
    ¬ ∃ g ∈ List.range (x4.view 0).A.length, Grounds (x4.view 0) .modify 0 g ∧
      ∀ j ∈ List.range (x4.view 0).A.length, ActiveDerivedOutside (x4.view 0) 0 j →
        RightChain (x4.view 0) g j :=
  ⟨⟨by decide, .reject (by decide)⟩, by decide, by decide⟩

/-! ## S8 (`corpus-spec2-m3.md` §1 S8) -/

/-- `c1 : enterFrame f2` without yielding `g` (O6): frame 2. -/
def x8 : SC := enterEffC x5 1 [] []

/-- `corpus-spec2-m3.md` §1 S8, `reject` (Spec 1 §43: `g` is held by the initial frame 1 of
context 1, neither the current frame nor a place): after `enterFrame f2`, `write3(T)` via `g`. -/
theorem S8_1_reject : opStepC KM (.enter [] []) 1 x5 (.ok x8) ∧
    opStepC KM (.write 5 [3]) 1 x8 .reject :=
  ⟨⟨by decide, .ok (by decide)⟩, ⟨by decide, _, .reject (by decide), rfl⟩⟩

/-- `c1 : g′ := derive(g, Modify)`, authority 6 (O1). -/
def x9 : SC := x5.set (deriveEff (x5.view 1) 5 [3] .modify)
/-- `c1 : enterFrame f2` yielding `g′` (O6): frame 2. -/
def x10 : SC := enterEffC x9 1 [6] []
/-- `f2 : write3(T)` via `g′` (O10). -/
def x11 : SC := x10.set (write3Eff (x10.view 1) [3])

/-- `corpus-spec2-m3.md` §1 S8, positive twin, `ok`: `enterFrame f2` yielding `g′ := derive(g,
Modify)`, then `write3(T)` via `g′`. -/
theorem S8_2_ok : opStepC KM (.derive 5 [3] .modify) 1 x5 (.ok x9) ∧
    opStepC KM (.enter [6] []) 1 x9 (.ok x10) ∧ opStepC KM (.write 6 [3]) 1 x10 (.ok x11) :=
  ⟨⟨by decide, _, .ok (by decide), rfl⟩, ⟨by decide, .ok (by decide)⟩,
    ⟨by decide, _, .ok (by decide), rfl⟩⟩

/-! ## S15 (`corpus-spec2-m3.md` §1 S15) -/

/-- `c1 : enterFrame f2` yielding the whole grant `g` (O6): frame 2. -/
def z1 : SC := enterEffC x5 1 [5] []
/-- `f2 : write3(T)` via `g` (O10). -/
def z2 : SC := z1.set (write3Eff (z1.view 1) [3])
/-- `exitFrameC(f2)` (O7, WC4 C6): `g` is released. -/
def z3 : SC := exitEffC z2 1

/-- `corpus-spec2-m3.md` §1 S15, steps 1–3, `ok`, `ok`, `ok` (O6, O10, O7: `exitFrameC` releases
`g`, which is not returned, Spec 1 §45). -/
theorem S15_1_ok : opStepC KM (.enter [5] []) 1 x5 (.ok z1) ∧
    opStepC KM (.write 5 [3]) 1 z1 (.ok z2) ∧ opStepC KM .exit 1 z2 (.ok z3) ∧
    ¬ z3.flat.Active 5 :=
  ⟨⟨by decide, .ok (by decide)⟩, ⟨by decide, _, .ok (by decide), rfl⟩, ⟨by decide, .ok (by decide)⟩,
    by decide⟩

/-- `corpus-spec2-m3.md` §1 S15, step 4, `reject` (WC4 C17.2: `g` is inactive): `unlock(e)` by
context 1 has no `ok` outcome, the recorded grant being inactive (the leaked-lock state of
S11). -/
theorem S15_4_reject : (∀ st', ¬ UnlockOk L0 z3 regG 1 0 st') ∧ ¬ z3.flat.Active 5 := by
  refine ⟨?_, by decide⟩
  rintro st' ⟨-, e, g, he, -, hg, hrel, -⟩
  cases he; cases hg
  exact (by decide : ¬ ReleasePre (z3.view 1) 5) hrel

/-- `exitFrameC(f2)` after `write3(T)` via `g′` (O7): `g′` is released. -/
def x12 : SC := exitEffC x11 1
/-- `c1 : unlock(e)` (WC4 C17). -/
def x13 : SC := x12.set (releaseEff (x12.view 1) 5)

/-- `corpus-spec2-m3.md` §1 S15, positive twin, `ok`: after `write3(T)` via `g′` (`S8_2_ok`),
`exitFrameC(f2)` releases `g′`, and `unlock(e)` succeeds (`g` active, without descendant). -/
theorem S15_5_ok : opStepC KM .exit 1 x11 (.ok x12) ∧ ¬ x12.flat.Active 6 ∧
    UnlockOk L0 x12 regG 1 0 (x13, regX) :=
  ⟨⟨by decide, .ok (by decide)⟩, by decide,
    ⟨by decide, ⟨3, some 5⟩, 5, rfl, by decide, rfl, by decide, by decide, rfl⟩⟩

/-! ## S11 (`corpus-spec2-m3.md` §1 S11) -/

/-- `c1 : enterFrame f1′` without parameter (O6): frame 2. -/
def y0 : SC := enterEffC x4 1 [] []

/-- `corpus-spec2-m3.md` §1 S11, setup without the cession of `o1′` ("sans elle C14.3/§68.2
échoue et `acquire` n'est pas habilité"): after `enterFrame f1′` without parameter, frame 2 holds
no authority over `lock`, so WC4 C14.3 (`CtrlRight`) fails and `acquire(e)` by context 1 has no
`ok` outcome. The cases below follow the corpus setup, which yields `o1′ := derive(o1, Observe)`
to `f1′` (`y1`, `y1'`; Spec 1 §45). -/
theorem S11_setup_wait : opStepC KM (.enter [] []) 1 x4 (.ok y0) ∧ ¬ CtrlRight L0 y0 ⟨3, none⟩ 2 ∧
    ∀ st', ¬ AcquireOk KM L0 y0 regX 1 0 st' := by
  refine ⟨⟨by decide, .ok (by decide)⟩, by decide, ?_⟩
  rintro st' ⟨-, e, he, hauth, -⟩
  cases he; exact (by decide : ¬ EntryAuth L0 y0 ⟨3, none⟩ (y0.view 1).top) hauth

/-- `c1 : o1′ := derive(o1, Observe, {slot, lock})`, authority 5 (O1). -/
def y1 : SC := x4.set (deriveEff (x4.view 1) 4 [1, 2] .observe)
/-- `c1 : enterFrame f1′` yielding `o1′` (O6): frame 2. -/
def y1' : SC := enterEffC y1 1 [5] []
/-- `c1 : acquire(e)`: `g`, authority 6, held by frame 2 (WC4 C16). -/
def y2 : SC := deriveSyncEff y1' 1 3
/-- The registry with the grant `g` = 6 recorded (WC4 C16). -/
def regG6 : SyncReg := [⟨3, some 6⟩]
/-- `c1 : exitFrameC(f1′)` without `unlock` (O7). -/
def y3 : SC := exitEffC y2 1

/-- `corpus-spec2-m3.md` §1 S11, step 1, `ok` (O7 releases `g` and `o1′`; `o1` stays active):
from `MX₄`, after `enterFrame f1′` yielding `o1′ := derive(o1, Observe)` and `acquire(e)` by
context 1, `exitFrameC(f1′)` without `unlock`; `g` is inactive and the registry still records
it. -/
theorem S11_1_ok : opStepC KM (.derive 4 [1, 2] .observe) 1 x4 (.ok y1) ∧
    opStepC KM (.enter [5] []) 1 y1 (.ok y1') ∧ AcquireOk KM L0 y1' regX 1 0 (y2, regG6) ∧
    opStepC KM .exit 1 y2 (.ok y3) ∧ ¬ y3.flat.Active 6 :=
  ⟨⟨by decide, _, .ok (by decide), rfl⟩, ⟨by decide, .ok (by decide)⟩,
    ⟨by decide, ⟨3, none⟩, rfl, by decide, by decide, rfl⟩, ⟨by decide, .ok (by decide)⟩,
    by decide⟩

/-- `corpus-spec2-m3.md` §1 S11, step 2, `non habilité` (WC4 C14.2: `grant = some g`, `g`
inactive): `acquire(e)` by context 0. -/
theorem S11_2_wait : ∀ st', ¬ AcquireOk KM L0 y3 regG6 0 0 st' := by
  rintro st' ⟨-, e, he, ⟨-, hg, -⟩, -⟩
  cases he; cases hg

/-- `corpus-spec2-m3.md` §1 S11, step 3, `reject` (WC4 C18.1: `ExercisableAt(guarded, Modify)`
needs `Modify` over `M`, and `root_M` has only `Observe` effective while `o1` is active):
`resetLock(e)` by context 0 has no `ok` outcome. -/
theorem S11_3_reject : (∀ st', ¬ ResetLockOk L0 y3 regG6 0 0 st') ∧
    ¬ (y3.view 0).ExercisableAt 3 .modify := by
  refine ⟨?_, by decide⟩
  rintro st' ⟨-, e, he, hex, -⟩
  cases he
  exact (by decide : ¬ (y3.view 0).ExercisableAt 3 .modify) hex

/-- `c1 : terminate` (WC4 C7). -/
def y4 : SC := termEffC y3 1
/-- `c0 : acquire(e)` after `resetLock(e)`: grant authority 7, held by frame 0 (WC4 C16). -/
def y5 : SC := deriveSyncEff y4 0 3

/-- `corpus-spec2-m3.md` §1 S11, positive twin, `ok`: `c1 : terminate`; `c0 : join(c1)`;
`resetLock(e)` (`root_M` has effective `Modify` again); `acquire(e)`. -/
theorem S11_4_ok : TermStep KM y3 1 (.ok y4) ∧ JoinStep y4 0 1 (.ok y4) ∧
    ResetLockOk L0 y4 regG6 0 0 (y4, regX) ∧ AcquireOk KM L0 y4 regX 0 0 (y5, [⟨3, some 7⟩]) :=
  ⟨⟨by decide, .ok (by decide)⟩, .ok (by decide) (by decide),
    ⟨by decide, ⟨3, some 6⟩, rfl, by decide, by decide, by decide, rfl⟩,
    ⟨by decide, ⟨3, none⟩, rfl, by decide, by decide, rfl⟩⟩

/-! ## S12 (`corpus-spec2-m3.md` §1 S12) -/

/-- `c0 : write3(lock)` via `root_M` (O10). -/
def x2w : SC := x2.set (write3Eff (x2.view 0) [2])

/-- `corpus-spec2-m3.md` §1 S12, `ok noyau` (O10), outside C22.4 and classed under OB-C05: from
`MX₃`, `write3(lock)` via `root_M` by context 0 is an `ok` kernel step and `Encap` admits it (WC4
C22.4 is a realization/interface obligation not represented in `S_C`). -/
theorem S12_1_ok : opStepC KM (.write 0 [2]) 0 x2 (.ok x2w) ∧
    Encap L0 (x2, regX) (.kernel 0 (.write 0 [2])) :=
  ⟨⟨by decide, _, .ok (by decide), rfl⟩, trivial⟩

/-- `c0 : acquire(e)` in `MX₃`: grant authority 4, held by frame 0 (WC4 C16). -/
def x2a : SC := deriveSyncEff x2 0 3
/-- `c0 : unlock(e)` (WC4 C17). -/
def x2u : SC := x2a.set (releaseEff (x2a.view 0) 4)

/-- `corpus-spec2-m3.md` §1 S12, twin, `ok`: in `MX₃`, `acquire(e)` then `unlock(e)` by context 0,
the operations of the protocol. -/
theorem S12_2_ok : AcquireOk KM L0 x2 regX 0 0 (x2a, [⟨3, some 4⟩]) ∧
    UnlockOk L0 x2a [⟨3, some 4⟩] 0 0 (x2u, regX) :=
  ⟨⟨by decide, ⟨3, none⟩, rfl, by decide, by decide, rfl⟩,
    ⟨by decide, ⟨3, some 4⟩, 4, rfl, by decide, rfl, by decide, by decide, rfl⟩⟩

/-! ## W-C22.2 (`corpus-spec2-m3.md` §2) -/

/-- `corpus-spec2-m3.md` §2 W-C22.2, `ok noyau / hors C22.2`: from `MX₄`, context 1 outside
`acquire` takes the raw `deriveSync(guarded)` step under the library instantiation (the facts
C14.1–C14.3 hold); `Encap` excludes it (WC4 C22.2). After the step the registry still records
`grant = none` while an active descendant covers `T`: `GrantDiscipline` fails, and `acquire(e)` is
enabled for neither context while the derivative is active (WC4 C13.9, C14: blocking
descendant); it is enabled again after its ordinary `release` (`W_C22_2_reenable`). Positive twin:
`S2_1_ok`. -/
theorem W_C22_2_encap : DeriveSyncStep (libKC KM L0) regX x4 1 3 (.ok x5) ∧
    ¬ Encap L0 (x4, regX) (.deriveSync 1 3) ∧ ¬ GrantDiscipline x5 regX ∧
    ∀ st', ¬ AcquireOk KM L0 x5 regX 0 0 st' ∧ ¬ AcquireOk KM L0 x5 regX 1 0 st' := by
  refine ⟨⟨by decide, .ok (by decide)⟩, fun h => h ⟨3, none⟩ (by decide) (by decide) rfl,
    fun h => (by decide : ¬ NoCoveringDesc x5 3) (h ⟨3, none⟩ (by decide) (by decide) rfl),
    fun st' => ⟨?_, ?_⟩⟩
  · rintro ⟨-, e, he, -, hpre, -⟩
    cases he; exact (by decide : ¬ DeriveSyncPre (libKC KM L0) regX x5 0 3) hpre
  · rintro ⟨-, e, he, -, hpre, -⟩
    cases he; exact (by decide : ¬ DeriveSyncPre (libKC KM L0) regX x5 1 3) hpre

/-- `c1 : release(g)` of the raw grant of W-C22.2 (O3). -/
def x5r : SC := x5.set (releaseEff (x5.view 1) 5)

/-- `corpus-spec2-m3.md` §2 W-C22.2, `acquire(e)` "de nouveau habilitée après son `release`
ordinaire": after the raw `deriveSync` of `W_C22_2_encap`, context 1 releases the derivative by an
ordinary `release` (O3), an `ok` step that `Encap` admits (WC4 C15 effect: the derivative "is
ordinary after creation … for its … legal release"); `GrantDiscipline` holds again and
`acquire(e)` by context 1 is enabled. -/
theorem W_C22_2_reenable : opStepC KM (.release 5) 1 x5 (.ok x5r) ∧
    Encap L0 (x5, regX) (.kernel 1 (.release 5)) ∧ GrantDiscipline x5r regX ∧
    AcquireOk KM L0 x5r regX 1 0 (deriveSyncEff x5r 1 3, [⟨3, some 6⟩]) :=
  ⟨⟨by decide, _, .ok (by decide), rfl⟩, trivial,
    fun e he _ _ => by rw [List.mem_singleton.1 he]; decide,
    ⟨by decide, ⟨3, none⟩, rfl, by decide, by decide, rfl⟩⟩

/-- `corpus-spec2-m3.md` §2 W-C22.2, "fondement renforcé de C22.2": the correct cycle `acquire(e)`
then `unlock(e)` by context 1 from `MX₄` reaches `(x5r, regX)`, the very state and registry
reached by the raw `deriveSync` of `W_C22_2_encap` followed by the `release` of
`W_C22_2_reenable`. The registry cannot tell the two histories apart afterwards. -/
theorem W_C22_2_cycle : AcquireOk KM L0 x4 regX 1 0 (x5, regG) ∧
    UnlockOk L0 x5 regG 1 0 (x5r, regX) :=
  ⟨S2_1_ok, ⟨by decide, ⟨3, some 5⟩, 5, rfl, by decide, rfl, by decide, by decide, rfl⟩⟩

/-! ## S9 (`corpus-spec2-m3.md` §1 S9) -/

/-- Statics (Spec 1 §47): two mutex values of the same type, each as in block MX: `0` `M1` with
fields `1` (`slot1`, `Uninit`) and `2` (`lock1`, `Init`), `3` `T1` (`Init`) owned by `M1`; `4`
`M2` with fields `5` (`slot2`) and `6` (`lock2`), `7` `T2` owned by `M2`. Root authorities: `0`
of `M1`, `1` of `T1` (held by `M1`), `2` of `M2`, `3` of `T2` (held by `M2`). -/
def s9st : Statics :=
  [((none, none, 0), false), ((some 0, none, 0), false), ((some 0, none, 0), true),
   ((none, some 0, 0), true), ((none, none, 0), false), ((some 4, none, 0), false),
   ((some 4, none, 0), true), ((none, some 4, 0), true)]

/-- The statics are well formed (Spec 1 §47). -/
theorem s9st_ok : StaticsOK s9st := by decide

/-- The contract of S9: the two controllers are `SharedMutable`. -/
abbrev K9 : K := KC [2, 6]

/-- Initial state of S9. -/
def n0 : SC := SC.ofS3 (S3.init s9st)
/-- `guarded1 := derive(root_T1, Modify, footprint(T1))`, authority 4. -/
def n1 : SC := n0.set (deriveEff (n0.view 0) 1 [3] .modify)
/-- `store(guarded1, slot1)`. -/
def n2 : SC := storeEffC n1 0 4 1
/-- `guarded2 := derive(root_T2, Modify, footprint(T2))`, authority 5. -/
def n3 : SC := n2.set (deriveEff (n2.view 0) 3 [7] .modify)
/-- `store(guarded2, slot2)`: both mutexes are in `MX₃`. -/
def n4 : SC := storeEffC n3 0 5 5
/-- The registry with the entries `e1` (`guarded1`) and `e2` (`guarded2`) (WC4 C13). -/
def reg9 : SyncReg := [⟨4, none⟩, ⟨5, none⟩]
/-- `c0 : acquire(e1)`: `g1`, authority 6 (WC4 C16). -/
def n5 : SC := deriveSyncEff n4 0 4
/-- `c0 : acquire(e2)`: `g2`, authority 7 (WC4 C16). -/
def n6 : SC := deriveSyncEff n5 0 5

/-- The construction of S9: both mutexes reach `MX₃` by an `EncapsulatedTrace` (WC4 C22, C23);
their controllers are distinct (WC4 C13.8). -/
theorem s9_trace : EncapsulatedTrace K9 L0 (n0, [], [])
    [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 4 1), .kernel 0 (.derive 3 [7] .modify),
     .kernel 0 (.store 5 5), .newMutex 0 4, .newMutex 0 5] (n4, reg9, []) ∧
    ControlOf L0 n4 ⟨4, none⟩ = some 2 ∧ ControlOf L0 n4 ⟨5, none⟩ = some 6 := by
  refine ⟨?_, by decide, by decide⟩
  have h1 : NewMutexOk K9 L0 [] n4 [] 0 4 (n4, [⟨4, none⟩]) := ⟨by decide, by decide, rfl⟩
  have h2 : NewMutexOk K9 L0 [] n4 [⟨4, none⟩] 0 5 (n4, reg9) := ⟨by decide, by decide, rfl⟩
  exact .cons (fun e he => by cases he) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons trivial (.kernel ⟨by decide, .ok (by decide)⟩) <|
    .cons (fun e he => by cases he) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons trivial (.kernel ⟨by decide, .ok (by decide)⟩) <|
    .cons trivial (.newMutex h1) <| .cons trivial (.newMutex h2) .nil

/-- `corpus-spec2-m3.md` §1 S9, step 1, `ok` (WC4 C16): `acquire(e1)` by context 0. Property:
`footprint(g1) = footprint(T1)` contains no leaf of `T2`, and `e2` still records
`grant = none`. -/
theorem S9_1_ok : AcquireOk K9 L0 n4 reg9 0 0 (n5, [⟨4, some 6⟩, ⟨5, none⟩]) ∧
    n5.flat.afp 6 = footprint n5.P 3 ∧ 7 ∉ n5.flat.afp 6 ∧
    ([⟨4, some 6⟩, ⟨5, none⟩] : SyncReg)[1]? = some ⟨5, none⟩ :=
  ⟨⟨by decide, ⟨4, none⟩, rfl, by decide, by decide, rfl⟩, by decide, by decide, rfl⟩

/-- `corpus-spec2-m3.md` §1 S9, step 2, `ok` (WC4 C13.8, C16): `acquire(e2)` by context 0, whose
controller is distinct. Property: `footprint(g2) = footprint(T2)`. Negative twin:
`Ern.Concurrency.Traces.shared_controller_rejected` (C13.8). -/
theorem S9_2_ok : AcquireOk K9 L0 n5 [⟨4, some 6⟩, ⟨5, none⟩] 0 1
      (n6, [⟨4, some 6⟩, ⟨5, some 7⟩]) ∧
    n6.flat.afp 7 = footprint n6.P 7 :=
  ⟨⟨by decide, ⟨5, none⟩, rfl, by decide, by decide, rfl⟩, by decide⟩

end Ern.Concurrency.Corpus
