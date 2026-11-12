import Ern.Concurrency.FullEncap.Protected
import Ern.Concurrency.Corpus.MutexEdgeStrict

/-!
# Witnesses W-AG, W-AG-J and W-AG′

`corpus-spec2-m3.md` v14 §2 terdecies: a grant abandoned by frame exit while a derivative of it
survives in another context. One theorem per expected fact, preconditions by `decide`; the
verdicts are written from the corpus. Contract `KM`, layout `L0`, from `MX₃`; the corpus step `k`
of W-AG is the label of index `k + 2` (`MX₃` takes three labels).

* W-AG: steps 1 to 7 are the trace of `protected_runFull_refuted`; steps 8 to 11 recover the mutex
  without `join`.
* W-AG-J: the same with `c1 : terminate` and `c0 : join(c1)` between steps 8 and 9.
* W-AG′: from the state after step 7, a derivation and a reanchoring while the recorded grant is
  inactive.
-/

set_option autoImplicit false

namespace Ern.Concurrency.FullEncap.AbandonedGrant

open Ern.MemoryModel Ern.MemoryModel.Access Ern.Concurrency Ern.Concurrency.MutexReal
open Ern.Concurrency.Corpus Ern.Concurrency.FullEncap.Protected
open Ern.Concurrency.FullEncap.Witness (instDecidableEncap5R)
open Ern.Concurrency.Corpus.MutexEdgeStrict (handoffOrderedS_of_two not_raceS_of_two)
open Ern.Concurrency.Traces (L0)

/-- The covering descendants of `g` in state `s` (WC5.2 C22; brief of the complement, "Descendants
couvrants"): the active strict descendants of `g` by the current origin chain, read transitively,
that cover a leaf of `footprint(g)` (`CoveringDesc`), listed by identity. -/
def covSet (s : SC) (g : Nat) : List Nat :=
  (List.range s.A.length).filter fun j => decide (CoveringDesc s g j)

/-! ## W-AG -/

/-- Step 8, `c1 : release(x)` (O3). -/
def ag10 : SC := ab9.set (releaseEff (ab9.view 1) 6)
/-- Step 10, `c0 : acquire(e)`: grant `g′`, authority 7, held by frame 0 (WC5.2 C16). -/
def ag11 : SC := deriveSyncEff ag10 0 3
/-- The registry with `g′` recorded. -/
def agReg : SyncReg := [⟨3, some 7⟩]
/-- Step 11, `c0 : write3(T)` via `g′` (O10). -/
def ag12 : SC := ag11.set (write3Eff (ag11.view 0) [3])

/-- The labels of W-AG: `MX₃`, then steps 1 to 11. -/
def agLbls : List Label :=
  abLbls ++ [.kernel 1 (.release 6), .resetLock 0 0, .acquire 0 0, .kernel 0 (.write 7 [3])]

/-- The named states of W-AG. -/
def agσ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(x0, [], []), (x1, [], []), (x2, [], []), (x2, regX, []), (ab3, regX, []), (ab4, regX, []),
    (ab5, abReg, []), (ab6, abReg, []), (ab7, abReg, []), (ab8, abReg, []), (ab9, abReg, []),
    (ag10, abReg, []), (ag10, regX, []), (ag11, agReg, []), (ag12, agReg, [])].getD i
    (ag12, agReg, [])

/-- The steps of W-AG from `MX₃`, each admitted by `Encap5R`. -/
theorem ag_steps : Steps5R KM L0
    [(x2, regX, []), (ab3, regX, []), (ab4, regX, []), (ab5, abReg, []), (ab6, abReg, []),
      (ab7, abReg, []), (ab8, abReg, []), (ab9, abReg, []), (ag10, abReg, []), (ag10, regX, []),
      (ag11, agReg, []), (ag12, agReg, [])]
    [.kernel 0 (.derive 0 [2] .observe), .kernel 0 (.enter [4] []), .acquire 0 0,
      .kernel 0 (.derive 5 [3] .modify), .spawn 0 [6] [], .kernel 0 .exit, .kernel 1 (.write 6 [3]),
      .kernel 1 (.release 6), .resetLock 0 0, .acquire 0 0, .kernel 0 (.write 7 [3])] :=
  .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
  .cons (by decide) (.kernel ⟨by decide, .ok (by decide)⟩) <|
  .cons (by decide) (.acquire ⟨by decide, ⟨3, none⟩, rfl, by decide, by decide, rfl⟩) <|
  .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
  .cons (by decide) (.spawn ⟨by decide, .ok (by decide)⟩) <|
  .cons (by decide) (.kernel ⟨by decide, .ok (by decide)⟩) <|
  .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
  .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
  .cons (by decide) (.resetLock ⟨by decide, ⟨3, some 5⟩, rfl, by decide, by decide, by decide,
    rfl⟩) <|
  .cons (by decide) (.acquire ⟨by decide, ⟨3, none⟩, rfl, by decide, by decide, rfl⟩) <|
  .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) .nil

/-- `corpus-spec2-m3.md` v14 §2 terdecies W-AG, steps 1 to 11: every step is an `ok` kernel or
library step (O1, O6, WC5.2 C14–C16, O1, C4, C6, O10, O3, C18, C16, O10) and is admitted by the
complete encapsulation; from the initial state, the trace is a `RunFull`. -/
theorem W_AG_run : agσ 0 = (SC.ofS3 (S3.init mxst), [], []) ∧ RunFull KM L0 agσ agLbls :=
  ⟨rfl, runFull_of_run7 (run7_of_run5R ((ClassifyWitness.mx3_steps ag_steps).run _) (by decide))
    (by decide)⟩

/-- `corpus-spec2-m3.md` v14 §2 terdecies W-AG, facts on step 6 (`c0 : exitFrameC(f1)`, from `ab7`
to `ab8`; Spec 1 §73 effect, WC5.2 C6):
* no authority is created;
* the origin of `x` (authority 6) goes from `g` (5) to `guarded` (3), its footprint and own mode
  unchanged;
* the covering descendants of `guarded` are `g` and `x` before the step, `x` alone after it;
* after the step, `e` is live (WC5.2 C12), `grant = some g` with `g` inactive, and `root_M` has
  effective `Modify` on `slot` and `lock` again (Spec 1 §43.2). -/
theorem W_AG_6_facts : ab8.A.length = ab7.A.length ∧
    ab7.flat.org 6 = some 5 ∧ ab8.flat.org 6 = some 3 ∧ ab8.flat.afp 6 = ab7.flat.afp 6 ∧
    (ab8.A[6]?).map (·.mode) = (ab7.A[6]?).map (·.mode) ∧
    covSet ab7 3 = [5, 6] ∧ covSet ab8 3 = [6] ∧
    (⟨3, some 5⟩ : SyncEntry).Live ab8 ∧ ¬ ab8.flat.Active 5 ∧
    effective ab8.flat 0 1 = some .modify ∧ effective ab8.flat 0 2 = some .modify := by
  decide

/-- `corpus-spec2-m3.md` v14 §2 terdecies W-AG, refusal a, from the state after step 7:
`c0 : acquire(e)` has no `ok` outcome. C14.1 and C14.3 hold (the entry is live; `root_M` gives the
controller access); C14.2 fails (`grant = some g`); C15.4 (Spec 1 §60.2, the effective mode of
`guarded` on `T`) and C15.5 (§60.3, the active `x` overlaps `T` outside the origin chain of
`guarded`) fail too. -/
theorem W_AG_a : (∀ st', ¬ AcquireOk KM L0 ab9 abReg 0 0 st') ∧
    (⟨3, some 5⟩ : SyncEntry).Live ab9 ∧ CtrlRight L0 ab9 ⟨3, some 5⟩ (ab9.view 0).top ∧
    ¬ (∀ l ∈ (ab9.view 0).afp 3, Allows (effective (ab9.view 0) 3 l) .modify) ∧
    ¬ (∀ b ∈ List.range ab9.A.length, OptP (ab9.A[b]?) (fun y => y.active = true →
      b ∉ 3 :: (ab9.view 0).ancs 3 → (∃ l ∈ (ab9.view 0).afp 3, l ∈ y.footprint) →
        y.mode = .observe ∧ Mode.modify = .observe) True) := by
  refine ⟨?_, by decide, by decide, by decide, by decide⟩
  rintro st' ⟨-, e, he, ⟨-, hg, -⟩, -⟩
  cases he; cases hg

/-- `corpus-spec2-m3.md` v14 §2 terdecies W-AG, refusal b: `c0 : unlock(e)` is refused; C17.2 fails,
the recorded grant `g` being inactive (Spec 1 §62.1). -/
theorem W_AG_b : (∀ st', ¬ UnlockOk L0 ab9 abReg 0 0 st') ∧ ¬ (ab9.view 0).Active 5 := by
  refine ⟨?_, by decide⟩
  rintro st' ⟨-, e, g, he, -, hg, hrel, -⟩
  cases he; cases hg
  exact absurd hrel.active (by decide)

/-- `corpus-spec2-m3.md` v14 §2 terdecies W-AG, refusal c: `c0 : resetLock(e)` is refused; C18.2
fails, `x`, an active descendant of `guarded`, covering `T`. C18.1 holds through `root_M`. -/
theorem W_AG_c : (∀ st', ¬ ResetLockOk L0 ab9 abReg 0 0 st') ∧ ¬ NoCoveringDesc ab9 3 ∧
    CoveringDesc ab9 3 6 ∧ (ab9.view 0).ExercisableAt 3 .modify := by
  refine ⟨?_, by decide, by decide, by decide⟩
  rintro st' ⟨-, e, he, -, hn, -⟩
  cases he
  exact absurd hn (by decide)

/-- `corpus-spec2-m3.md` v14 §2 terdecies W-AG, refusal d: `c0 : read3(T)` with `access = guarded`
is refused; O9.2 fails, the effective mode of `guarded` on `T` being absent (Spec 1 §43.3). -/
theorem W_AG_d : opStepC KM (.read 3 [3]) 0 ab9 .reject ∧ effective ab9.flat 3 3 = none :=
  ⟨⟨by decide, _, .reject (by decide), rfl⟩, by decide⟩

/-! ## W-AG-J -/

/-- `c1 : terminate` (WC5.2 C7), after step 8. -/
def aj11 : SC := termEffC ag10 1
/-- Step 10 of W-AG-J, `c0 : acquire(e)`: grant `g′`, authority 7 (WC5.2 C16). -/
def aj12 : SC := deriveSyncEff aj11 0 3
/-- Step 11 of W-AG-J, `c0 : write3(T)` via `g′` (O10). -/
def aj13 : SC := aj12.set (write3Eff (aj12.view 0) [3])

/-- The labels of W-AG-J: steps 1 to 8, `c1 : terminate`, `c0 : join(c1)`, steps 9 to 11. -/
def ajLbls : List Label :=
  abLbls ++ [.kernel 1 (.release 6), .terminate 1, .join 0 1, .resetLock 0 0, .acquire 0 0,
    .kernel 0 (.write 7 [3])]

/-- The named states of W-AG-J. -/
def ajσ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(x0, [], []), (x1, [], []), (x2, [], []), (x2, regX, []), (ab3, regX, []), (ab4, regX, []),
    (ab5, abReg, []), (ab6, abReg, []), (ab7, abReg, []), (ab8, abReg, []), (ab9, abReg, []),
    (ag10, abReg, []), (aj11, abReg, []), (aj11, abReg, []), (aj11, regX, []),
    (aj12, agReg, []), (aj13, agReg, [])].getD i (aj13, agReg, [])

/-- `corpus-spec2-m3.md` v14 §2 terdecies W-AG-J: the synchronized twin is `ok` at every step and
admitted; from the initial state, the trace is a `RunFull` (WC5.2 C7, C8). -/
theorem W_AGJ_run : ajσ 0 = (SC.ofS3 (S3.init mxst), [], []) ∧ RunFull KM L0 ajσ ajLbls := by
  have h : Steps5R KM L0
      [(x2, regX, []), (ab3, regX, []), (ab4, regX, []), (ab5, abReg, []), (ab6, abReg, []),
        (ab7, abReg, []), (ab8, abReg, []), (ab9, abReg, []), (ag10, abReg, []),
        (aj11, abReg, []), (aj11, abReg, []), (aj11, regX, []), (aj12, agReg, []),
        (aj13, agReg, [])]
      [.kernel 0 (.derive 0 [2] .observe), .kernel 0 (.enter [4] []), .acquire 0 0,
        .kernel 0 (.derive 5 [3] .modify), .spawn 0 [6] [], .kernel 0 .exit,
        .kernel 1 (.write 6 [3]), .kernel 1 (.release 6), .terminate 1, .join 0 1,
        .resetLock 0 0, .acquire 0 0, .kernel 0 (.write 7 [3])] :=
    .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons (by decide) (.kernel ⟨by decide, .ok (by decide)⟩) <|
    .cons (by decide) (.acquire ⟨by decide, ⟨3, none⟩, rfl, by decide, by decide, rfl⟩) <|
    .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons (by decide) (.spawn ⟨by decide, .ok (by decide)⟩) <|
    .cons (by decide) (.kernel ⟨by decide, .ok (by decide)⟩) <|
    .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons (by decide) (.terminate ⟨by decide, .ok (by decide)⟩) <|
    .cons (by decide) (.join (.ok (by decide) (by decide))) <|
    .cons (by decide) (.resetLock ⟨by decide, ⟨3, some 5⟩, rfl, by decide, by decide, by decide,
      rfl⟩) <|
    .cons (by decide) (.acquire ⟨by decide, ⟨3, none⟩, rfl, by decide, by decide, rfl⟩) <|
    .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) .nil
  exact ⟨rfl, runFull_of_run7 (run7_of_run5R ((ClassifyWitness.mx3_steps h).run _) (by decide))
    (by decide)⟩

/-! ## The strict graph -/

/-- `corpus-spec2-m3.md` v14 §2 terdecies, strict graph of W-AG: the two writes of `T`, by `c1`
(step 7, index 9) and by `c0` (step 11, index 13), form an exclusive pair with no strict `hb` path;
the pair violates strict `HandoffOrderedAt` (WC5.2 C46); the trace has a strict `Race` and is not
strictly `HandoffOrdered`. -/
theorem W_AG_strict : ExclPair agLbls 9 13 3 ∧ ¬ HBS agσ L0 agLbls (.step 9) (.step 13) ∧
    ¬ HandoffOrderedAtS agσ L0 agLbls 9 13 3 ∧ ¬ HandoffOrderedS agσ L0 agLbls ∧
    RaceS agσ L0 agLbls := by
  have hp : ExclPair agLbls 9 13 3 :=
    ⟨by decide, by decide, 0, 1, .modify, .modify, by decide, ⟨rfl, by decide, rfl⟩,
      ⟨rfl, by decide, rfl⟩, Or.inl rfl⟩
  have hnb : ¬ HBS agσ L0 agLbls (.step 9) (.step 13) := by decide
  have hno : ¬ HandoffOrderedAtS agσ L0 agLbls 9 13 3 := by decide
  exact ⟨hp, hnb, hno, fun h => hno (h 9 13 3 hp), ⟨9, 13, 3, hp, hnb⟩⟩

/-- `corpus-spec2-m3.md` v14 §2 terdecies, strict graph of W-AG-J: write of `c1` (index 9) →`po`
`terminate(c1)` (index 11) →`sw` `join(c1)` (index 12) →`po` write of `c0` (index 15); the pair
satisfies strict `HandoffOrderedAt` (WC5.2 C46), and the trace, whose only accesses are these two
writes, is strictly `HandoffOrdered` and has no strict `Race`. -/
theorem W_AGJ_strict : PO ajσ ajLbls (.step 9) (.step 11) ∧
    SWS ajσ L0 ajLbls (.step 11) (.step 12) ∧ PO ajσ ajLbls (.step 12) (.step 15) ∧
    HBS ajσ L0 ajLbls (.step 9) (.step 15) ∧ HandoffOrderedS ajσ L0 ajLbls ∧
    ¬ RaceS ajσ L0 ajLbls := by
  have hkey : ∀ k (h : k < ajLbls.length), (ajLbls[k]'h).accMode ≠ none → k = 9 ∨ k = 15 := by
    decide
  have hb : HBS ajσ L0 ajLbls (.step 9) (.step 15) := by decide
  refine ⟨by decide, by decide, by decide, hb, handoffOrderedS_of_two hkey (by decide) ?_,
    not_raceS_of_two hkey (by decide) hb⟩
  rintro l ⟨_, c, m, ⟨-, hl, -⟩⟩
  rw [List.mem_singleton.1 hl]
  decide

/-! ## W-AG′ -/

/-- A1, `c1 : y := derive(x, Modify, {T})`, authority 7 (O1). -/
def ap1 : SC := ab9.set (deriveEff (ab9.view 1) 6 [3] .modify)
/-- A2, `c1 : spawn c2` yielding `y` (WC5.2 C4): context 2, initial frame 3. -/
def ap2 : SC := spawnEff ap1 1 [7] []
/-- A3, `c1 : terminate` (WC5.2 C7): `x` is released, `y` survives and is reanchored. -/
def ap3 : SC := termEffC ap2 1
/-- A4, `c2 : write3(T)` via `y` (O10). -/
def ap4 : SC := ap3.set (write3Eff (ap3.view 2) [3])

/-- The labels of W-AG′: steps 1 to 7 of W-AG, then A1 to A4. -/
def apLbls : List Label :=
  abLbls ++ [.kernel 1 (.derive 6 [3] .modify), .spawn 1 [7] [], .terminate 1,
    .kernel 2 (.write 7 [3])]

/-- The named states of W-AG′. -/
def apσ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(x0, [], []), (x1, [], []), (x2, [], []), (x2, regX, []), (ab3, regX, []), (ab4, regX, []),
    (ab5, abReg, []), (ab6, abReg, []), (ab7, abReg, []), (ab8, abReg, []), (ab9, abReg, []),
    (ap1, abReg, []), (ap2, abReg, []), (ap3, abReg, []), (ap4, abReg, [])].getD i
    (ap4, abReg, [])

/-- `corpus-spec2-m3.md` v14 §2 terdecies W-AG′: A1 to A4 are `ok` and admitted (O1, WC5.2 C4, C7,
O10); from the initial state, the trace is a `RunFull`. The covering descendants of `guarded`,
step by step: `{x}` after step 7; `{x, y}` after A1 (a creation, of origin `x`, already in the
set); unchanged after A2; `{y}` after A3 (no creation; the origin of `y` goes from `x` to
`guarded`); unchanged after A4. -/
theorem W_AGp_run : apσ 0 = (SC.ofS3 (S3.init mxst), [], []) ∧ RunFull KM L0 apσ apLbls ∧
    covSet ab9 3 = [6] ∧ covSet ap1 3 = [6, 7] ∧ ap1.flat.org 7 = some 6 ∧
    covSet ap2 3 = [6, 7] ∧ covSet ap3 3 = [7] ∧ ap3.A.length = ap2.A.length ∧
    ap2.flat.org 7 = some 6 ∧ ap3.flat.org 7 = some 3 ∧ covSet ap4 3 = [7] := by
  have h : Steps5R KM L0
      [(x2, regX, []), (ab3, regX, []), (ab4, regX, []), (ab5, abReg, []), (ab6, abReg, []),
        (ab7, abReg, []), (ab8, abReg, []), (ab9, abReg, []), (ap1, abReg, []), (ap2, abReg, []),
        (ap3, abReg, []), (ap4, abReg, [])]
      [.kernel 0 (.derive 0 [2] .observe), .kernel 0 (.enter [4] []), .acquire 0 0,
        .kernel 0 (.derive 5 [3] .modify), .spawn 0 [6] [], .kernel 0 .exit,
        .kernel 1 (.write 6 [3]), .kernel 1 (.derive 6 [3] .modify), .spawn 1 [7] [],
        .terminate 1, .kernel 2 (.write 7 [3])] :=
    .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons (by decide) (.kernel ⟨by decide, .ok (by decide)⟩) <|
    .cons (by decide) (.acquire ⟨by decide, ⟨3, none⟩, rfl, by decide, by decide, rfl⟩) <|
    .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons (by decide) (.spawn ⟨by decide, .ok (by decide)⟩) <|
    .cons (by decide) (.kernel ⟨by decide, .ok (by decide)⟩) <|
    .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons (by decide) (.spawn ⟨by decide, .ok (by decide)⟩) <|
    .cons (by decide) (.terminate ⟨by decide, .ok (by decide)⟩) <|
    .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) .nil
  exact ⟨rfl, runFull_of_run7 (run7_of_run5R ((ClassifyWitness.mx3_steps h).run _) (by decide))
    (by decide), by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide⟩

/-- `corpus-spec2-m3.md` v14 §2 terdecies W-AG′, negative after A3: `c0 : resetLock(e)` is refused;
C18.2 fails, `y` being an active descendant of `guarded` covering `T`. -/
theorem W_AGp_neg : (∀ st', ¬ ResetLockOk L0 ap3 abReg 0 0 st') ∧ CoveringDesc ap3 3 7 := by
  refine ⟨?_, by decide⟩
  rintro st' ⟨-, e, he, -, hn, -⟩
  cases he
  exact absurd hn (by decide)

end Ern.Concurrency.FullEncap.AbandonedGrant
