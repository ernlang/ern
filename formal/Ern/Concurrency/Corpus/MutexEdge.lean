import Ern.Concurrency.Events
import Ern.Concurrency.Corpus.MX

/-!
# Interventions on the controller between `unlock` and `acquire`

`corpus-spec2-m3.md` v9 §2 octies: the common prefix P from `MX₄` and the witnesses W-RL₀, W-RL,
W-RL-J, W-TR and W-TR-J, at the level of the authority machine. One theorem per group of verdicts,
written from `corpus-spec2-m3.md` v9 §2 octies, preconditions by `decide`, contract `KM`. Each
trace is given with its named states and is a `Run5R` from the initial state of Spec 1 §47.
-/

namespace Ern.Concurrency.Corpus.MutexEdge

open Ern.MemoryModel.Access Ern.Concurrency Ern.Concurrency.Corpus
open Ern.Concurrency.Traces (L0)

/-! ## The prefix P -/

/-- P, step 4, `c1 : release(o1)` (O3), context 1 staying live. -/
def p4 : SC := x7.set (releaseEff (x7.view 1) 4)

/-- `corpus-spec2-m3.md` v9 §2 octies, prefix P from `MX₄`: step 1 `c1 : acquire(e)` `ok` (WC5.1
C16), step 2 `c1 : write3(T)` via `g` `ok` (O10), step 3 `c1 : unlock(e)` `ok` (WC5.1 C17),
step 4 `c1 : release(o1)` `ok` (O3.1–O3.3: `o1` is active, derived, held by the current frame of
context 1, without an active descendant). -/
theorem P_ok : AcquireOk KM L0 x4 regX 1 0 (x5, regG) ∧ opStepC KM (.write 5 [3]) 1 x5 (.ok x6) ∧
    UnlockOk L0 x6 regG 1 0 (x7, regX) ∧ opStepC KM (.release 4) 1 x7 (.ok p4) :=
  ⟨S2_1_ok, S2_2_ok, S2_3_ok, ⟨by decide, _, .ok (by decide), rfl⟩⟩

/-- After P, `root_M` has effective `Modify` again on `slot` and `lock` (Spec 1 §43.2; §62
effect), and `ControlOf(e)` is `lock`. -/
theorem P_facts : effective p4.flat 0 1 = some .modify ∧ effective p4.flat 0 2 = some .modify ∧
    ControlOf L0 p4 ⟨3, none⟩ = some 2 := by decide

/-- The labels of block MX up to `MX₄` and of the prefix P. -/
def pLbls : List Label :=
  [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 3 1), .newMutex 0 3,
   .kernel 0 (.derive 0 [1, 2] .observe), .spawn 0 [4] [], .acquire 1 0, .kernel 1 (.write 5 [3]),
   .unlock 1 0, .kernel 1 (.release 4)]

/-- The setup and the prefix P from the initial state, each step admitted by `Encap5R`, followed
by any run from the state after P. -/
theorem prefix_steps {sts : List (SC × SyncReg × ArenaReg)} {lbls : List Label}
    (h : Steps5R KM L0 ((p4, regX, []) :: sts) lbls) :
    Steps5R KM L0 ((x0, [], []) :: (x1, [], []) :: (x2, [], []) :: (x2, regX, []) ::
      (x3, regX, []) :: (x4, regX, []) :: (x5, regG, []) :: (x6, regG, []) :: (x7, regX, []) ::
      (p4, regX, []) :: sts) (pLbls ++ lbls) :=
  .cons ⟨⟨(fun e he => by cases he), by decide, trivial⟩, trivial⟩ (.kernel mx_steps.1) <|
  .cons ⟨⟨trivial, trivial, trivial⟩, by decide⟩ (.kernel mx_steps.2.1) <|
  .cons ⟨⟨trivial, trivial, trivial⟩, trivial⟩ (.newMutex mx_steps.2.2.1) <|
  .cons ⟨⟨(by decide : ∀ e ∈ regX, e.Live x2 → 0 ≠ e.guarded), by decide, trivial⟩, trivial⟩
    (.kernel mx_steps.2.2.2.2.1) <|
  .cons ⟨⟨trivial, trivial, trivial⟩, trivial⟩ (.spawn mx_steps.2.2.2.2.2) <|
  .cons ⟨⟨trivial, trivial, trivial⟩, by decide⟩ (.acquire P_ok.1) <|
  .cons ⟨⟨trivial, by decide, by decide⟩, trivial⟩ (.kernel P_ok.2.1) <|
  .cons ⟨⟨trivial, trivial, trivial⟩, trivial⟩ (.unlock P_ok.2.2.1) <|
  .cons ⟨⟨trivial, trivial, trivial⟩, by decide⟩ (.kernel P_ok.2.2.2) h

/-! ## W-RL₀ -/

/-- W-RL₀, `c0 : acquire(e)`: grant `g′`, authority `6`, held by frame 0 (WC5.1 C16). -/
def r0a : SC := deriveSyncEff p4 0 3
/-- W-RL₀, `c0 : write3(T)` via `g′` (O10). -/
def r0w : SC := r0a.set (write3Eff (r0a.view 0) [3])

/-- `corpus-spec2-m3.md` v9 §2 octies W-RL₀, after P: `c0 : acquire(e)` `ok` (WC5.1 C16: C14.1,
C14.2 with `grant = none`, C14.3 through `root_M`), `c0 : write3(T)` via `g′` `ok` (O10). -/
theorem W_RL0_ok : AcquireOk KM L0 p4 regX 0 0 (r0a, [⟨3, some 6⟩]) ∧
    opStepC KM (.write 6 [3]) 0 r0a (.ok r0w) :=
  ⟨⟨by decide, ⟨3, none⟩, rfl, by decide, by decide, rfl⟩, ⟨by decide, _, .ok (by decide), rfl⟩⟩

/-- The labels of W-RL₀. -/
def rl0Lbls : List Label := pLbls ++ [.acquire 0 0, .kernel 0 (.write 6 [3])]

/-- The states after P in W-RL₀. -/
def rl0Tail : List (SC × SyncReg × ArenaReg) := [(r0a, [⟨3, some 6⟩], []), (r0w, [⟨3, some 6⟩], [])]

/-- The named states of W-RL₀. -/
def rl0σ (i : Nat) : SC × SyncReg × ArenaReg :=
  ([(x0, [], []), (x1, [], []), (x2, [], []), (x2, regX, []), (x3, regX, []), (x4, regX, []),
    (x5, regG, []), (x6, regG, []), (x7, regX, []), (p4, regX, [])] ++ rl0Tail).getD i
    (r0w, [⟨3, some 6⟩], [])

/-- W-RL₀ from the initial state is a `Run5R`. -/
theorem W_RL0_run : rl0σ 0 = (SC.ofS3 (S3.init mxst), [], []) ∧ Run5R KM L0 rl0σ rl0Lbls := by
  have h : Steps5R KM L0 ((p4, regX, []) :: rl0Tail) [.acquire 0 0, .kernel 0 (.write 6 [3])] :=
    .cons ⟨⟨trivial, trivial, trivial⟩, by decide⟩ (.acquire W_RL0_ok.1) <|
    .cons ⟨⟨trivial, by decide, by decide⟩, trivial⟩ (.kernel W_RL0_ok.2) .nil
  exact ⟨rfl, (prefix_steps h).run _⟩

/-! ## W-RL -/

/-- `corpus-spec2-m3.md` v9 §2 octies W-RL, after P: `c0 : resetLock(e)` `ok` (WC5.1 C18.1:
`ExercisableAt(guarded, Modify)` by the third clause of Spec 1 §43, `guarded` held by `slot` on
whose leaves `root_M` has effective `Modify`; C18.2; C18.3; no precondition reads the recorded
grant), then `c0 : acquire(e)` `ok` (WC5.1 C16) and `c0 : write3(T)` via `g′` `ok` (O10). -/
theorem W_RL_ok : ResetLockOk L0 p4 regX 0 0 (p4, regX) ∧
    AcquireOk KM L0 p4 regX 0 0 (r0a, [⟨3, some 6⟩]) ∧ opStepC KM (.write 6 [3]) 0 r0a (.ok r0w) :=
  ⟨⟨by decide, ⟨3, none⟩, rfl, by decide, by decide, by decide, rfl⟩, W_RL0_ok⟩

/-- The labels of W-RL. -/
def rlLbls : List Label := pLbls ++ [.resetLock 0 0, .acquire 0 0, .kernel 0 (.write 6 [3])]

/-- The named states of W-RL. -/
def rlσ (i : Nat) : SC × SyncReg × ArenaReg :=
  ([(x0, [], []), (x1, [], []), (x2, [], []), (x2, regX, []), (x3, regX, []), (x4, regX, []),
    (x5, regG, []), (x6, regG, []), (x7, regX, []), (p4, regX, []), (p4, regX, [])] ++
    rl0Tail).getD i (r0w, [⟨3, some 6⟩], [])

/-- W-RL from the initial state is a `Run5R`: `Encap5R` admits the `resetLock`, none of its
conjuncts constraining that label. -/
theorem W_RL_run : rlσ 0 = (SC.ofS3 (S3.init mxst), [], []) ∧ Run5R KM L0 rlσ rlLbls := by
  have h : Steps5R KM L0 ((p4, regX, []) :: (p4, regX, []) :: rl0Tail)
      [.resetLock 0 0, .acquire 0 0, .kernel 0 (.write 6 [3])] :=
    .cons ⟨⟨trivial, trivial, trivial⟩, trivial⟩ (.resetLock W_RL_ok.1) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, by decide⟩ (.acquire W_RL0_ok.1) <|
    .cons ⟨⟨trivial, by decide, by decide⟩, trivial⟩ (.kernel W_RL0_ok.2) .nil
  exact ⟨rfl, (prefix_steps h).run _⟩

/-! ## W-RL-J -/

/-- W-RL-J, `c1 : terminate` (WC5.1 C7). -/
def jq : SC := termEffC p4 1
/-- W-RL-J, `c0 : acquire(e)` (WC5.1 C16). -/
def jqa : SC := deriveSyncEff jq 0 3
/-- W-RL-J, `c0 : write3(T)` via `g′` (O10). -/
def jqw : SC := jqa.set (write3Eff (jqa.view 0) [3])

/-- `corpus-spec2-m3.md` v9 §2 octies W-RL-J, after P: `c1 : terminate` `ok` (WC5.1 C7),
`c0 : join(c1)` `ok` (WC5.1 C8), then as W-RL: `resetLock(e)`, `acquire(e)`, `write3(T)`, all
`ok`. -/
theorem W_RLJ_ok : TermStep KM p4 1 (.ok jq) ∧ JoinStep jq 0 1 (.ok jq) ∧
    ResetLockOk L0 jq regX 0 0 (jq, regX) ∧ AcquireOk KM L0 jq regX 0 0 (jqa, [⟨3, some 6⟩]) ∧
    opStepC KM (.write 6 [3]) 0 jqa (.ok jqw) :=
  ⟨⟨by decide, .ok (by decide)⟩, .ok (by decide) (by decide),
    ⟨by decide, ⟨3, none⟩, rfl, by decide, by decide, by decide, rfl⟩,
    ⟨by decide, ⟨3, none⟩, rfl, by decide, by decide, rfl⟩, ⟨by decide, _, .ok (by decide), rfl⟩⟩

/-- The labels of W-RL-J. -/
def rljLbls : List Label :=
  pLbls ++ [.terminate 1, .join 0 1, .resetLock 0 0, .acquire 0 0, .kernel 0 (.write 6 [3])]

/-- The named states of W-RL-J. -/
def rljσ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(x0, [], []), (x1, [], []), (x2, [], []), (x2, regX, []), (x3, regX, []), (x4, regX, []),
    (x5, regG, []), (x6, regG, []), (x7, regX, []), (p4, regX, []), (jq, regX, []),
    (jq, regX, []), (jq, regX, []), (jqa, [⟨3, some 6⟩], []), (jqw, [⟨3, some 6⟩], [])].getD i
    (jqw, [⟨3, some 6⟩], [])

/-- W-RL-J from the initial state is a `Run5R`. -/
theorem W_RLJ_run : rljσ 0 = (SC.ofS3 (S3.init mxst), [], []) ∧ Run5R KM L0 rljσ rljLbls := by
  obtain ⟨ht, hj, hr, ha, hw⟩ := W_RLJ_ok
  have h : Steps5R KM L0 [(p4, regX, []), (jq, regX, []), (jq, regX, []), (jq, regX, []),
      (jqa, [⟨3, some 6⟩], []), (jqw, [⟨3, some 6⟩], [])]
      [.terminate 1, .join 0 1, .resetLock 0 0, .acquire 0 0, .kernel 0 (.write 6 [3])] :=
    .cons ⟨⟨trivial, trivial, trivial⟩, trivial⟩ (.terminate ht) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, trivial⟩ (.join hj) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, trivial⟩ (.resetLock hr) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, by decide⟩ (.acquire ha) <|
    .cons ⟨⟨trivial, by decide, by decide⟩, trivial⟩ (.kernel hw) .nil
  exact ⟨rfl, (prefix_steps h).run _⟩

/-! ## W-TR -/

/-- W-TR, `c0 : transfer(M, M′)` (O4): `guarded` is held by `slot′`. -/
def tq : SC := transferEffC p4 0 0 4
/-- W-TR, `c0 : acquire(e)` (WC5.1 C16). -/
def tqa : SC := deriveSyncEff tq 0 3
/-- W-TR, `c0 : write3(T)` via `g′` (O10). -/
def tqw : SC := tqa.set (write3Eff (tqa.view 0) [3])

/-- `corpus-spec2-m3.md` v9 §2 octies W-TR, after P: `c0 : transfer(M, M′)` `ok` (O4: §63.1 and
§63.4 hold as in `MX₃`, `o1` being inactive), after which `ControlOf(e)` is `lock′`; then
`c0 : acquire(e)` `ok` (WC5.1 C16, C14.3 through `root_M′`) and `c0 : write3(T)` via `g′` `ok`
(O10). -/
theorem W_TR_ok : opStepC KM (.transfer 0 4) 0 p4 (.ok tq) ∧ ControlOf L0 tq ⟨3, none⟩ = some 6 ∧
    AcquireOk KM L0 tq regX 0 0 (tqa, [⟨3, some 6⟩]) ∧ opStepC KM (.write 6 [3]) 0 tqa (.ok tqw) :=
  ⟨⟨by decide, .ok (by decide)⟩, by decide, ⟨by decide, ⟨3, none⟩, rfl, by decide, by decide, rfl⟩,
    ⟨by decide, _, .ok (by decide), rfl⟩⟩

/-- The labels of W-TR. -/
def trLbls : List Label :=
  pLbls ++ [.kernel 0 (.transfer 0 4), .acquire 0 0, .kernel 0 (.write 6 [3])]

/-- The named states of W-TR. -/
def trσ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(x0, [], []), (x1, [], []), (x2, [], []), (x2, regX, []), (x3, regX, []), (x4, regX, []),
    (x5, regG, []), (x6, regG, []), (x7, regX, []), (p4, regX, []), (tq, regX, []),
    (tqa, [⟨3, some 6⟩], []), (tqw, [⟨3, some 6⟩], [])].getD i (tqw, [⟨3, some 6⟩], [])

/-- W-TR from the initial state is a `Run5R`. -/
theorem W_TR_run : trσ 0 = (SC.ofS3 (S3.init mxst), [], []) ∧ Run5R KM L0 trσ trLbls := by
  obtain ⟨ht, -, ha, hw⟩ := W_TR_ok
  have h : Steps5R KM L0 [(p4, regX, []), (tq, regX, []), (tqa, [⟨3, some 6⟩], []),
      (tqw, [⟨3, some 6⟩], [])]
      [.kernel 0 (.transfer 0 4), .acquire 0 0, .kernel 0 (.write 6 [3])] :=
    .cons ⟨⟨(by decide : TransferExcl L0 (p4, regX) 0), trivial, trivial⟩, by decide⟩
      (.kernel ht) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, by decide⟩ (.acquire ha) <|
    .cons ⟨⟨trivial, by decide, by decide⟩, trivial⟩ (.kernel hw) .nil
  exact ⟨rfl, (prefix_steps h).run _⟩

/-! ## W-TR-J -/

/-- W-TR-J, `c0 : transfer(M, M′)` after `terminate` and `join` (O4). -/
def uq : SC := transferEffC jq 0 0 4
/-- W-TR-J, `c0 : acquire(e)` (WC5.1 C16). -/
def uqa : SC := deriveSyncEff uq 0 3
/-- W-TR-J, `c0 : write3(T)` via `g′` (O10). -/
def uqw : SC := uqa.set (write3Eff (uqa.view 0) [3])

/-- `corpus-spec2-m3.md` v9 §2 octies W-TR-J, after P: `c1 : terminate` `ok` (WC5.1 C7),
`c0 : join(c1)` `ok` (WC5.1 C8), then as W-TR: `transfer(M, M′)`, `acquire(e)`, `write3(T)`, all
`ok`. -/
theorem W_TRJ_ok : TermStep KM p4 1 (.ok jq) ∧ JoinStep jq 0 1 (.ok jq) ∧
    opStepC KM (.transfer 0 4) 0 jq (.ok uq) ∧ AcquireOk KM L0 uq regX 0 0 (uqa, [⟨3, some 6⟩]) ∧
    opStepC KM (.write 6 [3]) 0 uqa (.ok uqw) :=
  ⟨W_RLJ_ok.1, W_RLJ_ok.2.1, ⟨by decide, .ok (by decide)⟩,
    ⟨by decide, ⟨3, none⟩, rfl, by decide, by decide, rfl⟩, ⟨by decide, _, .ok (by decide), rfl⟩⟩

/-- The labels of W-TR-J. -/
def trjLbls : List Label :=
  pLbls ++ [.terminate 1, .join 0 1, .kernel 0 (.transfer 0 4), .acquire 0 0,
    .kernel 0 (.write 6 [3])]

/-- The named states of W-TR-J. -/
def trjσ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(x0, [], []), (x1, [], []), (x2, [], []), (x2, regX, []), (x3, regX, []), (x4, regX, []),
    (x5, regG, []), (x6, regG, []), (x7, regX, []), (p4, regX, []), (jq, regX, []),
    (jq, regX, []), (uq, regX, []), (uqa, [⟨3, some 6⟩], []), (uqw, [⟨3, some 6⟩], [])].getD i
    (uqw, [⟨3, some 6⟩], [])

/-- W-TR-J from the initial state is a `Run5R`. -/
theorem W_TRJ_run : trjσ 0 = (SC.ofS3 (S3.init mxst), [], []) ∧ Run5R KM L0 trjσ trjLbls := by
  obtain ⟨ht, hj, htr, ha, hw⟩ := W_TRJ_ok
  have h : Steps5R KM L0 [(p4, regX, []), (jq, regX, []), (jq, regX, []), (uq, regX, []),
      (uqa, [⟨3, some 6⟩], []), (uqw, [⟨3, some 6⟩], [])]
      [.terminate 1, .join 0 1, .kernel 0 (.transfer 0 4), .acquire 0 0,
        .kernel 0 (.write 6 [3])] :=
    .cons ⟨⟨trivial, trivial, trivial⟩, trivial⟩ (.terminate ht) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, trivial⟩ (.join hj) <|
    .cons ⟨⟨(by decide : TransferExcl L0 (jq, regX) 0), trivial, trivial⟩, by decide⟩
      (.kernel htr) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, by decide⟩ (.acquire ha) <|
    .cons ⟨⟨trivial, by decide, by decide⟩, trivial⟩ (.kernel hw) .nil
  exact ⟨rfl, (prefix_steps h).run _⟩

end Ern.Concurrency.Corpus.MutexEdge
