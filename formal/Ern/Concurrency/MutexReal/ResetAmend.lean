import Ern.Concurrency.MutexReal.NonRegression

/-!
# `resetLock` under the proposed C18 item 4

Brief of milestone 4, slice 2, layer R, corrective pass, task 5 (`corpus-spec2-m3.md` v11 §2
decies, "`resetLock` sous C18 amendé"): W-RC step 4 has no `ok` outcome for the amended step, the
failing clause being the controller-access right; its twin, and the `resetLock` steps of W-RL,
W-RL-J and of the positive twin of S11, stay `ok` under the amended form. In an amended execution
every protocol step `acquire(e)`, `unlock(e)`, `resetLock(e)` is made by a frame with a present
effective mode on `ControlOf(e)` (`protocol_authority`).
-/

set_option autoImplicit false

namespace Ern.Concurrency.MutexReal.ResetAmend

open Ern.MemoryModel.Access Ern.Concurrency Ern.Concurrency.MutexReal
open Ern.Concurrency.Corpus Ern.Concurrency.Corpus.MutexEdge
open Ern.Concurrency.Corpus.ResetLockRight
open Ern.Concurrency.Traces (L0)

/-! ## Verdicts -/

/-- `corpus-spec2-m3.md` v11 §2 decies, W-RC step 4, `c0 (f1) : resetLock(e)`, under the proposed
C18 item 4: no `ok` outcome; the failing clause is the new item 4 (no controller-access right of
`f1`), the clauses C18.1–C18.3 holding (`ResetLockOk`). Under the criterion of the corpus §0:
`reject`. -/
theorem W_RC_4_amended_reject : (∀ st', ¬ ResetLockAmOk L0 rc2 regX 0 0 st') ∧
    ResetLockOk L0 rc2 regX 0 0 (rc2, regX) ∧ ¬ CtrlRight L0 rc2 ⟨3, none⟩ (rc2.view 0).top := by
  have hc : ¬ CtrlRight L0 rc2 ⟨3, none⟩ (rc2.view 0).top := by decide
  refine ⟨fun st' h => ?_, W_RC_4_ok, hc⟩
  have h2 := h.2
  simp only [regX, List.getElem?_cons_zero, OptP] at h2
  exact hc h2

/-- `corpus-spec2-m3.md` v11 §2 decies, twin of W-RC: from `MX₃`, `c0 (f0) : resetLock(e)` is `ok`
under the amended form, `f0` having a present effective mode on `lock`. -/
theorem W_RC_twin_amended_ok : ResetLockAmOk L0 x2 regX 0 0 (x2, regX) :=
  ⟨W_RC_twin_ok.1, by decide⟩

/-- `corpus-spec2-m3.md` v11 §2 decies, W-RL: the `resetLock(e)` by `c0` after the prefix P is `ok`
under the amended form (`root_M` has a present effective mode on `lock`). -/
theorem W_RL_amended_ok : ResetLockAmOk L0 MutexEdge.p4 regX 0 0 (MutexEdge.p4, regX) :=
  ⟨W_RL_ok.1, by decide⟩

/-- `corpus-spec2-m3.md` v11 §2 decies, W-RL-J: the `resetLock(e)` by `c0` after `terminate` and
`join` is `ok` under the amended form. -/
theorem W_RLJ_amended_ok : ResetLockAmOk L0 jq regX 0 0 (jq, regX) :=
  ⟨W_RLJ_ok.2.2.1, by decide⟩

/-- `corpus-spec2-m3.md` v11 §2 decies, positive twin of S11 (§1 S11): after `terminate` and `join`,
the `resetLock(e)` of the abandoned grant by `c0` is `ok` under the amended form. -/
theorem S11_4_amended_ok : ResetLockAmOk L0 y4 regG6 0 0 (y4, regX) :=
  ⟨S11_4_ok.2.2.1, by decide⟩

/-- W-RL and W-RL-J are amended executions; W-RC is a `Run6` and no amended execution: trace step
5 (step 4 of the corpus) is the `resetLock` without controller-access right. -/
theorem amended_runs : RunAm KM L0 rlσ rlLbls ∧ RunAm KM L0 rljσ rljLbls ∧
    Run6 KM L0 rcσ rcLbls ∧ ¬ RunAm KM L0 rcσ rcLbls := by
  refine ⟨⟨NonRegression.W_RL_run6, by decide⟩, ⟨NonRegression.W_RLJ_run6, by decide⟩,
    NonRegression.W_RC_run6, fun h => ?_⟩
  have := h.2 5 (by decide)
  revert this
  decide

/-! ## Authority of the protocol steps -/

/-- Brief, corrective pass, task 5: an `ok` step `acquire(i)`, `unlock(i)` or `resetLock(i)` by `c`
that satisfies the clause of the proposed C18 item 4 is made by a frame with the
controller-access right on entry `i`: the current frame of `c` has an authority, exercisable in
`Observe`, with a present effective mode on `ControlOf(i)` (`CtrlRight`). For `acquire` it is
C14.3, for `unlock` C17.4, both in the step relation; for `resetLock` it is the amended clause. -/
theorem protocol_authority {k : K} {L : MutexLayout} {lbl : Label}
    {st st' : SC × SyncReg × ArenaReg} (h : LStep k L lbl st st') (ham : AmCond L st lbl)
    {c i : Nat} (hp : lbl = .acquire c i ∨ lbl = .unlock c i ∨ lbl = .resetLock c i) :
    OptP (st.2.1[i]?) (fun e => CtrlRight L st.1 e (st.1.view c).top) False := by
  rcases hp with rfl | rfl | rfl
  · cases h with
    | acquire ha =>
      obtain ⟨-, e, he, ⟨-, -, hcr⟩, -⟩ := ha
      simp only [he, OptP]
      exact hcr
  · cases h with
    | unlock hu =>
      obtain ⟨-, e, g, he, -, -, -, hcr, -⟩ := hu
      simp only [he, OptP]
      exact hcr
  · exact ham

/-- Brief, corrective pass, task 5: in an amended execution, every step `acquire(i)`, `unlock(i)`
or `resetLock(i)` by `c` is made by a frame with a present effective mode on `ControlOf(i)`. -/
theorem runAm_protocol_authority {k : K} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg}
    {lbls : List Label} (h : RunAm k L σ lbls) {j : Nat} (hj : j < lbls.length) {c i : Nat}
    (hp : lbls[j] = .acquire c i ∨ lbls[j] = .unlock c i ∨ lbls[j] = .resetLock c i) :
    OptP ((σ j).2.1[i]?) (fun e => CtrlRight L (σ j).1 e ((σ j).1.view c).top) False :=
  protocol_authority (h.1 j hj).2 (h.2 j hj) hp

end Ern.Concurrency.MutexReal.ResetAmend
