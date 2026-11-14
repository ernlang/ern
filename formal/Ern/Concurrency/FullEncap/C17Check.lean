import Ern.Concurrency.FullEncap.HandoffExtSame

/-!
# Targeted check of the proposed C17 item 4

Brief of milestone 4, "contrôle ciblé de la correction de C17 point 4"
(`formal/reports/spec2-m4-handoff-ext.md`, section « Contrôle de C17 point 4 »). The candidate
text, proposed C17 item 4, not adopted (brief), requires the controller-access right of WC5.3 C17
item 4 (Spec 1 §68.2) both before `unlock` and in the prospective authority state obtained by
releasing the recorded grant under O3 (Spec 1 §62). WC5.3 is unchanged; nothing here modifies an
existing definition (`UnlockOk`, `PremG`, `RunFull`, the definitions of `HandoffExt`).

* `prospUnlock`: the prospective state, the kernel component `UnlockOk` writes (`releaseEff` on
  the view of the acting context), the registry unchanged.
* `KeptRight`: in the prospective state, the controller-access right read as `PremG` reads it
  before the step (`CtrlRight5`, without a live `guarded` in the chain).
* `RunC17`: a `RunFull` every `unlock` step of which satisfies `KeptRight`.
-/

set_option autoImplicit false

namespace Ern.Concurrency.FullEncap.C17Check

open Ern.MemoryModel Ern.MemoryModel.Access Ern.Concurrency Ern.Concurrency.MutexReal
open Ern.Concurrency.FullEncap Ern.Concurrency.FullEncap.HandoffExt
open Ern.Concurrency.FullEncap.HandoffExtSame Ern.Concurrency.Corpus
open Ern.Concurrency.Traces (L0)

/-! ## Definitions -/

/-- The prospective authority state of an `unlock` executed by `c` on an entry recording the grant
`g` (proposed C17 item 4, not adopted (brief)): from the state before the step, `g` released
according to O3 (Spec 1 §62, `ok` effect: `releaseEff` on the view of `c`, written back as
`UnlockOk` writes it), the synchronization registry unchanged (it still records `grant = some g`),
hence the controller's logical state unchanged. It is a precondition state only (brief: neither
committed nor observable). -/
def prospUnlock (st : SC × SyncReg) (c g : Nat) : SC × SyncReg :=
  (st.1.set (releaseEff (st.1.view c) g), st.2)

/-- The kept right of `unlock` of entry `n` by `c` (brief, "Droit conservé"; proposed C17 item 4,
not adopted (brief)): in the prospective state, the acting frame has the controller-access right
of WC5.3 C17 item 4 (Spec 1 §68.2, C14 item 3), read in the form the complete encapsulation reads
it before the step (`PremG`: `CtrlRight5`, no live `guarded` in the holder chain). When entry `n`
does not exist or records no grant, C17 item 1 fails and the prospective state has no meaning
(brief, "Précision de lecture"); the predicate is then false. -/
def KeptRight (L : MutexLayout) (st : SC × SyncReg) (c n : Nat) : Prop :=
  OptP (st.2[n]?) (fun e => OptP e.grant (fun g => CtrlRight5 L (prospUnlock st c g) e c) False)
    False

/-- Decidability of `KeptRight`. -/
instance (L : MutexLayout) (st : SC × SyncReg) (c n : Nat) : Decidable (KeptRight L st c n) := by
  unfold KeptRight; infer_instance

/-- The kept right of a step (brief): `KeptRight` on the state before an `unlock`; no condition on
the other kinds. -/
def UnlockKept (L : MutexLayout) (st : SC × SyncReg × ArenaReg) : Label → Prop
  | .unlock c n => KeptRight L (st.1, st.2.1) c n
  | _ => True

/-- Decidability of `UnlockKept`. -/
instance (L : MutexLayout) (st : SC × SyncReg × ArenaReg) (lbl : Label) :
    Decidable (UnlockKept L st lbl) := by
  unfold UnlockKept; split <;> infer_instance

/-- Every step of the trace satisfies `UnlockKept` (brief, « Exécution corrigée »). -/
def KeptAll (L : MutexLayout) (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) : Prop :=
  ∀ i (h : i < lbls.length), UnlockKept L (σ i) lbls[i]

/-- Decidability of `KeptAll`. -/
instance (L : MutexLayout) (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) :
    Decidable (KeptAll L σ lbls) := by
  unfold KeptAll; infer_instance

/-- Corrected execution (brief, "Exécution corrigée"; proposed C17 item 4, not adopted (brief)): a
`RunFull` every `unlock` step of which satisfies the kept right. -/
def RunC17 (k : K) (L : MutexLayout) (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) :
    Prop :=
  RunFull k L σ lbls ∧ KeptAll L σ lbls

/-- Brief, "Exécution corrigée": a corrected execution is a `RunFull` (inclusion). -/
theorem runC17_runFull {k : K} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg}
    {lbls : List Label} (h : RunC17 k L σ lbls) : RunFull k L σ lbls :=
  h.1

/-! ## The controller is unchanged in the prospective state -/

/-- The release of the prospective state keeps the holders of the authorities (Spec 1 §62 `ok`
effect: only the activity of `g` and the anchors of its holding place change). -/
theorem prospUnlock_holder (st : SC × SyncReg) (c g a : Nat) :
    ((prospUnlock st c g).1.A[a]?).map (·.holder) = (st.1.A[a]?).map (·.holder) := by
  show ((releaseEff (st.1.view c) g).A[a]?).map (·.holder) = _
  unfold releaseEff
  split
  · rename_i x hx
    show ((st.1.A.set g { x with active := false })[a]?).map (·.holder) = _
    by_cases e : g = a
    · subst e
      have hx' : st.1.A[g]? = some x := hx
      rw [hx']
      simp [lt_of_getElem? hx']
    · simp [e]
  · rfl

/-- The controller of an entry is the same in the prospective state (WC5.3 C12 `ControlOf`,
positional: it reads the holder of `guarded` and the places, which the release keeps; brief,
"le contrôleur restant inchangé"). -/
theorem controlOf_prospUnlock (L : MutexLayout) (st : SC × SyncReg) (c g : Nat) (e : SyncEntry) :
    ControlOf L (prospUnlock st c g).1 e = ControlOf L st.1 e := by
  have hP : (prospUnlock st c g).1.P = st.1.P := by
    show (releaseEff (st.1.view c) g).P = _
    unfold releaseEff; split <;> rfl
  unfold ControlOf
  rw [prospUnlock_holder, hP]

/-! ## Task 1: the two traces of slice 4 -/

/-- Brief (C17 check), task 1, trace `unlock_r_eq_i_no_hb`: the prefix up to index 6 is a corrected
execution (it has no `unlock`); the `unlock` of `c1` at index 7, `ok` under WC5.3 C17 as adopted
and admitted by `PremG`, does not satisfy the kept right (proposed C17 item 4, not adopted
(brief)). The state fact: in the prospective state, grant 5 is inactive, `o1′` (authority 4) is
active and held by the protected leaf `T` (place 3), and `c1` has no `cap5` on `lock` (place 2),
the only chain from `c1` to `T` having passed through grant 5 (WC5.3 C43). -/
theorem ul_kept : RunC17 KM L0 ulσ (ulLbls.take 7) ∧ ulLbls[7] = .unlock 1 0 ∧
    ulσ 7 = (ul6, [⟨3, some 5⟩], []) ∧
    UnlockOk L0 ul6 [⟨3, some 5⟩] 1 0 (ul7, regX) ∧ PremG KM L0 (ulσ 7) (.unlock 1 0) ∧
    ¬ UnlockKept L0 (ulσ 7) ulLbls[7] ∧
    (prospUnlock (ul6, [⟨3, some 5⟩]) 1 5).1.A[5]?.map (·.active) = some false ∧
    (prospUnlock (ul6, [⟨3, some 5⟩]) 1 5).1.A[4]?.map (fun y => (y.active, y.holder)) =
      some (true, .place 3) ∧
    cap5 (prospUnlock (ul6, [⟨3, some 5⟩]) 1 5).1 [⟨3, some 5⟩] 1 2 = none := by
  have hr := unlock_r_eq_i_no_hb.1
  exact ⟨⟨Replay.RunFull.take hr 7, by decide⟩, rfl, rfl, ul_steps.2.2.2.2.1,
    (hr 7 (by decide)).1.2, by decide, by decide, by decide, by decide⟩

/-- Brief (C17 check), task 1, the twin without `resetLock` (`unlock_r_eq_i_twin`): the same
facts; the twin coincides with the trace up to index 7. -/
theorem ulj_kept : RunC17 KM L0 uljσ (uljLbls.take 7) ∧ uljLbls[7] = .unlock 1 0 ∧
    uljσ 7 = (ul6, [⟨3, some 5⟩], []) ∧
    UnlockOk L0 ul6 [⟨3, some 5⟩] 1 0 (ul7, regX) ∧ PremG KM L0 (uljσ 7) (.unlock 1 0) ∧
    ¬ UnlockKept L0 (uljσ 7) uljLbls[7] ∧
    (prospUnlock (ul6, [⟨3, some 5⟩]) 1 5).1.A[5]?.map (·.active) = some false ∧
    (prospUnlock (ul6, [⟨3, some 5⟩]) 1 5).1.A[4]?.map (fun y => (y.active, y.holder)) =
      some (true, .place 3) ∧
    cap5 (prospUnlock (ul6, [⟨3, some 5⟩]) 1 5).1 [⟨3, some 5⟩] 1 2 = none := by
  have hr := unlock_r_eq_i_twin.1
  exact ⟨⟨Replay.RunFull.take hr 7, by decide⟩, rfl, rfl, ul_steps.2.2.2.2.1,
    (hr 7 (by decide)).1.2, by decide, by decide, by decide, by decide⟩

end Ern.Concurrency.FullEncap.C17Check

/-! ## Task 2: non-regression on the other `RunFull` traces -/

namespace Ern.Concurrency.FullEncap.C17Check.NonReg

open Ern.MemoryModel Ern.MemoryModel.Access Ern.Concurrency Ern.Concurrency.MutexReal
open Ern.Concurrency.FullEncap Ern.Concurrency.FullEncap.HandoffExt
open Ern.Concurrency.Corpus Ern.Concurrency.Corpus.HandoffEvents Ern.Concurrency.Corpus.MutexEdge
open Ern.Concurrency.Corpus.ResetLockRight Ern.Concurrency.MutexReal.ClassifyWitness
open Ern.Concurrency.MutexReal.NonRegression
open Ern.Concurrency.MutexReal.Witness (s11σ s11Lbls)
open Ern.Concurrency.Corpus.GuardedChainC (lcLbls)
open Ern.Concurrency.FullEncap.AbandonedGrant
open Ern.Concurrency.Traces (L0)
open Ern.MemoryModel.Access.Examples (K0)
open Ern.Concurrency.FullEncap.C17Check Ern.Concurrency.FullEncap.HandoffExtSame

/-- The number of `unlock` steps of a trace (brief (C17 check), task 2, table). -/
def unlockCount (lbls : List Label) : Nat :=
  lbls.countP fun x => match x with
    | .unlock _ _ => true
    | _ => false

/-- Brief (C17 check), task 2, on the traces of the event pass, of the mutex edge and the final
amended executions (the 24 traces of `runAmF_traces_full`): each is a corrected execution
(proposed C17 item 4, not adopted (brief)), its `unlock` steps satisfying the kept right. -/
theorem nonreg_1 :
    RunC17 KF L0 hoσ hoLbls ∧ RunC17 KF L0 ho2σ ho2Lbls ∧ RunC17 KF L0 ho3σ ho3Lbls ∧
    RunC17 KF L0 hojσ hojLbls ∧ RunC17 KF L0 ho3jσ ho3jLbls ∧ RunC17 KM L0 lcσ lcLbls ∧
    RunC17 KM L0 rl0σ rl0Lbls ∧ RunC17 KM L0 rlσ rlLbls ∧ RunC17 KM L0 rljσ rljLbls ∧
    RunC17 KM L0 trσ trLbls ∧ RunC17 KM L0 trjσ trjLbls ∧ RunC17 KM L0 s11σ s11Lbls ∧
    RunC17 KM L0 cvσ cvLbls ∧ RunC17 KM L0 ceσ ceLbls ∧ RunC17 KM L0 crσ crLbls ∧
    RunC17 KM L0 gsTwinσ gsTwinLbls ∧ RunC17 KA L0 s3σ s3Lbls ∧ RunC17 KM L0 s10σ s10Lbls ∧
    RunC17 KM L0 AmendWitness.tsσ AmendWitness.tsLbls ∧
    RunC17 KA L0 AmendWitness.tiσ AmendWitness.tiLbls ∧
    RunC17 KM L0 AmendWitness.taσ AmendWitness.taLbls ∧
    RunC17 KM L0 AmendWitness.tdtσ AmendWitness.tdtLbls ∧
    RunC17 KM L0 FinalWitness.amσ FinalWitness.amLbls ∧
    RunC17 KM L0 AmendWitness.tdσ AmendWitness.tdLbls := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24⟩ := FullEncap.NonRegression.runAmF_traces_full
  exact ⟨⟨h1, by decide⟩, ⟨h2, by decide⟩, ⟨h3, by decide⟩, ⟨h4, by decide⟩, ⟨h5, by decide⟩,
    ⟨h6, by decide⟩, ⟨h7, by decide⟩, ⟨h8, by decide⟩, ⟨h9, by decide⟩, ⟨h10, by decide⟩,
    ⟨h11, by decide⟩, ⟨h12, by decide⟩, ⟨h13, by decide⟩, ⟨h14, by decide⟩, ⟨h15, by decide⟩,
    ⟨h16, by decide⟩, ⟨h17, by decide⟩, ⟨h18, by decide⟩, ⟨h19, by decide⟩, ⟨h20, by decide⟩,
    ⟨h21, by decide⟩, ⟨h22, by decide⟩, ⟨h23, by decide⟩, ⟨h24, by decide⟩⟩

/-- The number of `unlock` steps of the traces of `nonreg_1`, in the same order. -/
theorem nonreg_1_count :
    [unlockCount hoLbls, unlockCount ho2Lbls, unlockCount ho3Lbls, unlockCount hojLbls,
      unlockCount ho3jLbls, unlockCount lcLbls, unlockCount rl0Lbls, unlockCount rlLbls,
      unlockCount rljLbls, unlockCount trLbls, unlockCount trjLbls, unlockCount s11Lbls,
      unlockCount cvLbls, unlockCount ceLbls, unlockCount crLbls, unlockCount gsTwinLbls,
      unlockCount s3Lbls, unlockCount s10Lbls, unlockCount AmendWitness.tsLbls,
      unlockCount AmendWitness.tiLbls, unlockCount AmendWitness.taLbls,
      unlockCount AmendWitness.tdtLbls, unlockCount FinalWitness.amLbls,
      unlockCount AmendWitness.tdLbls] =
      [0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide

/-- Brief (C17 check), task 2, on the witnesses of slice 3, the replayed traces and the trace of
the refutation of slice 3: each is a corrected execution. -/
theorem nonreg_2 :
    RunC17 FullEncap.NonRegression.KL L0 FullEncap.NonRegression.lvσ
      FullEncap.NonRegression.lvLbls ∧
    RunC17 KM L0 Witness.gtσ Witness.gtLbls ∧ RunC17 Witness.KX L0 Witness.rxbσ Witness.rxbLbls ∧
    RunC17 CapacityWitness.KF4 L0 CapacityWitness.frσ CapacityWitness.frLbls ∧
    RunC17 CapacityWitness.KE3 L0 CapacityWitness.exσ CapacityWitness.exLbls ∧
    RunC17 CapacityWitness.KE3 L0 CapacityWitness.tmσ CapacityWitness.tmLbls ∧
    RunC17 KM L0 agσ agLbls ∧ RunC17 KM L0 ajσ ajLbls ∧ RunC17 KM L0 apσ apLbls ∧
    RunC17 KM L0 Replay.wrσ Replay.wrLbls ∧ RunC17 KM L0 Replay.cgσ Replay.cgLbls ∧
    RunC17 KA L0 Replay.s3fσ Replay.s3fLbls ∧
    RunC17 K0 L0 Replay.s4σ Replay.s4Lbls ∧ RunC17 K9 L0 Replay.s9σ Replay.s9Lbls ∧
    RunC17 K0 L0 Replay.mtσ Replay.mtLbls ∧ RunC17 K0 L0 Replay.dtσ Replay.dtLbls ∧
    RunC17 K0 L0 Replay.tAσ
      [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 4 1), .newMutex 0 4,
        .kernel 0 (.transfer 0 4)] ∧
    RunC17 K0 L0 Replay.tBσ
      [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 4 1), .newMutex 0 4, .acquire 0 0,
        .kernel 0 (.transfer 0 4)] ∧
    RunC17 K0 L0 Replay.kmσ Replay.kmLbls ∧ RunC17 K0 L0 Replay.ksσ Replay.ksLbls ∧
    RunC17 KW L0 Replay.tbσ Replay.tbLbls ∧ RunC17 K0 L0 Replay.saσ Replay.saLbls ∧
    RunC17 KM L0 Protected.abσ Protected.abLbls := by
  have hw := Replay.wc4_full
  exact ⟨⟨FullEncap.NonRegression.lv_full.2.1, by decide⟩, ⟨Witness.W_GI_twin.2, by decide⟩,
    ⟨Witness.W_RX_B.2, by decide⟩, ⟨CapacityWitness.exc_free.2.1, by decide⟩,
    ⟨CapacityWitness.exc_exit.2.1, by decide⟩, ⟨CapacityWitness.exc_terminate.2.1, by decide⟩,
    ⟨W_AG_run.2, by decide⟩, ⟨W_AGJ_run.2, by decide⟩, ⟨W_AGp_run.2.1, by decide⟩,
    ⟨Replay.W_GR_full.2.2.2.2.2, by decide⟩, ⟨Replay.W_GC_full.2.2.2.2.2, by decide⟩,
    ⟨Replay.S3_full.2, by decide⟩, ⟨Replay.S4_full.2, by decide⟩, ⟨Replay.S9_full.2, by decide⟩,
    ⟨Replay.mutex_full.2, by decide⟩, ⟨Replay.distinct_full.2, by decide⟩,
    ⟨hw.2.2.1, by decide⟩, ⟨hw.2.2.2.1, by decide⟩, ⟨Replay.endUseM_full.2, by decide⟩,
    ⟨Replay.endUseSlot_full.2, by decide⟩, ⟨Replay.W_C22_3b_twin_full.2, by decide⟩,
    ⟨Replay.S17a_twin_full.2, by decide⟩, ⟨Protected.protected_runFull_refuted.2.1, by decide⟩⟩

/-- The number of `unlock` steps of the traces of `nonreg_2`, in the same order. -/
theorem nonreg_2_count :
    [unlockCount FullEncap.NonRegression.lvLbls, unlockCount Witness.gtLbls,
      unlockCount Witness.rxbLbls, unlockCount CapacityWitness.frLbls,
      unlockCount CapacityWitness.exLbls, unlockCount CapacityWitness.tmLbls,
      unlockCount agLbls, unlockCount ajLbls, unlockCount apLbls, unlockCount Replay.wrLbls,
      unlockCount Replay.cgLbls, unlockCount Replay.s3fLbls, unlockCount Replay.s4Lbls,
      unlockCount Replay.s9Lbls, unlockCount Replay.mtLbls, unlockCount Replay.dtLbls,
      unlockCount [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 4 1), .newMutex 0 4,
        .kernel 0 (.transfer 0 4)],
      unlockCount [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 4 1), .newMutex 0 4,
        .acquire 0 0, .kernel 0 (.transfer 0 4)],
      unlockCount Replay.kmLbls, unlockCount Replay.ksLbls, unlockCount Replay.tbLbls,
      unlockCount Replay.saLbls, unlockCount Protected.abLbls] =
      [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide

/-- Brief (C17 check), task 2, on the witnesses of slice 4 other than the `(unlock, E)` trace and
its twin: each is a corrected execution; none has an `unlock` step. -/
theorem nonreg_3 :
    RunC17 KF L0 HandoffExtWitness.htσ HandoffExtWitness.htLbls ∧
    RunC17 KF L0 HandoffExtWitness.htjσ HandoffExtWitness.htjLbls ∧
    RunC17 KF L0 HandoffExtWitness.hsσ HandoffExtWitness.hsLbls ∧
    RunC17 KF L0 HandoffExtWitness.hsjσ HandoffExtWitness.hsjLbls ∧
    RunC17 KF L0 HandoffExtWitness.hxσ HandoffExtWitness.hxLbls ∧
    RunC17 KF L0 HandoffExtWitness.hxjσ HandoffExtWitness.hxjLbls ∧
    RunC17 K0 L0 HandoffExtWitness.svσ HandoffExtWitness.svLbls ∧
    RunC17 KM L0 HandoffExtWitness.crjσ HandoffExtWitness.crjLbls ∧
    RunC17 K0 L0 vnσ vnLbls ∧ RunC17 KM L0 hqσ hqLbls ∧
    [unlockCount HandoffExtWitness.htLbls, unlockCount HandoffExtWitness.htjLbls,
      unlockCount HandoffExtWitness.hsLbls, unlockCount HandoffExtWitness.hsjLbls,
      unlockCount HandoffExtWitness.hxLbls, unlockCount HandoffExtWitness.hxjLbls,
      unlockCount HandoffExtWitness.svLbls, unlockCount HandoffExtWitness.crjLbls,
      unlockCount vnLbls, unlockCount hqLbls] = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  exact ⟨⟨HandoffExtWitness.W_HT_run.2.2.2.2.2.2, by decide⟩, ⟨HandoffExtWitness.W_HTJ_run.2.2.2, by decide⟩,
    ⟨HandoffExtWitness.W_HS_run.2.2.2.2, by decide⟩, ⟨HandoffExtWitness.W_HSJ_run.2.2.2, by decide⟩,
    ⟨HandoffExtWitness.W_HX_run.2.2.2.2.2, by decide⟩, ⟨HandoffExtWitness.W_HXJ_run.2.2.2, by decide⟩,
    ⟨HandoffExtWitness.W_SV_run.2.2.2.2, by decide⟩, ⟨HandoffExtWitness.W_CR_twin.2, by decide⟩,
    ⟨spawnVal_N_witness.1, by decide⟩, ⟨hint_store_rejected.1, by decide⟩, by decide⟩

end Ern.Concurrency.FullEncap.C17Check.NonReg

/-! ## Task 3: a successful `unlock` is no longer its own frontier -/

namespace Ern.Concurrency.FullEncap.C17Check

open Ern.MemoryModel Ern.MemoryModel.Access Ern.Concurrency Ern.Concurrency.MutexReal
open Ern.Concurrency.FullEncap Ern.Concurrency.FullEncap.HandoffExt

/-- An `ok` `unlock` keeps the places (Spec 1 §62 `ok` effect; WC5.3 C17 effect). -/
theorem unlock_P {k : K} {L : MutexLayout} {st st' : SC × SyncReg × ArenaReg} {c n : Nat}
    (hs : LStep k L (.unlock c n) st st') : st'.1.P = st.1.P := by
  cases hs with
  | unlock h =>
    obtain ⟨-, _, _, -, -, -, -, -, rfl⟩ := h
    show (releaseEff _ _).P = _
    unfold releaseEff; split <;> rfl

/-- The leaf touched by an `ok` `unlock` of entry `n` is the controller of the entry (WC5.3 C17
item 4; the footprint `Touches` of the step): the step creates no place. -/
theorem unlock_touchL_ctl {k : K} {L : MutexLayout} {st st' : SC × SyncReg × ArenaReg}
    {c n l : Nat} (hs : LStep k L (.unlock c n) st st') (ht : TouchL L st st' (.unlock c n) l) :
    (st.2.1[n]?).bind (ControlOf L st.1) = some l := by
  have hP := unlock_P hs
  rcases ht with ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨⟨h1, h2⟩, -⟩
  · exact h
  · exact h
  · rw [hP] at h2; omega

/-- After an `ok` `unlock` of entry `n` by `c` that satisfies the kept right (proposed C17 item 4,
not adopted (brief)), from a state whose live contexts have nonempty stacks, `c` keeps a capability
at least `Observe` on the controller (WC5.3 C43). The kept right is read in the prospective state,
whose kernel component is that of the resulting state (`UnlockOk`); the resulting registry differs
only by `grant = none` and has the same `guarded` identities (`cap5_same`). -/
theorem unlock_cap_after {k : K} {L : MutexLayout} {st st' : SC × SyncReg × ArenaReg}
    {c n l : Nat} (hF : FramesC st.1) (hw : WF3 st'.1.flat) (hs : LStep k L (.unlock c n) st st')
    (hk : KeptRight L (st.1, st.2.1) c n)
    (hctl : (st.2.1[n]?).bind (ControlOf L st.1) = some l) :
    Allows (cap5 st'.1 st'.2.1 c l) .observe := by
  cases hs with
  | @unlock s reg ar c n st₁ h =>
    obtain ⟨hlv, e, g, hn, -, hg, -, -, rfl⟩ := h
    change OptP (reg[n]?) (fun e => OptP e.grant
      (fun g => CtrlRight5 L (prospUnlock (s, reg) c g) e c) False) False at hk
    rw [hn] at hk hctl
    change OptP e.grant (fun g => CtrlRight5 L (prospUnlock (s, reg) c g) e c) False at hk
    rw [hg] at hk
    change CtrlRight5 L (prospUnlock (s, reg) c g) e c at hk
    change ControlOf L s e = some l at hctl
    have hctl' := (controlOf_prospUnlock L (s, reg) c g e).trans hctl
    have h1 := cap5_of_ctrlRight5 (s := (prospUnlock (s, reg) c g).1) (reg := reg)
      (show (prospUnlock (s, reg) c g).1.stk c ≠ [] from hF.nonempty c hlv) hk hctl'
    have hle := cap5_same (s := (prospUnlock (s, reg) c g).1) (reg := reg)
      (reg' := reg.set n { e with grant := none }) hw rfl rfl rfl (fun e' he' => by
        rcases List.mem_or_eq_of_mem_set he' with h' | rfl
        · exact ⟨e', h', rfl⟩
        · exact ⟨e, List.mem_of_getElem? hn, rfl⟩) c l
    show Allows (cap5 (prospUnlock (s, reg) c g).1 (reg.set n { e with grant := none }) c l)
      .observe
    revert h1 hle
    generalize cap5 (prospUnlock (s, reg) c g).1 reg c l = o1
    generalize cap5 (prospUnlock (s, reg) c g).1 (reg.set n { e with grant := none }) c l = o2
    rcases o1 with _ | _ | _ <;> rcases o2 with _ | _ | _ <;> decide

/-- Brief (C17 check), task 3, **proved**: on a corrected execution from the initial state
(proposed C17 item 4, not adopted (brief)), the frontier of an extended exclusive pair `(i, j, l)`
whose first member is an `unlock` is strictly after it. The leaf `l` is then the controller of the
entry (`unlock_touchL_ctl`). After the `unlock`, its context keeps a capability at least `Observe`
on `l` (`unlock_cap_after`); the touch of the `unlock` requires `Observe` (WC5.3 C17 item 4), is
not dying (`extPair_first_not_dying`) and creates nothing, so the touch of `j` is exclusive (class D
or class E with `Modify`) and incompatible with any present capability (WC5.3 C43). -/
theorem frontier_gt_unlock {k : K} {L : MutexLayout} {statics : Statics}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} (hdd : DDSound k)
    (hstat : StaticsOK statics) (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], []))
    (h : RunC17 k L σ lbls) {i j l r : Nat} (hp : ExtPair k L σ lbls i j l)
    (hi : i < lbls.length) {c n : Nat} (hl : lbls[i] = .unlock c n)
    (hr : IsFrontier k σ lbls i j l r) : i < r := by
  refine Nat.lt_of_le_of_ne hr.1 fun hir => ?_
  subst hir
  have hn := extPair_second_not_created hdd hstat h0 h.1 hp
  have hnd := extPair_first_not_dying hdd hstat h0 h.1 hp
  obtain ⟨hij, hj, -, hti, -, hex⟩ := hp.out
  have e : (lbls[i]'(Nat.lt_trans hij hj)) = .unlock c n := hl
  rw [e] at hti hex
  have hfr := (frontAt_iff hi hj i).1 hr.2.2.1
  have hs := (h.1 i hi).2
  have hk := h.2 i hi
  rw [hl] at hs hk hfr
  rw [show (Label.unlock c n).ctx = c from rfl] at hfr
  have hcap := unlock_cap_after (runFull_inv hdd hstat h0 h.1 (Nat.le_of_lt hi)).1.1.1.1
    (runFull_inv hdd hstat h0 h.1 (Nat.succ_le_of_lt hi)).1.1.1.2 hs hk
    (unlock_touchL_ctl hs hti)
  have hxj : ClassD (σ j) (σ (j + 1)) l ∨ ClassEm k (σ j) (σ (j + 1)) lbls[j] l .modify := by
    rcases hex with ⟨-, hD | hC | hEm⟩ | ⟨-, hD | hC | hEm⟩
    · exact absurd hD hnd
    · have h2 := hC.1.2
      rw [unlock_P hs] at h2
      exact absurd hC.1.1 (Nat.not_le.2 h2)
    · exact nomatch (hEm.2 : Mode.modify = Mode.observe)
    · exact .inl hD
    · exact absurd hC.1 hn
    · exact .inr hEm
  revert hcap hfr
  rcases cap5 (σ (i + 1)).1 (σ (i + 1)).2.1 c l with _ | _ | _
  · exact fun _ hcap => hcap
  · exact fun hfr _ => nomatch touchCompat_excl_none hxj hfr
  · exact fun hfr _ => touchCompat_not_modify hfr

end Ern.Concurrency.FullEncap.C17Check

/-! ## Task 4: observation from the state before the refused `unlock` -/

namespace Ern.Concurrency.FullEncap.C17Check.Observe

open Ern.MemoryModel Ern.MemoryModel.Access Ern.Concurrency Ern.Concurrency.MutexReal
open Ern.Concurrency.FullEncap Ern.Concurrency.FullEncap.HandoffExt
open Ern.Concurrency.FullEncap.HandoffExtSame Ern.Concurrency.Corpus
open Ern.Concurrency.FullEncap.C17Check
open Ern.Concurrency.FullEncap.Witness (instDecidableEncap5R)
open Ern.Concurrency.Traces (L0)

/-- The registry before index 7 of `unlock_r_eq_i_no_hb`: entry `e` records grant 5, held by
`c1`. -/
def reg5 : SyncReg := [⟨3, some 5⟩]

/-- Suite A (brief (C17 check), task 4), step 1: `c1 : terminate` (WC5.3 C7). -/
def oA1 : SC := termEffC ul6 1
/-- Suite A, step 3: `c0 : acquire(e)` (WC5.3 C16): grant 6, held by frame 0. -/
def oA3 : SC := deriveSyncEff oA1 0 3
/-- Suite A, step 4: `c0 : release(o1′)` (O3, Spec 1 §62). -/
def oA4 : SC := oA3.set (releaseEff (oA3.view 0) 4)
/-- Suite A, step 5: `c0 : unlock(e)` (WC5.3 C17). -/
def oA5 : SC := oA4.set (releaseEff (oA4.view 0) 6)

/-- The labels of suite A. -/
def obsALbls : List Label :=
  [.terminate 1, .resetLock 0 0, .acquire 0 0, .kernel 0 (.release 4), .unlock 0 0]

/-- The named states of suite A, from the state before index 7 of `unlock_r_eq_i_no_hb`. -/
def obsAσ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(ul6, reg5, []), (oA1, reg5, []), (oA1, regX, []), (oA3, [⟨3, some 6⟩], []),
    (oA4, [⟨3, some 6⟩], []), (oA5, regX, [])].getD i (oA5, regX, [])

/-- Brief (C17 check), task 4, suite A, verdicts (an observation; the brief states no expected
verdict): from the state before index 7 (`c1` holds grant 5, `o1′` is held by `T`), every step is
`ok` at the kernel (WC5.3 C7, C18, C16; O3; C17), admitted by the complete encapsulation
(`EncapFull`), and the `unlock` of `c0` satisfies the kept right (proposed C17 item 4, not adopted
(brief)): the run is a corrected execution from that state. After `terminate`, grant 5 is
inactive, `o1′` still active and held by `T`. -/
theorem obsA : obsAσ 0 = ulσ 7 ∧ RunC17 KM L0 obsAσ obsALbls ∧
    TermStep KM ul6 1 (.ok oA1) ∧ ResetLockOk L0 oA1 reg5 0 0 (oA1, regX) ∧
    AcquireOk KM L0 oA1 regX 0 0 (oA3, [⟨3, some 6⟩]) ∧
    opStepC KM (.release 4) 0 oA3 (.ok oA4) ∧ UnlockOk L0 oA4 [⟨3, some 6⟩] 0 0 (oA5, regX) ∧
    oA1.A[5]?.map (·.active) = some false ∧
    oA1.A[4]?.map (fun y => (y.active, y.holder)) = some (true, .place 3) := by
  have t : TermStep KM ul6 1 (.ok oA1) := ⟨by decide, .ok (by decide)⟩
  have r : ResetLockOk L0 oA1 reg5 0 0 (oA1, regX) :=
    ⟨by decide, ⟨3, some 5⟩, rfl, by decide, by decide, by decide, rfl⟩
  have a : AcquireOk KM L0 oA1 regX 0 0 (oA3, [⟨3, some 6⟩]) :=
    ⟨by decide, ⟨3, none⟩, rfl, by decide, by decide, rfl⟩
  have rl : opStepC KM (.release 4) 0 oA3 (.ok oA4) := ⟨by decide, _, .ok (by decide), rfl⟩
  have u : UnlockOk L0 oA4 [⟨3, some 6⟩] 0 0 (oA5, regX) :=
    ⟨by decide, ⟨3, some 6⟩, 6, rfl, by decide, rfl, by decide, by decide, rfl⟩
  have h : Steps5R KM L0 [(ul6, reg5, []), (oA1, reg5, []), (oA1, regX, []),
      (oA3, [⟨3, some 6⟩], []), (oA4, [⟨3, some 6⟩], []), (oA5, regX, [])] obsALbls :=
    .cons (by decide) (.terminate t) <| .cons (by decide) (.resetLock r) <|
    .cons (by decide) (.acquire a) <| .cons (by decide) (.kernel rl) <|
    .cons (by decide) (.unlock u) .nil
  exact ⟨rfl, ⟨runFull_of_run7 (run7_of_run5R (h.run _) (by decide)) (by decide), by decide⟩,
    t, r, a, rl, u, by decide, by decide⟩

/-- Suite B (brief (C17 check), task 4), step 1: `c1 : o2 := derive(o1′, Observe, {lock})` (O1,
Spec 1 §60): authority 6, held by frame 1. -/
def oB1 : SC := ul6.set (deriveEff (ul6.view 1) 4 [2] .observe)
/-- Suite B, step 2: `c1 : unlock(e)` (WC5.3 C17). -/
def oB2 : SC := oB1.set (releaseEff (oB1.view 1) 5)

/-- The labels of suite B. -/
def obsBLbls : List Label := [.kernel 1 (.derive 4 [2] .observe), .unlock 1 0]

/-- The named states of suite B, from the state before index 7 of `unlock_r_eq_i_no_hb`. -/
def obsBσ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(ul6, reg5, []), (oB1, reg5, []), (oB2, regX, [])].getD i (oB2, regX, [])

/-- Brief (C17 check), task 4, suite B, verdicts (an observation; the brief states no expected
verdict): from the state before index 7, the `derive` of `c1` is `ok` at the kernel (O1, through
`o1′` held by `T` under grant 5) and admitted by the complete encapsulation; the `unlock` of `c1`
is then `ok` (WC5.3 C17), admitted, and satisfies the kept right (proposed C17 item 4, not adopted
(brief)), through `o2`, held by frame 1. After it, `c1` keeps `Observe` on `lock` (WC5.3 C43). -/
theorem obsB : obsBσ 0 = ulσ 7 ∧ RunC17 KM L0 obsBσ obsBLbls ∧
    opStepC KM (.derive 4 [2] .observe) 1 ul6 (.ok oB1) ∧ UnlockOk L0 oB1 reg5 1 0 (oB2, regX) ∧
    oB1.A[6]?.map (fun y => (y.active, y.holder, y.origin, y.mode)) =
      some (true, .frame 1, some 4, .observe) ∧
    cap5 oB2 regX 1 2 = some .observe := by
  have d : opStepC KM (.derive 4 [2] .observe) 1 ul6 (.ok oB1) :=
    ⟨by decide, _, .ok (by decide), rfl⟩
  have u : UnlockOk L0 oB1 reg5 1 0 (oB2, regX) :=
    ⟨by decide, ⟨3, some 5⟩, 5, rfl, by decide, rfl, by decide, by decide, rfl⟩
  have h : Steps5R KM L0 [(ul6, reg5, []), (oB1, reg5, []), (oB2, regX, [])] obsBLbls :=
    .cons (by decide) (.kernel d) <| .cons (by decide) (.unlock u) .nil
  exact ⟨rfl, ⟨runFull_of_run7 (run7_of_run5R (h.run _) (by decide)) (by decide), by decide⟩,
    d, u, by decide, by decide⟩

end Ern.Concurrency.FullEncap.C17Check.Observe
