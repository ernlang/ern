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

/-- Every step of the trace satisfies `UnlockKept`. -/
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
