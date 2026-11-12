import Ern.Concurrency.FullEncap.LastAcquire
import Ern.Concurrency.FullEncap.AbandonedGrant
import Ern.Concurrency.FullEncap.NonRegression

/-!
# Sweep of the complement on the `RunFull` traces

Brief of milestone 4, slice 3, complement, tasks 2, 3 and 5: the closure (`ClosureStep`), the
three cases of the protected data (`ThreeOK`, at mode `Observe`) and the absence of another
context's capacity on a dying leaf (`OtherCapFree`) are checked by `decide` at every step of the
`RunFull` traces of the repository, W-AG, W-AG-J and W-AG′ included. Step 7 of W-AG falls in the
third case (`W_AG_7_third`).
-/

set_option autoImplicit false

namespace Ern.Concurrency.FullEncap.Sweep

open Ern.MemoryModel Ern.MemoryModel.Access Ern.Concurrency Ern.Concurrency.MutexReal
open Ern.Concurrency.Corpus Ern.Concurrency.Corpus.HandoffEvents Ern.Concurrency.Corpus.MutexEdge
open Ern.Concurrency.Corpus.ResetLockRight Ern.Concurrency.MutexReal.ClassifyWitness
open Ern.Concurrency.MutexReal.NonRegression
open Ern.Concurrency.MutexReal.Witness (s11σ s11Lbls)
open Ern.Concurrency.Corpus.GuardedChainC (lcLbls)
open Ern.Concurrency.FullEncap.AbandonedGrant Ern.Concurrency.FullEncap.Protected
open Ern.Concurrency.Traces (L0)

/-- Decidability of `ProvCap` for a decidable provenance. -/
instance (st : SC × SyncReg × ArenaReg) (S : Nat → Prop) [DecidablePred S] (c l : Nat)
    (m : Mode) : Decidable (ProvCap st S c l m) := by
  unfold ProvCap; infer_instance

/-- The three cases of the brief of the complement, task 5, for one step, at mode `Observe`: for
every entry live before and after the step and every leaf of `footprint(guarded)` in the final
footprint, no grant is impossible; an active grant `g` gives a capacity from `g` or a descendant
of `g`; an inactive grant gives a capacity from the covering descendants. -/
def ThreeOK (L : MutexLayout) (st : SC × SyncReg × ArenaReg) (lbl : Label)
    (st' : SC × SyncReg × ArenaReg) : Prop :=
  ∀ e ∈ st.2.1, e.Live st.1 → e.Live st'.1 → ∀ l ∈ st.1.flat.afp e.guarded,
    TouchesF L st lbl l → OptP e.grant (fun g =>
      (st.1.flat.Active g → ProvCap st (fun x => x = g ∨ g ∈ st.1.flat.ancs x) lbl.ctx l .observe) ∧
      (¬ st.1.flat.Active g → ProvCap st (CoveringDesc st.1 e.guarded) lbl.ctx l .observe)) False

/-- Decidability of `ThreeOK`. -/
instance (L : MutexLayout) (st : SC × SyncReg × ArenaReg) (lbl : Label)
    (st' : SC × SyncReg × ArenaReg) : Decidable (ThreeOK L st lbl st') := by
  unfold ThreeOK; infer_instance

/-- The three checks at every step of a run. -/
def SweepOK (L : MutexLayout) (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) : Prop :=
  ∀ i (h : i < lbls.length), ClosureStep (σ i) lbls[i] (σ (i + 1)) ∧
    ThreeOK L (σ i) lbls[i] (σ (i + 1)) ∧ OtherCapFree (σ i) lbls[i] (σ (i + 1))

/-- Decidability of `SweepOK`. -/
instance (L : MutexLayout) (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) :
    Decidable (SweepOK L σ lbls) := by
  unfold SweepOK; infer_instance

/-- Brief of the complement, tasks 2, 3 and 5, on the `RunFull` traces of the repository: the 24
final amended executions, the trace of legitimate uses, the twins of W-GI and W-RX, the four
witnesses of the exceptions of slice 3 (`ce` among the 24), W-AG, W-AG-J and W-AG′. -/
theorem sweep :
    SweepOK L0 hoσ hoLbls ∧ SweepOK L0 ho2σ ho2Lbls ∧ SweepOK L0 ho3σ ho3Lbls ∧
    SweepOK L0 hojσ hojLbls ∧ SweepOK L0 ho3jσ ho3jLbls ∧ SweepOK L0 lcσ lcLbls ∧
    SweepOK L0 rl0σ rl0Lbls ∧ SweepOK L0 rlσ rlLbls ∧ SweepOK L0 rljσ rljLbls ∧
    SweepOK L0 trσ trLbls ∧ SweepOK L0 trjσ trjLbls ∧ SweepOK L0 s11σ s11Lbls ∧
    SweepOK L0 cvσ cvLbls ∧ SweepOK L0 ceσ ceLbls ∧ SweepOK L0 crσ crLbls ∧
    SweepOK L0 gsTwinσ gsTwinLbls ∧ SweepOK L0 s3σ s3Lbls ∧ SweepOK L0 s10σ s10Lbls ∧
    SweepOK L0 AmendWitness.tsσ AmendWitness.tsLbls ∧
    SweepOK L0 AmendWitness.tiσ AmendWitness.tiLbls ∧
    SweepOK L0 AmendWitness.taσ AmendWitness.taLbls ∧
    SweepOK L0 AmendWitness.tdtσ AmendWitness.tdtLbls ∧
    SweepOK L0 FinalWitness.amσ FinalWitness.amLbls ∧
    SweepOK L0 AmendWitness.tdσ AmendWitness.tdLbls ∧
    SweepOK L0 FullEncap.NonRegression.lvσ FullEncap.NonRegression.lvLbls ∧
    SweepOK L0 Witness.gtσ Witness.gtLbls ∧ SweepOK L0 Witness.rxbσ Witness.rxbLbls ∧
    SweepOK L0 CapacityWitness.frσ CapacityWitness.frLbls ∧
    SweepOK L0 CapacityWitness.exσ CapacityWitness.exLbls ∧
    SweepOK L0 CapacityWitness.tmσ CapacityWitness.tmLbls ∧
    SweepOK L0 agσ agLbls ∧ SweepOK L0 ajσ ajLbls ∧ SweepOK L0 apσ apLbls := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- The kinds whose effect may make a leaf unusable (brief of the complement, task 3, "which
kinds kill leaves"): `endUse` (Spec 1 §69), `free` (§70), `exitFrame` (§73) and `terminate`
(WC5.2 C7). -/
def killKind : Label → Bool
  | .kernel _ (.endUse _) | .kernel _ (.free _ _) | .kernel _ .exit | .terminate _ => true
  | _ => false

/-- At every step of a run, a leaf dies only in a step of one of the kinds of `killKind`. -/
def KillOK (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) : Prop :=
  ∀ i (h : i < lbls.length), ∀ l ∈ List.range (σ i).1.P.length, Dying (σ i).1 (σ (i + 1)).1 l →
    killKind lbls[i] = true

/-- Decidability of `KillOK`. -/
instance (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) : Decidable (KillOK σ lbls) := by
  unfold KillOK; infer_instance

/-- Brief of the complement, task 3, on the traces of `sweep`: no step outside `endUse`, `free`,
`exitFrame` and `terminate` kills a leaf. -/
theorem sweep_kill :
    KillOK hoσ hoLbls ∧ KillOK ho2σ ho2Lbls ∧ KillOK ho3σ ho3Lbls ∧ KillOK hojσ hojLbls ∧
    KillOK ho3jσ ho3jLbls ∧ KillOK lcσ lcLbls ∧ KillOK rl0σ rl0Lbls ∧ KillOK rlσ rlLbls ∧
    KillOK rljσ rljLbls ∧ KillOK trσ trLbls ∧ KillOK trjσ trjLbls ∧ KillOK s11σ s11Lbls ∧
    KillOK cvσ cvLbls ∧ KillOK ceσ ceLbls ∧ KillOK crσ crLbls ∧ KillOK gsTwinσ gsTwinLbls ∧
    KillOK s3σ s3Lbls ∧ KillOK s10σ s10Lbls ∧ KillOK AmendWitness.tsσ AmendWitness.tsLbls ∧
    KillOK AmendWitness.tiσ AmendWitness.tiLbls ∧ KillOK AmendWitness.taσ AmendWitness.taLbls ∧
    KillOK AmendWitness.tdtσ AmendWitness.tdtLbls ∧ KillOK FinalWitness.amσ FinalWitness.amLbls ∧
    KillOK AmendWitness.tdσ AmendWitness.tdLbls ∧
    KillOK FullEncap.NonRegression.lvσ FullEncap.NonRegression.lvLbls ∧
    KillOK Witness.gtσ Witness.gtLbls ∧ KillOK Witness.rxbσ Witness.rxbLbls ∧
    KillOK CapacityWitness.frσ CapacityWitness.frLbls ∧
    KillOK CapacityWitness.exσ CapacityWitness.exLbls ∧
    KillOK CapacityWitness.tmσ CapacityWitness.tmLbls ∧
    KillOK agσ agLbls ∧ KillOK ajσ ajLbls ∧ KillOK apσ apLbls := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- `corpus-spec2-m3.md` v14 §2 terdecies W-AG, step 7 (`c1 : write3(T)` via `x`, index 9): entry
`e` is live before and after, `T` is a protected leaf in the footprint, the recorded grant `g`
(authority 5) is inactive: the step falls in the third case, the capacity of `c1` coming from `x`
(authority 6), a covering descendant of `e`, at `Modify`. -/
theorem W_AG_7_third : (⟨3, some 5⟩ : SyncEntry).Live ab9 ∧ (⟨3, some 5⟩ : SyncEntry).Live ab8 ∧
    TouchesF L0 (agσ 9) (.kernel 1 (.write 6 [3])) 3 ∧ ¬ ab8.flat.Active 5 ∧
    CoveringDesc ab8 3 6 ∧ Attr5 ab8 abReg 1 6 .modify ∧ effective ab8.flat 6 3 = some .modify ∧
    ProvCap (agσ 9) (CoveringDesc ab8 3) 1 3 .modify := by
  decide

end Ern.Concurrency.FullEncap.Sweep
