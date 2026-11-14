import Ern.Concurrency.FullEncap.HandoffExtFrontier
import Ern.Concurrency.FullEncap.HandoffExtWitness
import Ern.Concurrency.FullEncap.Protected

/-!
# Sweep of the extended handoff on the `RunFull` traces

Brief of milestone 4, slice 4, task 5, "Balayage" (`formal/reports/spec2-m4-handoff-ext.md`). For
each `RunFull` trace of the repository, the witnesses of this slice included, `SweepExt` lists
the extended exclusive pairs `(i, j, l)`, their frontier `r`, and whether strict `hb` holds from
`r` to `j` (extended handoff order) and from `i` to `j` (no extended race). The list is complete
(`sweepExt_complete`): every extended exclusive pair of the trace is in it. The facts of the
corpus (`corpus-spec2-m3.md` v15 §2 quaterdecies) are the expected ones; for the other traces the
lists are results of the model, decided by `decide`.
-/

set_option autoImplicit false

namespace Ern.Concurrency.FullEncap.HandoffExtSweep

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

/-- The sweep of a trace (brief, task 5): every extended exclusive pair with `i`, `j` steps of the
trace and `l` a place of its last state is in the list `T`; each entry `(i, j, l, r, a, b)` of `T`
is an extended exclusive pair whose frontier is `r`, with strict `hb(r, j)` exactly when `a`
(extended handoff order) and strict `hb(i, j)` exactly when `b` (no extended race). -/
def SweepExt (k : K) (L : MutexLayout) (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label)
    (T : List (Nat × Nat × Nat × Nat × Bool × Bool)) : Prop :=
  (∀ i ∈ List.range lbls.length, ∀ j ∈ List.range lbls.length,
    ∀ l ∈ List.range (σ lbls.length).1.P.length,
      ExtPair k L σ lbls i j l → (i, j, l) ∈ T.map fun e => (e.1, e.2.1, e.2.2.1)) ∧
  ∀ e ∈ T, ExtPair k L σ lbls e.1 e.2.1 e.2.2.1 ∧
    IsFrontier k σ lbls e.1 e.2.1 e.2.2.1 e.2.2.2.1 ∧
    (HBS σ L lbls (.step e.2.2.2.1) (.step e.2.1) ↔ e.2.2.2.2.1 = true) ∧
    (HBS σ L lbls (.step e.1) (.step e.2.1) ↔ e.2.2.2.2.2 = true)

/-- Decidability of `SweepExt`. -/
instance (k : K) [DecidablePred k.SharedMutable] (L : MutexLayout)
    (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label)
    (T : List (Nat × Nat × Nat × Nat × Bool × Bool)) : Decidable (SweepExt k L σ lbls T) := by
  unfold SweepExt; infer_instance

/-- On a `RunFull` from the initial state, the list of `SweepExt` is complete: every extended
exclusive pair is in it, its leaf being a place of the last state (`touch_lt_run`,
`len_mono_run`). -/
theorem sweepExt_complete {k : K} {L : MutexLayout} {statics : Statics}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} (hdd : DDSound k)
    (hstat : StaticsOK statics) (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], []))
    (h : RunFull k L σ lbls) {T : List (Nat × Nat × Nat × Nat × Bool × Bool)}
    (hs : SweepExt k L σ lbls T) {i j l : Nat} (hp : ExtPair k L σ lbls i j l) :
    (i, j, l) ∈ T.map fun e => (e.1, e.2.1, e.2.2.1) := by
  obtain ⟨hij, hj, -, -, htj, -⟩ := hp.out
  have hl := Nat.lt_of_lt_of_le (touch_lt_run hdd hstat h0 h hj htj)
    (len_mono_run hdd hstat h0 h (Nat.succ_le_of_lt hj) (Nat.le_refl _))
  exact hs.1 i (List.mem_range.2 (Nat.lt_trans hij hj)) j (List.mem_range.2 hj) l
    (List.mem_range.2 hl) hp

/-- Brief, task 5, sweep, on the traces of the event pass and of the mutex edge: the extended
exclusive pairs, their frontier, the strict `hb` from the frontier and from the first member
(`SweepExt`). -/
theorem sweep_ext_1 :
    SweepExt KF L0 hoσ hoLbls
      [(2, 4, 1, 3, false, false), (2, 4, 2, 3, false, false)] ∧
    SweepExt KF L0 ho2σ ho2Lbls
      [(3, 5, 0, 4, false, false)] ∧
    SweepExt KF L0 ho3σ ho3Lbls
      [(4, 9, 0, 5, false, false)] ∧
    SweepExt KF L0 hojσ hojLbls
      [(2, 6, 1, 3, true, true), (2, 6, 2, 3, true, true)] ∧
    SweepExt KF L0 ho3jσ ho3jLbls
      [(4, 11, 0, 5, true, true)] ∧
    SweepExt KM L0 lcσ lcLbls
      [(4, 7, 2, 5, true, true), (4, 9, 2, 5, true, true), (8, 11, 4, 9, true, true)] ∧
    SweepExt KM L0 rl0σ rl0Lbls
      [(2, 5, 2, 3, true, true), (2, 7, 2, 3, true, true), (6, 10, 3, 7, true, true)] ∧
    SweepExt KM L0 rlσ rlLbls
      [(2, 5, 2, 3, true, true), (2, 7, 2, 3, true, true), (6, 11, 3, 7, false, false)] ∧
    SweepExt KM L0 rljσ rljLbls
      [(2, 5, 2, 3, true, true), (2, 7, 2, 3, true, true), (6, 13, 3, 7, true, true)] ∧
    SweepExt KM L0 trσ trLbls
      [(2, 5, 2, 3, true, true), (2, 7, 2, 3, true, true), (5, 9, 2, 8, false, false),
       (6, 11, 3, 7, false, false), (7, 9, 2, 8, false, false)] ∧
    SweepExt KM L0 trjσ trjLbls
      [(2, 5, 2, 3, true, true), (2, 7, 2, 3, true, true), (5, 11, 2, 8, true, true),
       (6, 13, 3, 7, true, true), (7, 11, 2, 8, true, true)] ∧
    SweepExt KM L0 s11σ s11Lbls
      [(2, 7, 2, 3, true, true)] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- Brief, task 5, sweep, on the final amended executions: the extended exclusive pairs, their
frontier, the strict `hb` from the frontier and from the first member (`SweepExt`). -/
theorem sweep_ext_2 :
    SweepExt KM L0 cvσ cvLbls
      [] ∧
    SweepExt KM L0 ceσ ceLbls
      [] ∧
    SweepExt KM L0 crσ crLbls
      [] ∧
    SweepExt KM L0 gsTwinσ gsTwinLbls
      [] ∧
    SweepExt KA L0 s3σ s3Lbls
      [(5, 8, 2, 6, true, true), (7, 9, 8, 7, true, true)] ∧
    SweepExt KM L0 s10σ s10Lbls
      [] ∧
    SweepExt KM L0 AmendWitness.tsσ AmendWitness.tsLbls
      [] ∧
    SweepExt KA L0 AmendWitness.tiσ AmendWitness.tiLbls
      [] ∧
    SweepExt KM L0 AmendWitness.taσ AmendWitness.taLbls
      [] ∧
    SweepExt KM L0 AmendWitness.tdtσ AmendWitness.tdtLbls
      [] ∧
    SweepExt KM L0 FinalWitness.amσ FinalWitness.amLbls
      [] ∧
    SweepExt KM L0 AmendWitness.tdσ AmendWitness.tdLbls
      [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- Brief, task 5, sweep, on the witnesses of slice 3 and the first replayed traces: the extended
exclusive pairs, their frontier, the strict `hb` from the frontier and from the first member
(`SweepExt`). -/
theorem sweep_ext_3 :
    SweepExt FullEncap.NonRegression.KL L0 FullEncap.NonRegression.lvσ
      FullEncap.NonRegression.lvLbls
      [] ∧
    SweepExt KM L0 Witness.gtσ Witness.gtLbls
      [] ∧
    SweepExt Witness.KX L0 Witness.rxbσ Witness.rxbLbls
      [] ∧
    SweepExt CapacityWitness.KF4 L0 CapacityWitness.frσ CapacityWitness.frLbls
      [] ∧
    SweepExt CapacityWitness.KE3 L0 CapacityWitness.exσ CapacityWitness.exLbls
      [] ∧
    SweepExt CapacityWitness.KE3 L0 CapacityWitness.tmσ CapacityWitness.tmLbls
      [(0, 2, 2, 0, true, true), (0, 3, 3, 0, true, true), (0, 4, 3, 0, true, true),
       (0, 5, 2, 0, true, true), (0, 5, 3, 0, true, true), (0, 5, 4, 0, true, true)] ∧
    SweepExt KM L0 agσ agLbls
      [(9, 13, 3, 10, false, false)] ∧
    SweepExt KM L0 ajσ ajLbls
      [(9, 15, 3, 10, true, true)] ∧
    SweepExt KM L0 apσ apLbls
      [(9, 13, 3, 11, true, true)] ∧
    SweepExt KM L0 Replay.wrσ Replay.wrLbls
      [] ∧
    SweepExt KM L0 Replay.cgσ Replay.cgLbls
      [] ∧
    SweepExt KA L0 Replay.s3fσ Replay.s3fLbls
      [(5, 8, 2, 6, true, true), (5, 10, 2, 6, true, true), (7, 9, 8, 7, true, true)] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- Brief, task 5, sweep, on the replayed traces and the trace of the refutation of slice 3: the
extended exclusive pairs, their frontier, the strict `hb` from the frontier and from the first
member (`SweepExt`). -/
theorem sweep_ext_4 :
    SweepExt K0 L0 Replay.s4σ Replay.s4Lbls
      [] ∧
    SweepExt K9 L0 Replay.s9σ Replay.s9Lbls
      [] ∧
    SweepExt K0 L0 Replay.mtσ Replay.mtLbls
      [] ∧
    SweepExt K0 L0 Replay.dtσ Replay.dtLbls
      [] ∧
    SweepExt K0 L0 Replay.tAσ
      [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 4 1), .newMutex 0 4,
      .kernel 0 (.transfer 0 4)]
      [] ∧
    SweepExt K0 L0 Replay.tBσ
      [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 4 1), .newMutex 0 4,
      .acquire 0 0, .kernel 0 (.transfer 0 4)]
      [] ∧
    SweepExt K0 L0 Replay.kmσ Replay.kmLbls
      [] ∧
    SweepExt K0 L0 Replay.ksσ Replay.ksLbls
      [] ∧
    SweepExt KW L0 Replay.tbσ Replay.tbLbls
      [] ∧
    SweepExt K0 L0 Replay.saσ Replay.saLbls
      [] ∧
    SweepExt KM L0 Protected.abσ Protected.abLbls
      [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- Brief, task 5, sweep, on the witnesses of this slice: the extended exclusive pairs, their
frontier, the strict `hb` from the frontier and from the first member (`SweepExt`). -/
theorem sweep_ext_5 :
    SweepExt KF L0 HandoffExtWitness.htσ HandoffExtWitness.htLbls
      [(2, 4, 0, 3, false, false)] ∧
    SweepExt KF L0 HandoffExtWitness.htjσ HandoffExtWitness.htjLbls
      [(2, 6, 0, 3, true, true)] ∧
    SweepExt KF L0 HandoffExtWitness.hsσ HandoffExtWitness.hsLbls
      [(3, 5, 0, 4, false, false)] ∧
    SweepExt KF L0 HandoffExtWitness.hsjσ HandoffExtWitness.hsjLbls
      [(3, 7, 0, 4, true, true)] ∧
    SweepExt KF L0 HandoffExtWitness.hxσ HandoffExtWitness.hxLbls
      [(0, 4, 0, 3, true, true), (1, 4, 0, 3, true, true), (4, 6, 0, 5, false, false)] ∧
    SweepExt KF L0 HandoffExtWitness.hxjσ HandoffExtWitness.hxjLbls
      [(0, 4, 0, 3, true, true), (1, 4, 0, 3, true, true), (4, 8, 0, 5, true, true)] ∧
    SweepExt K0 L0 HandoffExtWitness.svσ HandoffExtWitness.svLbls
      [(4, 5, 4, 4, true, true)] ∧
    SweepExt KM L0 HandoffExtWitness.crjσ HandoffExtWitness.crjLbls
      [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end Ern.Concurrency.FullEncap.HandoffExtSweep
