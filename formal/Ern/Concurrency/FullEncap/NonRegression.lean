import Ern.Concurrency.FullEncap.Witness
import Ern.Concurrency.MutexReal.FinalNonRegression

/-!
# Non-regression of the complete encapsulation

Brief of milestone 4, slice 3, task 3 (`corpus-spec2-m3.md` v13 §2 duodecies, "Usages
légitimes"): every final amended execution of the repository is a `RunFull`; the guard-free forms
are checked by `decide` at each step.
-/

set_option autoImplicit false

namespace Ern.Concurrency.FullEncap.NonRegression

open Ern.MemoryModel Ern.MemoryModel.Access Ern.Concurrency Ern.Concurrency.MutexReal
open Ern.Concurrency.Corpus Ern.Concurrency.Corpus.HandoffEvents Ern.Concurrency.Corpus.MutexEdge
open Ern.Concurrency.Corpus.ResetLockRight Ern.Concurrency.MutexReal.ClassifyWitness
open Ern.Concurrency.MutexReal.NonRegression
open Ern.Concurrency.MutexReal.Witness (s11σ s11Lbls)
open Ern.Concurrency.Corpus.GuardedChainC (lcLbls)
open Ern.Concurrency.Traces (L0)

/-- Brief of slice 3, task 3: every final amended execution of the repository is a `RunFull`:
the 18 traces of `runAmF_traces` (W-HO, W-HO′, W-HO″, W-HO-J, W-HO″-J, `lc_trace`, W-RL₀, W-RL,
W-RL-J, W-TR, W-TR-J, S11, the move by value, the end of use, the release, the twin of W-GS, S3,
S10), the four twins of `twins_runAmF` (`store`, `issue`, `alloc`, `depend` beside the
controller), and the two admitted steps of the final pass (`alloc(owner = M)`, `depend(lock, a)`).
-/
theorem runAmF_traces_full :
    RunFull KF L0 hoσ hoLbls ∧ RunFull KF L0 ho2σ ho2Lbls ∧ RunFull KF L0 ho3σ ho3Lbls ∧
    RunFull KF L0 hojσ hojLbls ∧ RunFull KF L0 ho3jσ ho3jLbls ∧ RunFull KM L0 lcσ lcLbls ∧
    RunFull KM L0 rl0σ rl0Lbls ∧ RunFull KM L0 rlσ rlLbls ∧ RunFull KM L0 rljσ rljLbls ∧
    RunFull KM L0 trσ trLbls ∧ RunFull KM L0 trjσ trjLbls ∧ RunFull KM L0 s11σ s11Lbls ∧
    RunFull KM L0 cvσ cvLbls ∧ RunFull KM L0 ceσ ceLbls ∧ RunFull KM L0 crσ crLbls ∧
    RunFull KM L0 gsTwinσ gsTwinLbls ∧ RunFull KA L0 s3σ s3Lbls ∧ RunFull KM L0 s10σ s10Lbls ∧
    RunFull KM L0 AmendWitness.tsσ AmendWitness.tsLbls ∧
    RunFull KA L0 AmendWitness.tiσ AmendWitness.tiLbls ∧
    RunFull KM L0 AmendWitness.taσ AmendWitness.taLbls ∧
    RunFull KM L0 AmendWitness.tdtσ AmendWitness.tdtLbls ∧
    RunFull KM L0 FinalWitness.amσ FinalWitness.amLbls ∧
    RunFull KM L0 AmendWitness.tdσ AmendWitness.tdLbls := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ :=
    FinalNonRegression.runAmF_traces
  obtain ⟨t1, t2, t3, t4⟩ := FinalNonRegression.twins_runAmF
  exact ⟨runFull_of_run7 h1.1 (by decide), runFull_of_run7 h2.1 (by decide),
    runFull_of_run7 h3.1 (by decide), runFull_of_run7 h4.1 (by decide),
    runFull_of_run7 h5.1 (by decide), runFull_of_run7 h6.1 (by decide),
    runFull_of_run7 h7.1 (by decide), runFull_of_run7 h8.1 (by decide),
    runFull_of_run7 h9.1 (by decide), runFull_of_run7 h10.1 (by decide),
    runFull_of_run7 h11.1 (by decide), runFull_of_run7 h12.1 (by decide),
    runFull_of_run7 h13.1 (by decide), runFull_of_run7 h14.1 (by decide),
    runFull_of_run7 h15.1 (by decide), runFull_of_run7 h16.1 (by decide),
    runFull_of_run7 h17.1 (by decide), runFull_of_run7 h18.1 (by decide),
    runFull_of_run7 t1.1 (by decide), runFull_of_run7 t2.1 (by decide),
    runFull_of_run7 t3.1 (by decide), runFull_of_run7 t4.1 (by decide),
    runFull_of_run7 FinalWitness.alloc_owner_M_admitted.2 (by decide),
    runFull_of_run7 FinalWitness.depend_admitted (by decide)⟩

/-! ## Legitimate uses under a live entry -/

/-- Some entry of the registry is live in the state. -/
def LiveAt (st : SC × SyncReg × ArenaReg) : Prop := ∃ e ∈ st.2.1, e.Live st.1

/-- Decidability of `LiveAt`. -/
instance (st : SC × SyncReg × ArenaReg) : Decidable (LiveAt st) := by
  unfold LiveAt; infer_instance

/-- Statics of the trace of legitimate uses (Spec 1 §47): those of W-GI (block MX without `M′`, the
free arena storage `ST0` with `R1`, `R2`, the arena value `AV0`), and two root leaves of the base
frame, `8` (`Y`, `Init`) and `9` (`P`, `Init`). Root authorities: `0` of `M`, `1` of `T` (held by
`M`), `2` of `ST0`, `3` of `AV0`, `4` of `Y`, `5` of `P`; all but `1` held by frame 0. -/
def lvst : Statics := Witness.gist ++ [((none, none, 0), true), ((none, none, 0), true)]

/-- The statics are well formed (Spec 1 §47). -/
theorem lvst_ok : StaticsOK lvst := by decide

/-- The contract of the trace: `lock` (place 2) and `Y` (place 8) are `SharedMutable`. -/
abbrev KL : K := Corpus.KC [2, 8]

/-- The arena of the trace (Spec 1 §46). -/
def lvE : Arena.ArenaEntry := ⟨4, 7, [5, 6], []⟩

/-- Initial state. -/
def lv0 : SC := SC.ofS3 (S3.init lvst)
/-- `guarded := derive(root_T, Modify, footprint(T))`, authority 6 (O1). -/
def lv1 : SC := lv0.set (deriveEff (lv0.view 0) 1 [3] .modify)
/-- `store(guarded, slot)` (O8). -/
def lv2 : SC := storeEffC lv1 0 6 1
/-- The registry after `newMutex(guarded)` (WC5.2 C13): entry `e`, live from now on. -/
def lvReg : SyncReg := [⟨6, none⟩]
/-- `internal0 := derive(root_ST0, Modify, footprint(ST0))`, authority 7 (O1). -/
def lv3 : SC := lv2.set (deriveEff (lv2.view 0) 2 [5, 6] .modify)
/-- `store(internal0, AV0)` (O8). -/
def lv4 : SC := storeEffC lv3 0 7 7
/-- The arena registry after `newArena(ST0, internal0)` (Spec 1 §76). -/
def lvAr : ArenaReg := [lvE]
/-- `reset(arena0)` (Spec 1 §78): `derive` of `internal0` over the storage (authority 8), then
`release` of it. -/
def lv5 : SC :=
  lv4.set (releaseEff (deriveEff (lv4.view 0) 7 (footprint lv4.P 4) .modify) lv4.A.length)
/-- The arena registry after the reset (Spec 1 §78 effect). -/
def lvAr5 : ArenaReg := lvAr.set 0 (Arena.resetMeta lv4.flat lvE)
/-- `split(root_Y, [[Y]])`, the block is authority 9 (O2). -/
def lv6 : SC := lv5.set (splitEff (lv5.view 0) 4 [[8]])
/-- `read3(Y)` via the block (O9): the state is unchanged. -/
def lv7 : SC := lv6.set (lv6.view 0)
/-- `writeShared(Y)` via the block (O11). -/
def lv8 : SC := lv7.set (write3Eff (lv7.view 0) [8])
/-- `release(block)` (O3). -/
def lv9 : SC := lv8.set (releaseEff (lv8.view 0) 9)
/-- `pin(Y)` (O15): obligation 0. -/
def lv10 : SC := lv9.set (pinEff (lv9.view 0) 8)
/-- `unpin(0)` (O16). -/
def lv11 : SC := lv10.set (unpinEff (lv10.view 0) 0)
/-- `alloc(provider = P, owner = Y, one leaf)` (O14): place 10, root authority 10 held by `Y`. -/
def lv12 : SC := lv11.set (allocEff (lv11.view 0) 8 [(none, 0)])
/-- `free(10)` (O13). -/
def lv13 : SC := lv12.set (freeEff (lv12.view 0) 10)
/-- `endUse(Y)` (O12). -/
def lv14 : SC := lv13.set (endUseEff (lv13.view 0) 8)

/-- The labels of the trace of legitimate uses. -/
def lvLbls : List Label :=
  [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 6 1), .newMutex 0 6,
   .kernel 0 (.derive 2 [5, 6] .modify), .kernel 0 (.store 7 7), .newArena 0 4 7, .reset 0 0,
   .kernel 0 (.split 4 [[8]]), .kernel 0 (.read 9 [8]), .kernel 0 (.writeShared 9 [8]),
   .kernel 0 (.release 9), .kernel 0 (.pin 8), .kernel 0 (.unpin 0),
   .kernel 0 (.alloc 9 8 [(none, 0)]), .kernel 0 (.free 10 0), .kernel 0 (.endUse 8)]

/-- The named states of the trace of legitimate uses. -/
def lvσ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(lv0, [], []), (lv1, [], []), (lv2, [], []), (lv2, lvReg, []), (lv3, lvReg, []),
    (lv4, lvReg, []), (lv4, lvReg, lvAr), (lv5, lvReg, lvAr5), (lv6, lvReg, lvAr5),
    (lv7, lvReg, lvAr5), (lv8, lvReg, lvAr5), (lv9, lvReg, lvAr5), (lv10, lvReg, lvAr5),
    (lv11, lvReg, lvAr5), (lv12, lvReg, lvAr5), (lv13, lvReg, lvAr5), (lv14, lvReg, lvAr5)].getD i
    (lv14, lvReg, lvAr5)

/-- The trace of legitimate uses from the initial state, each step admitted by `Encap5R`. -/
theorem lv_steps : Steps5R KL L0
    [(lv0, [], []), (lv1, [], []), (lv2, [], []), (lv2, lvReg, []), (lv3, lvReg, []),
      (lv4, lvReg, []), (lv4, lvReg, lvAr), (lv5, lvReg, lvAr5), (lv6, lvReg, lvAr5),
      (lv7, lvReg, lvAr5), (lv8, lvReg, lvAr5), (lv9, lvReg, lvAr5), (lv10, lvReg, lvAr5),
      (lv11, lvReg, lvAr5), (lv12, lvReg, lvAr5), (lv13, lvReg, lvAr5), (lv14, lvReg, lvAr5)]
    lvLbls :=
  .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
  .cons (by decide) (.kernel ⟨by decide, .ok (by decide)⟩) <|
  .cons (by decide) (.newMutex ⟨by decide, by decide, rfl⟩) <|
  .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
  .cons (by decide) (.kernel ⟨by decide, .ok (by decide)⟩) <|
  .cons (by decide) (.newArena ⟨by decide, .ok (by decide)⟩) <|
  .cons (by decide) (.reset ⟨by decide, _, .ok (E := lvE) rfl (.ok (by decide)) (.ok (by decide))
    (by decide), rfl⟩) <|
  .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
  .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
  .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
  .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
  .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
  .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
  .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide) trivial, rfl⟩) <|
  .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
  .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) .nil

/-- Brief of slice 3, task 3: the trace of legitimate uses is a `RunFull` from the initial state,
and entry `e` is live before each step from `derive(root_ST0)` on: `derive`, `store`, `newArena`,
`reset`, `split`, `read3`, `writeShared`, `release`, `pin`, `unpin`, `alloc`, `free`, `endUse`
are `ok` and admitted under a live entry, their rights resting on root authorities of `f0` or on
the split block (WC5.2 C22 item 6: another valid chain suffices). -/
theorem lv_full : lvσ 0 = (SC.ofS3 (S3.init lvst), [], []) ∧ RunFull KL L0 lvσ lvLbls ∧
    ∀ i ∈ List.range lvLbls.length, 3 ≤ i → LiveAt (lvσ i) := by
  refine ⟨rfl, runFull_of_run7 (run7_of_run5R (lv_steps.run _) (by decide)) (by decide), ?_⟩
  decide

/-- Brief of slice 3, task 3: the other kinds with a right premise have an `ok` step admitted
under a live entry in the `RunFull` traces above: `transfer` (S10, `transfer(M, M′)` under the
grant), `depend` (twin of the `depend` witness), by-value `spawn` (the move of the mutex), `issue`
(S3, under the grant of `e2`), `acquire`, `write3`, `unlock`, `resetLock` (W-RL), `newMutex` (W-RX,
twin B: `newMutex(guarded)` while `e_n` is live). -/
theorem live_uses :
    s10Lbls[6]? = some (.kernel 0 (.transfer 0 7)) ∧ LiveAt (s10σ 6) ∧
    AmendWitness.tdtLbls[4]? = some (.kernel 0 (.depend 6 4)) ∧ LiveAt (AmendWitness.tdtσ 4) ∧
    cvLbls[3]? = some (.spawnVal 0 [] mLocals [(0, 7)]) ∧ LiveAt (cvσ 3) ∧
    s3Lbls[9]? = some (.issue 1 0 [5] 8) ∧ LiveAt (s3σ 9) ∧
    rlLbls[5]? = some (.acquire 1 0) ∧ LiveAt (rlσ 5) ∧
    rlLbls[6]? = some (.kernel 1 (.write 5 [3])) ∧ LiveAt (rlσ 6) ∧
    rlLbls[7]? = some (.unlock 1 0) ∧ LiveAt (rlσ 7) ∧
    rlLbls[9]? = some (.resetLock 0 0) ∧ LiveAt (rlσ 9) ∧
    Witness.rxbLbls[5]? = some (.newMutex 0 4) ∧ LiveAt (Witness.rxbσ 5) :=
  ⟨rfl, by decide, rfl, by decide, rfl, by decide, rfl, by decide, rfl, by decide, rfl, by decide,
    rfl, by decide, rfl, by decide, rfl, by decide⟩

/-- Brief of slice 3, task 3, raw `deriveSync`: no `ok` raw `deriveSync` step is admitted by
`Encap` (WC5.2 C22 item 2), so no step of this kind exists under any encapsulation built on it:
its authorization names the `guarded` of a live entry (C14 item 1, C15 item 3), which C22 item 2
excludes. -/
theorem deriveSync_never_admitted {k : K} {L : MutexLayout} {c g : Nat}
    {st st' : SC × SyncReg × ArenaReg} (h : LStep k L (.deriveSync c g) st st') :
    ¬ Encap L (st.1, st.2.1) (.deriveSync c g) := by
  cases h with
  | deriveSync hd =>
    obtain ⟨e, he, hg, hl, -⟩ := (Guarded.ok_iff.1 hd.2).1.authorized
    exact fun hx => hx e he hl hg.symm

end Ern.Concurrency.FullEncap.NonRegression
