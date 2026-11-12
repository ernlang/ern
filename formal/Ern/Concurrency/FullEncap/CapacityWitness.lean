import Ern.Concurrency.FullEncap.Capacity
import Ern.Concurrency.FullEncap.Witness

/-!
# Witnesses of the exceptions of task 4

Brief of milestone 4, slice 3, task 4: each exception to "`cap5` at least the mode required on
every touched leaf" is stated with a witness. The only exception is the leaves that die with the
step outside the place it names (`endUse`, `free`), or with the frame or context (`exitFrame`,
`terminate`): their clauses (Spec 1 §69.1, §70.3, §73; WC5.2 C7) require no mode on them. In
each witness, a `RunFull` step from the initial state touches such a leaf, protected by a live
entry that dies with the step, on which the context has no `cap5` at all (WC5.2 C43: the live
`guarded` is attributable to no context, and its origin has no effective mode left).
-/

set_option autoImplicit false

namespace Ern.Concurrency.FullEncap.CapacityWitness

open Ern.MemoryModel Ern.MemoryModel.Access Ern.Concurrency Ern.Concurrency.MutexReal
open Ern.Concurrency.Corpus Ern.Concurrency.MutexReal.ClassifyWitness
open Ern.Concurrency.FullEncap.Witness (instDecidableEncap5R)
open Ern.Concurrency.Traces (L0)

/-! ## `endUse` -/

/-- Brief of slice 3, task 4, exception for `endUse`: from `MX₃`, `c0 : endUse(M)` is a `RunFull`
step (`endUse_ends`); it touches the leaf `t` (place 3) of `T`, owned by `M`, which dies with `M`
but is not a leaf of `M`; `c0` has no `cap5` on it, and entry `e` dies with the step. -/
theorem exc_endUse : RunFull KM L0 ceσ ceLbls ∧
    TouchesF L0 (ceσ 3) (.kernel 0 (.endUse 0)) 3 ∧ isLeaf x2.P 3 ∧ 3 < x2.P.length ∧
    3 ∉ footprint x2.P 0 ∧ cap5 x2 regX 0 3 = none ∧ (⟨3, none⟩ : SyncEntry).Live x2 ∧
    ¬ (⟨3, none⟩ : SyncEntry).Live ce1 :=
  ⟨runFull_of_run7 (run7_of_run5R endUse_ends.2.1 (by decide)) (by decide), by decide, by decide,
    by decide, by decide, by decide, by decide, by decide⟩

/-! ## `free` -/

/-- Statics: `0` a root leaf `Y`, `1` a root leaf `P` (the provider), both `Init`. Root
authorities: `0` of `Y`, `1` of `P` (frame 0). -/
def fst : Statics := [((none, none, 0), true), ((none, none, 0), true)]

/-- The statics are well formed (Spec 1 §47). -/
theorem fst_ok : StaticsOK fst := by decide

/-- The contract: the controller `lock_r` (place 4) is `SharedMutable`. -/
abbrev KF4 : K := Corpus.KC [4]

/-- Initial state. -/
def fr0 : SC := SC.ofS3 (S3.init fst)
/-- `alloc(provider = P, owner = Y, R = {slot_r, lock_r})` (O14): places 2, 3, 4; root `2` held
by `Y`. -/
def fr1 : SC := fr0.set (allocEff (fr0.view 0) 0 [(none, 0), (some 2, 0), (some 2, 0)])
/-- `alloc(provider = P, owner = R, T_r)` (O14): place 5; root `3` held by `R`. -/
def fr2 : SC := fr1.set (allocEff (fr1.view 0) 2 [(none, 0)])
/-- `guarded_r := derive(root_T_r, Modify, footprint(T_r))`, authority 4 (O1). -/
def fr3 : SC := fr2.set (deriveEff (fr2.view 0) 3 [5] .modify)
/-- `store(guarded_r, slot_r)` (O8). -/
def fr4 : SC := storeEffC fr3 0 4 3
/-- `write3(lock_r)` via `root_R` (O10): `lock_r` becomes `Init` (WC5.2 C13 item 10). -/
def fr5 : SC := fr4.set (write3Eff (fr4.view 0) [4])
/-- The registry after `newMutex(guarded_r)` (WC5.2 C13). -/
def frReg : SyncReg := [⟨4, none⟩]
/-- `free(R)` (O13). -/
def fr6 : SC := fr5.set (freeEff (fr5.view 0) 2)

/-- The labels of the `free` witness. -/
def frLbls : List Label :=
  [.kernel 0 (.alloc 1 0 [(none, 0), (some 2, 0), (some 2, 0)]),
   .kernel 0 (.alloc 1 2 [(none, 0)]), .kernel 0 (.derive 3 [5] .modify), .kernel 0 (.store 4 3),
   .kernel 0 (.write 2 [4]), .newMutex 0 4, .kernel 0 (.free 2 0)]

/-- The named states of the `free` witness. -/
def frσ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(fr0, [], []), (fr1, [], []), (fr2, [], []), (fr3, [], []), (fr4, [], []), (fr5, [], []),
    (fr5, frReg, []), (fr6, frReg, [])].getD i (fr6, frReg, [])

/-- Brief of slice 3, task 4, exception for `free`: a mutex is built inside allocated storage `R`
whose protected root `T_r` is owned by `R`; `c0 : free(R)` is a `RunFull` step from the initial
state; it touches the leaf `T_r` (place 5), which dies with `R` but is not a leaf of `R`; `c0` has
no `cap5` on it, and the entry dies with the step. -/
theorem exc_free : frσ 0 = (SC.ofS3 (S3.init fst), [], []) ∧ RunFull KF4 L0 frσ frLbls ∧
    TouchesF L0 (frσ 6) (.kernel 0 (.free 2 0)) 5 ∧ isLeaf fr5.P 5 ∧ 5 < fr5.P.length ∧
    5 ∉ footprint fr5.P 2 ∧ cap5 fr5 frReg 0 5 = none ∧ (⟨4, none⟩ : SyncEntry).Live fr5 ∧
    ¬ (⟨4, none⟩ : SyncEntry).Live fr6 := by
  have hs : Steps5R KF4 L0 [(fr0, [], []), (fr1, [], []), (fr2, [], []), (fr3, [], []),
      (fr4, [], []), (fr5, [], []), (fr5, frReg, []), (fr6, frReg, [])] frLbls :=
    .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide) trivial, rfl⟩) <|
    .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide) trivial, rfl⟩) <|
    .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons (by decide) (.kernel ⟨by decide, .ok (by decide)⟩) <|
    .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons (by decide) (.newMutex ⟨by decide, by decide, rfl⟩) <|
    .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) .nil
  exact ⟨rfl, runFull_of_run7 (run7_of_run5R (hs.run _) (by decide)) (by decide), by decide,
    by decide, by decide, by decide, by decide, by decide, by decide⟩

/-! ## `exitFrame` -/

/-- Statics: `0` a root leaf `Z`, `Init`; root authority `0` (frame 0). -/
def est : Statics := [((none, none, 0), true)]

/-- The statics are well formed (Spec 1 §47). -/
theorem est_ok : StaticsOK est := by decide

/-- The contract: the controller `lock1` (place 3) is `SharedMutable`. -/
abbrev KE3 : K := Corpus.KC [3]

/-- The locals of the callee: the mutex value `M1` (place 1) with fields `slot1` (2), `lock1` (3),
and a root leaf `X1` (4); roots `1` (of `M1`) and `2` (of `X1`), held by the new frame. -/
def eLocals : LocalShape := [(none, 0), (some 1, 0), (some 1, 0), (none, 0)]

/-- Initial state. -/
def ex0 : SC := SC.ofS3 (S3.init est)
/-- `c0 : enterFrame([], eLocals)` (O6): frame 1. -/
def ex1 : SC := enterEffC ex0 0 [] eLocals
/-- `guarded1 := derive(root_X1, Modify, {X1})`, authority 3 (O1). -/
def ex2 : SC := ex1.set (deriveEff (ex1.view 0) 2 [4] .modify)
/-- `store(guarded1, slot1)` (O8). -/
def ex3 : SC := storeEffC ex2 0 3 2
/-- `write3(lock1)` via `root_M1` (O10). -/
def ex4 : SC := ex3.set (write3Eff (ex3.view 0) [3])
/-- The registry after `newMutex(guarded1)` (WC5.2 C13). -/
def exReg : SyncReg := [⟨3, none⟩]
/-- `c0 : exitFrame` (O7). -/
def ex5 : SC := exitEffC ex4 0

/-- The labels of the `exitFrame` witness. -/
def exLbls : List Label :=
  [.kernel 0 (.enter [] eLocals), .kernel 0 (.derive 2 [4] .modify), .kernel 0 (.store 3 2),
   .kernel 0 (.write 1 [3]), .newMutex 0 3, .kernel 0 .exit]

/-- The named states of the `exitFrame` witness. -/
def exσ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(ex0, [], []), (ex1, [], []), (ex2, [], []), (ex3, [], []), (ex4, [], []), (ex4, exReg, []),
    (ex5, exReg, [])].getD i (ex5, exReg, [])

/-- Brief of slice 3, task 4, exception for `exitFrame`: a mutex is built in the locals of a
callee frame, its protected root `X1` a separate local; `c0 : exitFrame` is a `RunFull` step from
the initial state; it touches the leaf `X1` (place 4), which dies with the frame; `c0` has no
`cap5` on it, and the entry dies with the step. -/
theorem exc_exit : exσ 0 = (SC.ofS3 (S3.init est), [], []) ∧ RunFull KE3 L0 exσ exLbls ∧
    TouchesF L0 (exσ 5) (.kernel 0 .exit) 4 ∧ isLeaf ex4.P 4 ∧ 4 < ex4.P.length ∧
    cap5 ex4 exReg 0 4 = none ∧ (⟨3, none⟩ : SyncEntry).Live ex4 ∧
    ¬ (⟨3, none⟩ : SyncEntry).Live ex5 := by
  have hs : Steps5R KE3 L0 [(ex0, [], []), (ex1, [], []), (ex2, [], []), (ex3, [], []),
      (ex4, [], []), (ex4, exReg, []), (ex5, exReg, [])] exLbls :=
    .cons (by decide) (.kernel ⟨by decide, .ok (by decide)⟩) <|
    .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons (by decide) (.kernel ⟨by decide, .ok (by decide)⟩) <|
    .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons (by decide) (.newMutex ⟨by decide, by decide, rfl⟩) <|
    .cons (by decide) (.kernel ⟨by decide, .ok (by decide)⟩) .nil
  exact ⟨rfl, runFull_of_run7 (run7_of_run5R (hs.run _) (by decide)) (by decide), by decide,
    by decide, by decide, by decide, by decide, by decide⟩

/-! ## `terminate` -/

/-- `c0 : spawn([], eLocals)` (WC5.2 C4): context 1, initial frame 1, the same locals. -/
def tm1 : SC := spawnEff ex0 0 [] eLocals
/-- `c1 : guarded1 := derive(root_X1, Modify, {X1})`, authority 3 (O1). -/
def tm2 : SC := tm1.set (deriveEff (tm1.view 1) 2 [4] .modify)
/-- `c1 : store(guarded1, slot1)` (O8). -/
def tm3 : SC := storeEffC tm2 1 3 2
/-- `c1 : write3(lock1)` via `root_M1` (O10). -/
def tm4 : SC := tm3.set (write3Eff (tm3.view 1) [3])
/-- `c1 : terminate` (WC5.2 C7). -/
def tm5 : SC := termEffC tm4 1

/-- The labels of the `terminate` witness. -/
def tmLbls : List Label :=
  [.spawn 0 [] eLocals, .kernel 1 (.derive 2 [4] .modify), .kernel 1 (.store 3 2),
   .kernel 1 (.write 1 [3]), .newMutex 1 3, .terminate 1]

/-- The named states of the `terminate` witness. -/
def tmσ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(ex0, [], []), (tm1, [], []), (tm2, [], []), (tm3, [], []), (tm4, [], []), (tm4, exReg, []),
    (tm5, exReg, [])].getD i (tm5, exReg, [])

/-- Brief of slice 3, task 4, exception for `terminate`: the same mutex built by a child context
`c1` in its initial frame; `c1 : terminate` is a `RunFull` step from the initial state; it
touches the leaf `X1` (place 4), which dies with the context; `c1` has no `cap5` on it, and the
entry dies with the step. -/
theorem exc_terminate : tmσ 0 = (SC.ofS3 (S3.init est), [], []) ∧ RunFull KE3 L0 tmσ tmLbls ∧
    TouchesF L0 (tmσ 5) (.terminate 1) 4 ∧ isLeaf tm4.P 4 ∧ 4 < tm4.P.length ∧
    cap5 tm4 exReg 1 4 = none ∧ (⟨3, none⟩ : SyncEntry).Live tm4 ∧
    ¬ (⟨3, none⟩ : SyncEntry).Live tm5 := by
  have hs : Steps5R KE3 L0 [(ex0, [], []), (tm1, [], []), (tm2, [], []), (tm3, [], []),
      (tm4, [], []), (tm4, exReg, []), (tm5, exReg, [])] tmLbls :=
    .cons (by decide) (.spawn ⟨by decide, .ok (by decide)⟩) <|
    .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons (by decide) (.kernel ⟨by decide, .ok (by decide)⟩) <|
    .cons (by decide) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons (by decide) (.newMutex ⟨by decide, by decide, rfl⟩) <|
    .cons (by decide) (.terminate ⟨by decide, .ok (by decide)⟩) .nil
  exact ⟨rfl, runFull_of_run7 (run7_of_run5R (hs.run _) (by decide)) (by decide), by decide,
    by decide, by decide, by decide, by decide, by decide⟩

end Ern.Concurrency.FullEncap.CapacityWitness
