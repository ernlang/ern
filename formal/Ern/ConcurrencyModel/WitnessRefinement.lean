import Ern.ConcurrencyModel.RunRefinement
import Ern.ConcurrencyModel.WitnessMutex

/-!
# Witness: a translated run with two contexts (theorem 9, non-vacuity)

A witness does not replace any proof: it shows that the obligations of the steps of a translated
run (`TransRun`) can be met on a run with several contexts; it does not show that they are for
every run.

The run, from the initial state of Spec 1 §47 with the statics of the reference mutex and a value
`v`: context 0 builds the reference mutex (C13), then creates context 1 by the by-value composite
(C5), yielding `o` and moving `v` into the fresh local `d` of the child; context 1 writes `d`
(Spec 1 §67), acquires the mutex (C16), reads the controller by `readShared` (C37), unlocks it
(C17) and terminates (C7). The parameters are concrete, as in the runs of the memory model checked
by evaluation (`Refinement.Runs.piOf`, `obR`, `obW`).
-/

namespace Ern.ConcurrencyModel

open Ern.MemoryModel Ern.MemoryModel.Access Ern.MemoryModel.Refinement
open Ern.MemoryModel.Refinement.Runs

section Dec

variable (k : K) [∀ r r', Decidable (k.DeclaredDisjoint r r')] [DecidablePred k.SharedMutable]
  [DecidablePred k.Pinned] [DecidablePred k.ExternalDone] [DecidablePred k.Deallocable]
  [∀ p a, Decidable (k.FreeCompat p a)] [∀ p ls s, Decidable (k.Satisfiable p ls s)]
  {Ty : Type} (C : Nat → Nat → Prop) [DecidableRel C] (ObR : Machine.ReadOblSpec Ty)
  (ObW : Machine.WriteOblSpec Ty) [∀ s o, Decidable (Obl ObR ObW s o)] (π : Params Ty)
  (w : WriteRepr)

/-- Decidability of the obligations of a labelled step (Spec 1 §20.3, §82). -/
instance stepOblCDec (lbl : Label) (st : SC × SyncReg × ArenaReg) (m : Machine.State) :
    Decidable (StepOblC k C ObR ObW π w lbl st m) := by
  cases lbl <;> unfold StepOblC <;> infer_instance

end Dec

/-! ## The abstract run -/

/-- Statics (Spec 1 §47): those of the reference mutex (`mutexStatics`: `0` the mutex value `M`,
`1` its field `slot`, `2` its field `lock`, `3` the protected root `T` owned by `M`), and `4` a root
value `v`, `Init`, of frame 0. Root authorities: `0` of `M`, `1` of `T` (held by `M`), `2` of
`v`. -/
def wStatics : Statics :=
  [((none, none, 0), false), ((some 0, none, 0), false), ((some 0, none, 0), true),
   ((none, some 0, 0), true), ((none, none, 0), true)]

/-- Initial single-context state (Spec 1 §47). -/
def w0 : SC := SC.ofS3 (S3.init wStatics)
/-- `guarded := derive(root_T, Modify, footprint(T))`, authority 3 (O1). -/
def w1 : SC := w0.set (deriveEff (w0.view 0) 1 [3] .modify)
/-- `store(guarded, slot)` (O8). -/
def w2 : SC := storeEffC w1 0 3 1
/-- `o := derive(root_M, Observe, {slot, lock})`, authority 4 (O1). -/
def w3 : SC := w2.set (deriveEff (w2.view 0) 0 [1, 2] .observe)
/-- By-value `spawn` of context 1 (C5): parameter `o` yielded, `v` moved into the fresh local `d`
(place 5, root authority 5) of the initial frame 1. -/
def w4 : SC := spawnValEff w3 0 [4] [(none, 0)] [(4, 5)]
/-- `write(root_d, {d})` by context 1 (O10). -/
def w5 : SC := w4.set (write3Eff (w4.view 1) [5])
/-- `acquire(e)` by context 1 (C16): the grant, authority 6, held by frame 1. -/
def w6 : SC := deriveSyncEff w5 1 3
/-- `unlock(e)` by context 1 (C17): the grant 6 released (O3). -/
def w7 : SC := prospectiveUnlock w6 1 6
/-- `terminate` of context 1 (C7). -/
def w8 : SC := termEffC w7 1

/-- The labels of the run, in order. -/
def wLabels : List Label :=
  [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 3 1), .newMutex 0 3,
   .kernel 0 (.derive 0 [1, 2] .observe), .spawnVal 0 [4] [(none, 0)] [(4, 5)],
   .kernel 1 (.write 5 [5]), .acquire 1 0, .readShared 1 4 2 .acquire 0, .unlock 1 0,
   .terminate 1]

/-! ## The memory side -/

/-- Parameters of the run, fixed once from its final places (Spec 1 §82): the test layout and
geometry of `Refinement.Runs.piOf`. -/
def πW : Params Unit := piOf w4.P []

/-- The memory state realizing the initial state (Spec 1 §47, `Refinement.repr_init`). -/
def mw0 : Machine.State :=
  run Machine.State.empty (initOps πW.pl πW.geom πW.rtok πW.L πW.ty πW.ival wStatics)
/-- After `derive` (no raw operation). -/
def mw1 : Machine.State := run mw0 (rawOps πW wv (.kernel 0 (.derive 1 [3] .modify)) (w0, [], []) mw0)
/-- After `store` (the write of the reference, Spec 1 §82.3). -/
def mw2 : Machine.State := run mw1 (rawOps πW wv (.kernel 0 (.store 3 1)) (w1, [], []) mw1)
/-- After `newMutex` (no raw operation). -/
def mw3 : Machine.State := run mw2 (rawOps πW wv (.newMutex 0 3) (w2, [], []) mw2)
/-- After the second `derive` (no raw operation). -/
def mw4 : Machine.State :=
  run mw3 (rawOps πW wv (.kernel 0 (.derive 0 [1, 2] .observe)) (w2, [⟨3, none⟩], []) mw3)
/-- After the by-value `spawn`: the creation of `d`, then the copy of `v` into `d`. -/
def mw5 : Machine.State :=
  run mw4 (rawOps πW wv (.spawnVal 0 [4] [(none, 0)] [(4, 5)]) (w3, [⟨3, none⟩], []) mw4)
/-- After the `write` of `d` by context 1. -/
def mw6 : Machine.State := run mw5 (rawOps πW wv (.kernel 1 (.write 5 [5])) (w4, [⟨3, none⟩], []) mw5)
/-- After `acquire` (no raw operation). -/
def mw7 : Machine.State := run mw6 (rawOps πW wv (.acquire 1 0) (w5, [⟨3, none⟩], []) mw6)
/-- After `readShared` (the raw read of `lock`). -/
def mw8 : Machine.State :=
  run mw7 (rawOps πW wv (.readShared 1 4 2 .acquire 0) (w6, [⟨3, some 6⟩], []) mw7)
/-- After `unlock` (no raw operation). -/
def mw9 : Machine.State := run mw8 (rawOps πW wv (.unlock 1 0) (w6, [⟨3, some 6⟩], []) mw8)
/-- After `terminate` (the deallocation of `d`, Spec 1 §73, §82.5). -/
def mw10 : Machine.State := run mw9 (rawOps πW wv (.terminate 1) (w7, [⟨3, none⟩], []) mw9)

/-- Every obligation of the steps of the run holds under the fixed parameters (Spec 1 §20.3, §82):
the initial layout and writes, then `StepOblC` of each step in the state where it is taken. -/
theorem witness_obligations :
    NewLayout πW.L (S3.init wStatics).P 0 0 πW.geom (rootIdx (wStatics.map (·.1))) ∧
    OblAlong obR obW (run Machine.State.empty (allocOps (Ty := Unit) πW.pl πW.geom πW.rtok 0
      Machine.State.empty (rootIdx (wStatics.map (·.1))))) (writeOps (run Machine.State.empty
        (allocOps (Ty := Unit) πW.pl πW.geom πW.rtok 0 Machine.State.empty
          (rootIdx (wStatics.map (·.1))))) πW.L πW.ty πW.ival (initLeaves wStatics)) ∧
    StepOblC kMutex.toK (· = ·) obR obW πW wv (.kernel 0 (.derive 1 [3] .modify)) (w0, [], [])
      mw0 ∧
    StepOblC kMutex.toK (· = ·) obR obW πW wv (.kernel 0 (.store 3 1)) (w1, [], []) mw1 ∧
    StepOblC kMutex.toK (· = ·) obR obW πW wv (.newMutex 0 3) (w2, [], []) mw2 ∧
    StepOblC kMutex.toK (· = ·) obR obW πW wv (.kernel 0 (.derive 0 [1, 2] .observe))
      (w2, [⟨3, none⟩], []) mw3 ∧
    StepOblC kMutex.toK (· = ·) obR obW πW wv (.spawnVal 0 [4] [(none, 0)] [(4, 5)])
      (w3, [⟨3, none⟩], []) mw4 ∧
    StepOblC kMutex.toK (· = ·) obR obW πW wv (.kernel 1 (.write 5 [5])) (w4, [⟨3, none⟩], [])
      mw5 ∧
    StepOblC kMutex.toK (· = ·) obR obW πW wv (.acquire 1 0) (w5, [⟨3, none⟩], []) mw6 ∧
    StepOblC kMutex.toK (· = ·) obR obW πW wv (.readShared 1 4 2 .acquire 0)
      (w6, [⟨3, some 6⟩], []) mw7 ∧
    StepOblC kMutex.toK (· = ·) obR obW πW wv (.unlock 1 0) (w6, [⟨3, some 6⟩], []) mw8 ∧
    StepOblC kMutex.toK (· = ·) obR obW πW wv (.terminate 1) (w7, [⟨3, none⟩], []) mw9 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **Witness, theorem 9** (non-vacuity of `TransRun` and of theorems 9b and 9c; Spec 1 §82;
C5, C7, C13, C16, C17, C37): the run above, with two contexts, a by-value `spawn`, a write by the
created context, an `acquire` followed by an `unlock`, a `readShared` and a `terminate`, is a
translated run under the fixed parameters `πW`; its memory state is reached from the empty state by
an execution of `ok` raw steps, none of which is `ub`, and it is related by `ReprC` to the final
concurrent state, where context 1 has terminated and context 0 is live. -/
theorem witness_refinement :
    (∃ tr ops, TransRun kMutex mutexLayout (· = ·) obR obW wStatics πW tr ops
        (w8, [⟨3, none⟩], []) mw10 ∧ tr.map Prod.fst = wLabels ∧
      Machine.Exec (· = ·) obR obW ops Machine.State.empty mw10 ∧
      Along (NoUB (· = ·) obR obW) Machine.State.empty ops) ∧
    ReprC πW.L πW.rtok w8 mw10 ∧ w8.C.length = 2 ∧ w8.Live 0 ∧ ¬ w8.Live 1 := by
  obtain ⟨hlay, hini, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := witness_obligations
  have h0 : TransRun kMutex mutexLayout (· = ·) obR obW wStatics πW [] _ (w0, [], []) mw0 :=
    .init (by decide) hlay hini
  have h1 := TransRun.step (w := wv) (lbl := .kernel 0 (.derive 1 [3] .modify))
    (st' := (w1, [], [])) h0 (.kernel ⟨_, .ok (by decide), rfl⟩) o1
  have h2 := TransRun.step (w := wv) (lbl := .kernel 0 (.store 3 1)) (st' := (w2, [], [])) h1
    (.kernel (.ok (by decide))) o2
  have h3 := TransRun.step (w := wv) (lbl := .newMutex 0 3) (st' := (w2, [⟨3, none⟩], [])) h2
    (.newMutex (st' := (w2, [⟨3, none⟩])) ⟨by decide, rfl⟩) o3
  have h4 := TransRun.step (w := wv) (lbl := .kernel 0 (.derive 0 [1, 2] .observe))
    (st' := (w3, [⟨3, none⟩], [])) h3 (.kernel ⟨_, .ok (by decide), rfl⟩) o4
  have h5 := TransRun.step (w := wv) (lbl := .spawnVal 0 [4] [(none, 0)] [(4, 5)])
    (st' := (w4, [⟨3, none⟩], [])) h4 (.spawnVal (.ok (by decide))) o5
  have h6 := TransRun.step (w := wv) (lbl := .kernel 1 (.write 5 [5]))
    (st' := (w5, [⟨3, none⟩], [])) h5 (.kernel ⟨_, .ok (by decide), rfl⟩) o6
  have h7 := TransRun.step (w := wv) (lbl := .acquire 1 0) (st' := (w6, [⟨3, some 6⟩], [])) h6
    (.acquire (st' := (w6, [⟨3, some 6⟩])) ⟨⟨3, none⟩, rfl, by decide, by decide, rfl⟩) o7
  have h8 := TransRun.step (w := wv) (lbl := .readShared 1 4 2 .acquire 0)
    (st' := (w6, [⟨3, some 6⟩], [])) h7
    (.readShared (.ok ⟨by decide, by decide, ⟨4, 4, rfl⟩, trivial⟩)) o8
  have h9 := TransRun.step (w := wv) (lbl := .unlock 1 0) (st' := (w7, [⟨3, none⟩], [])) h8
    (.unlock (st' := (w7, [⟨3, none⟩]))
      ⟨⟨3, some 6⟩, 6, rfl, by decide, rfl, by decide, by decide, by decide, rfl⟩) o9
  have h10 := TransRun.step (w := wv) (lbl := .terminate 1) (st' := (w8, [⟨3, none⟩], [])) h9
    (.terminate (.ok (by decide))) o10
  have hdd : DDSound kMutex.toK := testKS_dd _ _ _
  obtain ⟨hex, hR, -⟩ := refinement_run hdd (piOf_ok _ []) h10
  exact ⟨⟨_, _, h10, rfl, hex, run_no_ub hdd (piOf_ok _ []) h10⟩, hR, by decide, by decide,
    by decide⟩

end Ern.ConcurrencyModel
