import Ern.Concurrency.MutexReal.Amend
import Ern.Concurrency.MutexReal.ClassifyWitness

/-!
# Exclusions and twins under the proposed C22 item 4

Brief of milestone 4, slice 2, layer R, corrective pass, task 2 (`corpus-spec2-m3.md` v11 §2
decies, "Contre-exemples de la classification et jumeaux"): the last steps of `store_cex`,
`alloc_cex` and `issue_cex` are refused by the restriction of the controller (`CtlRestr`) on their
existing states; each positive twin, and the `depend` witness with its twin, are checked by
`decide`. Verdicts and facts are written from the corpus.
-/

set_option autoImplicit false

namespace Ern.Concurrency.MutexReal.AmendWitness

open Ern.MemoryModel Ern.MemoryModel.Access Ern.Concurrency Ern.Concurrency.MutexReal
open Ern.Concurrency.Corpus Ern.Concurrency.MutexReal.ClassifyWitness
open Ern.Concurrency.Traces (L0)

/-! ## The three counter-examples are refused -/

/-- `corpus-spec2-m3.md` v11 §2 decies, `store`: the last step of `store_cex`,
`c0 : store(z, lock)`, admitted by `Encap5R`, is refused by the restriction of the controller (proposed C22 item 4: a
`store` whose target is the controller); the trace is no `Run6`. -/
theorem store_refused : ¬ CtlRestr L0 (csσ 4) (.kernel 0 (.store 4 2)) (csσ 5) ∧
    ¬ Run6 KM L0 csσ csLbls := by
  have h : ¬ CtlRestr L0 (csσ 4) (.kernel 0 (.store 4 2)) (csσ 5) := by decide
  exact ⟨h, fun hr => h (hr.restr (i := 4) (by decide))⟩

/-- `corpus-spec2-m3.md` v11 §2 decies, `alloc`: the last step of `alloc_cex`,
`c0 : alloc(provider = slot, owner = lock)`, is refused by the restriction of the controller (an `alloc` whose owner is
the controller); the trace is no `Run6`. -/
theorem alloc_refused : ¬ CtlRestr L0 (caσ 3) (.kernel 0 (.alloc 1 2 [(none, 0)])) (caσ 4) ∧
    ¬ Run6 KM L0 caσ caLbls := by
  have h : ¬ CtlRestr L0 (caσ 3) (.kernel 0 (.alloc 1 2 [(none, 0)])) (caσ 4) := by decide
  exact ⟨h, fun hr => h (hr.restr (i := 3) (by decide))⟩

/-- `corpus-spec2-m3.md` v11 §2 decies, `issue`: the last step of `issue_cex`,
`c0 : issue(arena, R1, lock2)`, is refused by the restriction of the controller (an `issue` whose destination is the
controller); the trace is no `Run6`. -/
theorem issue_refused : ¬ CtlRestr L0 (ciσ 7) (.issue 0 0 [5] 2) (ciσ 8) ∧
    ¬ Run6 KA L0 ciσ ciLbls := by
  have h : ¬ CtlRestr L0 (ciσ 7) (.issue 0 0 [5] 2) (ciσ 8) := by decide
  exact ⟨h, fun hr => h (hr.restr (i := 7) (by decide))⟩

/-! ## Twins -/

/-- `c0 : store(z, lock′)` (O8). -/
def ts2 : SC := storeEffC cs1 0 4 6

/-- The labels of the twin of the `store` counter-example. -/
def tsLbls : List Label :=
  mx3Lbls ++ [.kernel 0 (.derive 2 [5] .observe), .kernel 0 (.store 4 6)]

/-- The named states of the twin of the `store` counter-example. -/
def tsσ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(x0, [], []), (x1, [], []), (x2, [], []), (x2, regX, []), (cs1, regX, []),
    (ts2, regX, [])].getD i (ts2, regX, [])

/-- `corpus-spec2-m3.md` v11 §2 decies, twin of `store`: `c0 : store(z, lock′)` is `ok` (Spec 1
§65.1–§65.5; `M′` has no entry) and the trace is a `Run6` from the initial state. -/
theorem store_twin : tsσ 0 = (SC.ofS3 (S3.init mxst), [], []) ∧ Run6 KM L0 tsσ tsLbls := by
  have h : Steps5R KM L0 [(x2, regX, []), (cs1, regX, []), (ts2, regX, [])]
      [.kernel 0 (.derive 2 [5] .observe), .kernel 0 (.store 4 6)] :=
    .cons ⟨⟨(by decide : ∀ e ∈ regX, e.Live x2 → 2 ≠ e.guarded), by decide, trivial⟩, trivial⟩
      (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, by decide⟩ (.kernel ⟨by decide, .ok (by decide)⟩) .nil
  exact ⟨rfl, run6_of_run5R ((mx3_steps h).run _) (by decide)⟩

/-- `c0 : alloc(provider = slot, owner = lock′)` (O14). -/
def ta1 : SC := x2.set (allocEff (x2.view 0) 6 [(none, 0)])

/-- The labels of the twin of the `alloc` counter-example. -/
def taLbls : List Label := mx3Lbls ++ [.kernel 0 (.alloc 1 6 [(none, 0)])]

/-- The named states of the twin of the `alloc` counter-example. -/
def taσ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(x0, [], []), (x1, [], []), (x2, [], []), (x2, regX, []), (ta1, regX, [])].getD i
    (ta1, regX, [])

/-- `corpus-spec2-m3.md` v11 §2 decies, twin of `alloc`:
`c0 : alloc(provider = slot, owner = lock′)` is `ok` (Spec 1 §71.3: `Modify` exercisable on `lock′` through `root_M′`) and the trace is a `Run6`
from the initial state. -/
theorem alloc_twin : taσ 0 = (SC.ofS3 (S3.init mxst), [], []) ∧ Run6 KM L0 taσ taLbls := by
  have h : Steps5R KM L0 [(x2, regX, []), (ta1, regX, [])] [.kernel 0 (.alloc 1 6 [(none, 0)])] :=
    .cons ⟨⟨trivial, trivial, trivial⟩, by decide⟩
      (.kernel ⟨by decide, _, .ok (by decide) trivial, rfl⟩) .nil
  exact ⟨rfl, run6_of_run5R ((mx3_steps h).run _) (by decide)⟩

/-- `store(block, d0)` by context 0, the store phase of `issue(arena, R1, d0)` (O8). -/
def ti2 : SC := storeEffC ci2s 0 ci1.A.length 7

/-- The labels of the twin of the `issue` counter-example. -/
def tiLbls : List Label :=
  [.kernel 0 (.derive 2 [5, 6] .modify), .kernel 0 (.store 4 3), .newArena 0 4 4,
   .kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 5 1), .newMutex 0 5, .acquire 0 0,
   .issue 0 0 [5] 7]

/-- The named states of the twin of the `issue` counter-example. -/
def tiσ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(a0, [], []), (a1, [], []), (a2, [], []), (a2, [], arA), (a3, [], arA), (a4, [], arA),
    (a4, regA, arA), (ci1, regI, arA), (ti2, regI, arI)].getD i (ti2, regI, arI)

/-- `corpus-spec2-m3.md` v11 §2 decies, twin of `issue`: `c0 : issue(arena, R1, d0)`, `d0` a local
leaf of `f0` (as S3, step 3), is `ok` and the trace is a `Run6` from the initial state. -/
theorem issue_twin : tiσ 0 = (SC.ofS3 (S3.init arst), [], []) ∧ Run6 KA L0 tiσ tiLbls := by
  have h : Steps5R KA L0 [(a0, [], []), (a1, [], []), (a2, [], []), (a2, [], arA), (a3, [], arA),
      (a4, [], arA), (a4, regA, arA), (ci1, regI, arA), (ti2, regI, arI)] tiLbls :=
    .cons ⟨⟨(fun e he => by cases he), by decide, trivial⟩, trivial⟩
      (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, by decide⟩ (.kernel ⟨by decide, .ok (by decide)⟩) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, trivial⟩ (.newArena ⟨by decide, .ok (by decide)⟩) <|
    .cons ⟨⟨(fun e he => by cases he), by decide, trivial⟩, trivial⟩
      (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, by decide⟩ (.kernel ⟨by decide, .ok (by decide)⟩) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, trivial⟩ (.newMutex ⟨by decide, by decide, rfl⟩) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, by decide⟩
      (.acquire ⟨by decide, ⟨5, none⟩, rfl, by decide, by decide, rfl⟩) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, by decide⟩
      (.issue (.ok (E := ⟨4, 4, [5, 6], []⟩) rfl (by decide) (by decide)
        ⟨by decide, _, .ok (by decide), rfl⟩ ⟨by decide, .ok (by decide)⟩)) .nil
  exact ⟨rfl, run6_of_run5R (h.run _) (by decide)⟩

/-! ## `depend` -/

/-- `c0 : depend(lock, a)` (O5), `a` the authority 4 of `cs1`. -/
def td2 : SC := dependEffC cs1 0 2 4
/-- `c0 : depend(lock′, a)` (O5). -/
def tdt2 : SC := dependEffC cs1 0 6 4

/-- The labels of the `depend` witness. -/
def tdLbls : List Label :=
  mx3Lbls ++ [.kernel 0 (.derive 2 [5] .observe), .kernel 0 (.depend 2 4)]

/-- The named states of the `depend` witness. -/
def tdσ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(x0, [], []), (x1, [], []), (x2, [], []), (x2, regX, []), (cs1, regX, []),
    (td2, regX, [])].getD i (td2, regX, [])

/-- The labels of the twin of the `depend` witness. -/
def tdtLbls : List Label :=
  mx3Lbls ++ [.kernel 0 (.derive 2 [5] .observe), .kernel 0 (.depend 6 4)]

/-- The named states of the twin of the `depend` witness. -/
def tdtσ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(x0, [], []), (x1, [], []), (x2, [], []), (x2, regX, []), (cs1, regX, []),
    (tdt2, regX, [])].getD i (tdt2, regX, [])

/-- `corpus-spec2-m3.md` v11 §2 decies, `depend`: from `MX₃`, `c0 : a := derive(root_M′, Observe,
{slot′})` then `c0 : depend(lock, a)` form a `Run5R` from the initial state; the `depend` is an `ok`
kernel step (Spec 1 §64.1, §64.3), admitted by `Encap5R`, and refused by the restriction of the
controller (proposed C22 item 4: a change of the dependency state of the controller); entry `e`
stays live. -/
theorem depend_refused : tdσ 0 = (SC.ofS3 (S3.init mxst), [], []) ∧ Run5R KM L0 tdσ tdLbls ∧
    opStepC KM (.depend 2 4) 0 cs1 (.ok td2) ∧ (⟨3, none⟩ : SyncEntry).Live td2 ∧
    ¬ CtlRestr L0 (tdσ 4) (.kernel 0 (.depend 2 4)) (tdσ 5) := by
  have hd : opStepC KM (.depend 2 4) 0 cs1 (.ok td2) := ⟨by decide, .ok (by decide)⟩
  have h : Steps5R KM L0 [(x2, regX, []), (cs1, regX, []), (td2, regX, [])]
      [.kernel 0 (.derive 2 [5] .observe), .kernel 0 (.depend 2 4)] :=
    .cons ⟨⟨(by decide : ∀ e ∈ regX, e.Live x2 → 2 ≠ e.guarded), by decide, trivial⟩, trivial⟩
      (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, by decide⟩ (.kernel hd) .nil
  exact ⟨rfl, (mx3_steps h).run _, hd, by decide, by decide⟩

/-- `corpus-spec2-m3.md` v11 §2 decies, twin of `depend`: `c0 : depend(lock′, a)` is `ok` and the
trace is a `Run6` from the initial state. -/
theorem depend_twin : tdtσ 0 = (SC.ofS3 (S3.init mxst), [], []) ∧ Run6 KM L0 tdtσ tdtLbls := by
  have h : Steps5R KM L0 [(x2, regX, []), (cs1, regX, []), (tdt2, regX, [])]
      [.kernel 0 (.derive 2 [5] .observe), .kernel 0 (.depend 6 4)] :=
    .cons ⟨⟨(by decide : ∀ e ∈ regX, e.Live x2 → 2 ≠ e.guarded), by decide, trivial⟩, trivial⟩
      (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, by decide⟩ (.kernel ⟨by decide, .ok (by decide)⟩) .nil
  exact ⟨rfl, run6_of_run5R ((mx3_steps h).run _) (by decide)⟩

/-! ## Observations -/

/-- `c0 : alloc(provider = slot, owner = M)` (O14). -/
def tam1 : SC := x2.set (allocEff (x2.view 0) 0 [(none, 0)])

/-- Observation: from `MX₃`, `c0 : alloc(provider = slot, owner = M)` is an `ok` kernel step
admitted by `Encap5R`; entry `e` stays live and its controller stays `lock`. The restriction of the
controller refuses it: the footprint of `alloc` (`Touches`) contains the leaves of its owner `M`,
`lock` among them. The proposed C22 item 4 names the controller as owner, not a value that
contains it. -/
theorem alloc_owner_M_refused : opStepC KM (.alloc 1 0 [(none, 0)]) 0 x2 (.ok tam1) ∧
    Encap5R KM L0 (x2, regX, []) (.kernel 0 (.alloc 1 0 [(none, 0)])) ∧
    (⟨3, none⟩ : SyncEntry).Live tam1 ∧ ControlOf L0 tam1 ⟨3, none⟩ = some 2 ∧
    ¬ CtlRestr L0 (x2, regX, []) (.kernel 0 (.alloc 1 0 [(none, 0)])) (tam1, regX, []) :=
  ⟨⟨by decide, _, .ok (by decide) trivial, rfl⟩, ⟨⟨trivial, trivial, trivial⟩, by decide⟩,
    by decide, by decide, by decide⟩

/-- Observation on the dependency clause: `lock` is not in the footprint `Touches` of
`depend(lock, a)` (`tdσ`, step 4); only the place `result` added by `TouchesX` puts it there. -/
theorem depend_only_added : ¬ Touches L0 (tdσ 4) (.kernel 0 (.depend 2 4)) 2 ∧
    TouchesX L0 (tdσ 4) (.kernel 0 (.depend 2 4)) 2 := by
  decide

end Ern.Concurrency.MutexReal.AmendWitness
