import Ern.Concurrency.MutexReal.Bridge
import Ern.Concurrency.Corpus.HandoffEvents
import Ern.Concurrency.Corpus.MutexEdge

/-!
# Witnesses of the controller graph

Brief of milestone 4, slice 2, layer R, task 6 (`formal/reports/spec2-m4-mutexreal.md`;
`corpus-spec2-m3.md` v10 §2 nonies, "Faits attendus sur les graphes du contrôleur"): on `lc_trace`,
W-RL₀, W-RL and W-RL-J, the events of the controller of entry `e` (index `0`) and `rf`, the
consistency of the controller graph, its `sw` edges, the two variants of `lc_trace`, and the order,
in the strict graph of slice 1, between `newMutex(e)` and the protocol steps of `c1`. The facts are
written from the corpus and decided by `decide`. A last witness, S11, shows the invariant on an
abandoned grant.
-/

set_option autoImplicit false

namespace Ern.Concurrency.MutexReal.Witness

open Ern.MemoryModel.Access Ern.Concurrency Ern.Concurrency.MutexReal
open Ern.Concurrency.Corpus
open Ern.Concurrency.Traces (L0)
open Ern.Concurrency.Corpus.GuardedChainC (lcLbls)
open Ern.Concurrency.Corpus.MutexEdge
open Ern.Concurrency.Corpus.HandoffEvents (lcσ lc_run)

/-- The `sw` edges of a graph are exactly the edge `(a, b)`. -/
def SwExactly (g : EventModel.Graph) (a b : Nat) : Prop :=
  ∀ x ∈ List.range g.size, ∀ y ∈ List.range g.size, EventModel.SW g x y ↔ x = a ∧ y = b

/-- Decidability of `SwExactly`. -/
instance (g : EventModel.Graph) (a b : Nat) : Decidable (SwExactly g a b) := by
  unfold SwExactly; infer_instance

/-- Every protocol step on entry `0` made by context `1` comes after step `nm` in the strict graph
of slice 1 (`HBS`). -/
def AfterNewMutex (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) (nm : Nat) : Prop :=
  ∀ p ∈ List.range lbls.length, ((lbls[p]?).bind (ctlOp 0)).map (·.1) = some 1 →
    HBS σ L0 lbls (.step nm) (.step p)

/-- Decidability of `AfterNewMutex`. -/
instance (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) (nm : Nat) :
    Decidable (AfterNewMutex σ lbls nm) := by
  unfold AfterNewMutex; infer_instance

/-- `A1`, the RMW of an `acquire` by `c1`, under the reference realization. -/
abbrev A1 : EventModel.Ev := ⟨1, .rmw .acq 0 1⟩
/-- `U1`, the write of an `unlock` by `c1`. -/
abbrev U1 : EventModel.Ev := ⟨1, .wsh .rel 0⟩
/-- `R0`, the write of a `resetLock` by `c0`. -/
abbrev R0 : EventModel.Ev := ⟨0, .wsh .rlx 0⟩
/-- `A0`, the RMW of an `acquire` by `c0`. -/
abbrev A0 : EventModel.Ev := ⟨0, .rmw .acq 0 1⟩

/-! ## `lc_trace` -/

/-- `corpus-spec2-m3.md` v10 §2 nonies, `lc_trace`: the trace is a `Run5R` from the initial state;
step 4 is `newMutex(e)`; the controller events are `init`, `A1`, `U1`, `A0` (events 0 to 3, steps
4, 7, 9, 10), `rf` is `init → A1`, `U1 → A0`; the graph is well typed and consistent; `sw(U1, A0)`
is its only `sw` edge; `newMutex(e)` precedes every protocol step of `c1` in the strict graph. -/
theorem lc_graph : Run5R KM L0 lcσ lcLbls ∧ NewMutexAt lcσ lcLbls 0 4 ∧
    (ctlGraph refOrds 0 lcLbls).evs = [A1, U1, A0] ∧ (ctlGraph refOrds 0 lcLbls).rf = [(0, 1), (2, 3)] ∧
    [ctlIdx 0 lcLbls 7, ctlIdx 0 lcLbls 9, ctlIdx 0 lcLbls 10] = [1, 2, 3] ∧
    EventModel.WellTyped (ctlGraph refOrds 0 lcLbls) ∧
    EventModel.EventConsistent (ctlGraph refOrds 0 lcLbls) ∧
    SwExactly (ctlGraph refOrds 0 lcLbls) 2 3 ∧ AfterNewMutex lcσ lcLbls 4 :=
  ⟨lc_run.2, ⟨⟨0, 4, rfl⟩, rfl⟩, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide⟩

/-- `corpus-spec2-m3.md` v10 §2 nonies, variants of `lc_trace` (WC5.1 corrigé C32 item 1, C40;
herdtools7 B2 and B3): with the `unlock` in `relaxed`, or with the `acquire` in `relaxed`, `rf`
still relates `U1` to `A0`, the graph is consistent, and it has no `sw` edge. -/
theorem lc_variants :
    EventModel.RF (ctlGraph ⟨.acq, .rlx, .rlx⟩ 0 lcLbls) 2 3 ∧
    EventModel.EventConsistent (ctlGraph ⟨.acq, .rlx, .rlx⟩ 0 lcLbls) ∧
    EventModel.NoSW (ctlGraph ⟨.acq, .rlx, .rlx⟩ 0 lcLbls) ∧
    EventModel.RF (ctlGraph ⟨.rlx, .rel, .rlx⟩ 0 lcLbls) 2 3 ∧
    EventModel.EventConsistent (ctlGraph ⟨.rlx, .rel, .rlx⟩ 0 lcLbls) ∧
    EventModel.NoSW (ctlGraph ⟨.rlx, .rel, .rlx⟩ 0 lcLbls) := by
  decide

/-! ## W-RL₀, W-RL, W-RL-J -/

/-- `corpus-spec2-m3.md` v10 §2 nonies, W-RL₀: `Run5R` from the initial state; step 2 is
`newMutex(e)`; events `init`, `A1`, `U1`, `A0` (steps 5, 7, 9); `rf` `init → A1`, `U1 → A0`;
consistent; `sw(U1, A0)` only; `newMutex(e)` precedes the protocol steps of `c1` in the strict
graph. -/
theorem rl0_graph : Run5R KM L0 rl0σ rl0Lbls ∧ NewMutexAt rl0σ rl0Lbls 0 2 ∧
    (ctlGraph refOrds 0 rl0Lbls).evs = [A1, U1, A0] ∧
    (ctlGraph refOrds 0 rl0Lbls).rf = [(0, 1), (2, 3)] ∧
    EventModel.WellTyped (ctlGraph refOrds 0 rl0Lbls) ∧
    EventModel.EventConsistent (ctlGraph refOrds 0 rl0Lbls) ∧
    SwExactly (ctlGraph refOrds 0 rl0Lbls) 2 3 ∧ AfterNewMutex rl0σ rl0Lbls 2 :=
  ⟨W_RL0_run.2, ⟨⟨0, 3, rfl⟩, rfl⟩, by decide, by decide, by decide, by decide, by decide,
    by decide⟩

/-- `corpus-spec2-m3.md` v10 §2 nonies, W-RL: `Run5R` from the initial state; events `init`, `A1`,
`U1`, `R0`, `A0`; `rf` `init → A1`, `R0 → A0`; consistent; no `sw` edge, `A0` reading `R0`,
written in `relaxed`; `newMutex(e)` precedes the protocol steps of `c1` in the strict graph. -/
theorem rl_graph : Run5R KM L0 rlσ rlLbls ∧ NewMutexAt rlσ rlLbls 0 2 ∧
    (ctlGraph refOrds 0 rlLbls).evs = [A1, U1, R0, A0] ∧
    (ctlGraph refOrds 0 rlLbls).rf = [(0, 1), (3, 4)] ∧
    EventModel.WellTyped (ctlGraph refOrds 0 rlLbls) ∧
    EventModel.EventConsistent (ctlGraph refOrds 0 rlLbls) ∧
    EventModel.NoSW (ctlGraph refOrds 0 rlLbls) ∧ AfterNewMutex rlσ rlLbls 2 :=
  ⟨W_RL_run.2, ⟨⟨0, 3, rfl⟩, rfl⟩, by decide, by decide, by decide, by decide, by decide,
    by decide⟩

/-- `corpus-spec2-m3.md` v10 §2 nonies, W-RL-J: as W-RL, events, `rf`, consistency, no `sw` edge;
`newMutex(e)` precedes the protocol steps of `c1` in the strict graph. The two writes of `T`
(steps 6 and 13) are ordered by the `join` in the strict graph of slice 1, not by the controller
graph. -/
theorem rlj_graph : Run5R KM L0 rljσ rljLbls ∧ NewMutexAt rljσ rljLbls 0 2 ∧
    (ctlGraph refOrds 0 rljLbls).evs = [A1, U1, R0, A0] ∧
    (ctlGraph refOrds 0 rljLbls).rf = [(0, 1), (3, 4)] ∧
    EventModel.WellTyped (ctlGraph refOrds 0 rljLbls) ∧
    EventModel.EventConsistent (ctlGraph refOrds 0 rljLbls) ∧
    EventModel.NoSW (ctlGraph refOrds 0 rljLbls) ∧ AfterNewMutex rljσ rljLbls 2 ∧
    HBS rljσ L0 rljLbls (.step 6) (.step 13) :=
  ⟨W_RLJ_run.2, ⟨⟨0, 3, rfl⟩, rfl⟩, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide⟩

/-! ## The abandoned grant (S11) -/

/-- The labels of S11 (`corpus-spec2-m3.md` §1 S11): block MX up to `MX₄`, then
`c1 : o1′ := derive(o1, Observe)`, `c1 : enterFrame f1′` yielding `o1′`, `c1 : acquire(e)`,
`c1 : exitFrameC(f1′)` without `unlock`. -/
def s11Lbls : List Label :=
  [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 3 1), .newMutex 0 3,
   .kernel 0 (.derive 0 [1, 2] .observe), .spawn 0 [4] [], .kernel 1 (.derive 4 [1, 2] .observe),
   .kernel 1 (.enter [5] []), .acquire 1 0, .kernel 1 .exit]

/-- The named states of S11. -/
def s11σ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(x0, [], []), (x1, [], []), (x2, [], []), (x2, regX, []), (x3, regX, []), (x4, regX, []),
    (y1, regX, []), (y1', regX, []), (y2, regG6, []), (y3, regG6, [])].getD i (y3, regG6, [])

/-- Brief, task 3, the invariant on an abandoned grant (WC5.1 corrigé C18): S11 is a `Run5R` from
the initial state; after the exit of `f1′`, the grant `g` (authority 6) is recorded and inactive,
the controller is at `1` (the last controller event, the RMW of the `acquire`, wrote `1`), and
`ctl_invariant` applies at that state. -/
theorem s11_abandoned : Run5R KM L0 s11σ s11Lbls ∧ (s11σ 9).2.1[0]? = some ⟨3, some 6⟩ ∧
    ¬ (s11σ 9).1.flat.Active 6 ∧ lastW (ctlGraph refOrds 0 s11Lbls) = some 1 ∧
    ((⟨3, some 6⟩ : SyncEntry).grant = none ↔
      lastW (ctlGraph refOrds 0 (s11Lbls.take 9)) = some 0) := by
  have h : Steps5R KM L0 [(x0, [], []), (x1, [], []), (x2, [], []), (x2, regX, []),
      (x3, regX, []), (x4, regX, []), (y1, regX, []), (y1', regX, []), (y2, regG6, []),
      (y3, regG6, [])] s11Lbls :=
    .cons ⟨⟨(fun e he => by cases he), by decide, trivial⟩, trivial⟩ (.kernel mx_steps.1) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, by decide⟩ (.kernel mx_steps.2.1) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, trivial⟩ (.newMutex mx_steps.2.2.1) <|
    .cons ⟨⟨(by decide : ∀ e ∈ regX, e.Live x2 → 0 ≠ e.guarded), by decide, trivial⟩, trivial⟩
      (.kernel mx_steps.2.2.2.2.1) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, trivial⟩ (.spawn mx_steps.2.2.2.2.2) <|
    .cons ⟨⟨(by decide : ∀ e ∈ regX, e.Live x4 → 4 ≠ e.guarded), by decide, trivial⟩, trivial⟩
      (.kernel S11_1_ok.1) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, trivial⟩ (.kernel S11_1_ok.2.1) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, by decide⟩ (.acquire S11_1_ok.2.2.1) <|
    .cons ⟨⟨trivial, trivial, trivial⟩, trivial⟩ (.kernel S11_1_ok.2.2.2.1) .nil
  have hr := h.run (y3, regG6, [])
  refine ⟨hr, rfl, S11_1_ok.2.2.2.2, by decide, ?_⟩
  exact (ctl_invariant (fun i hi => (hr i hi).2) (fun x hx => by cases hx) refOrds 9
    (by decide)).1 ⟨3, some 6⟩ rfl

end Ern.Concurrency.MutexReal.Witness
