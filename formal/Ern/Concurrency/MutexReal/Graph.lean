import Ern.Concurrency.EventsStrict
import Ern.Concurrency.EventModel.Complements

/-!
# The controller graph of a mutex entry

Brief of milestone 4, slice 2, layer R, task 2 (`formal/reports/spec2-m4-mutexreal.md`): on a trace
of the authority machine, the atomic events of the controller of an entry `e`, placed in the event
fragment of layer E (`Ern.Concurrency.EventModel`), under the declared realization of
`corpus-spec2-m3.md` v10 §2 nonies and hypotheses 1, 2 and 4 of the brief:

* `newMutex(e)` gives the non-atomic initial write of `0`, event `0` of the fragment (hypothesis 4);
* `acquire(e)` gives a successful RMW reading `0` and writing `1`, `unlock(e)` and `resetLock(e)` an
  atomic write of `0`, with three orders as parameters (hypothesis 1);
* `mo` is the order of these steps in the trace and each RMW reads the modification just before it
  (hypothesis 2).

Entries are designated by their index in the registry, as the labels `acquire`, `unlock` and
`resetLock` do; `newMutex(e)` is the step that appends index `e` (`NewMutexAt`). The graph holds
only events on the atomic unit. Nothing of the authority machine, of the graphs of slice 1 or of
`EventModel` is changed.
-/

set_option autoImplicit false

namespace Ern.Concurrency.MutexReal

open Ern.Concurrency

/-! ## Realization -/

/-- The orders of the declared realization (brief, hypothesis 1; `corpus-spec2-m3.md` v10 §2
nonies): of the RMW of `acquire`, of the write of `unlock`, of the write of `resetLock`. -/
structure Ords where
  acq : EventModel.MOrd
  rel : EventModel.MOrd
  reset : EventModel.MOrd

/-- The reference realization (brief, hypothesis 1): `acquire`, `release`, `relaxed`. -/
def refOrds : Ords := ⟨.acq, .rel, .rlx⟩

/-- The protocol operations that modify the controller (WC5.1 corrigé C48; corpus v10 §2
nonies). -/
inductive CtlOp where
  | acq | unl | rst
deriving DecidableEq, Repr

/-- The event kind of a protocol operation under the orders `o` (brief, hypothesis 1): `acquire`
is a successful RMW reading `0` and writing `1` (WC5.1 corrigé C39, C48); `unlock` and
`resetLock` are an atomic write of `0`. -/
def CtlOp.kind (o : Ords) : CtlOp → EventModel.Kind
  | .acq => .rmw o.acq 0 1
  | .unl => .wsh o.rel 0
  | .rst => .wsh o.reset 0

/-- The step `lbl` as a protocol step on entry `e`: its context and its operation. -/
def ctlOp (e : Nat) : Label → Option (Nat × CtlOp)
  | .acquire c i => if i = e then some (c, .acq) else none
  | .unlock c i => if i = e then some (c, .unl) else none
  | .resetLock c i => if i = e then some (c, .rst) else none
  | _ => none

/-- The protocol steps on entry `e` of a list of labels, in trace order. -/
def ctlOps (e : Nat) (lbls : List Label) : List (Nat × CtlOp) := lbls.filterMap (ctlOp e)

/-- The controller events of entry `e` other than the initial write, in trace order (brief,
task 2: one per step `acquire(e)`, `unlock(e)`, `resetLock(e)`, with the context of the step). -/
def ctlEvs (o : Ords) (e : Nat) (lbls : List Label) : List EventModel.Ev :=
  (ctlOps e lbls).map fun p => ⟨p.1, p.2.kind o⟩

/-- The step `i` is `newMutex(e)`: a `newMutex` step that appends index `e` to the registry
(WC5.1 corrigé C13 effect). -/
def NewMutexAt (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) (e i : Nat) : Prop :=
  (∃ c g, lbls[i]? = some (.newMutex c g)) ∧ (σ i).2.1.length = e

/-! ## The graph -/

/-- The event kind is a successful RMW. -/
def kindIsRmw : EventModel.Kind → Bool
  | .rmw _ _ _ => true
  | _ => false

/-- All pairs `(a, b)` with `a < b < n`. -/
def allPairs (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap fun b => (List.range b).map fun a => (a, b)

/-- The `rf` edges of hypothesis 2: each RMW, event `j + 1`, reads event `j`, the modification just
before it. -/
def rfPairs (evs : List EventModel.Ev) : List (Nat × Nat) :=
  (List.range evs.length).filterMap fun j =>
    if (evs[j]?.map fun x => kindIsRmw x.kind) = some true then some (j, j + 1) else none

/-- The graph of a list of controller events (brief, task 2, hypotheses 2 and 4): the initial write
of `0` is event `0`; `mo` is the order of the events; each RMW reads the event just before it. -/
def mkGraph (evs : List EventModel.Ev) : EventModel.Graph :=
  { init := 0, evs := evs, rf := rfPairs evs, mo := allPairs (evs.length + 1) }

/-- The controller graph of entry `e` on the trace `lbls` under the orders `o` (brief, task 2). -/
def ctlGraph (o : Ords) (e : Nat) (lbls : List Label) : EventModel.Graph :=
  mkGraph (ctlEvs o e lbls)

/-- The event of the graph for the protocol step `i` on `e`: one more than the number of protocol
steps on `e` before it. -/
def ctlIdx (e : Nat) (lbls : List Label) (i : Nat) : Nat := (ctlOps e (lbls.take i)).length + 1

/-! ## Basic facts -/

/-- Membership in `allPairs`. -/
theorem mem_allPairs {n a b : Nat} : (a, b) ∈ allPairs n ↔ a < b ∧ b < n := by
  simp only [allPairs, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨b', hb', a', ha', rfl, rfl⟩; exact ⟨ha', hb'⟩
  · rintro ⟨ha, hb⟩; exact ⟨b, hb, a, ha, rfl, rfl⟩

/-- Membership in `rfPairs`. -/
theorem mem_rfPairs {evs : List EventModel.Ev} {w r : Nat} :
    (w, r) ∈ rfPairs evs ↔ r = w + 1 ∧ (evs[w]?.map fun x => kindIsRmw x.kind) = some true := by
  simp only [rfPairs, List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨j, -, h⟩
    split at h
    · rename_i hj; cases h; exact ⟨rfl, hj⟩
    · cases h
  · rintro ⟨rfl, h⟩
    refine ⟨w, ?_, by simp [h]⟩
    cases hw : evs[w]? with
    | none => rw [hw] at h; cases h
    | some _ => exact (List.getElem?_eq_some_iff.1 hw).1

/-- The number of controller events does not depend on the orders. -/
theorem ctlEvs_length (o : Ords) (e : Nat) (lbls : List Label) :
    (ctlEvs o e lbls).length = (ctlOps e lbls).length := by
  simp [ctlEvs]

/-- The controller events of a concatenation. -/
theorem ctlOps_append (e : Nat) (l₁ l₂ : List Label) :
    ctlOps e (l₁ ++ l₂) = ctlOps e l₁ ++ ctlOps e l₂ := by
  simp [ctlOps, List.filterMap_append]

/-- The controller events of a prefix extended by one step. -/
theorem ctlOps_take_succ (e : Nat) {lbls : List Label} {k : Nat} (hk : k < lbls.length) :
    ctlOps e (lbls.take (k + 1)) = ctlOps e (lbls.take k) ++ (ctlOp e lbls[k]).toList := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, ctlOps_append]
  cases h : ctlOp e lbls[k] <;> simp [ctlOps, h]

/-- The kind of event `j + 1` of `mkGraph`. -/
theorem kind?_mkGraph (evs : List EventModel.Ev) (j : Nat) :
    (mkGraph evs).kind? (j + 1) = evs[j]?.map (·.kind) := by
  simp [EventModel.Graph.kind?, EventModel.Graph.ev?, mkGraph]

/-- The context of event `j + 1` of `mkGraph`. -/
theorem ctx?_mkGraph (evs : List EventModel.Ev) (j : Nat) :
    (mkGraph evs).ctx? (j + 1) = evs[j]?.map (·.ctx) := by
  simp [EventModel.Graph.ctx?, EventModel.Graph.ev?, mkGraph]

/-- The controller event of the protocol step `i` on `e` is the entry of `ctlEvs` at the number of
protocol steps before `i`. -/
theorem ctlEvs_at (o : Ords) (e : Nat) {lbls : List Label} {i : Nat} (hi : i < lbls.length)
    {c : Nat} {op : CtlOp} (h : ctlOp e lbls[i] = some (c, op)) :
    (ctlEvs o e lbls)[(ctlOps e (lbls.take i)).length]? = some ⟨c, op.kind o⟩ := by
  have hs : lbls = lbls.take i ++ lbls[i] :: lbls.drop (i + 1) := by
    simp
  rw [hs, ctlEvs, ctlOps_append]
  simp only [ctlOps, List.filterMap_cons, h, List.map_append, List.map_cons]
  rw [List.getElem?_append_right (by simp)]
  simp

end Ern.Concurrency.MutexReal
