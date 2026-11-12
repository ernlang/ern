import Ern.Concurrency.MutexReal.Final
import Ern.Concurrency.MutexReal.Bridge

/-!
# No silent change under the final wording

Brief of milestone 4, slice 2, layer R, final pass, task 6 (`corpus-spec2-m3.md` v12 §2 undecies:
"L'amendement ne change ni l'effet abstrait de `newMutex`, ni l'état d'initialisation d'aucune
feuille (C13.10), ni le graphe du contrôleur"):

* the amended `newMutex` has the effect of `NewMutexOk` and keeps the initialization state of
  every leaf (`newMutexAm_effect`, `newMutexAm_same_effect`);
* the controller graph (`ctlGraph`) reads only the labels, never the states, so a final amended
  execution has the graph of its labels; its initial write, event `0`, is a non-atomic
  modification writing `0` and the source of no `sw` edge (`ctlGraph_init_write`);
* the invariant, the coherence and the bridge of layer R apply as they are to a final amended
  execution (`runAmF_ctl_invariant`, `runAmF_coherent`, `runAmF_bridge`, `runAmF_bridge_sw`,
  `runAmF_bridge_sw_ref`, `runAmF_bridge_converse`): corollaries, not new proofs.
-/

set_option autoImplicit false

namespace Ern.Concurrency.MutexReal

open Ern.MemoryModel.Access Ern.Concurrency

/-! ## The effect of `newMutex` -/

/-- Brief, final pass, task 6 (proposed C13, "Clarification to the Effect": the abstract
registration effect is unchanged and no structural leaf of `M` changes its initialization state):
an amended `newMutex` that is `ok` appends `⟨guarded, none⟩` to the registry, leaves the kernel
state unchanged, so the initialization state of every leaf, and the leaves of `M` are `Init` before
and after (WC5.1 corrigé C13.10). -/
theorem newMutexAm_effect {k : K} {L : MutexLayout} {ar : ArenaReg} {s : SC} {reg : SyncReg}
    {c g : Nat} {st' : SC × SyncReg} (h : NewMutexAmOk k L ar s reg c g st') :
    st' = (s, reg ++ [⟨g, none⟩]) ∧ (∀ l, st'.1.I l = s.I l) ∧
      OptP (mutexOf s g) (fun m => ∀ l ∈ footprint s.P m, st'.1.I l = .init) False := by
  obtain ⟨⟨-, hpre, rfl⟩, -⟩ := h
  exact ⟨rfl, fun _ => rfl, hpre.initM⟩

/-- Brief, final pass, task 6: the amended `newMutex` and `newMutex` have the same final state
when both are `ok`; the proposed C13 item 11 only removes `ok` outcomes. -/
theorem newMutexAm_same_effect {k : K} {L : MutexLayout} {ar : ArenaReg} {s : SC}
    {reg : SyncReg} {c g : Nat} {st' st'' : SC × SyncReg} (h : NewMutexAmOk k L ar s reg c g st')
    (h' : NewMutexOk k L ar s reg c g st'') : st' = st'' := by
  rw [h.1.2.2, h'.2.2]

/-! ## The controller graph -/

/-- Brief, final pass, task 6; `corpus-spec2-m3.md` v12 §2 undecies: in the controller graph of
any trace, the initial write (event `0`, hypothesis 4 of layer R) is a modification of the
controller (WC5.1 corrigé C31), not atomic, of no context, writing `0`, and the source of no `sw`
edge (C32 item 1: only a release-capable write is). -/
theorem ctlGraph_init_write (o : Ords) (e : Nat) (lbls : List Label) :
    (ctlGraph o e lbls).isMod 0 = true ∧ (ctlGraph o e lbls).isAtomic 0 = false ∧
      (ctlGraph o e lbls).ctx? 0 = none ∧ (ctlGraph o e lbls).valW 0 = some 0 ∧
      ∀ r, ¬ EventModel.SW (ctlGraph o e lbls) 0 r := by
  refine ⟨rfl, ?_, rfl, rfl, fun r h => ?_⟩
  · simp [EventModel.Graph.isAtomic, EventModel.Graph.kind?, EventModel.Graph.ev?]
  · have hr := h.2.1
    simp [EventModel.Graph.relCap, EventModel.Graph.kind?, EventModel.Graph.ev?] at hr

/-! ## Invariant, coherence and bridge -/

/-- Brief, final pass, task 6: `ctl_invariant` on a final amended execution. -/
theorem runAmF_ctl_invariant {k : K} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg}
    {lbls : List Label} (h : RunAmF k L σ lbls) {e : Nat}
    (h0 : ∀ x, (σ 0).2.1[e]? = some x → x.grant = none) (o : Ords) :
    ∀ n, n ≤ lbls.length →
      (∀ x, (σ n).2.1[e]? = some x →
        (x.grant = none ↔ lastW (ctlGraph o e (lbls.take n)) = some 0)) ∧
      ((σ n).2.1[e]? = none → ctlOps e (lbls.take n) = []) ∧
      PredZero (ctlEvs o e (lbls.take n)) :=
  ctl_invariant (fun i hi => (h.1 i hi).2) h0 o

/-- Brief, final pass, task 6: `ctlGraph_coherent_run` on a final amended execution from a state
with an empty registry. -/
theorem runAmF_coherent {k : K} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg}
    {lbls : List Label} (h : RunAmF k L σ lbls) (h0 : (σ 0).2.1 = []) (e : Nat) {o : Ords}
    (ho : o.WellTyped) :
    EventModel.WellTyped (ctlGraph o e lbls) ∧ EventModel.EventConsistent (ctlGraph o e lbls) :=
  ctlGraph_coherent_run (run7_run5R h.1) h0 e ho

/-- Brief, final pass, task 6: `bridge` on a final amended execution. -/
theorem runAmF_bridge {k : K} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg}
    {lbls : List Label} (h : RunAmF k L σ lbls) {e : Nat}
    (h0 : ∀ x, (σ 0).2.1[e]? = some x → x.grant = none) {u a c : Nat}
    (hu : lbls[u]? = some (.unlock c e)) (hsw : SWS σ L lbls (.step u) (.step a)) (o : Ords) :
    EventModel.RF (ctlGraph o e lbls) (ctlIdx e lbls u) (ctlIdx e lbls a) :=
  bridge (fun i hi => (h.1 i hi).2) h0 hu hsw o

/-- Brief, final pass, task 6: `bridge_sw` on a final amended execution. -/
theorem runAmF_bridge_sw {k : K} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg}
    {lbls : List Label} (h : RunAmF k L σ lbls) {e : Nat}
    (h0 : ∀ x, (σ 0).2.1[e]? = some x → x.grant = none) {u a c : Nat}
    (hu : lbls[u]? = some (.unlock c e)) (hsw : SWS σ L lbls (.step u) (.step a)) (o : Ords) :
    EventModel.SW (ctlGraph o e lbls) (ctlIdx e lbls u) (ctlIdx e lbls a) ↔
      (o.rel = .rel ∨ o.rel = .sc) ∧ (o.acq = .acq ∨ o.acq = .acqRel ∨ o.acq = .sc) :=
  bridge_sw (fun i hi => (h.1 i hi).2) h0 hu hsw o

/-- Brief, final pass, task 6: `bridge_sw_ref` on a final amended execution. -/
theorem runAmF_bridge_sw_ref {k : K} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg}
    {lbls : List Label} (h : RunAmF k L σ lbls) {e : Nat}
    (h0 : ∀ x, (σ 0).2.1[e]? = some x → x.grant = none) {u a c : Nat}
    (hu : lbls[u]? = some (.unlock c e)) (hsw : SWS σ L lbls (.step u) (.step a)) :
    EventModel.SW (ctlGraph refOrds e lbls) (ctlIdx e lbls u) (ctlIdx e lbls a) :=
  bridge_sw_ref (fun i hi => (h.1 i hi).2) h0 hu hsw

/-- Brief, final pass, task 6: `bridge_converse` on a final amended execution, under hypothesis 3
(`CtlFixed`). -/
theorem runAmF_bridge_converse {k : K} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg}
    {lbls : List Label} (h : RunAmF k L σ lbls) {e : Nat}
    (h0 : ∀ x, (σ 0).2.1[e]? = some x → x.grant = none) (h3 : CtlFixed σ L lbls e)
    {u a cu ca : Nat} (hu : lbls[u]? = some (.unlock cu e)) (ha : lbls[a]? = some (.acquire ca e))
    (o : Ords) (hrf : EventModel.RF (ctlGraph o e lbls) (ctlIdx e lbls u) (ctlIdx e lbls a)) :
    SWS σ L lbls (.step u) (.step a) :=
  bridge_converse (fun i hi => (h.1 i hi).2) h0 h3 hu ha o hrf

end Ern.Concurrency.MutexReal
