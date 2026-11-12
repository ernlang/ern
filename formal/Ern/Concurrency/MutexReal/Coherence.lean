import Ern.Concurrency.MutexReal.Graph

/-!
# Invariant and coherence of the controller graph

Brief of milestone 4, slice 2, layer R, task 3 (`formal/reports/spec2-m4-mutexreal.md`):

* the invariant: along the trace, the recorded grant of `e` is `none` exactly when the last
  modification of the controller wrote `0` (`ctl_invariant`); it reads only the registry, so it
  covers the abandoned grant, recorded and inactive with the controller at `1`;
* coherence: the controller graph is well typed for every well-typed triple of orders and
  `EventConsistent` for every triple (`ctlGraph_coherent`).

The coherence proof is split: a statement on lists of controller events (`mkGraph_consistent`:
every RMW reads `0` from the event before it), then the invariant, which gives that condition on a
trace. Neither needs `Encap5R`: they use the `ok` steps of the trace and the absence of a taken
grant for `e` in its first state.
-/

set_option autoImplicit false

namespace Ern.Concurrency.MutexReal

open Ern.MemoryModel.Access Ern.Concurrency

/-! ## Lists of controller events -/

/-- The events have the kinds of the declared realization (brief, hypothesis 1): a successful RMW
reading `0` and writing `1`, or an atomic write of `0`. -/
def CtlShape (evs : List EventModel.Ev) : Prop :=
  ∀ x ∈ evs, (∃ o, x.kind = .rmw o 0 1) ∨ ∃ o, x.kind = .wsh o 0

/-- Every RMW reads `0`: the event just before it, which it reads by hypothesis 2, wrote `0`. -/
def PredZero (evs : List EventModel.Ev) : Prop :=
  ∀ j x, evs[j]? = some x → kindIsRmw x.kind = true → (mkGraph evs).valW j = some 0

/-- The controller events of a trace have the kinds of the declared realization. -/
theorem ctlShape_ctlEvs (o : Ords) (e : Nat) (lbls : List Label) : CtlShape (ctlEvs o e lbls) := by
  intro x hx
  obtain ⟨⟨c, op⟩, -, rfl⟩ := List.mem_map.1 hx
  cases op
  · exact Or.inl ⟨o.acq, rfl⟩
  · exact Or.inr ⟨o.rel, rfl⟩
  · exact Or.inr ⟨o.reset, rfl⟩

section Pure

variable {evs : List EventModel.Ev}

/-- Size of `mkGraph`. -/
theorem size_mkGraph : (mkGraph evs).size = evs.length + 1 := rfl

/-- `mo` of `mkGraph` is the order of the event indices. -/
theorem mo_mkGraph {a b : Nat} : EventModel.MO (mkGraph evs) a b ↔ a < b ∧ b < evs.length + 1 := by
  unfold EventModel.MO
  rw [show (mkGraph evs).mo = allPairs (evs.length + 1) from rfl, mem_allPairs, size_mkGraph]
  constructor
  · rintro ⟨h, -, -⟩; exact h
  · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2⟩, Nat.lt_trans h1 h2, h2⟩

/-- `rf` of `mkGraph`: each RMW reads the event just before it. -/
theorem rf_mkGraph {w r : Nat} : EventModel.RF (mkGraph evs) w r ↔
    r = w + 1 ∧ (evs[w]?.map fun x => kindIsRmw x.kind) = some true := by
  unfold EventModel.RF
  rw [show (mkGraph evs).rf = rfPairs evs from rfl, mem_rfPairs, size_mkGraph]
  constructor
  · rintro ⟨h, -, -⟩; exact h
  · rintro ⟨rfl, h⟩
    have hw : w < evs.length := by
      cases hx : evs[w]? with
      | none => rw [hx] at h; cases h
      | some _ => exact (List.getElem?_eq_some_iff.1 hx).1
    exact ⟨⟨rfl, h⟩, by omega, by omega⟩

/-- The kind of the initial write. -/
theorem kind?_mkGraph_zero : (mkGraph evs).kind? 0 = none := EventModel.kind?_zero _

/-- Every event of `mkGraph` of controller events is a modification (WC5.1 corrigé C31). -/
theorem isMod_mkGraph (hs : CtlShape evs) {i : Nat} (hi : i < evs.length + 1) :
    (mkGraph evs).isMod i = true := by
  cases i with
  | zero => simp [EventModel.Graph.isMod]
  | succ j =>
    have hj : j < evs.length := by omega
    have hk := kind?_mkGraph evs j
    rw [List.getElem?_eq_getElem hj, Option.map_some] at hk
    unfold EventModel.Graph.isMod
    rw [hk]
    rcases hs _ (List.getElem_mem hj) with ⟨o, ho⟩ | ⟨o, ho⟩ <;> rw [ho] <;> simp

/-- An event of `mkGraph` of controller events reads `x` exactly when it is an RMW. -/
theorem isReadX_mkGraph (hs : CtlShape evs) {r : Nat} (h : (mkGraph evs).isReadX r = true) :
    ∃ j x, r = j + 1 ∧ evs[j]? = some x ∧ ∃ o, x.kind = .rmw o 0 1 := by
  cases r with
  | zero =>
    unfold EventModel.Graph.isReadX at h; rw [kind?_mkGraph_zero] at h; cases h
  | succ j =>
    unfold EventModel.Graph.isReadX at h
    rw [kind?_mkGraph] at h
    cases hx : evs[j]? with
    | none => rw [hx] at h; cases h
    | some x =>
      refine ⟨j, x, rfl, hx, ?_⟩
      rcases hs x (List.mem_of_getElem? hx) with hr | ⟨o, ho⟩
      · exact hr
      · rw [hx] at h; simp [ho] at h

/-- Edges of `po ∪ sw` of `mkGraph` increase the index. -/
theorem poSw_lt_mkGraph {a b : Nat} (h : EventModel.PoSw (mkGraph evs) a b) : a < b := by
  rcases h with ⟨-, h, -⟩ | ⟨h, -⟩
  · exact h
  · rw [(rf_mkGraph.1 h).1]; exact Nat.lt_succ_self a

/-- `hb` of `mkGraph` increases the index. -/
theorem hb_lt_mkGraph {a b : Nat} (h : EventModel.HB (mkGraph evs) a b) : a < b := by
  rcases h with h | ⟨rfl, h, -⟩
  · induction h with
    | single h => exact poSw_lt_mkGraph h
    | tail _ h ih => exact Nat.lt_trans ih (poSw_lt_mkGraph h)
  · exact h

/-- Edges of `rf ∪ mo ∪ rb` of `mkGraph` increase the index. -/
theorem ecoBase_lt_mkGraph {a b : Nat} (h : EventModel.EcoBase (mkGraph evs) a b) : a < b := by
  rcases h with h | h | ⟨⟨w, -, hwa, hwb⟩, hne⟩
  · rw [(rf_mkGraph.1 h).1]; exact Nat.lt_succ_self a
  · exact (mo_mkGraph.1 h).1
  · have h1 := (rf_mkGraph.1 hwa).1
    have h2 := (mo_mkGraph.1 hwb).1
    omega

/-- `eco` of `mkGraph` increases the index. -/
theorem eco_lt_mkGraph {a b : Nat} (h : EventModel.ECO (mkGraph evs) a b) : a < b := by
  induction h with
  | single h => exact ecoBase_lt_mkGraph h
  | tail _ h ih => exact Nat.lt_trans ih (ecoBase_lt_mkGraph h)

/-- Brief, task 3: a list of controller events of the declared realization whose RMWs each read
`0` gives a consistent graph (WC5.1 corrigé C31, C33): the five conjuncts of `EventConsistent`.
`po`, `sw`, `rf`, `mo` and `rb` all increase the index, which gives coherence. -/
theorem mkGraph_consistent (hs : CtlShape evs) (hp : PredZero evs) :
    EventModel.EventConsistent (mkGraph evs) := by
  have hcoh : EventModel.Coherent (mkGraph evs) := fun a _ =>
    ⟨fun h => Nat.lt_irrefl _ (hb_lt_mkGraph h),
     fun b _ hab hba => Nat.lt_irrefl _ (Nat.lt_trans (hb_lt_mkGraph hab) (eco_lt_mkGraph hba))⟩
  refine ⟨⟨fun w hw r _ hwr => ?_, fun r _ hr => ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, hcoh,
    EventModel.hbIrrefl_of_coherent hcoh⟩
  · obtain ⟨rfl, hk⟩ := rf_mkGraph.1 hwr
    cases hx : evs[w]? with
    | none => rw [hx] at hk; cases hk
    | some x =>
      rw [hx] at hk
      have hxr : kindIsRmw x.kind = true := by simpa using hk
      obtain ⟨o, ho⟩ : ∃ o, x.kind = .rmw o 0 1 := by
        rcases hs x (List.mem_of_getElem? hx) with h | ⟨o, ho⟩
        · exact h
        · rw [ho] at hxr; cases hxr
      refine ⟨isMod_mkGraph hs (by rw [size_mkGraph] at hw; exact List.mem_range.1 hw), ?_, ?_⟩
      · unfold EventModel.Graph.isReadX; rw [kind?_mkGraph, hx]; simp [ho]
      · rw [hp w x hx hxr]
        simp [EventModel.Graph.valR, kind?_mkGraph, hx, ho]
  · obtain ⟨j, x, rfl, hx, o, ho⟩ := isReadX_mkGraph hs hr
    have hrf : EventModel.RF (mkGraph evs) j (j + 1) :=
      rf_mkGraph.2 ⟨rfl, by rw [hx]; simp [ho, kindIsRmw]⟩
    refine ⟨j, List.mem_range.2 hrf.2.1, hrf, fun w' _ h' => ?_⟩
    have := (rf_mkGraph.1 h').1
    omega
  · intro a ha b hb hab
    exact ⟨isMod_mkGraph hs (List.mem_range.1 ha), isMod_mkGraph hs (List.mem_range.1 hb)⟩
  · intro a _ h
    exact Nat.lt_irrefl _ (mo_mkGraph.1 h).1
  · intro a _ b _ c _ hab hbc
    exact mo_mkGraph.2 ⟨Nat.lt_trans (mo_mkGraph.1 hab).1 (mo_mkGraph.1 hbc).1,
      (mo_mkGraph.1 hbc).2⟩
  · intro a ha b hb _ _ hne
    have ha' := List.mem_range.1 ha
    have hb' := List.mem_range.1 hb
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact Or.inl (mo_mkGraph.2 ⟨h, hb'⟩)
    · exact Or.inr (mo_mkGraph.2 ⟨h, ha'⟩)
  · intro m _ _ w _ hwm
    obtain ⟨rfl, -⟩ := rf_mkGraph.1 hwm
    refine ⟨mo_mkGraph.2 ⟨Nat.lt_succ_self w, hwm.2.2⟩, fun c _ ⟨h1, h2⟩ => ?_⟩
    have := (mo_mkGraph.1 h1).1
    have := (mo_mkGraph.1 h2).1
    omega

/-- `valW` of `mkGraph` below the length of a prefix. -/
theorem valW_mkGraph_append {ys : List EventModel.Ev} {j : Nat} (hj : j ≤ evs.length) :
    (mkGraph (evs ++ ys)).valW j = (mkGraph evs).valW j := by
  cases j with
  | zero => rfl
  | succ j =>
    simp only [EventModel.Graph.valW, Nat.add_one_ne_zero, ↓reduceIte, kind?_mkGraph]
    rw [List.getElem?_append_left (by omega)]

end Pure

/-! ## Typing -/

/-- A triple of orders is well typed when each order is in its row of WC5.1 corrigé C40: the RMW
of `acquire` (every order), the writes of `unlock` and `resetLock` (`relaxed`, `release`,
`seq_cst`). -/
def Ords.WellTyped (o : Ords) : Prop :=
  (CtlOp.acq.kind o).OrdOk ∧ (CtlOp.unl.kind o).OrdOk ∧ (CtlOp.rst.kind o).OrdOk

/-- Decidability of `Ords.WellTyped`. -/
instance (o : Ords) : Decidable o.WellTyped := by unfold Ords.WellTyped; infer_instance

/-- Brief, task 3: for a well-typed triple of orders, the controller graph is well typed (WC5.1
corrigé C40). -/
theorem ctlGraph_wellTyped {o : Ords} (ho : o.WellTyped) (e : Nat) (lbls : List Label) :
    EventModel.WellTyped (ctlGraph o e lbls) := by
  intro x hx
  obtain ⟨⟨c, op⟩, -, rfl⟩ := List.mem_map.1 hx
  cases op
  · exact ho.1
  · exact ho.2.1
  · exact ho.2.2

/-! ## The invariant -/

/-- The value written by the last modification in `mo` of a graph. -/
def lastW (g : EventModel.Graph) : Option Nat := g.valW g.evs.length

/-- Change of entry `e` of the registry by a step `lbl`, from `r` to `r'`: `acquire(e)` finds the
grant `none` and records some grant; `unlock(e)` and `resetLock(e)` record `none`; any other step
keeps entry `e`, or creates it with grant `none` when it did not exist (`newMutex`). -/
def EntryStep (e : Nat) (lbl : Label) (r r' : SyncReg) : Prop :=
  match ctlOp e lbl with
  | some (_, .acq) => ∃ x, r[e]? = some x ∧ x.grant = none ∧ ∃ g, r'[e]? = some { x with grant := g }
      ∧ g ≠ none
  | some (_, _) => ∃ x, r[e]? = some x ∧ r'[e]? = some { x with grant := none }
  | none => r'[e]? = r[e]? ∨ (r[e]? = none ∧ ∃ x, r'[e]? = some x ∧ x.grant = none)

/-- Entry `e` of a registry after `set` at another index. -/
theorem getElem?_set_other {r : SyncReg} {i e : Nat} {y : SyncEntry} (h : i ≠ e) :
    (r.set i y)[e]? = r[e]? := List.getElem?_set_ne h

/-- The registry effect of an `ok` step on entry `e` (WC5.1 corrigé C13, C16–C18 effects; every
other labelled step keeps the registry). -/
theorem lstep_entry {k : K} {L : MutexLayout} {lbl : Label} {st st' : SC × SyncReg × ArenaReg}
    (h : LStep k L lbl st st') (e : Nat) : EntryStep e lbl st.2.1 st'.2.1 := by
  have keep : ∀ (l : Label), ctlOp e l = none → st'.2.1 = st.2.1 → EntryStep e l st.2.1 st'.2.1 :=
    fun l hl hr => by unfold EntryStep; rw [hl]; exact Or.inl (by rw [hr])
  cases h with
  | kernel => exact keep _ rfl rfl
  | spawn => exact keep _ rfl rfl
  | terminate => exact keep _ rfl rfl
  | join => exact keep _ rfl rfl
  | deriveSync => exact keep _ rfl rfl
  | spawnVal => exact keep _ rfl rfl
  | newArena => exact keep _ rfl rfl
  | issue => exact keep _ rfl rfl
  | reset => exact keep _ rfl rfl
  | @newMutex s reg ar c g st' hn =>
    obtain ⟨-, -, rfl⟩ := hn
    unfold EntryStep
    simp only [ctlOp]
    rcases Nat.lt_or_ge e reg.length with he | he
    · exact Or.inl (List.getElem?_append_left he)
    · rcases Nat.eq_or_lt_of_le he with rfl | he
      · refine Or.inr ⟨List.getElem?_eq_none_iff.2 (Nat.le_refl _), ⟨g, none⟩, ?_, rfl⟩
        simp
      · refine Or.inl ?_
        rw [List.getElem?_eq_none_iff.2 (by simp; omega), List.getElem?_eq_none_iff.2 (by omega)]
  | @acquire s reg ar c i st' ha =>
    obtain ⟨-, x, hx, ⟨-, hg, -⟩, -, rfl⟩ := ha
    unfold EntryStep
    by_cases hi : i = e
    · subst hi
      simp only [ctlOp, ↓reduceIte]
      refine ⟨x, hx, hg, some s.A.length, ?_, by simp⟩
      rw [List.getElem?_set_self (List.getElem?_eq_some_iff.1 hx).1]
    · simp only [ctlOp, hi, ↓reduceIte]
      exact Or.inl (getElem?_set_other hi)
  | @unlock s reg ar c i st' hu =>
    obtain ⟨-, x, g, hx, -, -, -, -, rfl⟩ := hu
    unfold EntryStep
    by_cases hi : i = e
    · subst hi
      simp only [ctlOp, ↓reduceIte]
      exact ⟨x, hx, List.getElem?_set_self (List.getElem?_eq_some_iff.1 hx).1⟩
    · simp only [ctlOp, hi, ↓reduceIte]
      exact Or.inl (getElem?_set_other hi)
  | @resetLock s reg ar c i st' hr =>
    obtain ⟨-, x, hx, -, -, -, rfl⟩ := hr
    unfold EntryStep
    by_cases hi : i = e
    · subst hi
      simp only [ctlOp, ↓reduceIte]
      exact ⟨x, hx, List.getElem?_set_self (List.getElem?_eq_some_iff.1 hx).1⟩
    · simp only [ctlOp, hi, ↓reduceIte]
      exact Or.inl (getElem?_set_other hi)

/-- The controller events of a prefix extended by one step. -/
theorem ctlEvs_take_succ (o : Ords) (e : Nat) {lbls : List Label} {n : Nat}
    (hn : n < lbls.length) :
    ctlEvs o e (lbls.take (n + 1)) = ctlEvs o e (lbls.take n) ++
      ((ctlOp e lbls[n]).toList.map fun p => (⟨p.1, p.2.kind o⟩ : EventModel.Ev)) := by
  rw [ctlEvs, ctlOps_take_succ e hn, List.map_append]; rfl

/-- The last value after appending an event. -/
theorem lastW_snoc (evs : List EventModel.Ev) (x : EventModel.Ev) :
    lastW (mkGraph (evs ++ [x])) = (mkGraph [x]).valW 1 := by
  simp [lastW, mkGraph, EventModel.Graph.valW, EventModel.Graph.kind?, EventModel.Graph.ev?]

/-- `PredZero` of a list extended by one event. -/
theorem predZero_snoc {evs : List EventModel.Ev} {x : EventModel.Ev} (hp : PredZero evs)
    (hx : kindIsRmw x.kind = true → lastW (mkGraph evs) = some 0) : PredZero (evs ++ [x]) := by
  intro j y hy hr
  rcases Nat.lt_or_ge j evs.length with hj | hj
  · rw [valW_mkGraph_append (Nat.le_of_lt hj)]
    rw [List.getElem?_append_left hj] at hy
    exact hp j y hy hr
  · have hj' : j = evs.length := by
      have := (List.getElem?_eq_some_iff.1 hy).1
      simp at this; omega
    subst hj'
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at hy
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hy
    subst hy
    rw [valW_mkGraph_append (Nat.le_refl _)]
    exact hx hr

/-- Brief, task 3, the invariant: along the `ok` steps of a trace whose first state has no taken
grant for entry `e`, at every state `n`, (1) when entry `e` exists, its recorded grant is `none`
exactly when the last modification of the controller (the `mo`-last event of the controller graph
of the steps before `n`) wrote `0`; (2) when it does not exist, no protocol step on `e` occurred;
(3) every RMW of the controller graph reads `0`. The statement reads only the registry, not the
activity of the grant: it covers the abandoned grant (WC5.1 corrigé C18), recorded and inactive,
with the controller at `1`. -/
theorem ctl_invariant {k : K} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg}
    {lbls : List Label} (hs : ∀ i (h : i < lbls.length), LStep k L lbls[i] (σ i) (σ (i + 1)))
    {e : Nat} (h0 : ∀ x, (σ 0).2.1[e]? = some x → x.grant = none) (o : Ords) :
    ∀ n, n ≤ lbls.length →
      (∀ x, (σ n).2.1[e]? = some x →
        (x.grant = none ↔ lastW (ctlGraph o e (lbls.take n)) = some 0)) ∧
      ((σ n).2.1[e]? = none → ctlOps e (lbls.take n) = []) ∧
      PredZero (ctlEvs o e (lbls.take n))
  | 0, _ => by
    refine ⟨fun x hx => ⟨fun _ => rfl, fun _ => h0 x hx⟩, fun _ => rfl, ?_⟩
    intro j y hy; simp [ctlEvs, ctlOps] at hy
  | n + 1, hn => by
    have hn' : n < lbls.length := hn
    obtain ⟨ihA, ihB, ihC⟩ := ctl_invariant hs h0 o n (Nat.le_of_lt hn')
    have hstep := lstep_entry (hs n hn') e
    have hevs := ctlEvs_take_succ o e hn'
    have hops := ctlOps_take_succ e hn'
    unfold ctlGraph
    rw [hevs, hops]
    unfold EntryStep at hstep
    cases hop : ctlOp e lbls[n] with
    | none =>
      rw [hop] at hstep
      simp only [Option.toList_none, List.map_nil, List.append_nil]
      refine ⟨fun x hx => ?_, fun hx => ?_, ihC⟩
      · rcases hstep with hst | ⟨hnone, y, hy, hyg⟩
        · rw [hst] at hx; exact ihA x hx
        · rw [hy] at hx; cases hx
          have hnil : ctlEvs o e (lbls.take n) = [] := by simp [ctlEvs, ihB hnone]
          rw [hnil]
          exact ⟨fun _ => rfl, fun _ => hyg⟩
      · rcases hstep with hst | ⟨-, y, hy, -⟩
        · rw [hst] at hx; exact ihB hx
        · rw [hy] at hx; cases hx
    | some p =>
      obtain ⟨c, op⟩ := p
      rw [hop] at hstep
      simp only [Option.toList_some, List.map_cons, List.map_nil]
      cases op with
      | acq =>
        obtain ⟨x, hx, hxg, g, hy, hg⟩ := hstep
        refine ⟨fun y hy' => ?_, fun hy' => (by rw [hy] at hy'; cases hy'), ?_⟩
        · rw [hy] at hy'; cases hy'
          rw [lastW_snoc]
          simp [mkGraph, EventModel.Graph.valW, EventModel.Graph.kind?, EventModel.Graph.ev?,
            CtlOp.kind, hg]
        · exact predZero_snoc ihC fun _ => (ihA x hx).1 hxg
      | unl =>
        obtain ⟨x, -, hy⟩ := hstep
        refine ⟨fun y hy' => ?_, fun hy' => (by rw [hy] at hy'; cases hy'), ?_⟩
        · rw [hy] at hy'; cases hy'
          rw [lastW_snoc]
          simp [mkGraph, EventModel.Graph.valW, EventModel.Graph.kind?, EventModel.Graph.ev?,
            CtlOp.kind]
        · exact predZero_snoc ihC fun h => by simp [CtlOp.kind, kindIsRmw] at h
      | rst =>
        obtain ⟨x, -, hy⟩ := hstep
        refine ⟨fun y hy' => ?_, fun hy' => (by rw [hy] at hy'; cases hy'), ?_⟩
        · rw [hy] at hy'; cases hy'
          rw [lastW_snoc]
          simp [mkGraph, EventModel.Graph.valW, EventModel.Graph.kind?, EventModel.Graph.ev?,
            CtlOp.kind]
        · exact predZero_snoc ihC fun h => by simp [CtlOp.kind, kindIsRmw] at h

/-! ## Coherence -/

/-- Brief, task 3, coherence: along the `ok` steps of a trace whose first state has no taken grant
for entry `e`, the controller graph is well typed for every well-typed triple of orders and
`EventConsistent` (WC5.1 corrigé C31, C33, C40). Consistency holds for every triple; typing needs a
well-typed one. -/
theorem ctlGraph_coherent {k : K} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg}
    {lbls : List Label} (hs : ∀ i (h : i < lbls.length), LStep k L lbls[i] (σ i) (σ (i + 1)))
    {e : Nat} (h0 : ∀ x, (σ 0).2.1[e]? = some x → x.grant = none) {o : Ords}
    (ho : o.WellTyped) :
    EventModel.WellTyped (ctlGraph o e lbls) ∧ EventModel.EventConsistent (ctlGraph o e lbls) := by
  refine ⟨ctlGraph_wellTyped ho e lbls, ?_⟩
  have h := (ctl_invariant hs h0 o lbls.length (Nat.le_refl _)).2.2
  rw [List.take_length] at h
  exact mkGraph_consistent (ctlShape_ctlEvs o e lbls) h

/-- Brief, task 3, coherence on a `Run5R` from a state with an empty registry, the first state of
every run from the initial state of Spec 1 §47. -/
theorem ctlGraph_coherent_run {k : K} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg}
    {lbls : List Label} (hr : Run5R k L σ lbls) (h0 : (σ 0).2.1 = []) (e : Nat) {o : Ords}
    (ho : o.WellTyped) :
    EventModel.WellTyped (ctlGraph o e lbls) ∧ EventModel.EventConsistent (ctlGraph o e lbls) :=
  ctlGraph_coherent (fun i h => (hr i h).2) (fun x hx => by rw [h0] at hx; cases hx) ho

/-- The reference realization is well typed (WC5.1 corrigé C40). -/
theorem refOrds_wellTyped : refOrds.WellTyped := by decide

end Ern.Concurrency.MutexReal
