import Ern.Concurrency.MutexReal.Coherence
import Ern.Concurrency.MutexReal.Classify
import Ern.Concurrency.Corpus.MutexEdge

/-!
# The strict mutex edge and the controller graph

Brief of milestone 4, slice 2, layer R, task 5 (`formal/reports/spec2-m4-mutexreal.md`): the strict
mutex edge of slice 1 (`SWS`, `corpus-spec2-m3.md` v9 §2 octies) against the controller graph of
`Ern.Concurrency.MutexReal.Graph`, under the declared realization.

* bridge (`bridge`): a strict edge from `unlock(e)` to `acquire(e)` is an `rf` edge between their
  events; it uses the invariant (no `unlock(e)` between them) and not hypothesis 3;
* synchronization (`bridge_sw`): that `rf` edge is an `sw` edge exactly when the order of the
  `unlock` is release-capable and that of the `acquire` acquire-capable (WC5.1 corrigé C32 item 1,
  C40); in particular for the reference realization (`bridge_sw_ref`);
* converse (`bridge_converse`): under hypothesis 3, an `rf` edge from the write of an `unlock(e)` to
  the RMW of an `acquire(e)` is a strict edge; without it W-TR refutes it
  (`converse_needs_fixed`).

These are conditional statements under the declared realization: they do not prove that a
physical realization satisfies it, and they do not discharge `OB-C05`.
-/

set_option autoImplicit false

namespace Ern.Concurrency.MutexReal

open Ern.MemoryModel.Access Ern.Concurrency

/-! ## Counting protocol steps -/

/-- The protocol steps of a prefix are those of a shorter prefix. -/
theorem ctlOps_take_take (e : Nat) (lbls : List Label) {m n : Nat} (hmn : m ≤ n) :
    ctlOps e (lbls.take n) = ctlOps e (lbls.take m) ++ ctlOps e ((lbls.take n).drop m) := by
  rw [← ctlOps_append]
  conv => lhs; rw [← List.take_append_drop m (lbls.take n)]
  rw [List.take_take, Nat.min_eq_left hmn]

/-- The number of protocol steps grows with the prefix. -/
theorem ctlOps_length_mono (e : Nat) (lbls : List Label) {m n : Nat} (hmn : m ≤ n) :
    (ctlOps e (lbls.take m)).length ≤ (ctlOps e (lbls.take n)).length := by
  rw [ctlOps_take_take e lbls hmn, List.length_append]
  exact Nat.le_add_right _ _

/-- Without a protocol step in `[m, n)`, the prefixes `m` and `n` have the same protocol steps. -/
theorem ctlOps_take_eq_of_none (e : Nat) {lbls : List Label} {m : Nat} :
    ∀ d, m + d ≤ lbls.length →
      (∀ q (hq : q < lbls.length), m ≤ q → q < m + d → ctlOp e lbls[q] = none) →
      ctlOps e (lbls.take (m + d)) = ctlOps e (lbls.take m)
  | 0, _, _ => rfl
  | d + 1, hd, h => by
    have hq : m + d < lbls.length := by omega
    rw [← Nat.add_assoc, ctlOps_take_succ e hq, h (m + d) hq (Nat.le_add_right m d)
      (Nat.lt_succ_self _), Option.toList_none, List.append_nil]
    exact ctlOps_take_eq_of_none e d (by omega) fun q hq' h1 h2 => h q hq' h1 (by omega)

/-- With as many protocol steps in the prefixes `m` and `n`, there is none in `[m, n)`. -/
theorem ctlOps_none_of_length (e : Nat) {lbls : List Label} {m n : Nat}
    (hlen : (ctlOps e (lbls.take n)).length = (ctlOps e (lbls.take m)).length) :
    ∀ q (hq : q < lbls.length), m ≤ q → q < n → ctlOp e lbls[q] = none := by
  intro q hq h1 h2
  cases hc : ctlOp e lbls[q] with
  | none => rfl
  | some p =>
    exfalso
    have hs := ctlOps_take_succ e hq
    rw [hc] at hs
    have h3 : (ctlOps e (lbls.take (q + 1))).length = (ctlOps e (lbls.take q)).length + 1 := by
      rw [hs]; simp
    have h4 := ctlOps_length_mono e lbls h1
    have h5 := ctlOps_length_mono e lbls (show q + 1 ≤ n by omega)
    omega

/-- The label of a protocol step on `e`. -/
theorem ctlOp_label {e : Nat} {lbl : Label} {c : Nat} {op : CtlOp}
    (h : ctlOp e lbl = some (c, op)) :
    lbl = match op with
      | .acq => .acquire c e
      | .unl => .unlock c e
      | .rst => .resetLock c e := by
  cases lbl <;> simp only [ctlOp, reduceCtorEq] at h
  all_goals (split at h <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h)
  all_goals (obtain ⟨rfl, rfl⟩ := h; subst_vars; rfl)

/-- A step that is no protocol step on `e` is no `acquire(e)`. -/
theorem acquireOf_ne {e : Nat} {lbl : Label} (h : ctlOp e lbl = none) :
    lbl.acquireOf ≠ some e := by
  cases lbl with
  | acquire c i =>
    intro h'; simp only [Label.acquireOf, Option.some.injEq] at h'; subst h'; simp [ctlOp] at h
  | _ => simp [Label.acquireOf]

/-- A step that is no protocol step on `e` is no `resetLock(e)`. -/
theorem resetLockOf_ne {e : Nat} {lbl : Label} (h : ctlOp e lbl = none) :
    lbl.resetLockOf ≠ some e := by
  cases lbl with
  | resetLock c i =>
    intro h'; simp only [Label.resetLockOf, Option.some.injEq] at h'; subst h'; simp [ctlOp] at h
  | _ => simp [Label.resetLockOf]

/-- An `unlock` finds a recorded grant (WC5.1 corrigé C17 item 1). -/
theorem unlock_grant {k : K} {L : MutexLayout} {c i : Nat} {st st' : SC × SyncReg × ArenaReg}
    (h : LStep k L (.unlock c i) st st') : ∃ x g, st.2.1[i]? = some x ∧ x.grant = some g := by
  cases h with
  | unlock hu => obtain ⟨-, x, g, hx, -, hg, -⟩ := hu; exact ⟨x, g, hx, hg⟩

/-- The kind of the event of a protocol step on `e`. -/
theorem kind?_ctlIdx (o : Ords) (e : Nat) {lbls : List Label} {i : Nat} (hi : i < lbls.length)
    {c : Nat} {op : CtlOp} (h : ctlOp e lbls[i] = some (c, op)) :
    (ctlGraph o e lbls).kind? (ctlIdx e lbls i) = some (op.kind o) := by
  simp [EventModel.Graph.kind?, ctlGraph_ev o e hi h]

/-! ## Bridge -/

/-- Brief, task 5, bridge: along the `ok` steps of a trace whose first state has no taken grant
for entry `e`, if the strict mutex edge (`SWS`, `corpus-spec2-m3.md` v9 §2 octies) relates
`unlock(e)` at step `u` to the step `a`, then in the controller graph `rf` relates the write of `u`
to the RMW of `a` (WC5.1 corrigé C32 item 1, C48). Between `u` and `a` there is no `acquire(e)`
(`SWS`), no `resetLock(e)` (`MutexGap`), and no `unlock(e)`: the invariant (`ctl_invariant`) makes
the grant `none` after `u`, and `unlock` needs a recorded grant. The `ctlAt` clauses of `MutexGap`,
hence hypothesis 3, are not used. -/
theorem bridge {k : K} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label}
    (hs : ∀ i (h : i < lbls.length), LStep k L lbls[i] (σ i) (σ (i + 1))) {e : Nat}
    (h0 : ∀ x, (σ 0).2.1[e]? = some x → x.grant = none) {u a c : Nat}
    (hu : lbls[u]? = some (.unlock c e)) (hsw : SWS σ L lbls (.step u) (.step a)) (o : Ords) :
    EventModel.RF (ctlGraph o e lbls) (ctlIdx e lbls u) (ctlIdx e lbls a) := by
  obtain ⟨hua, ha, hsw'⟩ := hsw
  simp only [hu, Option.bind_some, Label.termOf, Label.unlockOf, OptP, false_or] at hsw'
  obtain ⟨hacq, hfirst, hgap, -, -⟩ := hsw'
  have hul : u < lbls.length := Nat.lt_trans hua ha
  have hu' : lbls[u] = .unlock c e := by
    rw [List.getElem?_eq_getElem hul] at hu; exact Option.some.inj hu
  have hopu : ctlOp e lbls[u] = some (c, .unl) := by rw [hu']; simp [ctlOp]
  have hsu := ctlOps_take_succ e hul
  rw [hopu] at hsu
  -- no protocol step on `e` strictly between `u` and `a`
  have hnone : ∀ p, p ≤ a → ∀ q (hq : q < lbls.length), u + 1 ≤ q → q < p →
      ctlOp e lbls[q] = none := by
    intro p
    induction p with
    | zero => intro _ q _ _ h; exact absurd h (Nat.not_lt_zero _)
    | succ p ih =>
      intro hp q hq h1 h2
      rcases Nat.lt_or_ge q p with hqp | hqp
      · exact ih (by omega) q hq h1 hqp
      · obtain rfl : q = p := by omega
        have hpl : q < lbls.length := hq
        have heq : ctlOps e (lbls.take q) = ctlOps e (lbls.take (u + 1)) := by
          have := ctlOps_take_eq_of_none e (m := u + 1) (q - (u + 1)) (by omega)
            fun r hr hr1 hr2 => ih (by omega) r hr hr1 (by omega)
          rwa [Nat.add_sub_cancel' h1] at this
        obtain ⟨hA, hB, -⟩ := ctl_invariant hs h0 o q (Nat.le_of_lt hpl)
        have hex : ∃ x, (σ q).2.1[e]? = some x := by
          cases hx : (σ q).2.1[e]? with
          | some x => exact ⟨x, rfl⟩
          | none =>
            have := hB hx
            rw [heq, hsu] at this
            simp at this
        obtain ⟨x, hx⟩ := hex
        have hlast : lastW (ctlGraph o e (lbls.take q)) = some 0 := by
          unfold ctlGraph ctlEvs
          rw [heq, hsu, List.map_append]
          simp [lastW, mkGraph, EventModel.Graph.valW, EventModel.Graph.kind?,
            EventModel.Graph.ev?, CtlOp.kind]
        have hgx : x.grant = none := (hA x hx).2 hlast
        cases hc : ctlOp e lbls[q] with
        | none => rfl
        | some pc =>
          obtain ⟨c', op⟩ := pc
          have hl := ctlOp_label hc
          exfalso
          cases op with
          | acq =>
            simp only at hl
            have := hfirst q (List.mem_range.2 (by omega)) (by omega)
            rw [List.getElem?_eq_getElem hpl, hl] at this
            simp [Label.acquireOf] at this
          | unl =>
            have hst := hs q hpl
            simp only at hl
            rw [hl] at hst
            obtain ⟨y, g, hy, hyg⟩ := unlock_grant hst
            rw [hx] at hy; cases hy
            rw [hgx] at hyg; cases hyg
          | rst =>
            simp only at hl
            have := hgap q (List.mem_range.2 (by omega)) (by omega)
            rw [List.getElem?_eq_getElem hpl, hl] at this
            simp [Label.resetLockOf] at this
  obtain ⟨ca, hla⟩ : ∃ ca, lbls[a] = .acquire ca e := by
    rw [List.getElem?_eq_getElem ha] at hacq
    cases hl : lbls[a] <;> simp [hl, Label.acquireOf] at hacq ⊢
    exact hacq
  have hopa : ctlOp e lbls[a] = some (ca, .acq) := by rw [hla]; simp [ctlOp]
  have heqa : ctlOps e (lbls.take a) = ctlOps e (lbls.take (u + 1)) := by
    have := ctlOps_take_eq_of_none e (m := u + 1) (a - (u + 1)) (by omega)
      fun r hr hr1 hr2 => hnone a (Nat.le_refl _) r hr hr1 (by omega)
    rwa [Nat.add_sub_cancel' (show u + 1 ≤ a by omega)] at this
  have hlen : (ctlOps e (lbls.take a)).length = (ctlOps e (lbls.take u)).length + 1 := by
    rw [heqa, hsu]; simp
  have hidx : ctlIdx e lbls a = ctlIdx e lbls u + 1 := by
    simp only [ctlIdx, hlen]
  rw [hidx]
  show EventModel.RF (mkGraph (ctlEvs o e lbls)) _ _
  refine rf_mkGraph.2 ⟨rfl, ?_⟩
  have hu1 : ctlIdx e lbls u = (ctlOps e (lbls.take a)).length := by simp only [ctlIdx, hlen]
  rw [hu1, ctlEvs_at o e ha hopa]
  simp [CtlOp.kind, kindIsRmw]

/-! ## Synchronization -/

/-- Brief, task 5, synchronization: under the hypotheses of `bridge`, `sw` relates the write of the
`unlock(e)` at `u` and the RMW of the `acquire(e)` at `a` exactly when the order of the `unlock` is
release-capable and the order of the `acquire` acquire-capable (WC5.1 corrigé C32 item 1, C40). -/
theorem bridge_sw {k : K} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg}
    {lbls : List Label} (hs : ∀ i (h : i < lbls.length), LStep k L lbls[i] (σ i) (σ (i + 1)))
    {e : Nat} (h0 : ∀ x, (σ 0).2.1[e]? = some x → x.grant = none) {u a c : Nat}
    (hu : lbls[u]? = some (.unlock c e)) (hsw : SWS σ L lbls (.step u) (.step a)) (o : Ords) :
    EventModel.SW (ctlGraph o e lbls) (ctlIdx e lbls u) (ctlIdx e lbls a) ↔
      (o.rel = .rel ∨ o.rel = .sc) ∧ (o.acq = .acq ∨ o.acq = .acqRel ∨ o.acq = .sc) := by
  have hrf := bridge hs h0 hu hsw o
  obtain ⟨hua, ha, hsw'⟩ := hsw
  simp only [hu, Option.bind_some, Label.termOf, Label.unlockOf, OptP, false_or] at hsw'
  have hacq := hsw'.1
  have hul : u < lbls.length := Nat.lt_trans hua ha
  have hopu : ctlOp e lbls[u] = some (c, .unl) := by
    rw [List.getElem?_eq_getElem hul] at hu; rw [Option.some.inj hu]; simp [ctlOp]
  obtain ⟨ca, hla⟩ : ∃ ca, lbls[a] = .acquire ca e := by
    rw [List.getElem?_eq_getElem ha] at hacq
    cases hl : lbls[a] <;> simp [hl, Label.acquireOf] at hacq ⊢
    exact hacq
  have hopa : ctlOp e lbls[a] = some (ca, .acq) := by rw [hla]; simp [ctlOp]
  have hku := kind?_ctlIdx o e hul hopu
  have hka := kind?_ctlIdx o e ha hopa
  unfold EventModel.SW EventModel.Graph.relCap EventModel.Graph.acqCap
  rw [hku, hka]
  simp only [CtlOp.kind, hrf, true_and]
  cases o.rel <;> cases o.acq <;> simp

/-- Brief, task 5: for the reference realization (`acquire`, `release`, `relaxed`), the strict
mutex edge is an `sw` edge of the controller graph. -/
theorem bridge_sw_ref {k : K} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg}
    {lbls : List Label} (hs : ∀ i (h : i < lbls.length), LStep k L lbls[i] (σ i) (σ (i + 1)))
    {e : Nat} (h0 : ∀ x, (σ 0).2.1[e]? = some x → x.grant = none) {u a c : Nat}
    (hu : lbls[u]? = some (.unlock c e)) (hsw : SWS σ L lbls (.step u) (.step a)) :
    EventModel.SW (ctlGraph refOrds e lbls) (ctlIdx e lbls u) (ctlIdx e lbls a) :=
  (bridge_sw hs h0 hu hsw refOrds).2 ⟨Or.inl rfl, Or.inl rfl⟩

/-! ## Converse -/

/-- Hypothesis 3 of the brief, controller fixed: the controller of entry `e` designates one leaf in
every state of the trace in which the entry exists (WC5.1 corrigé C12, C21 item 3). -/
def CtlFixed (σ : Nat → SC × SyncReg × ArenaReg) (L : MutexLayout) (lbls : List Label)
    (e : Nat) : Prop :=
  ∃ ctl, ∀ k, k ≤ lbls.length → ((σ k).2.1[e]?).isSome → ctlAt σ L e k = some ctl

/-- Brief, task 5, converse: along the `ok` steps of a trace whose first state has no taken grant
for entry `e`, under hypothesis 3 (`CtlFixed`), if in the controller graph `rf` relates the write
of an `unlock(e)` at step `u` to the RMW of an `acquire(e)` at step `a`, then the strict mutex edge
relates `u` to `a`. The `rf` edge makes the two events adjacent, so no protocol step on `e` lies
between the steps; hypothesis 3 gives the `ctlAt` clauses of `MutexGap`. -/
theorem bridge_converse {k : K} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg}
    {lbls : List Label} (hs : ∀ i (h : i < lbls.length), LStep k L lbls[i] (σ i) (σ (i + 1)))
    {e : Nat} (h0 : ∀ x, (σ 0).2.1[e]? = some x → x.grant = none) (h3 : CtlFixed σ L lbls e)
    {u a cu ca : Nat} (hu : lbls[u]? = some (.unlock cu e)) (ha : lbls[a]? = some (.acquire ca e))
    (o : Ords) (hrf : EventModel.RF (ctlGraph o e lbls) (ctlIdx e lbls u) (ctlIdx e lbls a)) :
    SWS σ L lbls (.step u) (.step a) := by
  have hidx : ctlIdx e lbls a = ctlIdx e lbls u + 1 := (rf_mkGraph.1 hrf).1
  have hul : u < lbls.length := by
    cases h : lbls[u]? with
    | none => rw [h] at hu; cases hu
    | some _ => exact (List.getElem?_eq_some_iff.1 h).1
  have hal : a < lbls.length := by
    cases h : lbls[a]? with
    | none => rw [h] at ha; cases ha
    | some _ => exact (List.getElem?_eq_some_iff.1 h).1
  have hopu : ctlOp e lbls[u] = some (cu, .unl) := by
    rw [List.getElem?_eq_getElem hul] at hu; rw [Option.some.inj hu]; simp [ctlOp]
  have hopa : ctlOp e lbls[a] = some (ca, .acq) := by
    rw [List.getElem?_eq_getElem hal] at ha; rw [Option.some.inj ha]; simp [ctlOp]
  have hsu := ctlOps_take_succ e hul
  rw [hopu] at hsu
  have hsa := ctlOps_take_succ e hal
  rw [hopa] at hsa
  have hsu' : (ctlOps e (lbls.take (u + 1))).length = (ctlOps e (lbls.take u)).length + 1 := by
    rw [hsu]; simp
  have hsa' : (ctlOps e (lbls.take (a + 1))).length = (ctlOps e (lbls.take a)).length + 1 := by
    rw [hsa]; simp
  have hidx' : (ctlOps e (lbls.take a)).length = (ctlOps e (lbls.take u)).length + 1 := by
    simp only [ctlIdx] at hidx; omega
  have hua : u < a := by
    refine Nat.lt_of_not_le fun hau => ?_
    rcases Nat.eq_or_lt_of_le hau with rfl | hau
    · rw [hu] at ha; cases ha
    · have := ctlOps_length_mono e lbls (show a + 1 ≤ u from hau)
      omega
  have hnone := ctlOps_none_of_length e (lbls := lbls) (m := u + 1) (n := a) (by omega)
  -- the entry exists from `u + 1` on
  obtain ⟨ctl, hctl⟩ := h3
  have hex : ∀ q, u + 1 ≤ q → q ≤ a → ctlAt σ L e q = some ctl := by
    intro q h1 h2
    refine hctl q (by omega) ?_
    obtain ⟨-, hB, -⟩ := ctl_invariant hs h0 o q (by omega)
    cases hx : (σ q).2.1[e]? with
    | some _ => rfl
    | none =>
      have h5 : (ctlOps e (lbls.take (u + 1))).length ≤ (ctlOps e (lbls.take q)).length :=
        ctlOps_length_mono e lbls h1
      rw [hB hx, List.length_nil] at h5
      omega
  refine ⟨hua, hal, Or.inr ?_⟩
  simp only [hu, ha, Option.bind_some, Label.unlockOf, Label.acquireOf, OptP, true_and]
  refine ⟨fun p hp hup => ?_, ⟨fun p hp hup => ?_, ?_, fun q hq h1 => ?_⟩⟩
  · have hpl : p < lbls.length := Nat.lt_trans (List.mem_range.1 hp) hal
    rw [List.getElem?_eq_getElem hpl, Option.bind_some]
    exact acquireOf_ne (hnone p hpl hup (List.mem_range.1 hp))
  · have hpl : p < lbls.length := Nat.lt_trans (List.mem_range.1 hp) hal
    rw [List.getElem?_eq_getElem hpl, Option.bind_some]
    exact resetLockOf_ne (hnone p hpl hup (List.mem_range.1 hp))
  · rw [hex (u + 1) (Nat.le_refl _) (by omega)]; simp
  · rw [hex q h1 (by have := List.mem_range.1 hq; omega), hex (u + 1) (Nat.le_refl _) (by omega)]

open Ern.Concurrency.Corpus.MutexEdge in
/-- Brief, task 5, the converse without hypothesis 3 is false: in W-TR (`corpus-spec2-m3.md` v9
§2 octies), a `Run5R` from the initial state, the controller graph of entry `e` has `rf` from the
write of the `unlock(e)` (step 7) to the RMW of the `acquire(e)` (step 10), the `transfer` of step 9
being no protocol step, while the strict mutex edge does not relate them; the controller moves from
`lock` (place 2) to `lock′` (place 6) at step 9. -/
theorem converse_needs_fixed : Run5R Ern.Concurrency.Corpus.KM Ern.Concurrency.Traces.L0 trσ trLbls ∧
    trLbls[7]? = some (.unlock 1 0) ∧ trLbls[10]? = some (.acquire 0 0) ∧
    EventModel.RF (ctlGraph refOrds 0 trLbls) (ctlIdx 0 trLbls 7) (ctlIdx 0 trLbls 10) ∧
    ¬ SWS trσ Ern.Concurrency.Traces.L0 trLbls (.step 7) (.step 10) ∧
    ctlAt trσ Ern.Concurrency.Traces.L0 0 9 = some 2 ∧
    ctlAt trσ Ern.Concurrency.Traces.L0 0 10 = some 6 :=
  ⟨W_TR_run.2, rfl, rfl, by decide, by decide, by decide, by decide⟩

end Ern.Concurrency.MutexReal
