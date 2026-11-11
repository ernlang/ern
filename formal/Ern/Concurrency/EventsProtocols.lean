import Ern.Concurrency.EventsCompose

/-!
# Ordering by the reference protocols

Brief of milestone 4, event pass, task 5 (`formal/reports/spec2-m4-events.md`): the `hb` order
established by the reference protocols `spawn`, `join` (WC5.1 C47) and the mutex (WC5.1 C48) on
the event graph of `Ern.Concurrency.Events`. The edge of the mutex is the abstract one, from
`unlock(e)` to the next successful `acquire(e)`; its realization by `rf` is `OB-C05`. The recovery
of an abandoned grant by `resetLock` is outside `lock_orders` (WC5.1 C49).
-/

namespace Ern.Concurrency

open Ern.MemoryModel.Access

/-! ## `spawn` (WC5.1 C32 item 2, C47) -/

/-- `spawn_orders` (brief, task 5; WC5.1 C47): on the `ok` steps of a trace, every step of the
creator up to the `spawn` or `spawnVal` creating `c` (step `s`) is `hb`-before every step of `c`.
That the steps of `c` come after `s` is a consequence of the trace (`step_after_create`). -/
theorem spawn_orders {k : K} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg}
    {lbls : List Label} (hs : ∀ i (h : i < lbls.length), LStep k L lbls[i] (σ i) (σ (i + 1)))
    {s p q : Nat} (hsp : (lbls[s]?).map Label.creates = some true) (hps : p ≤ s)
    (hp : (lbls[p]?).map Label.ctx = (lbls[s]?).map Label.ctx) (hq : q < lbls.length)
    (hc : (lbls[q]?).map Label.ctx = some (created σ s)) : HB σ lbls (.step p) (.step q) := by
  have hsq := step_after_create hs hsp hq hc
  have hsw : SW lbls (.step s) (.start s) := ⟨rfl, hsp⟩
  have hpo : PO σ lbls (.start s) (.step q) := ⟨hsq, hq, hsp, hc⟩
  have h2 : HB σ lbls (.step s) (.step q) := .tail (.single (Or.inr hsw)) (Or.inl hpo)
  rcases Nat.lt_or_ge p s with h | h
  · have hpo' : PO σ lbls (.step p) (.step s) := ⟨h, Nat.lt_trans hsq hq, hp⟩
    exact .trans (.single (Or.inl hpo')) h2
  · obtain rfl : p = s := Nat.le_antisymm hps h
    exact h2

/-! ## `terminate` and `join` (WC5.1 C32 item 3, C47) -/

/-- The completed contexts after a step (WC5.1 C7 effect): those before it, and the context it
terminates. -/
theorem lifeEff_done (lbl : Label) (ls : List Life) (d : Nat) :
    (lbl.lifeEff ls)[d]? = some .done ↔
      ls[d]? = some .done ∨ (lbl.termOf = some d ∧ d < ls.length) := by
  have noTerm : ∀ {o : Option Nat}, o = none →
      (ls[d]? = some .done ↔ ls[d]? = some .done ∨ (o = some d ∧ d < ls.length)) :=
    fun ho => by
      subst ho
      exact ⟨Or.inl, fun h => h.elim id (fun h' => by cases h'.1)⟩
  have append : (ls ++ [.live])[d]? = some .done ↔ ls[d]? = some .done := by
    rcases Nat.lt_or_ge d ls.length with h | h
    · rw [List.getElem?_append_left h]
    · rw [List.getElem?_append_right h, List.getElem?_eq_none_iff.2 h]
      cases d - ls.length with
      | zero => exact ⟨(fun h' => by cases h'), (fun h' => by cases h')⟩
      | succ n => exact ⟨(fun h' => by cases h'), (fun h' => by cases h')⟩
  cases lbl with
  | spawn => exact append.trans (noTerm rfl)
  | spawnVal => exact append.trans (noTerm rfl)
  | terminate c =>
    show (ls.set c .done)[d]? = some .done ↔ _
    by_cases hcd : c = d
    · subst hcd
      by_cases hl : c < ls.length
      · rw [List.getElem?_set_self hl]
        exact ⟨fun _ => Or.inr ⟨rfl, hl⟩, fun _ => rfl⟩
      · rw [List.set_eq_of_length_le (Nat.le_of_not_lt hl),
          List.getElem?_eq_none_iff.2 (Nat.le_of_not_lt hl)]
        exact ⟨(fun h => by cases h), (fun h => h.elim (fun h' => by cases h')
          (fun h' => absurd h'.2 hl))⟩
    · rw [List.getElem?_set_ne hcd]
      exact ⟨Or.inl, fun h => h.elim id (fun h' => absurd (Option.some.inj h'.1) hcd)⟩
  | _ => exact noTerm rfl

/-- A context is live exactly when its lifecycle state is `live` (WC5.1 C2). -/
theorem SC.live_iff {s : SC} {d : Nat} : s.Live d ↔ s.lifes[d]? = some .live := by
  unfold SC.Live SC.lifes
  rw [List.getElem?_map]
  cases s.C[d]? with
  | none => exact ⟨False.elim, fun h => by cases h⟩
  | some x =>
    show x.life = .live ↔ some x.life = some .live
    exact ⟨fun h => by rw [h], Option.some.inj⟩

/-- On the `ok` steps of a trace whose first state has no completed context, a context is
completed at position `t` exactly when it is terminated by a step before `t` (WC5.1 C7). -/
theorem done_iff {k : K} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg}
    {lbls : List Label} (hs : ∀ i (h : i < lbls.length), LStep k L lbls[i] (σ i) (σ (i + 1)))
    (h0 : ∀ x ∈ (σ 0).1.C, x.life = .live) (d : Nat) :
    ∀ t, t ≤ lbls.length → ((σ t).1.lifes[d]? = some .done ↔
      ∃ p, p < t ∧ (lbls[p]?).bind Label.termOf = some d)
  | 0, _ => by
    refine ⟨fun h => ?_, fun ⟨_, hp, _⟩ => absurd hp (Nat.not_lt_zero _)⟩
    unfold SC.lifes at h
    rw [List.getElem?_map] at h
    cases hx : (σ 0).1.C[d]? with
    | none => rw [hx] at h; cases h
    | some x =>
      rw [hx] at h
      have := h0 x (List.mem_of_getElem? hx)
      rw [Option.map_some, this] at h; cases h
  | t + 1, ht => by
    have ih := done_iff hs h0 d t (Nat.le_of_succ_le ht)
    obtain ⟨hl, he⟩ := lstep_lifes (hs t ht)
    rw [he, lifeEff_done, ih]
    constructor
    · rintro (⟨p, hp, hpd⟩ | ⟨hd, -⟩)
      · exact ⟨p, Nat.lt_succ_of_lt hp, hpd⟩
      · exact ⟨t, Nat.lt_succ_self _, by rw [List.getElem?_eq_getElem ht]; exact hd⟩
    · rintro ⟨p, hp, hpd⟩
      rcases Nat.lt_or_ge p t with h | h
      · exact Or.inl ⟨p, h, hpd⟩
      · obtain rfl : p = t := by omega
        rw [List.getElem?_eq_getElem ht, Option.bind_some] at hpd
        refine Or.inr ⟨hpd, ?_⟩
        have hc : lbls[p].ctx = d := by
          revert hpd; cases lbls[p] <;> simp [Label.termOf, Label.ctx]
        rw [hc] at hl
        have := SC.lt_of_live hl
        unfold SC.lifes; rw [List.length_map]; exact this

/-- A successful `join d` finds `d` completed (WC5.1 C8). -/
theorem lstep_join_done {k : K} {L : MutexLayout} {c d : Nat} {st st' : SC × SyncReg × ArenaReg}
    (h : LStep k L (.join c d) st st') : st.1.lifes[d]? = some .done := by
  cases h with
  | @join s _ _ _ _ _ hjs =>
    cases hjs with
    | ok _ hd =>
      unfold SC.lifes; rw [List.getElem?_map]
      revert hd; cases s.C[d]? with
      | none => exact False.elim
      | some x => intro hd; show some x.life = _; rw [show x.life = .done from hd]

/-- `join_orders` (brief, task 5; WC5.1 C47): on the `ok` steps of a trace whose first state has no
completed context (the initial states of Spec 1 §47), every step of a context `d` is `hb`-before
every successful `join` of `d`. That every step of `d` comes before its `terminate`, and that this
`terminate` comes before the `join`, are consequences of the trace (`done_iff`). -/
theorem join_orders {k : K} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg}
    {lbls : List Label} (hs : ∀ i (h : i < lbls.length), LStep k L lbls[i] (σ i) (σ (i + 1)))
    (h0 : ∀ x ∈ (σ 0).1.C, x.life = .live) {q j d : Nat} (hq : q < lbls.length)
    (hcq : (lbls[q]?).map Label.ctx = some d) (hj : j < lbls.length)
    (hjd : (lbls[j]?).bind Label.joinOf = some d) : HB σ lbls (.step q) (.step j) := by
  -- `d` is completed at the `join`
  have hdone : (σ j).1.lifes[d]? = some .done := by
    rw [List.getElem?_eq_getElem hj, Option.bind_some] at hjd
    have hstep := hs j hj
    generalize lbls[j] = lbl at hjd hstep
    cases lbl <;> simp only [Label.joinOf, reduceCtorEq, Option.some.injEq] at hjd
    subst hjd
    exact lstep_join_done hstep
  obtain ⟨t, htj, htd⟩ := (done_iff hs h0 d j (Nat.le_of_lt hj)).1 hdone
  have htl : t < lbls.length := Nat.lt_trans htj hj
  -- every step of `d` comes no later than its `terminate`
  have hqt : q ≤ t := by
    refine Nat.le_of_not_lt fun htq => ?_
    have hl := (lstep_lifes (hs q hq)).1
    rw [List.getElem?_eq_getElem hq, Option.map_some] at hcq
    rw [Option.some.inj hcq] at hl
    have hd' := (done_iff hs h0 d q (Nat.le_of_lt hq)).2 ⟨t, htq, htd⟩
    rw [SC.live_iff.1 hl] at hd'; cases hd'
  have hsw : SW lbls (.step t) (.step j) := by
    refine ⟨htj, hj, Or.inl ?_⟩
    rw [htd]; exact hjd
  rcases Nat.lt_or_ge q t with h | h
  · have hct : (lbls[t]?).map Label.ctx = some d := by
      rw [List.getElem?_eq_getElem htl, Option.bind_some] at htd
      rw [List.getElem?_eq_getElem htl, Option.map_some]
      revert htd; cases lbls[t] <;> simp [Label.termOf, Label.ctx]
    have hpo : PO σ lbls (.step q) (.step t) := ⟨h, htl, hcq.trans hct.symm⟩
    exact .tail (.single (Or.inl hpo)) (Or.inr hsw)
  · obtain rfl : q = t := Nat.le_antisymm hqt h
    exact .single (Or.inr hsw)

/-! ## The reference mutex (WC5.1 C48) -/

/-- `lock_orders` (brief, task 5; WC5.1 C48): for an entry `e`, an `unlock(e)` (step `u`) is
`hb`-before every successful `acquire(e)` after it (step `a`), as long as every intermediate
`acquire(e)` is given back, before `a`, by an `unlock(e)` that it is `hb`-before. The statement
reads the labels only. -/
theorem lock_orders {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} {e a : Nat}
    (ha : a < lbls.length) (hacq : (lbls[a]?).bind Label.acquireOf = some e) :
    ∀ {u : Nat}, u < a → (lbls[u]?).bind Label.unlockOf = some e →
      (∀ p, u < p → p < a → (lbls[p]?).bind Label.acquireOf = some e →
        ∃ p', p < p' ∧ p' < a ∧ (lbls[p']?).bind Label.unlockOf = some e ∧
          HB σ lbls (.step p) (.step p')) →
      HB σ lbls (.step u) (.step a)
  | u, hua, hu, hmid => by
    -- the first `acquire(e)` after `u`
    obtain ⟨p, -, hpa, hpp, hmin⟩ := find?_range_least (p := fun k =>
      decide (u < k) && decide ((lbls[k]?).bind Label.acquireOf = some e)) (n := a + 1)
      (a := a) (Nat.lt_succ_self _) (by rw [decide_eq_true hua, decide_eq_true hacq]; rfl)
    have hpp : (decide (u < p) && decide ((lbls[p]?).bind Label.acquireOf = some e)) = true := hpp
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hpp
    obtain ⟨hup, hpe⟩ := hpp
    have hsw : SW lbls (.step u) (.step p) := by
      refine ⟨hup, Nat.lt_of_le_of_lt hpa ha, Or.inr ?_⟩
      rw [hu]
      refine ⟨hpe, fun k hk huk hke => ?_⟩
      have hm : (decide (u < k) && decide ((lbls[k]?).bind Label.acquireOf = some e)) = false :=
        hmin k (List.mem_range.1 hk)
      rw [decide_eq_true huk, decide_eq_true hke] at hm
      cases hm
    rcases Nat.lt_or_ge p a with h | h
    · obtain ⟨p', hpp', hp'a, hp'u, hhb⟩ := hmid p hup h hpe
      have ih := lock_orders (σ := σ) ha hacq hp'a hp'u fun k hk hka hke =>
        hmid k (by omega) hka hke
      exact .trans (.single (Or.inr hsw)) (.trans hhb ih)
    · obtain rfl : p = a := Nat.le_antisymm hpa h
      exact .single (Or.inr hsw)
  termination_by u => a - u

/-- `lock_orders` when every intermediate `acquire(e)` is given back by an `unlock(e)` of the
context that took it: the grant is held by the current frame of that context (WC5.1 C15 effect,
C16), and `unlock` releases it under O3 (WC5.1 C17 item 2). -/
theorem lock_orders_holder {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} {e u a : Nat}
    (hua : u < a) (ha : a < lbls.length) (hu : (lbls[u]?).bind Label.unlockOf = some e)
    (hacq : (lbls[a]?).bind Label.acquireOf = some e)
    (hmid : ∀ p, u < p → p < a → (lbls[p]?).bind Label.acquireOf = some e →
      ∃ p', p < p' ∧ p' < a ∧ (lbls[p']?).bind Label.unlockOf = some e ∧
        (lbls[p']?).map Label.ctx = (lbls[p]?).map Label.ctx) :
    HB σ lbls (.step u) (.step a) :=
  lock_orders ha hacq hua hu fun p hup hpa hpe => by
    obtain ⟨p', h1, h2, h3, h4⟩ := hmid p hup hpa hpe
    exact ⟨p', h1, h2, h3, .single (Or.inl ⟨h1, Nat.lt_trans h2 ha, h4.symm⟩)⟩

end Ern.Concurrency
