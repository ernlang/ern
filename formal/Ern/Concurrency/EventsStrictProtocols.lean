import Ern.Concurrency.EventsStrict
import Ern.Concurrency.EventsProtocols

/-!
# Theorems on the strict graph

Brief of milestone 4, strict mutex edge, task 5 (`formal/reports/spec2-m4-events.md`, § Arête
stricte du mutex): `handoffOrdered_no_race`, `spawn_orders` and `join_orders` with the same
statements and hypotheses on strict `hb`; `lock_orders` on strict `hb` with no `resetLock(e)` and a
constant controller of `e` from the `unlock` to the `acquire` (WC5.1 C18 effect, C21 item 3, C48,
C49), and a finer form asking these conditions only between each `unlock(e)` and the next
`acquire(e)`.
-/

namespace Ern.Concurrency

open Ern.MemoryModel.Access

/-! ## Composition (WC5.1 C46, C52) -/

/-- `handoffOrdered_no_race` on the strict graph (brief, task 5; WC5.1 C52, ordinary leaves; C46
composition argument): under the hypotheses of `handoff_loss_exists_C`, strict `HandoffOrdered`
excludes strict `Race`. -/
theorem handoffOrdered_no_raceS {k : K} {L : MutexLayout} (hdd : DDSound k) {statics : Statics}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} (hst : StaticsOK statics)
    (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], [])) (hr : Run5C k L σ lbls)
    (ho : HandoffOrderedS σ L lbls) : ¬ RaceS σ L lbls := by
  rintro ⟨i, j, l, hp, hnb⟩
  obtain ⟨r, hls, hb⟩ := ho i j l hp
  obtain ⟨r', hls', hir, hrj, hctx⟩ := lossStep_own hdd hst h0 hr hp
  rw [hls] at hls'
  cases hls'
  obtain ⟨-, hj, -⟩ := hp
  have hpo : PO σ lbls (.step i) (.step r) := ⟨hir, Nat.lt_trans hrj hj, hctx.symm⟩
  exact hnb (.trans (.single (Or.inl hpo)) hb)

/-! ## `spawn` and `join` (WC5.1 C32 items 2 and 3, C47) -/

/-- `spawn_orders` on the strict graph (brief, task 5; WC5.1 C47): on the `ok` steps of a trace,
every step of the creator up to the `spawn` or `spawnVal` creating `c` (step `s`) is strictly
`hb`-before every step of `c`. -/
theorem spawn_ordersS {k : K} {L' L : MutexLayout}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label}
    (hs : ∀ i (h : i < lbls.length), LStep k L' lbls[i] (σ i) (σ (i + 1)))
    {s p q : Nat} (hsp : (lbls[s]?).map Label.creates = some true) (hps : p ≤ s)
    (hp : (lbls[p]?).map Label.ctx = (lbls[s]?).map Label.ctx) (hq : q < lbls.length)
    (hc : (lbls[q]?).map Label.ctx = some (created σ s)) : HBS σ L lbls (.step p) (.step q) := by
  have hsq := step_after_create hs hsp hq hc
  have hsw : SWS σ L lbls (.step s) (.start s) := ⟨rfl, hsp⟩
  have hpo : PO σ lbls (.start s) (.step q) := ⟨hsq, hq, hsp, hc⟩
  have h2 : HBS σ L lbls (.step s) (.step q) := .tail (.single (Or.inr hsw)) (Or.inl hpo)
  rcases Nat.lt_or_ge p s with h | h
  · have hpo' : PO σ lbls (.step p) (.step s) := ⟨h, Nat.lt_trans hsq hq, hp⟩
    exact .trans (.single (Or.inl hpo')) h2
  · obtain rfl : p = s := Nat.le_antisymm hps h
    exact h2

/-- `join_orders` on the strict graph (brief, task 5; WC5.1 C47): on the `ok` steps of a trace
whose first state has no completed context, every step of a context `d` is strictly `hb`-before
every successful `join` of `d`. -/
theorem join_ordersS {k : K} {L' L : MutexLayout}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label}
    (hs : ∀ i (h : i < lbls.length), LStep k L' lbls[i] (σ i) (σ (i + 1)))
    (h0 : ∀ x ∈ (σ 0).1.C, x.life = .live) {q j d : Nat} (hq : q < lbls.length)
    (hcq : (lbls[q]?).map Label.ctx = some d) (hj : j < lbls.length)
    (hjd : (lbls[j]?).bind Label.joinOf = some d) : HBS σ L lbls (.step q) (.step j) := by
  have hdone : (σ j).1.lifes[d]? = some .done := by
    have hjd' := hjd
    rw [List.getElem?_eq_getElem hj, Option.bind_some] at hjd'
    have hstep := hs j hj
    generalize lbls[j] = lbl at hjd' hstep
    cases lbl <;> simp only [Label.joinOf, reduceCtorEq, Option.some.injEq] at hjd'
    subst hjd'
    exact lstep_join_done hstep
  obtain ⟨t, htj, htd⟩ := (done_iff hs h0 d j (Nat.le_of_lt hj)).1 hdone
  have htl : t < lbls.length := Nat.lt_trans htj hj
  have hqt : q ≤ t := by
    refine Nat.le_of_not_lt fun htq => ?_
    have hl := (lstep_lifes (hs q hq)).1
    have hcq' := hcq
    rw [List.getElem?_eq_getElem hq, Option.map_some] at hcq'
    rw [Option.some.inj hcq'] at hl
    have hd' := (done_iff hs h0 d q (Nat.le_of_lt hq)).2 ⟨t, htq, htd⟩
    rw [SC.live_iff.1 hl] at hd'; cases hd'
  have hsw : SWS σ L lbls (.step t) (.step j) := by
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

/-! ## The reference mutex (WC5.1 C48, C49) -/

/-- `lock_orders` on the strict graph, finer form (brief, task 5): for an entry `e`, an
`unlock(e)` at step `u` is strictly `hb`-before every successful `acquire(e)` at a step `a > u`, as
long as every intermediate `acquire(e)` is given back, before `a`, by an `unlock(e)` that it is
strictly `hb`-before, and `MutexGap` holds from every `unlock(e)` at a step `u' ≥ u` to the first
`acquire(e)` after it up to `a`. The statement reads the labels and the controllers only. -/
theorem lock_ordersS_gaps {σ : Nat → SC × SyncReg × ArenaReg} {L : MutexLayout}
    {lbls : List Label} {e a : Nat} (ha : a < lbls.length)
    (hacq : (lbls[a]?).bind Label.acquireOf = some e) :
    ∀ {u : Nat}, u < a → (lbls[u]?).bind Label.unlockOf = some e →
      (∀ u' p, u ≤ u' → u' < p → p ≤ a → (lbls[u']?).bind Label.unlockOf = some e →
        (lbls[p]?).bind Label.acquireOf = some e →
        (∀ q, u' < q → q < p → (lbls[q]?).bind Label.acquireOf ≠ some e) →
        MutexGap σ L lbls e u' p) →
      (∀ p, u < p → p < a → (lbls[p]?).bind Label.acquireOf = some e →
        ∃ p', p < p' ∧ p' < a ∧ (lbls[p']?).bind Label.unlockOf = some e ∧
          HBS σ L lbls (.step p) (.step p')) →
      HBS σ L lbls (.step u) (.step a)
  | u, hua, hu, hgap, hmid => by
    obtain ⟨p, -, hpa, hpp, hmin⟩ := find?_range_least (p := fun k =>
      decide (u < k) && decide ((lbls[k]?).bind Label.acquireOf = some e)) (n := a + 1)
      (a := a) (Nat.lt_succ_self _) (by rw [decide_eq_true hua, decide_eq_true hacq]; rfl)
    have hpp : (decide (u < p) && decide ((lbls[p]?).bind Label.acquireOf = some e)) = true := hpp
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hpp
    obtain ⟨hup, hpe⟩ := hpp
    have hfirst : ∀ q, u < q → q < p → (lbls[q]?).bind Label.acquireOf ≠ some e := by
      intro q huq hqp hqe
      have hm : (decide (u < q) && decide ((lbls[q]?).bind Label.acquireOf = some e)) = false :=
        hmin q hqp
      rw [decide_eq_true huq, decide_eq_true hqe] at hm
      cases hm
    have hsw : SWS σ L lbls (.step u) (.step p) := by
      refine ⟨hup, Nat.lt_of_le_of_lt hpa ha, Or.inr ?_⟩
      rw [hu]
      exact ⟨hpe, fun q hq huq => hfirst q huq (List.mem_range.1 hq),
        hgap u p (Nat.le_refl _) hup hpa hu hpe hfirst⟩
    rcases Nat.lt_or_ge p a with h | h
    · obtain ⟨p', hpp', hp'a, hp'u, hhb⟩ := hmid p hup h hpe
      have ih := lock_ordersS_gaps (σ := σ) (L := L) ha hacq hp'a hp'u
        (fun u'' q h1 h2 h3 h4 h5 h6 => hgap u'' q (by omega) h2 h3 h4 h5 h6)
        (fun k hk hka hke => hmid k (by omega) hka hke)
      exact .trans (.single (Or.inr hsw)) (.trans hhb ih)
    · obtain rfl : p = a := Nat.le_antisymm hpa h
      exact .single (Or.inr hsw)
  termination_by u => a - u

/-- `lock_orders` on the strict graph (brief, task 5; WC5.1 C48, C49): the statement of
`lock_orders`, with two more hypotheses on the interval from `u` to `a`: no `resetLock(e)` at a
step strictly between them, and the controller of `e` designating the same leaf in every state
from the issue of step `u` to the entry of step `a`. -/
theorem lock_ordersS {σ : Nat → SC × SyncReg × ArenaReg} {L : MutexLayout} {lbls : List Label}
    {e u a : Nat} (hua : u < a) (ha : a < lbls.length)
    (hu : (lbls[u]?).bind Label.unlockOf = some e)
    (hacq : (lbls[a]?).bind Label.acquireOf = some e)
    (hnr : ∀ p, u < p → p < a → (lbls[p]?).bind Label.resetLockOf ≠ some e)
    (hctl : ∃ ctl, ∀ k, u + 1 ≤ k → k ≤ a → ctlAt σ L e k = some ctl)
    (hmid : ∀ p, u < p → p < a → (lbls[p]?).bind Label.acquireOf = some e →
      ∃ p', p < p' ∧ p' < a ∧ (lbls[p']?).bind Label.unlockOf = some e ∧
        HBS σ L lbls (.step p) (.step p')) :
    HBS σ L lbls (.step u) (.step a) := by
  obtain ⟨ctl, hctl⟩ := hctl
  refine lock_ordersS_gaps ha hacq hua hu (fun u' p h1 h2 h3 _ _ _ => ?_) hmid
  refine ⟨fun q hq hu'q => hnr q (by omega) (by have := List.mem_range.1 hq; omega), ?_, ?_⟩
  · rw [hctl (u' + 1) (by omega) (by omega)]; exact fun h => by cases h
  · intro k hk hu'k
    have := List.mem_range.1 hk
    rw [hctl k (by omega) (by omega), hctl (u' + 1) (by omega) (by omega)]

end Ern.Concurrency
