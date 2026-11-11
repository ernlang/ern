import Ern.Concurrency.Events

/-!
# Composition theorem for ordinary leaves

Brief of milestone 4, event pass, task 4 (`formal/reports/spec2-m4-events.md`): the line "ordinary
non-`SharedMutable` leaves" of WC5.1 C52 as a composition theorem on the event graph of
`Ern.Concurrency.Events`. `lossStep_own` places the loss step of WC5.1 C45 strictly between the two
accesses of an exclusive pair, in the context of the earlier one; `handoffOrdered_no_race` composes
it with `HandoffOrdered` (WC5.1 C46). Hypotheses: those of `handoff_loss_exists_C`.
-/

namespace Ern.Concurrency

open Ern.MemoryModel.Access

/-! ## Least elements of `List.range` -/

/-- When `List.find?` over `List.range n` finds nothing, the predicate is false below `n`. -/
theorem find?_range_none {p : Nat → Bool} {n : Nat} (h : (List.range n).find? p = none) :
    ∀ k, k < n → p k = false := fun k hk => by
  have := List.find?_eq_none.1 h k (List.mem_range.2 hk)
  cases hp : p k
  · rfl
  · exact absurd hp this

/-- What `List.find?` over `List.range n` finds is below `n`, satisfies the predicate, and is
the least such number. -/
theorem find?_range_some {p : Nat → Bool} :
    ∀ {n r : Nat}, (List.range n).find? p = some r →
      r < n ∧ p r = true ∧ ∀ k, k < r → p k = false
  | 0, _, h => by cases h
  | n + 1, r, h => by
    rw [List.range_succ, List.find?_append] at h
    cases hn : (List.range n).find? p with
    | some r' =>
      rw [hn, Option.some_or] at h
      cases h
      obtain ⟨h1, h2, h3⟩ := find?_range_some hn
      exact ⟨Nat.lt_succ_of_lt h1, h2, h3⟩
    | none =>
      rw [hn, Option.none_or, List.find?_cons] at h
      cases hp : p n
      · rw [hp] at h; cases h
      · rw [hp] at h
        cases h
        exact ⟨Nat.lt_succ_self _, hp, find?_range_none hn⟩

/-- The least `r < n` with `p r` exists and is at most `a` when `p a` holds. -/
theorem find?_range_least {p : Nat → Bool} {n a : Nat} (ha : a < n) (hp : p a = true) :
    ∃ r, (List.range n).find? p = some r ∧ r ≤ a ∧ p r = true ∧ ∀ k, k < r → p k = false := by
  cases h : (List.range n).find? p with
  | none => rw [find?_range_none h a ha] at hp; cases hp
  | some r =>
    obtain ⟨-, h2, h3⟩ := find?_range_some h
    refine ⟨r, rfl, Nat.le_of_not_lt fun har => ?_, h2, h3⟩
    rw [h3 a har] at hp; cases hp

/-! ## Ranks -/

/-- Least rank of an incompatible capability (`CapCompat`): `1` against `Modify`, `2` against
`Observe`. -/
def needRank : Mode → Nat
  | .modify => 1
  | .observe => 2

/-- `CapCompat` by ranks: compatible when the rank is below `needRank`. -/
theorem capCompat_iff (o : Option Mode) (m : Mode) :
    CapCompat o m = true ↔ capRank o < needRank m := by
  rcases o with _ | _ | _ <;> cases m <;> decide

/-- `CapCompat` by ranks: incompatible when the rank reaches `needRank`. -/
theorem capCompat_false_iff (o : Option Mode) (m : Mode) :
    CapCompat o m = false ↔ needRank m ≤ capRank o := by
  rcases o with _ | _ | _ <;> cases m <;> decide

/-- An access step gives its context and mode (`Label.Access`, `Label.accMode`). -/
theorem access_ctx_mode {lbl : Label} {d l : Nat} {m : Mode} (h : lbl.Access d l m) :
    lbl.ctx = d ∧ lbl.accMode = some m := by
  cases lbl with
  | kernel c op =>
    cases op <;> simp only [Label.Access] at h
    all_goals obtain ⟨rfl, -, rfl⟩ := h; exact ⟨rfl, rfl⟩
  | _ => simp only [Label.Access] at h

/-! ## The loss step -/

/-- `lossStep_own` (brief, task 4; WC5.1 C45; C52, ordinary leaves): under `DDSound` (Spec 1
§80), on a `Run5C` from an initial state (Spec 1 §47), the loss step `r(i, j, l)` of every
exclusive pair exists, satisfies `i < r < j` and is a step of the context of step `i`. From
`cap5_sound_C` (through `access_cap5`) at both accesses, the invariance of `cap5` under an access
step (`inert_effect`, `cap5_same`), `cap5_compat` at step `j`, and `cap5_drop_own` at the loss
step, where `cap5` crosses the compatibility threshold. -/
theorem lossStep_own {k : K} {L : MutexLayout} (hdd : DDSound k) {statics : Statics}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} (hst : StaticsOK statics)
    (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], [])) (hr : Run5C k L σ lbls) {i j l : Nat}
    (hp : ExclPair lbls i j l) :
    ∃ r, lossStep σ lbls i j l = some r ∧ i < r ∧ r < j ∧
      (lbls[r]?).map Label.ctx = (lbls[i]?).map Label.ctx := by
  obtain ⟨hij, hj, c, c', m, m', hcc, hai, haj, hmod⟩ := hp
  have hil : i < lbls.length := Nat.lt_trans hij hj
  have htr : ∀ n, n ≤ lbls.length → ∃ ls,
      EncapsulatedTrace5C k L (SC.ofS3 (S3.init statics), [], []) ls (σ n) := fun n hn => by
    rw [← h0]; exact run5C_prefix hr n hn
  let f : Nat → Nat := fun n => capRank (cap5 (σ n).1 (σ n).2.1 c' l)
  -- the lookup of `lossStep`
  obtain ⟨hci, -⟩ := access_ctx_mode hai
  obtain ⟨-, hmj⟩ := access_ctx_mode haj
  have hls : lossStep σ lbls i j l = (List.range lbls.length).find? fun k =>
      decide (i < k) && CapCompat (cap5 (σ (k + 1)).1 (σ (k + 1)).2.1 c' l) m' := by
    unfold lossStep
    rw [List.getElem?_eq_getElem hil, List.getElem?_eq_getElem hj, Option.map_some,
      Option.bind_some, hci, hmj]
  -- the earlier access: `cap5` of `c'` is incompatible after it
  obtain ⟨lsi, htri⟩ := htr i (Nat.le_of_lt hil)
  obtain ⟨hei, hsi⟩ := hr i hil
  have hcap := access_cap5 hdd hst htri hai hei hsi
  have hwi := (trace5_kInvCA hdd hst (encapsulatedTrace5C_imp htri)).parts.2.1
  have hinert : Label.Inert lbls[i] := by
    revert hai; cases lbls[i] with
    | kernel _ op => cases op <;> simp [Label.Access, Label.Inert]
    | _ => simp [Label.Access]
  obtain ⟨hA, hP, hC, hreg⟩ := inert_effect hinert hsi
  have hfi : f i ≤ f (i + 1) := cap5_same hwi hA hP hC hreg c' l
  have hneed : needRank m' ≤ f i := by
    show needRank m' ≤ capRank (cap5 (σ i).1 (σ i).2.1 c' l)
    cases m' with
    | modify =>
      cases hc : cap5 (σ i).1 (σ i).2.1 c' l with
      | none => rw [hc] at hcap; exact hcap.elim
      | some md => cases md <;> decide
    | observe =>
      have hm : m = .modify := by rcases hmod with h | h; exact h; cases h
      subst hm
      rw [allows_modify hcap]; decide
  have hinc : ∀ n, needRank m' ≤ f n →
      CapCompat (cap5 (σ n).1 (σ n).2.1 c' l) m' = false :=
    fun n h => (capCompat_false_iff _ _).2 h
  -- the later access: `cap5` of `c'` is compatible before it
  obtain ⟨lsj, htrj⟩ := htr j (Nat.le_of_lt hj)
  obtain ⟨hej, hsj⟩ := hr j hj
  have hcj := access_cap5 hdd hst htrj haj hej hsj
  have hcompat := fun {x y : Nat} (hxy : x ≠ y) =>
    cap5_compat (l := l) hdd hst (encapsulatedTrace5C_imp htrj) hxy
  have hfj : CapCompat (cap5 (σ j).1 (σ j).2.1 c' l) m' = true := by
    cases m' with
    | modify => rw [hcompat hcc (allows_modify hcj)]; rfl
    | observe =>
      cases hc' : cap5 (σ j).1 (σ j).2.1 c' l with
      | none => rfl
      | some md =>
        cases md with
        | observe => rfl
        | modify =>
          have := hcompat (Ne.symm hcc) hc'
          rw [this] at hcj; exact hcj.elim
  -- `j - 1` is a candidate
  have hj1 : i < j - 1 := by
    refine Nat.lt_of_le_of_ne (by omega) fun he => ?_
    have h1 := hinc (i + 1) (Nat.le_trans hneed hfi)
    rw [show i + 1 = j by omega, hfj] at h1
    cases h1
  have hpj : (decide (i < j - 1) && CapCompat (cap5 (σ (j - 1 + 1)).1 (σ (j - 1 + 1)).2.1 c' l)
      m') = true := by
    rw [show j - 1 + 1 = j by omega, hfj, decide_eq_true hj1]; rfl
  obtain ⟨r, hfind, hrj, hpr, hmin⟩ := find?_range_least (p := fun k =>
    decide (i < k) && CapCompat (cap5 (σ (k + 1)).1 (σ (k + 1)).2.1 c' l) m') (n := lbls.length)
    (a := j - 1) (by omega) hpj
  have hpr : (decide (i < r) && CapCompat (cap5 (σ (r + 1)).1 (σ (r + 1)).2.1 c' l) m') = true :=
    hpr
  rw [Bool.and_eq_true, decide_eq_true_eq] at hpr
  obtain ⟨hir, hcr⟩ := hpr
  -- `cap5` of `c'` is incompatible just before step `r`
  have hbefore : needRank m' ≤ f r := by
    rcases Nat.lt_or_ge (i + 1) r with h | h
    · have hm : (decide (i < r - 1) &&
          CapCompat (cap5 (σ (r - 1 + 1)).1 (σ (r - 1 + 1)).2.1 c' l) m') = false :=
        hmin (r - 1) (by omega)
      rw [show r - 1 + 1 = r by omega, decide_eq_true (by omega : i < r - 1), Bool.true_and]
        at hm
      exact (capCompat_false_iff _ _).1 hm
    · rw [show r = i + 1 by omega]; exact Nat.le_trans hneed hfi
  have hdrop : f (r + 1) < f r :=
    Nat.lt_of_lt_of_le ((capCompat_iff _ _).1 hcr) hbefore
  -- the loss step is a step of `c'`
  have hrl : r < lbls.length := by omega
  obtain ⟨lsr, htrr⟩ := htr r (Nat.le_of_lt hrl)
  obtain ⟨her, hsr⟩ := hr r hrl
  have hctx := cap5_drop_own hdd statics lsr (σ r) (σ (r + 1)) lbls[r] c' l hst
    (encapsulatedTrace5C_imp htrr) ⟨her.1, chainExcl_guardedExcl her.2.1, her.2.2⟩ hsr hdrop
  refine ⟨r, hls.trans hfind, hir, by omega, ?_⟩
  rw [List.getElem?_eq_getElem hrl, List.getElem?_eq_getElem hil, Option.map_some,
    Option.map_some, hctx, hci]

/-! ## Composition -/

/-- `handoffOrdered_no_race` (brief, task 4; WC5.1 C52, ordinary leaves; C46 composition
argument): under the hypotheses of `handoff_loss_exists_C`, `HandoffOrdered` excludes `Race`. The
loss step follows the earlier access in `po` (`lossStep_own`), and `HandoffOrdered` puts it
`hb`-before the later one. -/
theorem handoffOrdered_no_race {k : K} {L : MutexLayout} (hdd : DDSound k) {statics : Statics}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} (hst : StaticsOK statics)
    (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], [])) (hr : Run5C k L σ lbls)
    (ho : HandoffOrdered σ lbls) : ¬ Race σ lbls := by
  rintro ⟨i, j, l, hp, hnb⟩
  obtain ⟨r, hls, hb⟩ := ho i j l hp
  obtain ⟨r', hls', hir, hrj, hctx⟩ := lossStep_own hdd hst h0 hr hp
  rw [hls] at hls'
  cases hls'
  obtain ⟨-, hj, -⟩ := hp
  have hpo : PO σ lbls (.step i) (.step r) := ⟨hir, Nat.lt_trans hrj hj, hctx.symm⟩
  exact hnb (.trans (.single (Or.inl hpo)) hb)

end Ern.Concurrency
