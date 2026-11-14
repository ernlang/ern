import Ern.Concurrency.FullEncap.HandoffExtClass

/-!
# The abstract handoff frontier and the composition

Brief of milestone 4, slice 4, tasks 3 and 5 (`formal/reports/spec2-m4-handoff-ext.md`;
`corpus-spec2-m3.md` v15 §2 quaterdecies, "Faits attendus généraux"). On a `RunFull` from the
initial state, for every extended exclusive pair `(i, j, l)`:

* the frontier exists (`frontier_exists`) and every frontier satisfies `i ≤ r < j`
  (`frontier_lt`); the touch of `j` is of class D or E (task 2), and at the state before step `j`
  the capacity of the context of `i` is compatible with it: `other_cap_dying_run` for class D;
  `capacity_run`, `spawnVal_cap_pre` and `cap5_compat` for class E (`touchCompat_at_j`);
* a frontier `r > i` is a step of the context of `i` (`frontier_own`, by `cap5_drop_own`);
* every `ExclPair` is an extended exclusive pair, and its frontier is `lossStep`, with `i < r`
  (`exclPair_extPair`, `exclPair_frontier`).

Task 5: extended handoff order excludes an extended race, on `HB` and on `HBS`
(`handoffOrderedExt_no_race`, `handoffOrderedExtS_no_raceS`); every `Race` is an extended race
(`race_raceExt`, `raceS_raceExtS`). If `i < r`: `po(i, r)` then `hb(r, j)`; if `r = i`, `hb(r, j)`
is `hb(i, j)`; no order internal to a step is invoked.

Scope (brief, "Portée du résultat"): one event per abstract step; the extended order is the
abstract analogue of WC5.3 C46, not C46; the conclusion is conditional, not a proof of the absence
of races.
-/

set_option autoImplicit false

namespace Ern.Concurrency.FullEncap.HandoffExt

open Ern.MemoryModel Ern.MemoryModel.Access Ern.Concurrency Ern.Concurrency.MutexReal
open SyncPreserveAux SyncInitAux TransferPreserveAux PreservationAux

/-! ## Runs -/

/-- A prefix of a `RunFull` from the initial state is an `EncapsulatedTrace5C` from it. -/
theorem trace5C_run {k : K} {L : MutexLayout} {statics : Statics}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label}
    (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], [])) (h : RunFull k L σ lbls) {n : Nat}
    (hn : n ≤ lbls.length) :
    EncapsulatedTrace5C k L (SC.ofS3 (S3.init statics), [], []) (lbls.take n) (σ n) := by
  have htr5R := run5R_trace (run5R_take h n)
  have hlen : (lbls.take n).length = n := by simp; omega
  rw [hlen, h0] at htr5R
  exact encapsulatedTrace5R_imp htr5R

/-- Every `RunFull` is a `Run5C`: `handoffOrdered_no_raceS` applies to it with no further
hypothesis. -/
theorem runFull_run5C {k : K} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg}
    {lbls : List Label} (h : RunFull k L σ lbls) : Run5C k L σ lbls :=
  fun i hi => ⟨(h i hi).1.1.1.1, (h i hi).2⟩

/-! ## Compatibility at the second member -/

/-- `TouchCompat` is closed downwards in the rank of the capability. -/
theorem touchCompat_mono {k : K} {st st' : SC × SyncReg × ArenaReg} {lbl : Label} {l : Nat}
    {o o' : Option Mode} (h : TouchCompat k st st' lbl l o') (hr : capRank o ≤ capRank o') :
    TouchCompat k st st' lbl l o := by
  rcases h with ⟨hD, rfl⟩ | ⟨hE, ho, hm⟩
  · refine .inl ⟨hD, ?_⟩
    rcases o with _ | _ | _
    · rfl
    all_goals exact absurd hr (by decide)
  · refine .inr ⟨hE, fun h' => ?_, fun h' => ?_⟩
    · exact (capCompat_iff _ _).2 (Nat.lt_of_le_of_lt hr ((capCompat_iff _ _).1 (ho h')))
    · exact (capCompat_iff _ _).2 (Nat.lt_of_le_of_lt hr ((capCompat_iff _ _).1 (hm h')))

/-- On a `RunFull` from the initial state, in the state before the second member of an extended
exclusive pair, the capacity of the context of the first member is compatible with the touch of
the second: none on a leaf of class D (`other_cap_dying_run`); compatible with the required mode
on a leaf of class E (`capacity_run`, `spawnVal_cap_pre`, `cap5_compat`, WC5.3 C43). -/
theorem touchCompat_at_j {k : K} {L : MutexLayout} {statics : Statics}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} (hdd : DDSound k)
    (hstat : StaticsOK statics) (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], []))
    (h : RunFull k L σ lbls) {i j l : Nat} (hp : ExtPair k L σ lbls i j l) :
    ∃ (hij : i < j) (hj : j < lbls.length), TouchCompat k (σ j) (σ (j + 1)) lbls[j] l
      (cap5 (σ j).1 (σ j).2.1 (lbls[i]'(Nat.lt_trans hij hj)).ctx l) := by
  obtain ⟨_, hDE⟩ := extPair_second_classDE hdd hstat h0 h hp
  obtain ⟨hij, hj, hcc, -, htj, -⟩ := hp.out
  refine ⟨hij, hj, ?_⟩
  have htr := encapsulatedTrace5C_imp (trace5C_run h0 h (Nat.le_of_lt hj))
  rcases hDE with hD | hE
  · exact .inl ⟨hD, classD_other_run hdd hstat h0 h hj hcc hD⟩
  · refine .inr ⟨hE, fun hm => ?_, fun hm => ?_⟩
    · have hcap := classEm_cap_run hdd hstat h0 h hj htj ⟨hE, hm⟩
      cases hc : cap5 (σ j).1 (σ j).2.1 (lbls[i]'(Nat.lt_trans hij hj)).ctx l with
      | none => rfl
      | some md =>
        cases md with
        | observe => rfl
        | modify =>
          rw [cap5_compat hdd hstat htr hcc hc] at hcap
          exact hcap.elim
    · have hcap := classEm_cap_run hdd hstat h0 h hj htj ⟨hE, hm⟩
      rw [cap5_compat hdd hstat htr (Ne.symm hcc) (Ern.Concurrency.allows_modify hcap)]
      rfl

/-- `FrontAt` read on existing steps. -/
theorem frontAt_iff {k : K} {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label}
    {i j l : Nat} (hi : i < lbls.length) (hj : j < lbls.length) (q : Nat) :
    FrontAt k σ lbls i j l q ↔ TouchCompat k (σ j) (σ (j + 1)) lbls[j] l
      (cap5 (σ (q + 1)).1 (σ (q + 1)).2.1 lbls[i].ctx l) := by
  unfold FrontAt
  rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj]
  exact Iff.rfl

/-! ## Existence and bounds -/

/-- Brief, task 3, bounds: on a `RunFull` from the initial state, every frontier of an extended
exclusive pair lies before its second member: the step before `j` is already a candidate
(`touchCompat_at_j`); `i ≤ r` is in the definition. -/
theorem frontier_lt {k : K} {L : MutexLayout} {statics : Statics}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} (hdd : DDSound k)
    (hstat : StaticsOK statics) (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], []))
    (h : RunFull k L σ lbls) {i j l r : Nat} (hp : ExtPair k L σ lbls i j l)
    (hr : IsFrontier k σ lbls i j l r) : i ≤ r ∧ r < j := by
  obtain ⟨hij, hj, htc⟩ := touchCompat_at_j hdd hstat h0 h hp
  refine ⟨hr.1, Nat.lt_of_not_le fun hjr => ?_⟩
  apply hr.2.2.2 (j - 1) (List.mem_range.2 (by omega)) (by omega)
  rw [frontAt_iff (Nat.lt_trans hij hj) hj, show j - 1 + 1 = j by omega]
  exact htc

/-- Brief, task 3, existence: on a `RunFull` from the initial state, every extended exclusive pair
has a frontier, with `i ≤ r < j`. The search for the first step is constructive when
`K.SharedMutable` is decidable, which the required mode of the provider of `alloc` reads (§71.2,
`ReqMode`); without it the first step would need `Classical.choice`. -/
theorem frontier_exists {k : K} [DecidablePred k.SharedMutable] {L : MutexLayout}
    {statics : Statics} {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label}
    (hdd : DDSound k) (hstat : StaticsOK statics)
    (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], [])) (h : RunFull k L σ lbls) {i j l : Nat}
    (hp : ExtPair k L σ lbls i j l) : ∃ r, IsFrontier k σ lbls i j l r ∧ i ≤ r ∧ r < j := by
  obtain ⟨hij, hj, htc⟩ := touchCompat_at_j hdd hstat h0 h hp
  have hpj : (decide (i ≤ j - 1) && decide (FrontAt k σ lbls i j l (j - 1))) = true := by
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    refine ⟨by omega, (frontAt_iff (Nat.lt_trans hij hj) hj _).2 ?_⟩
    rw [show j - 1 + 1 = j by omega]
    exact htc
  obtain ⟨r, -, hrj, hpr, hmin⟩ := find?_range_least
    (p := fun q => decide (i ≤ q) && decide (FrontAt k σ lbls i j l q)) (n := lbls.length)
    (a := j - 1) (by omega) hpj
  have hpr : (decide (i ≤ r) && decide (FrontAt k σ lbls i j l r)) = true := hpr
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hpr
  refine ⟨r, ⟨hpr.1, by omega, hpr.2, fun q hq hiq hf => ?_⟩, hpr.1, by omega⟩
  have hm : (decide (i ≤ q) && decide (FrontAt k σ lbls i j l q)) = false :=
    hmin q (List.mem_range.1 hq)
  rw [decide_eq_true hiq, decide_eq_true hf] at hm
  cases hm

/-! ## Own context -/

/-- Brief, task 3, own context: on a `RunFull` from the initial state, a frontier `r > i` is a step
of the context of `i`: before step `r` the capacity is incompatible, after it compatible, so it
drops strictly at step `r`, which L1 attributes to the context itself (`cap5_drop_own`, WC5.3
C45). Compatibility being closed downwards (`touchCompat_mono`), no particular kind is
singled out. -/
theorem frontier_own {k : K} {L : MutexLayout} {statics : Statics}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} (hdd : DDSound k)
    (hstat : StaticsOK statics) (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], []))
    (h : RunFull k L σ lbls) {i j l r : Nat} (hr : IsFrontier k σ lbls i j l r) (hir : i < r) :
    (lbls[r]?).map Label.ctx = (lbls[i]?).map Label.ctx := by
  obtain ⟨-, hrl, hfr, hmin⟩ := hr
  have hil : i < lbls.length := by omega
  have hprev := hmin (r - 1) (List.mem_range.2 (by omega)) (by omega)
  unfold FrontAt at hfr hprev
  rw [List.getElem?_eq_getElem hil] at hfr hprev
  cases hjj : lbls[j]? with
  | none => rw [hjj] at hfr; exact hfr.elim
  | some lj =>
    rw [hjj] at hfr hprev
    have hprev' : ¬ TouchCompat k (σ j) (σ (j + 1)) lj l
        (cap5 (σ r).1 (σ r).2.1 lbls[i].ctx l) := by
      have e : r - 1 + 1 = r := by omega
      rw [e] at hprev; exact hprev
    have hdrop : capRank (cap5 (σ (r + 1)).1 (σ (r + 1)).2.1 lbls[i].ctx l) <
        capRank (cap5 (σ r).1 (σ r).2.1 lbls[i].ctx l) :=
      Nat.lt_of_not_le fun hle => hprev' (touchCompat_mono hfr hle)
    have htr := encapsulatedTrace5C_imp (trace5C_run h0 h (Nat.le_of_lt hrl))
    have he5C := (h r hrl).1.1.1.1
    have he5 : Encap5 L ((σ r).1, (σ r).2.1) lbls[r] :=
      ⟨he5C.1, chainExcl_guardedExcl he5C.2.1, he5C.2.2⟩
    have hctx := cap5_drop_own hdd statics (lbls.take r) (σ r) (σ (r + 1)) lbls[r] lbls[i].ctx l
      hstat htr he5 (h r hrl).2 hdrop
    rw [List.getElem?_eq_getElem hrl, List.getElem?_eq_getElem hil, Option.map_some,
      Option.map_some, hctx]

/-! ## Coincidence with the pairs of direct accesses -/

/-- The final footprint of an access contains its leaves (`Label.Access`, `TouchesF`). -/
theorem access_touchesF {L : MutexLayout} {st : SC × SyncReg × ArenaReg} {lbl : Label}
    {c l : Nat} {m : Mode} (h : lbl.Access c l m) : TouchesF L st lbl l := by
  cases lbl with
  | kernel c' op =>
    cases op <;> simp only [Label.Access] at h
    all_goals exact h.2.1
  | _ => exact (h : False).elim

/-- The required mode of an access is its mode (Spec 1 §66.2, §67.1, §68.2). -/
theorem access_reqMode {k : K} {st : SC × SyncReg × ArenaReg} {lbl : Label} {c l : Nat}
    {m : Mode} (h : lbl.Access c l m) : ReqMode k st lbl l m ∧ HasReq st lbl l := by
  cases lbl with
  | kernel c' op =>
    cases op <;> simp only [Label.Access] at h
    all_goals exact ⟨h.2.2, trivial⟩
  | _ => exact (h : False).elim

/-- An access step kills no leaf (`killKind`, `usable_run`). -/
theorem access_killKind {lbl : Label} {c l : Nat} {m : Mode} (h : lbl.Access c l m) :
    Sweep.killKind lbl = false := by
  cases lbl with
  | kernel c' op => cases op <;> first | rfl | exact (h : False).elim
  | _ => exact (h : False).elim

/-- On a `RunFull` from the initial state, an access step touches an existing leaf of class E, with
its mode as required mode; its context has that capacity (`access_cap5`). -/
theorem access_classEm_run {k : K} {L : MutexLayout} {statics : Statics}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} (hdd : DDSound k)
    (hstat : StaticsOK statics) (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], []))
    (h : RunFull k L σ lbls) {n : Nat} (hn : n < lbls.length) {c l : Nat} {m : Mode}
    (ha : lbls[n].Access c l m) :
    TouchL L (σ n) (σ (n + 1)) lbls[n] l ∧ ClassEm k (σ n) (σ (n + 1)) lbls[n] l m ∧
      Allows (cap5 (σ n).1 (σ n).2.1 c l) m := by
  have hcap := access_cap5 hdd hstat (trace5C_run h0 h (Nat.le_of_lt hn)) ha (h n hn).1.1.1.1
    (h n hn).2
  obtain ⟨x, -, -, hex⟩ := cap5_attained hcap
  obtain ⟨z, hz, -, hlz, -⟩ := eff_present (ne_none_of_allows hex)
  have hw : WF3 (σ n).1.flat := (runFull_inv hdd hstat h0 h (Nat.le_of_lt hn)).1.1.1.2
  obtain ⟨hlt, hleaf⟩ := hw.footprints x z hz l hlz
  obtain ⟨hrm, hhr⟩ := access_reqMode (k := k) (st := σ n) ha
  refine ⟨.inl ⟨hlt, hleaf, access_touchesF ha⟩, ⟨⟨hlt, hleaf, fun hD => ?_, hhr⟩, hrm⟩, hcap⟩
  exact hD.2.2 (usable_run hdd hstat h0 h hn (access_killKind ha) hD.2.1)

/-- Brief, task 3, coincidence: on a `RunFull` from the initial state, every `ExclPair` is an
extended exclusive pair. -/
theorem exclPair_extPair {k : K} {L : MutexLayout} {statics : Statics}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} (hdd : DDSound k)
    (hstat : StaticsOK statics) (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], []))
    (h : RunFull k L σ lbls) {i j l : Nat} (hp : ExclPair lbls i j l) :
    ExtPair k L σ lbls i j l := by
  obtain ⟨hij, hj, c, c', m, m', hcc, hai, haj, hmod⟩ := hp
  have hil := Nat.lt_trans hij hj
  obtain ⟨hti, hEi, -⟩ := access_classEm_run hdd hstat h0 h hil hai
  obtain ⟨htj, hEj, -⟩ := access_classEm_run hdd hstat h0 h hj haj
  refine ⟨hij, ?_⟩
  rw [List.getElem?_eq_getElem hil, List.getElem?_eq_getElem hj]
  refine ⟨?_, hti, htj, ?_⟩
  · rw [(access_ctx_mode hai).1, (access_ctx_mode haj).1]; exact Ne.symm hcc
  · rcases hmod with rfl | rfl
    · exact .inl ⟨hti, .inr (.inr hEi)⟩
    · exact .inr ⟨htj, .inr (.inr hEj)⟩

/-- Brief, task 3, coincidence: on a `RunFull` from the initial state, the frontier of an
`ExclPair` is its loss step (`lossStep`), and `i < r`. At `k = i` the capacity of the context of
`i` is still incompatible: an access keeps every `cap5` (`inert_effect`, `cap5_same`); beyond, the
two searches test the same compatibility (`touchCompat_iff_of_classEm`). -/
theorem exclPair_frontier {k : K} {L : MutexLayout} {statics : Statics}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} (hdd : DDSound k)
    (hstat : StaticsOK statics) (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], []))
    (h : RunFull k L σ lbls) {i j l : Nat} (hp : ExclPair lbls i j l) :
    ∃ r, lossStep σ lbls i j l = some r ∧ IsFrontier k σ lbls i j l r ∧ i < r := by
  obtain ⟨r, hls, hir, hrj, -⟩ := lossStep_own hdd hstat h0 (runFull_run5C h) hp
  obtain ⟨hij, hj, c, c', m, m', hcc, hai, haj, hmod⟩ := hp
  have hil := Nat.lt_trans hij hj
  obtain ⟨-, hEj, -⟩ := access_classEm_run (k := k) hdd hstat h0 h hj haj
  obtain ⟨-, -, hcap⟩ := access_classEm_run (k := k) hdd hstat h0 h hil hai
  obtain ⟨hci, -⟩ := access_ctx_mode hai
  obtain ⟨-, hmj⟩ := access_ctx_mode haj
  have hls' : lossStep σ lbls i j l = (List.range lbls.length).find? fun q =>
      decide (i < q) && CapCompat (cap5 (σ (q + 1)).1 (σ (q + 1)).2.1 c' l) m' := by
    unfold lossStep
    rw [List.getElem?_eq_getElem hil, List.getElem?_eq_getElem hj, Option.map_some,
      Option.bind_some, hci, hmj]
  rw [hls'] at hls
  obtain ⟨hrl, hpr, hmin⟩ := find?_range_some hls
  have hfa : ∀ q, FrontAt k σ lbls i j l q ↔
      CapCompat (cap5 (σ (q + 1)).1 (σ (q + 1)).2.1 c' l) m' = true := fun q => by
    rw [frontAt_iff hil hj, hci]; exact touchCompat_iff_of_classEm hEj _
  -- at `i`, the capacity of `c'` is still incompatible
  have hinert : Label.Inert lbls[i] := by
    revert hai; cases lbls[i] with
    | kernel _ op => cases op <;> simp [Label.Access, Label.Inert]
    | _ => simp [Label.Access]
  have hw : WF3 (σ i).1.flat := (runFull_inv hdd hstat h0 h (Nat.le_of_lt hil)).1.1.1.2
  obtain ⟨hA, hP, hC, hreg⟩ := inert_effect hinert (h i hil).2
  have hfi := cap5_same hw hA hP hC hreg c' l
  have hneed : needRank m' ≤ capRank (cap5 (σ i).1 (σ i).2.1 c' l) := by
    cases m' with
    | modify =>
      cases hc : cap5 (σ i).1 (σ i).2.1 c' l with
      | none => rw [hc] at hcap; exact hcap.elim
      | some md => cases md <;> decide
    | observe =>
      have hm : m = .modify := by rcases hmod with h | h; exact h; cases h
      subst hm
      rw [Ern.Concurrency.allows_modify hcap]; decide
  have hi0 : ¬ FrontAt k σ lbls i j l i := fun hf => by
    have := (capCompat_iff _ _).1 ((hfa i).1 hf)
    omega
  have hpr' : (decide (i < r) && CapCompat (cap5 (σ (r + 1)).1 (σ (r + 1)).2.1 c' l) m') =
      true := hpr
  rw [Bool.and_eq_true] at hpr'
  refine ⟨r, hls'.symm ▸ hls, ⟨Nat.le_of_lt hir, hrl, (hfa r).2 hpr'.2, fun q hq hiq hf => ?_⟩,
    hir⟩
  rcases Nat.eq_or_lt_of_le hiq with rfl | hlt
  · exact hi0 hf
  · have hm : (decide (i < q) && CapCompat (cap5 (σ (q + 1)).1 (σ (q + 1)).2.1 c' l) m') =
        false := hmin q (List.mem_range.1 hq)
    rw [decide_eq_true hlt, (hfa q).1 hf] at hm
    cases hm

/-! ## Composition (task 5) -/

/-- Brief, task 5, composition: on a `RunFull` from the initial state, extended handoff order
excludes an extended race. If `i < r`: `po(i, r)` (`frontier_own`), then `hb(r, j)`; if `r = i`,
`hb(r, j)` is `hb(i, j)`. No order internal to a step is invoked. This is the abstract analogue of
WC5.3 C46, a conditional composition, not a proof of the absence of races. -/
theorem handoffOrderedExt_no_race {k : K} {L : MutexLayout} {statics : Statics}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} (hdd : DDSound k)
    (hstat : StaticsOK statics) (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], []))
    (h : RunFull k L σ lbls) (ho : HandoffOrderedExt k L σ lbls) : ¬ RaceExt k L σ lbls := by
  rintro ⟨i, j, l, hp, hnb⟩
  obtain ⟨r, -, hfr, hb⟩ := ho i j l hp
  rcases Nat.eq_or_lt_of_le hfr.1 with rfl | hir
  · exact hnb hb
  · have hpo : PO σ lbls (.step i) (.step r) :=
      ⟨hir, hfr.2.1, (frontier_own hdd hstat h0 h hfr hir).symm⟩
    exact hnb (.trans (.single (Or.inl hpo)) hb)

/-- Brief, task 5, composition on the strict graph (`HBS`). -/
theorem handoffOrderedExtS_no_raceS {k : K} {L : MutexLayout} {statics : Statics}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} (hdd : DDSound k)
    (hstat : StaticsOK statics) (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], []))
    (h : RunFull k L σ lbls) (ho : HandoffOrderedExtS k L σ lbls) : ¬ RaceExtS k L σ lbls := by
  rintro ⟨i, j, l, hp, hnb⟩
  obtain ⟨r, -, hfr, hb⟩ := ho i j l hp
  rcases Nat.eq_or_lt_of_le hfr.1 with rfl | hir
  · exact hnb hb
  · have hpo : PO σ lbls (.step i) (.step r) :=
      ⟨hir, hfr.2.1, (frontier_own hdd hstat h0 h hfr hir).symm⟩
    exact hnb (.trans (.single (Or.inl hpo)) hb)

/-- Brief, task 5, inclusion: on a `RunFull` from the initial state, every `Race` is an extended
race. -/
theorem race_raceExt {k : K} {L : MutexLayout} {statics : Statics}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} (hdd : DDSound k)
    (hstat : StaticsOK statics) (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], []))
    (h : RunFull k L σ lbls) (hr : Race σ lbls) : RaceExt k L σ lbls := by
  obtain ⟨i, j, l, hp, hnb⟩ := hr
  exact ⟨i, j, l, exclPair_extPair hdd hstat h0 h hp, hnb⟩

/-- Brief, task 5, inclusion on the strict graph. -/
theorem raceS_raceExtS {k : K} {L : MutexLayout} {statics : Statics}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} (hdd : DDSound k)
    (hstat : StaticsOK statics) (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], []))
    (h : RunFull k L σ lbls) (hr : RaceS σ L lbls) : RaceExtS k L σ lbls := by
  obtain ⟨i, j, l, hp, hnb⟩ := hr
  exact ⟨i, j, l, exclPair_extPair hdd hstat h0 h hp, hnb⟩

/-- The old composition applies to every `RunFull` from the initial state, with no further
hypothesis (`runFull_run5C`). -/
theorem handoffOrdered_no_raceS_full {k : K} {L : MutexLayout} {statics : Statics}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} (hdd : DDSound k)
    (hstat : StaticsOK statics) (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], []))
    (h : RunFull k L σ lbls) (ho : HandoffOrderedS σ L lbls) : ¬ RaceS σ L lbls :=
  handoffOrdered_no_raceS hdd hstat h0 (runFull_run5C h) ho

end Ern.Concurrency.FullEncap.HandoffExt
