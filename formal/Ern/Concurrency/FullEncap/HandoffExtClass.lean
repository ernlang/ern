import Ern.Concurrency.FullEncap.HandoffExt

/-!
# Classes of a touch

Brief of milestone 4, slice 4, task 2 (`formal/reports/spec2-m4-handoff-ext.md`; `corpus-spec2-m3.md`
v15 §2 quaterdecies, "Faits attendus généraux"). On a `RunFull` from the initial state:

* partition: the classes D, C, E, N are disjoint and cover every touch (`classes_disjoint`,
  `classes_cover`);
* class N is not empty: a touched leaf of class N is a leaf created and not written by the step
  (`classN_created`); `enterFrame`, `spawn`, `alloc` and the by-value `spawn` create such leaves;
* class C: only a by-value `spawn` creates and writes a leaf (`cw_spawnVal`); the other creations
  leave their leaves `Uninit` (`created_uninit`, Spec 1 §71 effect, §72 effect; WC5.3 C4);
* dead leaves: a step touching an existing leaf requires it to be usable before the step
  (`touch_usable_run`); a place that is no longer usable never becomes usable again
  (`unusable_run`), the counterpart of `usable_run`;
* identities: a place created by a step did not exist in any earlier state (`created_fresh_run`);
* corollaries: no extended exclusive pair has as first member a step in which `l` dies
  (`extPair_first_not_dying`), nor as second member a step that creates `l`
  (`extPair_second_not_created`);
* each class is tied to the lemma that stands for its capacity: E to `capacity_run` and
  `spawnVal_cap_pre` (`classEm_cap_run`), D to `other_cap_dying_run` (`classD_other_run`).
-/

set_option autoImplicit false

namespace Ern.Concurrency.FullEncap.HandoffExt

open Ern.MemoryModel Ern.MemoryModel.Access Ern.Concurrency Ern.Concurrency.MutexReal
open SyncPreserveAux SyncInitAux TransferPreserveAux PreservationAux

/-! ## Partition -/

/-- A dying leaf exists before the step (Spec 1 §40: a usable place exists). -/
theorem dying_lt {s s' : SC} {l : Nat} (h : Dying s s' l) : l < s.P.length := h.2.1.lt

/-- Brief, task 2, partition: the four classes are disjoint. Class E excludes D by its definition
(order of priority); C excludes D and E, a created leaf not existing before the step. -/
theorem classes_disjoint {k : K} {L : MutexLayout} {st st' : SC × SyncReg × ArenaReg}
    {lbl : Label} {l : Nat} :
    (ClassD st st' l → ¬ ClassC st st' l) ∧ (ClassD st st' l → ¬ ClassE st st' lbl l) ∧
    (ClassC st st' l → ¬ ClassE st st' lbl l) ∧
    (ClassN L st st' lbl l → ¬ ClassD st st' l ∧ ¬ ClassC st st' l ∧ ¬ ClassE st st' lbl l) ∧
    (∀ m, ClassEm k st st' lbl l m → ClassE st st' lbl l) :=
  ⟨fun hD hC => absurd (dying_lt hD) (Nat.not_lt.2 hC.1.1),
   fun hD hE => hE.2.2.1 hD,
   fun hC hE => absurd hE.1 (Nat.not_lt.2 hC.1.1),
   fun hN => hN.2,
   fun _ h => h.1⟩

/-- Brief, task 2, partition: every touch is of class D, C, E or N. -/
theorem classes_cover {L : MutexLayout} {st st' : SC × SyncReg × ArenaReg} {lbl : Label}
    {l : Nat} (h : TouchL L st st' lbl l) :
    ClassD st st' l ∨ ClassC st st' l ∨ ClassE st st' lbl l ∨ ClassN L st st' lbl l := by
  by_cases hD : ClassD st st' l
  · exact .inl hD
  by_cases hC : ClassC st st' l
  · exact .inr (.inl hC)
  by_cases hE : ClassE st st' lbl l
  · exact .inr (.inr (.inl hE))
  · exact .inr (.inr (.inr ⟨h, hD, hC, hE⟩))

/-! ## The final footprint on existing leaves -/

/-- On an `ok` step, an existing leaf of the final footprint dies in the step or carries a mode
required by the clause (`TouchesF`, `HasReq`): the leaves of `free`, `exitFrame` and `terminate`
in the footprint are the dying ones (Spec 1 §70, §73; WC5.3 C7); those of `endUse` are the leaves
of `place` (§69.1) or the dying ones; the fresh part of `alloc`, `enterFrame`, `spawn` and the
by-value `spawn` holds no existing leaf. -/
theorem touchesF_existing {k : K} {L : MutexLayout} {st st' : SC × SyncReg × ArenaReg}
    {lbl : Label} {l : Nat} (hs : LStep k L lbl st st') (hlt : l < st.1.P.length)
    (ht : TouchesF L st lbl l) : ClassD st st' l ∨ HasReq st lbl l := by
  cases hs with
  | @kernel s s' reg ar c op h =>
    cases op with
    | read | write | writeShared | store | transfer => exact .inr trivial
    | endUse p =>
      rcases ht with hl | hd
      · exact .inr hl
      · obtain ⟨t, hR, rfl⟩ := viewStep_ok h
        obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hR
        exact .inl hd
    | free p au =>
      obtain ⟨t, hR, rfl⟩ := viewStep_ok h
      obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hR
      exact .inl ht
    | exit =>
      obtain ⟨-, h'⟩ := h; obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h'
      exact .inl ht
    | alloc pr ow ls =>
      rcases ht with hl | hl | hl
      · exact .inr (.inl hl)
      · exact .inr (.inr hl)
      · exact absurd hlt (Nat.not_lt.2 hl)
    | enter ps ls => exact absurd hlt (Nat.not_lt.2 ht)
    | _ => exact (ht : False).elim
  | spawn => exact absurd hlt (Nat.not_lt.2 ht)
  | @terminate s s' reg ar c h =>
    obtain ⟨-, h'⟩ := h; obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h'
    exact .inl ht
  | spawnVal =>
    rcases ht with hl | hv
    · exact absurd hlt (Nat.not_lt.2 hl)
    · exact .inr hv
  | issue | newMutex | acquire | unlock | resetLock => exact .inr trivial
  | _ => exact (ht : False).elim

/-- On an `ok` step, an existing touched leaf is of class D or E. -/
theorem existing_classDE {k : K} {L : MutexLayout} {st st' : SC × SyncReg × ArenaReg}
    {lbl : Label} {l : Nat} (hs : LStep k L lbl st st') (hlt : l < st.1.P.length)
    (hleaf : isLeaf st.1.P l) (ht : TouchesF L st lbl l) :
    ClassD st st' l ∨ ClassE st st' lbl l := by
  by_cases hD : ClassD st st' l
  · exact .inl hD
  · rcases touchesF_existing hs hlt ht with h | h
    · exact absurd h hD
    · exact .inr ⟨hlt, hleaf, hD, h⟩

/-- Brief, task 2, class N: on an `ok` step, a touched leaf of class N is a leaf created by the
step and not written by it. So class N is not empty as soon as a step creates a leaf without
writing it: the fresh locals of `enterFrame` and `spawn` (Spec 1 §72 effect; WC5.3 C4), the fresh
leaves of `alloc` (§71), the locals of a by-value `spawn` that are no destination (WC5.3 C5
phase 1); all are in `TouchesF` (`|P| ≤ l`). -/
theorem classN_created {k : K} {L : MutexLayout} {st st' : SC × SyncReg × ArenaReg} {lbl : Label}
    {l : Nat} (hs : LStep k L lbl st st') (h : ClassN L st st' lbl l) :
    Created st st' l ∧ isLeaf st'.1.P l ∧ ¬ CW st st' l := by
  obtain ⟨ht, hD, hC, hE⟩ := h
  rcases ht with ⟨hlt, hleaf, ht⟩ | ⟨hc, hleaf, -⟩ | hw
  · rcases existing_classDE hs hlt hleaf ht with h | h
    · exact absurd h hD
    · exact absurd h hE
  · exact ⟨hc, hleaf, hC⟩
  · exact absurd hw hC

/-! ## Created places -/

/-- A kernel operation other than `enterFrame` and `alloc` keeps the number of places (Spec 1
§60–§70, §73–§75 effects; §63 effect for `transfer`). -/
theorem opStepC_len {k : K} {op : KernelOp} {c : Nat} {s s' : SC}
    (h : opStepC k op c s (.ok s')) (hne : ∀ ps ls, op ≠ .enter ps ls)
    (hna : ∀ pr ow ls, op ≠ .alloc pr ow ls) : s'.P.length = s.P.length := by
  cases op with
  | enter ps ls => exact absurd rfl (hne ps ls)
  | alloc pr ow ls => exact absurd rfl (hna pr ow ls)
  | transfer src dst =>
    obtain ⟨-, h⟩ := h; obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
    show (transferEff (s.view c) src dst).P.length = _
    rw [transfer_len]; rfl
  | depend q x => obtain ⟨-, h⟩ := h; obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; rfl
  | store a p =>
    obtain ⟨-, h⟩ := h; obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
    show (storeEff (s.view c) a p).P.length = _
    unfold storeEff; split <;> rfl
  | exit => obtain ⟨-, h⟩ := h; obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; rfl
  | release a =>
    obtain ⟨t, hR, rfl⟩ := viewStep_ok h
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hR
    show (releaseEff (s.view c) a).P.length = _
    unfold releaseEff; split <;> rfl
  | _ =>
    obtain ⟨t, hR, rfl⟩ := viewStep_ok h
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hR
    rfl

/-- The fresh leaves of `enterFrame` executed by `c` are `Uninit` (Spec 1 §72 effect). -/
theorem enterC_fresh_uninit (s : SC) (c : Nat) (ps : List Nat) (ls : LocalShape) {l : Nat}
    (hl : s.P.length ≤ l) : (enterEffC s c ps ls).I l = .uninit := by
  show (if s.P.length ≤ l then InitSt.uninit else s.I l) = _
  split
  · rfl
  · exact absurd hl ‹_›

/-- The fresh leaves of `spawn` executed by `c`, and of the creation phase of the by-value `spawn`,
are `Uninit` (WC5.3 C4 effect, C5 phase 1). -/
theorem spawn_fresh_uninit (s : SC) (c : Nat) (ps : List Nat) (ls : LocalShape) {l : Nat}
    (hl : s.P.length ≤ l) : (spawnEff s c ps ls).I l = .uninit := by
  show (if s.P.length ≤ l then InitSt.uninit else s.I l) = _
  split
  · rfl
  · exact absurd hl ‹_›

/-- Brief, task 2, class C: on an `ok` step, a leaf created and written by the step is created by
a by-value `spawn`. The other steps create no place, except `enterFrame`, `spawn` and `alloc`,
whose fresh leaves are `Uninit` after the step (Spec 1 §71 effect: "its leaves start `Uninit`";
§72 effect; WC5.3 C4 effect). -/
theorem cw_spawnVal {k : K} {L : MutexLayout} {st st' : SC × SyncReg × ArenaReg} {lbl : Label}
    {l : Nat} (hs : LStep k L lbl st st') (h : CW st st' l) :
    ∃ c ps ls vs, lbl = .spawnVal c ps ls vs := by
  obtain ⟨⟨hge, hlt⟩, -, hI⟩ := h
  have hlen : ∀ {s s' : SC}, s'.P.length = s.P.length → s.P.length ≤ l →
      l < s'.P.length → False := fun e h1 h2 => by omega
  cases hs with
  | @kernel s s' reg ar c op h =>
    cases op with
    | enter ps ls =>
      obtain ⟨-, h'⟩ := h; obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h'
      rw [show (enterEffC s c ps ls).I l = .uninit from enterC_fresh_uninit s c ps ls hge] at hI
      cases hI
    | alloc pr ow ls =>
      obtain ⟨t, hR, rfl⟩ := viewStep_ok h
      cases hR with
      | ok =>
        have : (s.set (allocEff (s.view c) ow ls)).I l = .uninit := by
          show (if s.P.length ≤ l then InitSt.uninit else s.I l) = _
          split
          · rfl
          · exact absurd hge ‹_›
        rw [this] at hI; cases hI
    | _ =>
      exact (hlen (opStepC_len h (fun _ _ e => by cases e) (fun _ _ _ e => by cases e)) hge
        hlt).elim
  | @spawn s s' reg ar c ps ls h =>
    obtain ⟨-, h'⟩ := h; obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h'
    rw [show (spawnEff s c ps ls).I l = .uninit from spawn_fresh_uninit s c ps ls hge] at hI
    cases hI
  | spawnVal => exact ⟨_, _, _, _, rfl⟩
  | terminate h =>
    obtain ⟨-, h'⟩ := h; obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h'
    exact (hlen rfl hge hlt).elim
  | join h => cases h; exact (hlen rfl hge hlt).elim
  | deriveSync h =>
    obtain ⟨-, h'⟩ := h; obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h'
    exact (hlen rfl hge hlt).elim
  | newMutex h => obtain ⟨-, -, rfl⟩ := h; exact (hlen rfl hge hlt).elim
  | acquire h =>
    obtain ⟨-, _, -, -, -, rfl⟩ := h
    exact (hlen rfl hge hlt).elim
  | unlock h =>
    obtain ⟨-, _, _, -, -, -, -, -, rfl⟩ := h
    exact (hlen (by show (releaseEff _ _).P.length = _; unfold releaseEff; split <;> rfl) hge
      hlt).elim
  | resetLock h =>
    obtain ⟨-, _, -, -, -, -, rfl⟩ := h
    exact (hlen rfl hge hlt).elim
  | newArena h => obtain ⟨-, -, rfl⟩ := newArenaStepC_ok h; exact (hlen rfl hge hlt).elim
  | issue h =>
    obtain ⟨_, _, -, -, -, hsp, hsto, -⟩ := issueStepC_ok h
    exact (hlen ((opStepC_len hsto (fun _ _ e => by cases e) (fun _ _ _ e => by cases e)).trans
      (opStepC_len hsp (fun _ _ e => by cases e) (fun _ _ _ e => by cases e))) hge hlt).elim
  | reset h =>
    obtain ⟨_, _, -, hd, hrl, -, -⟩ := resetStepC_ok (k := k) h
    exact (hlen ((opStepC_len hrl (fun _ _ e => by cases e) (fun _ _ _ e => by cases e)).trans
      (opStepC_len hd (fun _ _ e => by cases e) (fun _ _ _ e => by cases e))) hge hlt).elim

/-! ## The capacity of an existing touched leaf -/

/-- Unfolding of `ExtPair`. -/
theorem ExtPair.out {k : K} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg}
    {lbls : List Label} {i j l : Nat} (hp : ExtPair k L σ lbls i j l) :
    ∃ (hij : i < j) (hj : j < lbls.length),
      (lbls[i]'(Nat.lt_trans hij hj)).ctx ≠ lbls[j].ctx ∧
      TouchL L (σ i) (σ (i + 1)) (lbls[i]'(Nat.lt_trans hij hj)) l ∧
      TouchL L (σ j) (σ (j + 1)) lbls[j] l ∧
      (ExclTouch k L (σ i) (σ (i + 1)) (lbls[i]'(Nat.lt_trans hij hj)) l ∨
        ExclTouch k L (σ j) (σ (j + 1)) lbls[j] l) := by
  obtain ⟨hij, hp⟩ := hp
  have hjl : j < lbls.length := by
    refine Nat.lt_of_not_le fun hle => ?_
    rw [List.getElem?_eq_none hle] at hp
    revert hp; cases lbls[i]? <;> exact id
  rw [List.getElem?_eq_getElem (Nat.lt_trans hij hjl), List.getElem?_eq_getElem hjl] at hp
  exact ⟨hij, hjl, hp⟩

/-- The required mode of a touched leaf gives the capacity of the acting context (`CapReq`, brief
of slice 3, task 4), the sources of a by-value `spawn` being given by `hsv` (WC5.3 C5, additional
precondition 1). -/
theorem capReq_mode {k : K} {st : SC × SyncReg × ArenaReg} {lbl : Label} {l : Nat} {m : Mode}
    (hc : CapReq k st lbl l) (hm : ReqMode k st lbl l m)
    (hsv : ∀ c ps ls vs, lbl = .spawnVal c ps ls vs → ∀ v ∈ vs, ∀ l' ∈ footprint st.1.P v.1,
      Allows (cap5 st.1 st.2.1 c l') .modify) :
    Allows (cap5 st.1 st.2.1 lbl.ctx l) m := by
  cases lbl with
  | kernel c op =>
    cases op with
    | read | writeShared => have e : m = .observe := hm; subst e; exact hc
    | write | store | transfer => have e : m = .modify := hm; subst e; exact hc
    | endUse p | free p _ => obtain ⟨hl, rfl⟩ := hm; exact hc hl
    | alloc pr ow ls =>
      rcases hm with ⟨rfl, rfl⟩ | ⟨-, hl, ⟨-, rfl⟩ | ⟨hs, rfl⟩⟩
      · exact hc.2 rfl
      · exact (hc.1 hl).1
      · rcases (hc.1 hl).2 with h | h
        · exact h
        · exact absurd h hs
    | _ => exact (hm : False).elim
  | issue | newMutex => have e : m = .modify := hm; subst e; exact hc
  | acquire | unlock | resetLock => have e : m = .observe := hm; subst e; exact hc
  | spawnVal c ps ls vs =>
    obtain ⟨⟨v, hv, hl⟩, rfl⟩ := hm
    exact hsv c ps ls vs rfl v hv l hl
  | _ => exact (hm : False).elim

/-- On a leaf where the clause requires a mode, `CapReq` gives at least `Observe`. -/
theorem capReq_observe {k : K} {st : SC × SyncReg × ArenaReg} {lbl : Label} {l : Nat}
    (hc : CapReq k st lbl l) (hr : HasReq st lbl l)
    (hsv : ∀ c ps ls vs, lbl = .spawnVal c ps ls vs → ∀ v ∈ vs, ∀ l' ∈ footprint st.1.P v.1,
      Allows (cap5 st.1 st.2.1 c l') .modify) :
    Allows (cap5 st.1 st.2.1 lbl.ctx l) .observe := by
  cases lbl with
  | kernel c op =>
    cases op with
    | read | writeShared => exact hc
    | write | store | transfer => exact allows_observe_of_modify hc
    | endUse p | free p _ => exact allows_observe_of_modify (hc hr)
    | alloc pr ow ls =>
      rcases hr with hl | hl
      · exact (hc.1 hl).1
      · exact allows_observe_of_modify (hc.2 hl)
    | _ => exact (hr : False).elim
  | issue | newMutex => exact allows_observe_of_modify hc
  | acquire | unlock | resetLock => exact hc
  | spawnVal c ps ls vs =>
    obtain ⟨v, hv, hl⟩ := hr
    exact allows_observe_of_modify (hsv c ps ls vs rfl v hv l hl)
  | _ => exact (hr : False).elim

/-- A leaf on which a context has a `cap5` is usable when `NoDangling` holds (Spec 1 §54): an
authority attaining it is active and covers the leaf. -/
theorem usable_of_cap5 {s : SC} {reg : SyncReg} {c l : Nat} (hnd : NoDangling s.flat)
    (hleaf : isLeaf s.P l) (hlt : l < s.P.length) (h : Allows (cap5 s reg c l) .observe) :
    s.flat.Usable l := by
  obtain ⟨x, -, -, hex⟩ := cap5_attained h
  obtain ⟨z, hz, za, hlz, -⟩ := eff_present (ne_none_of_allows hex)
  exact Decidable.byContradiction fun hu => hnd x z hz za l hu l (mem_footprint_self hleaf hlt) hlz

/-- On a `RunFull` from the initial state, the sources of a by-value `spawn` step carry `Modify`
for the creator (`spawnVal_cap_pre`), in the form `capReq_mode` reads. -/
theorem spawnVal_cap_run {k : K} {L : MutexLayout} {statics : Statics}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} (hdd : DDSound k)
    (hstat : StaticsOK statics) (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], []))
    (h : RunFull k L σ lbls) {i : Nat} (hi : i < lbls.length) :
    ∀ c ps ls vs, lbls[i] = .spawnVal c ps ls vs → ∀ v ∈ vs, ∀ l' ∈ footprint (σ i).1.P v.1,
      Allows (cap5 (σ i).1 (σ i).2.1 c l') .modify :=
  fun _ _ _ _ e v hv l hl => (spawnVal_cap_pre hdd hstat h0 h hi e v hv l hl).2

/-- Brief, task 2, link of class E: on a `RunFull` from the initial state, a touch of class E
with required mode `m` is made with `cap5` at least `m` (`capacity_run`, `spawnVal_cap_pre`). -/
theorem classEm_cap_run {k : K} {L : MutexLayout} {statics : Statics}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} (hdd : DDSound k)
    (hstat : StaticsOK statics) (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], []))
    (h : RunFull k L σ lbls) {i : Nat} (hi : i < lbls.length) {l : Nat} {m : Mode}
    (ht : TouchL L (σ i) (σ (i + 1)) lbls[i] l) (hE : ClassEm k (σ i) (σ (i + 1)) lbls[i] l m) :
    Allows (cap5 (σ i).1 (σ i).2.1 lbls[i].ctx l) m := by
  obtain ⟨⟨hlt, hleaf, -, -⟩, hm⟩ := hE
  have htf : TouchesF L (σ i) lbls[i] l := by
    rcases ht with ⟨-, -, h⟩ | ⟨hc, -⟩ | hc
    · exact h
    · exact absurd hlt (Nat.not_lt.2 hc.1)
    · exact absurd hlt (Nat.not_lt.2 hc.1.1)
  exact capReq_mode (capacity_run hdd hstat h0 h hi hleaf hlt htf) hm
    (spawnVal_cap_run hdd hstat h0 h hi)

/-- Brief, task 2, link of class D: on a `RunFull` from the initial state, no context other than
the acting one has a `cap5` on a leaf of class D (`other_cap_dying_run`). -/
theorem classD_other_run {k : K} {L : MutexLayout} {statics : Statics}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} (hdd : DDSound k)
    (hstat : StaticsOK statics) (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], []))
    (h : RunFull k L σ lbls) {i : Nat} (hi : i < lbls.length) {c' l : Nat}
    (hc' : c' ≠ lbls[i].ctx) (hD : ClassD (σ i) (σ (i + 1)) l) :
    cap5 (σ i).1 (σ i).2.1 c' l = none :=
  other_cap_dying_run hdd hstat h0 h hi hc' hD

/-! ## Dead leaves, first statement -/

/-- Brief, task 2, "Feuilles mortes", first statement: on a `RunFull` from the initial state, a
step that touches an existing leaf requires it to be usable in the state before the step. A leaf of
class D is usable before the step by definition; one of class E carries a `cap5` of the acting
context (`capacity_run`, `spawnVal_cap_pre`), so an active authority covers it, and `NoDangling`
(Spec 1 §54) makes it usable. Each clause that touches an existing leaf indeed requires its place
usable (Spec 1 §63.1, §65.2, §66.1, §67.1, §69.1, §70, §71.2; WC5.3 C13 item 3, C21 item 3). -/
theorem touch_usable_run {k : K} {L : MutexLayout} {statics : Statics}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} (hdd : DDSound k)
    (hstat : StaticsOK statics) (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], []))
    (h : RunFull k L σ lbls) {i : Nat} (hi : i < lbls.length) {l : Nat}
    (ht : TouchL L (σ i) (σ (i + 1)) lbls[i] l) (hlt : l < (σ i).1.P.length) :
    (σ i).1.flat.Usable l := by
  obtain ⟨-, hleaf, htf⟩ : l < (σ i).1.P.length ∧ isLeaf (σ i).1.P l ∧ TouchesF L (σ i) lbls[i] l := by
    rcases ht with h | ⟨hc, -⟩ | hc
    · exact h
    · exact absurd hlt (Nat.not_lt.2 hc.1)
    · exact absurd hlt (Nat.not_lt.2 hc.1.1)
  rcases existing_classDE (h i hi).2 hlt hleaf htf with hD | ⟨-, -, -, hr⟩
  · exact hD.2.1
  · have hk := (runFull_inv hdd hstat h0 h (Nat.le_of_lt hi)).1
    exact usable_of_cap5 (c := lbls[i].ctx) hk.1.2.1.2.2 hleaf hlt
      (capReq_observe (capacity_run hdd hstat h0 h hi hleaf hlt htf) hr
        (spawnVal_cap_run hdd hstat h0 h hi))

/-! ## Dead leaves, second statement: usability is never regained -/

/-- A place existing before a step and usable after it was usable before, when the step keeps the
existing places, marks no marked place unmarked and adds only frames of identity at least `nF`
(Spec 1 §40; §49.3: owner frames are below `nF`). -/
theorem flat_usable_back {s s' : SC} (hw : WF3 s.flat)
    (hP : ∀ q < s.P.length, s'.P[q]? = s.P[q]?)
    (hd : ∀ q < s.P.length, s'.dead q = false → s.dead q = false)
    (hF : ∀ f, f < s.nF → f ∈ s'.frames → f ∈ s.frames) {q : Nat} (hq : q < s.P.length)
    (h : s'.flat.Usable q) : s.flat.Usable q := by
  revert hq
  induction h with
  | @frame q f pl hpl hdq ho hf =>
    intro hq
    have hpl' : s.P[q]? = some pl := (hP q hq).symm.trans hpl
    exact .frame hpl' (hd q hq hdq) ho (hF f (hw.owners.1 q pl f hpl' ho) hf)
  | @place q o pl hpl hdq ho _ ih =>
    intro hq
    have hpl' : s.P[q]? = some pl := (hP q hq).symm.trans hpl
    exact .place hpl' (hd q hq hdq) ho (ih (hw.owners.2.1 q pl o hpl' ho))

/-- The frames of `enterFrame` and `spawn` are the old ones and `nF` (Spec 1 §72; WC5.3 C4). -/
theorem push_old {s s' : SC} {top : Nat} (hp : Push s s' top) :
    ∀ f, f < s.nF → f ∈ s'.frames → f ∈ s.frames := fun f hf hm => by
  rcases (hp.mem f).1 hm with rfl | h
  · exact absurd hf (Nat.lt_irrefl _)
  · exact h

/-- `spawn` executed by `c`, and the creation phase of the by-value `spawn`, make no existing
place usable that was not (Spec 1 §72 effect; WC5.3 C4 effect, C5 phase 1). -/
theorem spawn_usable_back {s : SC} {c : Nat} {ps : List Nat} {ls : LocalShape} (hfr : FramesC s)
    (hw : WF3 s.flat) (hc : s.stk c ≠ []) {q : Nat} (hq : q < s.P.length)
    (h : (spawnEff s c ps ls).flat.Usable q) : s.flat.Usable q :=
  flat_usable_back hw
    (fun _ hq => by show (shapeP s.P _ _)[_]? = _; exact List.getElem?_append_left hq)
    (fun q hq hd => by
      have e : (if s.P.length ≤ q then false else s.dead q) = false := hd
      split at e
      · exact absurd hq (Nat.not_lt.2 ‹_›)
      · exact e)
    (push_old (spawn_push (ps := ps) (ls := ls) hfr hc)) hq h

/-- The kernel operations, executed by `c` from a state satisfying `KInvCA`, make no existing place
usable that was not (Spec 1 §40; §60–§75 effects: places are only appended, death markers only
set, frames only pushed fresh or popped; §63 effect with §63.1 for `transfer`,
`transfer_usable_back`). -/
theorem opStepC_usable_back {k : K} {op : KernelOp} {c : Nat} {s s' : SC} (hk : KInvCA s)
    (h : opStepC k op c s (.ok s')) {q : Nat} (hq : q < s.P.length) (hu : s'.flat.Usable q) :
    s.flat.Usable q := by
  have hw : WF3 s.flat := hk.1.1.2
  cases op with
  | transfer src dst =>
    obtain ⟨-, h⟩ := h; obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
    have h1 := (set_usable (s := s) (t := transferEff (s.view c) src dst)
      fun _ => SC.mem_view_F (s := s) (c := c)).1 hu
    exact (usable_mem_congr (t := s.flat) (F' := (s.view c).F) fun _ => SC.mem_view_F).1
      (transfer_usable_back (view_facts hk c).1 hpre.srcUsable h1)
  | enter ps ls =>
    obtain ⟨-, h⟩ := h; obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
    exact flat_usable_back hw
      (fun _ hq => by show (shapeP s.P _ _)[_]? = _; exact List.getElem?_append_left hq)
      (fun q hq hd => by
        have e : (if s.P.length ≤ q then false else s.dead q) = false := hd
        split at e
        · exact absurd hq (Nat.not_lt.2 ‹_›)
        · exact e)
      (push_old (enter_push (ps := ps) (ls := ls) hk.1.1.1 hpre.callerLive)) hq hu
  | exit =>
    obtain ⟨hl, h⟩ := h; obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
    have hpop := exitEffC_pop hk.1.1.1.nodup hpre.hasCaller
    exact flat_usable_back (s' := exitEffC s c) hw (fun _ _ => rfl) (fun _ _ hd => hd)
      (fun f _ hm => ((hpop.mem_frames hk.1.1.1.nodup).1 hm).1) hq hu
  | endUse p =>
    obtain ⟨t, hR, rfl⟩ := viewStep_ok h
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hR
    exact flat_usable_back (s' := s.set (endUseEff (s.view c) p)) hw (fun _ _ => rfl)
      (fun q _ hd => (Bool.or_eq_false_iff.1 hd).1) (fun _ _ hm => hm) hq hu
  | free p au =>
    obtain ⟨t, hR, rfl⟩ := viewStep_ok h
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hR
    exact flat_usable_back (s' := s.set (freeEff (s.view c) p)) hw (fun _ _ => rfl)
      (fun q _ hd => (Bool.or_eq_false_iff.1 hd).1) (fun _ _ hm => hm) hq hu
  | alloc pr ow ls =>
    obtain ⟨t, hR, rfl⟩ := viewStep_ok h
    cases hR with
    | ok =>
      exact flat_usable_back (s' := s.set (allocEff (s.view c) ow ls)) hw
        (fun _ hq => by show (shapeP s.P _ _)[_]? = _; exact List.getElem?_append_left hq)
        (fun q hq hd => by
          have e : (if s.P.length ≤ q then false else s.dead q) = false := hd
          split at e
          · exact absurd hq (Nat.not_lt.2 ‹_›)
          · exact e)
        (fun _ _ hm => hm) hq hu
  | depend q' x =>
    obtain ⟨-, h⟩ := h; obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
    exact (set_usable_iff rfl rfl).1 hu
  | store a p =>
    obtain ⟨-, h⟩ := h; obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
    exact (set_usable_iff (by unfold storeEff; split <;> rfl)
      (by unfold storeEff; split <;> rfl)).1 hu
  | release a =>
    obtain ⟨t, hR, rfl⟩ := viewStep_ok h
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hR
    exact (set_usable_iff (by unfold releaseEff; split <;> rfl)
      (by unfold releaseEff; split <;> rfl)).1 hu
  | _ =>
    obtain ⟨t, hR, rfl⟩ := viewStep_ok h
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hR
    exact (set_usable_iff rfl rfl).1 hu

/-- The transfer phases of a by-value `spawn` make no place usable that was not (WC5.3 C5
phase 2; Spec 1 §63 effect, §63.1 at the start of each phase, `ValTransferPre.srcUsable`). -/
theorem transfers_usable_back {k : K} {fin : S3} {c : Nat} :
    ∀ (t : SC) (vs : List (Nat × Nat)), ValTransfersPre k fin c t vs → KBase t →
      (∀ v ∈ vs, FrameOwned t.P v.2) → ∀ (q : Nat), (transfersEff c t vs).flat.Usable q →
        t.flat.Usable q
  | _, [], _, _, _, _, h => h
  | t, v :: vs, ⟨hpre, hrest⟩, hk, hown, q, h => by
    have hd' := transfer_usable_frameOwned (src := v.1) (dst := v.2) hpre.dstUsable
      (hown v (List.mem_cons_self ..))
    have hk₁ := transfer_base hk hpre.srcUsable hpre.dstUsable hpre.depsValid hpre.sameShape
      hpre.disjoint hd'
    have h₁ := transfers_usable_back (transferEffC t c v.1 v.2) vs hrest hk₁
      (fun w hw => transfer_frameOwned (hown w (List.mem_cons_of_mem _ hw))) q h
    have h₂ := (set_usable (s := t) (t := transferEff (t.view c) v.1 v.2)
      fun _ => SC.mem_view_F (s := t) (c := c)).1 h₁
    exact (usable_mem_congr (t := t.flat) (F' := (t.view c).F) fun _ => SC.mem_view_F).1
      (transfer_usable_back (view_facts_base hk c).1 hpre.srcUsable h₂)

/-- The by-value `spawn` makes no existing place usable that was not (WC5.3 C5: creation, transfer
phases, yield, which changes holders only). -/
theorem spawnVal_usable_back {k : K} {s s' : SC} {c : Nat} {ps : List Nat} {ls : LocalShape}
    {vs : List (Nat × Nat)} (hk : KInvCA s) (h : SpawnValStep k s c ps ls vs (.ok s')) {q : Nat}
    (hq : q < s.P.length) (hu : s'.flat.Usable q) : s.flat.Usable q := by
  obtain ⟨-, h⟩ := h; obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  have hb₀ : KBase (spawnCreate s c ls) :=
    spawn_base hk hpre.creatorLive (fun _ h => nomatch h) hpre.localsOK
  have h₂ : (transfersEff c (spawnCreate s c ls) vs).flat.Usable q :=
    (S3.Usable.congr (s := (transfersEff c (spawnCreate s c ls) vs).flat)
      (s' := (spawnValEff s c ps ls vs).flat) rfl rfl rfl).1 hu
  have h₁ := transfers_usable_back (spawnCreate s c ls) vs hpre.transfers hb₀
    (fun v hv => spawn_frameOwned (hpre.freshDst v hv)) q h₂
  exact spawn_usable_back hk.1.1.1 hk.1.1.2 hpre.creatorLive hq h₁

/-- Per-step form, under `KInvCA` and `DDSound` (used for the intermediate state of `issue` and
`reset`): no step makes usable an existing place that was not (Spec 1
§40; the effects of WC5.3 C2–C8, C13–C18 and Spec 1 §60–§78 on the places, the death markers and
the live frames). -/
theorem usable_back_step {k : K} {L : MutexLayout} {st st' : SC × SyncReg × ArenaReg}
    {lbl : Label} (hdd : DDSound k) (hk : KInvCA st.1) (hs : LStep k L lbl st st') {q : Nat}
    (hq : q < st.1.P.length) (hu : st'.1.flat.Usable q) : st.1.flat.Usable q := by
  cases hs with
  | kernel h => exact opStepC_usable_back hk h hq hu
  | spawn h =>
    obtain ⟨-, h'⟩ := h; obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h'
    exact spawn_usable_back hk.1.1.1 hk.1.1.2 hpre.creatorLive hq hu
  | @terminate s s' reg ar c h =>
    obtain ⟨hl, h'⟩ := h; obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h'
    have hpop := termEffC_pop hk.1.1.1.nodup hpre.initialOnly
      (hk.1.1.1.rooted c hpre.nonInitial hl)
    exact flat_usable_back (s' := termEffC s c) hk.1.1.2 (fun _ _ => rfl) (fun _ _ hd => hd)
      (fun f _ hm => ((hpop.mem_frames hk.1.1.1.nodup).1 hm).1) hq hu
  | join h => cases h; exact hu
  | deriveSync h =>
    obtain ⟨-, h'⟩ := h; obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h'
    exact (set_usable_iff rfl rfl).1 hu
  | newMutex h => obtain ⟨-, -, rfl⟩ := h; exact hu
  | acquire h =>
    obtain ⟨-, _, -, -, -, rfl⟩ := h
    exact (set_usable_iff rfl rfl).1 hu
  | unlock h =>
    obtain ⟨-, _, _, -, -, -, -, -, rfl⟩ := h
    exact (set_usable_iff (by unfold releaseEff; split <;> rfl)
      (by unfold releaseEff; split <;> rfl)).1 hu
  | resetLock h => obtain ⟨-, _, -, -, -, -, rfl⟩ := h; exact hu
  | spawnVal h => exact spawnVal_usable_back hk h hq hu
  | newArena h => obtain ⟨-, -, rfl⟩ := newArenaStepC_ok h; exact hu
  | issue h =>
    obtain ⟨_, _, -, -, -, hsp, hsto, -⟩ := issueStepC_ok h
    have hk₁ := opStepC_preservesC hdd hk (fun e => by cases e) hsp
    exact opStepC_usable_back hk hsp hq (opStepC_usable_back hk₁ hsto
      (by rw [opStepC_len hsp (fun _ _ e => by cases e) (fun _ _ _ e => by cases e)]; exact hq) hu)
  | reset h =>
    obtain ⟨_, _, -, hd, hrl, -, -⟩ := resetStepC_ok (k := k) h
    have hk₁ := opStepC_preservesC hdd hk (fun e => by cases e) hd
    exact opStepC_usable_back hk hd hq (opStepC_usable_back hk₁ hrl
      (by rw [opStepC_len hd (fun _ _ e => by cases e) (fun _ _ _ e => by cases e)]; exact hq) hu)

/-! ## Along a run -/

/-- A step of a `RunFull` from the initial state does not lower the number of places (`PSkel` of
`shape_step`). -/
theorem len_step_run {k : K} {L : MutexLayout} {statics : Statics}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} (hdd : DDSound k)
    (hstat : StaticsOK statics) (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], []))
    (h : RunFull k L σ lbls) {i : Nat} (hi : i < lbls.length) :
    (σ i).1.P.length ≤ (σ (i + 1)).1.P.length := by
  obtain ⟨hk, hlib⟩ := runFull_inv hdd hstat h0 h (Nat.le_of_lt hi)
  exact (shape_step hk hlib.2.1 (h i hi).1.1.1.1.1 (h i hi).2).2.1

/-- Along a `RunFull` from the initial state, the number of places does not decrease. -/
theorem len_mono_run {k : K} {L : MutexLayout} {statics : Statics}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} (hdd : DDSound k)
    (hstat : StaticsOK statics) (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], []))
    (h : RunFull k L σ lbls) {i j : Nat} (hij : i ≤ j) (hj : j ≤ lbls.length) :
    (σ i).1.P.length ≤ (σ j).1.P.length := by
  revert hj
  induction hij with
  | refl => exact fun _ => Nat.le_refl _
  | @step m _ ih =>
    intro hj
    exact Nat.le_trans (ih (by omega)) (len_step_run hdd hstat h0 h (by omega))

/-- Brief, task 2, "Feuilles mortes", second statement (the counterpart of `usable_run`): on a
`RunFull` from the initial state, under `DDSound` and `StaticsOK`, a place that exists and is not
usable in a state is not usable in any later state (Spec 1 §40; `usable_back_step`). -/
theorem unusable_run {k : K} {L : MutexLayout} {statics : Statics}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} (hdd : DDSound k)
    (hstat : StaticsOK statics) (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], []))
    (h : RunFull k L σ lbls) {i j q : Nat} (hij : i ≤ j) (hj : j ≤ lbls.length)
    (hq : q < (σ i).1.P.length) (hu : ¬ (σ i).1.flat.Usable q) : ¬ (σ j).1.flat.Usable q := by
  revert hj
  induction hij with
  | refl => exact fun _ => hu
  | @step m hle ih =>
    intro hj hu'
    have hm : m < lbls.length := by omega
    have hqm : q < (σ m).1.P.length :=
      Nat.lt_of_lt_of_le hq (len_mono_run hdd hstat h0 h hle (Nat.le_of_lt hm))
    exact ih (Nat.le_of_lt hm)
      (usable_back_step hdd (runFull_inv hdd hstat h0 h (Nat.le_of_lt hm)).1 (h m hm).2 hqm hu')

/-- Brief, task 2, "Identités de places": on a `RunFull` from the initial state, a place created by
step `j` does not exist in the state before it, nor in any earlier state: identities are not
reused (Spec 1 §40: a place's identity is its index; the places are only appended, `PSkel`). -/
theorem created_fresh_run {k : K} {L : MutexLayout} {statics : Statics}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} (hdd : DDSound k)
    (hstat : StaticsOK statics) (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], []))
    (h : RunFull k L σ lbls) {j l : Nat} (hj : j < lbls.length)
    (hc : Created (σ j) (σ (j + 1)) l) {i : Nat} (hij : i ≤ j) : (σ i).1.P.length ≤ l :=
  Nat.le_trans (len_mono_run hdd hstat h0 h hij (Nat.le_of_lt hj)) hc.1

/-- A leaf touched by step `i` exists after it. -/
theorem touch_lt_run {k : K} {L : MutexLayout} {statics : Statics}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} (hdd : DDSound k)
    (hstat : StaticsOK statics) (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], []))
    (h : RunFull k L σ lbls) {i : Nat} (hi : i < lbls.length) {l : Nat}
    (ht : TouchL L (σ i) (σ (i + 1)) lbls[i] l) : l < (σ (i + 1)).1.P.length := by
  rcases ht with ⟨hlt, -, -⟩ | ⟨hc, -⟩ | hc
  · exact Nat.lt_of_lt_of_le hlt (len_step_run hdd hstat h0 h hi)
  · exact hc.2
  · exact hc.1.2

/-! ## Corollaries -/

/-- Brief, task 2, second corollary: on a `RunFull` from the initial state, no extended exclusive
pair has as second member a step that creates `l`: the first member touched `l`, which therefore
existed before the second (`created_fresh_run`). -/
theorem extPair_second_not_created {k : K} {L : MutexLayout} {statics : Statics}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} (hdd : DDSound k)
    (hstat : StaticsOK statics) (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], []))
    (h : RunFull k L σ lbls) {i j l : Nat} (hp : ExtPair k L σ lbls i j l) :
    ¬ Created (σ j) (σ (j + 1)) l := by
  obtain ⟨hij, hj, -, hti, -, -⟩ := hp.out
  intro hc
  have h1 := touch_lt_run hdd hstat h0 h (Nat.lt_trans hij hj) hti
  have h2 := created_fresh_run hdd hstat h0 h hj hc (i := i + 1) (Nat.succ_le_of_lt hij)
  omega

/-- On a `RunFull` from the initial state, the second member of an extended exclusive pair touches
an existing leaf of its final footprint. -/
theorem extPair_second_existing {k : K} {L : MutexLayout} {statics : Statics}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} (hdd : DDSound k)
    (hstat : StaticsOK statics) (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], []))
    (h : RunFull k L σ lbls) {i j l : Nat} (hp : ExtPair k L σ lbls i j l) :
    ∃ hj : j < lbls.length, l < (σ j).1.P.length ∧ isLeaf (σ j).1.P l ∧
      TouchesF L (σ j) lbls[j] l := by
  have hn := extPair_second_not_created hdd hstat h0 h hp
  obtain ⟨-, hj, -, -, htj, -⟩ := hp.out
  refine ⟨hj, ?_⟩
  rcases htj with h' | ⟨hc, -⟩ | hc
  · exact h'
  · exact absurd hc hn
  · exact absurd hc.1 hn

/-- On a `RunFull` from the initial state, the touch of the second member of an extended exclusive
pair is of class D or E. -/
theorem extPair_second_classDE {k : K} {L : MutexLayout} {statics : Statics}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} (hdd : DDSound k)
    (hstat : StaticsOK statics) (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], []))
    (h : RunFull k L σ lbls) {i j l : Nat} (hp : ExtPair k L σ lbls i j l) :
    ∃ hj : j < lbls.length,
      ClassD (σ j) (σ (j + 1)) l ∨ ClassE (σ j) (σ (j + 1)) lbls[j] l := by
  obtain ⟨hj, hlt, hleaf, htf⟩ := extPair_second_existing hdd hstat h0 h hp
  exact ⟨hj, existing_classDE (h j hj).2 hlt hleaf htf⟩

/-- Brief, task 2, first corollary: on a `RunFull` from the initial state, no extended exclusive
pair has as first member a step in which `l` dies: the second member touches `l` as an existing
leaf, so `l` is usable before it (`touch_usable_run`), whereas a dead leaf stays unusable
(`unusable_run`). -/
theorem extPair_first_not_dying {k : K} {L : MutexLayout} {statics : Statics}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} (hdd : DDSound k)
    (hstat : StaticsOK statics) (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], []))
    (h : RunFull k L σ lbls) {i j l : Nat} (hp : ExtPair k L σ lbls i j l) :
    ¬ ClassD (σ i) (σ (i + 1)) l := by
  intro hD
  obtain ⟨hj, hlt, hleaf, htf⟩ := extPair_second_existing hdd hstat h0 h hp
  obtain ⟨hij, -⟩ := hp
  have hu := touch_usable_run hdd hstat h0 h hj (.inl ⟨hlt, hleaf, htf⟩) hlt
  have hl1 : l < (σ (i + 1)).1.P.length :=
    Nat.lt_of_lt_of_le (dying_lt hD) (len_step_run hdd hstat h0 h (Nat.lt_trans hij hj))
  exact unusable_run hdd hstat h0 h (i := i + 1) (Nat.succ_le_of_lt hij) (Nat.le_of_lt hj) hl1
    hD.2.2 hu

end Ern.Concurrency.FullEncap.HandoffExt
