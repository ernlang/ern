import Ern.ConcurrencyModel.Conservativity
import Ern.ConcurrencyModel.Library

/-!
# Preservation of the synchronization invariants: the clauses of C21, C22

Per-operation lemmas for the preservation of `SyncInv` (C21) and `GrantDiscipline` (C22),
theorems 2 and 4 of `formal/DESIGN.md`: the per-entry clauses C21.1–C21.3, C21.5, C21.6, C22 and
guarded-identity uniqueness among synchronization entries (C21.4, second clause), grouped as
`SyncCore`, for every labelled step admitted by `RestrictedStep` (C23). Controller uniqueness
(C21.4, first clause), the guard across registries, the initialization invariant (C21.7) and the
assembled statements are in `Ern.ConcurrencyModel.SyncInit`.

The kernel facts about the states before and after a step (`WF3`) are hypotheses supplied by
theorem 2 (preservation of the re-indexed kernel invariant).

-/

namespace Ern.ConcurrencyModel

open Ern.MemoryModel.Access

/-- The synchronization invariant of theorems 2 and 4: `SyncInv` (C21) and `GrantDiscipline` (C22). -/
def SyncState (L : MutexLayout) (s : SC) (reg : SyncReg) (ar : ArenaReg) : Prop :=
  SyncInv L s reg ar ∧ GrantDiscipline s reg

namespace SyncPreserveAux

/-! ## Per-entry decomposition -/

/-- The clauses of `SyncState` about one entry (C21.1–C21.3, C21.5, C21.6, C22). -/
structure EntryOK (L : MutexLayout) (s : SC) (e : SyncEntry) : Prop where
  guarded : e.Live s → OptP (s.A[e.guarded]?) (fun y => y.mode = .modify ∧
    PlaceUsable s.flat y.holder) False
  grant : e.Live s → ∀ g, e.grant = some g → OptP (s.A[g]?) (fun y =>
    y.origin = some e.guarded ∧ ∀ l, l ∈ y.footprint ↔ l ∈ s.flat.afp e.guarded) False
  control : e.Live s → OptP (ControlOf L s e) (fun ctl =>
    s.flat.Usable ctl ∧ isLeaf s.P ctl) False
  disc : e.Live s → e.grant = none → NoCoveringDesc s e.guarded
  sub : e.Live s → ∀ g, e.grant = some g → s.flat.Active g →
    ∀ j, CoveringDesc s e.guarded j → j = g ∨ g ∈ s.flat.ancs j
  bound : e.guarded < s.A.length

/-- The guarded-identity uniqueness of `SyncState` (C21.4, second clause). -/
def Uniq (s : SC) (reg : SyncReg) : Prop :=
  ∀ (i j : Nat) (e e' : SyncEntry), reg[i]? = some e → reg[j]? = some e' → e.Live s →
    e'.Live s → e.guarded = e'.guarded → i = j

end SyncPreserveAux

open SyncPreserveAux

/-- The clauses of `SyncState` other than controller uniqueness (C21.4, first clause) and the
initialization invariant (C21.7): the per-entry clauses (C21.1–C21.3, C21.5, C21.6, C22)
and guarded-identity uniqueness (C21.4, second clause). -/
def SyncCore (L : MutexLayout) (s : SC) (reg : SyncReg) : Prop :=
  (∀ e ∈ reg, EntryOK L s e) ∧ Uniq s reg

/-- `SyncState` is `SyncCore` with controller uniqueness (C21.4), the guard across registries
(C21.4, C13.7) and the initialization invariant (C21.7). -/
theorem syncState_iff {L : MutexLayout} {s : SC} {reg : SyncReg} {ar : ArenaReg} :
    SyncState L s reg ar ↔
      SyncCore L s reg ∧ CtlUnique L s reg ∧ AdminSep s reg ar ∧ SlotInit s reg ∧
        CtlInit L s reg := by
  constructor
  · rintro ⟨hi, hg⟩
    exact ⟨⟨fun e he => ⟨hi.guarded e he, hi.grant e he, hi.control e he, hg e he,
      hi.grantSubtree e he, hi.regBound e he⟩, hi.unique⟩, hi.ctlUnique, hi.adminGuard,
      hi.slotInit, hi.ctlInit⟩
  · rintro ⟨⟨h, hu⟩, hc, hsep, hsi, hci⟩
    exact ⟨⟨fun e he => (h e he).guarded, fun e he => (h e he).grant,
      fun e he => (h e he).control, hc, hu, hsep, fun e he => (h e he).sub,
      fun e he => (h e he).bound, hsi, hci⟩, fun e he => (h e he).disc⟩

/-- The part of `SyncState` that reads only the synchronization registry: every clause of
`SyncInv` (C21) and `GrantDiscipline` (C22) except the guard across registries (C21.4, C13.7). -/
def SyncPart (L : MutexLayout) (s : SC) (reg : SyncReg) : Prop :=
  SyncCore L s reg ∧ CtlUnique L s reg ∧ SlotInit s reg ∧ CtlInit L s reg

/-- `SyncState` is `SyncPart` with the guard across registries (C21.4, C13.7). -/
theorem syncState_part {L : MutexLayout} {s : SC} {reg : SyncReg} {ar : ArenaReg} :
    SyncState L s reg ar ↔ SyncPart L s reg ∧ AdminSep s reg ar := by
  rw [syncState_iff]
  exact ⟨fun ⟨a, b, c, d, e⟩ => ⟨⟨a, b, d, e⟩, c⟩, fun ⟨⟨a, b, d, e⟩, c⟩ => ⟨a, b, c, d, e⟩⟩

namespace SyncPreserveAux

/-! ## Controller -/

/-- Unfolding of the positional `ControlOf` (C12). -/
theorem controlOf_spec {L : MutexLayout} {s : SC} {e : SyncEntry} {ctl : Nat}
    (h : ControlOf L s e = some ctl) : ∃ y hp m, s.A[e.guarded]? = some y ∧
      y.holder = .place hp ∧ parentOf s.P hp = some m ∧
      (kids s.P m)[L.guardedField]? = some hp ∧ (kids s.P m)[L.controlField]? = some ctl := by
  unfold ControlOf at h
  cases hy : s.A[e.guarded]? with
  | none => rw [hy] at h; simp at h
  | some y =>
    rw [hy] at h
    cases hh : y.holder with
    | frame f => simp [hh] at h
    | place hp =>
      simp only [Option.map_some, hh] at h
      cases hm : parentOf s.P hp with
      | none => rw [hm] at h; cases h
      | some m =>
        rw [hm] at h
        by_cases hk : (kids s.P m)[L.guardedField]? = some hp
        · simp only [hk, ↓reduceIte] at h; exact ⟨y, hp, m, rfl, hh, hm, hk, h⟩
        · simp only [hk, ↓reduceIte] at h; cases h

/-- The controller of a live entry is usable when the place holding `guarded` is (C12: the
fields of the mutex value share its owner and death marker, Spec 1 §49.2). -/
theorem control_usable {L : MutexLayout} {s : SC} {e : SyncEntry} {ctl : Nat}
    (hw : WF3 s.flat) (hl : e.Live s) (h : ControlOf L s e = some ctl) : s.flat.Usable ctl := by
  obtain ⟨y, hp, m, hy, hh, hm, hk, hc⟩ := controlOf_spec h
  obtain ⟨y₀, hy₀, ya⟩ := hl
  have hy' : s.flat.A[e.guarded]? = some y := hy
  rw [hy'] at hy₀; cases hy₀
  have hu : s.flat.Usable hp := by have := hw.holders _ _ hy' ya; rw [hh] at this; exact this
  have hcm : parentOf s.P ctl = some m := (mem_kids.1 (List.mem_of_getElem? hc)).2
  have hpar : ∀ q, parentOf s.P q = some m → ∃ pl pm, s.P[q]? = some pl ∧ s.P[m]? = some pm ∧
      pm.owner = pl.owner ∧ s.dead m = s.dead q := by
    intro q hq
    simp only [parentOf] at hq
    cases hpl : s.P[q]? with
    | none => rw [hpl] at hq; cases hq
    | some pl =>
      rw [hpl] at hq
      obtain ⟨pm, hpm, -, ho, hd⟩ := hw.places q pl m hpl hq
      exact ⟨pl, pm, rfl, hpm, ho, hd⟩
  obtain ⟨ph, pm, hph, hpm, ho, hd⟩ := hpar hp hm
  obtain ⟨pc, pm', hpc, hpm', ho', hd'⟩ := hpar ctl hcm
  rw [hpm] at hpm'; cases hpm'
  exact S3.Usable.of_same hu hph hpc (by rw [← ho', ho]) (by
    show s.dead ctl = s.dead hp; rw [← hd', hd])

/-! ## Abstract effect of a step on authorities -/

/-- What a step does to authorities, read on the effects of Spec 1 §60–§75 re-indexed and of 
C4, C7, C8, C15: authorities are only added; an old authority keeps its footprint and mode, is
never reactivated, keeps an origin that stays active, and its origin chain only loses elements
(and keeps those that stay active, when it stays active); an added authority is a root or is
derived from an active authority within its footprint. -/
structure Skel (s s' : SC) : Prop where
  len : s.A.length ≤ s'.A.length
  old : ∀ j y', s'.A[j]? = some y' → j < s.A.length → ∃ y, s.A[j]? = some y ∧
    y'.footprint = y.footprint ∧ y'.mode = y.mode ∧ (y'.active = true → y.active = true) ∧
    (∀ o, y.origin = some o → s'.flat.Active o → y'.origin = some o)
  ancsSub : ∀ j, j < s.A.length → ∀ x ∈ s'.flat.ancs j, x ∈ s.flat.ancs j
  ancsKeep : ∀ j, j < s.A.length → s'.flat.Active j → ∀ x ∈ s.flat.ancs j, s'.flat.Active x →
    x ∈ s'.flat.ancs j
  new : ∀ j y', s'.A[j]? = some y' → s.A.length ≤ j → y'.origin = none ∨
    ∃ o, y'.origin = some o ∧ o < s.A.length ∧ s.flat.Active o ∧
      (∀ l ∈ y'.footprint, l ∈ s.flat.afp o) ∧ s'.flat.ancs j = o :: s.flat.ancs o

section SkelLemmas

variable {s s' : SC}

/-- An index below the length has an element (Spec 1 §38: identities are indices). -/
theorem getElem?_of_lt {α : Type} {l : List α} {i : Nat} (h : i < l.length) :
    ∃ x, l[i]? = some x :=
  ⟨l[i], List.getElem?_eq_getElem h⟩

/-- Footprint of an existing authority (Spec 1 §42). -/
theorem afp_of {t : SC} {j : Nat} {y : Authority} (h : t.A[j]? = some y) :
    t.flat.afp j = y.footprint := by
  show (match t.A[j]? with | some x => x.footprint | none => []) = _
  rw [h]

/-- An active authority exists (Spec 1 §42). -/
theorem active_lt {t : SC} {j : Nat} (h : t.flat.Active j) : j < t.A.length := by
  obtain ⟨y, hy, -⟩ := h; exact lt_of_getElem? hy

/-- Activity after a step implies activity before it (no reactivation). -/
theorem Skel.active (hsk : Skel s s') {x : Nat} (hx : x < s.A.length) (h : s'.flat.Active x) :
    s.flat.Active x := by
  obtain ⟨y', hy', ya'⟩ := h
  obtain ⟨y, hy, -, -, ha, -⟩ := hsk.old x y' hy' hx
  exact ⟨y, hy, ha ya'⟩

/-- Footprints of existing authorities are kept by a step (Spec 1 §42). -/
theorem Skel.afp (hsk : Skel s s') {x : Nat} (hx : x < s.A.length) :
    s'.flat.afp x = s.flat.afp x := by
  obtain ⟨y', hy'⟩ := getElem?_of_lt (Nat.lt_of_lt_of_le hx hsk.len)
  obtain ⟨y, hy, hf, -⟩ := hsk.old x y' hy' hx
  rw [afp_of hy', afp_of hy, hf]

/-- A covering descendant (C22) after a step was one before it. -/
theorem Skel.covering (hsk : Skel s s') {g j : Nat} (hg : g < s.A.length) (hj : j < s.A.length)
    (h : CoveringDesc s' g j) : CoveringDesc s g j := by
  obtain ⟨hanc, hact, l, hl1, hl2⟩ := h
  exact ⟨hsk.ancsSub j hj g hanc, hsk.active hj hact, l, by rwa [← hsk.afp hj],
    by rwa [← hsk.afp hg]⟩

/-- A covering descendant created by the step is derived either directly from `g` or from a
covering descendant of the state before (C22). -/
theorem Skel.covering_new (hsk : Skel s s') {g j : Nat} (hg : g < s.A.length)
    (hj : s.A.length ≤ j) (h : CoveringDesc s' g j) : ∃ y' o, s'.A[j]? = some y' ∧
      y'.origin = some o ∧ (g = o ∨ CoveringDesc s g o) ∧ s'.flat.ancs j = o :: s.flat.ancs o := by
  obtain ⟨hanc, ⟨y', hy', ya'⟩, l, hl1, hl2⟩ := h
  have hy'' : s'.A[j]? = some y' := hy'
  rcases hsk.new j y' hy'' hj with ho | ⟨o, ho, hoA, hoa, hfp, hanc'⟩
  · have : s'.flat.org j = none := by simp [S3.org, hy', ho]
    rw [S3.ancs, chain_none this] at hanc; simp at hanc
  · refine ⟨y', o, hy'', ho, ?_, hanc'⟩
    rw [hanc'] at hanc
    rcases List.mem_cons.1 hanc with rfl | hanc
    · exact .inl rfl
    · refine .inr ⟨hanc, hoa, l, hfp l (by rwa [afp_of hy''] at hl1), ?_⟩
      rwa [← hsk.afp hg]

end SkelLemmas

/-- One entry keeps its clauses across a step with an unchanged registry record (C21.1–C21.3,
C21.5, C21.6, C22). `hsrc`: no authority added by the step is derived directly from `guarded`
(from `RestrictedStep`); `hhold`: a place-held `guarded` stays place-held; `hctl`: the controller stays
a leaf; `hw'`: `WF3` after the step (theorem 2). -/
theorem entry_step {L : MutexLayout} {s s' : SC} {e : SyncEntry} (hsk : Skel s s')
    (hw' : WF3 s'.flat) (he : EntryOK L s e)
    (hsrc : e.Live s → ∀ j y' o, s'.A[j]? = some y' → s.A.length ≤ j → y'.origin = some o →
      o ≠ e.guarded)
    (hhold : e.Live s' → ∀ y y', s.A[e.guarded]? = some y → s'.A[e.guarded]? = some y' →
      PlaceUsable s.flat y.holder → ∃ q, y'.holder = .place q)
    (hctl : e.Live s' → ∀ ctl, ControlOf L s e = some ctl → isLeaf s.P ctl →
      ∃ ctl', ControlOf L s' e = some ctl' ∧ isLeaf s'.P ctl') : EntryOK L s' e := by
  have hb := he.bound
  have hlive : e.Live s' → e.Live s := hsk.active hb
  refine ⟨fun hl => ?_, fun hl g₀ hg₀ => ?_, fun hl => ?_, fun hl hn => ?_,
    fun hl g₀ hg₀ ha₀ => ?_, Nat.lt_of_lt_of_le hb hsk.len⟩
  · obtain ⟨y', hy', ya'⟩ := hl
    have hy'' : s'.A[e.guarded]? = some y' := hy'
    obtain ⟨y, hy, -, hm, -⟩ := hsk.old _ y' hy'' hb
    have h1 := he.guarded (hlive ⟨y', hy', ya'⟩)
    simp only [OptP, hy] at h1
    obtain ⟨q, hq⟩ := hhold ⟨y', hy', ya'⟩ y y' hy hy'' h1.2
    simp only [OptP, hy'']
    refine ⟨hm ▸ h1.1, ?_⟩
    have := hw'.holders _ y' hy' ya'
    rw [hq] at this ⊢; exact this
  · have h2 := he.grant (hlive hl) g₀ hg₀
    unfold OptP at h2; split at h2
    · rename_i z hz
      obtain ⟨z', hz'⟩ := getElem?_of_lt (Nat.lt_of_lt_of_le (lt_of_getElem? hz) hsk.len)
      obtain ⟨z₀, hz₀, hf, -, -, ho⟩ := hsk.old g₀ z' hz' (lt_of_getElem? hz)
      rw [hz] at hz₀; cases hz₀
      simp only [OptP, hz']
      refine ⟨ho _ h2.1 hl, fun l => ?_⟩
      rw [hf, hsk.afp hb]; exact h2.2 l
    · exact h2.elim
  · have h3 := he.control (hlive hl)
    unfold OptP at h3; split at h3
    · rename_i ctl hc
      obtain ⟨ctl', hc', hleaf'⟩ := hctl hl ctl hc h3.2
      simp only [OptP, hc']
      exact ⟨control_usable hw' hl hc', hleaf'⟩
    · exact h3.elim
  · intro j hj hcov
    by_cases hjA : j < s.A.length
    · exact he.disc (hlive hl) hn j (List.mem_range.2 hjA) (hsk.covering hb hjA hcov)
    · obtain ⟨y', o, hy', ho, hor, -⟩ := hsk.covering_new hb (Nat.le_of_not_lt hjA) hcov
      rcases hor with rfl | hcov'
      · exact hsrc (hlive hl) j y' _ hy' (Nat.le_of_not_lt hjA) ho rfl
      · exact he.disc (hlive hl) hn o (List.mem_range.2 (active_lt hcov'.2.1)) hcov'
  · intro j hcov
    have hg₀A : g₀ < s.A.length := by
      have h2 := he.grant (hlive hl) g₀ hg₀
      unfold OptP at h2; split at h2
      · exact lt_of_getElem? ‹_›
      · exact h2.elim
    have ha₀' := hsk.active hg₀A ha₀
    by_cases hjA : j < s.A.length
    · rcases he.sub (hlive hl) g₀ hg₀ ha₀' j (hsk.covering hb hjA hcov) with rfl | h
      · exact .inl rfl
      · exact .inr (hsk.ancsKeep j hjA hcov.2.1 g₀ h ha₀)
    · obtain ⟨y', o, hy', ho, hor, hanc⟩ := hsk.covering_new hb (Nat.le_of_not_lt hjA) hcov
      rcases hor with rfl | hcov'
      · exact absurd rfl (hsrc (hlive hl) j y' _ hy' (Nat.le_of_not_lt hjA) ho)
      · rw [hanc]
        rcases he.sub (hlive hl) g₀ hg₀ ha₀' o hcov' with rfl | h
        · exact .inr (List.mem_cons_self ..)
        · exact .inr (List.mem_cons_of_mem _ h)

/-- Uniqueness across a step with an unchanged registry (C21.4): liveness only decreases. -/
theorem uniq_step {s s' : SC} {reg : SyncReg} (hsk : Skel s s')
    (hb : ∀ e ∈ reg, e.guarded < s.A.length)
    (hu : Uniq s reg) : Uniq s' reg := fun i j e e' hi hj hl hl' hg =>
  hu i j e e' hi hj (hsk.active (hb e (List.mem_of_getElem? hi)) hl)
    (hsk.active (hb e' (List.mem_of_getElem? hj)) hl') hg

/-- A step with an unchanged registry preserves `SyncCore`, given the per-entry hypotheses of
`entry_step`. -/
theorem kernel_step {L : MutexLayout} {s s' : SC} {reg : SyncReg} (hsk : Skel s s')
    (hw' : WF3 s'.flat) (hst : SyncCore L s reg)
    (hsrc : ∀ e ∈ reg, e.Live s → ∀ j y' o, s'.A[j]? = some y' → s.A.length ≤ j →
      y'.origin = some o → o ≠ e.guarded)
    (hhold : ∀ e ∈ reg, e.Live s' → ∀ y y', s.A[e.guarded]? = some y →
      s'.A[e.guarded]? = some y' → PlaceUsable s.flat y.holder → ∃ q, y'.holder = .place q)
    (hctl : ∀ e ∈ reg, e.Live s' → ∀ ctl, ControlOf L s e = some ctl → isLeaf s.P ctl →
      ∃ ctl', ControlOf L s' e = some ctl' ∧ isLeaf s'.P ctl') : SyncCore L s' reg := by
  obtain ⟨he, hu⟩ := hst
  exact ⟨fun e hm => entry_step hsk hw' (he e hm) (hsrc e hm) (hhold e hm)
    (hctl e hm), uniq_step hsk (fun e hm => (he e hm).bound) hu⟩

/-! ## Holders and places -/

/-- A place-held authority keeps its holder (every step but `transfer`). -/
def HoldSame (s s' : SC) : Prop :=
  ∀ (j : Nat) (y y' : Authority) (q : Nat), s.A[j]? = some y → s'.A[j]? = some y' →
    y.holder = .place q → y'.holder = y.holder

/-- The structural parents of the existing places are kept and no new place has an existing
parent (Spec 1 §72.2, §71.1 `ShapeOK`; §63 keeps parents). -/
def PSkel (P P' : List Place) : Prop :=
  P.length ≤ P'.length ∧ (∀ q, q < P.length → parentOf P' q = parentOf P q) ∧
    ∀ r q, parentOf P' r = some q → q < P.length → r < P.length

/-- A filter rejecting every element is empty. -/
theorem filter_nil {α : Type} {p : α → Bool} : ∀ {l : List α}, (∀ a ∈ l, p a = false) →
    l.filter p = []
  | [], _ => rfl
  | a :: l, h => by
    rw [List.filter_cons, h a (List.mem_cons_self ..)]
    exact filter_nil fun b hb => h b (List.mem_cons_of_mem _ hb)

/-- Children of an existing place are kept (Spec 1 §63.2 `kids`). -/
theorem PSkel.kids {P P' : List Place} (h : PSkel P P') {m : Nat} (hm : m < P.length) :
    kids P' m = kids P m := by
  obtain ⟨d, hd⟩ : ∃ d, P'.length = P.length + d := ⟨P'.length - P.length, by have := h.1; omega⟩
  unfold Ern.MemoryModel.Access.kids
  rw [hd, List.range_add, List.filter_append]
  rw [filter_nil (l := List.map (fun x => P.length + x) (List.range d)) (fun r hr => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hr
    cases e : decide (parentOf P' (P.length + i) = some m)
    · rfl
    · have := h.2.2 _ m (of_decide_eq_true e) hm; omega), List.append_nil]
  exact List.filter_congr fun r hr => by rw [h.2.1 r (List.mem_range.1 hr)]

/-- Leaf-ness of an existing place is kept (Spec 1 §40). -/
theorem PSkel.isLeaf {P P' : List Place} (h : PSkel P P') {l : Nat} (hl : l < P.length) :
    isLeaf P' l ↔ isLeaf P l := by
  constructor
  · intro h' r hr hp
    exact h' r (Nat.lt_of_lt_of_le hr h.1) (by rw [h.2.1 r hr]; exact hp)
  · intro h' r hr hp
    have hrP := h.2.2 r l hp hl
    exact h' r hrP (by rw [← h.2.1 r hrP]; exact hp)

/-- Unchanged places satisfy `PSkel`. -/
theorem pskel_refl (P : List Place) : PSkel P P :=
  ⟨Nat.le_refl _, fun _ _ => rfl, fun r q hp _ => by
    simp only [parentOf] at hp
    cases hr : P[r]? with
    | none => rw [hr] at hp; cases hp
    | some _ => exact lt_of_getElem? hr⟩

/-- Appending a well-formed shape satisfies `PSkel` (Spec 1 §71.1, §72.2 `ShapeOK`). -/
theorem pskel_shapeP {P : List Place} {hd : Holder} {sh : List (Option Nat × Option Nat × Nat)}
    (hsh : ShapeOK P.length sh) : PSkel P (shapeP P hd sh) := by
  refine ⟨by simp [shapeP], fun q hq => ?_, fun r q hp hq => ?_⟩
  · simp only [parentOf, shapeP, List.getElem?_append_left hq]
  · refine (Nat.lt_or_ge r P.length).elim id fun hr' => absurd hq ?_
    simp only [parentOf, shapeP, List.getElem?_append_right hr', List.getElem?_map] at hp
    by_cases hi : r - P.length < sh.length
    · rw [List.getElem?_range hi] at hp
      simp only [Option.map_some, Option.bind_some] at hp
      have := (hsh (r - P.length) (List.mem_range.2 hi)).1
      rw [hp] at this
      exact Nat.not_lt.2 this.1
    · rw [List.getElem?_eq_none_iff.2 (by simp only [List.length_range]; omega)] at hp; cases hp

/-- Folding of the positional `ControlOf` (C12). -/
theorem controlOf_of {L : MutexLayout} {s : SC} {e : SyncEntry} {y : Authority} {hp m : Nat}
    (hy : s.A[e.guarded]? = some y) (hh : y.holder = .place hp) (hm : parentOf s.P hp = some m)
    (hk : (kids s.P m)[L.guardedField]? = some hp) :
    ControlOf L s e = (kids s.P m)[L.controlField]? := by
  simp [ControlOf, hy, hh, hm, hk]

/-- With the same holder for `guarded` and kept parents, the controller is unchanged and stays a
leaf (C12). -/
theorem ctl_same {L : MutexLayout} {s s' : SC} {e : SyncEntry} (hw : WF3 s.flat)
    (hP : PSkel s.P s'.P) (hb : e.guarded < s'.A.length) (hh : HoldSame s s') {ctl : Nat}
    (hc : ControlOf L s e = some ctl) (hl : isLeaf s.P ctl) :
    ∃ ctl', ControlOf L s' e = some ctl' ∧ isLeaf s'.P ctl' := by
  obtain ⟨y, hp, m, hy, hph, hm, hk, hkc⟩ := controlOf_spec hc
  obtain ⟨y', hy'⟩ := getElem?_of_lt hb
  have hhp : y'.holder = .place hp := by rw [hh _ y y' hp hy hy' hph, hph]
  have hpP : hp < s.P.length := by
    simp only [parentOf] at hm
    cases hq : s.P[hp]? with
    | none => rw [hq] at hm; cases hm
    | some _ => exact lt_of_getElem? hq
  have hmP : m < s.P.length := (WF3.parent_lt (s := s.flat) hw hm).2
  have hctlP : ctl < s.P.length := (mem_kids.1 (List.mem_of_getElem? hkc)).1
  have hm' : parentOf s'.P hp = some m := by rw [hP.2.1 hp hpP, hm]
  have hk' : (kids s'.P m)[L.guardedField]? = some hp := by rw [hP.kids hmP]; exact hk
  refine ⟨ctl, by rw [controlOf_of hy' hhp hm' hk', hP.kids hmP, hkc], (hP.isLeaf hctlP).2 hl⟩

/-- `kernel_step` for steps keeping holders of places and parents. -/
theorem kernel_step_same {L : MutexLayout} {s s' : SC} {reg : SyncReg} (hsk : Skel s s')
    (hh : HoldSame s s') (hP : PSkel s.P s'.P) (hw : WF3 s.flat) (hw' : WF3 s'.flat)
    (hst : SyncCore L s reg)
    (hsrc : ∀ e ∈ reg, e.Live s → ∀ j y' o, s'.A[j]? = some y' → s.A.length ≤ j →
      y'.origin = some o → o ≠ e.guarded) : SyncCore L s' reg :=
  kernel_step hsk hw' hst hsrc
    (fun e _ _ y y' hy hy' hu => by
      cases hq : y.holder with
      | frame f => rw [hq] at hu; exact hu.elim
      | place q => exact ⟨q, by rw [hh _ y y' q hy hy' hq, hq]⟩)
    (fun e hm _ ctl hc hl => ctl_same hw hP
      (Nat.lt_of_lt_of_le (hst.1 e hm).bound hsk.len) hh hc hl)

/-! ## Builders of `Skel` -/

/-- An old authority after a step that keeps its skeleton, never reactivates it, and keeps the
holder of a place-held one. -/
structure Same (y y' : Authority) : Prop where
  fp : y'.footprint = y.footprint
  mode : y'.mode = y.mode
  origin : y'.origin = y.origin
  active : y'.active = true → y.active = true
  holder : ∀ q, y.holder = .place q → y'.holder = y.holder

/-- `Same` is reflexive. -/
theorem Same.refl (y : Authority) : Same y y := ⟨rfl, rfl, rfl, id, fun _ _ => rfl⟩

/-- Steps that only change activity or frame holders (Spec 1 §62, §64–§70, §74, §75 effects). -/
theorem skel_map {s s' : SC} (hlen : s'.A.length = s.A.length)
    (h : ∀ (j : Nat) (y' : Authority), s'.A[j]? = some y' → ∃ y, s.A[j]? = some y ∧ Same y y') :
    Skel s s' ∧ HoldSame s s' := by
  have horg : ∀ i, s'.flat.org i = s.flat.org i := by
    intro i
    show (s'.A[i]?).bind (·.origin) = (s.A[i]?).bind (·.origin)
    cases hy' : s'.A[i]? with
    | none =>
      have := List.getElem?_eq_none_iff.1 hy'
      rw [List.getElem?_eq_none_iff.2 (by omega)]
    | some y' => obtain ⟨y, hy, hS⟩ := h i y' hy'; rw [hy]; exact hS.origin
  have hancs : ∀ j, s'.flat.ancs j = s.flat.ancs j := fun j => chain_congr fun i _ => horg i
  refine ⟨⟨by omega, fun j y' hy' _ => ?_, fun j _ x hx => by rwa [hancs] at hx,
    fun j _ _ x hx _ => by rwa [hancs], fun j y' hy' hj => ?_⟩, fun j y y' q hy hy' hq => ?_⟩
  · obtain ⟨y, hy, hS⟩ := h j y' hy'
    exact ⟨y, hy, hS.fp, hS.mode, hS.active, fun o ho _ => by rw [hS.origin, ho]⟩
  · have := lt_of_getElem? hy'; omega
  · obtain ⟨y₀, hy₀, hS⟩ := h j y' hy'
    rw [hy] at hy₀; cases hy₀; exact hS.holder q hq

/-- Steps that keep the old authorities (up to `Same`) and append roots or authorities derived
within an active one (Spec 1 §60, §61, §71, §72; C4, C15 effects). -/
theorem skel_append {s s' : SC} {B N : List Authority} (hA : s'.A = B ++ N)
    (hlen : B.length = s.A.length)
    (hB : ∀ (j : Nat) (y' : Authority), B[j]? = some y' → ∃ y, s.A[j]? = some y ∧ Same y y')
    (hN : ∀ z ∈ N, z.origin = none ∨ ∃ o, z.origin = some o ∧ o < s.A.length ∧
      s.flat.Active o ∧ ∀ l ∈ z.footprint, l ∈ s.flat.afp o) : Skel s s' ∧ HoldSame s s' := by
  have hold : ∀ j, j < s.A.length → s'.A[j]? = B[j]? := fun j hj => by
    rw [hA, List.getElem?_append_left (by omega)]
  have horg : ∀ i, i < s.A.length → s'.flat.org i = s.flat.org i := by
    intro i hi
    show (s'.A[i]?).bind (·.origin) = (s.A[i]?).bind (·.origin)
    rw [hold i hi]
    obtain ⟨y', hy'⟩ := getElem?_of_lt (show i < B.length by omega)
    obtain ⟨y, hy, hS⟩ := hB i y' hy'
    rw [hy', hy]; exact hS.origin
  have hancs : ∀ j, j < s.A.length → s'.flat.ancs j = s.flat.ancs j :=
    fun j hj => chain_congr fun i hi => horg i (by omega)
  have hlen' : s'.A.length = s.A.length + N.length := by rw [hA, List.length_append, hlen]
  refine ⟨⟨by omega, fun j y' hy' hj => ?_, fun j hj x hx => by rwa [hancs j hj] at hx,
    fun j hj _ x hx _ => by rwa [hancs j hj], fun j y' hy' hj => ?_⟩,
    fun j y y' q hy hy' hq => ?_⟩
  · rw [hold j hj] at hy'
    obtain ⟨y, hy, hS⟩ := hB j y' hy'
    exact ⟨y, hy, hS.fp, hS.mode, hS.active, fun o ho _ => by rw [hS.origin, ho]⟩
  · rw [hA, List.getElem?_append_right (by omega)] at hy'
    rcases hN y' (List.mem_of_getElem? hy') with ho | ⟨o, ho, hoA, hoa, hfp⟩
    · exact .inl ho
    · refine .inr ⟨o, ho, hoA, hoa, hfp, ?_⟩
      have horgj : s'.flat.org j = some o := by
        show (s'.A[j]?).bind (·.origin) = some o
        rw [hA, List.getElem?_append_right (by omega), hy']; exact ho
      rw [S3.ancs, chain_cons horgj (by omega)]
      exact congrArg _ (hancs o hoA)
  · have hj := lt_of_getElem? hy
    rw [hold j hj] at hy'
    obtain ⟨y₀, hy₀, hS⟩ := hB j y' hy'
    rw [hy] at hy₀; cases hy₀; exact hS.holder q hq

/-- After the exit, origin chains only lose elements (Spec 1 §73.4 effect). -/
theorem exit_ancs_sub {v : S3} (hw : ∀ i o, v.org i = some o → o < i) :
    ∀ n x, x < n → ∀ w ∈ (exitEff v).ancs x, w ∈ v.ancs x
  | 0, _, h, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, x, hx, w, hw' => by
    obtain ⟨o', ho', hlt', hw''⟩ := mem_chain hw'
    have e' : (exitEff v).org x = (v.A[x]?).bind fun y => (exitG v v.F.tail x y).origin := by
      show ((exitEff v).A[x]?).bind (·.origin) = _
      rw [Frames.exit_A_get]; cases v.A[x]? <;> rfl
    cases hy : v.A[x]? with
    | none => rw [e', hy] at ho'; cases ho'
    | some y =>
      rw [e', hy] at ho'
      simp only [Option.bind_some] at ho'
      have hsub : ∀ z, z ∈ v.ancs x → (w = z ∨ w ∈ (exitEff v).ancs z) → z < x → w ∈ v.ancs x := by
        intro z hz hwz hzx
        rcases hwz with rfl | hwz
        · exact hz
        · exact chain_trans hw (x + 1) x (Nat.lt_succ_self x) z hz w
            (exit_ancs_sub hw n z (by omega) w hwz)
      rcases Frames.exitG_origin (s := v) (F₀ := v.F.tail) (a := x) (y := y) with e | ⟨-, -, e⟩
      · rw [e] at ho'
        have horg : v.org x = some o' := by simp [S3.org, hy, ho']
        have hox := hw x o' horg
        exact hsub o' (by rw [S3.ancs, chain_cons horg hox]; exact List.mem_cons_self ..) hw'' hox
      · rw [e] at ho'
        have hz := (Frames.firstSurv_some ho').1
        exact hsub o' hz hw'' (chain_lt hz)

/-- `exitFrameC` and `terminate` (Spec 1 §73 effect on the view; C6, C7). -/
theorem skel_exit {s s' : SC} {c : Nat} (hw : WF3 s.flat) (hA : s'.A = (exitEff (s.view c)).A) :
    Skel s s' ∧ HoldSame s s' := by
  have hwv : ∀ i o, (s.view c).org i = some o → o < i :=
    fun i o h => Frames.org_lt (s := s.flat) hw h
  have hget : ∀ j, s'.A[j]? = (s.A[j]?).map (exitG (s.view c) (s.view c).F.tail j) := by
    intro j; rw [hA]; exact Frames.exit_A_get (s.view c) j
  have hancs : s'.flat.ancs = (exitEff (s.view c)).ancs := by
    funext j
    show chain s'.flat.org j = chain (exitEff (s.view c)).org j
    congr 1; funext i
    show (s'.A[i]?).bind (·.origin) = ((exitEff (s.view c)).A[i]?).bind (·.origin)
    rw [hA]
  have hact : ∀ o, s'.flat.Active o → Survives (s.view c) (s.view c).F.tail o := by
    rintro o ⟨z, hz, za⟩
    have hz' : s'.A[o]? = some z := hz
    rw [hget] at hz'
    obtain ⟨z₀, -, rfl⟩ := Option.map_eq_some_iff.1 hz'
    exact Frames.exitG_active za
  have hlen : s'.A.length = s.A.length := by
    rw [hA]; simp [exitEff, length_mapI]; rfl
  refine ⟨⟨by omega, fun j y' hy' _ => ?_, fun j hj x hx => ?_, fun j hj _ x hx hxa => ?_,
    fun j y' hy' hj => by have := lt_of_getElem? hy'; omega⟩, fun j y y' q hy hy' hq => ?_⟩
  · rw [hget] at hy'
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hy'
    obtain ⟨hm, hf, -⟩ := Frames.exitG_same (s.view c) (s.view c).F.tail j y
    refine ⟨y, hy, hf, hm, Frames.exitG_active' (s := s.view c) hy, fun o ho hoa => ?_⟩
    rcases Frames.exitG_origin (s := s.view c) (F₀ := (s.view c).F.tail) (a := j) (y := y)
      with e | ⟨-, -, e⟩
    · rw [e, ho]
    · rw [e]
      have hy2 : (s.view c).A[j]? = some y := hy
      have horg : (s.view c).org j = some o := by simp [S3.org, hy2, ho]
      have hlt := hwv j o horg
      rw [S3.ancs, chain_cons horg hlt]
      simp [firstSurv, hact o hoa]
  · rw [hancs] at hx; exact exit_ancs_sub hwv (j + 1) j (Nat.lt_succ_self j) x hx
  · rw [hancs]; exact Frames.exit_ancs_keep (j + 1) j (Nat.lt_succ_self j) x hx (hact x hxa)
  · rw [hget, hy] at hy'
    simp only [Option.map_some, Option.some.injEq] at hy'
    rw [← hy']; exact (Frames.exitG_same _ _ _ _).2.2

/-- `Same` is transitive. -/
theorem Same.trans {y y' y'' : Authority} (h : Same y y') (h' : Same y' y'') : Same y y'' where
  fp := h'.fp.trans h.fp
  mode := h'.mode.trans h.mode
  origin := h'.origin.trans h.origin
  active a := h.active (h'.active a)
  holder q hq := (h'.holder q ((h.holder q hq).trans hq)).trans (h.holder q hq)

/-- Deactivation is `Same` (Spec 1 §62, §69, §70, §73 effects). -/
theorem same_deact (y : Authority) : Same y { y with active := false } :=
  ⟨rfl, rfl, rfl, (fun h => by cases h), fun _ _ => rfl⟩

/-- A choice between two `Same` results is `Same`. -/
theorem same_ite {p : Prop} [Decidable p] {y a b : Authority} (ha : Same y a) (hb : Same y b) :
    Same y (if p then a else b) := by split <;> assumption

/-- Steps that keep the authorities (Spec 1 §64, §66–§68, §74, §75; C8). -/
theorem skel_sameA {s s' : SC} (hA : s'.A = s.A) : Skel s s' ∧ HoldSame s s' :=
  skel_map (by rw [hA]) fun _ y' hy' => ⟨y', by rw [← hA]; exact hy', Same.refl _⟩

/-- Steps that map every authority by a `Same` function (Spec 1 §69, §70 effects). -/
theorem skel_mapf {s s' : SC} {f : Authority → Authority} (hA : s'.A = s.A.map f)
    (hS : ∀ y, Same y (f y)) : Skel s s' ∧ HoldSame s s' :=
  skel_map (by rw [hA, List.length_map]) fun j y' hy' => by
    rw [hA, List.getElem?_map] at hy'
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hy'
    exact ⟨y, hy, hS y⟩

/-- Steps that update one authority by a `Same` change (Spec 1 §62, §65 effects). -/
theorem skel_set {s s' : SC} {a : Nat} {x x' : Authority} (hx : s.A[a]? = some x)
    (hA : s'.A = s.A.set a x') (hS : Same x x') : Skel s s' ∧ HoldSame s s' :=
  skel_map (by rw [hA, List.length_set]) fun j y' hy' => by
    rw [hA, List.getElem?_set] at hy'
    by_cases e : a = j
    · subst e; simp only [lt_of_getElem? hx, ↓reduceIte, Option.some.injEq] at hy'
      subst hy'; exact ⟨x, hx, hS⟩
    · simp only [e, ↓reduceIte] at hy'; exact ⟨y', hy', Same.refl _⟩

/-- `Skel`, holders, places and the encapsulated sources of new authorities after a step with an
unchanged registry. -/
structure StepFacts (reg : SyncReg) (s s' : SC) : Prop where
  skel : Skel s s'
  hold : HoldSame s s'
  pskel : PSkel s.P s'.P
  src : ∀ e ∈ reg, e.Live s → ∀ j y' o, s'.A[j]? = some y' → s.A.length ≤ j →
    y'.origin = some o → o ≠ e.guarded

/-- Constructor of `StepFacts`. -/
theorem StepFacts.of {reg : SyncReg} {s s' : SC} (h : Skel s s' ∧ HoldSame s s')
    (hP : PSkel s.P s'.P) (hsrc : ∀ e ∈ reg, e.Live s → ∀ j y' o, s'.A[j]? = some y' →
      s.A.length ≤ j → y'.origin = some o → o ≠ e.guarded) : StepFacts reg s s' :=
  ⟨h.1, h.2, hP, hsrc⟩

/-- No authority is created (source condition vacuous). -/
theorem src_none {reg : SyncReg} {s s' : SC} (hlen : s'.A.length = s.A.length) :
    ∀ e ∈ reg, e.Live s → ∀ j y' o, s'.A[j]? = some y' → s.A.length ≤ j →
      y'.origin = some o → o ≠ e.guarded :=
  fun _ _ _ _ _ _ hy' hj _ => absurd (lt_of_getElem? hy') (by omega)

/-- Appended authorities are roots or derived from `src` (source condition from `RestrictedStep`). -/
theorem src_append {reg : SyncReg} {s s' : SC} {N : List Authority} {src : Nat}
    (hA : s'.A = s.A ++ N) (hN : ∀ z ∈ N, z.origin = none ∨ z.origin = some src)
    (he : ∀ e ∈ reg, e.Live s → src ≠ e.guarded) :
    ∀ e ∈ reg, e.Live s → ∀ j y' o, s'.A[j]? = some y' → s.A.length ≤ j →
      y'.origin = some o → o ≠ e.guarded := by
  intro e hm hl j y' o hy' hj ho
  rw [hA, List.getElem?_append_right hj] at hy'
  rcases hN y' (List.mem_of_getElem? hy') with h | h
  · rw [ho] at h; cases h
  · rw [ho] at h; cases h; exact he e hm hl

/-- Appended authorities are roots (source condition vacuous). -/
theorem src_roots {reg : SyncReg} {s s' : SC} {B N : List Authority} (hA : s'.A = B ++ N)
    (hlen : B.length = s.A.length) (hN : ∀ z ∈ N, z.origin = none) :
    ∀ e ∈ reg, e.Live s → ∀ j y' o, s'.A[j]? = some y' → s.A.length ≤ j →
      y'.origin = some o → o ≠ e.guarded := by
  intro e _ _ j y' o hy' hj ho
  rw [hA, List.getElem?_append_right (by omega)] at hy'
  rw [hN y' (List.mem_of_getElem? hy')] at ho; cases ho

/-- An `ok` outcome of an operation run on a view (C2). -/
theorem viewStep_ok {R : S3 → Outcome3 S3 → Prop} {c : Nat} {s s' : SC}
    (h : ViewStep R c s (.ok s')) : ∃ t, R (s.view c) (.ok t) ∧ s' = s.set t := by
  obtain ⟨o₃, hR, ho⟩ := h
  cases o₃ with
  | ok t => cases ho; exact ⟨t, hR, rfl⟩
  | reject => cases ho
  | fail => cases ho

/-- Authorities appended by `enterFrame`/`spawn` (Spec 1 §72 effect): parameters change their
frame holder, root authorities of the locals have no origin. -/
theorem skel_enter {s s' : SC} {c : Nat} {ps : List Nat} {ls : LocalShape}
    (hA : s'.A = (enterEff (s.view c) ps ls).A)
    (hpar : ∀ a ∈ ps, OptP ((s.view c).A[a]?) (fun y => y.active = true ∧
      y.holder = .frame (s.view c).top ∧ y.origin ≠ none) False) :
    Skel s s' ∧ HoldSame s s' := by
  refine skel_append (B := mapI (fun j y => if j ∈ ps then
      { y with holder := .frame (s.view c).nF } else y) 0 s.A)
    (N := (rootIdx ls.toShape).map fun i =>
      (⟨.modify, none, footprint (enterP (s.view c) ls) ((s.view c).P.length + i),
        shapeOwner ls.toShape (.frame (s.view c).nF) i, true⟩ : Authority))
    (by rw [hA]; rfl) (length_mapI _ _ _) (fun j y' hy' => ?_) (fun z hz => ?_)
  · rw [getElem?_mapI] at hy'
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hy'
    refine ⟨y, hy, ⟨by split <;> rfl, by split <;> rfl, by split <;> rfl,
      by split <;> exact id, fun q hq => ?_⟩⟩
    split
    · rename_i hj
      have := hpar j (by simpa using hj)
      have hy2 : (s.view c).A[j]? = some y := hy
      simp only [OptP, hy2] at this
      rw [this.2.1] at hq; cases hq
    · rfl
  · obtain ⟨i, -, rfl⟩ := List.mem_map.1 hz; exact .inl rfl

/-- Steps of the inherited operations other than `transfer` (Spec 1 §60–§62, §64–§75 effects
re-indexed, C2, C6). -/
theorem opStep_facts {k : K} {L : MutexLayout} {reg : SyncReg} {ar : ArenaReg} {c : Nat}
    {op : KernelOp} {s s' : SC} (h : opStepC k op c s (.ok s'))
    (he : RestrictedStep L (s, reg, ar) (.kernel c op))
    (hnt : ∀ src dst, op ≠ .transfer src dst) (hw : WF3 s.flat) : StepFacts reg s s' := by
  cases op with
  | transfer src dst => exact absurd rfl (hnt src dst)
  | depend q x =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
    exact .of (skel_sameA rfl) (pskel_refl _) (src_none rfl)
  | store a p =>
    obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
    have hd := hpre.derivedHeld
    unfold OptP at hd; split at hd
    · rename_i y hy
      have hy' : s.A[a]? = some y := hy
      have hA : (storeEffC s c a p).A = s.A.set a { y with holder := .place p } := by
        show (storeEff (s.view c) a p).A = _; simp [storeEff, hy]; rfl
      have hP : (storeEffC s c a p).P = s.P := by
        show (storeEff (s.view c) a p).P = _; simp [storeEff, hy]; rfl
      refine .of (skel_set hy' hA ⟨rfl, rfl, rfl, id, fun q hq => ?_⟩)
        (by rw [hP]; exact pskel_refl _) (src_none (by rw [hA, List.length_set]))
      rw [hd.2.2] at hq; cases hq
    · exact hd.elim
  | enter ps ls =>
    obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
    exact .of (skel_enter rfl hpre.params) (pskel_shapeP hpre.localsOK)
      (src_roots rfl (length_mapI _ _ _) fun z hz => by
        obtain ⟨i, -, rfl⟩ := List.mem_map.1 hz; rfl)
  | exit =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
    exact .of (skel_exit hw rfl) (pskel_refl _) (src_none (by
      show (exitEff (s.view c)).A.length = _; simp [exitEff, length_mapI]; rfl))
  | derive src region m =>
    obtain ⟨t, hR, rfl⟩ := viewStep_ok h
    obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 hR
    have hA : (s.set (deriveEff (s.view c) src region m)).A =
        s.A ++ [⟨m, some src, region, .frame (s.view c).top, true⟩] := rfl
    refine .of (skel_append hA rfl (fun j y' hy' => ⟨y', hy', Same.refl _⟩) fun z hz => ?_)
      (pskel_refl _) (src_append hA (fun z hz => by
        rw [List.mem_singleton] at hz; subst hz; exact .inr rfl) he)
    rw [List.mem_singleton] at hz; subst hz
    exact .inr ⟨src, rfl, active_lt hpre.active, hpre.active, hpre.within⟩
  | split src rs =>
    obtain ⟨t, hR, rfl⟩ := viewStep_ok h
    obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 hR
    have hA : (s.set (splitEff (s.view c) src rs)).A =
        s.A ++ rs.map fun r => ⟨.modify, some src, r, .frame (s.view c).top, true⟩ := rfl
    refine .of (skel_append hA rfl (fun j y' hy' => ⟨y', hy', Same.refl _⟩) fun z hz => ?_)
      (pskel_refl _) (src_append hA (fun z hz => by
        obtain ⟨r, -, rfl⟩ := List.mem_map.1 hz; exact .inr rfl) he)
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hz
    exact .inr ⟨src, rfl, active_lt hpre.active, hpre.active, fun p hp => (hpre.within r hr p hp).1⟩
  | release a =>
    obtain ⟨t, hR, rfl⟩ := viewStep_ok h
    obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 hR
    obtain ⟨x, hx, -⟩ := hpre.active
    have hx' : s.A[a]? = some x := hx
    have hA : (s.set (releaseEff (s.view c) a)).A = s.A.set a { x with active := false } := by
      show (releaseEff (s.view c) a).A = _; rw [releaseEff_eq hx]; rfl
    have hP : (s.set (releaseEff (s.view c) a)).P = s.P := by
      show (releaseEff (s.view c) a).P = _; rw [releaseEff_eq hx]; rfl
    exact .of (skel_set hx' hA (same_deact x)) (by rw [hP]; exact pskel_refl _)
      (src_none (by rw [hA, List.length_set]))
  | read => obtain ⟨t, hR, rfl⟩ := viewStep_ok h; obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hR
            exact .of (skel_sameA rfl) (pskel_refl _) (src_none rfl)
  | write => obtain ⟨t, hR, rfl⟩ := viewStep_ok h; obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hR
             exact .of (skel_sameA rfl) (pskel_refl _) (src_none rfl)
  | writeShared => obtain ⟨t, hR, rfl⟩ := viewStep_ok h; obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hR
                   exact .of (skel_sameA rfl) (pskel_refl _) (src_none rfl)
  | pin => obtain ⟨t, hR, rfl⟩ := viewStep_ok h; obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hR
           exact .of (skel_sameA rfl) (pskel_refl _) (src_none rfl)
  | unpin => obtain ⟨t, hR, rfl⟩ := viewStep_ok h; obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hR
             exact .of (skel_sameA rfl) (pskel_refl _) (src_none rfl)
  | endUse p =>
    obtain ⟨t, hR, rfl⟩ := viewStep_ok h; obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hR
    have hA : (s.set (endUseEff (s.view c) p)).A = s.A.map ((fun y =>
        if HolderLive (endUseS (s.view c) p) y.holder then y else { y with active := false }) ∘
        fun y => if heldIn s.P p y.holder then { y with active := false } else y) := by
      show (cleanup (endUseS (s.view c) p)).A = _
      simp only [cleanup, endUseS, List.map_map]; rfl
    exact .of (skel_mapf hA fun y => (same_ite (same_deact y) (Same.refl y)).trans
        (same_ite (Same.refl _) (same_deact _)))
      (pskel_refl _) (src_none (by rw [hA, List.length_map]))
  | free p auth =>
    obtain ⟨t, hR, rfl⟩ := viewStep_ok h; obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hR
    have hA : (s.set (freeEff (s.view c) p)).A = s.A.map ((fun y =>
        if HolderLive (freeS (s.view c) p) y.holder then y else { y with active := false }) ∘
        fun y => if (∃ l ∈ y.footprint, FreedPlace s.P p l) ∨ heldIn s.P p y.holder then
          { y with active := false } else y) := by
      show (cleanup (freeS (s.view c) p)).A = _
      simp only [cleanup, freeS, List.map_map]; rfl
    exact .of (skel_mapf hA fun y => (same_ite (same_deact y) (Same.refl y)).trans
        (same_ite (Same.refl _) (same_deact _)))
      (pskel_refl _) (src_none (by rw [hA, List.length_map]))
  | alloc pr ow ls =>
    obtain ⟨t, hR, rfl⟩ := viewStep_ok h
    cases hR with
    | ok hst _ =>
      have hA : (s.set (allocEff (s.view c) ow ls)).A = s.A ++ (rootIdx ls.toShape).map fun i =>
          (⟨.modify, none, footprint (allocP (s.view c) ow ls) ((s.view c).P.length + i),
            shapeOwner ls.toShape (.place ow) i, true⟩ : Authority) := rfl
      exact .of (skel_append hA rfl (fun j y' hy' => ⟨y', hy', Same.refl _⟩) fun z hz => by
          obtain ⟨i, -, rfl⟩ := List.mem_map.1 hz; exact .inl rfl)
        (pskel_shapeP hst.shapeOK)
        (src_roots hA rfl fun z hz => by obtain ⟨i, -, rfl⟩ := List.mem_map.1 hz; rfl)

/-! ## `transfer` (Spec 1 §63 re-indexed): positional controller -/

/-- Position in a strictly increasing list (Spec 1 §63.2 `posIn`). -/
theorem posIn_of_getElem : ∀ {l : List Nat} {i x : Nat}, l.Pairwise (· < ·) → l[i]? = some x →
    posIn x l = i
  | [], _, _, _, h => by simp at h
  | a :: l, 0, x, _, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h; simp [posIn]
  | a :: l, i + 1, x, hp, h => by
    simp only [List.getElem?_cons_succ] at h
    have hax : a ≠ x := Nat.ne_of_lt ((List.pairwise_cons.1 hp).1 x (List.mem_of_getElem? h))
    simp only [posIn, hax, ↓reduceIte, posIn_of_getElem (List.pairwise_cons.1 hp).2 h]

/-- Children are listed in increasing order (Spec 1 §63.2 `kids`). -/
theorem kids_pairwise (P : List Place) (m : Nat) : (kids P m).Pairwise (· < ·) :=
  (Frames.range_pairwise_lt _).filter _

/-- A child of a part of `src` is a part of `src` (Spec 1 §40). -/
theorem partOf_child {P : List Place} {r m src : Nat} (hr : r < P.length)
    (hm : parentOf P r = some m) (hlt : m < r) (h : partOf P m src) : partOf P r src := by
  refine ⟨hr, .inr ?_⟩
  rw [chain_cons hm hlt]
  rcases h.2 with rfl | h
  · exact List.mem_cons_self ..
  · exact List.mem_cons_of_mem _ h

/-- `transfer` keeps children (Spec 1 §63 effect). -/
theorem transfer_kids (t : S3) (src dst m : Nat) :
    kids (transferEff t src dst).P m = kids t.P m := by
  unfold Ern.MemoryModel.Access.kids; rw [transfer_len, transfer_parentOf]

/-- `transfer` keeps leaves (Spec 1 §63 effect). -/
theorem transfer_isLeaf (t : S3) (src dst l : Nat) :
    isLeaf (transferEff t src dst).P l ↔ isLeaf t.P l := by
  unfold isLeaf; rw [transfer_len, transfer_parentOf]

/-- The controller after a `transfer` whose source is not the place holding `guarded` (`RestrictedStep`):
either the mutex value does not move, or it moves as a whole and both fields move to the same
positions of the destination (Spec 1 §63.2 `corr`, C12 positional `ControlOf`). -/
theorem ctl_transfer {L : MutexLayout} {s : SC} {c src dst : Nat} {e : SyncEntry}
    (hw : WF3 s.flat) (hss : SameShape s.P src dst)
    (henc : (s.A[e.guarded]?).map (·.holder) ≠ some (.place src)) {ctl : Nat}
    (hc : ControlOf L s e = some ctl) (hl : isLeaf s.P ctl) :
    ∃ ctl', ControlOf L (s.set (transferEff (s.view c) src dst)) e = some ctl' ∧
      isLeaf (s.set (transferEff (s.view c) src dst)).P ctl' := by
  obtain ⟨y, hp, m, hy, hph, hm, hk, hkc⟩ := controlOf_spec hc
  have hP : (s.set (transferEff (s.view c) src dst)).P = (transferEff (s.view c) src dst).P := rfl
  have hpar : parentOf (s.set (transferEff (s.view c) src dst)).P = parentOf s.P :=
    transfer_parentOf (s.view c) src dst
  have hkids : ∀ x, kids (s.set (transferEff (s.view c) src dst)).P x = kids s.P x :=
    transfer_kids (s.view c) src dst
  have hleaf : ∀ x, isLeaf (s.set (transferEff (s.view c) src dst)).P x ↔ isLeaf s.P x :=
    transfer_isLeaf (s.view c) src dst
  have hA' : (s.set (transferEff (s.view c) src dst)).A[e.guarded]? = some
      (if heldIn s.P src y.holder then { y with holder := mvTo s.P src dst y.holder } else y) := by
    have hy2 : (s.view c).A[e.guarded]? = some y := hy
    show (transferEff (s.view c) src dst).A[e.guarded]? = _
    rw [transfer_A_get, hy2]; rfl
  have hmlt := WF3.parent_lt (s := s.flat) hw hm
  have hcm : parentOf s.P ctl = some m := (mem_kids.1 (List.mem_of_getElem? hkc)).2
  have hcP : ctl < s.P.length := (mem_kids.1 (List.mem_of_getElem? hkc)).1
  have hmc := (WF3.parent_lt (s := s.flat) hw hcm).1
  by_cases hin : heldIn s.P src y.holder
  · rw [hph] at hin
    -- the mutex value is a part of `src`
    have hne : hp ≠ src := fun e' => henc (by simp [hy, hph, e'])
    obtain ⟨o, ho, -, hor⟩ := mem_chain (hin.2.resolve_left hne)
    rw [hm] at ho; cases ho
    have hmsrc : partOf s.P m src := ⟨hmlt.2, hor.elim (fun e => .inl e.symm) .inr⟩
    have hcsrc : partOf s.P ctl src := partOf_child hcP hcm hmc hmsrc
    have hss1 := hss.1 m (List.mem_range.2 hmlt.2) hmsrc
    unfold OptP at hss1; split at hss1
    · rename_i m' hm'
      have hgp : posIn hp (kids s.P m) = L.guardedField := posIn_of_getElem (kids_pairwise _ _) hk
      have hcp : posIn ctl (kids s.P m) = L.controlField :=
        posIn_of_getElem (kids_pairwise _ _) hkc
      have hlen : L.controlField < (kids s.P m').length := by
        rw [hss1]; exact lt_of_getElem? hkc
      have hlen' : L.guardedField < (kids s.P m').length := by
        rw [hss1]; exact lt_of_getElem? hk
      obtain ⟨h', hh'⟩ := getElem?_of_lt hlen'
      obtain ⟨ctl', hc'⟩ := getElem?_of_lt hlen
      have hcorr : corr s.P src dst hp = some h' := by
        rw [corr_step hne hm hmlt.1, hm', Option.bind_some, hgp, hh']
      have hcne : ctl ≠ src := fun e' => by
        have := Frames.partOf_le hmsrc; omega
      have hcorrc : corr s.P src dst ctl = some ctl' := by
        rw [corr_step hcne hcm hmc, hm', Option.bind_some, hcp, hc']
      have hh'm : parentOf s.P h' = some m' := (mem_kids.1 (List.mem_of_getElem? hh')).2
      refine ⟨ctl', ?_, ?_⟩
      · rw [controlOf_of (y := { y with holder := mvTo s.P src dst y.holder }) (hp := h') (m := m')
          (by rw [hA']; simp only [show heldIn s.P src y.holder by rw [hph]; exact hin,
            ↓reduceIte])
          (by rw [hph]; simp [mvTo, hcorr])
          (by rw [hpar]; exact hh'm) (by rw [hkids]; exact hh'), hkids, hc']
      · rw [hleaf]
        have hsc := hss.1 ctl (List.mem_range.2 hcP) hcsrc
        rw [hcorrc] at hsc
        simp only [OptP] at hsc
        rw [kids_nil_iff.2 hl] at hsc
        exact kids_nil_iff.1 (List.eq_nil_of_length_eq_zero hsc)
    · exact hss1.elim
  · refine ⟨ctl, ?_, (hleaf ctl).2 hl⟩
    rw [controlOf_of (y := y) (hp := hp) (m := m) (by rw [hA']; simp only [hin, ↓reduceIte]) hph
      (by rw [hpar]; exact hm) (by rw [hkids]; exact hk), hkids, hkc]

/-- The effect of `transfer` executed by `c` (Spec 1 §63 effect re-indexed) preserves `SyncCore`
when the shapes match (§63.2) and the source is not the place holding the `guarded` of a live
entry (implied by C22.3, `holder_ne_of_excl`). -/
theorem transfer_core {L : MutexLayout} {reg : SyncReg} {c src dst : Nat} {s : SC}
    (hss : SameShape s.P src dst)
    (he : ∀ e ∈ reg, e.Live s → (s.A[e.guarded]?).map (·.holder) ≠ some (.place src))
    (hw : WF3 s.flat) (hw' : WF3 (transferEffC s c src dst).flat) (hs : SyncCore L s reg) :
    SyncCore L (transferEffC s c src dst) reg := by
  have hget : ∀ j : Nat, (transferEffC s c src dst).A[j]? = (s.A[j]?).map fun (y : Authority) =>
      if heldIn s.P src y.holder then { y with holder := mvTo s.P src dst y.holder } else y :=
    fun j => transfer_A_get (s.view c) src dst j
  have hlen : (transferEffC s c src dst).A.length = s.A.length := by
    show (transferEff (s.view c) src dst).A.length = _; simp [transferEff]; rfl
  have hsk : Skel s (transferEffC s c src dst) := by
    have horg : ∀ i, (transferEffC s c src dst).flat.org i = s.flat.org i := by
      intro i
      show ((transferEffC s c src dst).A[i]?).bind (·.origin) = (s.A[i]?).bind (·.origin)
      rw [hget]; cases s.A[i]? with
      | none => rfl
      | some y => simp only [Option.map_some, Option.bind_some]; split <;> rfl
    have hancs : ∀ j, (transferEffC s c src dst).flat.ancs j = s.flat.ancs j :=
      fun j => chain_congr fun i _ => horg i
    refine ⟨by omega, fun j y' hy' _ => ?_, fun j _ x hx => by rwa [hancs] at hx,
      fun j _ _ x hx _ => by rwa [hancs], fun j y' hy' hj => by
        have := lt_of_getElem? hy'; omega⟩
    rw [hget] at hy'
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hy'
    refine ⟨y, hy, by split <;> rfl, by split <;> rfl, by split <;> exact id, fun o ho _ => ?_⟩
    split <;> exact ho
  refine kernel_step hsk hw' hs (src_none hlen) (fun e _ _ y y' hy hy' hu => ?_)
    (fun e hm hl ctl hc hleaf => ctl_transfer hw hss
      (he e hm (hsk.active (hs.1 e hm).bound hl)) hc hleaf)
  rw [hget, hy] at hy'
  simp only [Option.map_some, Option.some.injEq] at hy'
  subst hy'
  cases hq : y.holder with
  | frame f => rw [hq] at hu; exact hu.elim
  | place q => split <;> simp [hq, mvTo]

/-- C22.3 excludes the place holding the `guarded` of a live entry as a source (its first
item), given that this place exists (C21.1). -/
theorem holder_ne_of_excl {L : MutexLayout} {reg : SyncReg} {s : SC} {src : Nat}
    (hx : TransferExcl L (s, reg) src) (hs : SyncCore L s reg) :
    ∀ e ∈ reg, e.Live s → (s.A[e.guarded]?).map (·.holder) ≠ some (.place src) := by
  intro e he hl hh
  have h1 := (hs.1 e he).guarded hl
  have h2 := (hx e he hl).1
  cases hy : s.A[e.guarded]? with
  | none => rw [hy] at h1; exact h1
  | some y =>
    rw [hy] at h1 hh
    simp only [Option.map_some, Option.some.injEq] at hh
    have hsl : slotOf s e.guarded = some src := by simp [slotOf, hy, hh]
    rw [hsl] at h2
    have hu : s.flat.Usable src := by have := h1.2; rw [hh] at this; exact this
    exact h2 ⟨hu.lt, .inl rfl⟩

/-! ## Frame steps (C4, C7, C8) -/

/-- Facts of a `spawn` step (C4 effect, Spec 1 §72 effect). -/
theorem spawn_facts {reg : SyncReg} {s s' : SC} {c : Nat} {ps : List Nat} {ls : LocalShape}
    (h : SpawnStep s c ps ls (.ok s')) : StepFacts reg s s' := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  exact .of (skel_enter rfl hpre.params) (pskel_shapeP hpre.localsOK)
    (src_roots rfl (length_mapI _ _ _) fun z hz => by obtain ⟨i, -, rfl⟩ := List.mem_map.1 hz; rfl)

/-- Facts of a `terminate` step (C7 effect, Spec 1 §73 effect). -/
theorem term_facts {k : K} {reg : SyncReg} {s s' : SC} {c : Nat} (hw : WF3 s.flat)
    (h : TermStep k s c (.ok s')) : StepFacts reg s s' := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
  exact .of (skel_exit hw rfl) (pskel_refl _) (src_none (by
    show (exitEff (s.view c)).A.length = _; simp [exitEff, length_mapI]; rfl))

/-- Facts of a `join` step (C8: state unchanged). -/
theorem join_facts {reg : SyncReg} {s s' : SC} {c d : Nat} (h : JoinStep s c d (.ok s')) :
    StepFacts reg s s' := by
  cases h; exact .of (skel_sameA rfl) (pskel_refl _) (src_none rfl)

/-! ## Library operations (C13, C16–C18) -/

/-- The clauses of an entry that do not read its grant, across a step (C21.1, C21.3). -/
theorem entry_static {L : MutexLayout} {s s' : SC} {e : SyncEntry} (hsk : Skel s s')
    (hh : HoldSame s s') (hP : PSkel s.P s'.P) (hw : WF3 s.flat) (hw' : WF3 s'.flat)
    (he : EntryOK L s e) (gr : Option Nat) :
    ((⟨e.guarded, gr⟩ : SyncEntry).Live s' → OptP (s'.A[e.guarded]?) (fun y =>
      y.mode = .modify ∧ PlaceUsable s'.flat y.holder) False) ∧
    ((⟨e.guarded, gr⟩ : SyncEntry).Live s' → OptP (ControlOf L s' ⟨e.guarded, gr⟩) (fun ctl =>
      s'.flat.Usable ctl ∧ isLeaf s'.P ctl) False) := by
  have hb := he.bound
  have hlive : (⟨e.guarded, gr⟩ : SyncEntry).Live s' → e.Live s := hsk.active hb
  refine ⟨fun hl => ?_, fun hl => ?_⟩
  · obtain ⟨y', hy', ya'⟩ := hl
    have hy'' : s'.A[e.guarded]? = some y' := hy'
    obtain ⟨y, hy, -, hm, -⟩ := hsk.old _ y' hy'' hb
    have h1 := he.guarded (hlive ⟨y', hy', ya'⟩)
    simp only [OptP, hy] at h1
    cases hq : y.holder with
    | frame f => rw [hq] at h1; exact h1.2.elim
    | place q =>
      simp only [OptP, hy'']
      refine ⟨hm ▸ h1.1, ?_⟩
      have := hw'.holders _ y' hy' ya'
      rw [hh _ y y' q hy hy'' hq, hq] at this ⊢; exact this
  · have h3 := he.control (hlive hl)
    unfold OptP at h3; split at h3
    · rename_i ctl hc
      obtain ⟨ctl', hc', hleaf'⟩ := ctl_same hw hP (Nat.lt_of_lt_of_le hb hsk.len) hh hc h3.2
      have hc'' : ControlOf L s' ⟨e.guarded, gr⟩ = some ctl' := hc'
      simp only [OptP, hc'']
      exact ⟨control_usable hw' hl hc'', hleaf'⟩
    · exact h3.elim

/-- A place-held `guarded` stays place-held under `HoldSame` (C21.1). -/
theorem hold_of_same {s s' : SC} (hh : HoldSame s s') (e : SyncEntry) : e.Live s' →
    ∀ y y', s.A[e.guarded]? = some y → s'.A[e.guarded]? = some y' →
      PlaceUsable s.flat y.holder → ∃ q, y'.holder = .place q := by
  intro _ y y' hy hy' hu
  cases hq : y.holder with
  | frame f => rw [hq] at hu; exact hu.elim
  | place q => exact ⟨q, by rw [hh _ y y' q hy hy' hq, hq]⟩

/-! ### Registry updates -/

/-- Members of an updated registry (C16–C18 record updates). -/
theorem mem_set_cases {reg : SyncReg} {i : Nat} {e' x : SyncEntry} (h : x ∈ reg.set i e') :
    x = e' ∨ ∃ j, reg[j]? = some x ∧ j ≠ i := by
  obtain ⟨j, hj⟩ := Frames.exists_getElem?_of_mem h
  rw [List.getElem?_set] at hj
  by_cases e : i = j
  · subst e
    by_cases hi : i < reg.length
    · simp only [hi, ↓reduceIte, Option.some.injEq] at hj; exact .inl hj.symm
    · simp [hi] at hj
  · simp only [e, ↓reduceIte] at hj; exact .inr ⟨j, hj, Ne.symm e⟩

/-- An entry of an updated registry has a counterpart with the same `guarded`. -/
theorem set_old {reg : SyncReg} {i j : Nat} {e e' x : SyncEntry} (hi : reg[i]? = some e)
    (hg : e'.guarded = e.guarded) (h : (reg.set i e')[j]? = some x) :
    ∃ x₀, reg[j]? = some x₀ ∧ x₀.guarded = x.guarded := by
  rw [List.getElem?_set] at h
  by_cases e₀ : i = j
  · subst e₀
    simp only [lt_of_getElem? hi, ↓reduceIte, Option.some.injEq] at h
    subst h; exact ⟨e, hi, hg.symm⟩
  · simp only [e₀, ↓reduceIte] at h; exact ⟨x, h, rfl⟩

/-- Uniqueness after a record update keeping `guarded` (C21.4). -/
theorem uniq_set {s : SC} {reg : SyncReg} {i : Nat} {e e' : SyncEntry} (hi : reg[i]? = some e)
    (hg : e'.guarded = e.guarded) (hu : Uniq s reg) : Uniq s (reg.set i e') := by
  intro j₁ j₂ x₁ x₂ h₁ h₂ hl₁ hl₂ hgg
  obtain ⟨y₁, hy₁, hg₁⟩ := set_old hi hg h₁
  obtain ⟨y₂, hy₂, hg₂⟩ := set_old hi hg h₂
  exact hu j₁ j₂ y₁ y₂ hy₁ hy₂ (by unfold SyncEntry.Live; rw [hg₁]; exact hl₁)
    (by unfold SyncEntry.Live; rw [hg₂]; exact hl₂) (by rw [hg₁, hg₂, hgg])

/-- Entries of an extended registry (C13). -/
theorem append_cases {reg : SyncReg} {e' x : SyncEntry} {j : Nat} (h : (reg ++ [e'])[j]? = some x) :
    (reg[j]? = some x) ∨ (j = reg.length ∧ x = e') := by
  by_cases hj : j < reg.length
  · rw [List.getElem?_append_left hj] at h; exact .inl h
  · rw [List.getElem?_append_right (Nat.le_of_not_lt hj)] at h
    cases e : j - reg.length with
    | zero => rw [e] at h; simp only [List.getElem?_cons_zero, Option.some.injEq] at h
              exact .inr ⟨by omega, h.symm⟩
    | succ n => rw [e] at h; simp at h

/-- Uniqueness after registering a fresh identity (C13.7, C21.4). -/
theorem uniq_append {s : SC} {reg : SyncReg} {e' : SyncEntry} (hu : Uniq s reg)
    (hfresh : ∀ x ∈ reg, x.Live s → x.guarded ≠ e'.guarded) : Uniq s (reg ++ [e']) := by
  intro j₁ j₂ x₁ x₂ h₁ h₂ hl₁ hl₂ hgg
  rcases append_cases h₁ with h₁' | ⟨rfl, rfl⟩ <;> rcases append_cases h₂ with h₂' | ⟨rfl, rfl⟩
  · exact hu _ _ _ _ h₁' h₂' hl₁ hl₂ hgg
  · exact absurd hgg (hfresh x₁ (List.mem_of_getElem? h₁') hl₁)
  · exact absurd hgg.symm (hfresh x₂ (List.mem_of_getElem? h₂') hl₂)
  · rfl

/-! ### `newMutex`, `acquire`, `unlock`, `resetLock` -/

/-- `newMutex` (C13) preserves `SyncCore`. -/
theorem newMutex_preserves {k : K} {L : MutexLayout} {ar : ArenaReg} {s : SC} {reg : SyncReg}
    {c g : Nat} {st' : SC × SyncReg} (h : NewMutexOk k L ar s reg c g st')
    (hs : SyncCore L s reg) : SyncCore L st'.1 st'.2 := by
  obtain ⟨hpre, rfl⟩ := h
  obtain ⟨hes, hu⟩ := hs
  have hg := hpre.guarded
  unfold OptP at hg; split at hg
  · rename_i y hy
    have hnew : EntryOK L s ⟨g, none⟩ := by
      refine ⟨fun _ => by simp only [OptP, hy]; exact ⟨hg.2.1, hg.2.2⟩,
        (fun _ _ h => by cases h), fun hl => ?_, fun _ _ => hpre.available,
        (fun _ _ h => by cases h), lt_of_getElem? hy⟩
      have hctl := hpre.control
      cases hc : ControlOf L s ⟨g, none⟩ with
      | none => rw [hc] at hctl; exact hctl.elim
      | some ctl => rw [hc] at hctl; exact hctl
    refine ⟨fun x hx => ?_, uniq_append hu fun x hx hl => hpre.unique x hx hl⟩
    rcases List.mem_append.1 hx with hx | hx
    · exact hes x hx
    · rw [List.mem_singleton.1 hx]; exact hnew
  · exact hg.elim

/-- `acquire` (C16) preserves `SyncCore`. -/
theorem acquire_preserves {ks : KShared} {L : MutexLayout} {s : SC} {reg : SyncReg} {c i : Nat}
    {st' : SC × SyncReg} (h : AcquireOk ks L s reg c i st') (hw : WF3 s.flat)
    (hw' : WF3 st'.1.flat) (hs : SyncCore L s reg) : SyncCore L st'.1 st'.2 := by
  obtain ⟨e, hi, ⟨hl, hn, -⟩, hpre, rfl⟩ := h
  obtain ⟨hes, hu⟩ := hs
  have heo := hes e (List.mem_of_getElem? hi)
  have hA : (deriveSyncEff s c e.guarded).A = s.A ++ [⟨.modify, some e.guarded,
      (s.view c).afp e.guarded, .frame (s.view c).top, true⟩] := rfl
  obtain ⟨hsk, hh⟩ := skel_append hA rfl (fun j y' hy' => ⟨y', hy', Same.refl _⟩) fun z hz => by
    rw [List.mem_singleton] at hz; subst hz
    exact .inr ⟨e.guarded, rfl, active_lt hpre.active, hpre.active, fun l hl => hl⟩
  have hP : PSkel s.P (deriveSyncEff s c e.guarded).P := pskel_refl _
  refine ⟨fun x hx => ?_,
    uniq_set hi rfl (uniq_step hsk (fun x hx => (hes x hx).bound) hu)⟩
  rcases mem_set_cases hx with rfl | ⟨j, hj, hji⟩
  · obtain ⟨hg1, hc1⟩ := entry_static hsk hh hP hw hw' heo (some s.A.length)
    refine ⟨hg1, fun _ g₀ hg₀ => ?_, hc1, (fun _ h => by cases h), fun _ g₀ hg₀ _ j hcov => ?_,
      Nat.lt_of_lt_of_le heo.bound hsk.len⟩
    · cases hg₀
      have hnew : (deriveSyncEff s c e.guarded).A[s.A.length]? = some
          ⟨.modify, some e.guarded, (s.view c).afp e.guarded, .frame (s.view c).top, true⟩ := by
        rw [hA, List.getElem?_append_right (Nat.le_refl _)]; simp
      simp only [OptP, hnew]
      refine ⟨by first | rfl | trivial, fun l => ?_⟩
      show l ∈ s.flat.afp e.guarded ↔ l ∈ (deriveSyncEff s c e.guarded).flat.afp e.guarded
      rw [hsk.afp heo.bound]
    · cases hg₀
      by_cases hjA : j < s.A.length
      · exact absurd (hsk.covering heo.bound hjA hcov)
          (heo.disc hl hn j (List.mem_range.2 hjA))
      · have hjl := active_lt hcov.2.1
        rw [hA, List.length_append, List.length_singleton] at hjl
        exact .inl (by omega)
  · have hxo := hes x (List.mem_of_getElem? hj)
    refine entry_step hsk hw' hxo ?_ (hold_of_same hh x) fun hl' ctl hc hleaf =>
      ctl_same hw hP (Nat.lt_of_lt_of_le hxo.bound hsk.len) hh hc hleaf
    intro hxl j' y' o hy' hj' ho
    rw [hA, List.getElem?_append_right hj'] at hy'
    have : o = e.guarded := by
      have hm := List.mem_of_getElem? hy'
      rw [List.mem_singleton] at hm; subst hm; cases ho; rfl
    subst this
    exact fun hg => hji (hu j i x e hj hi hxl hl hg.symm)

/-- `unlock` (C17) preserves `SyncCore`. -/
theorem unlock_preserves {L : MutexLayout} {s : SC} {reg : SyncReg} {c i : Nat}
    {st' : SC × SyncReg} (h : UnlockOk L s reg c i st') (hw : WF3 s.flat)
    (hw' : WF3 st'.1.flat) (hs : SyncCore L s reg) : SyncCore L st'.1 st'.2 := by
  obtain ⟨e, g₀, hi, hl, hg₀, hpre, -, -, rfl⟩ := h
  obtain ⟨hes, hu⟩ := hs
  have heo := hes e (List.mem_of_getElem? hi)
  obtain ⟨x, hx, xa⟩ := hpre.active
  have hx' : s.A[g₀]? = some x := hx
  have hA : (s.set (releaseEff (s.view c) g₀)).A = s.A.set g₀ { x with active := false } := by
    show (releaseEff (s.view c) g₀).A = _; rw [releaseEff_eq hx]; rfl
  have hP : PSkel s.P (s.set (releaseEff (s.view c) g₀)).P := by
    show PSkel s.P (releaseEff (s.view c) g₀).P; rw [releaseEff_eq hx]; exact pskel_refl _
  obtain ⟨hsk, hh⟩ := skel_set hx' hA (same_deact x)
  have hlen : (s.set (releaseEff (s.view c) g₀)).A.length = s.A.length := by
    rw [hA, List.length_set]
  refine ⟨fun y hy => ?_,
    uniq_set hi rfl (uniq_step hsk (fun x hx => (hes x hx).bound) hu)⟩
  rcases mem_set_cases hy with rfl | ⟨j, hj, -⟩
  · obtain ⟨hg1, hc1⟩ := entry_static hsk hh hP hw hw' heo none
    refine ⟨hg1, (fun _ _ h => by cases h), hc1, fun _ _ j hj hcov => ?_, (fun _ _ h => by cases h),
      Nat.lt_of_lt_of_le heo.bound hsk.len⟩
    have hjA : j < s.A.length := by rw [← hlen]; exact List.mem_range.1 hj
    rcases heo.sub hl g₀ hg₀ ⟨x, hx, xa⟩ j (hsk.covering heo.bound hjA hcov) with hjg | hanc
    · obtain ⟨z, hz, za⟩ := hcov.2.1
      have hz' : (s.set (releaseEff (s.view c) g₀)).A[j]? = some z := hz
      rw [hA, List.getElem?_set, hjg] at hz'
      simp only [lt_of_getElem? hx', ↓reduceIte, Option.some.injEq] at hz'
      rw [← hz'] at za; cases za
    · exact hpre.noActiveDesc j (List.mem_range.2 hjA) hanc (hsk.active hjA hcov.2.1)
  · have hxo := hes y (List.mem_of_getElem? hj)
    exact entry_step hsk hw' hxo (src_none hlen y (List.mem_of_getElem? hj)) (hold_of_same hh y)
      fun _ ctl hc hleaf => ctl_same hw hP (Nat.lt_of_lt_of_le hxo.bound hsk.len) hh hc hleaf

/-- `resetLock` (C18) preserves `SyncCore`. -/
theorem resetLock_preserves {L : MutexLayout} {s : SC} {reg : SyncReg} {c i : Nat}
    {st' : SC × SyncReg} (h : ResetLockOk L s reg c i st') (hs : SyncCore L s reg) :
    SyncCore L st'.1 st'.2 := by
  obtain ⟨e, hi, -, hnc, -, -, rfl⟩ := h
  obtain ⟨hes, hu⟩ := hs
  have heo := hes e (List.mem_of_getElem? hi)
  refine ⟨fun y hy => ?_, uniq_set hi rfl hu⟩
  rcases mem_set_cases hy with rfl | ⟨j, hj, -⟩
  · exact ⟨heo.guarded, (fun _ _ h => by cases h), heo.control, fun _ _ => hnc,
      (fun _ _ h => by cases h), heo.bound⟩
  · exact hes y (List.mem_of_getElem? hj)

/-- A raw `deriveSync` under the library instantiation targets the `guarded` of a live entry,
which `RestrictedStep` excludes (C14, C15; only `acquire` derives from `guarded`). -/
theorem deriveSync_excluded {ks : KShared} {L : MutexLayout} {reg : SyncReg} {ar : ArenaReg}
    {s s' : SC} {c g : Nat} (h : DeriveSyncStep (libKC ks L) reg s c g (.ok s'))
    (he : RestrictedStep L (s, reg, ar) (.deriveSync c g)) :
    False := by
  obtain ⟨hpre, -⟩ := Guarded.ok_iff.1 h
  obtain ⟨e, hm, hg, hl, -⟩ := hpre.authorized
  exact he e hm hl hg.symm

/-! ## Controller uniqueness (C21.4) -/

/-- With the same holder for `guarded` and kept parents, the controller is unchanged (C12). -/
theorem ctl_same_eq {L : MutexLayout} {s s' : SC} {e : SyncEntry} (hw : WF3 s.flat)
    (hP : PSkel s.P s'.P) (hb : e.guarded < s'.A.length) (hh : HoldSame s s') {ctl : Nat}
    (hc : ControlOf L s e = some ctl) : ControlOf L s' e = some ctl := by
  obtain ⟨y, hp, m, hy, hph, hm, hk, hkc⟩ := controlOf_spec hc
  obtain ⟨y', hy'⟩ := getElem?_of_lt hb
  have hhp : y'.holder = .place hp := by rw [hh _ y y' hp hy hy' hph, hph]
  have hpP : hp < s.P.length := by
    simp only [parentOf] at hm
    cases hq : s.P[hp]? with
    | none => rw [hq] at hm; cases hm
    | some _ => exact lt_of_getElem? hq
  have hmP : m < s.P.length := (WF3.parent_lt (s := s.flat) hw hm).2
  have hm' : parentOf s'.P hp = some m := by rw [hP.2.1 hp hpP, hm]
  have hk' : (kids s'.P m)[L.guardedField]? = some hp := by rw [hP.kids hmP]; exact hk
  rw [controlOf_of hy' hhp hm' hk', hP.kids hmP, hkc]

/-- Controller uniqueness across a step with an unchanged registry that carries the controllers of
the live entries forward (C21.4); liveness only decreases. -/
theorem ctlUnique_step {L : MutexLayout} {s s' : SC} {reg : SyncReg} (hsk : Skel s s')
    (hc : SyncCore L s reg)
    (hfwd : ∀ e ∈ reg, ∀ ctl, ControlOf L s e = some ctl → ControlOf L s' e = some ctl)
    (hu : CtlUnique L s reg) : CtlUnique L s' reg := by
  intro i j e e' ctl hi hj hl hl' h1 h2
  have back : ∀ x ∈ reg, x.Live s' → ControlOf L s' x = some ctl →
      x.Live s ∧ ControlOf L s x = some ctl := by
    intro x hx hxl' hx'
    have hxo := hc.1 x hx
    have hxl := hsk.active hxo.bound hxl'
    have h3 := hxo.control hxl
    unfold OptP at h3; split at h3
    · rename_i c₀ hc₀
      rw [hfwd x hx c₀ hc₀] at hx'
      exact ⟨hxl, by rw [hc₀, hx']⟩
    · exact h3.elim
  obtain ⟨hl₀, h1₀⟩ := back e (List.mem_of_getElem? hi) hl h1
  obtain ⟨hl₀', h2₀⟩ := back e' (List.mem_of_getElem? hj) hl' h2
  exact hu i j e e' ctl hi hj hl₀ hl₀' h1₀ h2₀

/-- `ControlOf` and liveness read an entry only through its `guarded` identity (C12). -/
theorem controlOf_guarded {L : MutexLayout} {s : SC} {x y : SyncEntry}
    (h : x.guarded = y.guarded) : ControlOf L s x = ControlOf L s y ∧ (x.Live s ↔ y.Live s) := by
  unfold ControlOf SyncEntry.Live; rw [h]; exact ⟨rfl, Iff.rfl⟩

/-- Controller uniqueness after a record update keeping `guarded` (C21.4). -/
theorem ctlUnique_set {L : MutexLayout} {s : SC} {reg : SyncReg} {i : Nat} {e e' : SyncEntry}
    (hi : reg[i]? = some e) (hg : e'.guarded = e.guarded) (hu : CtlUnique L s reg) :
    CtlUnique L s (reg.set i e') := by
  intro j₁ j₂ x₁ x₂ ctl h₁ h₂ hl₁ hl₂ hc₁ hc₂
  obtain ⟨y₁, hy₁, hg₁⟩ := set_old hi hg h₁
  obtain ⟨y₂, hy₂, hg₂⟩ := set_old hi hg h₂
  obtain ⟨hC₁, hL₁⟩ := controlOf_guarded (L := L) (s := s) hg₁
  obtain ⟨hC₂, hL₂⟩ := controlOf_guarded (L := L) (s := s) hg₂
  exact hu j₁ j₂ y₁ y₂ ctl hy₁ hy₂ (hL₁.2 hl₁) (hL₂.2 hl₂) (hC₁ ▸ hc₁) (hC₂ ▸ hc₂)

/-- Controller uniqueness after registering an entry whose controller is not that of a live entry
(C13.8, C21.4). -/
theorem ctlUnique_append {L : MutexLayout} {s : SC} {reg : SyncReg} {e' : SyncEntry}
    (hu : CtlUnique L s reg)
    (hfresh : ∀ ctl, ControlOf L s e' = some ctl → ∀ x ∈ reg, x.Live s → ControlOf L s x ≠ some ctl) :
    CtlUnique L s (reg ++ [e']) := by
  intro j₁ j₂ x₁ x₂ ctl h₁ h₂ hl₁ hl₂ hc₁ hc₂
  rcases append_cases h₁ with h₁' | ⟨rfl, rfl⟩ <;> rcases append_cases h₂ with h₂' | ⟨rfl, rfl⟩
  · exact hu _ _ _ _ ctl h₁' h₂' hl₁ hl₂ hc₁ hc₂
  · exact absurd hc₁ (hfresh ctl hc₂ x₁ (List.mem_of_getElem? h₁') hl₁)
  · exact absurd hc₂ (hfresh ctl hc₁ x₂ (List.mem_of_getElem? h₂') hl₂)
  · rfl

/-- `newMutex` (C13.8) preserves controller uniqueness. -/
theorem newMutex_ctlUnique {k : K} {L : MutexLayout} {ar : ArenaReg} {s : SC} {reg : SyncReg}
    {c g : Nat} {st' : SC × SyncReg} (h : NewMutexOk k L ar s reg c g st')
    (hu : CtlUnique L s reg) : CtlUnique L st'.1 st'.2 := by
  obtain ⟨hpre, rfl⟩ := h
  refine ctlUnique_append hu fun ctl hc => ?_
  have h8 := hpre.ctlUnique
  rw [show ControlOf L s ⟨g, none⟩ = some ctl from hc] at h8
  exact h8

/-- `acquire` (C16) preserves controller uniqueness. -/
theorem acquire_ctlUnique {ks : KShared} {L : MutexLayout} {s : SC} {reg : SyncReg} {c i : Nat}
    {st' : SC × SyncReg} (h : AcquireOk ks L s reg c i st') (hw : WF3 s.flat)
    (hs : SyncCore L s reg) (hu : CtlUnique L s reg) : CtlUnique L st'.1 st'.2 := by
  obtain ⟨e, hi, -, hpre, rfl⟩ := h
  have hA : (deriveSyncEff s c e.guarded).A = s.A ++ [⟨.modify, some e.guarded,
      (s.view c).afp e.guarded, .frame (s.view c).top, true⟩] := rfl
  obtain ⟨hsk, hh⟩ := skel_append hA rfl (fun j y' hy' => ⟨y', hy', Same.refl _⟩) fun z hz => by
    rw [List.mem_singleton] at hz; subst hz
    exact .inr ⟨e.guarded, rfl, active_lt hpre.active, hpre.active, fun l hl => hl⟩
  exact ctlUnique_set hi rfl (ctlUnique_step hsk hs (fun x hx _ hc =>
    ctl_same_eq (s' := deriveSyncEff s c e.guarded) hw (pskel_refl _)
      (Nat.lt_of_lt_of_le (hs.1 x hx).bound hsk.len) hh hc) hu)

/-- `unlock` (C17) preserves controller uniqueness. -/
theorem unlock_ctlUnique {L : MutexLayout} {s : SC} {reg : SyncReg} {c i : Nat}
    {st' : SC × SyncReg} (h : UnlockOk L s reg c i st') (hw : WF3 s.flat)
    (hs : SyncCore L s reg) (hu : CtlUnique L s reg) : CtlUnique L st'.1 st'.2 := by
  obtain ⟨e, g₀, hi, -, -, hpre, -, -, rfl⟩ := h
  obtain ⟨x, hx, -⟩ := hpre.active
  have hx' : s.A[g₀]? = some x := hx
  have hA : (s.set (releaseEff (s.view c) g₀)).A = s.A.set g₀ { x with active := false } := by
    show (releaseEff (s.view c) g₀).A = _; rw [releaseEff_eq hx]; rfl
  have hP : PSkel s.P (s.set (releaseEff (s.view c) g₀)).P := by
    show PSkel s.P (releaseEff (s.view c) g₀).P; rw [releaseEff_eq hx]; exact pskel_refl _
  obtain ⟨hsk, hh⟩ := skel_set hx' hA (same_deact x)
  exact ctlUnique_set hi rfl (ctlUnique_step hsk hs (fun y hy _ hc =>
    ctl_same_eq hw hP (Nat.lt_of_lt_of_le (hs.1 y hy).bound hsk.len) hh hc) hu)

/-- `resetLock` (C18) preserves controller uniqueness. -/
theorem resetLock_ctlUnique {L : MutexLayout} {s : SC} {reg : SyncReg} {c i : Nat}
    {st' : SC × SyncReg} (h : ResetLockOk L s reg c i st') (hu : CtlUnique L s reg) :
    CtlUnique L st'.1 st'.2 := by
  obtain ⟨e, hi, -, -, -, -, rfl⟩ := h
  exact ctlUnique_set hi rfl hu

/-- Controller uniqueness across a step described by `StepFacts` (C21.4). -/
theorem facts_ctlUnique {L : MutexLayout} {reg : SyncReg} {s s' : SC} (hf : StepFacts reg s s')
    (hw : WF3 s.flat) (hs : SyncCore L s reg) (hu : CtlUnique L s reg) : CtlUnique L s' reg :=
  ctlUnique_step hf.skel hs (fun e hm _ hc =>
    ctl_same_eq hw hf.pskel (Nat.lt_of_lt_of_le (hs.1 e hm).bound hf.skel.len) hf.hold hc) hu

end SyncPreserveAux

open SyncPreserveAux

end Ern.ConcurrencyModel
