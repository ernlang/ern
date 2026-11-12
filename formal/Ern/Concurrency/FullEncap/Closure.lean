import Ern.Concurrency.FullEncap.Capacity

/-!
# Closure of the descendance of `guarded`

Brief of milestone 4, slice 3, complement, task 2 (`corpus-spec2-m3.md` v14 §2 terdecies,
"Fermeture de la descendance"): on a `RunFull` from the initial state, for every step and every
entry `e` live before and after it, every covering descendant of `e` after the step (WC5.2 C22:
an active strict descendant of `guarded` by the current origin chain, read transitively, covering
a leaf of `footprint(guarded)`; `CoveringDesc`) was one before the step (case 1, its direct origin
possibly changed), or is created by the step with an origin that was one before the step
(case 2), or is the grant recorded by the step, an `acquire(e)` (case 3).

The proof reads each step through the abstraction `Skel` of `SyncPreserve` (old authorities keep
footprint and mode, are never reactivated, and their origin chain only loses elements; added
authorities are roots or derived from an old active authority). The composite steps (`issue`,
`reset`, by-value `spawn`) are read phase by phase (`Skel.comp`): only their first phase creates
authorities, so an authority they create has an origin that existed before the step, and the
form (2′) of the brief is not needed.
-/

set_option autoImplicit false

namespace Ern.Concurrency.FullEncap

open Ern.MemoryModel Ern.MemoryModel.Access Ern.Concurrency Ern.Concurrency.MutexReal
open SyncPreserveAux SyncInitAux TransferPreserveAux

/-! ## Composition of steps -/

/-- Two steps compose when the second creates no authority and keeps every origin (`store`,
`release`, `transfer`, the yield of the by-value composite). -/
theorem Skel.comp {s s₁ s₂ : SC} (h1 : Skel s s₁) (h2 : Skel s₁ s₂)
    (hlen : s₂.A.length = s₁.A.length) (horg : ∀ i, s₂.flat.org i = s₁.flat.org i) :
    Skel s s₂ := by
  have hancs : ∀ j, s₂.flat.ancs j = s₁.flat.ancs j := fun j => chain_congr fun i _ => horg i
  refine ⟨by have := h1.len; omega, fun j y'' hy'' hj => ?_, fun j hj x hx => ?_,
    fun j hj hact x hx hxa => ?_, fun j y'' hy'' hj => ?_⟩
  · have hj₁ : j < s₁.A.length := Nat.lt_of_lt_of_le hj h1.len
    obtain ⟨y', hy', hf', hm', ha', ho'⟩ := h2.old j y'' hy'' hj₁
    obtain ⟨y, hy, hf, hm, ha, ho⟩ := h1.old j y' hy' hj
    refine ⟨y, hy, hf'.trans hf, hm'.trans hm, fun h => ha (ha' h), fun o hyo hoa => ?_⟩
    have ho₁ : s₁.flat.Active o := h2.active (by have := active_lt hoa; omega) hoa
    exact ho' o (ho o hyo ho₁) hoa
  · exact h1.ancsSub j hj x (h2.ancsSub j (Nat.lt_of_lt_of_le hj h1.len) x hx)
  · have hj₁ : j < s₁.A.length := Nat.lt_of_lt_of_le hj h1.len
    have hact₁ := h2.active hj₁ hact
    have hxa₁ := h2.active (by have := active_lt hxa; omega) hxa
    exact h2.ancsKeep j hj₁ hact x (h1.ancsKeep j hj hact₁ x hx hxa₁) hxa
  · have hj₁ : j < s₁.A.length := by have := lt_of_getElem? hy''; omega
    obtain ⟨y', hy', hf', -, -, -⟩ := h2.old j y'' hy'' hj₁
    have hoe : y''.origin = y'.origin := by
      have := horg j
      simp only [S3.org] at this
      have e1 : s₂.flat.A[j]? = some y'' := hy''
      have e2 : s₁.flat.A[j]? = some y' := hy'
      rw [e1, e2] at this; simpa using this
    rcases h1.new j y' hy' hj with ho | ⟨o, ho, hoA, hoa, hfp, hanc⟩
    · exact .inl (hoe.trans ho)
    · exact .inr ⟨o, hoe.trans ho, hoA, hoa, by rw [hf']; exact hfp, by rw [hancs]; exact hanc⟩

/-- The identity step. -/
theorem skel_refl (s : SC) : Skel s s := (skel_sameA rfl).1

/-- `store` executed by `c` keeps the number of authorities and every origin (Spec 1 §65 effect:
only the holder of the stored authority changes). -/
theorem store_org (s : SC) (c a p : Nat) :
    (storeEffC s c a p).A.length = s.A.length ∧
      ∀ i, (storeEffC s c a p).flat.org i = s.flat.org i := by
  have hA : (storeEffC s c a p).A = (storeEff (s.view c) a p).A := rfl
  unfold storeEff at hA
  cases hy : (s.view c).A[a]? with
  | none =>
    rw [hy] at hA
    exact ⟨by rw [hA]; rfl, fun i => by show ((storeEffC s c a p).A[i]?).bind _ = _; rw [hA]; rfl⟩
  | some y =>
    rw [hy] at hA
    refine ⟨by rw [hA]; simp; rfl, fun i => ?_⟩
    show ((storeEffC s c a p).A[i]?).bind (·.origin) = (s.A[i]?).bind (·.origin)
    rw [hA]
    have hy' : s.A[a]? = some y := hy
    by_cases e : a = i
    · subst e
      rw [List.getElem?_set_self (lt_of_getElem? hy), hy']; rfl
    · rw [List.getElem?_set_ne e]; rfl

/-- `release` keeps the number of authorities and every origin (Spec 1 §62 effect). -/
theorem release_org (t : SC) (c a : Nat) :
    (t.set (releaseEff (t.view c) a)).A.length = t.A.length ∧
      ∀ i, (t.set (releaseEff (t.view c) a)).flat.org i = t.flat.org i := by
  cases hx : (t.view c).A[a]? with
  | none =>
    have h0 : releaseEff (t.view c) a = t.view c := by simp [releaseEff, hx]
    have hA : (t.set (releaseEff (t.view c) a)).A = t.A := by
      show (releaseEff (t.view c) a).A = t.A
      rw [h0]; rfl
    refine ⟨by rw [hA], fun i => ?_⟩
    show ((t.set (releaseEff (t.view c) a)).A[i]?).bind (·.origin) = (t.A[i]?).bind (·.origin)
    rw [hA]
  | some x =>
    have hA : (t.set (releaseEff (t.view c) a)).A = t.A.set a { x with active := false } := by
      show (releaseEff (t.view c) a).A = _; rw [releaseEff_eq hx]; rfl
    refine ⟨by rw [hA, List.length_set], fun i => ?_⟩
    show ((t.set (releaseEff (t.view c) a)).A[i]?).bind (·.origin) = (t.A[i]?).bind (·.origin)
    rw [hA]
    have hx' : t.A[a]? = some x := hx
    by_cases e : a = i
    · subst e
      rw [List.getElem?_set_self (lt_of_getElem? hx'), hx']; rfl
    · rw [List.getElem?_set_ne e]

/-- `transfer` executed by `c` (Spec 1 §63 effect): a step keeping the number of authorities and
every origin. -/
theorem transfer_skel (s : SC) (c src dst : Nat) :
    Skel s (transferEffC s c src dst) ∧
      (transferEffC s c src dst).A.length = s.A.length ∧
      ∀ i, (transferEffC s c src dst).flat.org i = s.flat.org i := by
  have hget : ∀ j : Nat, (transferEffC s c src dst).A[j]? = (s.A[j]?).map fun (y : Authority) =>
      if heldIn s.P src y.holder then { y with holder := mvTo s.P src dst y.holder } else y :=
    fun j => transfer_A_get (s.view c) src dst j
  have hlen : (transferEffC s c src dst).A.length = s.A.length := by
    show (transferEff (s.view c) src dst).A.length = _; simp [transferEff]; rfl
  have horg : ∀ i, (transferEffC s c src dst).flat.org i = s.flat.org i := by
    intro i
    show ((transferEffC s c src dst).A[i]?).bind (·.origin) = (s.A[i]?).bind (·.origin)
    rw [hget]; cases s.A[i]? with
    | none => rfl
    | some y => simp only [Option.map_some, Option.bind_some]; split <;> rfl
  have hancs : ∀ j, (transferEffC s c src dst).flat.ancs j = s.flat.ancs j :=
    fun j => chain_congr fun i _ => horg i
  refine ⟨⟨by omega, fun j y' hy' _ => ?_, fun j _ x hx => by rwa [hancs] at hx,
    fun j _ _ x hx _ => by rwa [hancs], fun j y' hy' hj => by
      have := lt_of_getElem? hy'; omega⟩, hlen, horg⟩
  rw [hget] at hy'
  obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hy'
  refine ⟨y, hy, by split <;> rfl, by split <;> rfl, by split <;> exact id, fun o ho _ => ?_⟩
  split <;> exact ho

/-- The transfer phases of the by-value composite (WC5.2 C5 phase 2): a step keeping the number of
authorities and every origin. -/
theorem transfers_skel (c : Nat) : ∀ (t : SC) (vs : List (Nat × Nat)),
    Skel t (transfersEff c t vs) ∧ (transfersEff c t vs).A.length = t.A.length ∧
      ∀ i, (transfersEff c t vs).flat.org i = t.flat.org i
  | t, [] => ⟨skel_refl t, rfl, fun _ => rfl⟩
  | t, v :: vs => by
    obtain ⟨h1, l1, o1⟩ := transfer_skel t c v.1 v.2
    obtain ⟨h2, l2, o2⟩ := transfers_skel c (transferEffC t c v.1 v.2) vs
    exact ⟨Skel.comp h1 h2 l2 o2, l2.trans l1, fun i => (o2 i).trans (o1 i)⟩

/-- The yield phase of the by-value composite (WC5.2 C5 phase 3), the yielded parameters being held
by a frame: a step keeping the number of authorities and every origin. -/
theorem yield_skel' {t : SC} {ps : List Nat} {f : Nat}
    (hp : ∀ a ∈ ps, ∀ y, t.A[a]? = some y → ∃ g, y.holder = .frame g) :
    Skel t (yieldEff t ps f) ∧ (yieldEff t ps f).A.length = t.A.length ∧
      ∀ i, (yieldEff t ps f).flat.org i = t.flat.org i := by
  have hlen : (yieldEff t ps f).A.length = t.A.length := length_mapI _ _ _
  have hS : ∀ (j : Nat) (y' : Authority), (yieldEff t ps f).A[j]? = some y' →
      ∃ y, t.A[j]? = some y ∧ Same y y' := by
    intro j y' hy'
    rw [yield_get] at hy'
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hy'
    refine ⟨y, hy, ?_⟩
    unfold yieldF; split
    · rename_i hj
      obtain ⟨g, hg⟩ := hp j hj y hy
      exact ⟨rfl, rfl, rfl, id, fun q hq => by rw [hg] at hq; cases hq⟩
    · exact Same.refl y
  refine ⟨(skel_map hlen hS).1, hlen, fun i => ?_⟩
  show ((yieldEff t ps f).A[i]?).bind (·.origin) = (t.A[i]?).bind (·.origin)
  rw [yield_get]; cases t.A[i]? with
  | none => rfl
  | some y => simp only [Option.map_some, Option.bind_some]; unfold yieldF; split <;> rfl

/-! ## The closure -/

/-- Case 3 of the closure: the step is an `acquire` of an entry whose `guarded` is that of `e`,
and `j` is the grant it records, of fresh identity `|A|` (WC5.2 C16 effect). -/
def GrantOf (st : SC × SyncReg × ArenaReg) (e : SyncEntry) (j : Nat) : Label → Prop
  | .acquire _ i => OptP (st.2.1[i]?) (fun e' => e'.guarded = e.guarded ∧ j = st.1.A.length) False
  | _ => False

/-- Decidability of `GrantOf`. -/
instance (st : SC × SyncReg × ArenaReg) (e : SyncEntry) (j : Nat) (lbl : Label) :
    Decidable (GrantOf st e j lbl) := by
  unfold GrantOf; split <;> infer_instance

/-- The closure of the brief of the complement, task 2, for a step from `st` to `st'`: for every
entry of the registry before the step, live before and after it, every covering descendant after
the step is one before it (case 1), or is created by the step with an origin that is one before it
(case 2), or is the grant recorded by the step, an `acquire` of an entry with the same `guarded`
(case 3). -/
def ClosureStep (st : SC × SyncReg × ArenaReg) (lbl : Label) (st' : SC × SyncReg × ArenaReg) :
    Prop :=
  ∀ e ∈ st.2.1, e.Live st.1 → e.Live st'.1 → ∀ j ∈ List.range st'.1.A.length,
    CoveringDesc st'.1 e.guarded j →
      CoveringDesc st.1 e.guarded j ∨
      (st.1.A.length ≤ j ∧ ∃ o, st'.1.flat.org j = some o ∧ CoveringDesc st.1 e.guarded o) ∨
      GrantOf st e j lbl

/-- Decidability of `ClosureStep`. -/
instance (st : SC × SyncReg × ArenaReg) (lbl : Label) (st' : SC × SyncReg × ArenaReg) :
    Decidable (ClosureStep st lbl st') := by
  unfold ClosureStep; infer_instance

/-- A covering descendant after a step read through `Skel` was one before it, or is created with
an origin that is `g` itself or a covering descendant before the step (WC5.2 C22). -/
theorem cover_of_skel {s s' : SC} {g j : Nat} (hsk : Skel s s') (hg : g < s.A.length)
    (h : CoveringDesc s' g j) : CoveringDesc s g j ∨
      (s.A.length ≤ j ∧ ∃ o, s'.flat.org j = some o ∧ (g = o ∨ CoveringDesc s g o)) := by
  by_cases hj : j < s.A.length
  · exact .inl (hsk.covering hg hj h)
  · obtain ⟨y', o, hy', ho, hor, -⟩ := hsk.covering_new hg (Nat.le_of_not_lt hj) h
    refine .inr ⟨Nat.le_of_not_lt hj, o, ?_, hor⟩
    show (s'.A[j]?).bind (·.origin) = some o
    rw [hy']; exact ho

/-- A step read through `Skel` whose added authorities are not derived directly from the `guarded`
of a live entry (`StepFacts.src`) satisfies the closure without its case 3. -/
theorem closure_of_skel {s s' : SC} {reg reg' : SyncReg} {ar ar' : ArenaReg} {lbl : Label}
    (hsk : Skel s s')
    (hsrc : ∀ e ∈ reg, e.Live s → ∀ j y' o, s'.A[j]? = some y' → s.A.length ≤ j →
      y'.origin = some o → o ≠ e.guarded) :
    ClosureStep (s, reg, ar) lbl (s', reg', ar') := by
  intro e he hl _ j _ hcov
  rcases cover_of_skel hsk (active_lt hl) hcov with h | ⟨hj, o, ho, hor⟩
  · exact .inl h
  · rcases hor with rfl | hc
    · obtain ⟨y', hy'⟩ : ∃ y', s'.A[j]? = some y' := by
        cases hy : s'.A[j]? with
        | none => simp [S3.org, show s'.flat.A[j]? = none from hy] at ho
        | some y' => exact ⟨y', rfl⟩
      have hyo : y'.origin = some e.guarded := by
        have : (s'.A[j]?).bind (·.origin) = some e.guarded := ho
        rw [hy'] at this; exact this
      exact absurd rfl (hsrc e he hl j y' _ hy' hj hyo)
    · exact .inr (.inl ⟨hj, o, ho, hc⟩)

/-- The source condition carries over a phase that creates no authority and keeps every origin. -/
theorem src_carry {s s₁ s₂ : SC} {reg : SyncReg}
    (hsrc : ∀ e ∈ reg, e.Live s → ∀ j y' o, s₁.A[j]? = some y' → s.A.length ≤ j →
      y'.origin = some o → o ≠ e.guarded)
    (hlen : s₂.A.length = s₁.A.length) (horg : ∀ i, s₂.flat.org i = s₁.flat.org i) :
    ∀ e ∈ reg, e.Live s → ∀ j y'' o, s₂.A[j]? = some y'' → s.A.length ≤ j →
      y''.origin = some o → o ≠ e.guarded := by
  intro e he hl j y'' o hy'' hj ho
  obtain ⟨y', hy'⟩ := getElem?_of_lt (show j < s₁.A.length by
    have := lt_of_getElem? hy''; omega)
  have h := horg j
  simp only [S3.org] at h
  have e1 : s₂.flat.A[j]? = some y'' := hy''
  have e2 : s₁.flat.A[j]? = some y' := hy'
  rw [e1, e2] at h
  simp only [Option.bind_some] at h
  exact hsrc e he hl j y' o hy' hj (h ▸ ho)

/-- `store` executed by `c` of an authority held by the current frame (Spec 1 §65.1) is a step
read through `Skel`. -/
theorem store_skel' {s : SC} {c a p : Nat}
    (hd : OptP ((s.view c).A[a]?) (fun y => y.active = true ∧ y.origin ≠ none ∧
      y.holder = .frame (s.view c).top) False) : Skel s (storeEffC s c a p) := by
  unfold OptP at hd
  split at hd
  · rename_i y hy
    have hy' : s.A[a]? = some y := hy
    have hA : (storeEffC s c a p).A = s.A.set a { y with holder := .place p } := by
      show (storeEff (s.view c) a p).A = _; simp [storeEff, hy]; rfl
    exact (skel_set hy' hA ⟨rfl, rfl, rfl, id, fun q hq => by rw [hd.2.2] at hq; cases hq⟩).1
  · exact hd.elim

/-- `release` executed by `c` of an existing authority (Spec 1 §62) is a step read through
`Skel`. -/
theorem release_skel' {t : SC} {c a : Nat} {x : Authority} (hx : t.A[a]? = some x) :
    Skel t (t.set (releaseEff (t.view c) a)) := by
  have hx' : (t.view c).A[a]? = some x := hx
  have hA : (t.set (releaseEff (t.view c) a)).A = t.A.set a { x with active := false } := by
    show (releaseEff (t.view c) a).A = _; rw [releaseEff_eq hx']; rfl
  exact (skel_set hx hA (same_deact x)).1

/-- Brief of the complement, task 2, step form: an `ok` step admitted by `Encap` (WC5.2 C22 items
1–3, 5), from a state satisfying `KInvCA` and the separation of the registries (`AdminSep`, Spec 1
§56, WC5.2 C13 item 7), satisfies the closure. -/
theorem closure_step {k : K} {L : MutexLayout} {st st' : SC × SyncReg × ArenaReg} {lbl : Label}
    (hk : KInvCA st.1) (hsep : AdminSep st.1 st.2.1 st.2.2) (he : Encap L (st.1, st.2.1) lbl)
    (hs : LStep k L lbl st st') : ClosureStep st lbl st' := by
  have hw : WF3 st.1.flat := hk.1.1.2
  cases hs with
  | @kernel s s' reg ar c op h =>
    cases op
    case transfer src dst =>
      obtain ⟨-, h'⟩ := h; obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h'
      obtain ⟨hsk, hlen, -⟩ := transfer_skel s c src dst
      exact closure_of_skel hsk (src_none hlen)
    all_goals
      have hf := opStep_facts (reg := reg) h he (fun _ _ h => by cases h) hw
      exact closure_of_skel hf.skel hf.src
  | @spawn s s' reg ar c ps ls h =>
    obtain ⟨-, h'⟩ := h; obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h'
    have hf := spawnEff_facts (reg := reg) hpre.params hpre.localsOK
    exact closure_of_skel hf.skel hf.src
  | @terminate s s' reg ar c h =>
    have hf := term_facts (reg := reg) hw h
    exact closure_of_skel hf.skel hf.src
  | @join s s' reg ar c d h =>
    have hf := join_facts (reg := reg) h
    exact closure_of_skel hf.skel hf.src
  | deriveSync h => exact (deriveSync_excluded h he).elim
  | newMutex h =>
    obtain ⟨-, -, rfl⟩ := h
    exact closure_of_skel (skel_refl _) (src_none rfl)
  | @acquire s reg ar c i st₁ h =>
    obtain ⟨-, e₀, hi, -, hpre, rfl⟩ := h
    have hA : (deriveSyncEff s c e₀.guarded).A = s.A ++ [⟨.modify, some e₀.guarded,
        (s.view c).afp e₀.guarded, .frame (s.view c).top, true⟩] := rfl
    obtain ⟨hsk, -⟩ := skel_append hA rfl (fun j y' hy' => ⟨y', hy', Same.refl _⟩) fun z hz => by
      rw [List.mem_singleton] at hz; subst hz
      exact .inr ⟨e₀.guarded, rfl, active_lt hpre.active, hpre.active, fun l hl => hl⟩
    intro e _ hl _ j hjr hcov
    rcases cover_of_skel hsk (active_lt hl) hcov with h | ⟨hj, o, ho, hor⟩
    · exact .inl h
    · have hjlen : j < s.A.length + 1 := by
        have := List.mem_range.1 hjr
        simp only [hA, List.length_append, List.length_singleton] at this
        exact this
      have hje : j = s.A.length := by omega
      have hoe : o = e₀.guarded := by
        have : ((deriveSyncEff s c e₀.guarded).A[j]?).bind (·.origin) = some o := ho
        rw [hA, hje, List.getElem?_append_right (Nat.le_refl _)] at this
        simpa using this.symm
      rcases hor with hg | hc
      · refine .inr (.inr ?_)
        show OptP (reg[i]?) _ False
        rw [hi]
        exact ⟨by rw [← hoe, hg], hje⟩
      · exact .inr (.inl ⟨hj, o, ho, hc⟩)
  | @unlock s reg ar c i st₁ h =>
    obtain ⟨-, e₀, g₀, -, -, -, hpre, -, rfl⟩ := h
    obtain ⟨x, hx, -⟩ := hpre.active
    have hsk := release_skel' (c := c) (show s.A[g₀]? = some x from hx)
    exact closure_of_skel hsk (src_none (release_org s c g₀).1)
  | resetLock h =>
    obtain ⟨-, -, -, -, -, -, rfl⟩ := h
    exact closure_of_skel (skel_refl _) (src_none rfl)
  | @spawnVal s s' reg ar c ps ls vs h =>
    obtain ⟨-, h'⟩ := h; obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h'
    have hf := spawnEff_facts (reg := reg) (c := c) (ps := []) (s := s) (fun _ h => by cases h)
      hpre.localsOK
    obtain ⟨h1, l1, o1⟩ := transfers_skel c (spawnCreate s c ls) vs
    have hp : ∀ a ∈ ps, ∀ y, (transfersEff c (spawnCreate s c ls) vs).A[a]? = some y →
        ∃ g, y.holder = .frame g := by
      intro a ha y hy
      have := hpre.paramsAtYield a ha
      have hy' : ((transfersEff c (spawnCreate s c ls) vs).view c).A[a]? = some y := hy
      rw [hy'] at this
      exact ⟨_, this.2.1⟩
    obtain ⟨h2, l2, o2⟩ := yield_skel' (f := s.nF) hp
    have hsk : Skel s (spawnValEff s c ps ls vs) :=
      Skel.comp (Skel.comp hf.skel h1 l1 o1) h2 l2 o2
    exact closure_of_skel hsk
      (src_carry (src_carry hf.src l1 o1) l2 o2)
  | newArena h =>
    obtain ⟨-, -, rfl⟩ := newArenaStepC_ok h
    exact closure_of_skel (skel_refl _) (src_none rfl)
  | @issue s reg ar c i region dst st₁ h =>
    obtain ⟨E, s₁, hE, hst, -, hsp, hsto, -⟩ := issueStepC_ok h
    have hsep' : Encap L (s, reg) (.kernel c (.split E.internal [region])) :=
      fun e hm hl heq => hsep e hm E (List.mem_of_getElem? hE) hl
        (by show s.flat.Active E.internal; rw [heq]; exact hl) heq.symm
    have hf := opStep_facts (reg := reg) hsp hsep' (fun _ _ h => by cases h) hw
    obtain ⟨-, h'⟩ := hsto; obtain ⟨hpre, he₂⟩ := Guarded.ok_iff.1 h'
    rw [he₂]
    obtain ⟨l2, o2⟩ := store_org s₁ c s.A.length dst
    exact closure_of_skel (Skel.comp hf.skel (store_skel' hpre.derivedHeld) l2 o2)
      (src_carry hf.src l2 o2)
  | @reset s reg ar c i st₁ h =>
    obtain ⟨E, s₁, hE, hd, hrl, -, -⟩ := resetStepC_ok (k := k) h
    have hl₀ : s.flat.Active E.internal := by
      obtain ⟨-, o, hR, ho⟩ := hd
      cases hR with
      | ok hp => exact hp.active
      | reject => cases ho
    have hsep' :
        Encap L (s, reg) (.kernel c (.derive E.internal (footprint s.P E.storage) .modify)) :=
      fun e hm hl heq => hsep e hm E (List.mem_of_getElem? hE) hl
        (by show s.flat.Active E.internal; exact hl₀) heq.symm
    have hf := opStep_facts (reg := reg) hd hsep' (fun _ _ h => by cases h) hw
    obtain ⟨-, o, hR, ho⟩ := hrl
    cases hR with
    | ok hp =>
      have he₂ : st₁.1 = s₁.set (releaseEff (s₁.view c) s.A.length) := Outcome3.ok.inj ho
      rw [he₂]
      obtain ⟨x, hx, -⟩ := hp.active
      obtain ⟨l2, o2⟩ := release_org s₁ c s.A.length
      exact closure_of_skel (Skel.comp hf.skel (release_skel' (c := c) hx) l2 o2)
        (src_carry hf.src l2 o2)
    | reject => cases ho

/-- Brief of the complement, task 2: on a `RunFull` from the initial state of Spec 1 §47, under
`DDSound` (Spec 1 §80), every step satisfies the closure of the covering descendants: an authority
enters the covering descendants of a live entry only by being created from one of them, or as the
grant of an `acquire` of that entry. -/
theorem closure_run {k : K} {L : MutexLayout} {statics : Statics}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} (hdd : DDSound k)
    (hstat : StaticsOK statics) (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], []))
    (h : RunFull k L σ lbls) {i : Nat} (hi : i < lbls.length) :
    ClosureStep (σ i) lbls[i] (σ (i + 1)) := by
  obtain ⟨hk, hlib⟩ := runFull_inv hdd hstat h0 h (Nat.le_of_lt hi)
  exact closure_step hk hlib.2.1 (h i hi).1.1.1.1.1 (h i hi).2

end Ern.Concurrency.FullEncap
