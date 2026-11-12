import Ern.Concurrency.FullEncap.Capacity

/-!
# Capacity of the by-value `spawn` in the state before the step

Brief of milestone 4, slice 3, complement, task 4 (`corpus-spec2-m3.md` v14 §2 terdecies,
"`spawnVal`"): the creating context has `Modify` on every leaf of every source of a by-value
`spawn`, read in the state before the step.

The right on a source is checked at the start of its transfer phase (WC5.2 C5.2); the guard-free
form gives an `Exer5` chain in the phase state. The phase states differ from the state before the
step by fresh root locals of the child, held by its new frame (WC5.2 C5 phase 1), and by the
holders moved into those locals by the earlier transfers (Spec 1 §63 effect: a transfer moves held
authorities, it creates none). `PhaseRel` records these differences; an `Exer5` chain of the
creator in a phase state uses only authorities and holders of the state before the step
(`exer5_back`), with the same effective modes on the existing leaves.
-/

set_option autoImplicit false

namespace Ern.Concurrency.FullEncap

open Ern.MemoryModel Ern.MemoryModel.Access Ern.Concurrency Ern.Concurrency.MutexReal
open SyncPreserveAux SyncInitAux TransferPreserveAux

/-! ## Correspondence lands in fresh places -/

/-- `corr` (Spec 1 §63.2) lands at or below the destination: when parents precede their children
and the destination is at least `N`, so is every corresponding part. -/
theorem corrF_ge {P : List Place} {src dst N : Nat}
    (hpp : ∀ q o, parentOf P q = some o → o < q) (hd : N ≤ dst) (hdl : dst < P.length) :
    ∀ n r x, corrF P src dst n r = some x → N ≤ x ∧ x < P.length
  | 0, r, x, h => by
    simp only [corrF] at h
    split at h
    · cases h; exact ⟨hd, hdl⟩
    · cases h
  | n + 1, r, x, h => by
    simp only [corrF] at h
    split at h
    · cases h; exact ⟨hd, hdl⟩
    · split at h
      · rename_i p hp
        split at h
        · obtain ⟨p', hp', hx⟩ := Option.bind_eq_some_iff.1 h
          have hN := (corrF_ge hpp hd hdl n p p' hp').1
          have hmem : x ∈ kids P p' := List.mem_of_getElem? hx
          have hm := List.mem_filter.1 hmem
          have hpx : parentOf P x = some p' := of_decide_eq_true hm.2
          have := hpp x p' hpx
          exact ⟨by omega, List.mem_range.1 hm.1⟩
        · cases h
      · cases h

/-- The holder given by a transfer to an authority held within the source is a place at least
`N` when the destination is (Spec 1 §63 effect). -/
theorem mvTo_ge {P : List Place} {src dst N : Nat}
    (hpp : ∀ q o, parentOf P q = some o → o < q) (hd : N ≤ dst) (hdl : dst < P.length)
    (r : Nat) : ∃ p, mvTo P src dst (.place r) = .place p ∧ N ≤ p ∧ p < P.length := by
  refine ⟨(corr P src dst r).getD dst, rfl, ?_⟩
  cases h : corr P src dst r with
  | none => exact ⟨hd, hdl⟩
  | some x => exact corrF_ge hpp hd hdl r r x h

/-! ## The relation between a phase state and the state before the step -/

/-- A phase state `t` of a by-value `spawn` by `c` from `s` (WC5.2 C5 phases 1 and 2): existing
places keep their footprints, new places hold only new leaves and follow their parents; existing
authorities keep their skeleton, their frame holders, and any holder that is an existing place;
new authorities are held by the new frame `s.nF`; effective modes of existing authorities on
existing leaves are unchanged; the current frame of `c` is unchanged. -/
structure PhaseRel (s : SC) (c : Nat) (t : SC) : Prop where
  lenP : s.P.length ≤ t.P.length
  lenA : s.A.length ≤ t.A.length
  parentLt : ∀ q o, parentOf t.P q = some o → o < q
  fpOld : ∀ q, q < s.P.length → ∀ l, l ∈ footprint t.P q ↔ l ∈ footprint s.P q
  fpNew : ∀ q l, s.P.length ≤ q → l ∈ footprint t.P q → s.P.length ≤ l
  holdLt : ∀ (a : Nat) (y : Authority) (p : Nat), t.A[a]? = some y → y.active = true →
    y.holder = .place p → p < t.P.length
  aOld : ∀ (a : Nat) (y : Authority), t.A[a]? = some y → a < s.A.length → ∃ y₀, s.A[a]? = some y₀ ∧
    skel y = skel y₀ ∧ (∀ f, y.holder = .frame f → y₀.holder = .frame f) ∧
    (∀ p, y.holder = .place p → p < s.P.length → y₀.holder = .place p)
  aNew : ∀ (a : Nat) (y : Authority), t.A[a]? = some y → s.A.length ≤ a → y.holder = .frame s.nF
  eff : ∀ b l, b < s.A.length → l < s.P.length → effective t.flat b l = effective s.flat b l
  top : (t.view c).top = (s.view c).top

/-- Existing authorities active before the step stay active in a phase state. -/
theorem PhaseRel.active {s t : SC} {c g : Nat} (h : PhaseRel s c t) (ha : s.flat.Active g) :
    t.flat.Active g := by
  obtain ⟨y₀, hy₀, ya⟩ := ha
  have hg : g < s.A.length := lt_of_getElem? hy₀
  obtain ⟨y, hy⟩ := getElem?_of_lt (Nat.lt_of_lt_of_le hg h.lenA)
  obtain ⟨y₀', hy₀', hsk, -, -⟩ := h.aOld g y hy hg
  have hy₀'' : s.A[g]? = some y₀ := hy₀
  rw [hy₀''] at hy₀'; cases hy₀'
  simp only [skel, Prod.mk.injEq] at hsk
  exact ⟨y, hy, by rw [hsk.2.2.2]; exact ya⟩

/-- An effective mode that permits a request is present (Spec 1 §43). -/
theorem ne_none_of_allows {e : Option Mode} {m : Mode} (h : Allows e m) : e ≠ none := by
  cases e with
  | none => exact h.elim
  | some _ => exact fun h' => by cases h'

/-- An `Exer5` chain of the creator in a phase state is an `Exer5` chain in the state before the
step, through existing authorities only (WC5.2 C5 phase 2; Spec 1 §43, §63 effect). -/
theorem exer5_back {s t : SC} {reg : SyncReg} {c : Nat} (h : PhaseRel s c t)
    (hfp : ∀ (a : Nat) (y : Authority), s.A[a]? = some y → ∀ l ∈ y.footprint, l < s.P.length)
    (htop : s.nF ≠ (s.view c).top) {a : Nat} {m : Mode} (hx : Exer5 t reg c a m) :
    a < s.A.length ∧ Exer5 s reg c a m := by
  induction hx with
  | @base a m y hg hy ha hm hf =>
    have hng : NotGuarded s reg a := fun e he hl => hg e he (h.active hl)
    by_cases hlt : a < s.A.length
    · obtain ⟨y₀, hy₀, hsk, hfr, -⟩ := h.aOld a y hy hlt
      simp only [skel, Prod.mk.injEq] at hsk
      exact ⟨hlt, .base hng hy₀ (by rw [← hsk.2.2.2]; exact ha) (by rw [← hsk.1]; exact hm)
        (by rw [hfr _ hf, h.top])⟩
    · have h1 := h.aNew a y hy (Nat.le_of_not_lt hlt)
      rw [hf] at h1
      have h2 : (t.view c).top = s.nF := Holder.frame.inj h1
      exact absurd (by rw [← h.top, h2]) htop
  | @held a p b m y hg hy ha hm hp _ hc ih =>
    obtain ⟨hb, hbx⟩ := ih
    have hng : NotGuarded s reg a := fun e he hl => hg e he (h.active hl)
    have hlt : a < s.A.length := Decidable.byContradiction fun hge => by
      have h1 := h.aNew a y hy (Nat.le_of_not_lt hge)
      rw [hp] at h1; cases h1
    obtain ⟨y₀, hy₀, hsk, -, hpl⟩ := h.aOld a y hy hlt
    simp only [skel, Prod.mk.injEq] at hsk
    have hpo : p < s.P.length := Decidable.byContradiction fun hge => by
      have hpt := h.holdLt a y p hy ha hp
      obtain ⟨l, hl⟩ := footprint_ne h.parentLt (t.P.length - p) p (Nat.le_refl _) hpt
      have hl' := h.fpNew p l (Nat.le_of_not_lt hge) hl
      obtain ⟨z, hz, -, hlz, -⟩ := eff_present (ne_none_of_allows (hc l hl))
      obtain ⟨z₀, hz₀, hzs, -, -⟩ := h.aOld b z hz hb
      simp only [skel, Prod.mk.injEq] at hzs
      have := hfp b z₀ hz₀ l (by rw [← hzs.2.2.1]; exact hlz)
      omega
    refine ⟨hlt, .held hng hy₀ (by rw [← hsk.2.2.2]; exact ha) (by rw [← hsk.1]; exact hm)
      (hpl p hp hpo) hbx fun l hl => ?_⟩
    have hl' : l ∈ footprint t.P p := (h.fpOld p hpo l).2 hl
    rw [← h.eff b l hb (mem_footprint.1 hl).1]
    exact hc l hl'

/-! ## The creation phase and the transfer phases -/

/-- A leaf of the footprint of `q` is `q` or one of its parts (Spec 1 §40), so not below it. -/
theorem fp_ge {P : List Place} {q l : Nat} (h : l ∈ footprint P q) : q ≤ l := by
  obtain ⟨-, -, -, h | h⟩ := mem_footprint.1 h
  · omega
  · exact Nat.le_of_lt (chain_lt h)

/-- Authorities appended without origin are no descendants: they leave the effective modes of the
existing authorities unchanged (Spec 1 §43). -/
theorem effective_append_none {u v : S3} {N : List Authority} (hA : u.A = v.A ++ N)
    (hN : ∀ z ∈ N, z.origin = none) {b : Nat} (hb : b < v.A.length) (l : Nat) :
    effective u b l = effective v b l := by
  have hold : ∀ j, j < v.A.length → u.A[j]? = v.A[j]? := fun j hj => by
    rw [hA, List.getElem?_append_left hj]
  have horg : ∀ j, j < v.A.length → u.org j = v.org j := fun j hj => by
    show (u.A[j]?).bind (·.origin) = (v.A[j]?).bind (·.origin); rw [hold j hj]
  have hd : descModes u b l = descModes v b l := by
    unfold descModes
    have hlen : u.A.length = v.A.length + N.length := by rw [hA, List.length_append]
    rw [hlen, List.range_add, List.filterMap_append]
    refine (congr (congrArg (· ++ ·) (filterMap_congr' ?_)) (List.filterMap_eq_nil_iff.2 ?_)).trans
      (List.append_nil _)
    · intro j hj
      have hj' := List.mem_range.1 hj
      rw [hold j hj']
      have : u.ancs j = v.ancs j := chain_congr fun i hi => horg i (by omega)
      rw [this]
    · intro j hj
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hj
      split
      · rename_i y hy
        have hy' : y ∈ N := by
          rw [hA, List.getElem?_append_right (by omega)] at hy
          simp only [Nat.add_sub_cancel_left] at hy
          exact List.mem_of_getElem? hy
        have hno : u.org (v.A.length + i) = none := by
          show (u.A[v.A.length + i]?).bind (·.origin) = none; rw [hy]; exact hN y hy'
        simp [S3.ancs, chain_none hno]
      · rfl
  unfold effective; rw [hold b hb, hd]

/-- The current frame of a context with a nonempty stack is the head of its stack (WC5.2 C2). -/
theorem view_top_eq {s : SC} {c : Nat} (hne : s.stk c ≠ []) :
    (s.view c).top = (s.stk c).headD 0 := by
  obtain ⟨f, r, hfr⟩ := List.exists_cons_of_ne_nil hne
  show (s.stk c ++ _).headD 0 = _
  rw [hfr]; rfl

/-- The creation phase of the by-value composite (WC5.2 C5 phase 1) is a phase state. -/
theorem phaseRel_create {s : SC} {c : Nat} {ls : LocalShape}
    (hw₀ : WF3 (spawnCreate s c ls).flat) (hsh : ShapeOK s.P.length ls.toShape)
    (hl : s.Live c) (hne : s.stk c ≠ []) : PhaseRel s c (spawnCreate s c ls) := by
  have hP : (spawnCreate s c ls).P = shapeP s.P (.frame s.nF) ls.toShape := rfl
  have hA : (spawnCreate s c ls).A = (enterEff (s.view c) [] ls).A := rfl
  have hold : ∀ a, a < s.A.length → (spawnCreate s c ls).A[a]? = s.A[a]? := fun a ha => by
    rw [hA, Frames.enter_lt (s := s.view c) ha]
    show ((s.A[a]?).map _) = _
    cases s.A[a]? <;> simp
  have hps := pskel_shapeP (hd := .frame s.nF) hsh
  refine ⟨by rw [hP]; exact hps.1, ?_, fun q o h => (hw₀.parent_lt h).1, fun q hq l => ?_,
    fun q l hq h => Nat.le_trans hq (fp_ge h), fun a y p hy ya hp => ?_, fun a y hy ha => ?_,
    fun a y hy ha => ?_, fun b l hb _ => ?_, ?_⟩
  · rw [hA]; simp only [enterEff, List.length_append, length_mapI]; exact Nat.le_add_right _ _
  · rw [hP]; exact Arena.footprint_shapeP hsh hq l
  · have := hw₀.holders a y hy ya
    rw [hp] at this; exact this.lt
  · rw [hold a ha] at hy
    exact ⟨y, hy, rfl, fun _ h => h, fun _ h _ => h⟩
  · rw [hA] at hy
    rcases Frames.enter_get (s := s.view c) hy with ⟨hlt, -⟩ | ⟨-, i, -, rfl⟩
    · exact absurd ha (by show ¬ s.A.length ≤ a; exact Nat.not_le.2 hlt)
    · rfl
  · have hAeq : (spawnCreate s c ls).flat.A = s.flat.A ++ (rootIdx ls.toShape).map fun i =>
        (⟨.modify, none, footprint (enterP (s.view c) ls) ((s.view c).P.length + i),
          shapeOwner ls.toShape (.frame (s.view c).nF) i, true⟩ : Authority) := by
      show (enterEff (s.view c) [] ls).A = _
      simp only [enterEff]
      rw [mapI_id 0 _ fun _ _ => by simp]
      rfl
    exact effective_append_none hAeq (fun z hz => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hz; rfl) hb l
  · rw [view_top_eq (by rw [stk_spawnCreate hl]; exact hne), view_top_eq hne, stk_spawnCreate hl]

/-- A transfer phase whose destination is a fresh place keeps a phase state (WC5.2 C5 phase 2;
Spec 1 §63 effect). -/
theorem phaseRel_transfer {s t : SC} {c src dst : Nat} (h : PhaseRel s c t)
    (hd : s.P.length ≤ dst) (hdl : dst < t.P.length) :
    PhaseRel s c (transferEffC t c src dst) := by
  have hP : (transferEffC t c src dst).P = (transferEff (t.view c) src dst).P := rfl
  have hget : ∀ j : Nat, (transferEffC t c src dst).A[j]? = (t.A[j]?).map fun (y : Authority) =>
      if heldIn t.P src y.holder then { y with holder := mvTo t.P src dst y.holder } else y :=
    fun j => transfer_A_get (t.view c) src dst j
  have hlenP : (transferEffC t c src dst).P.length = t.P.length := by
    rw [hP, transfer_len]; rfl
  have hpar : parentOf (transferEffC t c src dst).P = parentOf t.P := by
    rw [hP, transfer_parentOf]; rfl
  have hfp : ∀ q, footprint (transferEffC t c src dst).P q = footprint t.P q := fun q => by
    rw [hP, transfer_footprint]; rfl
  refine ⟨by rw [hlenP]; exact h.lenP, ?_, fun q o hq => h.parentLt q o (by rwa [hpar] at hq),
    fun q hq l => by rw [hfp]; exact h.fpOld q hq l, fun q l hq hl => h.fpNew q l hq (by
      rwa [hfp] at hl), fun a y p hy ya hp => ?_, fun a y hy ha => ?_, fun a y hy ha => ?_,
    fun b l hb hl => ?_,
    (show ((transferEffC t c src dst).view c).top = (t.view c).top from rfl).trans h.top⟩
  · have : (transferEffC t c src dst).A.length = t.A.length := by
      show (transferEff (t.view c) src dst).A.length = _; simp [transferEff]; rfl
    rw [this]; exact h.lenA
  · rw [hget] at hy
    obtain ⟨y₁, hy₁, rfl⟩ := Option.map_eq_some_iff.1 hy
    split at hp
    · rename_i hh
      cases hq : y₁.holder with
      | frame f => rw [hq] at hh; exact hh.elim
      | place r =>
        rw [hq] at hp
        obtain ⟨p', hp', -, hlt⟩ := mvTo_ge h.parentLt hd hdl r
        rw [hp'] at hp; cases hp
        rw [hlenP]; exact hlt
    · rw [hlenP]; exact h.holdLt a y₁ p hy₁ (by split at ya <;> simp_all) hp
  · rw [hget] at hy
    obtain ⟨y₁, hy₁, rfl⟩ := Option.map_eq_some_iff.1 hy
    obtain ⟨y₀, hy₀, hsk, hfr, hpl⟩ := h.aOld a y₁ hy₁ ha
    refine ⟨y₀, hy₀, by split <;> exact hsk, fun f hf => ?_, fun p hp hpo => ?_⟩
    · split at hf
      · rename_i hh
        cases hq : y₁.holder with
        | frame f' => rw [hq] at hh; exact hh.elim
        | place r =>
          rw [hq] at hf
          obtain ⟨p', hp', -⟩ := mvTo_ge h.parentLt hd hdl r
          rw [hp'] at hf; cases hf
      · exact hfr f hf
    · split at hp
      · rename_i hh
        cases hq : y₁.holder with
        | frame f' => rw [hq] at hh; exact hh.elim
        | place r =>
          rw [hq] at hp
          obtain ⟨p', hp', hge, -⟩ := mvTo_ge h.parentLt hd hdl r
          rw [hp'] at hp; cases hp
          omega
      · exact hpl p hp hpo
  · rw [hget] at hy
    obtain ⟨y₁, hy₁, rfl⟩ := Option.map_eq_some_iff.1 hy
    have hn := h.aNew a y₁ hy₁ ha
    have : ¬ heldIn t.P src y₁.holder := by rw [hn]; exact id
    simp only [this, ↓reduceIte]; exact hn
  · rw [← h.eff b l hb hl]
    have h1 := (transfer_skel (t.view c) src dst).effective b l
    rw [effective_of_A (t := (transferEffC t c src dst).flat)
      (t' := transferEff (t.view c) src dst) rfl, h1]
    exact effective_of_A rfl b l

/-! ## The capacity on the sources -/

/-- Along the transfer phases, every source has, for every leaf of its footprint in the state
before the step, an authority of the creator attributable without a live `guarded` with
effective `Modify` there (WC5.2 C5.2, C43). -/
theorem phases_cap {s : SC} {reg : SyncReg} {c : Nat}
    (hfp : ∀ (a : Nat) (y : Authority), s.A[a]? = some y → ∀ l ∈ y.footprint, l < s.P.length)
    (htop : s.nF ≠ (s.view c).top) (hne : s.stk c ≠ []) :
    ∀ (t : SC) (vs : List (Nat × Nat)), PhaseRel s c t →
      (∀ v ∈ vs, s.P.length ≤ v.2 ∧ v.2 < t.P.length) → ValRightsG reg c t vs →
      ∀ v ∈ vs, ∀ l ∈ footprint s.P v.1, ∃ x ∈ List.range s.A.length,
        Attr5 s reg c x .modify ∧ Allows (effective s.flat x l) .modify
  | _, [], _, _, _ => fun _ hv => (List.not_mem_nil hv).elim
  | t, w :: vs, h, hd, ⟨⟨hr, _⟩, hrest⟩ => by
    intro v hv l hl
    rcases List.mem_cons.1 hv with rfl | hv
    · obtain ⟨a, -, hx, hall⟩ := hr
      obtain ⟨ha, hx'⟩ := exer5_back h hfp htop hx
      have hl1 := (mem_footprint.1 hl).1
      have hq : v.1 < s.P.length := Nat.lt_of_le_of_lt (fp_ge hl) hl1
      refine ⟨a, List.mem_range.2 ha, Exer5.attr5 hne hx', ?_⟩
      rw [← h.eff a l ha hl1]
      exact hall l ((h.fpOld v.1 hq l).2 hl)
    · obtain ⟨hd1, hd2⟩ := hd w (List.mem_cons_self ..)
      have h' := phaseRel_transfer (src := w.1) h hd1 hd2
      have hlen : (transferEffC t c w.1 w.2).P.length = t.P.length := by
        show (transferEff (t.view c) w.1 w.2).P.length = _; rw [transfer_len]; rfl
      exact phases_cap hfp htop hne _ vs h'
        (fun u hu => by rw [hlen]; exact hd u (List.mem_cons_of_mem _ hu)) hrest v hv l hl

/-- An `ok` by-value `spawn` is executed by a live context under its preconditions (WC5.2 C4,
C5). -/
theorem spawnVal_pre {k : K} {L : MutexLayout} {c : Nat} {ps : List Nat} {ls : LocalShape}
    {vs : List (Nat × Nat)} {st st' : SC × SyncReg × ArenaReg}
    (h : LStep k L (.spawnVal c ps ls vs) st st') :
    st.1.Live c ∧ SpawnValPre k st.1 c ps ls vs := by
  cases h with
  | spawnVal hv => exact ⟨hv.1, (Guarded.ok_iff.1 hv.2).1⟩

/-- Brief of the complement, task 4: on a `RunFull` from the initial state, under `DDSound`, a
by-value `spawn` step of `c` is made with, for every leaf of every source in the state before the
step, an authority attributable to `c` without a live `guarded` with effective `Modify` on it
(WC5.2 C5.2, C43), so with `cap5(c, l) = Modify`. -/
theorem spawnVal_cap_pre {k : K} {L : MutexLayout} {statics : Statics}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} (hdd : DDSound k)
    (hstat : StaticsOK statics) (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], []))
    (h : RunFull k L σ lbls) {i : Nat} (hi : i < lbls.length) {c : Nat} {ps : List Nat}
    {ls : LocalShape} {vs : List (Nat × Nat)} (hl : lbls[i] = .spawnVal c ps ls vs) :
    ∀ v ∈ vs, ∀ l ∈ footprint (σ i).1.P v.1,
      (∃ x ∈ List.range (σ i).1.A.length, Attr5 (σ i).1 (σ i).2.1 c x .modify ∧
        Allows (effective (σ i).1.flat x l) .modify) ∧
      Allows (cap5 (σ i).1 (σ i).2.1 c l) .modify := by
  obtain ⟨hk, -⟩ := runFull_inv hdd hstat h0 h (Nat.le_of_lt hi)
  have hs := (h i hi).2
  have hp := (h i hi).1.2
  rw [hl] at hs hp
  obtain ⟨hlive, hpre⟩ := spawnVal_pre hs
  have hF := hk.parts.1
  have hw := hk.parts.2.1
  have hne := hF.nonempty c hlive
  have hfp : ∀ (a : Nat) (y : Authority), (σ i).1.A[a]? = some y →
      ∀ l ∈ y.footprint, l < (σ i).1.P.length := fun a y hy l hl =>
    (hw.footprints a y hy l hl).1
  have htop : (σ i).1.nF ≠ ((σ i).1.view c).top := by
    intro he
    have hmem : ((σ i).1.view c).top ∈ (σ i).1.frames := by
      have hc : c < (σ i).1.C.length := by
        unfold SC.Live at hlive
        cases hx : (σ i).1.C[c]? with
        | none => rw [hx] at hlive; exact hlive.elim
        | some x => exact (List.getElem?_eq_some_iff.1 hx).1
      exact List.mem_flatMap.2 ⟨c, List.mem_range.2 hc, view_top_mem hne⟩
    have := hF.bound _ hmem
    omega
  have hb₀ := spawn_base (ps := []) (ls := ls) hk hne (fun _ h => by cases h) hpre.localsOK
  have h₀ := phaseRel_create (c := c) hb₀.2.1 hpre.localsOK hlive hne
  have hd : ∀ v ∈ vs, (σ i).1.P.length ≤ v.2 ∧ v.2 < (spawnCreate (σ i).1 c ls).P.length := by
    intro v hv
    obtain ⟨j, hj, he⟩ := hpre.freshDst v hv
    have hjl : j < ls.toShape.length := List.mem_range.1 (List.mem_filter.1 hj).1
    have hlen : (spawnCreate (σ i).1 c ls).P.length = (σ i).1.P.length + ls.toShape.length := by
      show (shapeP (σ i).1.P _ _).length = _; simp [shapeP]
    rw [he, hlen]; exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hjl _⟩
  intro v hv l hl
  obtain ⟨x, hx, hax, hex⟩ := phases_cap hfp htop hne _ vs h₀ hd hp v hv l hl
  exact ⟨⟨x, hx, hax, hex⟩, cap5_of hax hex⟩

end Ern.Concurrency.FullEncap
