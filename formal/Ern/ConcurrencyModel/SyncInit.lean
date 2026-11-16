import Ern.ConcurrencyModel.SyncPreserve
import Ern.ConcurrencyModel.SpawnValuePreserve
import Ern.MemoryModel.Arena

/-!
# Theorem 2, synchronization part: controller uniqueness and initialization (C21.4, C21.7, C22, C23)

Preservation of `SyncState` (`SyncInv`, C21.1–C21.7, with `GrantDiscipline`, C22) by the
labelled steps admitted by `RestrictedStep` (C22.1–C22.3, C22.5), `transfer` and the by-value composite
included.
-/

namespace Ern.ConcurrencyModel

open Ern.MemoryModel.Access

namespace SyncInitAux

open SyncPreserveAux

/-! ## Structural parts (Spec 1 §40, §49.2) -/

section Tree

variable {t : S3}

/-- Structural parthood is transitive (Spec 1 §40). -/
theorem partOf_trans (hw : WF3 t) {a b c : Nat} (hab : partOf t.P a b) (hbc : partOf t.P b c) :
    partOf t.P a c := by
  have hlt : ∀ i o, parentOf t.P i = some o → o < i := fun i o h => (WF3.parent_lt hw h).1
  refine ⟨hab.1, ?_⟩
  rcases hab.2 with rfl | hab'
  · exact hbc.2
  · rcases hbc.2 with rfl | hbc'
    · exact .inr hab'
    · exact .inr (chain_trans hlt (a + 1) a (Nat.lt_succ_self a) b hab' c hbc')

/-- The structural ancestors of a place are totally ordered (Spec 1 §40, §49.2: each place has at
most one structural parent). -/
theorem partOf_total (hw : WF3 t) : ∀ (n l : Nat), l < n → ∀ {a b : Nat},
    partOf t.P l a → partOf t.P l b → partOf t.P a b ∨ partOf t.P b a
  | 0, _, h, _, _, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, l, hl, a, b, ha, hb => by
    rcases ha.2 with rfl | ha'
    · exact .inl hb
    rcases hb.2 with rfl | hb'
    · exact .inr ha
    obtain ⟨p, hp, hpl, hap⟩ := mem_chain ha'
    obtain ⟨p', hp', -, hbp⟩ := mem_chain hb'
    rw [hp] at hp'; cases hp'
    have hpP : p < t.P.length := (WF3.parent_lt hw hp).2
    have ha₁ : partOf t.P p a := ⟨hpP, hap.elim (fun e => .inl e.symm) .inr⟩
    have hb₁ : partOf t.P p b := ⟨hpP, hbp.elim (fun e => .inl e.symm) .inr⟩
    exact partOf_total hw n p (by omega) ha₁ hb₁

/-- Two places sharing a leaf are structurally comparable (Spec 1 §40). -/
theorem footprint_comparable (hw : WF3 t) {a b l : Nat} (ha : l ∈ footprint t.P a)
    (hb : l ∈ footprint t.P b) : partOf t.P a b ∨ partOf t.P b a := by
  obtain ⟨hlP, -, hla⟩ := mem_footprint.1 ha
  obtain ⟨-, -, hlb⟩ := mem_footprint.1 hb
  exact partOf_total hw (l + 1) l (Nat.lt_succ_self l) hla hlb

/-- A strict ancestor of a place with parent `m` is an ancestor of `m` (Spec 1 §40). -/
theorem partOf_parent (hw : WF3 t) {x a m : Nat} (h : partOf t.P x a) (hne : x ≠ a)
    (hm : parentOf t.P x = some m) : partOf t.P m a := by
  obtain ⟨o, ho, -, hor⟩ := mem_chain (h.2.resolve_left hne)
  rw [hm] at ho; cases ho
  exact ⟨(WF3.parent_lt hw hm).2, hor.elim (fun e => .inl e.symm) .inr⟩

/-- A leaf has no strict part (Spec 1 §40). -/
theorem partOf_leaf (hw : WF3 t) : ∀ (n y : Nat), y < n → ∀ {x : Nat}, isLeaf t.P x →
    partOf t.P y x → y = x
  | 0, _, h, _, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, y, hy, x, hx, h => by
    rcases h.2 with e | hc
    · exact e
    obtain ⟨p, hp, hpy, hor⟩ := mem_chain hc
    rcases hor with rfl | hor
    · exact absurd hp (hx y h.1)
    · have := partOf_leaf hw n p (by omega) hx ⟨(WF3.parent_lt hw hp).2, .inr hor⟩
      subst this
      exact absurd hp (hx y h.1)

/-- A leaf in the footprint of a place is a part of it (Spec 1 §40). -/
theorem leaf_mem_footprint {x q : Nat} (hx : isLeaf t.P x) (h : partOf t.P x q) :
    x ∈ footprint t.P q :=
  mem_footprint.2 ⟨h.1, hx, h⟩

/-- A leaf in the footprint of a place is the place or a strict part of it (Spec 1 §40). -/
theorem partOf_of_mem_footprint {x q : Nat} (h : x ∈ footprint t.P q) : partOf t.P x q :=
  (mem_footprint.1 h).2.2

end Tree

/-! ## Corresponding parts of a transfer (Spec 1 §63.2) -/

/-- Membership gives a position (Spec 1 §63.2 `posIn`). -/
theorem getElem?_posIn : ∀ {l : List Nat} {x : Nat}, x ∈ l → l[posIn x l]? = some x
  | [], _, h => by simp at h
  | a :: l, x, h => by
    by_cases e : a = x
    · subst e; simp [posIn]
    · have hx : x ∈ l := (List.mem_cons.1 h).resolve_left (Ne.symm e)
      simp only [posIn, e, ↓reduceIte, List.getElem?_cons_succ]
      exact getElem?_posIn hx

/-- A corresponding part other than `dst` lies strictly below a part of `dst`: its parent is the
place corresponding to the parent of the original part (Spec 1 §63.2 `corr`). -/
theorem corr_parent {P : List Place} {src dst r p x : Nat} (hr : r ≠ src)
    (hp : parentOf P r = some p) (hlt : p < r) (hx : corr P src dst r = some x) :
    ∃ p', corr P src dst p = some p' ∧ parentOf P x = some p' ∧ x < P.length := by
  rw [corr_step hr hp hlt] at hx
  cases hc : corr P src dst p with
  | none => rw [hc] at hx; cases hx
  | some p' =>
    rw [hc, Option.bind_some] at hx
    have hm := mem_kids.1 (List.mem_of_getElem? hx)
    exact ⟨p', rfl, hm.2, hm.1⟩

/-- `corr` is injective on the parts of the source (Spec 1 §63.2: positional correspondence). -/
theorem corr_inj {t : S3} (hw : WF3 t) {src dst : Nat} (hd : dst < t.P.length) :
    ∀ (n r q : Nat), r < n → q < n → ∀ {x : Nat}, corr t.P src dst r = some x →
      corr t.P src dst q = some x → partOf t.P r src → partOf t.P q src → r = q
  | 0, _, _, h, _, _, _, _, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, r, q, hr, hq, x, hxr, hxq, hrs, hqs => by
    -- a part other than `src` corresponds to a strict part of `dst`
    have strict : ∀ {y : Nat}, y < n + 1 → y ≠ src → partOf t.P y src →
        corr t.P src dst y = some x → x ≠ dst := by
      intro y _ hy hys hxy hxd
      obtain ⟨p, hp, hpy, -⟩ := mem_chain (hys.2.resolve_left hy)
      obtain ⟨p', hp', hxp, -⟩ := corr_parent hy hp hpy hxy
      have hpd := corr_partOf hw hd (p + 1) p p' (Nat.lt_succ_self p) hp'
      subst hxd
      have h1 := Ern.MemoryModel.Access.Frames.partOf_le hpd
      have h2 := (WF3.parent_lt hw hxp).1
      omega
    by_cases er : r = src
    · subst er
      rw [corr_src] at hxr; cases hxr
      by_cases eq : q = r
      · exact eq.symm
      · exact absurd rfl (strict hq eq hqs hxq)
    by_cases eq : q = src
    · subst eq
      rw [corr_src] at hxq; cases hxq
      exact absurd rfl (strict hr er hrs hxr)
    obtain ⟨p, hp, hpr, -⟩ := mem_chain (hrs.2.resolve_left er)
    obtain ⟨pq, hpq, hpqq, -⟩ := mem_chain (hqs.2.resolve_left eq)
    obtain ⟨a, ha, hxa, -⟩ := corr_parent er hp hpr hxr
    obtain ⟨b, hb, hxb, -⟩ := corr_parent eq hpq hpqq hxq
    rw [hxa] at hxb; cases hxb
    have hps : partOf t.P p src := partOf_parent hw hrs er hp
    have hpqs : partOf t.P pq src := partOf_parent hw hqs eq hpq
    have hpp : p = pq := corr_inj hw hd n p pq (by omega) (by omega) ha hb hps hpqs
    subst hpp
    rw [corr_step er hp hpr, ha, Option.bind_some] at hxr
    rw [corr_step eq hpq hpqq, ha, Option.bind_some] at hxq
    have hi := posIn_of_getElem (kids_pairwise _ _) hxr
    have hj := posIn_of_getElem (kids_pairwise _ _) hxq
    have hpos : posIn r (kids t.P p) = posIn q (kids t.P p) := by rw [← hi, hj]
    have hr' := getElem?_posIn (mem_kids.2 ⟨hrs.1, hp⟩)
    have hq' := getElem?_posIn (mem_kids.2 ⟨hqs.1, hpq⟩)
    rw [hpos, hq'] at hr'
    cases hr'; rfl

/-- The place corresponding to a leaf of the source is a leaf of the destination (the proof of
`Ern.MemoryModel.Refinement.corr_leaf`, Spec 1 §63.2). -/
theorem corr_leaf' {t : S3} (hw : WF3 t) {src dst l l' : Nat} (hd : dst < t.P.length)
    (hsh : SameShape t.P src dst) (hl : l ∈ footprint t.P src)
    (hc : corr t.P src dst l = some l') : l' ∈ footprint t.P dst ∧ isLeaf t.P l' := by
  obtain ⟨hlP, hlf, hls⟩ := mem_footprint.1 hl
  have hp := corr_partOf hw hd (l + 1) l l' (Nat.lt_succ_self l) hc
  have hk := hsh.1 l (List.mem_range.2 hlP) hls
  rw [hc] at hk; simp only [OptP] at hk
  rw [kids_nil_iff.2 hlf] at hk
  have hleaf := kids_nil_iff.1 (List.eq_nil_of_length_eq_zero hk)
  exact ⟨mem_footprint.2 ⟨hp.1, hleaf, hp⟩, hleaf⟩

/-! ## Steps keeping the `Init` leaves of existing places (Spec 1 §60–§75 effects) -/

/-- A step keeps the footprints of the existing places and their `Init` leaves. -/
structure InitFacts (s s' : SC) : Prop where
  fp : ∀ q, q < s.P.length → ∀ l, l ∈ footprint s'.P q ↔ l ∈ footprint s.P q
  keep : ∀ l, l < s.P.length → s.I l = .init → s'.I l = .init

/-- A step whose places and initialization states are unchanged. -/
theorem initFacts_same {s s' : SC} (hP : s'.P = s.P) (hI : s'.I = s.I) : InitFacts s s' :=
  ⟨fun _ _ _ => by rw [hP], fun _ _ h => by rw [hI]; exact h⟩

/-- A step of the kernel run on the view of `c` keeps the footprints of existing places
(`Ern.MemoryModel.Arena.kstep_fp`). -/
theorem view_fp {k : K} {op : KernelOp} {c : Nat} {s : SC} {t : S3}
    (hR : op.Step k (s.view c) (.ok t)) {q : Nat} (hq : q < s.P.length) (l : Nat) :
    l ∈ footprint (s.set t).P q ↔ l ∈ footprint s.P q :=
  Ern.MemoryModel.Arena.kstep_fp (kstep_iff.2 ⟨op, hR⟩) hq l

/-- The inherited operations O1–O16 executed by a context, other than `transfer` and `endUse`,
keep the footprints of existing places and their `Init` leaves (Spec 1 §60–§75 effects
re-indexed: only `store`, `write`, `writeShared` change initialization states of existing places,
to `Init`; `enterFrame` and `alloc` append `Uninit` places). -/
theorem opStep_init {k : K} {c : Nat} {op : KernelOp} {s s' : SC}
    (h : opStepC k op c s (.ok s')) (hnt : ∀ src dst, op ≠ .transfer src dst)
    (hne : ∀ p, op ≠ .endUse p) : InitFacts s s' := by
  cases op with
  | transfer src dst => exact absurd rfl (hnt src dst)
  | endUse p => exact absurd rfl (hne p)
  | depend q x =>
    obtain ⟨-, h⟩ := h; obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; exact initFacts_same rfl rfl
  | store a p =>
    obtain ⟨-, h⟩ := h; obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
    have hd := hpre.derivedHeld
    unfold OptP at hd; split at hd
    · rename_i y hy
      have hP : (storeEffC s c a p).P = s.P := by
        show (storeEff (s.view c) a p).P = _; simp [storeEff, hy]; rfl
      have hI : (storeEffC s c a p).I = fun l => if l = p then .init else s.I l := by
        show (storeEff (s.view c) a p).I = _; simp [storeEff, hy]; rfl
      refine ⟨fun _ _ _ => by rw [hP], fun l _ hl => ?_⟩
      rw [hI]
      show (if l = p then InitSt.init else s.I l) = .init
      split
      · rfl
      · exact hl
    · exact hd.elim
  | enter ps ls =>
    obtain ⟨-, h⟩ := h; obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
    refine ⟨fun q hq l => Ern.MemoryModel.Arena.footprint_shapeP hpre.localsOK hq l,
      fun l hl hi => ?_⟩
    show (if (s.view c).P.length ≤ l then InitSt.uninit else s.I l) = .init
    have hn : ¬ (s.view c).P.length ≤ l := Nat.not_le.2 hl
    simp only [hn, ↓reduceIte]; exact hi
  | exit =>
    obtain ⟨-, h⟩ := h; obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; exact initFacts_same rfl rfl
  | derive src region m =>
    obtain ⟨t, hR, rfl⟩ := viewStep_ok h
    refine ⟨fun q hq l => view_fp hR hq l, fun l _ hl => ?_⟩
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hR; exact hl
  | split src rs =>
    obtain ⟨t, hR, rfl⟩ := viewStep_ok h
    refine ⟨fun q hq l => view_fp hR hq l, fun l _ hl => ?_⟩
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hR; exact hl
  | release a =>
    obtain ⟨t, hR, rfl⟩ := viewStep_ok h
    refine ⟨fun q hq l => view_fp hR hq l, fun l _ hl => ?_⟩
    obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 hR
    obtain ⟨x, hx, -⟩ := hpre.active
    show (releaseEff (s.view c) a).I l = .init
    rw [releaseEff_eq hx]; exact hl
  | read a ls =>
    obtain ⟨t, hR, rfl⟩ := viewStep_ok h
    refine ⟨fun q hq l => view_fp hR hq l, fun l _ hl => ?_⟩
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hR; exact hl
  | write a ls =>
    obtain ⟨t, hR, rfl⟩ := viewStep_ok h
    refine ⟨fun q hq l => view_fp hR hq l, fun l _ hl => ?_⟩
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hR
    show (if l ∈ ls then InitSt.init else s.I l) = .init
    split
    · rfl
    · exact hl
  | writeShared a ls =>
    obtain ⟨t, hR, rfl⟩ := viewStep_ok h
    refine ⟨fun q hq l => view_fp hR hq l, fun l _ hl => ?_⟩
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hR
    show (if l ∈ ls then InitSt.init else s.I l) = .init
    split
    · rfl
    · exact hl
  | pin p =>
    obtain ⟨t, hR, rfl⟩ := viewStep_ok h
    refine ⟨fun q hq l => view_fp hR hq l, fun l _ hl => ?_⟩
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hR; exact hl
  | unpin o =>
    obtain ⟨t, hR, rfl⟩ := viewStep_ok h
    refine ⟨fun q hq l => view_fp hR hq l, fun l _ hl => ?_⟩
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hR; exact hl
  | free p auth =>
    obtain ⟨t, hR, rfl⟩ := viewStep_ok h
    refine ⟨fun q hq l => view_fp hR hq l, fun l _ hl => ?_⟩
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hR; exact hl
  | alloc pr ow ls =>
    obtain ⟨t, hR, rfl⟩ := viewStep_ok h
    refine ⟨fun q hq l => view_fp hR hq l, fun l hlP hl => ?_⟩
    change AllocStep k pr ow ls (s.view c) (.ok t) at hR
    cases hR with
    | ok _ _ =>
      show (if (s.view c).P.length ≤ l then InitSt.uninit else s.I l) = .init
      have hn : ¬ (s.view c).P.length ≤ l := Nat.not_le.2 hlP
      simp only [hn, ↓reduceIte]; exact hl

/-- `spawn` and the creation phase of the by-value composite keep the footprints of existing
places and their `Init` leaves (C4 effect, Spec 1 §72 effect). -/
theorem spawn_init {s : SC} {c : Nat} {ps : List Nat} {ls : LocalShape}
    (hsh : ShapeOK s.P.length ls.toShape) : InitFacts s (spawnEff s c ps ls) := by
  refine ⟨fun q hq l => Ern.MemoryModel.Arena.footprint_shapeP hsh hq l, fun l hl hi => ?_⟩
  show (if (s.view c).P.length ≤ l then InitSt.uninit else s.I l) = .init
  have hn : ¬ (s.view c).P.length ≤ l := Nat.not_le.2 hl
  simp only [hn, ↓reduceIte]; exact hi

/-- The initialization invariant (C21.7) across a step with an unchanged registry that keeps
holders of places, parents, footprints and `Init` leaves. -/
theorem init_step {L : MutexLayout} {reg : SyncReg} {s s' : SC} (hsk : Skel s s')
    (hh₀ : HoldSame s s') (hP : PSkel s.P s'.P)
    (hi : InitFacts s s') (hw : WF3 s.flat) (hs : SyncCore L s reg) (hsi : SlotInit s reg)
    (hci : CtlInit L s reg) : SlotInit s' reg ∧ CtlInit L s' reg := by
  refine ⟨fun e he hl => ?_, fun e he hl => ?_⟩
  · have heo := hs.1 e he
    have hl₀ := hsk.active heo.bound hl
    have h1 := heo.guarded hl₀
    have h2 := hsi e he hl₀
    cases hy : s.A[e.guarded]? with
    | none => rw [hy] at h1; exact h1.elim
    | some y =>
      rw [hy] at h1
      simp only [OptP] at h1
      cases hh : y.holder with
      | frame f => rw [hh] at h1; exact h1.2.elim
      | place q =>
        have hsl : slotOf s e.guarded = some q := by simp [slotOf, hy, hh]
        rw [hsl] at h2
        obtain ⟨y', hy'⟩ := getElem?_of_lt (Nat.lt_of_lt_of_le heo.bound hsk.len)
        have hh' : y'.holder = .place q := by rw [hh₀ _ y y' q hy hy' hh, hh]
        have hsl' : slotOf s' e.guarded = some q := by simp [slotOf, hy', hh']
        rw [hsl']
        have hq : q < s.P.length := by
          have := h1.2; rw [hh] at this; exact this.lt
        intro l hl'
        have hl₁ := (hi.fp q hq l).1 hl'
        exact hi.keep l (mem_footprint.1 hl₁).1 (h2 l hl₁)
  · have heo := hs.1 e he
    have hl₀ := hsk.active heo.bound hl
    have h3 := heo.control hl₀
    have h4 := hci e he hl₀
    cases hc : ControlOf L s e with
    | none => rw [hc] at h3; exact h3.elim
    | some ctl =>
      rw [hc] at h3 h4
      simp only [OptP] at h3 h4
      rw [ctl_same_eq hw hP (Nat.lt_of_lt_of_le heo.bound hsk.len) hh₀ hc]
      exact hi.keep ctl h3.1.lt h4

/-- `SyncPart` across a step with an unchanged registry described by `StepFacts` and
`InitFacts`. -/
theorem facts_syncState {L : MutexLayout} {reg : SyncReg} {s s' : SC} (hf : StepFacts reg s s')
    (hi : InitFacts s s') (hw : WF3 s.flat) (hw' : WF3 s'.flat) (hs : SyncPart L s reg) :
    SyncPart L s' reg := by
  obtain ⟨hc, hu, hsi, hci⟩ := hs
  obtain ⟨hsi', hci'⟩ := init_step hf.skel hf.hold hf.pskel hi hw hc hsi hci
  exact ⟨kernel_step_same hf.skel hf.hold hf.pskel hw hw' hc hf.src,
    facts_ctlUnique hf hw hc hu, hsi', hci'⟩

/-! ## `endUse` (Spec 1 §69; C22.5) -/

/-- An authority active after `endUse p` was not held within `p` (Spec 1 §69 effect). -/
theorem endUse_active {v : S3} {p j : Nat} {y' : Authority}
    (hy : (endUseEff v p).A[j]? = some y') (ha : y'.active = true) :
    ∃ y, v.A[j]? = some y ∧ ¬ heldIn v.P p y.holder := by
  have e1 : (endUseEff v p).A[j]? = ((endUseS v p).A[j]?).map (fun y =>
      if HolderLive (endUseS v p) y.holder then y else { y with active := false }) := by
    simp only [endUseEff, cleanup, List.getElem?_map]
  have e2 : (endUseS v p).A[j]? = (v.A[j]?).map (fun y =>
      if heldIn v.P p y.holder then { y with active := false } else y) := by
    simp only [endUseS, List.getElem?_map]
  rw [e1, e2] at hy
  cases hv : v.A[j]? with
  | none => rw [hv] at hy; cases hy
  | some y =>
    rw [hv] at hy
    refine ⟨y, rfl, fun hh => ?_⟩
    simp only [Option.map_some, hh, ↓reduceIte, Option.some.injEq] at hy
    subst hy
    by_cases hL : HolderLive (endUseS v p) y.holder
    · simp [hL] at ha
    · simp [hL] at ha

/-- `endUse` (Spec 1 §69) preserves `SyncPart` under `RestrictedStep` (C22.5). -/
theorem endUse_syncState {k : K} {L : MutexLayout} {reg : SyncReg} {ar : ArenaReg} {c p : Nat}
    {s s' : SC} (h : opStepC k (.endUse p) c s (.ok s'))
    (he : RestrictedStep L (s, reg, ar) (.kernel c (.endUse p)))
    (hw : WF3 s.flat) (hw' : WF3 s'.flat) (hs : SyncPart L s reg) : SyncPart L s' reg := by
  have hx : ∀ e ∈ reg, e.Live s → ControlOf L s e ≠ some p ∧
      OptP (slotOf s e.guarded) (fun q => partOf s.P p q → p = q) True := he
  have hf := opStep_facts (reg := reg) h he (fun _ _ h => by cases h) hw
  obtain ⟨hc, hu, hsi, hci⟩ := hs
  obtain ⟨t, hR, rfl⟩ := viewStep_ok h
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hR
  have hI : ∀ l, (s.set (endUseEff (s.view c) p)).I l =
      if l ∈ footprint s.P p then .uninit else s.I l := fun _ => rfl
  -- the slot of a live entry after the step is not within `p`
  have hslot : ∀ e ∈ reg, e.Live (s.set (endUseEff (s.view c) p)) →
      ∃ y q, s.A[e.guarded]? = some y ∧ y.holder = .place q ∧ ¬ partOf s.P q p ∧
        slotOf s e.guarded = some q ∧
        slotOf (s.set (endUseEff (s.view c) p)) e.guarded = some q := by
    intro e he' hl
    have heo := hc.1 e he'
    have hl₀ := hf.skel.active heo.bound hl
    obtain ⟨y', hy', ya'⟩ := hl
    obtain ⟨y, hy, hnh⟩ := endUse_active (v := s.view c) hy' ya'
    have h1 := heo.guarded hl₀
    have hy₀ : s.A[e.guarded]? = some y := hy
    rw [hy₀] at h1; simp only [OptP] at h1
    cases hh : y.holder with
    | frame f => rw [hh] at h1; exact h1.2.elim
    | place q =>
      have hh' : y'.holder = .place q := by rw [hf.hold _ y y' q hy₀ hy' hh, hh]
      refine ⟨y, q, hy₀, hh, fun hq => hnh (by rw [hh]; exact hq), by simp [slotOf, hy₀, hh],
        by simp [slotOf, show (s.set (endUseEff (s.view c) p)).A[e.guarded]? = some y' from hy',
          hh']⟩
  refine ⟨kernel_step_same hf.skel hf.hold hf.pskel hw hw' hc hf.src,
    facts_ctlUnique hf hw hc hu, fun e he' hl => ?_, fun e he' hl => ?_⟩
  · obtain ⟨y, q, hy, hh, hnq, hsl, hsl'⟩ := hslot e he' hl
    have hl₀ := hf.skel.active (hc.1 e he').bound hl
    have h2 := hsi e he' hl₀
    rw [hsl] at h2
    rw [hsl']
    intro l hl'
    rw [hI]
    have hnot : l ∉ footprint s.P p := fun hp => by
      have hx' := (hx e he' hl₀).2
      rw [hsl] at hx'
      rcases footprint_comparable (t := s.flat) hw hl' hp with h₁ | h₁
      · exact hnq h₁
      · have e' := hx' h₁
        subst e'
        exact hnq h₁
    simp only [hnot, ↓reduceIte]
    exact h2 l hl'
  · obtain ⟨y, q, hy, hh, hnq, -, -⟩ := hslot e he' hl
    have heo := hc.1 e he'
    have hl₀ := hf.skel.active heo.bound hl
    have h3 := heo.control hl₀
    have h4 := hci e he' hl₀
    cases hco : ControlOf L s e with
    | none => rw [hco] at h3; exact h3.elim
    | some ctl =>
      rw [hco] at h3 h4; simp only [OptP] at h3 h4
      rw [ctl_same_eq hw hf.pskel (Nat.lt_of_lt_of_le heo.bound hf.skel.len) hf.hold hco]
      show (s.set (endUseEff (s.view c) p)).I ctl = .init
      rw [hI]
      have hnot : ctl ∉ footprint s.P p := fun hp => by
        have hcp := partOf_of_mem_footprint (t := s.flat) hp
        have hne : ctl ≠ p := fun e' => (hx e he' hl₀).1 (by rw [hco, e'])
        obtain ⟨y₁, hp₁, m, hy₁, hh₁, hm, -, hkc⟩ := controlOf_spec hco
        rw [hy] at hy₁; cases hy₁
        rw [hh] at hh₁; cases hh₁
        have hcm : parentOf s.P ctl = some m := (mem_kids.1 (List.mem_of_getElem? hkc)).2
        have hmp := partOf_parent (t := s.flat) hw hcp hne hcm
        have hqP : q < s.P.length := by
          have h1 := heo.guarded hl₀
          rw [hy] at h1; simp only [OptP] at h1
          have := h1.2; rw [hh] at this; exact this.lt
        have hqm : partOf s.P q m := ⟨hqP, .inr (by
          rw [chain_cons hm (WF3.parent_lt (s := s.flat) hw hm).1]; exact List.mem_cons_self ..)⟩
        exact hnq (partOf_trans (t := s.flat) hw hqm hmp)
      simp only [hnot, ↓reduceIte]
      exact h4

/-! ## `transfer` (Spec 1 §63; C22.3) -/

/-- The controller after a `transfer` whose source is not the place holding `guarded`: the
corresponding part of the controller when the mutex value moves, the controller itself otherwise
(Spec 1 §63.2 `corr`, C12 positional `ControlOf`; the proof of `ctl_transfer`). -/
theorem ctl_transfer_eq {L : MutexLayout} {s : SC} {c src dst : Nat} {e : SyncEntry}
    (hw : WF3 s.flat) (hss : SameShape s.P src dst)
    (henc : (s.A[e.guarded]?).map (·.holder) ≠ some (.place src)) {ctl : Nat}
    (hc : ControlOf L s e = some ctl) :
    ∃ y hp m, s.A[e.guarded]? = some y ∧ y.holder = .place hp ∧ parentOf s.P hp = some m ∧
      parentOf s.P ctl = some m ∧
      ((partOf s.P hp src ∧ partOf s.P ctl src ∧
          ControlOf L (transferEffC s c src dst) e = corr s.P src dst ctl) ∨
        (¬ partOf s.P hp src ∧ ControlOf L (transferEffC s c src dst) e = some ctl)) := by
  obtain ⟨y, hp, m, hy, hph, hm, hk, hkc⟩ := controlOf_spec hc
  have hpar : parentOf (transferEffC s c src dst).P = parentOf s.P :=
    transfer_parentOf (s.view c) src dst
  have hkids : ∀ x, kids (transferEffC s c src dst).P x = kids s.P x :=
    transfer_kids (s.view c) src dst
  have hA' : (transferEffC s c src dst).A[e.guarded]? = some
      (if heldIn s.P src y.holder then { y with holder := mvTo s.P src dst y.holder } else y) := by
    have hy2 : (s.view c).A[e.guarded]? = some y := hy
    show (transferEff (s.view c) src dst).A[e.guarded]? = _
    rw [transfer_A_get, hy2]; rfl
  have hmlt := WF3.parent_lt (s := s.flat) hw hm
  have hcm : parentOf s.P ctl = some m := (mem_kids.1 (List.mem_of_getElem? hkc)).2
  have hcP : ctl < s.P.length := (mem_kids.1 (List.mem_of_getElem? hkc)).1
  have hmc := (WF3.parent_lt (s := s.flat) hw hcm).1
  refine ⟨y, hp, m, hy, hph, hm, hcm, ?_⟩
  by_cases hin : partOf s.P hp src
  · have hne : hp ≠ src := fun e' => henc (by simp [hy, hph, e'])
    obtain ⟨o, ho, -, hor⟩ := mem_chain (hin.2.resolve_left hne)
    rw [hm] at ho; cases ho
    have hmsrc : partOf s.P m src := ⟨hmlt.2, hor.elim (fun e => .inl e.symm) .inr⟩
    have hcsrc : partOf s.P ctl src := partOf_child hcP hcm hmc hmsrc
    refine .inl ⟨hin, hcsrc, ?_⟩
    have hss1 := hss.1 m (List.mem_range.2 hmlt.2) hmsrc
    unfold OptP at hss1; split at hss1
    · rename_i m' hm'
      have hgp : posIn hp (kids s.P m) = L.guardedField := posIn_of_getElem (kids_pairwise _ _) hk
      have hcp : posIn ctl (kids s.P m) = L.controlField :=
        posIn_of_getElem (kids_pairwise _ _) hkc
      have hlen' : L.guardedField < (kids s.P m').length := by
        rw [hss1]; exact lt_of_getElem? hk
      obtain ⟨h', hh'⟩ := getElem?_of_lt hlen'
      have hcorr : corr s.P src dst hp = some h' := by
        rw [corr_step hne hm hmlt.1, hm', Option.bind_some, hgp, hh']
      have hcne : ctl ≠ src := fun e' => by
        have := Frames.partOf_le hmsrc; omega
      have hcorrc : corr s.P src dst ctl = (kids s.P m')[L.controlField]? := by
        rw [corr_step hcne hcm hmc, hm', Option.bind_some, hcp]
      have hh'm : parentOf s.P h' = some m' := (mem_kids.1 (List.mem_of_getElem? hh')).2
      rw [controlOf_of (y := { y with holder := mvTo s.P src dst y.holder }) (hp := h') (m := m')
          (by rw [hA']; simp only [show heldIn s.P src y.holder by rw [hph]; exact hin,
            ↓reduceIte])
          (by rw [hph]; simp [mvTo, hcorr])
          (by rw [hpar]; exact hh'm) (by rw [hkids]; exact hh'), hkids, hcorrc]
    · exact hss1.elim
  · refine .inr ⟨hin, ?_⟩
    have hin' : ¬ heldIn s.P src y.holder := by rw [hph]; exact hin
    rw [controlOf_of (y := y) (hp := hp) (m := m) (by rw [hA']; simp only [hin', ↓reduceIte]) hph
      (by rw [hpar]; exact hm) (by rw [hkids]; exact hk), hkids, hkc]

/-- Liveness is unchanged by a transfer (Spec 1 §63 effect: holders change, activity does not). -/
theorem transfer_live {s : SC} {c src dst : Nat} {e : SyncEntry} :
    e.Live (transferEffC s c src dst) ↔ e.Live s := by
  unfold SyncEntry.Live
  have hget : (transferEffC s c src dst).A[e.guarded]? = (s.A[e.guarded]?).map fun y =>
      if heldIn s.P src y.holder then { y with holder := mvTo s.P src dst y.holder } else y :=
    transfer_A_get (s.view c) src dst e.guarded
  constructor
  · rintro ⟨y', hy', ya'⟩
    change (transferEffC s c src dst).A[e.guarded]? = some y' at hy'
    rw [hget] at hy'
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hy'
    exact ⟨y, hy, by split at ya' <;> exact ya'⟩
  · rintro ⟨y, hy, ya⟩
    have hy' : s.A[e.guarded]? = some y := hy
    refine ⟨if heldIn s.P src y.holder then { y with holder := mvTo s.P src dst y.holder } else y,
      ?_, ?_⟩
    · show (transferEffC s c src dst).A[e.guarded]? = _
      rw [hget, hy']; rfl
    · split <;> exact ya

/-- The controller of a live entry across a transfer admitted by C22.3 whose destination
has no `Init` leaf (Spec 1 §63.3): either it moves to the corresponding leaf of the destination,
or it stays and lies outside the source and the destination. -/
theorem transfer_ctl_cases {L : MutexLayout} {reg : SyncReg} {c src dst : Nat} {s : SC}
    {e : SyncEntry} (hss : SameShape s.P src dst) (hdni : ∀ l ∈ footprint s.P dst, s.I l ≠ .init)
    (hd : dst < s.P.length) (hx : TransferExcl L (s, reg) src) (hw : WF3 s.flat)
    (hc : SyncCore L s reg) (hci : CtlInit L s reg) (he : e ∈ reg) (hl : e.Live s) {ctl : Nat}
    (hco : ControlOf L s e = some ctl) :
    (partOf s.P ctl src ∧ ∃ ctl', corr s.P src dst ctl = some ctl' ∧
        ControlOf L (transferEffC s c src dst) e = some ctl' ∧ ctl' ∈ footprint s.P dst) ∨
      (ControlOf L (transferEffC s c src dst) e = some ctl ∧ ctl ∉ footprint s.P src ∧
        ctl ∉ footprint s.P dst) := by
  have h3 := (hc.1 e he).control hl
  rw [hco] at h3; simp only [OptP] at h3
  have h4 := hci e he hl
  rw [hco] at h4; simp only [OptP] at h4
  obtain ⟨y, hp, m, hy, hph, hm, hcm, hcase⟩ :=
    ctl_transfer_eq (c := c) hw hss (holder_ne_of_excl hx hc e he hl) hco
  rcases hcase with ⟨-, hcs, hc'⟩ | ⟨hnp, hc'⟩
  · have hcf : ctl ∈ footprint s.P src := mem_footprint.2 ⟨h3.1.lt, h3.2, hcs⟩
    have hk := hss.1 ctl (List.mem_range.2 h3.1.lt) hcs
    cases hcc : corr s.P src dst ctl with
    | none => rw [hcc] at hk; exact hk.elim
    | some ctl' =>
      exact .inl ⟨hcs, ctl', rfl, by rw [hc', hcc],
        (corr_leaf' (t := s.flat) hw hd hss hcf hcc).1⟩
  · refine .inr ⟨hc', fun hcf => ?_, fun hcd => hdni ctl hcd h4⟩
    have hcs := partOf_of_mem_footprint (t := s.flat) hcf
    by_cases hne : ctl = src
    · exact (hx e he hl).2 (by rw [hco, hne])
    · have hms := partOf_parent (t := s.flat) hw hcs hne hcm
      have hpP : hp < s.P.length := by
        have h1 := (hc.1 e he).guarded hl
        rw [hy] at h1; simp only [OptP] at h1
        have := h1.2; rw [hph] at this; exact this.lt
      have hpm : partOf s.P hp m := ⟨hpP, .inr (by
        rw [chain_cons hm (WF3.parent_lt (s := s.flat) hw hm).1]; exact List.mem_cons_self ..)⟩
      exact hnp (partOf_trans (t := s.flat) hw hpm hms)

/-- `transfer` executed by `c` (Spec 1 §63 effect) preserves `SyncPart` when it is admitted by
C22.3, the shapes match (§63.2) and no destination leaf is `Init` (§63.3). -/
theorem transfer_syncState {L : MutexLayout} {reg : SyncReg} {c src dst : Nat} {s : SC}
    (hss : SameShape s.P src dst) (hdni : ∀ l ∈ footprint s.P dst, s.I l ≠ .init)
    (hd : dst < s.P.length) (hx : TransferExcl L (s, reg) src) (hw : WF3 s.flat)
    (hw' : WF3 (transferEffC s c src dst).flat) (hs : SyncPart L s reg) :
    SyncPart L (transferEffC s c src dst) reg := by
  obtain ⟨hc, hu, hsi, hci⟩ := hs
  have hcore := transfer_core (c := c) hss (holder_ne_of_excl hx hc) hw hw' hc
  have hI : ∀ l, (transferEffC s c src dst).I l = if l ∈ footprint s.P dst then .init
      else if l ∈ footprint s.P src then .moved else s.I l := fun _ => rfl
  have hctlI : ∀ e ∈ reg, e.Live s → ∀ ctl, ControlOf L s e = some ctl →
      ∃ c', ControlOf L (transferEffC s c src dst) e = some c' ∧
        (transferEffC s c src dst).I c' = .init := by
    intro e he hl ctl hco
    have h4 := hci e he hl
    rw [hco] at h4; simp only [OptP] at h4
    rcases transfer_ctl_cases hss hdni hd hx hw hc hci he hl hco with
      ⟨-, ctl', -, hc', hcd⟩ | ⟨hc', hns, hnd⟩
    · exact ⟨ctl', hc', by rw [hI]; simp [hcd]⟩
    · exact ⟨ctl, hc', by rw [hI]; simp [hns, hnd, h4]⟩
  refine ⟨hcore, fun i j e f c₀ hi hj hl hl' h1 h2 => ?_, fun e he hl => ?_,
    fun e he hl => ?_⟩
  · -- controller uniqueness (C21.4)
    have hl₀ := transfer_live.1 hl
    have hl₀' := transfer_live.1 hl'
    have he := List.mem_of_getElem? hi
    have hf := List.mem_of_getElem? hj
    have h3e := (hc.1 e he).control hl₀
    have h3f := (hc.1 f hf).control hl₀'
    cases hce : ControlOf L s e with
    | none => rw [hce] at h3e; exact h3e.elim
    | some ce =>
      cases hcf : ControlOf L s f with
      | none => rw [hcf] at h3f; exact h3f.elim
      | some cf =>
        rcases transfer_ctl_cases hss hdni hd hx hw hc hci he hl₀ hce with
          ⟨hes, ce', hce', hce'', hced⟩ | ⟨hce'', -, hcend⟩ <;>
        rcases transfer_ctl_cases hss hdni hd hx hw hc hci hf hl₀' hcf with
          ⟨hfs, cf', hcf', hcf'', hcfd⟩ | ⟨hcf'', -, hcfnd⟩
        · rw [hce''] at h1; rw [hcf''] at h2; cases h1; cases h2
          have := corr_inj (t := s.flat) hw hd (ce + cf + 1) ce cf (by omega) (by omega)
            hce' hcf' hes hfs
          subst this
          exact hu i j e f _ hi hj hl₀ hl₀' hce hcf
        · rw [hce''] at h1; rw [hcf''] at h2; cases h1; cases h2
          exact (hcfnd hced).elim
        · rw [hce''] at h1; rw [hcf''] at h2; cases h1; cases h2
          exact (hcend hcfd).elim
        · rw [hce''] at h1; rw [hcf''] at h2; cases h1; cases h2
          exact hu i j e f _ hi hj hl₀ hl₀' hce hcf
  · -- `slot` stays `Init` (C21.7)
    have hl₀ := transfer_live.1 hl
    have heo := hc.1 e he
    have h1 := heo.guarded hl₀
    have h2 := hsi e he hl₀
    cases hy : s.A[e.guarded]? with
    | none => rw [hy] at h1; exact h1.elim
    | some y =>
      rw [hy] at h1; simp only [OptP] at h1
      cases hh : y.holder with
      | frame f => rw [hh] at h1; exact h1.2.elim
      | place q =>
        have hsl : slotOf s e.guarded = some q := by simp [slotOf, hy, hh]
        rw [hsl] at h2; simp only [OptP] at h2
        have hqP : q < s.P.length := by have := h1.2; rw [hh] at this; exact this.lt
        have hA' : (transferEffC s c src dst).A[e.guarded]? = some
            (if heldIn s.P src y.holder then { y with holder := mvTo s.P src dst y.holder }
              else y) := by
          have hy2 : (s.view c).A[e.guarded]? = some y := hy
          show (transferEff (s.view c) src dst).A[e.guarded]? = _
          rw [transfer_A_get, hy2]; rfl
        by_cases hin : partOf s.P q src
        · have hk := hss.1 q (List.mem_range.2 hqP) hin
          cases hcq : corr s.P src dst q with
          | none => rw [hcq] at hk; exact hk.elim
          | some q' =>
            have hsl' : slotOf (transferEffC s c src dst) e.guarded = some q' := by
              simp only [slotOf, hA', hh, show heldIn s.P src (.place q) from hin, ↓reduceIte,
                Option.map_some, mvTo, hcq, Option.getD_some]
            rw [hsl']; simp only [OptP]
            have hq'd := corr_partOf (s := s.flat) hw hd (q + 1) q q' (Nat.lt_succ_self q) hcq
            intro l hl'
            rw [show footprint (transferEffC s c src dst).P q' = footprint s.P q' from
              transfer_footprint (s.view c) src dst q'] at hl'
            obtain ⟨hlP, hlf, hlq⟩ := mem_footprint.1 hl'
            have hld : l ∈ footprint s.P dst :=
              mem_footprint.2 ⟨hlP, hlf, partOf_trans (t := s.flat) hw hlq hq'd⟩
            rw [hI]; simp [hld]
        · have hsl' : slotOf (transferEffC s c src dst) e.guarded = some q := by
            simp only [slotOf, hA', hh, show ¬ heldIn s.P src (.place q) from hin, ↓reduceIte,
              Option.map_some]
          rw [hsl']; simp only [OptP]
          intro l hl'
          rw [show footprint (transferEffC s c src dst).P q = footprint s.P q from
            transfer_footprint (s.view c) src dst q] at hl'
          rw [hI]
          by_cases hld : l ∈ footprint s.P dst
          · simp [hld]
          · have hls : l ∉ footprint s.P src := fun hls => by
              rcases footprint_comparable (t := s.flat) hw hl' hls with h₁ | h₁
              · exact hin h₁
              · have := (hx e he hl₀).1
                rw [hsl] at this
                exact this h₁
            simp [hld, hls, h2 l hl']
  · -- the controller stays `Init` (C21.7)
    have hl₀ := transfer_live.1 hl
    have h3 := (hc.1 e he).control hl₀
    cases hco : ControlOf L s e with
    | none => rw [hco] at h3; exact h3.elim
    | some ctl =>
      obtain ⟨c', hc', hi'⟩ := hctlI e he hl₀ ctl hco
      rw [hc']; exact hi'

/-! ## Library operations (C13, C16–C18) -/

/-- The initialization invariant after a record update keeping `guarded` (C21.7). -/
theorem init_set {L : MutexLayout} {s : SC} {reg : SyncReg} {i : Nat} {e e' : SyncEntry}
    (hi : reg[i]? = some e) (hg : e'.guarded = e.guarded) (hsi : SlotInit s reg)
    (hci : CtlInit L s reg) : SlotInit s (reg.set i e') ∧ CtlInit L s (reg.set i e') := by
  have he := List.mem_of_getElem? hi
  obtain ⟨hC, hL⟩ := controlOf_guarded (L := L) (s := s) hg
  refine ⟨fun x hx hl => ?_, fun x hx hl => ?_⟩
  · rcases mem_set_cases hx with rfl | ⟨j, hj, -⟩
    · rw [hg]; exact hsi e he (hL.1 hl)
    · exact hsi x (List.mem_of_getElem? hj) hl
  · rcases mem_set_cases hx with rfl | ⟨j, hj, -⟩
    · rw [hC]; exact hci e he (hL.1 hl)
    · exact hci x (List.mem_of_getElem? hj) hl

/-- `newMutex` (C13; C13.10: `initM`) preserves `SyncPart`. -/
theorem newMutex_syncState {k : K} {L : MutexLayout} {ar : ArenaReg} {s : SC} {reg : SyncReg}
    {c g : Nat} {st' : SC × SyncReg} (h : NewMutexOk k L ar s reg c g st') (hw : WF3 s.flat)
    (hs : SyncPart L s reg) : SyncPart L st'.1 st'.2 := by
  obtain ⟨hc, hu, hsi, hci⟩ := hs
  have hcore := newMutex_preserves h hc
  have hcu := newMutex_ctlUnique h hu
  obtain ⟨-, hpre, rfl⟩ := h
  have h1 := hpre.control
  cases hco : ControlOf L s ⟨g, none⟩ with
  | none => rw [hco] at h1; exact h1.elim
  | some ctl =>
    rw [hco] at h1; simp only [OptP] at h1
    obtain ⟨y, q, m, hy, hh, hm, -, hkc⟩ := controlOf_spec hco
    have hy' : s.A[g]? = some y := hy
    have hmu : mutexOf s g = some m := by simp [mutexOf, hy', hh, hm]
    have hinit := hpre.initM
    rw [hmu] at hinit; simp only [OptP] at hinit
    have hqP : q < s.P.length := by
      simp only [parentOf] at hm
      cases hq : s.P[q]? with
      | none => rw [hq] at hm; cases hm
      | some _ => exact lt_of_getElem? hq
    have hqm : partOf s.P q m := ⟨hqP, .inr (by
      rw [chain_cons hm (WF3.parent_lt (s := s.flat) hw hm).1]; exact List.mem_cons_self ..)⟩
    have hcm : parentOf s.P ctl = some m := (mem_kids.1 (List.mem_of_getElem? hkc)).2
    have hcP : ctl < s.P.length := (mem_kids.1 (List.mem_of_getElem? hkc)).1
    have hcmp : partOf s.P ctl m := ⟨hcP, .inr (by
      rw [chain_cons hcm (WF3.parent_lt (s := s.flat) hw hcm).1]; exact List.mem_cons_self ..)⟩
    refine ⟨hcore, hcu, fun x hx hl => ?_, fun x hx hl => ?_⟩
    · rcases List.mem_append.1 hx with hx | hx
      · exact hsi x hx hl
      · rw [List.mem_singleton.1 hx]
        show OptP (slotOf s g) _ False
        rw [show slotOf s g = some q by simp [slotOf, hy', hh]]
        exact fun l hl' => hinit l (footprint_sub (s := s.flat) hw hqm hl')
    · rcases List.mem_append.1 hx with hx | hx
      · exact hci x hx hl
      · rw [List.mem_singleton.1 hx, hco]
        exact hinit ctl (leaf_mem_footprint (t := s.flat) h1.2 hcmp)

/-- `acquire` (C16) preserves `SyncPart`. -/
theorem acquire_syncState {ks : KShared} {L : MutexLayout} {s : SC} {reg : SyncReg} {c i : Nat}
    {st' : SC × SyncReg} (h : AcquireOk ks L s reg c i st') (hw : WF3 s.flat)
    (hw' : WF3 st'.1.flat) (hs : SyncPart L s reg) : SyncPart L st'.1 st'.2 := by
  obtain ⟨hc, hu, hsi, hci⟩ := hs
  have hcore := acquire_preserves h hw hw' hc
  have hcu := acquire_ctlUnique h hw hc hu
  obtain ⟨-, e, hi, -, hpre, rfl⟩ := h
  have hA : (deriveSyncEff s c e.guarded).A = s.A ++ [⟨.modify, some e.guarded,
      (s.view c).afp e.guarded, .frame (s.view c).top, true⟩] := rfl
  obtain ⟨hsk, hh⟩ := skel_append hA rfl (fun j y' hy' => ⟨y', hy', Same.refl _⟩) fun z hz => by
    rw [List.mem_singleton] at hz; subst hz
    exact .inr ⟨e.guarded, rfl, active_lt hpre.active, hpre.active, fun l hl => hl⟩
  obtain ⟨hsi', hci'⟩ := init_step (L := L) (reg := reg) hsk hh (pskel_refl _)
    (initFacts_same rfl rfl) hw hc hsi hci
  obtain ⟨hsi'', hci''⟩ := init_set (e' := { e with grant := some s.A.length }) hi rfl hsi' hci'
  exact ⟨hcore, hcu, hsi'', hci''⟩

/-- `unlock` (C17) preserves `SyncPart`. -/
theorem unlock_syncState {L : MutexLayout} {s : SC} {reg : SyncReg} {c i : Nat}
    {st' : SC × SyncReg} (h : UnlockOk L s reg c i st') (hw : WF3 s.flat)
    (hw' : WF3 st'.1.flat) (hs : SyncPart L s reg) : SyncPart L st'.1 st'.2 := by
  obtain ⟨hc, hu, hsi, hci⟩ := hs
  have hcore := unlock_preserves h hw hw' hc
  have hcu := unlock_ctlUnique h hw hc hu
  obtain ⟨-, e, g₀, hi, -, -, hpre, -, -, rfl⟩ := h
  obtain ⟨x, hx, -⟩ := hpre.active
  have hx' : s.A[g₀]? = some x := hx
  have hA : (s.set (releaseEff (s.view c) g₀)).A = s.A.set g₀ { x with active := false } := by
    show (releaseEff (s.view c) g₀).A = _; rw [releaseEff_eq hx]; rfl
  have hP : (s.set (releaseEff (s.view c) g₀)).P = s.P := by
    show (releaseEff (s.view c) g₀).P = _; rw [releaseEff_eq hx]; rfl
  have hI : (s.set (releaseEff (s.view c) g₀)).I = s.I := by
    show (releaseEff (s.view c) g₀).I = _; rw [releaseEff_eq hx]; rfl
  obtain ⟨hsk, hh⟩ := skel_set hx' hA (same_deact x)
  obtain ⟨hsi', hci'⟩ := init_step (L := L) (reg := reg) hsk hh (by rw [hP]; exact pskel_refl _)
    (initFacts_same hP hI) hw hc hsi hci
  obtain ⟨hsi'', hci''⟩ := init_set (e' := { e with grant := none }) hi rfl hsi' hci'
  exact ⟨hcore, hcu, hsi'', hci''⟩

/-- `resetLock` (C18; C18.3) preserves `SyncPart`. -/
theorem resetLock_syncState {L : MutexLayout} {s : SC} {reg : SyncReg} {c i : Nat}
    {st' : SC × SyncReg} (h : ResetLockOk L s reg c i st') (hs : SyncPart L s reg) :
    SyncPart L st'.1 st'.2 := by
  obtain ⟨hc, hu, hsi, hci⟩ := hs
  have hcore := resetLock_preserves h hc
  have hcu := resetLock_ctlUnique h hu
  obtain ⟨-, e, hi, -, -, -, -, rfl⟩ := h
  obtain ⟨hsi', hci'⟩ := init_set (e' := { e with grant := none }) hi rfl hsi hci
  exact ⟨hcore, hcu, hsi', hci'⟩

/-! ## The by-value composite (C5, C23) -/

open TransferPreserveAux PreservationAux

/-- Facts of the effect of `spawn` (C4 effect, Spec 1 §72 effect), from its parameter and
shape clauses. -/
theorem spawnEff_facts {reg : SyncReg} {s : SC} {c : Nat} {ps : List Nat} {ls : LocalShape}
    (hpar : ∀ a ∈ ps, OptP ((s.view c).A[a]?) (fun y => y.active = true ∧
      y.holder = .frame (s.view c).top ∧ y.origin ≠ none) False)
    (hsh : ShapeOK s.P.length ls.toShape) : StepFacts reg s (spawnEff s c ps ls) :=
  .of (skel_enter rfl hpar) (pskel_shapeP hsh)
    (src_roots rfl (length_mapI _ _ _) fun z hz => by obtain ⟨i, -, rfl⟩ := List.mem_map.1 hz; rfl)

/-- Authorities after the yield (C5.3). -/
theorem yield_get {t : SC} {ps : List Nat} {f j : Nat} :
    (yieldEff t ps f).A[j]? = (t.A[j]?).map (yieldF ps f j) := by
  show (mapI (yieldF ps f) 0 t.A)[j]? = _
  rw [getElem?_mapI, Nat.zero_add]

/-- C22.3 carries from the state before the yield to the state after it, when
`SyncPart` holds after it: the `guarded` of a live entry is held by a place, so it is not a
parameter. -/
theorem yield_excl {L : MutexLayout} {reg : SyncReg} {t : SC} {ps : List Nat} {f src : Nat}
    (hs : SyncPart L (yieldEff t ps f) reg) (hx : TransferExcl L (t, reg) src) :
    TransferExcl L (yieldEff t ps f, reg) src := by
  intro e he hl
  have h1 := (hs.1.1 e he).guarded hl
  cases hy : (yieldEff t ps f).A[e.guarded]? with
  | none => rw [hy] at h1; exact h1.elim
  | some y =>
    rw [hy] at h1; simp only [OptP] at h1
    rw [yield_get] at hy
    obtain ⟨y₀, hy₀, e₀⟩ := Option.map_eq_some_iff.1 hy
    have hnp : e.guarded ∉ ps := fun hp => by
      unfold yieldF at e₀; simp only [hp, ↓reduceIte] at e₀
      rw [← e₀] at h1; exact h1.2
    have hA : (yieldEff t ps f).A[e.guarded]? = t.A[e.guarded]? := by
      rw [yield_get, hy₀]; unfold yieldF; simp [hnp]
    have hlt : e.Live t := by
      obtain ⟨z, hz, za⟩ := hl
      change (yieldEff t ps f).A[e.guarded]? = some z at hz
      rw [hA] at hz; exact ⟨z, hz, za⟩
    obtain ⟨h₁, h₂⟩ := hx e he hlt
    have hsl : slotOf (yieldEff t ps f) e.guarded = slotOf t e.guarded := by
      unfold slotOf; rw [hA]
    have hco : ControlOf L (yieldEff t ps f) e = ControlOf L t e := by
      unfold ControlOf; rw [hA]; rfl
    exact ⟨by rw [hsl]; exact h₁, by rw [hco]; exact h₂⟩

/-- `SyncPart` along the transfer phases of the by-value composite (C5.2), on the states where
the parameters are already yielded. -/
theorem transfers_sync {k : K} {L : MutexLayout} {reg : SyncReg} {fin : S3} {c f : Nat}
    {ps : List Nat} :
    ∀ (t : SC) (vs : List (Nat × Nat)), ValTransfersPre k fin c t vs → EncapVals L reg c t vs →
      KBase (yieldEff t ps f) → SyncPart L (yieldEff t ps f) reg →
      (∀ v ∈ vs, FrameOwned t.P v.2) →
      (∀ a ∈ ps, ∀ y, t.A[a]? = some y → ∃ g, y.holder = .frame g) →
      SyncPart L (yieldEff (transfersEff c t vs) ps f) reg
  | _, [], _, _, _, hs, _, _ => hs
  | t, v :: vs, ⟨hpre, hrest⟩, ⟨hx, hxs⟩, hk, hs, hown, hp => by
    simp only [transfersEff]
    have hk₁ := transfers_base (ps := ps) (f := f) t [v] ⟨hpre, trivial⟩ hk
      (fun w hw => hown w (by simp at hw; simp [hw])) hp
    simp only [transfersEff] at hk₁
    have hw' : WF3 (transferEffC (yieldEff t ps f) c v.1 v.2).flat := by
      rw [yield_transfer hp]; exact hk₁.2.1
    have hs₁ := transfer_syncState (s := yieldEff t ps f) (c := c) (src := v.1) (dst := v.2)
      hpre.sameShape
      hpre.dstNotInit hpre.dstUsable.lt (yield_excl hs hx) hk.2.1 hw' hs
    rw [yield_transfer hp] at hs₁
    refine transfers_sync (transferEffC t c v.1 v.2) vs hrest hxs hk₁ hs₁ (fun w hw => ?_)
      (fun a ha y hy => ?_)
    · exact transfer_frameOwned (hown w (List.mem_cons_of_mem _ hw))
    · obtain ⟨y₀, hy₀, e⟩ := transfer_frame_held hy
      obtain ⟨g, hg⟩ := hp a ha y₀ hy₀
      exact ⟨g, by rw [e ⟨g, hg⟩, hg]⟩

/-- The by-value composite (C5) admitted by C22.3 preserves `SyncPart`, from a state
satisfying `KInvCA`. -/
theorem spawnVal_syncState {k : K} {L : MutexLayout} {reg : SyncReg} {s s' : SC} {c : Nat}
    {ps : List Nat} {ls : LocalShape} {vs : List (Nat × Nat)} (hk : KInvCA s)
    (h : SpawnValStep k s c ps ls vs (.ok s')) (he : EncapVals L reg c (spawnCreate s c ls) vs)
    (hs : SyncPart L s reg) : SyncPart L s' reg := by
  obtain ⟨-, h⟩ := h; obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  have hpar : ParamsOK (s.view c) ps := hpre.params
  have hlt : ∀ a ∈ ps, a < s.A.length := fun a ha => by
    have := hpre.params a ha
    unfold OptP at this; split at this
    · exact lt_of_getElem? ‹_›
    · exact this.elim
  have hframe : ∀ a ∈ ps, ∀ y, (spawnCreate s c ls).A[a]? = some y →
      ∃ g, y.holder = .frame g := by
    intro a ha y hy
    have hp := hpre.params a ha
    have hy' : (spawnCreate s c ls).A[a]? = s.A[a]? := by
      show (mapI _ 0 s.A ++ _)[a]? = _
      rw [List.getElem?_append_left (by rw [length_mapI]; exact hlt a ha), getElem?_mapI]
      cases s.A[a]? <;> simp
    rw [hy'] at hy
    have hy₂ : (s.view c).A[a]? = some y := hy
    rw [hy₂] at hp
    exact ⟨_, hp.2.1⟩
  have hb₀ : KBase (spawnEff s c ps ls) := spawn_base hk hpre.creatorLive hpar hpre.localsOK
  have hs₀ : SyncPart L (spawnEff s c ps ls) reg :=
    facts_syncState (spawnEff_facts hpre.params hpre.localsOK) (spawn_init hpre.localsOK)
      hk.1.1.2 hb₀.2.1 hs
  rw [← create_yield hlt] at hb₀ hs₀
  exact transfers_sync (spawnCreate s c ls) vs hpre.transfers he hb₀ hs₀
    (fun v hv => spawn_frameOwned (hpre.freshDst v hv)) hframe

end SyncInitAux

open SyncPreserveAux SyncInitAux

/-! ## Theorem 2, synchronization part -/

/-- A kernel step that is neither `transfer` nor `endUse`, taken under `RestrictedStep`, preserves
`SyncPart` (C21, C22, C23). -/
theorem kernel_syncState {k : K} {L : MutexLayout} {reg : SyncReg} {ar : ArenaReg} {c : Nat}
    {op : KernelOp} {s s' : SC} (h : opStepC k op c s (.ok s'))
    (he : RestrictedStep L (s, reg, ar) (.kernel c op))
    (hnt : ∀ src dst, op ≠ .transfer src dst) (hne : ∀ p, op ≠ .endUse p) (hw : WF3 s.flat)
    (hw' : WF3 s'.flat) (hs : SyncPart L s reg) : SyncPart L s' reg :=
  facts_syncState (opStep_facts h he hnt hw) (opStep_init h hnt hne) hw hw' hs

/-- `WF3` of the globally live frames after an operation run on the view of `c` that keeps the
stack (C2). -/
theorem wf3_after_view {k : K} {op : KernelOp} {c : Nat} {s s' : SC} (hfr : FramesC s)
    (h : ViewStep (op.Step k) c s (.ok s'))
    (hW : ∀ t', op.Step k (s.view c) (.ok t') → WF3 t' ∧ t'.F = (s.view c).F) :
    WF3 s'.flat := by
  obtain ⟨t', hR, rfl⟩ := SyncPreserveAux.viewStep_ok h
  obtain ⟨hwt, hF⟩ := hW t' hR
  have hv : (s.set t').view c = t' := SC.view_set hF
  exact SC.wf3_flat_of_view (c := c) (by rw [hv]; exact hwt) hfr.nodup

/-- Theorem 2, synchronization part (C21, C22, C23) on one labelled step: every labelled step
taken under `RestrictedStep` (C22.1–C22.3, C22.5), `transfer`, the by-value composite and the
atomic cases included, preserves `SyncPart` (every clause of `SyncInv`, C21.1–C21.7, and of
`GrantDiscipline`, C22, but the guard across registries). `KInvCA` before the step and `WF3`
after it are supplied by the kernel part of theorem 2. -/
theorem lstep_preserves {ks : KShared} {L : MutexLayout} {lbl : Label}
    {st st' : SC × SyncReg × ArenaReg}
    (h : LStep ks L lbl st st') (he : RestrictedStep L st lbl) (hk : KInvCA st.1)
    (hw' : WF3 st'.1.flat) (hs : SyncPart L st.1 st.2.1) :
    SyncPart L st'.1 st'.2.1 := by
  have hw : WF3 st.1.flat := hk.1.1.2
  cases h with
  | @kernel s s' reg ar c op h =>
    cases op
    case transfer src dst =>
      obtain ⟨-, h'⟩ := h; obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h'
      exact transfer_syncState hpre.sameShape hpre.dstNotInit hpre.dstUsable.lt he hw hw' hs
    case endUse p => exact endUse_syncState h he hw hw' hs
    all_goals
      exact facts_syncState (opStep_facts (reg := reg) h he (fun _ _ h => by cases h) hw)
        (opStep_init h (fun _ _ h => by cases h) (fun _ h => by cases h)) hw hw' hs
  | @spawn s s' reg ar c ps ls h =>
    obtain ⟨-, h'⟩ := h; obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h'
    exact facts_syncState (spawnEff_facts hpre.params hpre.localsOK) (spawn_init hpre.localsOK)
      hw hw' hs
  | @terminate s s' reg ar c h =>
    have hf := term_facts (reg := reg) hw h
    obtain ⟨-, h'⟩ := h; obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h'
    exact facts_syncState hf (initFacts_same rfl rfl) hw hw' hs
  | @join s s' reg ar c d h =>
    have hf := join_facts (reg := reg) h
    cases h
    exact facts_syncState hf (initFacts_same rfl rfl) hw hw' hs
  | deriveSync h => exact (deriveSync_excluded h he).elim
  | newMutex h => exact newMutex_syncState h hw hs
  | acquire h => exact acquire_syncState h hw hw' hs
  | unlock h => exact unlock_syncState h hw hw' hs
  | resetLock h => exact resetLock_syncState h hs
  | spawnVal h => exact spawnVal_syncState hk h he hs
  | newArena h => obtain ⟨-, -, rfl⟩ := newArenaStepC_ok h; exact hs
  | @issue s reg ar c i region dst st' h =>
    obtain ⟨E, s₁, hE, -, -, hsp, hsto, -⟩ := issueStepC_ok h
    have hsep' : ∀ e ∈ reg, e.Live s → E.internal ≠ e.guarded := by
      have := he; simp only [RestrictedStep, hE, OptP] at this; exact this
    have hw₁ : WF3 s₁.flat := wf3_after_view hk.1.1.1
      (show ViewStep ((KernelOp.split E.internal [region]).Step ks.toK) c s (.ok s₁) from hsp)
      fun t' hR => by
        have hR' : SplitStep ks.toK E.internal [region] (s.view c) (.ok t') := hR
        refine ⟨split_preserves_wf3 (SC.wf3_view hk.1.1.1 hw) hR', ?_⟩
        obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hR'; rfl
    exact kernel_syncState (ar := ar) hsto trivial (fun _ _ e => by cases e)
      (fun _ e => by cases e) hw₁ hw'
      (kernel_syncState (ar := ar) hsp hsep' (fun _ _ e => by cases e) (fun _ e => by cases e)
        hw hw₁ hs)
  | @reset s reg ar c i st' h =>
    obtain ⟨E, s₁, hE, hd, hrl, -, -⟩ := resetStepC_ok (k := ks.toK) h
    have hsep' : ∀ e ∈ reg, e.Live s → E.internal ≠ e.guarded := by
      have := he; simp only [RestrictedStep, hE, OptP] at this; exact this
    have hw₁ : WF3 s₁.flat := wf3_after_view hk.1.1.1
      (show ViewStep ((KernelOp.derive E.internal (footprint s.P E.storage) .modify).Step ks.toK)
        c s (.ok s₁) from hd)
      fun t' hR => by
        have hR' : DeriveStep E.internal (footprint s.P E.storage) .modify (s.view c) (.ok t') := hR
        refine ⟨derive_preserves_wf3 (SC.wf3_view hk.1.1.1 hw) hR', ?_⟩
        obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hR'; rfl
    exact kernel_syncState (ar := ar) hrl trivial (fun _ _ e => by cases e)
      (fun _ e => by cases e) hw₁ hw'
      (kernel_syncState (ar := ar) hd hsep' (fun _ _ e => by cases e) (fun _ e => by cases e)
        hw hw₁ hs)
  | @readShared s reg ar c a l v order h =>
    exact hs
  | @writeShared s s' reg ar c a region order kind h =>
    have hk' := writeSharedC_ok_kernel h.1 h.2
    exact facts_syncState (opStep_facts (L := L) (reg := reg) (ar := ar) hk' trivial
      (fun _ _ h => by cases h) hw)
      (opStep_init hk' (fun _ _ h => by cases h) (fun _ h => by cases h)) hw hw' hs
  | @cas s s' reg ar c a l succ fail br h =>
    rcases cas_ok_cases h with hk' | rfl
    · exact facts_syncState (opStep_facts (L := L) (reg := reg) (ar := ar) hk' trivial
        (fun _ _ h => by cases h) hw)
        (opStep_init hk' (fun _ _ h => by cases h) (fun _ h => by cases h)) hw hw' hs
    · exact hs

/-! ## A transfer onto a live mutex value is rejected (C21.7; Spec 1 §63.3) -/

/-- C21.7 with Spec 1 §63.3: under `SyncPart`, a `transfer` whose destination contains the mutex
value of a live entry is rejected, its controller leaf being `Init`. -/
theorem transfer_into_live_mutex_rejected {k : K} {L : MutexLayout} {reg : SyncReg}
    {c src dst m : Nat} {s : SC} {e : SyncEntry} (hw : WF3 s.flat) (hs : SyncPart L s reg)
    (he : e ∈ reg) (hl : e.Live s) (hm : mutexOf s e.guarded = some m)
    (hmd : partOf s.P m dst) : ¬ TransferPreC k s c src dst := by
  intro hpre
  have h3 := (hs.1.1 e he).control hl
  have h4 := hs.2.2.2 e he hl
  cases hco : ControlOf L s e with
  | none => rw [hco] at h3; exact h3
  | some ctl =>
    rw [hco] at h3 h4; simp only [OptP] at h3 h4
    obtain ⟨y, q, m', hy, hh, hm', -, hkc⟩ := SyncPreserveAux.controlOf_spec hco
    have hy' : s.A[e.guarded]? = some y := hy
    have hmm : mutexOf s e.guarded = some m' := by simp [mutexOf, hy', hh, hm']
    rw [hm] at hmm; cases hmm
    have hcm : parentOf s.P ctl = some m := (mem_kids.1 (List.mem_of_getElem? hkc)).2
    have hcmp : partOf s.P ctl m := ⟨h3.1.lt, .inr (by
      rw [chain_cons hcm (WF3.parent_lt (s := s.flat) hw hcm).1]; exact List.mem_cons_self ..)⟩
    have hcd : ctl ∈ footprint s.P dst :=
      SyncInitAux.leaf_mem_footprint (t := s.flat) h3.2
        (SyncInitAux.partOf_trans (t := s.flat) hw hcmp hmd)
    exact hpre.dstNotInit ctl hcd h4

end Ern.ConcurrencyModel
