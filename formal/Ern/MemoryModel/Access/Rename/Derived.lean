import Ern.MemoryModel.Access.Rename.Places

/-!
# Renaming of identities: derived notions of a state

Equivariance of the state-level notions of `specs/ERN_Memory_Model_Specification.md` read by
the operations O1–O16 and by the invariants, under related states (§38; §49, last paragraph): the
current frame (§39), origin chains and effective anchors (§42, §44), activity (§42), usability,
frames of places and live holders (§40, §49.8), effective modes (§43), exercise and the
grounding of a right (§43; §63.4, §69.2, §70.3), dependencies (§44), anchor order (§44, §54),
dynamic pinning (§74) and leaves of usable places (§66.1).

Iff lemmas are proved in one direction and closed by symmetry (`SRel.symm`).
-/

namespace Ern.MemoryModel.Access.Rename

variable {π α : Ren} {s s' : S3}

/-! ## Frames, origins, activity (§39, §42, §44) -/

/-- The current frame is kept (§39; §49, last paragraph). -/
theorem SRel.top (h : SRel π α s s') : s'.top = s.top := by
  unfold S3.top; rw [h.F]

/-- Origin links correspond (§42; §49, last paragraph). -/
theorem SRel.org (h : SRel π α s s') (j : Nat) : s'.org (α.f j) = (s.org j).map α.f := by
  simp only [S3.org]
  cases hy : s.A[j]? with
  | none => rw [(h.A_none j).1 hy]; rfl
  | some y =>
    obtain ⟨y', hy', hr⟩ := h.A_some hy
    rw [hy', Option.bind_some, Option.bind_some, hr.origin]

/-- Origin chains correspond (§42, §43; §49, last paragraph). -/
theorem SRel.ancs (h : SRel π α s s') (hd : Down s) (hd' : Down s') (j : Nat) :
    s'.ancs (α.f j) = (s.ancs j).map α.f :=
  chain_ren hd.2 hd'.2 h.org j

/-- Membership in origin chains is invariant (§42, §43; §49, last paragraph). -/
theorem SRel.mem_ancs (h : SRel π α s s') (hd : Down s) (hd' : Down s') (i j : Nat) :
    α.f j ∈ s'.ancs (α.f i) ↔ j ∈ s.ancs i := by
  rw [h.ancs hd hd', α.mem_map_f]

/-- Effective anchors correspond (§44; §49, last paragraph). -/
theorem SRel.effAnchor (h : SRel π α s s') (hd : Down s) (hd' : Down s') (x : Nat) :
    s'.effAnchor (α.f x) = α.f (s.effAnchor x) := by
  unfold S3.effAnchor; rw [h.ancs hd hd', List.getLastD_map]

/-- Activity is invariant (§42, §44; §49, last paragraph). -/
theorem SRel.active (h : SRel π α s s') (x : Nat) : s'.Active (α.f x) ↔ s.Active x := by
  constructor
  · rintro ⟨y', hy', ha⟩
    obtain ⟨y, hy, hr⟩ := h.A_some' hy'
    exact ⟨y, hy, by rw [← hr.active]; exact ha⟩
  · rintro ⟨y, hy, ha⟩
    obtain ⟨y', hy', hr⟩ := h.A_some hy
    exact ⟨y', hy', by rw [hr.active]; exact ha⟩

/-- Anchor membership is invariant (§44: `D(p)` is a set; §49, last paragraph). -/
theorem SRel.mem_D (h : SRel π α s s') (q x : Nat) : α.f x ∈ s'.D (π.f q) ↔ x ∈ s.D q :=
  (h.D q).mem_iff.trans (α.mem_map_f _ _)

/-- Footprint membership is invariant (§40; §49, last paragraph). -/
theorem SRel.mem_footprint (h : SRel π α s s') (hd : Down s) (hd' : Down s') (l q : Nat) :
    π.f l ∈ footprint s'.P (π.f q) ↔ l ∈ footprint s.P q :=
  mem_footprint_ren h.P hd.1 hd'.1 l q

/-- Footprints correspond up to permutation (§40, §42: a set; §49, last paragraph). -/
theorem SRel.footprint_perm (h : SRel π α s s') (hd : Down s) (hd' : Down s') (q : Nat) :
    (footprint s'.P (π.f q)).Perm ((footprint s.P q).map π.f) :=
  footprint_perm_ren h.P hd.1 hd'.1 q

/-! ## Usability, frames of places, live holders (§40, §49.8) -/

/-- `Usable` is preserved forward (§40; §49, last paragraph). -/
theorem SRel.usable_of (h : SRel π α s s') {q : Nat} (hq : s.Usable q) : s'.Usable (π.f q) := by
  induction hq with
  | frame hpl hd ho hf =>
    rename_i f _
    exact .frame (f := f) (by rw [h.P.get, hpl]; rfl) (by rw [h.dead]; exact hd)
      (by simp only [Place.ren, ho, Holder.ren]) (by rw [h.F]; exact hf)
  | place hpl hd ho _ ih =>
    exact .place (by rw [h.P.get, hpl]; rfl) (by rw [h.dead]; exact hd)
      (by simp only [Place.ren, ho, Holder.ren]) ih

/-- `Usable` is invariant (§40; §49, last paragraph). -/
theorem SRel.usable (h : SRel π α s s') (q : Nat) : s'.Usable (π.f q) ↔ s.Usable q :=
  ⟨fun hq => by simpa only [Ren.symm_f, π.gf] using h.symm.usable_of hq, h.usable_of⟩

/-- Live holders are invariant (§49.8; §49, last paragraph). -/
theorem SRel.holderLive (h : SRel π α s s') (o : Holder) :
    HolderLive s' (o.ren π) ↔ HolderLive s o := by
  cases o with
  | frame f => show f ∈ s'.F ↔ f ∈ s.F; rw [h.F]
  | place p => exact h.usable p

/-- `FrameOf` is preserved forward (§40, `placeFrame`; §49, last paragraph). -/
theorem SRel.frameOf_of (h : SRel π α s s') {q f : Nat} (hq : FrameOf s q f) :
    FrameOf s' (π.f q) f := by
  induction hq with
  | frame hpl ho =>
    exact .frame (by rw [h.P.get, hpl]; rfl) (by simp only [Place.ren, ho, Holder.ren])
  | place hpl ho _ ih =>
    exact .place (by rw [h.P.get, hpl]; rfl) (by simp only [Place.ren, ho, Holder.ren]) ih

/-- `FrameOf` is invariant; frames are not renamed (§40, `placeFrame`; §49, last paragraph). -/
theorem SRel.frameOf (h : SRel π α s s') (q f : Nat) : FrameOf s' (π.f q) f ↔ FrameOf s q f :=
  ⟨fun hq => by simpa only [Ren.symm_f, π.gf] using h.symm.frameOf_of hq, h.frameOf_of⟩

/-- `placeFrame` is invariant (§40; §49, last paragraph). -/
theorem SRel.pframe (h : SRel π α s s') (q : Nat) : s'.pframe (π.f q) = s.pframe q :=
  Option.ext fun f => by rw [pframe_iff, pframe_iff, h.frameOf]

/-- The frame of a holder is invariant (§44; §49, last paragraph). -/
theorem SRel.hframe (h : SRel π α s s') (o : Holder) : s'.hframe (o.ren π) = s.hframe o := by
  cases o with
  | frame f => rfl
  | place p => exact h.pframe p

/-! ## Effective modes (§43) -/

/-- Modes of covering active descendants are invariant as a set (§43; §49, last paragraph). -/
theorem SRel.mem_descModes (h : SRel π α s s') (hd : Down s) (hd' : Down s') (a p : Nat)
    (m : Mode) : m ∈ descModes s' (α.f a) (π.f p) ↔ m ∈ descModes s a p := by
  simp only [Access.mem_descModes]
  constructor
  · rintro ⟨j, y', hy', h1, h2, h3, h4⟩
    rw [← α.fg j] at hy' h3
    obtain ⟨y, hy, hyy⟩ := h.A_some' hy'
    refine ⟨α.g j, y, hy, hyy.active ▸ h1, (hyy.mem_footprint p).1 h2,
      (h.mem_ancs hd hd' _ _).1 h3, hyy.mode ▸ h4⟩
  · rintro ⟨j, y, hy, h1, h2, h3, h4⟩
    obtain ⟨y', hy', hyy⟩ := h.A_some hy
    exact ⟨α.f j, y', hy', hyy.active ▸ h1, (hyy.mem_footprint p).2 h2,
      (h.mem_ancs hd hd' _ _).2 h3, hyy.mode.symm ▸ h4⟩

/-- `effOf` reads its list of modes as a set (§43, cases 2–4; §49, last paragraph). -/
theorem effOf_congr {m : Mode} {ds ds' : List Mode} (h : ∀ x, x ∈ ds ↔ x ∈ ds') :
    effOf m ds = effOf m ds' := by
  have h0 : ds = [] ↔ ds' = [] := by simp only [List.eq_nil_iff_forall_not_mem, h]
  simp only [effOf, h0, h Mode.modify]

/-- Effective modes are invariant (§43; §49, last paragraph). -/
theorem SRel.effective (h : SRel π α s s') (hd : Down s) (hd' : Down s') (a p : Nat) :
    effective s' (α.f a) (π.f p) = effective s a p := by
  cases hy : s.A[a]? with
  | none => simp only [Access.effective, hy, (h.A_none a).1 hy]
  | some y =>
    obtain ⟨y', hy', hr⟩ := h.A_some hy
    simp only [Access.effective, hy, hy', hr.active, hr.mem_footprint, hr.mode,
      effOf_congr (h.mem_descModes hd hd' a p)]

/-- Footprints of authorities correspond up to permutation (§42: a set; §49, last
paragraph). -/
theorem SRel.afp (h : SRel π α s s') (a : Nat) : (s'.afp (α.f a)).Perm ((s.afp a).map π.f) := by
  unfold S3.afp
  cases hy : s.A[a]? with
  | none => rw [(h.A_none a).1 hy]; exact .nil
  | some y =>
    obtain ⟨y', hy', hr⟩ := h.A_some hy
    rw [hy']; exact hr.footprint

/-- Footprint membership of authorities is invariant (§42; §49, last paragraph). -/
theorem SRel.mem_afp (h : SRel π α s s') (a l : Nat) : π.f l ∈ s'.afp (α.f a) ↔ l ∈ s.afp a :=
  (h.afp a).mem_iff.trans (π.mem_map_f _ _)

/-- Sufficient effective mode over a footprint is invariant (§43; §49, last paragraph). -/
theorem SRel.forall_footprint_allows (h : SRel π α s s') (hd : Down s) (hd' : Down s')
    (q a : Nat) (m : Mode) :
    (∀ l ∈ footprint s'.P (π.f q), Allows (Access.effective s' (α.f a) l) m) ↔
      ∀ l ∈ footprint s.P q, Allows (Access.effective s a l) m :=
  π.forall_mem_iff (fun l => h.mem_footprint hd hd' l q)
    (fun l => by rw [h.effective hd hd'])

/-! ## Exercise and rights (§43; §63.4, §69.2, §70.3) -/

/-- `ExercisableAt` is preserved forward (§43; §49, last paragraph). -/
theorem SRel.exercisableAt_of (h : SRel π α s s') (hd : Down s) (hd' : Down s') {a : Nat}
    {m : Mode} (he : s.ExercisableAt a m) : s'.ExercisableAt (α.f a) m := by
  induction he with
  | base hy ha hm hf =>
    obtain ⟨y', hy', hr⟩ := h.A_some hy
    exact .base hy' (by rw [hr.active]; exact ha) (by rw [hr.mode]; exact hm)
      (by rw [hr.holder, hf, h.top]; rfl)
  | held hy ha hm hp _ hc ih =>
    obtain ⟨y', hy', hr⟩ := h.A_some hy
    exact .held hy' (by rw [hr.active]; exact ha) (by rw [hr.mode]; exact hm)
      (by rw [hr.holder, hp]; rfl) ih ((h.forall_footprint_allows hd hd' _ _ _).2 hc)

/-- `ExercisableAt` is invariant (§43; §49, last paragraph). -/
theorem SRel.exercisableAt (h : SRel π α s s') (hd : Down s) (hd' : Down s') (a : Nat)
    (m : Mode) : s'.ExercisableAt (α.f a) m ↔ s.ExercisableAt a m :=
  ⟨fun he => by simpa only [Ren.symm_f, α.gf] using h.symm.exercisableAt_of hd' hd he,
   h.exercisableAt_of hd hd'⟩

/-- `HasRight` is invariant (§43; §49, last paragraph). -/
theorem SRel.hasRight (h : SRel π α s s') (hd : Down s) (hd' : Down s') (m : Mode) (q : Nat) :
    HasRight s' m (π.f q) ↔ HasRight s m q :=
  α.exists_mem_iff h.mem_rangeA fun a =>
    and_congr (h.exercisableAt hd hd' a m) (h.forall_footprint_allows hd hd' q a m)

/-- `Grounds` is invariant (§43; §63.4, §69.2, §70.3; §49, last paragraph). -/
theorem SRel.grounds (h : SRel π α s s') (hd : Down s) (hd' : Down s') (m : Mode) (q g : Nat) :
    Grounds s' m (π.f q) (α.f g) ↔ Grounds s m q g :=
  and_congr (h.mem_rangeA g)
    (and_congr (h.exercisableAt hd hd' g m) (h.forall_footprint_allows hd hd' q g m))

/-- `RightChain` is invariant (§63.4, §69.2, §70.3; §49, last paragraph). -/
theorem SRel.rightChain (h : SRel π α s s') (hd : Down s) (hd' : Down s') (g j : Nat) :
    RightChain s' (α.f g) (α.f j) ↔ RightChain s g j :=
  or_congr α.f_inj (h.mem_ancs hd hd' g j)

/-! ## Dependencies and anchor order (§44, §54) -/

/-- Anchors gathered over the places selected by corresponding predicates correspond up to
permutation (§44: `D(p)` is a set; §63, `ok` effect; §49, last paragraph). -/
theorem SRel.filter_flatMap_D (h : SRel π α s s') {Q Q' : Nat → Bool}
    (hQ : ∀ r, Q' (π.f r) = Q r) :
    (((List.range s'.P.length).filter Q').flatMap s'.D).Perm
      ((((List.range s.P.length).filter Q).flatMap s.D).map α.f) := by
  have hL : ((List.range s'.P.length).filter Q').Perm
      (((List.range s.P.length).filter Q).map π.f) :=
    π.perm_of_mem (List.Pairwise.filter _ List.nodup_range)
      (List.Pairwise.filter _ List.nodup_range) fun r => by
        simp only [List.mem_filter, h.P.mem_range, hQ]
  refine (hL.flatMap_right s'.D).trans ?_
  rw [List.flatMap_map, List.map_flatMap]
  exact perm_flatMap_pointwise fun r _ => h.D r

/-- Inherited anchors correspond up to permutation (§44; §49, last paragraph). -/
theorem SRel.depsOf (h : SRel π α s s') (hd : Down s) (hd' : Down s') (q : Nat) :
    (Access.depsOf s' (π.f q)).Perm ((Access.depsOf s q).map α.f) :=
  h.filter_flatMap_D fun r => decide_eq_decide.2 (partOf_ren h.P hd.1 hd'.1 r q)

/-- `DepsValid` is invariant (§44; §66.3, §67.3, §68.3; §49, last paragraph). -/
theorem SRel.depsValid (h : SRel π α s s') (hd : Down s) (hd' : Down s') (p : Nat) :
    DepsValid s' (π.f p) ↔ DepsValid s p :=
  π.forall_mem_iff h.P.mem_range fun q => by
    rw [partOf_ren h.P hd.1 hd'.1]
    exact imp_congr_right fun _ => α.forall_mem_iff (h.mem_D q) h.active

/-- `EffAnchorOK` is invariant; frames are not renamed (§44; §49, last paragraph). -/
theorem SRel.effAnchorOK (h : SRel π α s s') (hd : Down s) (hd' : Down s') (x : Nat)
    (fd : Option Nat) : EffAnchorOK s' (α.f x) fd ↔ EffAnchorOK s x fd := by
  unfold EffAnchorOK
  rw [h.effAnchor hd hd']
  cases hz : s.A[s.effAnchor x]? with
  | none => rw [(h.A_none _).1 hz]; exact Iff.rfl
  | some z =>
    obtain ⟨z', hz', hr⟩ := h.A_some hz
    rw [hz']
    simp only [OptP, hr.holder, h.hframe, h.F]

/-- `AnchorOrder` is preserved forward (§44, §54; §49, last paragraph). -/
theorem SRel.anchorOrder_of (h : SRel π α s s') (hd : Down s) (hd' : Down s')
    (ha : AnchorOrder s) : AnchorOrder s' := by
  intro q' hq' x' hx'
  rw [← π.fg q'] at hq' hx' ⊢
  rw [← α.fg x'] at hx' ⊢
  rw [h.pframe, h.effAnchorOK hd hd']
  exact ha _ ((h.usable _).1 hq') _ ((h.mem_D _ _).1 hx')

/-- `AnchorOrder` is invariant (§44, §54; §49, last paragraph). -/
theorem SRel.anchorOrder (h : SRel π α s s') (hd : Down s) (hd' : Down s') :
    AnchorOrder s' ↔ AnchorOrder s :=
  ⟨h.symm.anchorOrder_of hd' hd, h.anchorOrder_of hd hd'⟩

/-- `AnchorOrderHeld` is preserved forward (§44, §54; §49, last paragraph). -/
theorem SRel.anchorOrderHeld_of (h : SRel π α s s') (hd : Down s) (hd' : Down s')
    (ha : AnchorOrderHeld s) : AnchorOrderHeld s' := by
  intro q' hq' x' y' hy' ya hh
  rw [← π.fg q'] at hq' hh ⊢
  rw [← α.fg x'] at hy' ⊢
  obtain ⟨y, hy, hr⟩ := h.A_some' hy'
  rw [h.pframe, h.effAnchorOK hd hd']
  rw [hr.holder] at hh
  exact ha _ ((h.usable _).1 hq') _ y hy (by rw [← hr.active]; exact ya)
    ((Holder.ren_inj π (b := .place (π.g q'))).1 hh)

/-- `AnchorOrderHeld` is invariant (§44, §54; §49, last paragraph). -/
theorem SRel.anchorOrderHeld (h : SRel π α s s') (hd : Down s) (hd' : Down s') :
    AnchorOrderHeld s' ↔ AnchorOrderHeld s :=
  ⟨h.symm.anchorOrderHeld_of hd' hd, h.anchorOrderHeld_of hd hd'⟩

/-! ## Dynamic pinning, leaves of usable places (§74, §66.1) -/

/-- Dynamic pinning is invariant (§74; §49, last paragraph). -/
theorem SRel.pin (h : SRel π α s s') (l : Nat) : s'.pin (π.f l) = s.pin l := by
  rw [Bool.eq_iff_iff, S3.pin_iff, S3.pin_iff]
  constructor
  · rintro ⟨i, ob', hob', ha, hl⟩
    obtain ⟨ob, hob, hr⟩ := h.pins_some' hob'
    exact ⟨i, ob, hob, by rw [← hr.active]; exact ha, (hr.mem_leaves l).1 hl⟩
  · rintro ⟨i, ob, hob, ha, hl⟩
    obtain ⟨ob', hob', hr⟩ := h.pins_some hob
    exact ⟨i, ob', hob', by rw [hr.active]; exact ha, (hr.mem_leaves l).2 hl⟩

/-- `LeafOfUsable` is invariant (§66.1, §67.1, §68.1; §49, last paragraph). -/
theorem SRel.leafOfUsable (h : SRel π α s s') (hd : Down s) (hd' : Down s') (l : Nat) :
    LeafOfUsable s' (π.f l) ↔ LeafOfUsable s l :=
  π.exists_mem_iff h.P.mem_range fun q => and_congr (h.usable q) (h.mem_footprint hd hd' l q)

end Ern.MemoryModel.Access.Rename
