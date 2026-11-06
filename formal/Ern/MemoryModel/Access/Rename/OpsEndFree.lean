import Ern.MemoryModel.Access.Rename.Derived

/-!
# Renaming of identities: `endUse`, `free`, `alloc`

Correspondence under a renaming of identities (§49, last paragraph) of the operations O12
`endUse` (§69), O13 `free` (§70) and O14 `alloc` (§71) of
`specs/ERN_Memory_Model_Specification.md`: the release of authorities whose holder died
(§69, §70 `ok` effects), the effects and preconditions of each operation, `Satisfiable` (§71) under
the interface obligation `KExt`, the correspondence of outcomes (§58), and the preservation by `ok`
steps of downward links and of field order (§63.2).

`FreeCompat`'s `auth` is not renamed (§70.2); shapes are not renamed (§71.1).
-/

namespace Ern.MemoryModel.Access.Rename

variable {π α : Ren} {s s' : S3} {k k' : K}

/-! ## Generic helpers -/

/-- Related authorities mapped by corresponding functions stay related (§42; §49, last
paragraph). -/
private theorem optionRel_mapA {g g' : Authority → Authority}
    (hg : ∀ y y', AuthRel π α y y' → AuthRel π α (g y) (g' y')) {o o' : Option Authority}
    (h : Option.Rel (AuthRel π α) o o') : Option.Rel (AuthRel π α) (o.map g) (o'.map g') := by
  cases h with
  | none => exact .none
  | some hr => exact .some (hg _ _ hr)

/-- Related authorities made inactive stay related (§69, §70 `ok` effects; §49, last
paragraph). -/
private theorem authRel_off {y y' : Authority} (hr : AuthRel π α y y') :
    AuthRel π α { y with active := false } { y' with active := false } :=
  ⟨hr.mode, hr.origin, hr.footprint, hr.holder, rfl⟩

/-- Choices between related authorities under corresponding conditions stay related (§69, §70
`ok` effects; §49, last paragraph). -/
private theorem authRel_ite {c c' : Prop} [Decidable c] [Decidable c'] (hc : c' ↔ c)
    {a b a' b' : Authority} (ha : AuthRel π α a a') (hb : AuthRel π α b b') :
    AuthRel π α (if c then a else b) (if c' then a' else b') := by
  by_cases h : c
  · have h' := hc.2 h
    simp only [h, h', ↓reduceIte]; exact ha
  · have h' := mt hc.1 h
    simp only [h, h', ↓reduceIte]; exact hb

/-- Effects that keep the places and only release authorities keep downward links (§69, §70
`ok` effects; §49, last paragraph). -/
private theorem down_of_releases {s₁ : S3} (hd : Down s) (hP : s₁.P = s.P)
    (hr : EndFree.OnlyReleases s s₁) : Down s₁ :=
  ⟨by rw [hP]; exact hd.1, fun j o ho => hd.2 j o (by rw [← hr.org]; exact ho)⟩

/-! ## Release of authorities whose holder died (§69, §70) -/

/-- `cleanup` is equivariant (§69, §70 `ok` effects; §49, last paragraph). -/
theorem SRel.cleanup (h : SRel π α s s') : SRel π α (Access.cleanup s) (Access.cleanup s') :=
  { h with
    Alen := by simp only [Access.cleanup, List.length_map, h.Alen]
    A := fun x => by
      simp only [Access.cleanup, List.getElem?_map]
      refine optionRel_mapA (fun y y' hr => ?_) (h.A x)
      have hl : HolderLive s' y'.holder ↔ HolderLive s y.holder := by
        rw [hr.holder]; exact h.holderLive _
      exact authRel_ite hl hr (authRel_off hr)
    Afix := fun x hx => h.Afix x (by simpa only [Access.cleanup, List.length_map] using hx) }

/-- `cleanup` keeps downward links (§69, §70 `ok` effects; §49, last paragraph). -/
theorem cleanup_down (hd : Down s) : Down (cleanup s) :=
  down_of_releases hd rfl (EndFree.cleanup_releases s)

/-! ## O12 `endUse` (§69) -/

/-- `endUseS` is equivariant (§69, `ok` effect; §49, last paragraph). -/
theorem endUseS_ren (h : SRel π α s s') (hd : Down s) (hd' : Down s') (p : Nat) :
    SRel π α (endUseS s p) (endUseS s' (π.f p)) :=
  { h with
    I := fun l => by simp only [endUseS, h.mem_footprint hd hd', h.I]
    Alen := by simp only [endUseS, List.length_map, h.Alen]
    A := fun x => by
      simp only [endUseS, List.getElem?_map]
      refine optionRel_mapA (fun y y' hr => ?_) (h.A x)
      have hc : heldIn s'.P (π.f p) y'.holder ↔ heldIn s.P p y.holder := by
        rw [hr.holder]; exact heldIn_ren h.P hd.1 hd'.1 p y.holder
      exact authRel_ite hc (authRel_off hr) hr
    Afix := fun x hx => h.Afix x (by simpa only [endUseS, List.length_map] using hx)
    D := fun q => by
      by_cases hq : partOf s.P q p
      · simp only [endUseS, hq, (partOf_ren h.P hd.1 hd'.1 q p).2 hq, ↓reduceIte, List.map_nil]
        exact .nil
      · simp only [endUseS, hq, mt (partOf_ren h.P hd.1 hd'.1 q p).1 hq, ↓reduceIte]
        exact h.D q
    dead := fun q => by simp only [endUseS, h.dead, ownedIn_ren h.P hd.1 hd'.1] }

/-- The effect of `endUse` is equivariant (§69, `ok` effect; §49, last paragraph). -/
theorem endUseEff_ren (h : SRel π α s s') (hd : Down s) (hd' : Down s') (p : Nat) :
    SRel π α (endUseEff s p) (endUseEff s' (π.f p)) :=
  (endUseS_ren h hd hd' p).cleanup

/-- `endUseS` keeps downward links (§69, `ok` effect; §49, last paragraph). -/
theorem endUseS_down (hd : Down s) (p : Nat) : Down (endUseS s p) :=
  down_of_releases hd rfl (EndFree.endUseS_releases s p)

/-- The effect of `endUse` keeps downward links (§69, `ok` effect; §49, last paragraph). -/
theorem endUseEff_down (hd : Down s) (p : Nat) : Down (endUseEff s p) :=
  cleanup_down (endUseS_down hd p)

/-- Ending leaves are invariant (§69.2, §69.4; §49, last paragraph). -/
theorem SRel.endingLeaf (h : SRel π α s s') (hd : Down s) (hd' : Down s') (p l : Nat) :
    EndingLeaf s' (π.f p) (π.f l) ↔ EndingLeaf s p l := by
  unfold EndingLeaf
  exact or_congr (h.mem_footprint hd hd' l p) (and_congr (isLeaf_ren h.P l)
    (and_congr (h.usable l) (not_congr ((endUseS_ren h hd hd' p).usable l))))

/-- Root authorities of a value are invariant (§69.3; §49, last paragraph). -/
theorem isRootOf_ren (h : SRel π α s s') (hd : Down s) (hd' : Down s') {y y' : Authority}
    (hr : AuthRel π α y y') (p : Nat) : IsRootOf s' (π.f p) y' ↔ IsRootOf s p y := by
  unfold IsRootOf
  rw [hr.origin, Option.map_eq_none_iff]
  exact and_congr Iff.rfl
    (π.exists_mem_iff (fun l => h.mem_footprint hd hd' l p) fun l => hr.mem_footprint l)

/-- The access condition of `endUse` is invariant (§69.2; §49, last paragraph). -/
theorem SRel.endUseAccessOK (h : SRel π α s s') (hd : Down s) (hd' : Down s') (p j : Nat) :
    EndUseAccessOK s' (π.f p) (α.f j) ↔ EndUseAccessOK s p j := by
  unfold EndUseAccessOK
  cases hy : s.A[j]? with
  | none => rw [(h.A_none j).1 hy]; exact Iff.rfl
  | some y =>
    obtain ⟨y', hy', hr⟩ := h.A_some hy
    rw [hy']
    simp only [OptP]
    rw [hr.active, hr.origin, hr.holder]
    exact imp_congr Iff.rfl (imp_congr (not_congr Option.map_eq_none_iff)
      (imp_congr (π.exists_mem_iff hr.mem_footprint fun l => h.endingLeaf hd hd' p l)
        (or_congr (heldIn_ren h.P hd.1 hd'.1 p y.holder)
          (not_congr ((endUseS_ren h hd hd' p).holderLive y.holder)))))

/-- The anchor condition of `endUse` is invariant (§69.3; §49, last paragraph). -/
theorem SRel.endUseAnchorOK (h : SRel π α s s') (hd : Down s) (hd' : Down s') (p x : Nat) :
    EndUseAnchorOK s' (π.f p) (α.f x) ↔ EndUseAnchorOK s p x := by
  unfold EndUseAnchorOK
  cases hy : s.A[x]? with
  | none => rw [(h.A_none x).1 hy]; exact Iff.rfl
  | some y =>
    obtain ⟨y', hy', hr⟩ := h.A_some hy
    rw [hy']
    simp only [OptP]
    have hro := isRootOf_ren h hd hd' hr p
    rw [hr.holder]
    exact and_congr (not_congr (heldIn_ren h.P hd.1 hd'.1 p y.holder))
      (and_congr (not_congr hro) ((endUseS_ren h hd hd' p).holderLive y.holder))

/-- The preconditions of `endUse` as a conjunction (§69). -/
private theorem endUsePre_iff {p : Nat} : EndUsePre k s p ↔
    (s.Usable p ∧ HasRight s .modify p ∧
    (∃ g ∈ List.range s.A.length, Grounds s .modify p g ∧
      ∀ j ∈ List.range s.A.length, RightChain s g j ∨ EndUseAccessOK s p j) ∧
    (∀ a ∈ List.range s.A.length, ∀ j ∈ List.range s.A.length, s.Active a →
      ¬ (endUseEff s p).Active a → a ∈ s.ancs j → ¬ (endUseEff s p).Active j) ∧
    (∀ q ∈ List.range s.P.length, (endUseS s p).Usable q →
      ∀ x ∈ (endUseS s p).D q, EndUseAnchorOK s p x) ∧
    (∀ l ∈ List.range s.P.length, EndingLeaf s p l → s.pin l = false ∧ ¬ k.Pinned l)) :=
  ⟨fun ⟨a, b, c, d, e, f⟩ => ⟨a, b, c, d, e, f⟩, fun ⟨a, b, c, d, e, f⟩ => ⟨a, b, c, d, e, f⟩⟩

/-- The preconditions of `endUse` are invariant (§69; §49, last paragraph). -/
theorem endUsePre_ren (hK : KCorr π α k k') (hS : Sim π α s s') (p : Nat) :
    EndUsePre k' s' (π.f p) ↔ EndUsePre k s p := by
  obtain ⟨h, hd, hd', -⟩ := hS
  have hu := endUseS_ren h hd hd' p
  have he := endUseEff_ren h hd hd' p
  rw [endUsePre_iff, endUsePre_iff]
  refine and_congr (h.usable p) (and_congr (h.hasRight hd hd' .modify p)
    (and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))))
  · exact α.exists_mem_iff h.mem_rangeA fun g => and_congr (h.grounds hd hd' .modify p g)
      (α.forall_mem_iff h.mem_rangeA fun j =>
        or_congr (h.rightChain hd hd' g j) (h.endUseAccessOK hd hd' p j))
  · exact α.forall_mem_iff h.mem_rangeA fun a => α.forall_mem_iff h.mem_rangeA fun j =>
      imp_congr (h.active a) (imp_congr (not_congr (he.active a))
        (imp_congr (h.mem_ancs hd hd' j a) (not_congr (he.active j))))
  · exact π.forall_mem_iff h.P.mem_range fun q => imp_congr (hu.usable q)
      (α.forall_mem_iff (hu.mem_D q) fun x => h.endUseAnchorOK hd hd' p x)
  · exact π.forall_mem_iff h.P.mem_range fun l => imp_congr (h.endingLeaf hd hd' p l)
      (and_congr (by rw [h.pin]) (not_congr (hK.pinned l)))

/-- `endUse` steps correspond (§69, §58; §49, last paragraph). -/
theorem endUse_corr {p : Nat} (hS : Sim π α s s') :
    StepCorr π α (EndUseStep k p s) (EndUseStep (k.rename π α) (π.f p) s') :=
  guarded_corr (endUsePre_ren (KCorr.rename π α k) hS p)
    fun _ => endUseEff_ren hS.rel hS.down hS.down' p

/-- An `ok` step of `endUse` keeps downward links (§69, `ok` effect; §49, last paragraph). -/
theorem endUse_down {p : Nat} {t : S3} (hd : Down s) (hst : EndUseStep k p s (.ok t)) :
    Down t := by
  cases hst with
  | ok _ => exact endUseEff_down hd p

/-- An `ok` step of `endUse` keeps field order (§63.2, §69; §49, last paragraph): the places are
unchanged. -/
theorem endUse_sib {p : Nat} {t : S3} (_hP : PRel π s.P s'.P) (hs : SibMono π s.P)
    (hst : EndUseStep k p s (.ok t)) : SibMono π t.P := by
  cases hst with
  | ok _ => exact hs

/-! ## O13 `free` (§70) -/

/-- `OwnedRoot` is invariant (§70.1; §49, last paragraph). -/
theorem SRel.ownedRoot (h : SRel π α s s') (p : Nat) : OwnedRoot s' (π.f p) ↔ OwnedRoot s p := by
  unfold OwnedRoot
  rw [h.P.get]
  cases s.P[p]? with
  | none => exact Iff.rfl
  | some pl =>
    simp only [Option.map_some, OptP, Place.ren, Option.map_eq_none_iff, Holder.isPlace_ren]

/-- `freeS` is equivariant (§70, `ok` effect; §49, last paragraph). -/
theorem freeS_ren (h : SRel π α s s') (hd : Down s) (hd' : Down s') (p : Nat) :
    SRel π α (freeS s p) (freeS s' (π.f p)) :=
  { h with
    Alen := by simp only [freeS, List.length_map, h.Alen]
    A := fun x => by
      simp only [freeS, List.getElem?_map]
      refine optionRel_mapA (fun y y' hr => ?_) (h.A x)
      have hc : ((∃ l ∈ y'.footprint, FreedPlace s'.P (π.f p) l) ∨ heldIn s'.P (π.f p) y'.holder)
          ↔ ((∃ l ∈ y.footprint, FreedPlace s.P p l) ∨ heldIn s.P p y.holder) := by
        rw [hr.holder]
        exact or_congr
          (π.exists_mem_iff hr.mem_footprint fun l => freedPlace_ren h.P hd.1 hd'.1 p l)
          (heldIn_ren h.P hd.1 hd'.1 p y.holder)
      exact authRel_ite hc (authRel_off hr) hr
    Afix := fun x hx => h.Afix x (by simpa only [freeS, List.length_map] using hx)
    dead := fun q => by simp only [freeS, h.dead, freedPlace_ren h.P hd.1 hd'.1] }

/-- The effect of `free` is equivariant (§70, `ok` effect; §49, last paragraph). -/
theorem freeEff_ren (h : SRel π α s s') (hd : Down s) (hd' : Down s') (p : Nat) :
    SRel π α (freeEff s p) (freeEff s' (π.f p)) :=
  (freeS_ren h hd hd' p).cleanup

/-- `freeS` keeps downward links (§70, `ok` effect; §49, last paragraph). -/
theorem freeS_down (hd : Down s) (p : Nat) : Down (freeS s p) :=
  down_of_releases hd rfl (EndFree.freeS_releases s p)

/-- The effect of `free` keeps downward links (§70, `ok` effect; §49, last paragraph). -/
theorem freeEff_down (hd : Down s) (p : Nat) : Down (freeEff s p) :=
  cleanup_down (freeS_down hd p)

/-- Leaves of the released unit are invariant (§70.3, §70.4; §49, last paragraph). -/
theorem SRel.freedLeaf (h : SRel π α s s') (hd : Down s) (hd' : Down s') (p l : Nat) :
    FreedLeaf s' (π.f p) (π.f l) ↔ FreedLeaf s p l := by
  unfold FreedLeaf
  exact or_congr (h.mem_footprint hd hd' l p) (and_congr (isLeaf_ren h.P l)
    (and_congr (h.usable l) (not_congr ((freeS_ren h hd hd' p).usable l))))

/-- The access condition of `free` is invariant (§70.3; §49, last paragraph). -/
theorem SRel.freeAccessOK (h : SRel π α s s') (hd : Down s) (hd' : Down s') (p j : Nat) :
    FreeAccessOK s' (π.f p) (α.f j) ↔ FreeAccessOK s p j := by
  unfold FreeAccessOK
  cases hy : s.A[j]? with
  | none => rw [(h.A_none j).1 hy]; exact Iff.rfl
  | some y =>
    obtain ⟨y', hy', hr⟩ := h.A_some hy
    rw [hy']
    simp only [OptP]
    rw [hr.active, hr.origin, hr.holder]
    exact imp_congr Iff.rfl (imp_congr (not_congr Option.map_eq_none_iff)
      (imp_congr (π.exists_mem_iff hr.mem_footprint fun l => h.freedLeaf hd hd' p l)
        (or_congr (heldIn_ren h.P hd.1 hd'.1 p y.holder)
          (not_congr ((freeS_ren h hd hd' p).holderLive y.holder)))))

/-- The anchor condition of `free` is invariant (§70.3; §49, last paragraph). -/
theorem SRel.freeAnchorOK (h : SRel π α s s') (hd : Down s) (hd' : Down s') (p x : Nat) :
    FreeAnchorOK s' (π.f p) (α.f x) ↔ FreeAnchorOK s p x := by
  unfold FreeAnchorOK
  cases hy : s.A[x]? with
  | none => rw [(h.A_none x).1 hy]; exact Iff.rfl
  | some y =>
    obtain ⟨y', hy', hr⟩ := h.A_some hy
    rw [hy']
    simp only [OptP]
    rw [hr.holder]
    exact and_congr
      (not_congr (π.exists_mem_iff hr.mem_footprint fun l => freedPlace_ren h.P hd.1 hd'.1 p l))
      (and_congr (not_congr (heldIn_ren h.P hd.1 hd'.1 p y.holder))
        ((freeS_ren h hd hd' p).holderLive y.holder))

/-- The preconditions of `free` as a conjunction (§70). -/
private theorem freePre_iff {p auth : Nat} : FreePre k s p auth ↔
    (OwnedRoot s p ∧ k.Deallocable p ∧ k.FreeCompat p auth ∧ HasRight s .modify p ∧
    (∃ g ∈ List.range s.A.length, Grounds s .modify p g ∧
      ∀ j ∈ List.range s.A.length, RightChain s g j ∨ FreeAccessOK s p j) ∧
    (∀ a ∈ List.range s.A.length, ∀ j ∈ List.range s.A.length, s.Active a →
      ¬ (freeEff s p).Active a → a ∈ s.ancs j → ¬ (freeEff s p).Active j) ∧
    (∀ q ∈ List.range s.P.length, (freeS s p).Usable q → ∀ x ∈ s.D q, FreeAnchorOK s p x) ∧
    (∀ l ∈ List.range s.P.length, FreedLeaf s p l → s.pin l = false ∧ ¬ k.Pinned l)) :=
  ⟨fun ⟨a, b, c, d, e, f, g, h⟩ => ⟨a, b, c, d, e, f, g, h⟩,
   fun ⟨a, b, c, d, e, f, g, h⟩ => ⟨a, b, c, d, e, f, g, h⟩⟩

/-- The preconditions of `free` are invariant; `auth` is not renamed (§70, §70.2; §49, last
paragraph). -/
theorem freePre_ren (hK : KCorr π α k k') (hS : Sim π α s s') (p auth : Nat) :
    FreePre k' s' (π.f p) auth ↔ FreePre k s p auth := by
  obtain ⟨h, hd, hd', -⟩ := hS
  have hu := freeS_ren h hd hd' p
  have he := freeEff_ren h hd hd' p
  rw [freePre_iff, freePre_iff]
  refine and_congr (h.ownedRoot p) (and_congr (hK.dealloc p) (and_congr (hK.compat p auth)
    (and_congr (h.hasRight hd hd' .modify p) (and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))))))
  · exact α.exists_mem_iff h.mem_rangeA fun g => and_congr (h.grounds hd hd' .modify p g)
      (α.forall_mem_iff h.mem_rangeA fun j =>
        or_congr (h.rightChain hd hd' g j) (h.freeAccessOK hd hd' p j))
  · exact α.forall_mem_iff h.mem_rangeA fun a => α.forall_mem_iff h.mem_rangeA fun j =>
      imp_congr (h.active a) (imp_congr (not_congr (he.active a))
        (imp_congr (h.mem_ancs hd hd' j a) (not_congr (he.active j))))
  · exact π.forall_mem_iff h.P.mem_range fun q => imp_congr (hu.usable q)
      (α.forall_mem_iff (h.mem_D q) fun x => h.freeAnchorOK hd hd' p x)
  · exact π.forall_mem_iff h.P.mem_range fun l => imp_congr (h.freedLeaf hd hd' p l)
      (and_congr (by rw [h.pin]) (not_congr (hK.pinned l)))

/-- `free` steps correspond; `auth` is not renamed (§70, §70.2, §58; §49, last paragraph). -/
theorem free_corr {p auth : Nat} (hS : Sim π α s s') :
    StepCorr π α (FreeStep k p auth s) (FreeStep (k.rename π α) (π.f p) auth s') :=
  guarded_corr (freePre_ren (KCorr.rename π α k) hS p auth)
    fun _ => freeEff_ren hS.rel hS.down hS.down' p

/-- An `ok` step of `free` keeps downward links (§70, `ok` effect; §49, last paragraph). -/
theorem free_down {p auth : Nat} {t : S3} (hd : Down s) (hst : FreeStep k p auth s (.ok t)) :
    Down t := by
  cases hst with
  | ok _ => exact freeEff_down hd p

/-- An `ok` step of `free` keeps field order (§63.2, §70; §49, last paragraph): the places are
unchanged. -/
theorem free_sib {p auth : Nat} {t : S3} (_hP : PRel π s.P s'.P) (hs : SibMono π s.P)
    (hst : FreeStep k p auth s (.ok t)) : SibMono π t.P := by
  cases hst with
  | ok _ => exact hs

/-! ## O14 `alloc` (§71) -/

/-- The preconditions of `writeShared` as a conjunction (§68). -/
private theorem allocWSPre_iff {a : Nat} {ls : List Nat} : WriteSharedPre k s a ls ↔
    ((∀ l ∈ ls, LeafOfUsable s l) ∧ (∀ l ∈ ls, k.SharedMutable l) ∧
    s.ExercisableAt a .observe ∧ (∀ l ∈ ls, effective s a l ≠ none) ∧
    (∀ l ∈ ls, DepsValid s l)) :=
  ⟨fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩, fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩⟩

/-- The `writeShared` alternative of §71.2 is invariant on corresponding leaf lists (§68, §71.2;
§49, last paragraph). -/
private theorem allocWSPre_ren (hK : KCorr π α k k') (h : SRel π α s s') (hd : Down s)
    (hd' : Down s') {ls ls' : List Nat} (hls : ∀ l, π.f l ∈ ls' ↔ l ∈ ls) (a : Nat) :
    WriteSharedPre k' s' (α.f a) ls' ↔ WriteSharedPre k s a ls := by
  rw [allocWSPre_iff, allocWSPre_iff]
  exact and_congr (π.forall_mem_iff hls fun l => h.leafOfUsable hd hd' l)
    (and_congr (π.forall_mem_iff hls hK.shared) (and_congr (h.exercisableAt hd hd' a .observe)
      (and_congr (π.forall_mem_iff hls fun l => by rw [h.effective hd hd'])
        (π.forall_mem_iff hls fun l => h.depsValid hd hd' l))))

/-- The static preconditions of `alloc` as a conjunction (§71). -/
private theorem allocStatic_iff {pr ow : Nat} {ls : LocalShape} : AllocStatic k s pr ow ls ↔
    (ls ≠ [] ∧ ShapeOK s.P.length ls.toShape ∧ (rootIdx ls.toShape).length = 1 ∧
    s.Usable pr ∧ (∀ l ∈ footprint s.P pr, s.I l = .init) ∧
    (HasRight s .modify pr ∨
      ∃ via ∈ List.range s.A.length, WriteSharedPre k s via (footprint s.P pr)) ∧
    HasRight s .modify ow ∧ s.Usable ow) :=
  ⟨fun ⟨a, b, c, d, e, f, g, h⟩ => ⟨a, b, c, d, e, f, g, h⟩,
   fun ⟨a, b, c, d, e, f, g, h⟩ => ⟨a, b, c, d, e, f, g, h⟩⟩

/-- The static preconditions of `alloc` are invariant; the shape is not renamed (§71, §71.1;
§49, last paragraph). -/
theorem allocStatic_ren (hK : KCorr π α k k') (hS : Sim π α s s') (pr ow : Nat)
    (ls : LocalShape) : AllocStatic k' s' (π.f pr) (π.f ow) ls ↔ AllocStatic k s pr ow ls := by
  obtain ⟨h, hd, hd', -⟩ := hS
  rw [allocStatic_iff, allocStatic_iff, h.P.len]
  exact and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl (and_congr (h.usable pr)
    (and_congr (π.forall_mem_iff (fun l => h.mem_footprint hd hd' l pr) fun l => by rw [h.I])
      (and_congr (or_congr (h.hasRight hd hd' .modify pr)
        (α.exists_mem_iff h.mem_rangeA fun via =>
          allocWSPre_ren hK h hd hd' (fun l => h.mem_footprint hd hd' l pr) via))
        (and_congr (h.hasRight hd hd' .modify ow) (h.usable ow)))))))

/-- The effect of `alloc` is equivariant; the shape is not renamed, its new identities are fixed
(§71, `ok` outcome, §71.1; §49, last paragraph). -/
theorem allocEff_ren (h : SRel π α s s') (hd : Down s) (hd' : Down s') (ow : Nat)
    (ls : LocalShape) (hok : ShapeOK s.P.length ls.toShape) :
    SRel π α (allocEff s ow ls) (allocEff s' (π.f ow) ls) := by
  have hok' : ShapeOK s'.P.length ls.toShape := by rw [h.P.len]; exact hok
  have hP₁ : PRel π (allocP s ow ls) (allocP s' (π.f ow) ls) := shapeP_ren h.P hok (.place ow)
  have hd₁ : DownP (allocP s ow ls) := shapeP_down hd.1 hok
  have hd₁' : DownP (allocP s' (π.f ow) ls) := shapeP_down hd'.1 hok'
  have hle : ∀ q, s'.P.length ≤ π.f q ↔ s.P.length ≤ q := fun q => by
    rw [← Nat.not_lt, ← Nat.not_lt, h.P.lt_iff]
  exact
  { F := h.F
    nF := h.nF
    P := hP₁
    I := fun l => by simp only [allocEff, hle, h.I]
    Alen := by simp only [allocEff, List.length_append, List.length_map, h.Alen]
    A := fun x => by
      simp only [allocEff]
      by_cases hx : x < s.A.length
      · rw [List.getElem?_append_left hx, List.getElem?_append_left ((h.Alt x).2 hx)]
        exact h.A x
      · rw [h.Afix x (by omega), List.getElem?_append_right (by omega),
          List.getElem?_append_right (by rw [h.Alen]; omega), h.Alen, List.getElem?_map,
          List.getElem?_map]
        cases (rootIdx ls.toShape)[x - s.A.length]? with
        | none => exact .none
        | some i =>
          refine .some ⟨rfl, rfl, ?_, ?_, rfl⟩
          · have := footprint_perm_ren hP₁ hd₁ hd₁' (s.P.length + i)
            rw [h.P.fix _ (Nat.le_add_right _ _)] at this
            show (footprint (allocP s' (π.f ow) ls) (s'.P.length + i)).Perm _
            rw [h.P.len]; exact this
          · show shapeOwner ls.toShape (.place (π.f ow)) i =
              (shapeOwner ls.toShape (.place ow) i).ren π
            rw [Alloc.shapeOwner_toShape, Alloc.shapeOwner_toShape]; rfl
    Afix := fun x hx => h.Afix x (by
      simp only [allocEff, List.length_append] at hx; omega)
    D := fun q => by
      by_cases hq : s.P.length ≤ q
      · simp only [allocEff, hq, (hle q).2 hq, ↓reduceIte, List.map_nil]; exact .nil
      · simp only [allocEff, hq, mt (hle q).1 hq, ↓reduceIte]; exact h.D q
    dead := fun q => by simp only [allocEff, hle, h.dead]
    pins := h.pins }

/-- The new authorities of `alloc` have no origin, so origin links are kept (§71, `ok` outcome;
§42). -/
private theorem allocEff_org (s : S3) (ow : Nat) (ls : LocalShape) :
    (allocEff s ow ls).org = s.org := by
  funext j
  simp only [S3.org, allocEff]
  by_cases hj : j < s.A.length
  · rw [List.getElem?_append_left hj]
  · rw [List.getElem?_append_right (by omega), List.getElem?_eq_none (by omega : s.A.length ≤ j),
      List.getElem?_map]
    cases (rootIdx ls.toShape)[j - s.A.length]? <;> rfl

/-- The effect of `alloc` keeps downward links (§71, `ok` outcome, §71.1; §49, last
paragraph). -/
theorem allocEff_down (hd : Down s) {ow : Nat} {ls : LocalShape}
    (hok : ShapeOK s.P.length ls.toShape) : Down (allocEff s ow ls) :=
  ⟨shapeP_down hd.1 hok, fun j o ho => hd.2 j o (by rw [← allocEff_org s ow ls]; exact ho)⟩

/-- `Satisfiable` of the renamed contract on related states (§71; §49, last paragraph). The
direction from the renamed side uses the interface obligation `KExt` (§42, §44). -/
theorem satisfiable_ren (hk : KExt k) (h : SRel π α s s') (pr : Nat) (ls : LocalShape) :
    (k.rename π α).Satisfiable (π.f pr) ls s' ↔ k.Satisfiable pr ls s := by
  show (∃ t₀, SRel π α t₀ s' ∧ k.Satisfiable (π.g (π.f pr)) ls t₀) ↔ _
  rw [π.gf]
  constructor
  · rintro ⟨t₀, h₀, ht⟩
    have h₁ := h₀.trans h.symm
    rw [Ren.symm_comp, Ren.symm_comp] at h₁
    exact hk pr ls t₀ s h₁ ht
  · intro hs
    exact ⟨s, h, hs⟩

/-- `alloc` steps correspond, `reject`, `fail` and `ok` alike; the shape is not renamed (§71,
§58; §49, last paragraph). -/
theorem alloc_corr {pr ow : Nat} {ls : LocalShape} (hk : KExt k) (hS : Sim π α s s') :
    StepCorr π α (AllocStep k pr ow ls s)
      (AllocStep (k.rename π α) (π.f pr) (π.f ow) ls s') := by
  have hst := allocStatic_ren (KCorr.rename π α k) hS pr ow ls
  have hsat := satisfiable_ren hk hS.rel pr ls
  constructor
  · intro o ho
    cases ho with
    | ok h1 h2 =>
      exact ⟨_, .ok (hst.2 h1) (hsat.2 h2),
        allocEff_ren hS.rel hS.down hS.down' ow ls h1.shapeOK⟩
    | fail h1 h2 => exact ⟨_, .fail (hst.2 h1) (fun h => h2 (hsat.1 h)), trivial⟩
    | reject h1 => exact ⟨_, .reject (fun h => h1 (hst.1 h)), trivial⟩
  · intro o' ho'
    cases ho' with
    | ok h1 h2 =>
      exact ⟨_, .ok (hst.1 h1) (hsat.1 h2),
        allocEff_ren hS.rel hS.down hS.down' ow ls (hst.1 h1).shapeOK⟩
    | fail h1 h2 => exact ⟨_, .fail (hst.1 h1) (fun h => h2 (hsat.2 h)), trivial⟩
    | reject h1 => exact ⟨_, .reject (fun h => h1 (hst.2 h)), trivial⟩

/-- An `ok` step of `alloc` keeps downward links (§71, `ok` outcome; §49, last paragraph). -/
theorem alloc_down {pr ow : Nat} {ls : LocalShape} {t : S3} (hd : Down s)
    (hst : AllocStep k pr ow ls s (.ok t)) : Down t := by
  cases hst with
  | ok h1 _ => exact allocEff_down hd h1.shapeOK

/-- An `ok` step of `alloc` keeps field order (§63.2, §71; §49, last paragraph): the new places
are appended. -/
theorem alloc_sib {pr ow : Nat} {ls : LocalShape} {t : S3} (hP : PRel π s.P s'.P)
    (hs : SibMono π s.P) (hst : AllocStep k pr ow ls s (.ok t)) : SibMono π t.P := by
  cases hst with
  | ok _ _ => exact shapeP_sib hP hs

end Ern.MemoryModel.Access.Rename
