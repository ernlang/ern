import Ern.MemoryModel.Access.Main

/-!
# Access kernel: no active authority covers a leaf of its own holder

The auxiliary invariant `NoSelfLock` (not a clause of §57 of
`specs/ERN_Memory_Model_Specification.md`): no authority satisfies `SelfLock` (§63.8). It
holds initially (§47) and every kernel step keeps it from a `WF3` state (§49): `transfer` through
§63.8, `store` through §65.3, `alloc` because its new root covers only new leaves (§71), the other
steps because they move no holder onto a covered place (§60–§75 `ok` effects). Hence it holds on
every reachable state (§57, `reachable_noSelfLock`).
-/

namespace Ern.MemoryModel.Access

/-- `NoSelfLock` (auxiliary invariant, not a clause of §57): no authority is `SelfLock` (§63.8;
kept by §63.8 and §65.3, see also §88). -/
def NoSelfLock (s : S3) : Prop := ∀ x, ¬ SelfLock s x

/-- Introduction of `NoSelfLock` (§63.8). -/
theorem noSelfLock_intro {s : S3}
    (h : ∀ (x : Nat) (y : Authority) (l : Nat), s.A[x]? = some y → y.active = true →
      l ∈ y.footprint → l ∈ holderLeaves s y.holder → False) : NoSelfLock s := by
  intro x hx
  unfold SelfLock at hx
  cases hy : s.A[x]? with
  | none => rw [hy] at hx; exact hx
  | some y => rw [hy] at hx; obtain ⟨ya, l, hl, hh⟩ := hx; exact h x y l hy ya hl hh

/-- Elimination of `NoSelfLock` (§63.8). -/
theorem NoSelfLock.elim {s : S3} (h : NoSelfLock s) {x : Nat} {y : Authority} {l : Nat}
    (hy : s.A[x]? = some y) (ya : y.active = true) (hl : l ∈ y.footprint)
    (hh : l ∈ holderLeaves s y.holder) : False :=
  h x (by unfold SelfLock; rw [hy]; exact ⟨ya, l, hl, hh⟩)

/-- A frame has no leaves (§63.8). -/
theorem not_mem_holderLeaves_frame {s : S3} {f l : Nat} : l ∉ holderLeaves s (.frame f) :=
  fun h => by simp [holderLeaves] at h

/-- `NoSelfLock` depends only on the places and the authorities (§38, §63.8). -/
theorem NoSelfLock.congr {s s' : S3} (h : NoSelfLock s) (hA : s'.A = s.A) (hP : s'.P = s.P) :
    NoSelfLock s' :=
  noSelfLock_intro fun x y l hy ya hl hh => by
    rw [hA] at hy
    exact h.elim hy ya hl (by unfold holderLeaves at hh ⊢; rw [hP] at hh; exact hh)

/-- An element of an appended list comes from one of the two parts (§42: authorities added by
`split`). -/
private theorem getElem?_append_cases {α : Type} {l E : List α} {x : Nat} {y : α}
    (h : (l ++ E)[x]? = some y) : l[x]? = some y ∨ y ∈ E := by
  by_cases hx : x < l.length
  · rw [List.getElem?_append_left hx] at h; exact .inl h
  · rw [List.getElem?_append_right (by omega)] at h; exact .inr (List.mem_of_getElem? h)

/-! ## The initial state (§47) -/

/-- The initial state satisfies `NoSelfLock` for a well-formed statics declaration (`StaticsOK`,
§47): the root authority of a root static is held by frame 0 or by its owning static, an earlier
static that is not a part of it (§40, §47). -/
theorem init_noSelfLock {statics : Statics} (hst : StaticsOK statics) :
    NoSelfLock (S3.init statics) := by
  have hw : WF3 (S3.init statics) := (init_kinv hst).1.1
  have hlen : (S3.init statics).P.length = statics.length := by simp [S3.init, shapeP]
  refine noSelfLock_intro fun x y l hy ya hl hh => ?_
  simp only [S3.init, List.getElem?_map] at hy
  obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.1 hy
  have hmem := List.mem_of_getElem? hi
  simp only [rootIdx, List.mem_filter, List.mem_range, Option.isNone_iff_eq_none] at hmem
  obtain ⟨hil, hpn⟩ := hmem
  have hroot : RootPlace (S3.init statics).P i := by
    refine ⟨by rw [hlen]; simpa using hil, ?_⟩
    simp only [parentOf, S3.init, shapeP, List.nil_append, List.getElem?_map,
      List.getElem?_range hil, Option.map_some, Option.bind_some]
    simpa using hpn
  simp only [shapeOwner] at hh
  split at hh
  · rename_i o ho
    have hoi : o < i := by
      have := (hst i (List.mem_range.2 hil)).2
      rw [ho] at this; have := this.2; omega
    obtain ⟨r, hr, hor⟩ := exists_rootPlace hw (o + 1) o (Nat.lt_succ_self o)
      (by rw [hlen]; simp at hil; omega)
    have hlr := footprint_sub hw hor hh
    obtain rfl := rootOf_unique hr hroot (mem_footprint.1 hlr).2.2 (mem_footprint.1 hl).2.2
    have := Frames.partOf_le hor; omega
  · exact not_mem_holderLeaves_frame hh

/-! ## Preservation by every step (§60–§75) -/

/-- Every kernel step keeps `NoSelfLock` from a `WF3` state (§49.8: holders of active authorities
are live): `derive`, `split` and `enterFrame` add frame-held authorities (§60, §61, §72);
`release`, `exitFrame`, `endUse`, `free` only deactivate, reanchor or keep authorities (§62, §73,
§69, §70); `transfer` is guarded by §63.8 and keeps footprints (§63); `store` by §65.3; the new
root of `alloc` covers only new leaves, its owner only former ones (§71); the remaining steps
change neither places nor authorities (§64, §66–§68, §74, §75). -/
theorem kstep_preserves_noSelfLock {k : K} {s s' : S3} (hw : WF3 s) (hns : NoSelfLock s)
    (h : KStep k s s') : NoSelfLock s' := by
  cases h with
  | derive h =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
    refine noSelfLock_intro fun x y l hy ya hl hh => ?_
    rcases addAuth_get hy with ⟨-, hy⟩ | ⟨-, rfl⟩
    · exact hns.elim hy ya hl hh
    · exact not_mem_holderLeaves_frame hh
  | split h =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
    refine noSelfLock_intro fun x y l hy ya hl hh => ?_
    rcases getElem?_append_cases hy with hy | hy
    · exact hns.elim hy ya hl hh
    · obtain ⟨r, -, rfl⟩ := List.mem_map.1 hy; exact not_mem_holderLeaves_frame hh
  | release h =>
    rename_i a
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
    cases hx₀ : s.A[a]? with
    | none => simp only [releaseEff, hx₀]; exact hns
    | some x₀ =>
      rw [releaseEff_eq hx₀]
      refine noSelfLock_intro fun x y l hy ya hl hh => ?_
      simp only [set_get (lt_of_getElem? hx₀)] at hy
      split at hy
      · cases hy; cases ya
      · exact hns.elim hy ya hl hh
  | transfer h =>
    rename_i src dst
    obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
    refine noSelfLock_intro fun x y l hy ya hl hh => ?_
    have hy' := hy
    rw [transfer_A_get] at hy'
    obtain ⟨y₀, hy₀, e⟩ := Option.map_eq_some_iff.1 hy'
    by_cases hin : heldIn s.P src y₀.holder
    · refine hpre.noSelfLock x (List.mem_range.2 (lt_of_getElem? hy₀)) (by rw [hy₀]; exact hin) ?_
      unfold SelfLock; rw [hy]; exact ⟨ya, l, hl, hh⟩
    · simp only [hin, ↓reduceIte] at e; subst e
      refine hns.elim hy₀ ya hl ?_
      cases hho : y₀.holder with
      | frame f => rw [hho] at hh; exact absurd hh not_mem_holderLeaves_frame
      | place q =>
        rw [hho] at hh
        show l ∈ footprint s.P q
        rw [← transfer_footprint s src dst q]; exact hh
  | depend h =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; exact hns.congr rfl rfl
  | enter h =>
    rename_i ps ls
    obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
    refine noSelfLock_intro fun x y l hy ya hl hh => ?_
    rcases Frames.enter_get hy with ⟨-, y₀, hy₀, e⟩ | ⟨-, i, -, rfl⟩
    · split at e
      · subst e; exact not_mem_holderLeaves_frame hh
      · subst e
        cases hho : y.holder with
        | frame f => rw [hho] at hh; exact not_mem_holderLeaves_frame hh
        | place q =>
          rw [hho] at hh
          have hu : s.Usable q := by have := hw.holders x y hy₀ ya; rw [hho] at this; exact this
          refine hns.elim hy₀ ya hl ?_
          rw [hho]; exact (Frames.enter_footprint_old hpre.localsOK hu.lt l).1 hh
    · exact not_mem_holderLeaves_frame hh
  | exit h =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
    refine noSelfLock_intro fun x y l hy ya hl hh => ?_
    obtain ⟨y₀, hy₀, rfl⟩ := Frames.exit_get hy
    obtain ⟨-, hf, hh'⟩ := Frames.exitG_same s s.F.tail x y₀
    rw [hf] at hl; rw [hh'] at hh
    exact hns.elim hy₀ (Frames.exitG_active' hy₀ ya) hl hh
  | read h => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; exact hns
  | write h => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; exact hns.congr rfl rfl
  | writeShared h => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; exact hns.congr rfl rfl
  | pin h => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; exact hns.congr rfl rfl
  | unpin h => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; exact hns.congr rfl rfl
  | endUse h =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
    exact noSelfLock_intro fun x y l hy ya hl hh =>
      hns.elim (EndFree.endUse_active hy ya).1 ya hl hh
  | free h =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
    exact noSelfLock_intro fun x y l hy ya hl hh =>
      hns.elim (EndFree.free_active hy ya).1 ya hl hh
  | alloc h =>
    cases h with
    | ok hst _ =>
      refine noSelfLock_intro fun x y l hy ya hl hh => ?_
      rcases Alloc.allocA_get hst hy with ⟨-, hy₀⟩ | ⟨-, rfl⟩
      · cases hho : y.holder with
        | frame f => rw [hho] at hh; exact not_mem_holderLeaves_frame hh
        | place q =>
          rw [hho] at hh
          have hu : s.Usable q := by have := hw.holders x y hy₀ ya; rw [hho] at this; exact this
          refine hns.elim hy₀ ya hl ?_
          rw [hho]; exact (Alloc.footprint_old hst.shapeOK hu.lt l).1 hh
      · have h1 := Alloc.fp_new_ge hl
        have h2 := (Alloc.footprint_old hst.shapeOK hst.ownerUsable.lt l).1 hh
        have := (mem_footprint.1 h2).1; omega
  | store h =>
    rename_i a p
    obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
    cases hy₁ : s.A[a]? with
    | none => simp only [storeEff, hy₁]; exact hns
    | some y₁ =>
      have heq : storeEff s a p = { s with
          A := s.A.set a { y₁ with holder := .place p }
          D := fun q => if q = p then s.D p ++ [a] else s.D q
          I := fun l => if l = p then .init else s.I l } := by
        simp only [storeEff, hy₁]
      rw [heq]
      refine noSelfLock_intro fun x y l hy ya hl hh => ?_
      simp only [set_get (lt_of_getElem? hy₁)] at hy
      split at hy
      · cases hy
        exact (hpre.noCover l (by simp only [S3.afp, hy₁]; exact hl)).1 hh
      · exact hns.elim hy ya hl hh

/-! ## Reachable states (§57) -/

/-- `NoSelfLock` (auxiliary invariant, not a clause of §57; §63.8, §65.3) holds on every state
reachable from `S3.init statics`, under `DDSound` (§80, through `reachable_kinv`, which gives
`WF3`) and `StaticsOK` (§47). -/
theorem reachable_noSelfLock {k : K} {statics : Statics} {s : S3} (hdd : DDSound k)
    (hst : StaticsOK statics) (h : Reachable k statics s) : NoSelfLock s := by
  induction h with
  | init => exact init_noSelfLock hst
  | step hr h ih => exact kstep_preserves_noSelfLock (reachable_kinv hdd hst hr).1 ih h

end Ern.MemoryModel.Access
