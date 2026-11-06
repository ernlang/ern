import Ern.MemoryModel.Access.Rename.Basic

/-!
# Renaming of identities: places

Equivariance of the place-level notions of `specs/ERN_Memory_Model_Specification.md` under a
renaming of identities (§49, last paragraph): parent chains, parts, leaves and footprints (§40),
overlap (§63.3), transitive ownership (§40), root places (§40), released units (§70), children,
positional correspondence and same shape (§63.2), holders within a value and their move (§63),
and the places appended from a shape (§47, §71, §72).
-/

namespace Ern.MemoryModel.Access.Rename

variable {π : Ren} {P P' : List Place}

/-- A renamed option is a renamed `some` exactly when the option is that `some` (§49, last
paragraph). -/
theorem Ren.option_map_eq_some (π : Ren) (o : Option Nat) (x : Nat) :
    o.map π.f = some (π.f x) ↔ o = some x := by
  cases o <;> simp [Ren.f_inj]

/-! ## Chains, parts, leaves, footprints (§40) -/

/-- Chains along links related by an injective map, both downward, correspond (§40 parents, §42
origins; §49, last paragraph). -/
theorem chain_ren {org org' : Nat → Option Nat} {f : Nat → Nat}
    (hd : ∀ j o, org j = some o → o < j) (hd' : ∀ j o, org' j = some o → o < j)
    (h : ∀ j, org' (f j) = (org j).map f) : ∀ i, chain org' (f i) = (chain org i).map f := by
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
    cases ho : org i with
    | none => rw [chain_none ho, chain_none (by rw [h, ho]; rfl)]; rfl
    | some o =>
      have h' : org' (f i) = some (f o) := by rw [h, ho]; rfl
      rw [chain_cons ho (hd _ _ ho), chain_cons h' (hd' _ _ h'), ih o (hd _ _ ho)]
      rfl

/-- Structural parents of related place lists correspond (§40; §49, last paragraph). -/
theorem PRel.parentOf (hP : PRel π P P') (q : Nat) :
    parentOf P' (π.f q) = (parentOf P q).map π.f := by
  simp only [Ern.MemoryModel.Access.parentOf, hP.get]
  cases P[q]? <;> simp [Place.ren]

/-- A renamed place has the renamed parent exactly when the place has that parent (§40; §49,
last paragraph). -/
theorem PRel.parentOf_eq_some (hP : PRel π P P') (q p : Nat) :
    Access.parentOf P' (π.f q) = some (π.f p) ↔ Access.parentOf P q = some p := by
  rw [hP.parentOf, π.option_map_eq_some]

/-- Structural parent chains correspond (§40; §49, last paragraph). -/
theorem chainP_ren (hP : PRel π P P') (hd : DownP P) (hd' : DownP P') (q : Nat) :
    chain (parentOf P') (π.f q) = (chain (parentOf P) q).map π.f :=
  chain_ren hd hd' hP.parentOf q

/-- `partOf` is invariant (§40; §49, last paragraph). -/
theorem partOf_ren (hP : PRel π P P') (hd : DownP P) (hd' : DownP P') (p q : Nat) :
    partOf P' (π.f p) (π.f q) ↔ partOf P p q := by
  simp only [partOf, hP.lt_iff, chainP_ren hP hd hd', π.mem_map_f, Ren.f_inj]

/-- Leaves are invariant (§40; §49, last paragraph). -/
theorem isLeaf_ren (hP : PRel π P P') (l : Nat) : isLeaf P' (π.f l) ↔ isLeaf P l := by
  unfold isLeaf
  refine π.forall_iff fun r => ?_
  rw [hP.lt_iff, Ne, hP.parentOf_eq_some]

/-- `footprint` membership is invariant (§40; §49, last paragraph). -/
theorem mem_footprint_ren (hP : PRel π P P') (hd : DownP P) (hd' : DownP P') (l q : Nat) :
    π.f l ∈ footprint P' (π.f q) ↔ l ∈ footprint P q := by
  simp only [mem_footprint, hP.lt_iff, isLeaf_ren hP, partOf_ren hP hd hd']

/-- A footprint has no duplicate (§40: a set of leaves; §49, last paragraph). -/
theorem footprint_nodup (P : List Place) (q : Nat) : (footprint P q).Nodup :=
  List.Pairwise.filter _ List.nodup_range

/-- Footprints correspond up to permutation (§40, §42: a set; §49, last paragraph). -/
theorem footprint_perm_ren (hP : PRel π P P') (hd : DownP P) (hd' : DownP P') (q : Nat) :
    (footprint P' (π.f q)).Perm ((footprint P q).map π.f) :=
  π.perm_of_mem (footprint_nodup P q) (footprint_nodup P' _) fun l =>
    mem_footprint_ren hP hd hd' l q

/-- `overlap` is invariant (§63.3; §49, last paragraph). -/
theorem overlap_ren (hP : PRel π P P') (hd : DownP P) (hd' : DownP P') (p q : Nat) :
    overlap P' (π.f p) (π.f q) ↔ overlap P p q :=
  π.exists_mem_iff (fun x => mem_footprint_ren hP hd hd' x p)
    (fun x => mem_footprint_ren hP hd hd' x q)

/-! ## Ownership, root places, released units (§40, §70) -/

/-- `OwnedIn` is preserved forward (§40; §49, last paragraph). -/
theorem ownedIn_ren_of (hP : PRel π P P') (hd : DownP P) (hd' : DownP P') {src q : Nat}
    (h : OwnedIn P src q) : OwnedIn P' (π.f src) (π.f q) := by
  induction h with
  | direct hpl ho hp =>
    exact .direct (by rw [hP.get, hpl]; rfl) (by simp only [Place.ren, ho, Holder.ren])
      ((partOf_ren hP hd hd' _ _).2 hp)
  | step hpl ho _ ih =>
    exact .step (by rw [hP.get, hpl]; rfl) (by simp only [Place.ren, ho, Holder.ren]) ih

/-- `OwnedIn` is invariant (§40; §49, last paragraph). -/
theorem ownedIn_ren (hP : PRel π P P') (hd : DownP P) (hd' : DownP P') (src q : Nat) :
    OwnedIn P' (π.f src) (π.f q) ↔ OwnedIn P src q :=
  ⟨fun h => by simpa only [Ren.symm_f, π.gf] using ownedIn_ren_of hP.symm hd' hd h,
   ownedIn_ren_of hP hd hd'⟩

/-- Root places are invariant (§40; §49, last paragraph). -/
theorem rootPlace_ren (hP : PRel π P P') (r : Nat) : RootPlace P' (π.f r) ↔ RootPlace P r := by
  simp only [RootPlace, hP.lt_iff, hP.parentOf, Option.map_eq_none_iff]

/-- Places of a released unit are invariant (§70; §49, last paragraph). -/
theorem freedPlace_ren (hP : PRel π P P') (hd : DownP P) (hd' : DownP P') (p q : Nat) :
    FreedPlace P' (π.f p) (π.f q) ↔ FreedPlace P p q := by
  simp only [FreedPlace, partOf_ren hP hd hd', ownedIn_ren hP hd hd']

/-! ## Children, correspondence, same shape (§63.2) -/

/-- Children are listed in increasing index order (§63.2; §49, last paragraph). -/
theorem kids_sorted (P : List Place) (x : Nat) : (kids P x).Pairwise (· < ·) :=
  List.pairwise_lt_range.filter _

/-- Children correspond in order when `π` keeps field order (§63.2; §49, last paragraph). -/
theorem kids_ren (hP : PRel π P P') (hs : SibMono π P) (x : Nat) :
    kids P' (π.f x) = (kids P x).map π.f := by
  apply eq_of_sorted_mem (kids_sorted P' _)
  · rw [List.pairwise_map]
    refine (kids_sorted P x).imp_of_mem fun {a b} ha hb hab => ?_
    exact hs a b x (mem_kids.1 ha).2 (mem_kids.1 hb).2 hab
  · intro a
    rw [← π.fg a, π.mem_map_f, mem_kids, mem_kids, hP.lt_iff, hP.parentOf_eq_some]

/-- `corr` of a part without parent other than `src` is undefined (§63.2; §49, last
paragraph). -/
theorem corr_none {src dst r : Nat} (hr : r ≠ src) (hp : parentOf P r = none) :
    corr P src dst r = none := by
  unfold corr; cases r <;> simp [corrF, hr, hp]

/-- `corr` is equivariant when `π` keeps field order (§63.2; §49, last paragraph). -/
theorem corr_ren (hP : PRel π P P') (hd : DownP P) (hd' : DownP P') (hs : SibMono π P)
    (src dst : Nat) : ∀ r, corr P' (π.f src) (π.f dst) (π.f r) = (corr P src dst r).map π.f := by
  intro r
  induction r using Nat.strongRecOn with
  | _ r ih =>
    by_cases hr : r = src
    · subst hr; rw [corr_src, corr_src]; rfl
    · have hr' : π.f r ≠ π.f src := fun e => hr ((Ren.f_inj π).1 e)
      cases hp : parentOf P r with
      | none =>
        rw [corr_none hr hp, corr_none hr' (by rw [hP.parentOf, hp]; rfl)]; rfl
      | some p =>
        have hp' : parentOf P' (π.f r) = some (π.f p) := by rw [hP.parentOf, hp]; rfl
        rw [corr_step hr hp (hd _ _ hp), corr_step hr' hp' (hd' _ _ hp'), ih p (hd _ _ hp),
          kids_ren hP hs p, posIn_map (fun _ _ e => (Ren.f_inj π).1 e)]
        cases corr P src dst p with
        | none => rfl
        | some p0 =>
          simp only [Option.map_some, Option.bind_some, kids_ren hP hs p0, List.getElem?_map]

/-- `SameShape` is invariant when `π` keeps field order (§63.2; §49, last paragraph). -/
theorem sameShape_ren (hP : PRel π P P') (hd : DownP P) (hd' : DownP P') (hs : SibMono π P)
    (src dst : Nat) : SameShape P' (π.f src) (π.f dst) ↔ SameShape P src dst := by
  unfold SameShape
  refine and_congr (π.forall_mem_iff hP.mem_range fun r => ?_)
    (π.forall_mem_iff hP.mem_range fun z => ?_)
  · rw [partOf_ren hP hd hd', corr_ren hP hd hd' hs]
    refine imp_congr_right fun _ => ?_
    cases corr P src dst r with
    | none => exact Iff.rfl
    | some c => simp only [Option.map_some, OptP, kids_ren hP hs, List.length_map]
  · rw [partOf_ren hP hd hd']
    refine imp_congr_right fun _ => π.exists_mem_iff hP.mem_range fun r => ?_
    rw [partOf_ren hP hd hd', corr_ren hP hd hd' hs, π.option_map_eq_some]

/-! ## Holders within a value and their move (§63, §69, §70) -/

/-- `heldIn` is invariant (§63, §69, §70; §49, last paragraph). -/
theorem heldIn_ren (hP : PRel π P P') (hd : DownP P) (hd' : DownP P') (q : Nat) (o : Holder) :
    heldIn P' (π.f q) (o.ren π) ↔ heldIn P q o := by
  cases o with
  | frame f => exact Iff.rfl
  | place r => exact partOf_ren hP hd hd' r q

/-- The move of a holder by `transfer` is equivariant when `π` keeps field order (§63, `ok`
effect; §49, last paragraph). -/
theorem mvTo_ren (hP : PRel π P P') (hd : DownP P) (hd' : DownP P') (hs : SibMono π P)
    (src dst : Nat) (o : Holder) :
    mvTo P' (π.f src) (π.f dst) (o.ren π) = (mvTo P src dst o).ren π := by
  cases o with
  | frame f => rfl
  | place r => simp only [Holder.ren, mvTo, corr_ren hP hd hd' hs, Option.getD_map]

/-! ## Places appended from a shape (§47, §71, §72) -/

/-- The former places of `shapeP` (§47, §71, §72; §49, last paragraph). -/
theorem shapeP_get_old {hd : Holder} {ls : List (Option Nat × Option Nat × Nat)} {q : Nat}
    (hq : q < P.length) : (shapeP P hd ls)[q]? = P[q]? :=
  List.getElem?_append_left hq

/-- The appended places of `shapeP` (§47, §71, §72; §49, last paragraph). -/
theorem shapeP_get_new (P : List Place) (hd : Holder) (ls : List (Option Nat × Option Nat × Nat))
    (i : Nat) : (shapeP P hd ls)[P.length + i]? = if i < ls.length then
      some ⟨(ls[i]?).bind (·.1), shapeOwner ls hd i, ((ls[i]?).map (·.2.2)).getD 0⟩ else none := by
  simp only [shapeP, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    List.getElem?_map]
  split
  · rename_i hi; rw [List.getElem?_range hi]; rfl
  · rename_i hi
    rw [List.getElem?_eq_none_iff.2 (by simp only [List.length_range]; omega)]; rfl

/-- Parents of the former places of `shapeP` (§47, §71, §72; §49, last paragraph). -/
theorem shapeP_parentOf_old {hd : Holder} {ls : List (Option Nat × Option Nat × Nat)} {q : Nat}
    (hq : q < P.length) : parentOf (shapeP P hd ls) q = parentOf P q := by
  simp only [Ern.MemoryModel.Access.parentOf, shapeP_get_old hq]

/-- Parents of the appended places of `shapeP` (§47, §71, §72; §49, last paragraph). -/
theorem shapeP_parentOf_new (P : List Place) (hd : Holder)
    (ls : List (Option Nat × Option Nat × Nat)) (i : Nat) :
    parentOf (shapeP P hd ls) (P.length + i) = (ls[i]?).bind (·.1) := by
  simp only [Ern.MemoryModel.Access.parentOf, shapeP_get_new]
  split
  · rfl
  · rename_i hi; rw [List.getElem?_eq_none_iff.2 (by omega)]; rfl

/-- Appending a well-formed shape keeps the relation, the shape not renamed (§71.1, §72.2:
parents and owning elements are fresh; §49, last paragraph). -/
theorem shapeP_ren (hP : PRel π P P') {ls : List (Option Nat × Option Nat × Nat)}
    (hok : ShapeOK P.length ls) (o : Holder) :
    PRel π (shapeP P o ls) (shapeP P' (o.ren π) ls) where
  len := by simp [shapeP, hP.len]
  get q := by
    by_cases hq : q < P.length
    · rw [shapeP_get_old ((hP.lt_iff q).2 hq), shapeP_get_old hq, hP.get]
    · obtain ⟨i, rfl⟩ : ∃ i, q = P.length + i := ⟨q - P.length, by omega⟩
      rw [hP.fix _ (Nat.le_add_right _ _), ← hP.len, shapeP_get_new, hP.len, shapeP_get_new]
      split
      · rename_i hi
        have hc := hok i (List.mem_range.2 hi)
        simp only [Option.map_some, Place.ren, Option.some.injEq, Place.mk.injEq, and_true]
        constructor
        · have h1 := hc.1
          revert h1
          cases (ls[i]?).bind (·.1) with
          | none => intro; rfl
          | some r => intro h1; simp only [Option.map_some, hP.fix r h1.1]
        · have h2 := hc.2
          revert h2
          unfold shapeOwner
          cases (ls[i]?).bind (·.2.1) with
          | none => intro; rfl
          | some r => intro h2; simp only [Holder.ren, hP.fix r h2.1]
      · rfl
  fix q hq := hP.fix q (Nat.le_trans (by simp [shapeP]) hq)

/-- Appending a well-formed shape keeps parent links downward (§71.1, §72.2; §49, last
paragraph). -/
theorem shapeP_down (hdP : DownP P) {o : Holder} {ls : List (Option Nat × Option Nat × Nat)}
    (hok : ShapeOK P.length ls) : DownP (shapeP P o ls) := by
  intro j p hj
  by_cases hq : j < P.length
  · rw [shapeP_parentOf_old hq] at hj; exact hdP j p hj
  · obtain ⟨i, rfl⟩ : ∃ i, j = P.length + i := ⟨j - P.length, by omega⟩
    rw [shapeP_parentOf_new] at hj
    have hi : i < ls.length := by
      apply Classical.byContradiction; intro hi
      rw [List.getElem?_eq_none_iff.2 (by omega)] at hj; cases hj
    have hc := (hok i (List.mem_range.2 hi)).1
    rw [hj] at hc; exact hc.2.1

/-- Appending places keeps field order (§63.2, §71, §72; §49, last paragraph): appended places are
fixed and follow the former ones. -/
theorem shapeP_sib (hP : PRel π P P') (hs : SibMono π P) {o : Holder}
    {ls : List (Option Nat × Option Nat × Nat)} : SibMono π (shapeP P o ls) := by
  intro x y p hx hy hxy
  by_cases hyP : y < P.length
  · have hxP : x < P.length := by omega
    rw [shapeP_parentOf_old hxP] at hx; rw [shapeP_parentOf_old hyP] at hy
    exact hs x y p hx hy hxy
  · rw [hP.fix y (by omega)]
    by_cases hxP : x < P.length
    · have := (hP.lt_iff x).2 hxP; rw [hP.len] at this; omega
    · rw [hP.fix x (by omega)]; exact hxy

end Ern.MemoryModel.Access.Rename
