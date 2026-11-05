import Ern.MemoryModel.Access.Preserve.Common

/-!
# Access kernel: `alloc` (O14)

Results on `alloc provider owner shape` of `specs/ERN_Memory_Model_Specification_v0.md` §71 and
on the outcomes of §58: the `ok` outcome preserves the main invariant of §57 (`KInv`) together
with its auxiliary `KAux`; it adds exactly one root place and exactly one authority, the root
`Modify` authority of that place, with no origin, held by `owner`, the new leaves `Uninit` (§71,
`ok`); `fail` happens only when the static preconditions hold and `K.Satisfiable` is false, and
produces no new state (§58, §71); `alloc` is deterministic; no other kernel operation O1–O16
yields `fail` (§58). Helper lemmas live in the namespace `Alloc`.
-/

namespace Ern.MemoryModel.Access

namespace Alloc

/-! ## Shape of the new places (§71.1, §71 `ok`) -/

/-- Every element of a local shape is owned by the receiving holder (§71.1: the shape is
represented like the locals of `enterFrame`, which have no owning element). -/
theorem shapeOwner_toShape (ls : LocalShape) (hd : Holder) (i : Nat) :
    shapeOwner ls.toShape hd i = hd := by
  simp only [shapeOwner, LocalShape.toShape, List.getElem?_map]
  cases ls[i]? <;> rfl

/-- A local shape has one element per entry (§71.1). -/
theorem length_toShape (ls : LocalShape) : ls.toShape.length = ls.length := by
  simp [LocalShape.toShape]

/-- The places after `alloc` are the former places followed by the elements of the shape (§71,
`ok`: fresh identities). -/
theorem allocP_len (s : S3) (ow : Nat) (ls : LocalShape) :
    (allocP s ow ls).length = s.P.length + ls.length := by
  simp [allocP, shapeP, LocalShape.toShape]

/-- `alloc` keeps the former places (§71, `ok`). -/
theorem allocP_lt {s : S3} {ow : Nat} {ls : LocalShape} {q : Nat} (h : q < s.P.length) :
    (allocP s ow ls)[q]? = s.P[q]? := List.getElem?_append_left h

/-- The new place of index `|P| + i` has the parent given by the shape and is owned by `owner`
(§71, `ok`: owned by `owner`). -/
theorem allocP_new {s : S3} {ow : Nat} {ls : LocalShape} {i : Nat} (h : i < ls.length) :
    (allocP s ow ls)[s.P.length + i]? =
      some ⟨(ls.toShape[i]?).bind (·.1), .place ow, ((ls.toShape[i]?).map (·.2.2)).getD 0⟩ := by
  have h' : i < ls.toShape.length := by rw [length_toShape]; exact h
  simp only [allocP, shapeP, List.getElem?_append_right (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left, List.getElem?_map, List.getElem?_range h', Option.map_some,
    shapeOwner_toShape]

/-- A place after `alloc` is a former place, or a new element of the shape owned by `owner`
(§71, `ok`). -/
theorem allocP_get {s : S3} {ow : Nat} {ls : LocalShape} {q : Nat} {pl : Place}
    (h : (allocP s ow ls)[q]? = some pl) :
    (q < s.P.length ∧ s.P[q]? = some pl) ∨
    (s.P.length ≤ q ∧ q < s.P.length + ls.length ∧
      pl.parent = (ls.toShape[q - s.P.length]?).bind (·.1) ∧ pl.owner = .place ow) := by
  by_cases hq : q < s.P.length
  · exact .inl ⟨hq, by rwa [allocP_lt hq] at h⟩
  · have hlt := lt_of_getElem? h
    rw [allocP_len] at hlt
    obtain ⟨i, rfl⟩ : ∃ i, q = s.P.length + i := ⟨q - s.P.length, by omega⟩
    rw [allocP_new (by omega)] at h
    cases h
    exact .inr ⟨by omega, hlt, by simp, rfl⟩

/-- `alloc` keeps the parents of the former places (§71, `ok`). -/
theorem parentOf_lt {s : S3} {ow : Nat} {ls : LocalShape} {q : Nat} (h : q < s.P.length) :
    parentOf (allocP s ow ls) q = parentOf s.P q := by
  simp only [parentOf, allocP_lt h]

/-- The parent of a new place is the one given by the shape (§71.1). -/
theorem parentOf_new {s : S3} {ow : Nat} {ls : LocalShape} {i : Nat} (h : i < ls.length) :
    parentOf (allocP s ow ls) (s.P.length + i) = (ls.toShape[i]?).bind (·.1) := by
  simp only [parentOf, allocP_new h, Option.bind_some]

/-- The parent of a new place is an earlier new place (§71.1: well-formed shape). -/
theorem parentOf_ge {s : S3} {ow : Nat} {ls : LocalShape}
    (hsh : ShapeOK s.P.length ls.toShape) {q r : Nat} (hq : s.P.length ≤ q)
    (h : parentOf (allocP s ow ls) q = some r) : s.P.length ≤ r ∧ r < q := by
  have hlt : q < s.P.length + ls.length := by
    simp only [parentOf] at h
    cases h' : (allocP s ow ls)[q]? with
    | none => rw [h'] at h; cases h
    | some _ => have := lt_of_getElem? h'; rwa [allocP_len] at this
  obtain ⟨i, rfl⟩ : ∃ i, q = s.P.length + i := ⟨q - s.P.length, by omega⟩
  rw [parentOf_new (by omega)] at h
  have h1 := (hsh i (List.mem_range.2 (by rw [length_toShape]; omega))).1
  rw [h] at h1
  simp only [OptP] at h1
  obtain ⟨h₁, h₂, -⟩ := h1
  exact ⟨h₁, h₂⟩

/-- The structural ancestors of a new place are new places (§71.1). -/
theorem chain_ge {s : S3} {ow : Nat} {ls : LocalShape} (hsh : ShapeOK s.P.length ls.toShape) :
    ∀ n q, q < n → s.P.length ≤ q → ∀ x ∈ chain (parentOf (allocP s ow ls)) q, s.P.length ≤ x
  | 0, _, h, _, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, q, hq, hge, x, hx => by
    cases hpo : parentOf (allocP s ow ls) q with
    | none => rw [chain_none hpo] at hx; simp at hx
    | some r =>
      obtain ⟨hr, hrq⟩ := parentOf_ge hsh hge hpo
      rw [chain_cons hpo hrq] at hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hr
      · exact chain_ge hsh n r (by omega) hr x hx

/-- `alloc` keeps the structural ancestors of the former places (§71, `ok`). -/
theorem chain_old {s : S3} {ow : Nat} {ls : LocalShape} {l : Nat} (h : l < s.P.length) :
    chain (parentOf (allocP s ow ls)) l = chain (parentOf s.P) l :=
  chain_congr fun _ hj => parentOf_lt (Nat.lt_of_le_of_lt hj h)

/-- `alloc` keeps the structural parts of the former places (§40, §71 `ok`). -/
theorem partOf_old {s : S3} {ow : Nat} {ls : LocalShape} {l r : Nat} (h : l < s.P.length) :
    partOf (allocP s ow ls) l r ↔ partOf s.P l r := by
  simp only [partOf, chain_old h, allocP_len]
  constructor
  · rintro ⟨-, hc⟩; exact ⟨h, hc⟩
  · rintro ⟨-, hc⟩; exact ⟨by omega, hc⟩

/-- A former place is a leaf after `alloc` exactly when it was one before: new places have new
parents (§40, §71.1). -/
theorem isLeaf_old {s : S3} {ow : Nat} {ls : LocalShape} (hsh : ShapeOK s.P.length ls.toShape)
    {l : Nat} (h : l < s.P.length) : isLeaf (allocP s ow ls) l ↔ isLeaf s.P l := by
  constructor
  · intro hl r hr
    rw [← parentOf_lt (ow := ow) (ls := ls) hr]
    exact hl r (by rw [allocP_len]; omega)
  · intro hl r _ hp
    by_cases hrn : r < s.P.length
    · rw [parentOf_lt hrn] at hp; exact hl r hrn hp
    · have := (parentOf_ge hsh (by omega) hp).1; omega

/-- `alloc` keeps the footprints of the former places (§40, §71 `ok`). -/
theorem footprint_old {s : S3} {ow : Nat} {ls : LocalShape} (hsh : ShapeOK s.P.length ls.toShape)
    {q : Nat} (hq : q < s.P.length) (l : Nat) :
    l ∈ footprint (allocP s ow ls) q ↔ l ∈ footprint s.P q := by
  rw [mem_footprint, mem_footprint]
  by_cases hl : l < s.P.length
  · rw [isLeaf_old hsh hl, partOf_old hl]
    exact ⟨fun h => ⟨hl, h.2⟩, fun h => ⟨by rw [allocP_len]; omega, h.2⟩⟩
  · constructor
    · rintro ⟨-, -, -, hc | hc⟩
      · omega
      · have := chain_ge hsh (l + 1) l (Nat.lt_succ_self l) (by omega) q hc; omega
    · rintro ⟨h, -⟩; exact absurd h hl

/-- The leaves of the new place `|P|` are new places (§71, `ok`). -/
theorem fp_new_ge {s : S3} {ow : Nat} {ls : LocalShape} {l : Nat}
    (h : l ∈ footprint (allocP s ow ls) s.P.length) : s.P.length ≤ l := by
  obtain ⟨-, -, -, h | h⟩ := mem_footprint.1 h
  · omega
  · have := chain_lt h; omega

/-! ## The single new root (§71.1, §71 `ok`) -/

section Root
variable {k : K} {s : S3} {pr ow : Nat} {ls : LocalShape}

/-- An accepted shape is nonempty (§71.1). -/
theorem len_pos (hst : AllocStatic k s pr ow ls) : 0 < ls.length := by
  cases ls with
  | nil => exact absurd rfl hst.nonempty
  | cons _ _ => exact Nat.succ_pos _

/-- The first element of an accepted shape has no parent: a parent would be an earlier element
(§71.1). -/
theorem parent0 (hst : AllocStatic k s pr ow ls) : (ls.toShape[0]?).bind (·.1) = none := by
  have h1 := (hst.shapeOK 0 (List.mem_range.2 (by rw [length_toShape]; exact len_pos hst))).1
  cases hp : (ls.toShape[0]?).bind (·.1) with
  | none => rfl
  | some r =>
    rw [hp] at h1
    simp only [OptP] at h1
    obtain ⟨h₁, h₂, -⟩ := h1
    omega

/-- The only root element of an accepted shape is its first element (§71.1, §71 `ok`: a new
storage root). -/
theorem rootIdx_eq (hst : AllocStatic k s pr ow ls) : rootIdx ls.toShape = [0] := by
  have h0 : 0 ∈ rootIdx ls.toShape := by
    simp only [rootIdx, List.mem_filter, List.mem_range, length_toShape]
    exact ⟨len_pos hst, by rw [parent0 hst]; rfl⟩
  have hl := hst.oneRoot
  generalize rootIdx ls.toShape = L at h0 hl ⊢
  match L, h0, hl with
  | [x], h0, _ => rw [List.mem_singleton] at h0; rw [h0]
  | [], h0, _ => exact absurd h0 (List.not_mem_nil)
  | _ :: _ :: _, _, hl => exact absurd hl (by simp only [List.length_cons]; omega)

/-- The new place `|P|`: no parent, owned by `owner` (§71, `ok`). -/
theorem allocP_root (hst : AllocStatic k s pr ow ls) :
    (allocP s ow ls)[s.P.length]? =
      some ⟨none, .place ow, ((ls.toShape[0]?).map (·.2.2)).getD 0⟩ := by
  have := allocP_new (s := s) (ow := ow) (len_pos hst)
  rw [Nat.add_zero, parent0 hst] at this
  exact this

/-- The new place `|P|` is a root place (§40, §71 `ok`). -/
theorem root_new (hst : AllocStatic k s pr ow ls) : RootPlace (allocP s ow ls) s.P.length :=
  ⟨by rw [allocP_len]; have := len_pos hst; omega,
    by simp only [parentOf, allocP_root hst, Option.bind_some]⟩

/-- `|P|` is the only new root place (§71 `ok`: a new storage root). -/
theorem root_unique_new (hst : AllocStatic k s pr ow ls) {r : Nat} (hr : s.P.length ≤ r)
    (h : RootPlace (allocP s ow ls) r) : r = s.P.length := by
  obtain ⟨hlt, hp⟩ := h
  rw [allocP_len] at hlt
  obtain ⟨i, rfl⟩ : ∃ i, r = s.P.length + i := ⟨r - s.P.length, by omega⟩
  rw [parentOf_new (by omega)] at hp
  have : i ∈ rootIdx ls.toShape := by
    simp only [rootIdx, List.mem_filter, List.mem_range, length_toShape]
    exact ⟨by omega, by rw [hp]; rfl⟩
  rw [rootIdx_eq hst, List.mem_singleton] at this
  omega

/-- The authorities after `alloc`: the former ones and one root `Modify` authority with no
origin, on the footprint of the new root, held by `owner` (§71, `ok`). -/
theorem allocEff_A (hst : AllocStatic k s pr ow ls) : (allocEff s ow ls).A =
    s.A ++ [⟨.modify, none, footprint (allocP s ow ls) s.P.length, .place ow, true⟩] := by
  simp only [allocEff, rootIdx_eq hst, List.map_cons, List.map_nil, Nat.add_zero,
    shapeOwner_toShape]

/-- An authority after `alloc` is a former one, or the new root authority at the fresh identity
`|A|` (§42 fresh identities, §71 `ok`). -/
theorem allocA_get (hst : AllocStatic k s pr ow ls) {j : Nat} {z : Authority}
    (h : (allocEff s ow ls).A[j]? = some z) :
    (j < s.A.length ∧ s.A[j]? = some z) ∨
    (j = s.A.length ∧
      z = ⟨.modify, none, footprint (allocP s ow ls) s.P.length, .place ow, true⟩) :=
  addAuth_get (s := s) (by show (s.A ++ [_])[j]? = some z; rw [← allocEff_A hst]; exact h)

/-- The new root authority has no origin, so `alloc` keeps every origin link (§42, §71 `ok`). -/
theorem org_eq (hst : AllocStatic k s pr ow ls) : (allocEff s ow ls).org = s.org := by
  funext i
  simp only [S3.org, allocEff_A hst]
  by_cases hi : i < s.A.length
  · rw [List.getElem?_append_left hi]
  · rw [List.getElem?_append_right (by omega), List.getElem?_eq_none (by omega : s.A.length ≤ i)]
    cases i - s.A.length <;> simp

/-- `alloc` keeps every origin chain (§42, §71 `ok`). -/
theorem ancs_eq (hst : AllocStatic k s pr ow ls) : (allocEff s ow ls).ancs = s.ancs := by
  funext x; simp only [S3.ancs, org_eq hst]

end Root

/-- `alloc` keeps the former authorities (§71, `ok`). -/
theorem A_lt {s : S3} {ow : Nat} {ls : LocalShape} {j : Nat} (h : j < s.A.length) :
    (allocEff s ow ls).A[j]? = s.A[j]? := List.getElem?_append_left h

/-! ## Usability and frames (§40, §44) -/

section Usable
variable {s : S3} {ow : Nat} {ls : LocalShape}

/-- A place usable before `alloc` stays usable (§40, §71 `ok`). -/
theorem usable_old {q : Nat} (h : s.Usable q) : (allocEff s ow ls).Usable q := by
  induction h with
  | @frame q f pl hpl hd ho hf =>
    exact .frame (show (allocP s ow ls)[q]? = _ by rw [allocP_lt (lt_of_getElem? hpl)]; exact hpl)
      (by simp [allocEff, hd, show ¬ s.P.length ≤ q from Nat.not_le.2 (lt_of_getElem? hpl)]) ho hf
  | @place q o pl hpl hd ho _ ih =>
    exact .place (show (allocP s ow ls)[q]? = _ by rw [allocP_lt (lt_of_getElem? hpl)]; exact hpl)
      (by simp [allocEff, hd, show ¬ s.P.length ≤ q from Nat.not_le.2 (lt_of_getElem? hpl)]) ho ih

/-- A former place usable after `alloc` was usable before (§40, §49.3, §71 `ok`). -/
theorem usable_back (hw : WF3 s) {q : Nat} (h : (allocEff s ow ls).Usable q)
    (hq : q < s.P.length) : s.Usable q := by
  induction h with
  | @frame q f pl hpl hd ho hf =>
    have hpl' : s.P[q]? = some pl := by
      have : (allocP s ow ls)[q]? = some pl := hpl; rwa [allocP_lt hq] at this
    exact .frame hpl' (by simpa [allocEff, show ¬ s.P.length ≤ q by omega] using hd) ho hf
  | @place q o pl hpl hd ho _ ih =>
    have hpl' : s.P[q]? = some pl := by
      have : (allocP s ow ls)[q]? = some pl := hpl; rwa [allocP_lt hq] at this
    exact .place hpl' (by simpa [allocEff, show ¬ s.P.length ≤ q by omega] using hd) ho
      (ih (hw.owners.2.1 q pl o hpl' ho))

/-- Every new place is usable when `owner` is (§40, §71.3, §71 `ok`). -/
theorem usable_new (hu : s.Usable ow) {q : Nat} (hq : s.P.length ≤ q)
    (hq' : q < s.P.length + ls.length) : (allocEff s ow ls).Usable q := by
  obtain ⟨i, rfl⟩ : ∃ i, q = s.P.length + i := ⟨q - s.P.length, by omega⟩
  exact .place (show (allocP s ow ls)[_]? = _ from allocP_new (by omega)) (by simp [allocEff]) rfl
    (usable_old hu)

/-- `alloc` keeps the frame of the former places (§40, `placeFrame`; §49.3). -/
theorem frameOf_old (hw : WF3 s) {q f : Nat} (hq : q < s.P.length) :
    FrameOf (allocEff s ow ls) q f ↔ FrameOf s q f := by
  constructor
  · intro h
    induction h with
    | @frame q f pl hpl ho =>
      exact .frame (by have : (allocP s ow ls)[q]? = some pl := hpl; rwa [allocP_lt hq] at this) ho
    | @place q o f pl hpl ho _ ih =>
      have hpl' : s.P[q]? = some pl := by
        have : (allocP s ow ls)[q]? = some pl := hpl; rwa [allocP_lt hq] at this
      exact .place hpl' ho (ih (hw.owners.2.1 q pl o hpl' ho))
  · intro h
    clear hq
    induction h with
    | frame hpl ho =>
      exact .frame (show (allocP s ow ls)[_]? = _ by rw [allocP_lt (lt_of_getElem? hpl)]; exact hpl)
        ho
    | place hpl ho _ ih =>
      exact .place (show (allocP s ow ls)[_]? = _ by rw [allocP_lt (lt_of_getElem? hpl)]; exact hpl)
        ho ih

/-- `alloc` keeps `placeFrame` of the former places (§40, §44). -/
theorem pframe_old (hw : WF3 s) {q : Nat} (hq : q < s.P.length) :
    (allocEff s ow ls).pframe q = s.pframe q :=
  Option.ext fun f => by rw [pframe_iff, pframe_iff, frameOf_old hw hq]

end Usable

/-! ## Effective anchors (§44) -/

/-- A frame of the stack is its own ancestor (§39, `ancestor`). -/
theorem ancestor_self {f : Nat} : ∀ {F : Frames}, f ∈ F → ancestor F f f
  | g :: F, h => by
    unfold ancestor
    simp only [List.dropWhile_cons]
    by_cases e : g = f
    · subst e; simp
    · have hgf : (g != f) = true := by simp [e]
      simp only [hgf, ↓reduceIte]
      exact ancestor_self (List.mem_cons.1 h |>.resolve_left (fun h' => e h'.symm))

section Anchor
variable {k : K} {s : S3} {pr ow : Nat} {ls : LocalShape}

/-- The anchor-order condition of an existing authority carries over `alloc` (§44, §71 `ok`):
effective anchors, their holders and the frames of the former places are unchanged. -/
theorem effAnchorOK_old (hst : AllocStatic k s pr ow ls) (hw : WF3 s) {x : Nat}
    {fd : Option Nat} (h : EffAnchorOK s x fd) : EffAnchorOK (allocEff s ow ls) x fd := by
  have he : (allocEff s ow ls).effAnchor x = s.effAnchor x := by
    simp only [S3.effAnchor, ancs_eq hst]
  unfold EffAnchorOK at h ⊢
  rw [he]
  cases hz : s.A[s.effAnchor x]? with
  | none => rw [hz] at h; exact h.elim
  | some z =>
    rw [hz] at h
    rw [A_lt (lt_of_getElem? hz), hz]
    have hh : (allocEff s ow ls).hframe z.holder = s.hframe z.holder := by
      cases hzh : z.holder with
      | frame f => rfl
      | place p =>
        show (allocEff s ow ls).pframe p = s.pframe p
        cases hg : s.pframe p with
        | none => simp only [OptP, hzh, S3.hframe, hg] at h
        | some g => rw [← hg]; exact pframe_old hw (pframe_iff.1 hg).lt
    simp only [OptP] at h ⊢
    rw [hh]
    exact h

/-- The new root authority satisfies the anchor-order condition for its holder `owner` (§44,
§71 `ok`): it is its own effective anchor, held by `owner`, whose frame is on the stack. -/
theorem effAnchorOK_new (hst : AllocStatic k s pr ow ls) :
    EffAnchorOK (allocEff s ow ls) s.A.length ((allocEff s ow ls).pframe ow) := by
  have hA : (allocEff s ow ls).A[s.A.length]? =
      some ⟨.modify, none, footprint (allocP s ow ls) s.P.length, .place ow, true⟩ := by
    rw [allocEff_A hst]; simp
  have he : (allocEff s ow ls).effAnchor s.A.length = s.A.length := by
    simp only [S3.effAnchor, S3.ancs,
      chain_none (show (allocEff s ow ls).org s.A.length = none by simp [S3.org, hA]),
      List.getLastD_nil]
  obtain ⟨f, hf, hfF⟩ := (usable_old (ls := ls) hst.ownerUsable).frameOf
  have hpf := pframe_iff.2 hf
  unfold EffAnchorOK
  rw [he, hA, hpf]
  simp only [OptP, S3.hframe, hpf]
  exact ancestor_self hfF

end Anchor

/-! ## Preservation of the invariants (§49–§54, §57) -/

section Preserve
variable {k : K} {s : S3} {pr ow : Nat} {ls : LocalShape}

/-- `alloc` preserves `RootChain` (§49.6, §71 `ok`): former authorities keep their chains and the
footprints of former places are unchanged; the new root authority is the root authority of the
new root place. -/
theorem rootChain (hst : AllocStatic k s pr ow ls) (hw : WF3 s) :
    RootChain (allocEff s ow ls) := by
  intro a y l ha hl hleaf
  rcases allocA_get hst ha with ⟨ha', hy⟩ | ⟨rfl, rfl⟩
  · obtain ⟨hlt, -⟩ := hw.footprints a y hy l hl
    obtain ⟨x0, z, r, hx0, hz, hzo, ⟨hrl, hrp⟩, hlr, hfz⟩ :=
      hw.rootChain a y l hy hl ((isLeaf_old hst.shapeOK hlt).1 hleaf)
    have hx0lt : x0 < s.A.length := by
      rcases hx0 with rfl | hx0
      · exact ha'
      · exact Nat.lt_trans (chain_lt hx0) ha'
    refine ⟨x0, z, r, by rw [ancs_eq hst]; exact hx0, by rw [A_lt hx0lt]; exact hz, hzo,
      ⟨by show r < (allocP s ow ls).length; rw [allocP_len]; omega,
       by show parentOf (allocP s ow ls) r = none; rw [parentOf_lt hrl]; exact hrp⟩,
      (partOf_old hlt).2 hlr, fun l' => ?_⟩
    show _ ↔ l' ∈ footprint (allocP s ow ls) r
    rw [footprint_old hst.shapeOK hrl]; exact hfz l'
  · exact ⟨s.A.length, _, s.P.length, .inl rfl, ha, rfl, root_new hst, (mem_footprint.1 hl).2.2,
      fun _ => Iff.rfl⟩

/-- `alloc` preserves `RootHeld` (§49.7, §71 `ok`): former usable root places keep their root
authority; the new root place has the new root authority, held by its owner `owner`. -/
theorem rootHeld (hst : AllocStatic k s pr ow ls) (hw : WF3 s) :
    RootHeld (allocEff s ow ls) := by
  intro r hr hu
  by_cases hrl : r < s.P.length
  · have hr0 : RootPlace s.P r :=
      ⟨hrl, by rw [← parentOf_lt (ow := ow) (ls := ls) hrl]; exact hr.2⟩
    obtain ⟨i, z, pr', hz, za, zo, zm, hpr, hh, hf⟩ := hw.rootHeld r hr0 (usable_back hw hu hrl)
    exact ⟨i, z, pr', by rw [A_lt (lt_of_getElem? hz)]; exact hz, za, zo, zm,
      by show (allocP s ow ls)[r]? = _; rw [allocP_lt hrl]; exact hpr, hh,
      fun l => by
        show _ ↔ l ∈ footprint (allocP s ow ls) r
        rw [footprint_old hst.shapeOK hrl]; exact hf l⟩
  · obtain rfl := root_unique_new hst (by omega) hr
    exact ⟨s.A.length, ⟨.modify, none, footprint (allocP s ow ls) s.P.length, .place ow, true⟩, _,
      by rw [allocEff_A hst]; simp, rfl, rfl, rfl, allocP_root hst, rfl, fun _ => Iff.rfl⟩

/-- `alloc` preserves `WF3` (§49, §71.3 "new identities and ownership relations must respect
`WF3`, `RootHeld`"). -/
theorem wf3 (hst : AllocStatic k s pr ow ls) (hw : WF3 s) : WF3 (allocEff s ow ls) where
  frames := hw.frames
  places q pl r hq hp := by
    rcases allocP_get hq with ⟨hql, hq'⟩ | ⟨hqn, -, -, how⟩
    · obtain ⟨pr', hpr, hlt, ho, hd⟩ := hw.places q pl r hq' hp
      refine ⟨pr', by show (allocP s ow ls)[r]? = _; rw [allocP_lt (by omega)]; exact hpr, hlt,
        ho, ?_⟩
      simp [allocEff, show ¬ s.P.length ≤ r by omega, show ¬ s.P.length ≤ q by omega, hd]
    · have hpo : parentOf (allocP s ow ls) q = some r := by
        simp only [parentOf]; rw [show (allocP s ow ls)[q]? = some pl from hq]; exact hp
      obtain ⟨hr, hrq⟩ := parentOf_ge hst.shapeOK hqn hpo
      have hrl : q < s.P.length + ls.length := by
        have := lt_of_getElem? hq; rwa [show (allocEff s ow ls).P = allocP s ow ls from rfl,
          allocP_len] at this
      obtain ⟨i, rfl⟩ : ∃ i, r = s.P.length + i := ⟨r - s.P.length, by omega⟩
      exact ⟨_, allocP_new (by omega), hrq, by rw [how],
        by simp [allocEff, hqn]⟩
  owners := ⟨fun q pl f hq ho => (by
      rcases allocP_get hq with ⟨-, hq'⟩ | ⟨-, -, -, how⟩
      · exact hw.owners.1 q pl f hq' ho
      · rw [how] at ho; cases ho),
    fun q pl o hq ho => (by
      show o < (allocP s ow ls).length
      rw [allocP_len]
      rcases allocP_get hq with ⟨-, hq'⟩ | ⟨-, -, -, how⟩
      · have := hw.owners.2.1 q pl o hq' ho; omega
      · rw [how] at ho; cases ho; have := hst.ownerUsable.lt; omega),
    fun _ hq => S3.Usable.frameOf hq⟩
  footprints a x hx l hl := by
    rcases allocA_get hst hx with ⟨-, hx'⟩ | ⟨-, rfl⟩
    · obtain ⟨hlt, hleaf⟩ := hw.footprints a x hx' l hl
      exact ⟨by show l < (allocP s ow ls).length; rw [allocP_len]; omega,
        (isLeaf_old hst.shapeOK hlt).2 hleaf⟩
    · obtain ⟨h1, h2, -⟩ := mem_footprint.1 hl
      exact ⟨h1, h2⟩
  origins b y a hb ho := by
    rcases allocA_get hst hb with ⟨-, hb'⟩ | ⟨-, rfl⟩
    · exact hw.origins b y a hb' ho
    · cases ho
  rootChain := rootChain hst hw
  rootHeld := rootHeld hst hw
  holders a y hy ya := by
    rcases allocA_get hst hy with ⟨-, hy'⟩ | ⟨-, rfl⟩
    · have := hw.holders a y hy' ya
      cases hh : y.holder with
      | frame f => rw [hh] at this; exact this
      | place p => rw [hh] at this; exact usable_old this
    · exact usable_old hst.ownerUsable

/-- `alloc` preserves `I1` (§50, §71 `ok`): the new root authority covers only new leaves. -/
theorem i1 (hst : AllocStatic k s pr ow ls) (hw : WF3 s) (h1 : I1 s) :
    I1 (allocEff s ow ls) := by
  intro a b x y p hab ha hb xa ya xp yp hnab hnba
  rcases allocA_get hst ha with ⟨-, hx⟩ | ⟨rfl, rfl⟩ <;>
    rcases allocA_get hst hb with ⟨-, hy⟩ | ⟨rfl, rfl⟩
  · rw [ancs_eq hst] at hnab hnba
    exact h1 a b x y p hab hx hy xa ya xp yp hnab hnba
  · have := (hw.footprints a x hx p xp).1
    have := fp_new_ge (s := s) (ow := ow) (ls := ls) yp; omega
  · have := (hw.footprints b y hy p yp).1
    have := fp_new_ge (s := s) (ow := ow) (ls := ls) xp; omega
  · exact absurd rfl hab

/-- `alloc` preserves `I2` (§51, §71 `ok`): the new authority has no origin. -/
theorem i2 (hst : AllocStatic k s pr ow ls) (h2 : I2 s) : I2 (allocEff s ow ls) := by
  intro b y a hb ho
  rcases allocA_get hst hb with ⟨-, hb'⟩ | ⟨-, rfl⟩
  · obtain ⟨x₁, hx₁, hh⟩ := h2 b y a hb' ho
    exact ⟨x₁, by rw [A_lt (lt_of_getElem? hx₁)]; exact hx₁, hh⟩
  · cases ho

/-- `alloc` preserves `I3` (§52, §71 `ok`): the new places have no anchor. -/
theorem i3 (hw : WF3 s) (h3 : I3 s) : I3 (allocEff s ow ls) := by
  intro q hq x hx
  by_cases hql : q < s.P.length
  · have hx' : x ∈ s.D q := by simpa [allocEff, show ¬ s.P.length ≤ q by omega] using hx
    obtain ⟨y, hy, ya⟩ := h3 q (usable_back hw hq hql) x hx'
    exact ⟨y, by rw [A_lt (lt_of_getElem? hy)]; exact hy, ya⟩
  · simp [allocEff, show s.P.length ≤ q by omega] at hx

/-- `alloc` preserves `AnchorOrder` (§44, §54, §71 `ok`): the new places have no anchor and the
frames of the former places do not change. -/
theorem anchorOrder (hst : AllocStatic k s pr ow ls) (hw : WF3 s) (hao : AnchorOrder s) :
    AnchorOrder (allocEff s ow ls) := by
  intro q hq x hx
  by_cases hql : q < s.P.length
  · have hx' : x ∈ s.D q := by simpa [allocEff, show ¬ s.P.length ≤ q by omega] using hx
    rw [pframe_old hw hql]
    exact effAnchorOK_old hst hw (hao q (usable_back hw hq hql) x hx')
  · simp [allocEff, show s.P.length ≤ q by omega] at hx

/-- `alloc` preserves `NoDangling` (§54, §71 `ok`): former places keep their footprints and
usability; the new root authority covers only new places, which are usable. -/
theorem noDangling (hst : AllocStatic k s pr ow ls) (hw : WF3 s) (hnd : NoDangling s) :
    NoDangling (allocEff s ow ls) := by
  intro j z hz za q hq l hl hlz
  obtain ⟨hlP, -, hlq⟩ := mem_footprint.1 hl
  have hql : q ≤ l := by
    rcases hlq.2 with rfl | hc
    · exact Nat.le_refl _
    · exact Nat.le_of_lt (chain_lt hc)
  rcases allocA_get hst hz with ⟨-, hy⟩ | ⟨-, rfl⟩
  · have hlo := (hw.footprints j z hy l hlz).1
    have hqo : q < s.P.length := by omega
    exact hnd j z hy za q (fun hu => hq (usable_old hu)) l
      ((footprint_old hst.shapeOK hqo l).1 hl) hlz
  · have hge := fp_new_ge (s := s) (ow := ow) (ls := ls) hlz
    by_cases hqo : q < s.P.length
    · have := (mem_footprint.1 ((footprint_old hst.shapeOK hqo l).1 hl)).1; omega
    · have hlP' : l < (allocP s ow ls).length := hlP
      rw [allocP_len] at hlP'
      exact hq (usable_new hst.ownerUsable (by omega) (by omega))

/-- `alloc` preserves `AnchorOrderHeld` (§44, §54, §71 `ok`): former held authorities keep their
condition; the new root authority is its own effective anchor, held by `owner`. -/
theorem anchorOrderHeld (hst : AllocStatic k s pr ow ls) (hw : WF3 s) (h : AnchorOrderHeld s) :
    AnchorOrderHeld (allocEff s ow ls) := by
  intro q hq x y hx ya hh
  rcases allocA_get hst hx with ⟨-, hx'⟩ | ⟨rfl, rfl⟩
  · have hq0 : s.Usable q := by have := hw.holders x y hx' ya; rw [hh] at this; exact this
    rw [pframe_old hw hq0.lt]
    exact effAnchorOK_old hst hw (h q hq0 x y hx' ya hh)
  · cases hh
    exact effAnchorOK_new hst

/-- `alloc` preserves the auxiliary `RootHeldConv` (§40, §49.7, §71 `ok`): the new root authority
covers only leaves of the new root place, whose owner `owner` holds it. -/
theorem rootHeldConv (hst : AllocStatic k s pr ow ls) (hw : WF3 s) (hc : RootHeldConv s) :
    RootHeldConv (allocEff s ow ls) := by
  intro x z l r hx ho hl hr hlr
  rcases allocA_get hst hx with ⟨-, hx'⟩ | ⟨rfl, rfl⟩
  · have hlt := (hw.footprints x z hx' l hl).1
    have hlr' := (partOf_old hlt).1 hlr
    have hrl : r < s.P.length := by
      rcases hlr'.2 with rfl | hc'
      · exact hlt
      · exact Nat.lt_trans (chain_lt hc') hlt
    have hr' : RootPlace s.P r :=
      ⟨hrl, by rw [← parentOf_lt (ow := ow) (ls := ls) hrl]; exact hr.2⟩
    obtain ⟨pr', hpr, hh⟩ := hc x z l r hx' ho hl hr' hlr'
    exact ⟨pr', by show (allocP s ow ls)[r]? = _; rw [allocP_lt hrl]; exact hpr, hh⟩
  · obtain rfl := rootOf_unique hr (root_new hst) hlr (mem_footprint.1 hl).2.2
    exact ⟨_, allocP_root hst, rfl⟩

end Preserve

/-- No `Guarded` transition yields `fail` (§58). -/
theorem guarded_ne_fail {σ : Type} {Pre : Prop} {eff : σ} : ¬ Guarded Pre eff .fail :=
  fun h => by cases h

end Alloc

/-! ## Main results (§57, §58, §71) -/

/-- `alloc` preserves the main invariant (§57, §58: an `ok` transition preserves the invariants;
§71.3: the new identities and ownership relations respect `WF3` and `RootHeld`): from a state
satisfying `KInv` and `KAux`, the `ok` outcome of `alloc` satisfies both. -/
theorem alloc_preserves {k : K} {pr ow : Nat} {ls : LocalShape} {s s' : S3}
    (hk : KInv s) (ha : KAux s) (h : AllocStep k pr ow ls s (.ok s')) : KInv s' ∧ KAux s' := by
  cases h with
  | ok hst _ =>
    obtain ⟨hw, ⟨⟨h1, h2, h3, -⟩, hao, hnd⟩, haoh, -⟩ := hk
    exact ⟨kInv_of (Alloc.wf3 hst hw)
        ⟨⟨Alloc.i1 hst hw h1, Alloc.i2 hst h2, Alloc.i3 hw h3, i4_always _⟩,
          Alloc.anchorOrder hst hw hao, Alloc.noDangling hst hw hnd⟩
        (Alloc.anchorOrderHeld hst hw haoh),
      Alloc.rootHeldConv hst hw ha⟩

/-- The `ok` effect of `alloc` (§71, `ok`): the former places are kept and the nonempty shape is
appended with fresh identities, every new place owned by `owner`; among the new places exactly
one, `|P|`, is a root place (a new storage root); exactly one authority is added, at the fresh
identity `|A|`: the root `Modify` authority of `|P|`, with no origin, held by `owner`, covering
the footprint of `|P|`; the leaves of `|P|` are `Uninit`. -/
theorem alloc_one_root {k : K} {pr ow : Nat} {ls : LocalShape} {s s' : S3}
    (h : AllocStep k pr ow ls s (.ok s')) :
    s'.P.length = s.P.length + ls.length ∧ 0 < ls.length ∧
    (∀ q < s.P.length, s'.P[q]? = s.P[q]?) ∧
    (∀ (q : Nat) (pl : Place), s.P.length ≤ q → s'.P[q]? = some pl → pl.owner = .place ow) ∧
    RootPlace s'.P s.P.length ∧
    (∀ r, s.P.length ≤ r → RootPlace s'.P r → r = s.P.length) ∧
    s'.A = s.A ++ [⟨.modify, none, footprint s'.P s.P.length, .place ow, true⟩] ∧
    ∀ l ∈ footprint s'.P s.P.length, s'.I l = .uninit := by
  cases h with
  | ok hst _ =>
    refine ⟨Alloc.allocP_len s ow ls, Alloc.len_pos hst, fun q hq => Alloc.allocP_lt hq,
      fun q pl hq hpl => ?_, Alloc.root_new hst,
      fun r hr hrp => Alloc.root_unique_new hst hr hrp, Alloc.allocEff_A hst, fun l hl => ?_⟩
    · rcases Alloc.allocP_get hpl with ⟨hq', -⟩ | ⟨-, -, -, how⟩
      · omega
      · exact how
    · have := Alloc.fp_new_ge (s := s) (ow := ow) (ls := ls) hl
      simp [allocEff, this]

/-- `alloc` is deterministic (§58, §71): its outcome is a function of the state and the
arguments. -/
theorem alloc_det {k : K} {pr ow : Nat} {ls : LocalShape} {s : S3} {o₁ o₂ : Outcome3 S3}
    (h₁ : AllocStep k pr ow ls s o₁) (h₂ : AllocStep k pr ow ls s o₂) : o₁ = o₂ := by
  cases h₁ <;> cases h₂ <;> first | rfl | contradiction

/-- A failed `alloc` leaves the state unchanged (§58: `fail` is a defined failure leaving the
state unchanged; §71: `fail` when the static preconditions hold but `K.Satisfiable` is false, no
state change). The `fail` outcome carries no state, so the state stays `s`; moreover the failure
happens only when the static preconditions hold and `K.Satisfiable(provider, shape, s)` is false,
and then no `ok` successor state exists. -/
theorem alloc_fail_unchanged {k : K} {pr ow : Nat} {ls : LocalShape} {s : S3}
    (h : AllocStep k pr ow ls s .fail) :
    AllocStatic k s pr ow ls ∧ ¬ k.Satisfiable pr ls s ∧
      ∀ s', ¬ AllocStep k pr ow ls s (.ok s') := by
  cases h with
  | fail h1 h2 => exact ⟨h1, h2, fun _ h' => by cases alloc_det (.fail h1 h2) h'⟩

/-- Only `alloc` may produce `fail` in the O1–O16 kernel (§58: "Other kernel operations produce
`ok` or `reject`"): none of the other fifteen operation relations of `KStep` yields `fail`. -/
theorem fail_only_alloc (k : K) (s : S3) :
    (∀ src region m, ¬ DeriveStep src region m s .fail) ∧
    (∀ src rs, ¬ SplitStep k src rs s .fail) ∧
    (∀ a, ¬ ReleaseStep a s .fail) ∧
    (∀ src dst, ¬ TransferStep k src dst s .fail) ∧
    (∀ q x, ¬ DependStep q x s .fail) ∧
    (∀ ps ls, ¬ EnterStep ps ls s .fail) ∧
    ¬ ExitStep k s .fail ∧
    (∀ a ls, ¬ Read3Step a ls s .fail) ∧
    (∀ a ls, ¬ Write3Step a ls s .fail) ∧
    (∀ a ls, ¬ WriteSharedStep k a ls s .fail) ∧
    (∀ p, ¬ PinStep p s .fail) ∧
    (∀ p, ¬ UnpinStep k p s .fail) ∧
    (∀ p, ¬ EndUseStep k p s .fail) ∧
    (∀ p auth, ¬ FreeStep k p auth s .fail) ∧
    (∀ a p, ¬ StoreStep a p s .fail) :=
  ⟨fun _ _ _ => Alloc.guarded_ne_fail, fun _ _ => Alloc.guarded_ne_fail,
    fun _ => Alloc.guarded_ne_fail, fun _ _ => Alloc.guarded_ne_fail,
    fun _ _ => Alloc.guarded_ne_fail, fun _ _ => Alloc.guarded_ne_fail, Alloc.guarded_ne_fail,
    fun _ _ => Alloc.guarded_ne_fail, fun _ _ => Alloc.guarded_ne_fail,
    fun _ _ => Alloc.guarded_ne_fail, fun _ => Alloc.guarded_ne_fail,
    fun _ => Alloc.guarded_ne_fail, fun _ => Alloc.guarded_ne_fail,
    fun _ _ => Alloc.guarded_ne_fail, fun _ _ => Alloc.guarded_ne_fail⟩

end Ern.MemoryModel.Access
