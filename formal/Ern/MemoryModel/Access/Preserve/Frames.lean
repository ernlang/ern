import Ern.MemoryModel.Access.Preserve.Common

/-!
# Access kernel: preservation by `enterFrame` and `exitFrame`

Operations O6 `enterFrame` (§72) and O7 `exitFrame` (§73) of
`specs/ERN_Memory_Model_Specification_v0.md`, with the frame rules of §39 and the parameter and
reanchoring rules of §45. Both steps preserve the kernel invariant of §57 (`KInv`) and, separately,
the auxiliary invariant `KAux`. The file also proves entry protection of parameters (§72.3 and
the last paragraph of §72), the release of authorities whose holder dies at the exit (§73
effect, §39), the absence of dangling authorities after the exit (§73, §54), reanchoring to the
first surviving active origin (§73.4, §73 effect), and determinism of both steps (§58).

Helper lemmas live in the namespace `Ern.MemoryModel.Access.Frames`.
-/

namespace Ern.MemoryModel.Access

namespace Frames

/-! ## Lists -/

/-- Indices of `List.range` are strictly increasing (§72: identities of the root locals). -/
theorem range_pairwise_lt : ∀ n, (List.range n).Pairwise (· < ·)
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.pairwise_append]
    refine ⟨range_pairwise_lt n, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
    rw [List.mem_singleton] at hb; subst hb; exact List.mem_range.1 ha

/-- In a strictly increasing list, a value sits at one index only (§72: identities of the root
locals). -/
theorem getElem?_inj_of_lt : ∀ {l : List Nat} {i j x : Nat}, l.Pairwise (· < ·) →
    l[i]? = some x → l[j]? = some x → i = j
  | [], _, _, _, _, h, _ => by simp at h
  | _ :: _, 0, 0, _, _, _, _ => rfl
  | _ :: l, 0, j + 1, x, hp, hi, hj => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hi; subst hi
    have := (List.pairwise_cons.1 hp).1 _ (List.mem_of_getElem? hj)
    exact absurd this (Nat.lt_irrefl _)
  | _ :: l, i + 1, 0, x, hp, hi, hj => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hj; subst hj
    have := (List.pairwise_cons.1 hp).1 _ (List.mem_of_getElem? hi)
    exact absurd this (Nat.lt_irrefl _)
  | _ :: l, i + 1, j + 1, x, hp, hi, hj => by
    simp only [List.getElem?_cons_succ] at hi hj
    rw [getElem?_inj_of_lt (List.pairwise_cons.1 hp).2 hi hj]

/-- A member of a list sits at some index (§72: the root locals). -/
theorem exists_getElem?_of_mem {α : Type} {a : α} : ∀ {l : List α}, a ∈ l →
    ∃ k : Nat, l[k]? = some a
  | b :: l, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨0, rfl⟩
    · obtain ⟨k, hk⟩ := exists_getElem?_of_mem h; exact ⟨k + 1, by simpa using hk⟩

/-- An element of the mapped suffix of an appended list has an index (§72: the root authorities
of the locals). -/
theorem append_map_get {α β : Type} (A₀ : List β) (g : α → β) {l : List α} {a : α} (h : a ∈ l) :
    ∃ j, (A₀ ++ l.map g)[A₀.length + j]? = some (g a) := by
  obtain ⟨j, hj⟩ := exists_getElem?_of_mem h
  exact ⟨j, by rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    List.getElem?_map, hj]; rfl⟩

/-! ## Shapes of locals (§72.2) -/

/-- A local shape has as many elements as its shape (§72). -/
theorem toShape_length (ls : LocalShape) : ls.toShape.length = ls.length := by
  simp [LocalShape.toShape]

/-- No local has an owning element (§72, §39: locals are owned by the new frame). -/
theorem toShape_owner (ls : LocalShape) (i : Nat) : (ls.toShape[i]?).bind (·.2.1) = none := by
  simp only [LocalShape.toShape, List.getElem?_map]; cases ls[i]? <;> rfl

/-- Every local is owned by the receiving holder (§72 `ok` effect, §39). -/
theorem shapeOwner_toShape (ls : LocalShape) (hd : Holder) (i : Nat) :
    shapeOwner ls.toShape hd i = hd := by
  simp only [shapeOwner, toShape_owner]

/-- Root locals are elements of the shape without parent (§40, §72). -/
theorem rootIdx_mem {ls : LocalShape} {k i : Nat} (h : (rootIdx ls.toShape)[k]? = some i) :
    i < ls.length ∧ (ls.toShape[i]?).bind (·.1) = none := by
  have := List.mem_of_getElem? h
  simp only [rootIdx, List.mem_filter, List.mem_range, Option.isNone_iff_eq_none] at this
  rw [toShape_length] at this; exact this

/-- An element without parent is a root local (§40, §72). -/
theorem mem_rootIdx {ls : LocalShape} {k : Nat} (hk : k < ls.length)
    (hn : (ls.toShape[k]?).bind (·.1) = none) : k ∈ rootIdx ls.toShape := by
  simp only [rootIdx, List.mem_filter, List.mem_range, toShape_length, hk, hn,
    Option.isNone_none, and_self]

/-- Root locals have distinct positions (§72: one root authority per root local). -/
theorem rootIdx_inj {ls : LocalShape} {k k' i : Nat} (h : (rootIdx ls.toShape)[k]? = some i)
    (h' : (rootIdx ls.toShape)[k']? = some i) : k = k' :=
  getElem?_inj_of_lt ((range_pairwise_lt _).filter _) h h'

/-- The parent of a local is an earlier local (§72.2, `ShapeOK`). -/
theorem shape_parent {n : Nat} {ls : LocalShape} (hsh : ShapeOK n ls.toShape) {i r : Nat}
    (hi : i < ls.length) (hr : (ls.toShape[i]?).bind (·.1) = some r) : n ≤ r ∧ r < n + i := by
  have := (hsh i (List.mem_range.2 (by rw [toShape_length]; exact hi))).1
  rw [hr] at this; exact ⟨this.1, this.2.1⟩

/-! ## Origin chains and effective anchors (§42, §44) -/

/-- Under the origin order of `WF3` (§49.5), the origin of an authority precedes it. -/
theorem org_lt {s : S3} (hw : WF3 s) {x o : Nat} (h : s.org x = some o) : o < x := by
  simp only [S3.org] at h
  cases hy : s.A[x]? with
  | none => rw [hy] at h; cases h
  | some y => rw [hy] at h; exact hw.origins x y o hy h

/-- One step of an origin chain (§42): the chain starts with the origin when it is smaller, or
it is empty. -/
theorem ancs_step {s : S3} {x o : Nat} (h : s.org x = some o) :
    (o < x ∧ s.ancs x = o :: s.ancs o) ∨ s.ancs x = [] := by
  by_cases hlt : o < x
  · exact .inl ⟨hlt, chain_cons h hlt⟩
  · right; unfold S3.ancs chain
    cases x with
    | zero => rfl
    | succ k => simp [chainF, h, hlt]

/-- Under the origin order of `WF3` (§49.5), the origin chain of `x` reaches a root authority:
some element of `x` and its ancestors has no origin. -/
theorem reaches_root {s : S3} (hw : WF3 s) :
    ∀ n x, x < n → ∃ r, (r = x ∨ r ∈ s.ancs x) ∧ s.org r = none
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, x, hx => by
    cases ho : s.org x with
    | none => exact ⟨x, .inl rfl, ho⟩
    | some o =>
      have hlt := org_lt hw ho
      obtain ⟨r, hr, hro⟩ := reaches_root hw n o (by omega)
      refine ⟨r, .inr ?_, hro⟩
      rw [S3.ancs, chain_cons ho hlt]
      rcases hr with rfl | hr
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ hr

/-- On an origin chain, an element without origin comes after every other element (§42). -/
theorem ancs_root_after {s : S3} : ∀ n a, a < n → ∀ y w, y ∈ s.ancs a → w ∈ s.ancs a →
    s.org w = none → w = y ∨ w ∈ s.ancs y
  | 0, _, h, _, _, _, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, a, ha, y, w, hy, hw, hwo => by
    cases ho : s.org a with
    | none => rw [S3.ancs, chain_none ho] at hy; simp at hy
    | some o =>
      rcases ancs_step ho with ⟨hlt, he⟩ | he
      · rw [he] at hy hw
        rcases List.mem_cons.1 hy with rfl | hy
        · rcases List.mem_cons.1 hw with rfl | hw
          · exact .inl rfl
          · exact .inr hw
        · rcases List.mem_cons.1 hw with rfl | hw
          · rw [S3.ancs, chain_none hwo] at hy; simp at hy
          · exact ancs_root_after n o (by omega) y w hy hw hwo
      · rw [he] at hy; simp at hy

/-- The effective anchor of `x` is `x` or one of its ancestors (§44). -/
theorem effAnchor_mem (s : S3) (x : Nat) : s.effAnchor x = x ∨ s.effAnchor x ∈ s.ancs x :=
  List.mem_cons.1 (List.getLastD_mem_cons (l := s.ancs x) (a := x))

/-- The effective anchor of `x` does not exceed `x` (§44). -/
theorem effAnchor_le (s : S3) (x : Nat) : s.effAnchor x ≤ x := by
  rcases effAnchor_mem s x with h | h
  · exact Nat.le_of_eq h
  · exact Nat.le_of_lt (chain_lt h)

/-- The effective anchor of `x` is the element without origin of its chain (§44). -/
theorem effAnchor_eq {s : S3} : ∀ n x, x < n → ∀ r, (r = x ∨ r ∈ s.ancs x) → s.org r = none →
    s.effAnchor x = r
  | 0, _, h, _, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, x, hx, r, hr, hro => by
    rcases hr with rfl | hr
    · simp [S3.effAnchor, S3.ancs, chain_none hro]
    · cases ho : s.org x with
      | none => rw [S3.ancs, chain_none ho] at hr; simp at hr
      | some o =>
        rcases ancs_step ho with ⟨hlt, he⟩ | he
        · have e : s.effAnchor x = s.effAnchor o := by
            simp only [S3.effAnchor, he, List.getLastD_cons]
          rw [e]; rw [he] at hr
          exact effAnchor_eq n o (by omega) r (List.mem_cons.1 hr) hro
        · rw [he] at hr; simp at hr

/-- Under the origin order of `WF3` (§49.5), the effective anchor has no origin (§44). -/
theorem effAnchor_root {s : S3} (hw : WF3 s) (x : Nat) : s.org (s.effAnchor x) = none := by
  obtain ⟨r, hr, hro⟩ := reaches_root hw (x + 1) x (Nat.lt_succ_self x)
  rw [effAnchor_eq (x + 1) x (Nat.lt_succ_self x) r hr hro]; exact hro

/-- The effective anchor depends only on the origin chain (§44). -/
theorem effAnchor_congr {s s' : S3} {x : Nat} (h : s'.ancs x = s.ancs x) :
    s'.effAnchor x = s.effAnchor x := by simp only [S3.effAnchor, h]

/-- An anchor satisfying the rule of §44 has an existing effective anchor. -/
theorem effAnchorOK_get {s : S3} {x : Nat} {fd : Option Nat} (h : EffAnchorOK s x fd) :
    ∃ z, s.A[s.effAnchor x]? = some z := by
  unfold EffAnchorOK at h
  cases hz : s.A[s.effAnchor x]? with
  | none => rw [hz] at h; exact h.elim
  | some z => exact ⟨z, rfl⟩

/-- The effective anchor of an anchor satisfying the rule of §44 has a holder frame. -/
theorem effAnchorOK_frame {s : S3} {x : Nat} {fd : Option Nat} {z : Authority}
    (h : EffAnchorOK s x fd) (hz : s.A[s.effAnchor x]? = some z) :
    ∃ g, s.hframe z.holder = some g := by
  unfold EffAnchorOK at h; rw [hz] at h; simp only [OptP] at h
  cases hg : s.hframe z.holder with
  | none => rw [hg] at h; exact h.elim
  | some g => exact ⟨g, rfl⟩

/-- An anchor satisfying the rule of §44 is an authority of `A`. -/
theorem effAnchorOK_lt {s : S3} {x : Nat} {fd : Option Nat} (h : EffAnchorOK s x fd) :
    x < s.A.length := by
  obtain ⟨z, hz⟩ := effAnchorOK_get h
  rcases effAnchor_mem s x with e | e
  · rw [e] at hz; exact lt_of_getElem? hz
  · have : s.org x ≠ none := fun ho => by rw [S3.ancs, chain_none ho] at e; simp at e
    simp only [S3.org] at this
    cases hx : s.A[x]? with
    | none => rw [hx] at this; exact absurd rfl this
    | some _ => exact lt_of_getElem? hx

/-- The rule of §44 carries over between states with the same holder frame of the effective
anchor and the same ancestor relation on the relevant frames. -/
theorem effAnchorOK_of_same {s s' : S3} {x x' : Nat} {z z' : Authority}
    (hz : s.A[s.effAnchor x]? = some z) (hz' : s'.A[s'.effAnchor x']? = some z')
    (hh : s'.hframe z'.holder = s.hframe z.holder) {fd fd' : Option Nat}
    (hanc : ∀ g f, fd = some f → (ancestor s'.F g f ↔ ancestor s.F g f)) (hfd : fd' = fd) :
    EffAnchorOK s' x' fd' ↔ EffAnchorOK s x fd := by
  rw [hfd]; unfold EffAnchorOK; rw [hz, hz']; simp only [OptP]; rw [hh]
  cases hg : s.hframe z.holder with
  | none => simp
  | some g =>
    cases hf : fd with
    | none => simp
    | some f => simp only; rw [hanc g f hf]

/-- Pushing a frame absent from the stack does not change the ancestors of a frame of the stack
(§39). -/
theorem ancestor_push {F : Frames} {n g f : Nat} (hn : n ≠ f) :
    ancestor (n :: F) g f ↔ ancestor F g f := by
  have hne : (n != f) = true := by simpa using hn
  show g ∈ (n :: F).dropWhile (· != f) ↔ g ∈ F.dropWhile (· != f)
  rw [List.dropWhile_cons]; simp only [hne, ↓reduceIte]

/-! ## Places and usability (§40) -/

/-- A part lies below the places it belongs to (§40, §49.2). -/
theorem partOf_le {P : List Place} {l r : Nat} (h : partOf P l r) : r ≤ l := by
  rcases h.2 with rfl | h
  · exact Nat.le_refl _
  · exact Nat.le_of_lt (chain_lt h)

/-- A usable place is not dead (§40, item 1). -/
theorem usable_dead {s : S3} {q : Nat} (h : s.Usable q) : s.dead q = false := by
  cases h <;> assumption

/-- The owner of a usable place is live (§40, items 2–3). -/
theorem usable_owner_live {s : S3} {q : Nat} {pl : Place} (h : s.Usable q)
    (hpl : s.P[q]? = some pl) : HolderLive s pl.owner := by
  cases h with
  | frame hp _ ho hf => rw [hpl] at hp; cases hp; rw [ho]; exact hf
  | place hp _ ho hu => rw [hpl] at hp; cases hp; rw [ho]; exact hu

/-- A place that exists, is not dead and has a live owner is usable (§40). -/
theorem usable_of_owner {s : S3} {q : Nat} {pl : Place} (hpl : s.P[q]? = some pl)
    (hd : s.dead q = false) (h : HolderLive s pl.owner) : s.Usable q := by
  cases ho : pl.owner with
  | frame f => rw [ho] at h; exact .frame hpl hd ho h
  | place o => rw [ho] at h; exact .place hpl hd ho h

/-! ## Places after `enterFrame` (§72 `ok` effect) -/

section Enter

variable {s : S3} {ps : List Nat} {ls : LocalShape}

/-- The locals are appended to the places (§72 `ok` effect). -/
theorem enterP_len (s : S3) (ls : LocalShape) :
    (enterP s ls).length = s.P.length + ls.length := by
  simp [enterP, shapeP, toShape_length]

/-- Existing places are unchanged by `enterFrame` (§72 `ok` effect). -/
theorem enterP_lt {q : Nat} (h : q < s.P.length) : (enterP s ls)[q]? = s.P[q]? :=
  List.getElem?_append_left h

/-- Local `i` is the place `|P| + i`, owned by the new frame (§72 `ok` effect, §39). -/
theorem enterP_new {i : Nat} (h : i < ls.length) : (enterP s ls)[s.P.length + i]? =
    some ⟨(ls.toShape[i]?).bind (·.1), .frame s.nF, ((ls.toShape[i]?).map (·.2.2)).getD 0⟩ := by
  simp only [enterP, shapeP, List.getElem?_append_right (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left, List.getElem?_map,
    List.getElem?_range (show i < ls.toShape.length by rw [toShape_length]; exact h),
    Option.map_some, shapeOwner_toShape]

/-- A place after `enterFrame` is an existing place or a local owned by the new frame (§72 `ok`
effect). -/
theorem enterP_get {q : Nat} {pl : Place} (h : (enterP s ls)[q]? = some pl) :
    (q < s.P.length ∧ s.P[q]? = some pl) ∨ (s.P.length ≤ q ∧ ∃ i, i < ls.length ∧
      q = s.P.length + i ∧ pl = ⟨(ls.toShape[i]?).bind (·.1), .frame s.nF,
        ((ls.toShape[i]?).map (·.2.2)).getD 0⟩) := by
  by_cases hq : q < s.P.length
  · exact .inl ⟨hq, by rwa [enterP_lt hq] at h⟩
  · have hi : q - s.P.length < ls.length := by
      have := lt_of_getElem? h; rw [enterP_len] at this; omega
    have e : q = s.P.length + (q - s.P.length) := by omega
    rw [e, enterP_new hi] at h; cases h
    exact .inr ⟨by omega, _, hi, e, rfl⟩

/-- An authority after `enterFrame` is an existing one, moved to the new frame if it is a
parameter, or the root authority of a root local, held by the new frame (§72 `ok` effect). -/
theorem enter_get {j : Nat} {z : Authority} (h : (enterEff s ps ls).A[j]? = some z) :
    (j < s.A.length ∧ ∃ y, s.A[j]? = some y ∧
      z = if j ∈ ps then { y with holder := .frame s.nF } else y) ∨
    (s.A.length ≤ j ∧ ∃ i, (rootIdx ls.toShape)[j - s.A.length]? = some i ∧
      z = ⟨.modify, none, footprint (enterP s ls) (s.P.length + i), .frame s.nF, true⟩) := by
  simp only [enterEff] at h
  by_cases hj : j < s.A.length
  · have hj' : j < (mapI (fun j y => if j ∈ ps then { y with holder := .frame s.nF } else y) 0
        s.A).length := by rw [length_mapI]; exact hj
    rw [List.getElem?_append_left hj', getElem?_mapI] at h
    cases hy : s.A[j]? with
    | none => rw [hy] at h; cases h
    | some y => rw [hy] at h; cases h; exact .inl ⟨hj, y, rfl, by simp⟩
  · rw [List.getElem?_append_right (by rw [length_mapI]; omega), length_mapI,
      List.getElem?_map] at h
    cases hi : (rootIdx ls.toShape)[j - s.A.length]? with
    | none => rw [hi] at h; cases h
    | some i =>
      rw [hi] at h; cases h
      exact .inr ⟨by omega, i, rfl, by simp only [shapeOwner_toShape]⟩

/-- Existing authorities after `enterFrame`: only parameters change, and only their holder
(§72 `ok` effect). -/
theorem enter_lt {j : Nat} (h : j < s.A.length) : (enterEff s ps ls).A[j]? =
    (s.A[j]?).map fun y => if j ∈ ps then { y with holder := .frame s.nF } else y := by
  simp only [enterEff]
  rw [List.getElem?_append_left (by rw [length_mapI]; exact h), getElem?_mapI]; simp

/-- Origins of existing authorities are unchanged by `enterFrame` (§72: no additional right). -/
theorem enter_org_lt {j : Nat} (h : j < s.A.length) : (enterEff s ps ls).org j = s.org j := by
  simp only [S3.org, enter_lt h]
  cases s.A[j]? with
  | none => rfl
  | some y => simp only [Option.map_some, Option.bind_some]; split <;> rfl

/-- Origin chains of existing authorities are unchanged by `enterFrame` (§72). -/
theorem enter_ancs_lt {j : Nat} (h : j < s.A.length) : (enterEff s ps ls).ancs j = s.ancs j :=
  chain_congr fun _ hi => enter_org_lt (Nat.lt_of_le_of_lt hi h)

/-- The parent of local `i` (§72.2). -/
theorem enter_parentOf_new {i : Nat} (h : i < ls.length) :
    parentOf (enterP s ls) (s.P.length + i) = (ls.toShape[i]?).bind (·.1) := by
  simp [parentOf, enterP_new h]

/-- Parents of existing places are unchanged by `enterFrame` (§72). -/
theorem enter_parentOf_lt {q : Nat} (h : q < s.P.length) :
    parentOf (enterP s ls) q = parentOf s.P q := by
  simp [parentOf, enterP_lt h]

/-- The footprint of a local is made of locals (§40, §72.2). -/
theorem enter_root_fp_ge {i l : Nat} (h : l ∈ footprint (enterP s ls) (s.P.length + i)) :
    s.P.length ≤ l := by
  obtain ⟨-, -, -, h | h⟩ := mem_footprint.1 h
  · omega
  · have := chain_lt h; omega

/-- Two distinct root locals have disjoint footprints (§40, §72). -/
theorem enter_roots_disjoint {i i' l : Nat} (hii : i ≠ i')
    (hn : (ls.toShape[i]?).bind (·.1) = none) (hn' : (ls.toShape[i']?).bind (·.1) = none)
    (h : l ∈ footprint (enterP s ls) (s.P.length + i))
    (h' : l ∈ footprint (enterP s ls) (s.P.length + i')) : False := by
  have hlt : ∀ {j}, l ∈ footprint (enterP s ls) (s.P.length + j) → j < ls.length := fun hj => by
    obtain ⟨hl, -, -, hq⟩ := mem_footprint.1 hj
    rw [enterP_len] at hl
    rcases hq with hq | hq
    · omega
    · have := chain_lt hq; omega
  have hi := hlt h; have hi' := hlt h'
  have r := enter_parentOf_new (s := s) hi; rw [hn] at r
  have r' := enter_parentOf_new (s := s) hi'; rw [hn'] at r'
  obtain ⟨-, -, -, h | h⟩ := mem_footprint.1 h <;> obtain ⟨-, -, -, h' | h'⟩ := mem_footprint.1 h'
  · omega
  · subst h; rw [chain_none r] at h'; simp at h'
  · subst h'; rw [chain_none r'] at h; simp at h
  · exact hii (by have := chainF_root _ _ _ _ h r h' r'; omega)

/-- Locals are usable once the frame is entered: they are owned by the new frame (§72 `ok`
effect, §39, §40). -/
theorem enter_usable_new {i : Nat} (hi : i < ls.length) :
    (enterEff s ps ls).Usable (s.P.length + i) :=
  .frame (show (enterP s ls)[_]? = _ from enterP_new hi) (by simp [enterEff])
    rfl (List.mem_cons_self ..)

/-- Existing usable places stay usable when a frame is entered (§40, §72). -/
theorem enter_usable_old {q : Nat} (h : s.Usable q) : (enterEff s ps ls).Usable q := by
  induction h with
  | @frame q f pl hpl hd ho hf =>
    exact .frame (show (enterP s ls)[q]? = _ by rw [enterP_lt (lt_of_getElem? hpl)]; exact hpl)
      (by simp [enterEff, hd]) ho (List.mem_cons_of_mem _ hf)
  | @place q o pl hpl hd ho _ ih =>
    exact .place (show (enterP s ls)[q]? = _ by rw [enterP_lt (lt_of_getElem? hpl)]; exact hpl)
      (by simp [enterEff, hd]) ho ih

/-- An existing place usable after `enterFrame` was usable before: the new frame owns only the
locals (§40, §49.3, §72). -/
theorem enter_usable_back (hwf : WF3 s) {q : Nat} (h : (enterEff s ps ls).Usable q)
    (hq : q < s.P.length) : s.Usable q := by
  induction h with
  | @frame q f pl hpl hd ho hf =>
    have hpl' : s.P[q]? = some pl := by
      have : (enterP s ls)[q]? = some pl := hpl
      rwa [enterP_lt hq] at this
    have hd' : s.dead q = false := by simpa [enterEff, hq] using hd
    have hlt := hwf.owners.1 q pl f hpl' ho
    rcases List.mem_cons.1 hf with e | hf
    · subst e; exact absurd hlt (Nat.lt_irrefl _)
    · exact .frame hpl' hd' ho hf
  | @place q o pl hpl hd ho _ ih =>
    have hpl' : s.P[q]? = some pl := by
      have : (enterP s ls)[q]? = some pl := hpl
      rwa [enterP_lt hq] at this
    have hd' : s.dead q = false := by simpa [enterEff, hq] using hd
    exact .place hpl' hd' ho (ih (hwf.owners.2.1 q pl o hpl' ho))

/-- Ancestors of a local are locals (§72.2). -/
theorem enter_chain_ge (hsh : ShapeOK s.P.length ls.toShape) : ∀ n q, q < n → s.P.length ≤ q →
    ∀ x ∈ chain (parentOf (enterP s ls)) q, s.P.length ≤ x
  | 0, _, h, _, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, q, hq, hge, x, hx => by
    have hi : q - s.P.length < ls.length := by
      cases hpo : parentOf (enterP s ls) q with
      | none => rw [chain_none hpo] at hx; simp at hx
      | some r =>
        simp only [parentOf] at hpo
        cases h' : (enterP s ls)[q]? with
        | none => rw [h'] at hpo; cases hpo
        | some _ => have := lt_of_getElem? h'; rw [enterP_len] at this; omega
    have hpo := enter_parentOf_new (s := s) hi
    rw [show s.P.length + (q - s.P.length) = q by omega] at hpo
    cases hb : (ls.toShape[q - s.P.length]?).bind (·.1) with
    | none => rw [hb] at hpo; rw [chain_none hpo] at hx; simp at hx
    | some r =>
      rw [hb] at hpo
      have h1 := shape_parent hsh hi hb
      rw [chain_cons hpo (by omega)] at hx
      rcases List.mem_cons.1 hx with rfl | hx
      · omega
      · exact enter_chain_ge hsh n r (by omega) (by omega) x hx

/-- An existing leaf stays a leaf: the parents of locals are locals (§40, §72.2). -/
theorem enter_isLeaf_old (hsh : ShapeOK s.P.length ls.toShape) {l : Nat} (hl : l < s.P.length) :
    isLeaf (enterP s ls) l ↔ isLeaf s.P l := by
  simp only [isLeaf, enterP_len]
  constructor
  · intro h r hr; rw [← enter_parentOf_lt hr]; exact h r (by omega)
  · intro h r hr
    by_cases hrn : r < s.P.length
    · rw [enter_parentOf_lt hrn]; exact h r hrn
    · intro he
      have hi : r - s.P.length < ls.length := by omega
      have hpo' := enter_parentOf_new (s := s) hi
      rw [show s.P.length + (r - s.P.length) = r by omega, he] at hpo'
      have := shape_parent hsh hi hpo'.symm; omega

/-- The footprint of an existing place does not change when a frame is entered (§40, §72.2). -/
theorem enter_footprint_old (hsh : ShapeOK s.P.length ls.toShape) {q : Nat}
    (hq : q < s.P.length) : ∀ l, l ∈ footprint (enterP s ls) q ↔ l ∈ footprint s.P q := by
  have hch : ∀ l < s.P.length, chain (parentOf (enterP s ls)) l = chain (parentOf s.P) l :=
    fun l hl => chain_congr fun j hj => enter_parentOf_lt (by omega)
  intro l
  rw [mem_footprint, mem_footprint]
  constructor
  · rintro ⟨hl, hleaf, -, hpo⟩
    have hln : l < s.P.length := by
      rcases Nat.lt_or_ge l s.P.length with h | h
      · exact h
      · rcases hpo with rfl | hpo
        · omega
        · have := enter_chain_ge hsh (l + 1) l (Nat.lt_succ_self l) h q hpo; omega
    refine ⟨hln, (enter_isLeaf_old hsh hln).1 hleaf, hln, ?_⟩
    rcases hpo with rfl | hpo
    · exact .inl rfl
    · exact .inr (by rwa [hch l hln] at hpo)
  · rintro ⟨hl, hleaf, -, hpo⟩
    have hl' : l < (enterP s ls).length := by rw [enterP_len]; omega
    refine ⟨hl', (enter_isLeaf_old hsh hl).2 hleaf, hl', ?_⟩
    rcases hpo with rfl | hpo
    · exact .inl rfl
    · exact .inr (by rwa [hch l hl])

/-- Existing parts keep their roots (§40, §72). -/
theorem enter_partOf_old {l r : Nat} (hl : l < s.P.length) :
    partOf (enterP s ls) l r ↔ partOf s.P l r := by
  have hch : chain (parentOf (enterP s ls)) l = chain (parentOf s.P) l :=
    chain_congr fun j hj => enter_parentOf_lt (Nat.lt_of_le_of_lt hj hl)
  simp only [partOf, hch, enterP_len]
  exact ⟨fun h => ⟨hl, h.2⟩, fun h => ⟨by omega, h.2⟩⟩

/-! ## `enterFrame` preserves `WF3` (§49, §72) -/

/-- `enterFrame` preserves `RootChain` (§49.6, §72): existing authorities keep their chains and
existing places their footprints; each new root authority is the root authority of its local. -/
theorem enter_rootChain (hwf : WF3 s) (hsh : ShapeOK s.P.length ls.toShape) :
    RootChain (enterEff s ps ls) := by
  intro a y l ha hl hleaf
  rcases enter_get ha with ⟨ha', y₀, hy₀, rfl⟩ | ⟨ha', i, hi, rfl⟩
  · have hl0 : l ∈ y₀.footprint := by split at hl <;> exact hl
    obtain ⟨hlt, hleaf0⟩ := hwf.footprints a y₀ hy₀ l hl0
    obtain ⟨x0, z, r, hx0, hz, hzo, ⟨hrl, hrp⟩, hlr, hfz⟩ :=
      hwf.rootChain a y₀ l hy₀ hl0 hleaf0
    have hx0lt : x0 < s.A.length := by
      rcases hx0 with rfl | hx0
      · exact ha'
      · exact Nat.lt_trans (chain_lt hx0) ha'
    refine ⟨x0, _, r, by rw [enter_ancs_lt ha']; exact hx0, by rw [enter_lt hx0lt, hz]; rfl, ?_,
      ⟨?_, ?_⟩, (enter_partOf_old hlt).2 hlr, fun l' => ?_⟩
    · split <;> exact hzo
    · show r < (enterP s ls).length; rw [enterP_len]; omega
    · show parentOf (enterP s ls) r = none; rw [enter_parentOf_lt hrl]; exact hrp
    · show _ ↔ l' ∈ footprint (enterP s ls) r
      rw [enter_footprint_old hsh hrl]
      split <;> exact hfz l'
  · obtain ⟨hil, hin⟩ := rootIdx_mem hi
    refine ⟨a, _, s.P.length + i, .inl rfl, ha, rfl, ⟨?_, ?_⟩, (mem_footprint.1 hl).2.2,
      fun _ => Iff.rfl⟩
    · show s.P.length + i < (enterP s ls).length; rw [enterP_len]; omega
    · show parentOf (enterP s ls) (s.P.length + i) = none; rw [enter_parentOf_new hil]; exact hin

/-- `enterFrame` preserves `RootHeld` (§49.7, §72): an existing usable root keeps its root
authority, which is not a parameter; a root local receives its root authority, held by the new
frame that owns it. -/
theorem enter_rootHeld (hwf : WF3 s) (hpre : EnterPre s ps ls) : RootHeld (enterEff s ps ls) := by
  intro r hrp hur
  by_cases hr : r < s.P.length
  · have hrp0 : RootPlace s.P r := ⟨hr, by rw [← enter_parentOf_lt hr]; exact hrp.2⟩
    obtain ⟨i, z, pr, hz, za, zo, zm, hpr, hzh, hzf⟩ :=
      hwf.rootHeld r hrp0 (enter_usable_back hwf hur hr)
    have hni : i ∉ ps := fun hm => by
      have h2 := hpre.params i hm
      simp only [OptP, hz] at h2; exact h2.2.2 zo
    refine ⟨i, z, pr, by rw [enter_lt (lt_of_getElem? hz), hz]; simp [hni], za, zo, zm,
      by show (enterP s ls)[r]? = _; rw [enterP_lt hr]; exact hpr, hzh, fun l => ?_⟩
    show _ ↔ l ∈ footprint (enterP s ls) r
    rw [enter_footprint_old hpre.localsOK hr]; exact hzf l
  · have hrl := hrp.1
    rw [show (enterEff s ps ls).P = enterP s ls from rfl, enterP_len] at hrl
    obtain ⟨k, rfl⟩ : ∃ k, r = s.P.length + k := ⟨r - s.P.length, by omega⟩
    have hk : k < ls.length := by omega
    have hn : (ls.toShape[k]?).bind (·.1) = none := by
      have := hrp.2
      rw [show (enterEff s ps ls).P = enterP s ls from rfl, enter_parentOf_new hk] at this
      exact this
    obtain ⟨j, hj⟩ := append_map_get
      (mapI (fun j y => if j ∈ ps then { y with holder := .frame s.nF } else y) 0 s.A)
      (fun i => (⟨.modify, none, footprint (enterP s ls) (s.P.length + i),
        shapeOwner ls.toShape (.frame s.nF) i, true⟩ : Authority)) (mem_rootIdx hk hn)
    exact ⟨_, _, _, hj, rfl, rfl, rfl, enterP_new hk, shapeOwner_toShape _ _ _,
      fun _ => Iff.rfl⟩

/-- `enterFrame` preserves `RootHeldConv` (§40, §49.7, §72): an authority without origin is not
a parameter and keeps its holder; a new root authority is held by the frame owning its local. -/
theorem enter_rootHeldConv (hwf : WF3 s) (hpre : EnterPre s ps ls) (hr : RootHeldConv s) :
    RootHeldConv (enterEff s ps ls) := by
  intro x z l r hx ho hl hrp hlr
  rcases enter_get hx with ⟨-, z₀, hz₀, rfl⟩ | ⟨-, i, hi, rfl⟩
  · have ho' : z₀.origin = none := by split at ho <;> exact ho
    have hl' : l ∈ z₀.footprint := by split at hl <;> exact hl
    have hnp : x ∉ ps := fun hp => by
      have := hpre.params x hp; simp only [OptP, hz₀] at this; exact this.2.2 ho'
    have hlt := (hwf.footprints x z₀ hz₀ l hl').1
    have hlr' : partOf s.P l r := (enter_partOf_old hlt).1 hlr
    have hrl : r < s.P.length := Nat.lt_of_le_of_lt (partOf_le hlr') hlt
    have hrp' : RootPlace s.P r := ⟨hrl, by rw [← enter_parentOf_lt hrl]; exact hrp.2⟩
    obtain ⟨pr, hpr, hh⟩ := hr x z₀ l r hz₀ ho' hl' hrp' hlr'
    exact ⟨pr, by show (enterP s ls)[r]? = _; rw [enterP_lt hrl]; exact hpr, by simp [hnp, hh]⟩
  · obtain ⟨hil, hin⟩ := rootIdx_mem hi
    have hroot : RootPlace (enterEff s ps ls).P (s.P.length + i) :=
      ⟨by show s.P.length + i < (enterP s ls).length; rw [enterP_len]; omega,
        by show parentOf (enterP s ls) (s.P.length + i) = none
           rw [enter_parentOf_new hil]; exact hin⟩
    obtain rfl := rootOf_unique hrp hroot hlr (mem_footprint.1 hl).2.2
    exact ⟨_, enterP_new hil, rfl⟩

/-- `enterFrame` preserves `WF3` (§49, §72): the new frame is fresh, the locals are owned by it
with earlier parents, parameters move to it, and each root local receives its root authority. -/
theorem enter_wf (hwf : WF3 s) (hpre : EnterPre s ps ls) : WF3 (enterEff s ps ls) := by
  have hsh := hpre.localsOK
  have live : ∀ (hd : Holder), HolderLive s hd → HolderLive (enterEff s ps ls) hd := by
    intro hd hl; cases hd with
    | frame f => exact List.mem_cons_of_mem _ hl
    | place p => exact enter_usable_old hl
  refine ⟨⟨by simp [enterEff], ?_, ?_⟩, ?_, ⟨?_, ?_, fun q hq => hq.frameOf⟩, ?_, ?_,
    enter_rootChain hwf hsh, enter_rootHeld hwf hpre, ?_⟩
  · exact List.nodup_cons.2 ⟨fun hm => Nat.lt_irrefl _ (hwf.frames.2.2 _ hm), hwf.frames.2.1⟩
  · intro f hf; rcases List.mem_cons.1 hf with rfl | hf
    · exact Nat.lt_succ_self _
    · exact Nat.lt_succ_of_lt (hwf.frames.2.2 f hf)
  · intro q pl r hq hp
    rcases enterP_get hq with ⟨hq', hq''⟩ | ⟨hq', i, hi, rfl, rfl⟩
    · obtain ⟨pr, hpr, hlt, ho, hd⟩ := hwf.places q pl r hq'' hp
      refine ⟨pr, by show (enterP s ls)[r]? = _; rw [enterP_lt (by omega)]; exact hpr, hlt, ho, ?_⟩
      simp [enterEff, show ¬ s.P.length ≤ r by omega, show ¬ s.P.length ≤ q by omega, hd]
    · have h1 := shape_parent hsh hi hp
      have hri : r - s.P.length < ls.length := by omega
      have hr' := enterP_new (s := s) (ls := ls) hri
      rw [show s.P.length + (r - s.P.length) = r by omega] at hr'
      exact ⟨_, hr', by omega, rfl, by simp [enterEff, show s.P.length ≤ r by omega]⟩
  · intro q pl f hq ho
    rcases enterP_get hq with ⟨-, hq'⟩ | ⟨-, i, -, -, rfl⟩
    · exact Nat.lt_succ_of_lt (hwf.owners.1 q pl f hq' ho)
    · cases ho; exact Nat.lt_succ_self _
  · intro q pl o hq ho
    rcases enterP_get hq with ⟨-, hq'⟩ | ⟨-, i, -, -, rfl⟩
    · have := hwf.owners.2.1 q pl o hq' ho
      show o < (enterP s ls).length; rw [enterP_len]; omega
    · cases ho
  · intro a y hy l hl
    rcases enter_get hy with ⟨-, y₀, hy₀, rfl⟩ | ⟨-, i, -, rfl⟩
    · obtain ⟨hlt, hleaf⟩ := hwf.footprints a y₀ hy₀ l (by split at hl <;> exact hl)
      exact ⟨by show l < (enterP s ls).length; rw [enterP_len]; omega,
        (enter_isLeaf_old hsh hlt).2 hleaf⟩
    · exact ⟨(mem_footprint.1 hl).1, (mem_footprint.1 hl).2.1⟩
  · intro b y a hb ho
    rcases enter_get hb with ⟨-, y₀, hy₀, rfl⟩ | ⟨-, _, -, rfl⟩
    · exact hwf.origins b y₀ a hy₀ (by split at ho <;> exact ho)
    · cases ho
  · intro a y hy ya
    rcases enter_get hy with ⟨-, y₀, hy₀, rfl⟩ | ⟨-, i, -, rfl⟩
    · have ya₀ : y₀.active = true := by split at ya <;> exact ya
      split
      · exact (List.mem_cons_self .. : s.nF ∈ s.nF :: s.F)
      · exact live _ (hwf.holders a y₀ hy₀ ya₀)
    · exact (List.mem_cons_self .. : s.nF ∈ s.nF :: s.F)

/-! ## `enterFrame` preserves `Inv3` (§50–§54, §57, §72) -/

/-- `enterFrame` preserves `I1` (§50, §72): moving parameters changes only holders, and the root
authorities of the locals cover only the locals, pairwise disjointly. -/
theorem enter_i1 (hwf : WF3 s) (i1 : I1 s) : I1 (enterEff s ps ls) := by
  intro a b x y p hab ha hb xa ya xp yp hnab hnba
  rcases enter_get ha with ⟨ha', x₀, hx₀, rfl⟩ | ⟨ha', i, hi, rfl⟩ <;>
    rcases enter_get hb with ⟨hb', y₀, hy₀, rfl⟩ | ⟨hb', i', hi', rfl⟩
  · rw [enter_ancs_lt hb'] at hnab; rw [enter_ancs_lt ha'] at hnba
    have := i1 a b x₀ y₀ p hab hx₀ hy₀ (by split at xa <;> exact xa)
      (by split at ya <;> exact ya) (by split at xp <;> exact xp) (by split at yp <;> exact yp)
      hnab hnba
    constructor
    · split <;> exact this.1
    · split <;> exact this.2
  · have := (hwf.footprints a x₀ hx₀ p (by split at xp <;> exact xp)).1
    have := enter_root_fp_ge yp; omega
  · have := (hwf.footprints b y₀ hy₀ p (by split at yp <;> exact yp)).1
    have := enter_root_fp_ge xp; omega
  · have hk : a - s.A.length ≠ b - s.A.length := by omega
    have hii : i ≠ i' := fun e => hk (rootIdx_inj hi (by rw [e]; exact hi'))
    exact (enter_roots_disjoint hii (rootIdx_mem hi).2 (rootIdx_mem hi').2 xp yp).elim

/-- `enterFrame` preserves `I1`–`I4` (§50–§53, §72): moving parameters changes only holders, the
root authorities of the locals have no origin, and the locals have no anchor. -/
theorem enter_inv3base (hwf : WF3 s) (hinv : Inv3base s) :
    Inv3base (enterEff s ps ls) := by
  obtain ⟨i1, i2, i3, -⟩ := hinv
  refine ⟨enter_i1 hwf i1, ?_, ?_, i4_always _⟩
  · intro b y a hb ho
    rcases enter_get hb with ⟨-, y₀, hy₀, rfl⟩ | ⟨-, _, -, rfl⟩
    · obtain ⟨x₁, hx₁, hm, hh⟩ := i2 b y₀ a hy₀ (by split at ho <;> exact ho)
      refine ⟨_, by rw [enter_lt (lt_of_getElem? hx₁), hx₁]; rfl, ?_, fun p hp => ?_⟩
      · split <;> split <;> exact hm
      · have := hh p (by split at hp <;> exact hp)
        split <;> exact this
    · cases ho
  · intro q hq x hx
    by_cases hlt : q < s.P.length
    · have hx' : x ∈ s.D q := by simpa [enterEff, show ¬ s.P.length ≤ q by omega] using hx
      obtain ⟨y, hy, ya⟩ := i3 q (enter_usable_back hwf hq hlt) x hx'
      exact ⟨_, by rw [enter_lt (lt_of_getElem? hy), hy]; rfl, by split <;> exact ya⟩
    · simp [enterEff, show s.P.length ≤ q by omega] at hx

/-- The frame of an existing place is unchanged by `enterFrame` (§40, §72). -/
theorem enter_frameOf_old (hwf : WF3 s) {q f : Nat} (hq : q < s.P.length) :
    FrameOf (enterEff s ps ls) q f ↔ FrameOf s q f := by
  constructor
  · intro h
    revert hq
    induction h with
    | @frame q f pl hpl ho =>
      intro hq
      exact .frame (by have : (enterP s ls)[q]? = some pl := hpl; rwa [enterP_lt hq] at this) ho
    | @place q o f pl hpl ho _ ih =>
      intro hq
      have hpl' : s.P[q]? = some pl := by
        have : (enterP s ls)[q]? = some pl := hpl; rwa [enterP_lt hq] at this
      exact .place hpl' ho (ih (hwf.owners.2.1 q pl o hpl' ho))
  · intro h
    clear hq
    induction h with
    | frame hpl ho =>
      exact .frame (show (enterP s ls)[_]? = _ by rw [enterP_lt (lt_of_getElem? hpl)]; exact hpl) ho
    | place hpl ho _ ih =>
      exact .place (show (enterP s ls)[_]? = _ by rw [enterP_lt (lt_of_getElem? hpl)]; exact hpl)
        ho ih

/-- `placeFrame` of an existing place is unchanged by `enterFrame` (§40, §72). -/
theorem enter_pframe_old (hwf : WF3 s) {q : Nat} (hq : q < s.P.length) :
    (enterEff s ps ls).pframe q = s.pframe q :=
  Option.ext fun f => by rw [pframe_iff, pframe_iff, enter_frameOf_old hwf hq]

/-- `enterFrame` preserves `AnchorOrder` (§44, §72): frames of existing places do not change, the
new frame is not an ancestor of an existing one, and an effective anchor, having no origin, is
never a parameter. -/
theorem enter_anchorOrder (hwf : WF3 s) (hao : AnchorOrder s) (hpre : EnterPre s ps ls) :
    AnchorOrder (enterEff s ps ls) := by
  intro q hq x hx
  by_cases hlt : q < s.P.length
  · have hq0 := enter_usable_back hwf hq hlt
    have hx0 : x ∈ s.D q := by simpa [enterEff, show ¬ s.P.length ≤ q by omega] using hx
    have hok := hao q hq0 x hx0
    obtain ⟨z, hz⟩ := effAnchorOK_get hok
    obtain ⟨g, hg⟩ := effAnchorOK_frame hok hz
    have hxl := effAnchorOK_lt hok
    have he : (enterEff s ps ls).effAnchor x = s.effAnchor x :=
      effAnchor_congr (enter_ancs_lt hxl)
    have hrl : s.effAnchor x < s.A.length := Nat.lt_of_le_of_lt (effAnchor_le s x) hxl
    have hro : s.org (s.effAnchor x) = none := effAnchor_root hwf x
    have hnp : s.effAnchor x ∉ ps := fun hp => by
      have := hpre.params _ hp; simp only [OptP, hz] at this
      exact this.2.2 (by simpa [S3.org, hz] using hro)
    refine (effAnchorOK_of_same (s' := enterEff s ps ls) (z' := z) hz
      (by rw [he, enter_lt hrl, hz]; simp [hnp]) ?_ ?_ (enter_pframe_old hwf hlt)).2 hok
    · cases hh : z.holder with
      | frame f => rfl
      | place p =>
        rw [hh] at hg
        exact enter_pframe_old hwf (pframe_iff.1 hg).lt
    · intro g f hf
      obtain ⟨f', hf', hfF⟩ := hq0.frameOf
      rw [pframe_iff.2 hf'] at hf; rw [← Option.some.inj hf]
      exact ancestor_push fun e => Nat.lt_irrefl _ (e ▸ hwf.frames.2.2 _ hfF)
  · simp [enterEff, show s.P.length ≤ q by omega] at hx

/-- `enterFrame` preserves `NoDangling` (§54, §72): existing places keep their footprints and
their usability; a new root authority covers only its local, which is usable. -/
theorem enter_noDangling (hwf : WF3 s) (hnd : NoDangling s) (hpre : EnterPre s ps ls) :
    NoDangling (enterEff s ps ls) := by
  intro j z hz za q hq l hl hlz
  obtain ⟨hlP, -, hlq⟩ := mem_footprint.1 hl
  have hql : q ≤ l := partOf_le hlq
  rcases enter_get hz with ⟨-, y, hy, rfl⟩ | ⟨-, i, -, rfl⟩
  · have hly : l ∈ y.footprint := by split at hlz <;> exact hlz
    have ya : y.active = true := by split at za <;> exact za
    have hqo : q < s.P.length := Nat.lt_of_le_of_lt hql (hwf.footprints j y hy l hly).1
    exact hnd j y hy ya q (fun hu => hq (enter_usable_old hu)) l
      ((enter_footprint_old hpre.localsOK hqo l).1 hl) hly
  · have hge : s.P.length ≤ l := enter_root_fp_ge hlz
    by_cases hqo : q < s.P.length
    · have := (mem_footprint.1 ((enter_footprint_old hpre.localsOK hqo l).1 hl)).1; omega
    · have hlP' : l < (enterP s ls).length := hlP
      rw [enterP_len] at hlP'
      have hu := enter_usable_new (s := s) (ps := ps) (ls := ls) (i := q - s.P.length) (by omega)
      rw [show s.P.length + (q - s.P.length) = q by omega] at hu
      exact hq hu

end Enter

/-! ## The first surviving origin (§73.4) -/

/-- The first surviving element of a list survives and belongs to it (§73.4). -/
theorem firstSurv_some {s : S3} {F₀ : Frames} {l : List Nat} {z : Nat}
    (h : firstSurv s F₀ l = some z) : z ∈ l ∧ Survives s F₀ z :=
  ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

/-- No element of a list without first surviving element survives (§73.4). -/
theorem firstSurv_none {s : S3} {F₀ : Frames} {l : List Nat} (h : firstSurv s F₀ l = none) :
    ∀ w ∈ l, ¬ Survives s F₀ w := by
  intro w hw hs
  have := List.find?_eq_none.1 h w hw
  simp [hs] at this

/-- The first surviving strict ancestor (§73.4): an ancestor that survives, such that every
surviving ancestor is it or one of its own ancestors. -/
theorem firstSurv_ancs {s : S3} {F₀ : Frames} :
    ∀ n x, x < n → ∀ z, firstSurv s F₀ (s.ancs x) = some z →
      z ∈ s.ancs x ∧ Survives s F₀ z ∧
        ∀ w ∈ s.ancs x, Survives s F₀ w → w = z ∨ w ∈ s.ancs z
  | 0, _, h, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, x, hx, z, hz => by
    cases ho : s.org x with
    | none => rw [S3.ancs, chain_none ho] at hz; simp [firstSurv] at hz
    | some o =>
      obtain ⟨hlt, he⟩ : o < x ∧ s.ancs x = o :: s.ancs o := by
        rcases ancs_step ho with h | he
        · exact h
        · rw [he] at hz; simp [firstSurv] at hz
      rw [he] at hz ⊢
      by_cases hs : Survives s F₀ o
      · simp only [firstSurv, List.find?_cons_of_pos (p := fun z => decide (Survives s F₀ z))
          (by simpa using hs), Option.some.injEq] at hz
        subst hz
        refine ⟨List.mem_cons_self .., hs, fun w hw' _ => ?_⟩
        rcases List.mem_cons.1 hw' with rfl | hw'
        · exact .inl rfl
        · exact .inr hw'
      · simp only [firstSurv, List.find?_cons_of_neg (p := fun z => decide (Survives s F₀ z))
          (by simpa using hs)] at hz
        obtain ⟨h1, h2, h3⟩ := firstSurv_ancs n o (by omega) z hz
        refine ⟨List.mem_cons_of_mem _ h1, h2, fun w hw' hws => ?_⟩
        rcases List.mem_cons.1 hw' with rfl | hw'
        · exact absurd hws hs
        · exact h3 w hw' hws

/-! ## Authorities after `exitFrame` (§73 `ok` effect) -/

section Exit

variable {s : S3}

/-- Authority `j` after the exit (§73 `ok` effect). -/
theorem exit_A_get (s : S3) (j : Nat) :
    (exitEff s).A[j]? = (s.A[j]?).map (exitG s s.F.tail j) := by
  simp [exitEff, getElem?_mapI]

/-- An authority after the exit comes from the authority of the same identity (§73). -/
theorem exit_get {j : Nat} {z : Authority} (hz : (exitEff s).A[j]? = some z) :
    ∃ z₀, s.A[j]? = some z₀ ∧ z = exitG s s.F.tail j z₀ := by
  rw [exit_A_get] at hz
  obtain ⟨z₀, hz₀, rfl⟩ := Option.map_eq_some_iff.1 hz
  exact ⟨z₀, hz₀, rfl⟩

/-- Reanchoring and release change neither the own mode, nor the footprint, nor the holder
(§73 `ok` effect, fourth item). -/
theorem exitG_same (s : S3) (F₀ : Frames) (a : Nat) (y : Authority) :
    (exitG s F₀ a y).mode = y.mode ∧ (exitG s F₀ a y).footprint = y.footprint ∧
    (exitG s F₀ a y).holder = y.holder := by
  unfold exitG; split
  · split <;> simp
  · simp

/-- An authority active after the exit survives (§73 `ok` effect, second item). -/
theorem exitG_active {F₀ : Frames} {a : Nat} {y : Authority} :
    (exitG s F₀ a y).active = true → Survives s F₀ a := by
  unfold exitG; split
  · intro; assumption
  · simp

/-- A surviving authority stays active (§73 `ok` effect). -/
theorem exitG_surv {F₀ : Frames} {a : Nat} {y : Authority} (hy : s.A[a]? = some y)
    (h : Survives s F₀ a) : (exitG s F₀ a y).active = true := by
  have hya : y.active = true := by unfold Survives at h; rw [hy] at h; exact h.1
  unfold exitG; simp only [h, ↓reduceIte]; split <;> simpa using hya

/-- An authority active after the exit was active before (§73 `ok` effect). -/
theorem exitG_active' {F₀ : Frames} {a : Nat} {y : Authority} (hy : s.A[a]? = some y)
    (h : (exitG s F₀ a y).active = true) : y.active = true := by
  have := exitG_active h; unfold Survives at this; rw [hy] at this; exact this.1

/-- The origin after the exit is unchanged, or it is the first surviving ancestor of a surviving
derived authority (§73 `ok` effect, third item). -/
theorem exitG_origin {F₀ : Frames} {a : Nat} {y : Authority} :
    (exitG s F₀ a y).origin = y.origin ∨
    (Survives s F₀ a ∧ y.origin ≠ none ∧ (exitG s F₀ a y).origin = firstSurv s F₀ (s.ancs a)) := by
  unfold exitG; split
  · rename_i hs; split
    · exact .inl rfl
    · rename_i o ho; exact .inr ⟨hs, by simp [ho], rfl⟩
  · exact .inl rfl

/-- After the exit, surviving ancestors of an authority are still its ancestors (§73.4). -/
theorem exit_ancs_keep :
    ∀ n x, x < n → ∀ w ∈ s.ancs x, Survives s s.F.tail w → w ∈ (exitEff s).ancs x
  | 0, _, h, _, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, x, hx, w, hw', hws => by
    cases hy : s.A[x]? with
    | none =>
      have : s.org x = none := by simp [S3.org, hy]
      rw [S3.ancs, chain_none this] at hw'; simp at hw'
    | some y =>
      cases ho : y.origin with
      | none =>
        have : s.org x = none := by simp [S3.org, hy, ho]
        rw [S3.ancs, chain_none this] at hw'; simp at hw'
      | some o =>
        have hob : s.org x = some o := by simp [S3.org, hy, ho]
        obtain ⟨hlt, hax⟩ : o < x ∧ s.ancs x = o :: s.ancs o := by
          rcases ancs_step hob with h | hax
          · exact h
          · rw [hax] at hw'; simp at hw'
        have e' : (exitEff s).org x = (exitG s s.F.tail x y).origin := by
          simp [S3.org, exit_A_get, hy]
        rcases exitG_origin (s := s) (F₀ := s.F.tail) (a := x) (y := y) with e | ⟨-, -, e⟩
        · rw [e, ho] at e'
          rw [show (exitEff s).ancs x = o :: (exitEff s).ancs o from chain_cons e' hlt]
          rw [hax] at hw'
          rcases List.mem_cons.1 hw' with rfl | hw'
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (exit_ancs_keep n o (by omega) w hw' hws)
        · rw [e] at e'
          cases hz : firstSurv s s.F.tail (s.ancs x) with
          | none => exact absurd hws (firstSurv_none hz w hw')
          | some z =>
            rw [hz] at e'
            obtain ⟨hz1, -, hz3⟩ := firstSurv_ancs (x + 1) x (Nat.lt_succ_self x) z hz
            have hzx := chain_lt hz1
            rw [show (exitEff s).ancs x = z :: (exitEff s).ancs z from chain_cons e' hzx]
            rcases hz3 w hw' hws with rfl | hw''
            · exact List.mem_cons_self ..
            · exact List.mem_cons_of_mem _ (exit_ancs_keep n z (by omega) w hw'' hws)

/-- The precondition of §73.4 as stated by `ExitPre.origins`. -/
abbrev OriginsSurvive (s : S3) : Prop :=
  ∀ a ∈ List.range s.A.length, Survives s s.F.tail a → s.org a ≠ none →
    firstSurv s s.F.tail (s.ancs a) ≠ none

/-- The root of an origin chain stays on the chain after the exit (§73.4), when every surviving
derived authority has a surviving origin. -/
theorem exit_root_kept (h3 : OriginsSurvive s) :
    ∀ n a, a < n → ∀ x0, x0 ∈ s.ancs a → s.org x0 = none → x0 ∈ (exitEff s).ancs a
  | 0, _, h, _, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, a, ha, x0, hx0, hx0o => by
    cases hy : s.A[a]? with
    | none =>
      have : s.org a = none := by simp [S3.org, hy]
      rw [S3.ancs, chain_none this] at hx0; simp at hx0
    | some y =>
      cases ho : y.origin with
      | none =>
        have : s.org a = none := by simp [S3.org, hy, ho]
        rw [S3.ancs, chain_none this] at hx0; simp at hx0
      | some o =>
        have hob : s.org a = some o := by simp [S3.org, hy, ho]
        obtain ⟨hlt, hax⟩ : o < a ∧ s.ancs a = o :: s.ancs o := by
          rcases ancs_step hob with h | hax
          · exact h
          · rw [hax] at hx0; simp at hx0
        have e' : (exitEff s).org a = (exitG s s.F.tail a y).origin := by
          simp [S3.org, exit_A_get, hy]
        rcases exitG_origin (s := s) (F₀ := s.F.tail) (a := a) (y := y) with e | ⟨hsv, -, e⟩
        · rw [e, ho] at e'
          rw [show (exitEff s).ancs a = o :: (exitEff s).ancs o from chain_cons e' hlt]
          rw [hax] at hx0
          rcases List.mem_cons.1 hx0 with rfl | hx0
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (exit_root_kept h3 n o (by omega) x0 hx0 hx0o)
        · rw [e] at e'
          cases hz : firstSurv s s.F.tail (s.ancs a) with
          | none =>
            exact absurd hz (h3 a (List.mem_range.2 (lt_of_getElem? hy)) hsv (by rw [hob]; simp))
          | some z =>
            rw [hz] at e'
            have hz1 := (firstSurv_some hz).1
            have hzx := chain_lt hz1
            rw [show (exitEff s).ancs a = z :: (exitEff s).ancs z from chain_cons e' hzx]
            rcases ancs_root_after (a + 1) a (Nat.lt_succ_self a) z x0 hz1 hx0 hx0o with rfl | hx'
            · exact List.mem_cons_self ..
            · exact List.mem_cons_of_mem _ (exit_root_kept h3 n z (by omega) x0 hx' hx0o)

/-- The root of the origin chain of a surviving authority survives (§73.4), when every surviving
derived authority has a surviving origin. -/
theorem exit_root_survives (h3 : OriginsSurvive s) :
    ∀ n a, a < n → Survives s s.F.tail a → ∀ x0, (x0 = a ∨ x0 ∈ s.ancs a) → s.org x0 = none →
      Survives s s.F.tail x0
  | 0, _, h, _, _, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, a, ha, hs, x0, hx0, hx0o => by
    rcases hx0 with rfl | hx0
    · exact hs
    have hA : a < s.A.length := by
      unfold Survives OptP at hs; split at hs
      · exact lt_of_getElem? ‹_›
      · exact hs.elim
    have horg : s.org a ≠ none := fun e => by rw [S3.ancs, chain_none e] at hx0; simp at hx0
    cases hz : firstSurv s s.F.tail (s.ancs a) with
    | none => exact absurd hz (h3 a (List.mem_range.2 hA) hs horg)
    | some z =>
      obtain ⟨hz1, hzs⟩ := firstSurv_some hz
      rcases ancs_root_after (a + 1) a (Nat.lt_succ_self a) z x0 hz1 hx0 hx0o with rfl | hx'
      · exact hzs
      · exact exit_root_survives h3 n z (by have := chain_lt hz1; omega) hzs x0 (.inr hx') hx0o

/-- Usability after the exit is usability with the popped stack (§40, §73). -/
theorem exit_usable_iff {q : Nat} :
    (exitEff s).Usable q ↔ ({ s with F := s.F.tail } : S3).Usable q :=
  S3.Usable.congr (s := ({ s with F := s.F.tail } : S3)) (s' := exitEff s) rfl rfl rfl

/-- A place usable with the popped stack was usable before the exit (§40, §73). -/
theorem usable_of_tail {q : Nat} (h : ({ s with F := s.F.tail } : S3).Usable q) : s.Usable q :=
  S3.Usable.mono (s := s) (s' := ({ s with F := s.F.tail } : S3)) rfl
    (fun _ hg => List.mem_of_mem_tail hg) (fun _ h => h) h

/-- Conservation along an origin chain (§51): a derived authority has a mode not exceeding, and a
footprint within, those of every ancestor. -/
theorem i2_chain (h2 : I2 s) :
    ∀ n b, b < n → ∀ (y : Authority) z, s.A[b]? = some y → z ∈ s.ancs b →
      ∃ x : Authority, s.A[z]? = some x ∧ y.mode.le x.mode ∧ ∀ p ∈ y.footprint, p ∈ x.footprint
  | 0, _, h, _, _, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, b, hb, y, z, hy, hz => by
    cases ho : y.origin with
    | none =>
      have : s.org b = none := by simp [S3.org, hy, ho]
      rw [S3.ancs, chain_none this] at hz; simp at hz
    | some o =>
      have hob : s.org b = some o := by simp [S3.org, hy, ho]
      obtain ⟨hlt, he⟩ : o < b ∧ s.ancs b = o :: s.ancs o := by
        rcases ancs_step hob with h | he
        · exact h
        · rw [he] at hz; simp at hz
      rw [he] at hz
      obtain ⟨x, hx, hm, hh⟩ := h2 b y o hy ho
      rcases List.mem_cons.1 hz with rfl | hz
      · exact ⟨x, hx, hm, hh⟩
      · obtain ⟨x', hx', hm', hh'⟩ := i2_chain h2 n o (by omega) x z hx hz
        exact ⟨x', hx', Mode.le_trans hm hm', fun p hp => hh' p (hh p hp)⟩

/-! ## `exitFrame` preserves `WF3` (§49, §73) -/

/-- `exitFrame` preserves `RootChain` (§49.6, §73.4): reanchoring keeps the root of every chain. -/
theorem exit_rootChain (hc : RootChain s) (h3 : OriginsSurvive s) : RootChain (exitEff s) := by
  intro a y l ha hl hleaf
  obtain ⟨y₀, hy₀, rfl⟩ := exit_get ha
  rw [(exitG_same s s.F.tail a y₀).2.1] at hl
  obtain ⟨x0, z, r, hx0, hz, hzo, hr, hlr, hfz⟩ := hc a y₀ l hy₀ hl hleaf
  have hx0o : s.org x0 = none := by simp [S3.org, hz, hzo]
  refine ⟨x0, exitG s s.F.tail x0 z, r, ?_, by rw [exit_A_get, hz]; rfl, ?_, hr, hlr,
    fun l' => by rw [(exitG_same s s.F.tail x0 z).2.1]; exact hfz l'⟩
  · rcases hx0 with rfl | hx0
    · exact .inl rfl
    · exact .inr (exit_root_kept h3 (a + 1) a (Nat.lt_succ_self a) x0 hx0 hx0o)
  · rcases exitG_origin (s := s) (F₀ := s.F.tail) (a := x0) (y := z) with e | ⟨-, hn, -⟩
    · rw [e]; exact hzo
    · exact absurd hzo hn

/-- `exitFrame` preserves `RootHeld` (§49.7, §73): the root authority of a root place still
usable is held by the live owner of that place, so it survives unchanged. -/
theorem exit_rootHeld (h : RootHeld s) : RootHeld (exitEff s) := by
  intro r hrp hur
  have hu' : ({ s with F := s.F.tail } : S3).Usable r := exit_usable_iff.1 hur
  obtain ⟨i, z, pr, hz, za, zo, zm, hpr, hzh, hzf⟩ := h r hrp (usable_of_tail hu')
  have hlive : HolderLive { s with F := s.F.tail } z.holder := by
    rw [hzh]; exact usable_owner_live hu' hpr
  have hsv : Survives s s.F.tail i := by unfold Survives; rw [hz]; exact ⟨za, hlive⟩
  refine ⟨i, z, pr, ?_, za, zo, zm, hpr, hzh, hzf⟩
  rw [exit_A_get, hz]; unfold exitG; simp [hsv, zo]

/-- `exitFrame` preserves `WF3` (§49, §73): the caller survives and the stack shrinks; places
are unchanged; reanchored origins are earlier ancestors; active authorities survive, so their
holders are live. -/
theorem exit_wf (hwf : WF3 s) (hne : s.F.tail ≠ []) (h3 : OriginsSurvive s) :
    WF3 (exitEff s) := by
  refine ⟨⟨hne, List.Nodup.sublist (List.tail_sublist _) hwf.frames.2.1,
    fun g hg => hwf.frames.2.2 g (List.mem_of_mem_tail hg)⟩, hwf.places,
    ⟨hwf.owners.1, hwf.owners.2.1, fun q hq => hq.frameOf⟩, ?_, ?_,
    exit_rootChain hwf.rootChain h3, exit_rootHeld hwf.rootHeld, ?_⟩
  · intro a x hx l hl
    obtain ⟨x₀, hx₀, rfl⟩ := exit_get hx
    exact hwf.footprints a x₀ hx₀ l ((exitG_same s s.F.tail a x₀).2.1 ▸ hl)
  · intro b y a hb ho
    obtain ⟨y₀, hy₀, rfl⟩ := exit_get hb
    rcases exitG_origin (s := s) (F₀ := s.F.tail) (a := b) (y := y₀) with e' | ⟨-, -, e'⟩
    · exact hwf.origins b y₀ a hy₀ (e' ▸ ho)
    · rw [e'] at ho; exact chain_lt (firstSurv_some ho).1
  · intro a y hy ya
    obtain ⟨y₀, hy₀, rfl⟩ := exit_get hy
    have hs := exitG_active ya
    rw [(exitG_same s s.F.tail a y₀).2.2,
      HolderLive.congr (s := ({ s with F := s.F.tail } : S3)) (s' := exitEff s) rfl rfl rfl]
    unfold Survives at hs; rw [hy₀] at hs; exact hs.2

/-- `exitFrame` preserves `RootHeldConv` (§40, §49.7, §73): an authority without origin after the
exit had none before, and keeps its footprint and holder. -/
theorem exit_rootHeldConv (hc : RootHeldConv s) (h3 : OriginsSurvive s) :
    RootHeldConv (exitEff s) :=
  hc.transport rfl fun x z' hx ho => by
    obtain ⟨z, hz, rfl⟩ := exit_get hx
    refine ⟨z, hz, ?_, (exitG_same s s.F.tail x z).2.1, (exitG_same s s.F.tail x z).2.2⟩
    rcases exitG_origin (s := s) (F₀ := s.F.tail) (a := x) (y := z) with e | ⟨hsv, hn, e⟩
    · rw [← e]; exact ho
    · rw [e] at ho
      exact absurd ho (h3 x (List.mem_range.2 (lt_of_getElem? hz)) hsv (by simp [S3.org, hz, hn]))

/-! ## `exitFrame` preserves `Inv3` (§50–§54, §57, §73) -/

/-- `exitFrame` preserves `I1`–`I4` (§50–§53, §73): surviving ancestors stay ancestors, a
reanchored origin is an ancestor, and every anchor of a place still usable is replaced by a
surviving authority. -/
theorem exit_inv3base (hinv : Inv3base s)
    (hR1 : ∀ q ∈ List.range s.P.length, ({ s with F := s.F.tail } : S3).Usable q →
      ∀ x ∈ s.D q, firstSurv s s.F.tail (x :: s.ancs x) ≠ none) :
    Inv3base (exitEff s) := by
  obtain ⟨i1, i2, -, -⟩ := hinv
  have lift : ∀ {a x₁}, s.A[a]? = some x₁ → (exitEff s).A[a]? = some (exitG s s.F.tail a x₁) :=
    fun h => by rw [exit_A_get, h]; rfl
  refine ⟨fun a b x y p hab ha hb xa ya xp yp hnab hnba => ?_,
    fun b y a hb ho => ?_, fun q hq x hx => ?_, i4_always _⟩
  · obtain ⟨x₀, hx₀, rfl⟩ := exit_get ha; obtain ⟨y₀, hy₀, rfl⟩ := exit_get hb
    have sa := exitG_active xa; have sb := exitG_active ya
    rw [(exitG_same s s.F.tail a x₀).1, (exitG_same s s.F.tail b y₀).1]
    refine i1 a b x₀ y₀ p hab hx₀ hy₀ (exitG_active' hx₀ xa) (exitG_active' hy₀ ya)
      ((exitG_same s s.F.tail a x₀).2.1 ▸ xp) ((exitG_same s s.F.tail b y₀).2.1 ▸ yp)
      (fun hm => hnab ?_) (fun hm => hnba ?_)
    · exact exit_ancs_keep (b + 1) b (Nat.lt_succ_self b) a hm sa
    · exact exit_ancs_keep (a + 1) a (Nat.lt_succ_self a) b hm sb
  · obtain ⟨y₀, hy₀, rfl⟩ := exit_get hb
    obtain ⟨ym, yf, -⟩ := exitG_same s s.F.tail b y₀
    rcases exitG_origin (s := s) (F₀ := s.F.tail) (a := b) (y := y₀) with e' | ⟨-, -, e'⟩
    · obtain ⟨x₁, hx₁, hm, hh⟩ := i2 b y₀ a hy₀ (e' ▸ ho)
      obtain ⟨xm, xf, -⟩ := exitG_same s s.F.tail a x₁
      exact ⟨_, lift hx₁, by rw [ym, xm]; exact hm, fun p hp => by
        rw [xf]; exact hh p (yf ▸ hp)⟩
    · rw [e'] at ho
      obtain ⟨x₁, hx₁, hm, hh⟩ := i2_chain i2 (b + 1) b (Nat.lt_succ_self b) y₀ a hy₀
        (firstSurv_some ho).1
      obtain ⟨xm, xf, -⟩ := exitG_same s s.F.tail a x₁
      exact ⟨_, lift hx₁, by rw [ym, xm]; exact hm, fun p hp => by
        rw [xf]; exact hh p (yf ▸ hp)⟩
  · have hq₁ : ({ s with F := s.F.tail } : S3).Usable q := exit_usable_iff.1 hq
    simp only [exitEff, List.mem_map] at hx
    obtain ⟨x₀, hx₀, rfl⟩ := hx
    have hne' := hR1 q (List.mem_range.2 (usable_of_tail hq₁).lt) hq₁ x₀ hx₀
    cases hz : firstSurv s s.F.tail (x₀ :: s.ancs x₀) with
    | none => exact absurd hz hne'
    | some z =>
      simp only [Option.getD_some]
      obtain ⟨-, hzs⟩ := firstSurv_some hz
      have hzA : ∃ y, s.A[z]? = some y := by
        unfold Survives at hzs
        cases hy : s.A[z]? with
        | none => rw [hy] at hzs; exact hzs.elim
        | some y => exact ⟨y, rfl⟩
      obtain ⟨y, hy⟩ := hzA
      exact ⟨_, lift hy, exitG_surv hy hzs⟩

/-- `exitFrame` preserves `AnchorOrder` (§44, §73.5): an anchor is replaced by a surviving
authority of its chain, whose effective anchor is the root of the original chain; frames of
places are unchanged and the exited frame is no ancestor of a surviving one. -/
theorem exit_anchorOrder (hwf : WF3 s) (hao : AnchorOrder s)
    (hR1 : ∀ q ∈ List.range s.P.length, ({ s with F := s.F.tail } : S3).Usable q →
      ∀ x ∈ s.D q, firstSurv s s.F.tail (x :: s.ancs x) ≠ none)
    (h3 : OriginsSurvive s) : AnchorOrder (exitEff s) := by
  obtain ⟨f, hF⟩ : ∃ f, s.F = f :: s.F.tail := by
    cases h : s.F with
    | nil => exact absurd h hwf.frames.1
    | cons f F₀ => exact ⟨f, rfl⟩
  have hnd := (List.nodup_cons.1 (hF ▸ hwf.frames.2.1)).1
  intro q hq x' hx'
  have hq₁ : ({ s with F := s.F.tail } : S3).Usable q := exit_usable_iff.1 hq
  have hq₀ : s.Usable q := usable_of_tail hq₁
  simp only [exitEff, List.mem_map] at hx'
  obtain ⟨x, hx, rfl⟩ := hx'
  obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.1 (hR1 q (List.mem_range.2 hq₀.lt) hq₁ x hx)
  rw [hz]; simp only [Option.getD_some]
  have hok := hao q hq₀ x hx
  obtain ⟨r, hr, hro⟩ := reaches_root hwf (x + 1) x (Nat.lt_succ_self x)
  have hex : s.effAnchor x = r := effAnchor_eq (x + 1) x (Nat.lt_succ_self x) r hr hro
  have hzx : z = x ∨ z ∈ s.ancs x := List.mem_cons.1 (firstSurv_some hz).1
  have hrz : r = z ∨ r ∈ s.ancs z := by
    rcases hzx with rfl | hzx
    · exact hr
    · rcases hr with rfl | hr
      · rw [S3.ancs, chain_none hro] at hzx; simp at hzx
      · exact ancs_root_after (x + 1) x (Nat.lt_succ_self x) z r hzx hr hro
  obtain ⟨y, hy⟩ := effAnchorOK_get hok
  rw [hex] at hy
  have hyo : y.origin = none := by simpa [S3.org, hy] using hro
  have hro' : (exitEff s).org r = none := by
    simp only [S3.org, exit_A_get, hy, Option.map_some, Option.bind_some]
    rcases exitG_origin (s := s) (F₀ := s.F.tail) (a := r) (y := y) with e' | ⟨-, hn, -⟩
    · rw [e']; exact hyo
    · exact absurd hyo hn
  have hrz' : r = z ∨ r ∈ (exitEff s).ancs z := hrz.imp id fun hh =>
    exit_root_kept h3 (z + 1) z (Nat.lt_succ_self z) r hh hro
  have hez : (exitEff s).effAnchor z = r :=
    effAnchor_eq (z + 1) z (Nat.lt_succ_self z) r hrz' hro'
  refine (effAnchorOK_of_same (s := s) (s' := exitEff s) (x := x) (x' := z)
    (z' := exitG s s.F.tail r y) (by rw [hex]; exact hy) (by rw [hez, exit_A_get, hy]; rfl)
    (by rw [(exitG_same s s.F.tail r y).2.2]
        exact S3.hframe_congr (s := s) (s' := exitEff s) rfl _)
    ?_ (S3.pframe_congr (s := s) (s' := exitEff s) rfl q)).2 hok
  intro g f₁ hf
  obtain ⟨f', hf', hfF⟩ := hq₁.frameOf
  rw [pframe_iff.2 ((FrameOf.congr (s := s) (s' := ({ s with F := s.F.tail } : S3)) rfl).1 hf')]
    at hf
  rw [← Option.some.inj hf]
  show ancestor s.F.tail g f' ↔ ancestor s.F g f'
  conv => rhs; rw [hF]
  exact (ancestor_push fun e => hnd (by rw [e]; exact hfF)).symm

/-- After an `ok` exit, no active authority covers a leaf of an unusable place (§73, §54):
an active authority survives; the root of its chain survives (§73.4), is active and, by `WF3`,
`I1` and `NoDangling` (`rootHeldConv_active`), is held by the owner of the root place of the
leaf, which is therefore usable after the exit, and so is every place containing the leaf. -/
theorem exit_noDangling (hwf : WF3 s) (h1 : I1 s) (hnd : NoDangling s)
    (h3 : OriginsSurvive s) : NoDangling (exitEff s) := by
  intro j z hz za q hq l hl hlz
  obtain ⟨y₀, hy₀, rfl⟩ := exit_get hz
  have hs := exitG_active za
  rw [(exitG_same s s.F.tail j y₀).2.1] at hlz
  have hq' : ¬ ({ s with F := s.F.tail } : S3).Usable q := fun hu => hq (exit_usable_iff.2 hu)
  by_cases hq₀ : s.Usable q
  · obtain ⟨hlP, hleaf, hlq⟩ := mem_footprint.1 hl
    obtain ⟨x0, z, r, hx0, hz, hzo, hr, hlr, hfz⟩ := hwf.rootChain j y₀ l hy₀ hlz hleaf
    have hx0o : s.org x0 = none := by simp [S3.org, hz, hzo]
    have hs0 := exit_root_survives h3 (j + 1) j (Nat.lt_succ_self j) hs x0 hx0 hx0o
    have hlz0 : l ∈ z.footprint := (hfz l).2 (mem_footprint.2 ⟨hlP, hleaf, hlr⟩)
    unfold Survives at hs0; rw [hz] at hs0
    obtain ⟨zact, hlive⟩ := hs0
    obtain ⟨pr, hpr, hh⟩ := rootHeldConv_active hwf h1 hnd x0 z l r hz zact hzo hlz0 hr hlr
    rw [hh] at hlive
    obtain ⟨pl, pr', hpl, hpr', e1⟩ := hwf.ownerOf hlr
    rw [hpr] at hpr'; cases hpr'
    obtain ⟨pl', pq, hpl', hpq, e2⟩ := hwf.ownerOf hlq
    rw [hpl] at hpl'; cases hpl'
    have hdr : s.dead r = false := by
      rw [← hwf.deadOf hlr, hwf.deadOf hlq]; exact usable_dead hq₀
    have hur : ({ s with F := s.F.tail } : S3).Usable r := usable_of_owner hpr hdr hlive
    exact hq' (S3.Usable.of_same hur hpr hpq (e2.symm.trans e1)
      ((hwf.deadOf hlq).symm.trans (hwf.deadOf hlr)))
  · exact hnd j y₀ hy₀ (exitG_active' hy₀ za) q hq₀ l hl hlz

end Exit

end Frames

/-! ## Preservation of the kernel invariant (§57, §72, §73) -/

/-- `enterFrame` preserves the kernel invariant of §57 (`WF3 ∧ Inv3 ∧ AnchorOrderHeld ∧
NoOrphan`) (§72). -/
theorem enter_preserves {s s' : S3} {ps : List Nat} {ls : LocalShape} (hk : KInv s)
    (h : EnterStep ps ls s (.ok s')) : KInv s' := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  obtain ⟨hwf, ⟨hb, hao, hnd⟩, -, -⟩ := hk
  exact kInv_of (Frames.enter_wf hwf hpre) ⟨Frames.enter_inv3base hwf hb,
    Frames.enter_anchorOrder hwf hao hpre, Frames.enter_noDangling hwf hnd hpre⟩
    hpre.anchorOrderHeld

/-- `enterFrame` preserves the auxiliary `KAux` (`RootHeldConv`, §40, §49.7; §72) from a `KInv`
state. -/
theorem enter_preserves_kAux {s s' : S3} {ps : List Nat} {ls : LocalShape} (hk : KInv s)
    (ha : KAux s) (h : EnterStep ps ls s (.ok s')) : KAux s' := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  exact Frames.enter_rootHeldConv hk.1 hpre ha

/-- `exitFrame` preserves the kernel invariant of §57 (`WF3 ∧ Inv3 ∧ AnchorOrderHeld ∧
NoOrphan`) (§73). -/
theorem exit_preserves {k : K} {s s' : S3} (hk : KInv s)
    (h : ExitStep k s (.ok s')) : KInv s' := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  obtain ⟨hwf, ⟨hb, hao, hnd⟩, -, -⟩ := hk
  exact kInv_of (Frames.exit_wf hwf hpre.hasCaller hpre.origins)
    ⟨Frames.exit_inv3base hb hpre.anchors,
     Frames.exit_anchorOrder hwf hao hpre.anchors hpre.origins,
     Frames.exit_noDangling hwf hb.1 hnd hpre.origins⟩ hpre.anchorOrderHeld

/-- `exitFrame` preserves the auxiliary `KAux` (`RootHeldConv`, §40, §49.7; §73). -/
theorem exit_preserves_kAux {k : K} {s s' : S3} (ha : KAux s)
    (h : ExitStep k s (.ok s')) : KAux s' := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  exact Frames.exit_rootHeldConv ha hpre.origins

/-! ## Determinism (§58, §72, §73) -/

/-- `enterFrame` has one outcome (§58, §72). -/
theorem enterStep_det {s : S3} {ps : List Nat} {ls : LocalShape} {o₁ o₂ : Outcome3 S3}
    (h₁ : EnterStep ps ls s o₁) (h₂ : EnterStep ps ls s o₂) : o₁ = o₂ :=
  Guarded.det h₁ h₂

/-- `exitFrame` has one outcome (§58, §73). -/
theorem exitStep_det {k : K} {s : S3} {o₁ o₂ : Outcome3 S3} (h₁ : ExitStep k s o₁)
    (h₂ : ExitStep k s o₂) : o₁ = o₂ :=
  Guarded.det h₁ h₂

/-! ## Frames (§39) -/

/-- Neither step changes the bottom of the stack (§39: the base frame never exits): `exitFrame`
keeps a nonempty stack with the same last frame. -/
theorem exit_keeps_base {k : K} {s s' : S3} (h : ExitStep k s (.ok s')) :
    s'.F ≠ [] ∧ s'.F.getLast? = s.F.getLast? := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  refine ⟨hpre.hasCaller, ?_⟩
  show s.F.tail.getLast? = s.F.getLast?
  cases hF : s.F with
  | nil => rfl
  | cons f F₀ => exact (getLast?_cons_ne (by simpa [hF] using hpre.hasCaller)).symm

/-- Neither step changes the bottom of the stack (§39: the base frame never exits):
`enterFrame` pushes the new frame on top. -/
theorem enter_keeps_base {s s' : S3} {ps : List Nat} {ls : LocalShape}
    (h : EnterStep ps ls s (.ok s')) : s'.F.getLast? = s.F.getLast? := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  exact getLast?_cons_ne hpre.callerLive

/-- An exited frame leaves the stack and is the terminal owner of no usable place (§39, §73 `ok`
effect, first item). -/
theorem exitFrame_frame_gone {k : K} {s s' : S3} (hw : WF3 s) (h : ExitStep k s (.ok s')) :
    s.top ∉ s'.F ∧ ∀ q, s'.Usable q → ¬ FrameOf s' q s.top := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
  obtain ⟨f, F₀, hF⟩ : ∃ f F₀, s.F = f :: F₀ := by
    cases h : s.F with
    | nil => exact absurd h hw.frames.1
    | cons f F₀ => exact ⟨f, F₀, rfl⟩
  have hnd := (List.nodup_cons.1 (hF ▸ hw.frames.2.1)).1
  have htop : s.top = f := by simp [S3.top, hF]
  have hF' : (exitEff s).F = F₀ := by simp [exitEff, hF]
  rw [htop, hF']
  refine ⟨hnd, fun q hq hfq => ?_⟩
  obtain ⟨g, hg, hgF⟩ := hq.frameOf
  have e := FrameOf.det hfq hg
  rw [hF', ← e] at hgF
  exact hnd hgF

/-! ## Release at the exit (§73 `ok` effect, §39, §45) -/

/-- `exitFrame_releases_all` (§73 `ok` effect, second item; §39; §45): after an `ok` exit, an
authority held by the exited frame or by a place that is no longer usable is released, with its
holder unchanged (it is not returned to the caller); every active authority has a live holder,
other than the exited frame. -/
theorem exitFrame_releases_all {k : K} {s s' : S3} (hw : WF3 s) (h : ExitStep k s (.ok s')) :
    (∀ (j : Nat) (y : Authority), s.A[j]? = some y →
      (y.holder = .frame s.top ∨ ∃ p, y.holder = .place p ∧ ¬ s'.Usable p) →
      ∃ y', s'.A[j]? = some y' ∧ y'.active = false ∧ y'.holder = y.holder) ∧
    (∀ (j : Nat) (y : Authority), s'.A[j]? = some y → y.active = true →
      HolderLive s' y.holder ∧ y.holder ≠ .frame s.top) := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
  obtain ⟨f, F₀, hF⟩ : ∃ f F₀, s.F = f :: F₀ := by
    cases h : s.F with
    | nil => exact absurd h hw.frames.1
    | cons f F₀ => exact ⟨f, F₀, rfl⟩
  have hnd := (List.nodup_cons.1 (hF ▸ hw.frames.2.1)).1
  have htop : s.top = f := by simp [S3.top, hF]
  have hlive : ∀ hd, HolderLive (exitEff s) hd ↔ HolderLive ({ s with F := s.F.tail } : S3) hd :=
    HolderLive.congr (s := ({ s with F := s.F.tail } : S3)) (s' := exitEff s) rfl rfl rfl
  have hnot : ¬ HolderLive ({ s with F := s.F.tail } : S3) (.frame f) := by
    show f ∉ s.F.tail; rw [hF]; exact hnd
  refine ⟨fun j y hy hh => ?_, fun j y hy ya => ?_⟩
  · have hns : ¬ Survives s s.F.tail j := by
      unfold Survives; rw [hy]; rintro ⟨-, hl⟩
      rcases hh with e | ⟨p, e, hp⟩
      · rw [e, htop] at hl; exact hnot hl
      · rw [e] at hl; exact hp ((hlive (.place p)).2 hl)
    refine ⟨_, by rw [Frames.exit_A_get, hy]; rfl, by simp [exitG, hns], by simp [exitG, hns]⟩
  · obtain ⟨y₀, hy₀, rfl⟩ := Frames.exit_get hy
    have hs := Frames.exitG_active ya
    unfold Survives at hs; rw [hy₀] at hs
    have hl : HolderLive ({ s with F := s.F.tail } : S3) y₀.holder := hs.2
    rw [(Frames.exitG_same s s.F.tail j y₀).2.2]
    refine ⟨(hlive _).2 hl, fun e => ?_⟩
    rw [e, htop] at hl; exact hnot hl

/-! ## No dangling authority after the exit (§73, §54) -/

/-- `exitFrame_no_dangling` (§73, §54): from a state satisfying `WF3` (§49), `I1` (§50) and
`NoDangling` (§54), clauses of §57, after an `ok` exit no active authority covers a leaf of a
place that is not usable, in particular of a local of the exited frame or of storage dying with
it. -/
theorem exitFrame_no_dangling {k : K} {s s' : S3} (hw : WF3 s) (h1 : I1 s) (hnd : NoDangling s)
    (h : ExitStep k s (.ok s')) :
    ∀ q, ¬ s'.Usable q → ∀ (j : Nat) (y : Authority), s'.A[j]? = some y → y.active = true →
      ∀ l ∈ footprint s'.P q, l ∉ y.footprint := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  intro q hq j y hy ya
  exact Frames.exit_noDangling hw h1 hnd hpre.origins j y hy ya q hq

/-! ## Reanchoring at the exit (§73.4, §73 `ok` effect, §45) -/

/-- Reanchoring (§73.4; §73 `ok` effect, third and fourth items; §45): after an `ok` exit, a
surviving authority stays active with its own mode, footprint and holder; it keeps no origin if
it had none; otherwise its origin becomes the first surviving active origin of its chain: no
earlier ancestor survives, and that origin is active and held, after the exit, by a frame of the
stack or by a usable place. -/
theorem exitFrame_reanchors {k : K} {s s' : S3} (h : ExitStep k s (.ok s')) {a : Nat}
    {y : Authority} (hy : s.A[a]? = some y) (hs : Survives s s.F.tail a) :
    ∃ y', s'.A[a]? = some y' ∧ y'.active = true ∧ y'.mode = y.mode ∧
      y'.footprint = y.footprint ∧ y'.holder = y.holder ∧
      (y.origin = none → y'.origin = none) ∧
      (y.origin ≠ none → ∃ (z : Nat) (pre post : List Nat) (yz : Authority),
        y'.origin = some z ∧ s.ancs a = pre ++ z :: post ∧
        (∀ w ∈ pre, ¬ Survives s s.F.tail w) ∧
        s'.A[z]? = some yz ∧ yz.active = true ∧ HolderLive s' yz.holder) := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  have hlive : ∀ hd, HolderLive (exitEff s) hd ↔ HolderLive ({ s with F := s.F.tail } : S3) hd :=
    HolderLive.congr (s := ({ s with F := s.F.tail } : S3)) (s' := exitEff s) rfl rfl rfl
  obtain ⟨ym, yf, yh⟩ := Frames.exitG_same s s.F.tail a y
  refine ⟨_, by rw [Frames.exit_A_get, hy]; rfl, Frames.exitG_surv hy hs, ym, yf, yh,
    fun ho => by simp [exitG, hs, ho], fun ho => ?_⟩
  have horg : s.org a ≠ none := by simpa [S3.org, hy] using ho
  obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.1
    (hpre.origins a (List.mem_range.2 (lt_of_getElem? hy)) hs horg)
  obtain ⟨-, pre, post, hl, hpre'⟩ := List.find?_eq_some_iff_append.1 hz
  obtain ⟨-, hzs⟩ := Frames.firstSurv_some hz
  have hzs' := hzs
  unfold Survives OptP at hzs'
  split at hzs'
  · rename_i yz hyz
    refine ⟨z, pre, post, _, ?_, hl, fun w hw => by simpa using hpre' w hw,
      by rw [Frames.exit_A_get, hyz]; rfl, Frames.exitG_surv hyz hzs, ?_⟩
    · obtain ⟨o, ho'⟩ := Option.ne_none_iff_exists'.1 ho
      simp [exitG, hs, ho', hz]
    · rw [(Frames.exitG_same s s.F.tail z yz).2.2]; exact (hlive _).2 hzs'.2
  · exact hzs'.elim

/-- Reanchoring of anchors (§73 `ok` effect, third item; §73.5): after an `ok` exit, every anchor
of a usable place is replaced by the first surviving authority among itself and its origins,
which is an anchor of the place after the exit and is active. -/
theorem exitFrame_reanchors_anchors {k : K} {s s' : S3} (h : ExitStep k s (.ok s')) :
    ∀ q, s'.Usable q → ∀ x ∈ s.D q, ∃ z, firstSurv s s.F.tail (x :: s.ancs x) = some z ∧
      (z = x ∨ z ∈ s.ancs x) ∧ z ∈ s'.D q ∧ s'.Active z := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  intro q hq x hx
  have hq₁ : ({ s with F := s.F.tail } : S3).Usable q := Frames.exit_usable_iff.1 hq
  have hne := hpre.anchors q (List.mem_range.2 (Frames.usable_of_tail hq₁).lt) hq₁ x hx
  obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.1 hne
  obtain ⟨hzm, hzs⟩ := Frames.firstSurv_some hz
  have hmem : z ∈ (exitEff s).D q := List.mem_map.2 ⟨x, hx, by simp [hz]⟩
  refine ⟨z, hz, List.mem_cons.1 hzm, hmem, ?_⟩
  have hzs' := hzs
  unfold Survives OptP at hzs'
  split at hzs'
  · rename_i yz hyz
    exact ⟨_, by rw [Frames.exit_A_get, hyz]; rfl, Frames.exitG_surv hyz hzs⟩
  · exact hzs'.elim

/-! ## Parameters (§45, §72) -/

/-- The caller yields its parameters (§45; §72 `ok` effect): after an `ok` entry the new frame is
the current frame, it holds every parameter, the other existing authorities are unchanged, and
every new authority is the root authority (no origin) of a root local, held by the new frame, so
the caller keeps no copy of a parameter. -/
theorem enter_yields {s s' : S3} {ps : List Nat} {ls : LocalShape} (hw : WF3 s)
    (h : EnterStep ps ls s (.ok s')) :
    s'.top = s.nF ∧ s.nF ∉ s.F ∧ s'.F = s.nF :: s.F ∧
    (∀ j < s.A.length, s'.A[j]? =
      (s.A[j]?).map fun y => if j ∈ ps then { y with holder := .frame s'.top } else y) ∧
    (∀ (j : Nat) (y : Authority), s.A.length ≤ j → s'.A[j]? = some y →
      y.origin = none ∧ y.holder = .frame s'.top) := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
  have htop : (enterEff s ps ls).top = s.nF := rfl
  refine ⟨htop, ?_, rfl, fun j hj => by rw [htop]; exact Frames.enter_lt hj,
    fun j y hj hy => ?_⟩
  · exact fun hm => Nat.lt_irrefl _ (hw.frames.2.2 _ hm)
  · rcases Frames.enter_get hy with ⟨hj', -⟩ | ⟨-, i, -, rfl⟩
    · omega
    · exact ⟨rfl, rfl⟩

/-- An active `Modify` authority takes every effective mode, on each of its leaves, away from its
direct origin (§43 case 3; last paragraph of §72: while a `Modify` parameter remains active, its
direct origin remains subject to effective-mode restrictions). -/
theorem param_origin_restricted {s : S3} (hw : WF3 s) {p o l : Nat} {y : Authority}
    (hp : s.A[p]? = some y) (ya : y.active = true) (hm : y.mode = .modify)
    (ho : y.origin = some o) (hl : l ∈ y.footprint) : effective s o l = none := by
  have hop : s.org p = some o := by simp [S3.org, hp, ho]
  have hoa : o ∈ s.ancs p := by
    rw [S3.ancs, chain_cons hop (hw.origins p y o hp ho)]; exact List.mem_cons_self ..
  have hd : Mode.modify ∈ descModes s o l := mem_descModes.2 ⟨p, y, hp, ya, hl, hoa, hm⟩
  unfold effective
  split
  · split
    · unfold effOf
      have hne : descModes s o l ≠ [] := fun e => by rw [e] at hd; cases hd
      simp [hne, hd]
    · rfl
  · rfl

/-- While an active `Modify` authority `p` covers a leaf, every authority with a present
effective mode on that leaf is `p` or one of its descendants (§50 `I1`, §43; last paragraph of
§72 for a `Modify` parameter). -/
theorem call_params_effective_protected {s : S3} (h1 : I1 s) {p b l : Nat} {y : Authority}
    (hp : s.A[p]? = some y) (ya : y.active = true) (hm : y.mode = .modify) (hl : l ∈ y.footprint)
    (hb : effective s b l ≠ none) : b = p ∨ p ∈ s.ancs b := by
  by_cases e : b = p
  · exact .inl e
  by_cases hpb : p ∈ s.ancs b
  · exact .inr hpb
  cases he : effective s b l with
  | none => exact absurd he hb
  | some mb =>
    obtain ⟨x, hx, xa, xl, ex⟩ := effective_some he
    by_cases hbp : b ∈ s.ancs p
    · have hd : Mode.modify ∈ descModes s b l := mem_descModes.2 ⟨p, y, hp, ya, hl, hbp, hm⟩
      rcases effOf_cases ex with ⟨h0, -⟩ | ⟨-, hn, -⟩
      · simp [h0] at hd
      · exact absurd hd hn
    · have := (h1 b p x y l e hx hp xa ya xl hl hbp hpb).2
      rw [hm] at this; cases this

/-- `enter_params_protected` (§72.3; last paragraph of §72): after an `ok` entry, the direct
origin of each `Modify` parameter is exercisable in no mode, and on each leaf of a `Modify`
parameter every authority with a present effective mode is the parameter or one of its
descendants, so its direct origin has no effective mode there. -/
theorem enter_params_protected {s s' : S3} {ps : List Nat} {ls : LocalShape} (hwf : WF3 s)
    (h1 : I1 s) (h : EnterStep ps ls s (.ok s')) :
    (∀ p ∈ ps, ParamOriginHidden s' p) ∧
      ∀ p ∈ ps, ∀ y : Authority, s'.A[p]? = some y → y.mode = .modify → ∀ l ∈ y.footprint,
        (∀ b, effective s' b l ≠ none → b = p ∨ p ∈ s'.ancs b) ∧
        ∀ o, y.origin = some o → effective s' o l = none := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  have hi1 := Frames.enter_i1 hwf h1 (ps := ps) (ls := ls)
  have hwf' := Frames.enter_wf hwf hpre
  refine ⟨hpre.originHidden, fun p hp y hy hm l hl => ?_⟩
  have ya : y.active = true := by
    have h2 := hpre.params p hp
    unfold OptP at h2; split at h2
    · rename_i y₀ hy₀
      rw [Frames.enter_lt (lt_of_getElem? hy₀), hy₀] at hy
      simp only [Option.map_some, Option.some.injEq] at hy
      subst hy; split <;> exact h2.1
    · exact h2.elim
  exact ⟨fun b hb => call_params_effective_protected hi1 hy ya hm hl hb,
    fun o ho => param_origin_restricted hwf' hy ya hm ho hl⟩

/-! ## Witness: reanchoring to an origin held by a place (§73.4) -/

namespace Frames.Witness

open Examples

/-- After `derive(0, [0], Modify)` (authority 3) and `store(3, 1)` (§60, §65): authority 3 is
held by static place 1. -/
def w2 : S3 := storeEff s1 3 1
/-- After `derive(3, [0], Modify)` (§60): authority 4, held by frame 0. -/
def w3 : S3 := deriveEff w2 3 [0] .modify
/-- After `derive(2, [2], Modify)` (§60): authority 5, held by frame 0. -/
def w4 : S3 := deriveEff w3 2 [2] .modify
/-- After `enterFrame([4, 5], [])` (§72): frame 1 holds parameters 4 and 5. -/
def w5 : S3 := enterEff w4 [4, 5] []
/-- After `derive(4, [0], Modify)` (§60): authority 6, held by frame 1. -/
def w6 : S3 := deriveEff w5 4 [0] .modify
/-- After `store(6, 2)` (§65): authority 6 is held by static place 2, owned by frame 0. -/
def w7 : S3 := storeEff w6 6 2

/-- The state `w7` is reachable from `S3.init st` (§57). -/
theorem w7_reachable : Reachable K0 st w7 :=
  .step (.step (.step (.step (.step (.step (.step .init
    (.derive (.ok (by decide : DerivePre s0 0 [0] .modify))))
    (.store (.ok (by decide : StorePre s1 3 1))))
    (.derive (.ok (by decide : DerivePre w2 3 [0] .modify))))
    (.derive (.ok (by decide : DerivePre w3 2 [2] .modify))))
    (.enter (.ok (by decide : EnterPre w4 [4, 5] []))))
    (.derive (.ok (by decide : DerivePre w5 4 [0] .modify))))
    (.store (.ok (by decide : StorePre w6 6 2)))

/-- Witness for §73.4 (a surviving origin is not skipped because it is held by a place): from
the reachable state `w7`, `exitFrame` is `ok`; authority 6 (held by place 2) survives; its
direct origin 4, held by the exiting frame, does not survive; it is reanchored to authority 3,
the next origin of its chain, which is active and held by the usable place 1, rather than to the
root authority 0. -/
theorem exit_reanchors_to_place_witness :
    Reachable K0 st w7 ∧ ExitStep K0 w7 (.ok (exitEff w7)) ∧
      w7.org 6 = some 4 ∧ w7.org 4 = some 3 ∧ w7.org 3 = some 0 ∧
      Survives w7 w7.F.tail 6 ∧ ¬ Survives w7 w7.F.tail 4 ∧
      (exitEff w7).org 6 = some 3 ∧
      OptP ((exitEff w7).A[3]?) (fun z => z.active = true ∧ z.holder = .place 1) False ∧
      (exitEff w7).Usable 1 :=
  ⟨w7_reachable, .ok (by decide), by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩

end Frames.Witness


end Ern.MemoryModel.Access
