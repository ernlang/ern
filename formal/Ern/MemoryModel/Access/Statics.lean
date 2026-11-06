import Ern.MemoryModel.Access.Invariants

/-!
# Access kernel: conforming statics declarations and their numbering

`StaticsConf` is the conformance of a statics declaration to §47 and §49 with no order between
identifiers. `StaticsOK` (`Ern.MemoryModel.Access.Invariants`) asks parents and owning statics to
be earlier statics; by §49 (last paragraph) this ordering only represents well-formedness. Every
conforming declaration has a consistent renumbering satisfying `StaticsOK`
(`StaticsConf.exists_renumber`), and every declaration satisfying `StaticsOK` conforms
(`StaticsConf.of_staticsOK`).
-/

namespace Ern.MemoryModel.Access

/-! ## Conformance (§40, §47, §49) -/

/-- Structural parent of static `i` (§40): `none` for a root static or an index outside the
declaration. -/
def staticParent (statics : Statics) (i : Nat) : Option Nat := (statics[i]?).bind (·.1.1)

/-- Owning static of static `i` (§40, §47): `none` for a static owned by frame 0 or an index
outside the declaration. -/
def staticOwner (statics : Statics) (i : Nat) : Option Nat := (statics[i]?).bind (·.1.2.1)

/-- Conformance of a statics declaration to §47 and §49, with no order between identifiers
(§49, last paragraph). Owners are frame 0 or a static (§40, §47), parents and owning statics are
declared statics (§49.2, §49.3), composition links are acyclic (§49.2), no static is owned,
directly or transitively, by itself (§47), and every structural part has its parent's owner
(§49.2, §40).

Acyclicity is the irreflexivity of the transitive closure `Relation.TransGen` of the one-step
link (`a`'s parent, resp. owning static, is `b`): `TransGen link i i` holds exactly when a
nonempty chain of links leads from `i` back to `i`, which is what §47 ("owned, directly or
transitively, by itself") and §49.2 (acyclic composition links) exclude. No bound on chain
length is involved. -/
structure StaticsConf (statics : Statics) : Prop where
  /-- §49.2: composition links are valid; every structural parent is a declared static. -/
  parent_lt : ∀ i p, staticParent statics i = some p → p < statics.length
  /-- §49.3, §47: owners are valid; every owning static is a declared static. -/
  owner_lt : ∀ i o, staticOwner statics i = some o → o < statics.length
  /-- §49.2: composition links are acyclic; no static is its own strict structural ancestor. -/
  parent_acyclic : ∀ i, ¬ Relation.TransGen (fun a b => staticParent statics a = some b) i i
  /-- §47: no static is owned, directly or transitively, by itself. -/
  owner_acyclic : ∀ i, ¬ Relation.TransGen (fun a b => staticOwner statics a = some b) i i
  /-- §49.2, §40: every structural part shares its parent's owner. -/
  part_owner : ∀ i p, staticParent statics i = some p →
    staticOwner statics i = staticOwner statics p

/-! ## Renumbering (§49, last paragraph; §63.2) -/

/-- A static's entry with its references, parent and owning static, mapped through `τ`; its
kind and initial state are kept (§49, last paragraph). -/
def mapRefs (τ : Nat → Nat) (e : (Option Nat × Option Nat × Nat) × Bool) :
    (Option Nat × Option Nat × Nat) × Bool :=
  ((e.1.1.map τ, e.1.2.1.map τ, e.1.2.2), e.2)

/-- Renumbering of a declaration by `σ` (§49, last paragraph): new index `i` holds old static
`σ[i]`, its parent and owning static mapped through the inverse `σ.idxOf`. Meant for `σ` a
permutation of `List.range statics.length`. -/
def renumber (σ : List Nat) (statics : Statics) : Statics :=
  σ.map fun j => mapRefs σ.idxOf ((statics[j]?).getD ((none, none, 0), false))

/-- Consistent renumbering (§49, last paragraph; §63.2): the new index `σ.idxOf x` of every old
static `x` holds `x` with its parent and owning static mapped through `σ.idxOf`, and its kind and
initial state; the parts of every place keep their relative order, which is their positional
field order (§63.2; `kids` orders the parts of a place by index). -/
structure ConsistentRenumbering (σ : List Nat) (statics : Statics) : Prop where
  /-- Parents to parents, owning statics to owning statics, same kind and initial state. -/
  entry : ∀ x < statics.length,
    (renumber σ statics)[σ.idxOf x]? = (statics[x]?).map (mapRefs σ.idxOf)
  /-- §63.2: the field order of every place is preserved. -/
  field_order : ∀ x y p, staticParent statics x = some p → staticParent statics y = some p →
    x < y → σ.idxOf x < σ.idxOf y

/-! ## Proof support: chains of a partial link -/

/-- Pigeonhole: a duplicate-free list of numbers below `n` has at most `n` elements. -/
private theorem nodup_length_le : ∀ (n : Nat) (l : List Nat), l.Nodup → (∀ a ∈ l, a < n) →
    l.length ≤ n
  | 0, [], _, _ => Nat.le_refl _
  | 0, a :: _, _, h => absurd (h a (List.mem_cons_self ..)) (Nat.not_lt_zero _)
  | n + 1, l, hd, h => by
    have := nodup_length_le n (l.erase n) (hd.erase n) fun a ha => by
      rw [hd.mem_erase_iff] at ha
      have := h a ha.2
      omega
    rw [List.length_erase] at this
    split at this <;> omega

/-- `k` links `f` from `x`. -/
private def iter (f : Nat → Option Nat) : Nat → Nat → Option Nat
  | 0, x => some x
  | k + 1, x => (iter f k x).bind f

private theorem iter_add (f : Nat → Option Nat) (x i : Nat) : ∀ d,
    iter f (i + d) x = (iter f i x).bind (iter f d)
  | 0 => by
    show iter f i x = _
    cases iter f i x <;> rfl
  | d + 1 => by
    show (iter f (i + d) x).bind f = _
    rw [iter_add f x i d, Option.bind_assoc]
    rfl

private theorem transGen_of_iter {f : Nat → Option Nat} {x : Nat} : ∀ {k y : Nat},
    iter f (k + 1) x = some y → Relation.TransGen (fun a b => f a = some b) x y
  | 0, _, h => .single h
  | k + 1, _, h => by
    obtain ⟨c, hc, hcy⟩ := Option.bind_eq_some_iff.1 h
    exact .tail (transGen_of_iter hc) hcy

/-- An acyclic partial link whose targets are below `n` has chains of fewer than `n` links from
any `x < n`. -/
private theorem iter_bound {f : Nat → Option Nat} {n : Nat}
    (hacyc : ∀ a, ¬ Relation.TransGen (fun a b => f a = some b) a a)
    (hlt : ∀ a b, f a = some b → b < n) {x : Nat} (hx : x < n) {k : Nat}
    (hk : (iter f k x).isSome) : k < n := by
  let g := fun i => (iter f i x).getD 0
  have hsome : ∀ i ≤ k, iter f i x = some (g i) := by
    intro i hi
    have := iter_add f x i (k - i)
    rw [Nat.add_sub_cancel' hi] at this
    cases hc : iter f i x with
    | none => rw [hc] at this; rw [this] at hk; simp at hk
    | some c => simp [g, hc]
  have hlt' : ∀ a ∈ (List.range (k + 1)).map g, a < n := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ha
    have hi' := hsome i (by rw [List.mem_range] at hi; omega)
    cases i with
    | zero => simp only [iter, Option.some.injEq] at hi'; omega
    | succ j =>
      obtain ⟨c, -, hc⟩ := Option.bind_eq_some_iff.1 hi'
      exact hlt c _ hc
  have hnd : ((List.range (k + 1)).map g).Nodup := by
    unfold List.Nodup
    rw [List.pairwise_map]
    refine List.pairwise_lt_range.imp_of_mem fun {i j} hi hj hij heq => ?_
    rw [List.mem_range] at hi hj
    have hj' := iter_add f x i (j - i)
    rw [Nat.add_sub_cancel' (Nat.le_of_lt hij), hsome i (by omega), hsome j (by omega), heq,
      Option.bind_some] at hj'
    obtain ⟨d, hd⟩ : ∃ d, j - i = d + 1 := ⟨j - i - 1, by omega⟩
    rw [hd] at hj'
    exact hacyc _ (transGen_of_iter hj'.symm)
  have := nodup_length_le n _ hnd hlt'
  simp only [List.length_map, List.length_range] at this
  omega

/-- Length of the chain of links `f` from `x`, cut at `k` links. -/
private def chainLen (f : Nat → Option Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, x => match f x with
    | none => 0
    | some y => chainLen f k y + 1

private theorem chainLen_some {f : Nat → Option Nat} {k x y : Nat} (h : f x = some y) :
    chainLen f (k + 1) x = chainLen f k y + 1 := by
  show (match f x with | none => 0 | some y => chainLen f k y + 1) = _
  rw [h]

private theorem chainLen_congr {f : Nat → Option Nat} {x y : Nat} (h : f x = f y) :
    ∀ k, chainLen f k x = chainLen f k y
  | 0 => rfl
  | _ + 1 => by simp only [chainLen, h]

private theorem iter_of_chainLen_ne {f : Nat → Option Nat} : ∀ {k z : Nat},
    chainLen f (k + 1) z ≠ chainLen f k z → (iter f (k + 1) z).isSome
  | 0, z, h => by
    cases hz : f z with
    | none => simp [chainLen, hz] at h
    | some y => simp [iter, hz]
  | k + 1, z, h => by
    cases hz : f z with
    | none => simp [chainLen, hz] at h
    | some y =>
      rw [chainLen_some hz, chainLen_some hz] at h
      have := iter_add f z 1 (k + 1)
      rw [Nat.add_comm 1] at this
      rw [this]
      simp only [iter, Option.bind_some, hz]
      exact iter_of_chainLen_ne (by omega)

/-- Under an acyclic link with targets below `n`, the chain length cut at `n` grows by one along
each link. -/
private theorem chainLen_step {f : Nat → Option Nat} {n : Nat}
    (hacyc : ∀ a, ¬ Relation.TransGen (fun a b => f a = some b) a a)
    (hlt : ∀ a b, f a = some b → b < n) {x y : Nat} (h : f x = some y) :
    chainLen f n x = chainLen f n y + 1 := by
  have hy := hlt x y h
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [chainLen_some h]
  refine congrArg (· + 1) (Classical.byContradiction fun hne => ?_)
  have := iter_bound hacyc hlt hy (iter_of_chainLen_ne (k := m) (fun e => hne e.symm))
  omega

/-! ## Proof support: the order of a conforming declaration -/

/-- Ownership depth of a static. -/
private def odepth (statics : Statics) (x : Nat) : Nat :=
  chainLen (staticOwner statics) statics.length x

/-- Structural depth of a static. -/
private def sdepth (statics : Statics) (x : Nat) : Nat :=
  chainLen (staticParent statics) statics.length x

/-- Lexicographic order on (ownership depth, structural depth, index). -/
private def keyLe (statics : Statics) (a b : Nat) : Bool :=
  decide (odepth statics a < odepth statics b ∨ odepth statics a = odepth statics b ∧
    (sdepth statics a < sdepth statics b ∨ sdepth statics a = sdepth statics b ∧ a ≤ b))

private theorem idxOf_lt_of_key {statics : Statics} {σ : List Nat}
    (hσ : σ.Perm (List.range statics.length)) (hs : σ.Pairwise (fun a b => keyLe statics a b))
    {x y : Nat} (hx : x < statics.length) (hy : y < statics.length)
    (hk : odepth statics x < odepth statics y ∨ odepth statics x = odepth statics y ∧
      (sdepth statics x < sdepth statics y ∨ sdepth statics x = sdepth statics y ∧ x < y)) :
    σ.idxOf x < σ.idxOf y := by
  have hix := List.idxOf_lt_length_of_mem (hσ.mem_iff.2 (List.mem_range.2 hx))
  have hiy := List.idxOf_lt_length_of_mem (hσ.mem_iff.2 (List.mem_range.2 hy))
  have gx := List.getElem_idxOf hix
  have gy := List.getElem_idxOf hiy
  rcases Nat.lt_trichotomy (σ.idxOf x) (σ.idxOf y) with h | h | h
  · exact h
  · have : x = y := by
      rw [← gx, ← gy]
      exact getElem_congr rfl h hix
    subst this
    omega
  · have := List.pairwise_iff_getElem.1 hs _ _ hiy hix h
    rw [gx, gy] at this
    simp only [keyLe, decide_eq_true_eq] at this
    omega

private theorem lt_of_parent {statics : Statics} {x p : Nat}
    (h : staticParent statics x = some p) : x < statics.length := by
  unfold staticParent at h
  cases hx : statics[x]? with
  | none => rw [hx] at h; cases h
  | some _ => exact (List.getElem?_eq_some_iff.1 hx).1

private theorem lt_of_owner {statics : Statics} {x o : Nat}
    (h : staticOwner statics x = some o) : x < statics.length := by
  unfold staticOwner at h
  cases hx : statics[x]? with
  | none => rw [hx] at h; cases h
  | some _ => exact (List.getElem?_eq_some_iff.1 hx).1

private theorem shape_parent (statics : Statics) (i : Nat) :
    ((statics.map (·.1))[i]?).bind (·.1) = staticParent statics i := by
  simp only [List.getElem?_map, staticParent]
  cases statics[i]? <;> rfl

private theorem shape_owner (statics : Statics) (i : Nat) :
    ((statics.map (·.1))[i]?).bind (·.2.1) = staticOwner statics i := by
  simp only [List.getElem?_map, staticOwner]
  cases statics[i]? <;> rfl

private theorem renumber_get {σ : List Nat} {statics : Statics} {i : Nat} (hi : i < σ.length)
    (hx : σ[i] < statics.length) :
    (renumber σ statics)[i]? = some (mapRefs σ.idxOf statics[σ[i]]) := by
  simp [renumber, hi, hx]

private theorem renumber_parent {σ : List Nat} {statics : Statics} {i : Nat} (hi : i < σ.length)
    (hx : σ[i] < statics.length) :
    staticParent (renumber σ statics) i = (staticParent statics σ[i]).map σ.idxOf := by
  rw [staticParent, renumber_get hi hx, staticParent, List.getElem?_eq_getElem hx]
  rfl

private theorem renumber_owner {σ : List Nat} {statics : Statics} {i : Nat} (hi : i < σ.length)
    (hx : σ[i] < statics.length) :
    staticOwner (renumber σ statics) i = (staticOwner statics σ[i]).map σ.idxOf := by
  rw [staticOwner, renumber_get hi hx, staticOwner, List.getElem?_eq_getElem hx]
  rfl

/-! ## Existence of a conforming numbering -/

/-- Owner decision of 2026-11-06 on `StaticsOK`, point (a) (§47, §49 and its last paragraph,
§63.2): every declaration conforming to §47 and §49 has a consistent renumbering, a permutation
of its identifiers preserving parents, owning statics, kinds, initial states and field order,
that satisfies `StaticsOK`. -/
theorem StaticsConf.exists_renumber {statics : Statics} (h : StaticsConf statics) :
    ∃ σ : List Nat, σ.Perm (List.range statics.length) ∧ ConsistentRenumbering σ statics ∧
      StaticsOK (renumber σ statics) := by
  let σ := (List.range statics.length).mergeSort (keyLe statics)
  have hσ : σ.Perm (List.range statics.length) := List.mergeSort_perm _ _
  have hs : σ.Pairwise (fun a b => keyLe statics a b) :=
    List.pairwise_mergeSort
      (fun a b c hab hbc => by simp only [keyLe, decide_eq_true_eq] at *; omega)
      (fun a b => by simp only [keyLe, Bool.or_eq_true, decide_eq_true_eq]; omega) _
  have hnd : σ.Nodup := hσ.nodup_iff.2 List.nodup_range
  have hown : ∀ x o, staticOwner statics x = some o → odepth statics x = odepth statics o + 1 :=
    fun _ _ hxo => chainLen_step h.owner_acyclic h.owner_lt hxo
  have hpar : ∀ x p, staticParent statics x = some p → sdepth statics x = sdepth statics p + 1 :=
    fun _ _ hxp => chainLen_step h.parent_acyclic h.parent_lt hxp
  have hpo : ∀ x p, staticParent statics x = some p → odepth statics x = odepth statics p :=
    fun x p hxp => chainLen_congr (h.part_owner x p hxp) _
  refine ⟨σ, hσ, ⟨fun x hx => ?_, fun x y p hx hy hxy => ?_⟩, ?_⟩
  · have hix := List.idxOf_lt_length_of_mem (hσ.mem_iff.2 (List.mem_range.2 hx))
    simp [renumber, List.getElem?_eq_getElem hix, List.getElem_idxOf hix,
      List.getElem?_eq_getElem hx]
  · have := hpar x p hx
    have := hpar y p hy
    have := hpo x p hx
    have := hpo y p hy
    exact idxOf_lt_of_key hσ hs (lt_of_parent hx) (lt_of_parent hy) (by omega)
  · unfold StaticsOK ShapeOK
    intro i hi
    simp only [List.length_map, renumber, List.mem_range] at hi
    have hxi : σ[i] < statics.length := List.mem_range.1 (hσ.mem_iff.1 (List.getElem_mem hi))
    have hii : σ.idxOf σ[i] = i :=
      (List.Nodup.getElem_inj hnd).1 (List.getElem_idxOf (List.idxOf_lt_length_of_mem
        (List.getElem_mem hi)))
    simp only [shape_parent, shape_owner, Nat.sub_zero, Nat.zero_add, renumber_parent hi hxi,
      renumber_owner hi hxi]
    constructor
    · cases hp : staticParent statics σ[i] with
      | none => trivial
      | some p =>
        have hpl := h.parent_lt _ _ hp
        have hip := List.idxOf_lt_length_of_mem (hσ.mem_iff.2 (List.mem_range.2 hpl))
        have hpσ : σ[σ.idxOf p] = p := List.getElem_idxOf hip
        refine ⟨Nat.zero_le _, ?_, ?_⟩
        · have := hpar _ _ hp
          have := hpo _ _ hp
          have := idxOf_lt_of_key hσ hs hpl hxi (by omega)
          show σ.idxOf p < i
          omega
        · show (staticOwner statics σ[i]).map σ.idxOf = staticOwner (renumber σ statics) (σ.idxOf p)
          rw [renumber_owner hip (by rw [hpσ]; exact hpl), hpσ, h.part_owner _ _ hp]
    · cases ho : staticOwner statics σ[i] with
      | none => trivial
      | some o =>
        have hol := h.owner_lt _ _ ho
        have := hown _ _ ho
        have := idxOf_lt_of_key hσ hs hol hxi (by omega)
        exact ⟨Nat.zero_le _, show σ.idxOf o < i by omega⟩

/-! ## `StaticsOK` declarations conform -/

private theorem rank_of_transGen {R : Nat → Nat → Prop} (rank : Nat → Nat)
    (h : ∀ a b, R a b → rank b < rank a) {a b : Nat} (hab : Relation.TransGen R a b) :
    rank b < rank a := by
  induction hab with
  | single hr => exact h _ _ hr
  | tail _ hr ih => exact Nat.lt_trans (h _ _ hr) ih

/-- `StaticsOK` (§47, §49) is a numbering of a conforming declaration: it implies
`StaticsConf`. -/
theorem StaticsConf.of_staticsOK {statics : Statics} (h : StaticsOK statics) :
    StaticsConf statics := by
  have hok : ∀ i, i < statics.length →
      OptP (staticParent statics i)
        (fun r => r < i ∧ staticOwner statics i = staticOwner statics r) True ∧
      OptP (staticOwner statics i) (fun o => o < i) True := by
    intro i hi
    have := h i (List.mem_range.2 (by simpa using hi))
    simp only [shape_parent, shape_owner, Nat.sub_zero, Nat.zero_add] at this
    obtain ⟨h1, h2⟩ := this
    refine ⟨?_, ?_⟩
    · cases hp : staticParent statics i with
      | none => trivial
      | some r =>
        rw [hp] at h1
        obtain ⟨-, h3, h4⟩ := h1
        exact ⟨h3, h4⟩
    · cases ho : staticOwner statics i with
      | none => trivial
      | some o =>
        rw [ho] at h2
        exact h2.2
  have hpar : ∀ a b, staticParent statics a = some b → b < a := fun a b hab => by
    have := (hok a (lt_of_parent hab)).1
    rw [hab] at this
    exact this.1
  have hown : ∀ a b, staticOwner statics a = some b → b < a := fun a b hab => by
    have := (hok a (lt_of_owner hab)).2
    rw [hab] at this
    exact this
  exact {
    parent_lt := fun i p hp => Nat.lt_trans (hpar i p hp) (lt_of_parent hp)
    owner_lt := fun i o ho => Nat.lt_trans (hown i o ho) (lt_of_owner ho)
    parent_acyclic := fun _ hc => Nat.lt_irrefl _ (rank_of_transGen id hpar hc)
    owner_acyclic := fun _ hc => Nat.lt_irrefl _ (rank_of_transGen id hown hc)
    part_owner := fun i p hp => by
      have := (hok i (lt_of_parent hp)).1
      rw [hp] at this
      exact this.2 }

/-! ## Non-vacuity examples (§47, §49, §63.2) -/

namespace StaticsExamples

/-- Static 0 is a part of static 1, declared before it (§49, last paragraph). -/
def partFirst : Statics := [((some 1, none, 0), true), ((none, none, 1), false)]

/-- `partFirst` is not numbered parent first. -/
example : ¬ StaticsOK partFirst := by decide

private theorem partFirst_owner : ∀ i, staticOwner partFirst i = none
  | 0 | 1 | _ + 2 => rfl

/-- `partFirst` conforms to §47 and §49. -/
example : StaticsConf partFirst where
  parent_lt i p hp := by
    rcases i with _ | _ | i <;> simp [staticParent, partFirst] at hp ⊢
    omega
  owner_lt i o ho := by rw [partFirst_owner] at ho; cases ho
  parent_acyclic _ hc := Nat.lt_irrefl _ (rank_of_transGen (fun a => if a = 1 then 0 else 1)
    (fun a b hab => by
      rcases a with _ | _ | a <;> simp [staticParent, partFirst] at hab
      subst hab; decide) hc)
  owner_acyclic _ hc := Nat.lt_irrefl _ (rank_of_transGen (fun _ => 0)
    (fun a b hab => by rw [partFirst_owner] at hab; cases hab) hc)
  part_owner i p _ := by rw [partFirst_owner, partFirst_owner]

/-- Its renumbering by `[1, 0]` satisfies `StaticsOK`. -/
example : StaticsOK (renumber [1, 0] partFirst) := by decide

/-- Two fields 0 and 1 of static 2, declared before it (§63.2). -/
def fieldsFirst : Statics :=
  [((some 2, none, 0), true), ((some 2, none, 1), false), ((none, none, 2), false)]

/-- Swapping the fields gives a declaration satisfying `StaticsOK`, but not a consistent
renumbering: the field order clause is not vacuous (§63.2). -/
example : StaticsOK (renumber [2, 1, 0] fieldsFirst) ∧
    ¬ ConsistentRenumbering [2, 1, 0] fieldsFirst :=
  ⟨by decide, fun h => absurd (h.field_order 0 1 2 rfl rfl (by decide)) (by decide)⟩

/-- An ownership cycle does not conform (§47). -/
example : ¬ StaticsConf [((none, some 1, 0), true), ((none, some 0, 0), true)] :=
  fun h => h.owner_acyclic 0 (.tail (.single rfl) rfl)

end StaticsExamples

end Ern.MemoryModel.Access
