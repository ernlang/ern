import Ern.MemoryModel.Access.Rename.Derived
import Ern.MemoryModel.Access.Statics

/-!
# Renaming of identities: the initial state

Two `StaticsOK` numberings of one statics declaration related by a consistent renumbering
(`specs/ERN_Memory_Model_Specification.md` §47; §49, last paragraph; §63.2) have
corresponding initial states: the place renaming `Renumbered.π` and the root-authority renaming
`Renumbered.α` relate `S3.init` of both numberings (`Renumbered.initSim`).
-/

namespace Ern.MemoryModel.Access.Rename

variable {statics : Statics} {σ : List Nat}

/-! ## Two numberings of one declaration (§47; §49, last paragraph; §63.2) -/

/-- Two `StaticsOK` numberings of one declaration (§47; §49, last paragraph; §63.2): `statics`
and its consistent renumbering by the permutation `σ`. -/
structure Renumbered (statics : Statics) (σ : List Nat) : Prop where
  perm : σ.Perm (List.range statics.length)
  cons : ConsistentRenumbering σ statics
  ok : StaticsOK statics
  ok' : StaticsOK (renumber σ statics)

/-- The place renaming of a renumbering (§49, last paragraph): old static `x` is new place
`σ.idxOf x`; identity from `statics.length` on. -/
def Renumbered.π (h : Renumbered statics σ) : Ren := Ren.ofPerm σ statics.length h.perm

/-- Old position of the root authority at each new position (§47; `S3.init` lists root
authorities in `rootIdx` order): new position `j'` holds the root of new root static `R'[j']`,
old static `π.g R'[j']`, whose old position is its index in the old `rootIdx`. -/
def rootPerm (statics : Statics) (σ : List Nat) (π : Ren) : List Nat :=
  (rootIdx ((renumber σ statics).map (·.1))).map fun i' =>
    (rootIdx (statics.map (·.1))).idxOf (π.g i')

/-! ## Proof support: the initial places (§47) -/

/-- Place of a static entry in `S3.init` (§47): its parent, its owning static or frame 0, its
kind. -/
private def initPlace (e : (Option Nat × Option Nat × Nat) × Bool) : Place :=
  ⟨e.1.1, match e.1.2.1 with | some o => .place o | none => .frame 0, e.1.2.2⟩

/-- The places of `S3.init` are the declared statics (§47). -/
private theorem init_P_get (st : Statics) (q : Nat) :
    (S3.init st).P[q]? = (st[q]?).map initPlace := by
  have := shapeP_get_new [] (.frame 0) (st.map (·.1)) q
  rw [List.length_nil, Nat.zero_add] at this
  show (shapeP [] (.frame 0) (st.map (·.1)))[q]? = _
  rw [this, List.length_map]
  split
  · rename_i hq
    simp only [List.getElem?_map, List.getElem?_eq_getElem hq, Option.map_some, Option.bind_some,
      shapeOwner, initPlace, Option.getD_some]
    rfl
  · rename_i hq
    rw [List.getElem?_eq_none_iff.2 (by omega)]
    rfl

/-- `S3.init` has one place per static (§47). -/
private theorem init_P_length (st : Statics) : (S3.init st).P.length = st.length := by
  simp [S3.init, shapeP]

/-- Parents of the initial places are the declared parents (§47). -/
private theorem init_parentOf (st : Statics) (q : Nat) :
    parentOf (S3.init st).P q = staticParent st q := by
  unfold parentOf staticParent
  rw [init_P_get]
  cases st[q]? <;> rfl

/-- A static with a parent is declared (§47). -/
private theorem init_lt_of_staticParent {st : Statics} {x p : Nat}
    (h : staticParent st x = some p) : x < st.length := by
  unfold staticParent at h
  cases hx : st[x]? with
  | none => rw [hx] at h; cases h
  | some _ => exact (List.getElem?_eq_some_iff.1 hx).1

/-- Root statics are the declared statics with no parent (§40, §47). -/
private theorem init_mem_rootIdx (st : Statics) (i : Nat) :
    i ∈ rootIdx (st.map (·.1)) ↔ ∃ e, st[i]? = some e ∧ e.1.1 = none := by
  simp only [rootIdx, List.mem_filter, List.mem_range, List.length_map, List.getElem?_map]
  constructor
  · rintro ⟨hi, hn⟩
    refine ⟨st[i], List.getElem?_eq_getElem hi, ?_⟩
    simpa [List.getElem?_eq_getElem hi] using hn
  · rintro ⟨e, he, hn⟩
    exact ⟨(List.getElem?_eq_some_iff.1 he).1, by simp [he, hn]⟩

/-- `rootIdx` has no duplicate (§47). -/
private theorem init_rootIdx_nodup (ls : List (Option Nat × Option Nat × Nat)) :
    (rootIdx ls).Nodup :=
  List.nodup_range.filter _

/-- A renamed static entry is the renamed place (§47; §49, last paragraph). -/
private theorem initPlace_mapRefs (π : Ren) (e : (Option Nat × Option Nat × Nat) × Bool) :
    initPlace (mapRefs π.f e) = (initPlace e).ren π := by
  obtain ⟨⟨p, o, k⟩, b⟩ := e
  cases o <;> rfl

/-! ## The place renaming (§47; §49, last paragraph) -/

/-- A renumbering keeps the number of statics (§49, last paragraph). -/
theorem Renumbered.length (h : Renumbered statics σ) :
    (renumber σ statics).length = statics.length := by
  simp [renumber, h.perm.length_eq]

/-- `π` below the number of statics is the position in `σ` (§49, last paragraph). -/
theorem Renumbered.π_lt (h : Renumbered statics σ) {x : Nat} (hx : x < statics.length) :
    h.π.f x = σ.idxOf x := by
  simp [Renumbered.π, Ren.ofPerm, hx]

/-- `π` is the identity from the number of statics on (§49, last paragraph). -/
theorem Renumbered.π_fix (h : Renumbered statics σ) {x : Nat} (hx : statics.length ≤ x) :
    h.π.f x = x := by
  simp [Renumbered.π, Ren.ofPerm, Nat.not_lt.2 hx]

/-- `ConsistentRenumbering.entry` with `σ.idxOf` replaced by `π.f` (§47; §49, last paragraph):
the references of a `StaticsOK` declaration are declared statics; both sides are `none` from the
number of statics on. -/
theorem Renumbered.entry (h : Renumbered statics σ) (x : Nat) :
    (renumber σ statics)[h.π.f x]? = (statics[x]?).map (mapRefs h.π.f) := by
  by_cases hx : x < statics.length
  · rw [h.π_lt hx, h.cons.entry x hx]
    cases he : statics[x]? with
    | none => rfl
    | some e =>
      have hc := StaticsConf.of_staticsOK h.ok
      have href : ∀ o : Option Nat, (∀ p, o = some p → p < statics.length) →
          o.map σ.idxOf = o.map h.π.f := by
        intro o ho
        cases o with
        | none => rfl
        | some p => simp [h.π_lt (ho p rfl)]
      have hp := href e.1.1 fun p hp => hc.parent_lt x p (by simp [staticParent, he, hp])
      have ho := href e.1.2.1 fun o ho => hc.owner_lt x o (by simp [staticOwner, he, ho])
      simp only [Option.map_some, mapRefs, hp, ho]
  · have hx' : statics.length ≤ x := Nat.not_lt.1 hx
    rw [h.π_fix hx', List.getElem?_eq_none_iff.2 (by rw [h.length]; exact hx'),
      List.getElem?_eq_none_iff.2 hx']
    rfl

/-- The places of both initial states correspond (§47; §49, last paragraph). -/
theorem Renumbered.initP (h : Renumbered statics σ) :
    PRel h.π (S3.init statics).P (S3.init (renumber σ statics)).P where
  len := by rw [init_P_length, init_P_length, h.length]
  get q := by
    rw [init_P_get, init_P_get, h.entry]
    cases statics[q]? with
    | none => rfl
    | some e => exact congrArg some (initPlace_mapRefs h.π e)
  fix q hq := h.π_fix (by rwa [init_P_length] at hq)

/-- The owners of both initial states correspond (§47; §49, last paragraph). -/
private theorem Renumbered.init_shapeOwner (h : Renumbered statics σ) (i : Nat) :
    shapeOwner ((renumber σ statics).map (·.1)) (.frame 0) (h.π.f i) =
      (shapeOwner (statics.map (·.1)) (.frame 0) i).ren h.π := by
  unfold shapeOwner
  rw [List.getElem?_map, List.getElem?_map, h.entry]
  cases statics[i]? with
  | none => rfl
  | some e =>
    obtain ⟨⟨p, o, k⟩, b⟩ := e
    cases o <;> rfl

/-! ## The root-authority renaming (§47; §49, last paragraph) -/

/-- Root statics correspond, forward (§40, §47). -/
private theorem Renumbered.root_mem_f (h : Renumbered statics σ) (i : Nat) :
    h.π.f i ∈ rootIdx ((renumber σ statics).map (·.1)) ↔ i ∈ rootIdx (statics.map (·.1)) := by
  rw [init_mem_rootIdx, init_mem_rootIdx, h.entry]
  cases statics[i]? with
  | none => simp
  | some e => simp [mapRefs]

/-- Root statics correspond (§40, §47; §49, last paragraph). -/
theorem Renumbered.root_mem (h : Renumbered statics σ) (i' : Nat) :
    i' ∈ rootIdx ((renumber σ statics).map (·.1)) ↔ h.π.g i' ∈ rootIdx (statics.map (·.1)) :=
  h.π.mem_iff_g h.root_mem_f i'

/-- The root statics of both numberings correspond up to order (§47; §49, last paragraph). -/
theorem Renumbered.rootIdx_perm (h : Renumbered statics σ) :
    (rootIdx ((renumber σ statics).map (·.1))).Perm
      ((rootIdx (statics.map (·.1))).map h.π.f) :=
  h.π.perm_of_mem (init_rootIdx_nodup _) (init_rootIdx_nodup _) h.root_mem_f

/-- `rootPerm` is a permutation of the root-authority positions (§47; §49, last paragraph). -/
theorem Renumbered.rootPerm_perm (h : Renumbered statics σ) :
    (rootPerm statics σ h.π).Perm (List.range (rootIdx (statics.map (·.1))).length) := by
  have hm : ∀ i' ∈ rootIdx ((renumber σ statics).map (·.1)),
      h.π.g i' ∈ rootIdx (statics.map (·.1)) := fun i' hi' => (h.root_mem i').1 hi'
  apply perm_range_of_nodup
  · unfold rootPerm List.Nodup
    rw [List.pairwise_map]
    refine (init_rootIdx_nodup _).imp_of_mem fun {a b} ha hb hab e => hab ?_
    have ga := List.getElem_idxOf (List.idxOf_lt_length_of_mem (hm a ha))
    have gb := List.getElem_idxOf (List.idxOf_lt_length_of_mem (hm b hb))
    have : h.π.g a = h.π.g b := by
      rw [← ga, ← gb]
      exact getElem_congr rfl e _
    rw [← h.π.fg a, this, h.π.fg]
  · intro a ha
    obtain ⟨i', hi', rfl⟩ := List.mem_map.1 ha
    exact List.idxOf_lt_length_of_mem (hm i' hi')
  · rw [rootPerm, List.length_map, h.rootIdx_perm.length_eq, List.length_map]

/-- The root-authority renaming of a renumbering (§47; §49, last paragraph): old root authority
`j` goes to the new position of the root of static `π.f R[j]`; identity from the number of root
authorities on. -/
def Renumbered.α (h : Renumbered statics σ) : Ren :=
  Ren.ofPerm (rootPerm statics σ h.π) _ h.rootPerm_perm

/-- `rootIdx_α`, read backward (§47; §49, last paragraph). -/
private theorem Renumbered.rootIdx_αg (h : Renumbered statics σ) (j' : Nat) :
    (rootIdx ((renumber σ statics).map (·.1)))[j']? =
      ((rootIdx (statics.map (·.1)))[h.α.g j']?).map h.π.f := by
  have hlen := h.rootIdx_perm.length_eq
  rw [List.length_map] at hlen
  simp only [Renumbered.α, Ren.ofPerm]
  split
  · rename_i hj
    have hj' : j' < (rootIdx ((renumber σ statics).map (·.1))).length := by
      simpa [rootPerm] using hj
    have hm := (h.root_mem _).1 (List.getElem_mem hj')
    simp only [rootPerm, List.getElem_map]
    rw [List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hm),
      List.getElem_idxOf (List.idxOf_lt_length_of_mem hm), Option.map_some, h.π.fg,
      List.getElem?_eq_getElem hj']
  · rename_i hj
    have hj' : (rootIdx ((renumber σ statics).map (·.1))).length ≤ j' := by
      simpa [rootPerm] using hj
    rw [List.getElem?_eq_none_iff.2 hj', List.getElem?_eq_none_iff.2 (hlen ▸ hj')]
    rfl

/-- Root authority `j` of `statics` and root authority `α.f j` of the renumbering hold the roots
of corresponding statics (§47; §49, last paragraph). -/
theorem Renumbered.rootIdx_α (h : Renumbered statics σ) (j : Nat) :
    (rootIdx ((renumber σ statics).map (·.1)))[h.α.f j]? =
      ((rootIdx (statics.map (·.1)))[j]?).map h.π.f := by
  have := h.rootIdx_αg (h.α.f j)
  rwa [h.α.gf] at this

/-! ## The initial states correspond (§47; §49, last paragraph; §63.2) -/

/-- Parent and origin links of the initial state go to smaller identities (§47, §49.2, §49.5;
§49, last paragraph): `init_kinv`. -/
theorem init_down (hst : StaticsOK statics) : Down (S3.init statics) :=
  Down.of_wf3 (init_kinv hst).1.1

/-- The initial states of both numberings are related (§47; §49, last paragraph). -/
theorem Renumbered.initRel (h : Renumbered statics σ) :
    SRel h.π h.α (S3.init statics) (S3.init (renumber σ statics)) where
  F := rfl
  nF := rfl
  P := h.initP
  I l := by
    show (if (((renumber σ statics)[h.π.f l]?).map (·.2)).getD false then InitSt.init
      else .uninit) = if ((statics[l]?).map (·.2)).getD false then .init else .uninit
    rw [h.entry, Option.map_map]
    rfl
  Alen := by simp [S3.init, h.rootIdx_perm.length_eq]
  A x := by
    simp only [S3.init, List.getElem?_map]
    rw [h.rootIdx_α]
    cases (rootIdx (statics.map (·.1)))[x]? with
    | none => exact .none
    | some i =>
      exact .some ⟨rfl, rfl,
        footprint_perm_ren h.initP (init_down h.ok).1 (init_down h.ok').1 i,
        h.init_shapeOwner i, rfl⟩
  Afix x hx := by
    have hx' : (rootIdx (statics.map (·.1))).length ≤ x := by simpa [S3.init] using hx
    simp [Renumbered.α, Ren.ofPerm, Nat.not_lt.2 hx']
  D _ := by simp [S3.init]
  dead _ := rfl
  pins o := by simp only [S3.init, List.getElem?_nil]; exact .none

/-- `π` keeps the field order of the initial places (§63.2; §49, last paragraph):
`ConsistentRenumbering.field_order`. -/
theorem Renumbered.initSib (h : Renumbered statics σ) : SibMono h.π (S3.init statics).P := by
  intro x y p hx hy hxy
  rw [init_parentOf] at hx hy
  rw [h.π_lt (init_lt_of_staticParent hx), h.π_lt (init_lt_of_staticParent hy)]
  exact h.cons.field_order x y p hx hy hxy

/-- The simulation invariant holds between the initial states of both numberings (§47; §49, last
paragraph; §63.2). -/
theorem Renumbered.initSim (h : Renumbered statics σ) :
    Sim h.π h.α (S3.init statics) (S3.init (renumber σ statics)) :=
  ⟨h.initRel, init_down h.ok, init_down h.ok', h.initSib⟩

/-- Every `StaticsOK` declaration (§47; §49, last paragraph; §63.2) is `Renumbered` with the
consistent renumbering that `StaticsConf.exists_renumber` builds from it
(`StaticsConf.of_staticsOK`). `Renumbered` asks `StaticsOK` of both numberings, so a conforming
declaration that is not `StaticsOK` is not related to its numbering by this theorem. -/
theorem StaticsOK.renumbered (hok : StaticsOK statics) : ∃ σ, Renumbered statics σ := by
  obtain ⟨σ, hp, hc, hok'⟩ := (StaticsConf.of_staticsOK hok).exists_renumber
  exact ⟨σ, hp, hc, hok, hok'⟩

/-! ## Non-vacuity (§47; §49, last paragraph; §63.2) -/

namespace InitExamples

/-- Root static 0 with fields 1 and 2, and root static 3 (§47, §63.2). -/
def n1 : Statics := [((none, none, 0), false), ((some 0, none, 1), true),
  ((some 0, none, 2), true), ((none, none, 3), false)]

/-- `n1` and its renumbering by `[3, 0, 1, 2]` are two `StaticsOK` numberings of one declaration
(§47; §49, last paragraph; §63.2). -/
theorem n1_renumbered : Renumbered n1 [3, 0, 1, 2] where
  perm := by decide
  cons := {
    entry := fun x hx => by
      have key : ∀ x ∈ List.range 4, (renumber [3, 0, 1, 2] n1)[[3, 0, 1, 2].idxOf x]? =
          (n1[x]?).map (mapRefs [3, 0, 1, 2].idxOf) := by
        decide
      exact key x (List.mem_range.2 hx)
    field_order := fun x y _ hx hy hxy => by
      have key : ∀ x ∈ List.range 4, ∀ y ∈ List.range 4, staticParent n1 x = staticParent n1 y →
          (staticParent n1 x).isSome → x < y → [3, 0, 1, 2].idxOf x < [3, 0, 1, 2].idxOf y := by
        decide
      exact key x (List.mem_range.2 (init_lt_of_staticParent hx)) y
        (List.mem_range.2 (init_lt_of_staticParent hy)) (hx.trans hy.symm) (by rw [hx]; rfl) hxy }
  ok := by decide
  ok' := by decide

/-- Both renamings are non-trivial (§49, last paragraph): `π` sends static 0 to 1 and 3 to 0,
`α` swaps the two root authorities. -/
example : n1_renumbered.π.f 0 = 1 ∧ n1_renumbered.π.f 3 = 0 ∧ n1_renumbered.α.f 0 = 1 ∧
    n1_renumbered.α.f 1 = 0 := by decide

/-- The initial states of both numberings of `n1` correspond (§47; §49, last paragraph). -/
example : Sim n1_renumbered.π n1_renumbered.α (S3.init n1) (S3.init (renumber [3, 0, 1, 2] n1)) :=
  n1_renumbered.initSim

end InitExamples

end Ern.MemoryModel.Access.Rename
