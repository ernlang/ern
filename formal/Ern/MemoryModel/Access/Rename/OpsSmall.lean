import Ern.MemoryModel.Access.Rename.Derived

/-!
# Renaming of identities: O1, O2, O3, O5, O8, O9, O10, O11, O15, O16

Correspondence under related states (§49, last paragraph) of the steps `derive` (§60), `split`
(§61), `release` (§62), `depend` (§64), `store` (§65), `read` (§66), `write` (§67), `writeShared`
(§68), `pin` (§74) and `unpin` (§75) of `specs/ERN_Memory_Model_Specification.md`, with the
arguments renamed as in `KernelOp.ren`. Per operation: the preconditions correspond (`…Pre_ren`),
the effects are related (`…Eff_ren`), the step relations correspond (`…_corr`), and an `ok`
outcome keeps downward links (`…_down`) and the field order of `π` (`…_sib`).
-/

namespace Ern.MemoryModel.Access.Rename

variable {π α : Ren} {s s' t : S3} {k k' : K}

/-! ## Helpers -/

/-- An optional authority read by corresponding predicates (§42; §49, last paragraph). -/
private theorem SRel.optP_A (h : SRel π α s s') {Q Q' : Authority → Prop} {d d' : Prop}
    (hd : d' ↔ d) (hQ : ∀ y y', AuthRel π α y y' → (Q' y' ↔ Q y)) (x : Nat) :
    OptP (s'.A[α.f x]?) Q' d' ↔ OptP (s.A[x]?) Q d := by
  cases hy : s.A[x]? with
  | none => rw [(h.A_none x).1 hy]; exact hd
  | some y =>
    obtain ⟨y', hy', hr⟩ := h.A_some hy
    rw [hy']; exact hQ y y' hr

/-- An optional pinning obligation read by corresponding predicates (§74, §75; §49, last
paragraph). -/
private theorem SRel.optP_pins (h : SRel π α s s') {Q Q' : PinOb → Prop} {d d' : Prop}
    (hd : d' ↔ d) (hQ : ∀ ob ob', PinRel π ob ob' → (Q' ob' ↔ Q ob)) (o : Nat) :
    OptP (s'.pins[o]?) Q' d' ↔ OptP (s.pins[o]?) Q d := by
  cases hob : s.pins[o]? with
  | none => rw [(h.pins_none o).1 hob]; exact hd
  | some ob =>
    obtain ⟨ob', hob', hr⟩ := h.pins_some hob
    rw [hob']; exact hQ ob ob' hr

/-- A renamed holder is a frame exactly when the holder is that frame (§42; §49, last
paragraph). -/
private theorem ren_eq_frame (π : Ren) (o : Holder) (f : Nat) :
    o.ren π = .frame f ↔ o = .frame f :=
  Holder.ren_inj π (b := .frame f)

/-- A renamed holder is a renamed place exactly when the holder is that place (§42; §49, last
paragraph). -/
private theorem ren_eq_place (π : Ren) (o : Holder) (p : Nat) :
    o.ren π = .place (π.f p) ↔ o = .place p :=
  Holder.ren_inj π (b := .place p)

/-- The f-form of a membership correspondence given in g-form (§49, last paragraph). -/
private theorem mem_f_of_g {ls ls' : List Nat} (hls : ∀ l, l ∈ ls' ↔ π.g l ∈ ls) (l : Nat) :
    π.f l ∈ ls' ↔ l ∈ ls := by
  rw [hls, π.gf]

/-- Related states with related authorities of fresh identities appended are related (§42, §60,
§61; §49, last paragraph). -/
private theorem SRel.appendA (h : SRel π α s s') {ys ys' : List Authority}
    (hlen : ys'.length = ys.length)
    (hys : ∀ i : Nat, Option.Rel (AuthRel π α) (ys[i]?) (ys'[i]?)) :
    SRel π α { s with A := s.A ++ ys } { s' with A := s'.A ++ ys' } where
  F := h.F
  nF := h.nF
  P := h.P
  I := h.I
  Alen := by simp only [List.length_append, h.Alen, hlen]
  A x := by
    show Option.Rel _ ((s.A ++ ys)[x]?) ((s'.A ++ ys')[α.f x]?)
    by_cases hx : x < s.A.length
    · rw [List.getElem?_append_left hx, List.getElem?_append_left ((h.Alt x).2 hx)]
      exact h.A x
    · have hx' := Nat.le_of_not_lt hx
      rw [h.Afix x hx', List.getElem?_append_right hx',
        List.getElem?_append_right (h.Alen ▸ hx'), h.Alen]
      exact hys _
  Afix x hx := h.Afix x (Nat.le_trans (by simp) hx)
  D := h.D
  dead := h.dead
  pins := h.pins

/-- Corresponding authorities updated in place are related (§42, §62, §65; §49, last
paragraph). -/
private theorem SRel.setA (h : SRel π α s s') {a : Nat} {y y' : Authority}
    (hr : AuthRel π α y y') (x : Nat) :
    Option.Rel (AuthRel π α) ((s.A.set a y)[x]?) ((s'.A.set (α.f a) y')[α.f x]?) := by
  simp only [List.getElem?_set, α.f_inj, h.Alt]
  by_cases e : a = x
  · subst e
    rw [ite_eq_left rfl, ite_eq_left rfl]
    split
    · exact .some hr
    · exact .none
  · rw [ite_eq_right e, ite_eq_right e]; exact h.A x

/-- Appending authorities whose origins exist keeps downward links (§49.5; §49, last
paragraph). -/
private theorem down_appendA (hd : Down s) {ys : List Authority}
    (hys : ∀ y ∈ ys, ∀ o, y.origin = some o → o < s.A.length) :
    Down { s with A := s.A ++ ys } := by
  refine ⟨hd.1, fun j o ho => ?_⟩
  simp only [S3.org] at ho
  by_cases hj : j < s.A.length
  · rw [List.getElem?_append_left hj] at ho; exact hd.2 j o ho
  · rw [List.getElem?_append_right (Nat.le_of_not_lt hj)] at ho
    obtain ⟨y, hy, hyo⟩ := Option.bind_eq_some_iff.1 ho
    exact Nat.lt_of_lt_of_le (hys y (List.mem_of_getElem? hy) o hyo) (Nat.le_of_not_lt hj)

/-- Updating an authority without changing its origin keeps downward links (§49.5; §49, last
paragraph). -/
private theorem down_setA (hd : Down s) {a : Nat} {x y : Authority} (hx : s.A[a]? = some x)
    {t : S3} (hP : t.P = s.P) (hA : t.A = s.A.set a y) (ho : y.origin = x.origin) : Down t := by
  refine ⟨by rw [hP]; exact hd.1, fun j o hj => hd.2 j o ?_⟩
  simp only [S3.org, hA, List.getElem?_set] at hj ⊢
  by_cases e : a = j
  · subst e
    rw [ite_eq_left rfl, ite_eq_left (lt_of_getElem? hx)] at hj
    rw [hx]; simpa [ho] using hj
  · rwa [ite_eq_right e] at hj

/-! ## O1 `derive` (§60) -/

/-- The effects of `derive` are related (§60, `ok` effect; §49, last paragraph). -/
theorem deriveEff_ren (h : SRel π α s s') (src : Nat) (region : List Nat) (m : Mode) :
    SRel π α (deriveEff s src region m) (deriveEff s' (α.f src) (region.map π.f) m) :=
  h.appendA rfl fun i => by
    cases i with
    | zero => exact .some ⟨rfl, rfl, .refl _, by rw [h.top]; rfl, rfl⟩
    | succ i => exact .none

/-- The effect of `derive` keeps downward links (§60, `ok` effect; §49.5; §49, last
paragraph). -/
theorem deriveEff_down (hd : Down s) {src : Nat} (hsrc : src < s.A.length) (region : List Nat)
    (m : Mode) : Down (deriveEff s src region m) :=
  down_appendA hd fun y hy o ho => by
    rw [List.mem_singleton] at hy; subst hy; cases ho; exact hsrc

/-- The preconditions of `derive` correspond (§60; §49, last paragraph). -/
theorem derivePre_ren (hS : Sim π α s s') (src : Nat) (region : List Nat) (m : Mode) :
    DerivePre s' (α.f src) (region.map π.f) m ↔ DerivePre s src region m := by
  have h := hS.rel; have hd := hS.down; have hd' := hS.down'
  have hreg := π.mem_map_f region
  have e1 := h.active src
  have e2 := h.exercisableAt hd hd' src m
  have e3 : (∀ x ∈ s'.ancs (α.f src), s'.Active x) ↔ ∀ x ∈ s.ancs src, s.Active x :=
    α.forall_mem_iff (h.mem_ancs hd hd' src) h.active
  have e4 : (∀ l ∈ region.map π.f, l < s'.P.length ∧ isLeaf s'.P l) ↔
      ∀ l ∈ region, l < s.P.length ∧ isLeaf s.P l :=
    π.forall_mem_iff hreg fun l => and_congr (h.P.lt_iff l) (isLeaf_ren h.P l)
  have e5 : (∀ l ∈ region.map π.f, l ∈ s'.afp (α.f src)) ↔ ∀ l ∈ region, l ∈ s.afp src :=
    π.forall_mem_iff hreg (h.mem_afp src)
  have e6 : (∀ l ∈ region.map π.f, Allows (effective s' (α.f src) l) m) ↔
      ∀ l ∈ region, Allows (effective s src l) m :=
    π.forall_mem_iff hreg fun l => by rw [h.effective hd hd']
  have e7 : (∀ b ∈ List.range s'.A.length, OptP (s'.A[b]?) (fun y => y.active = true →
      b ∉ α.f src :: s'.ancs (α.f src) → (∃ l ∈ region.map π.f, l ∈ y.footprint) →
        y.mode = .observe ∧ m = .observe) True) ↔
      ∀ b ∈ List.range s.A.length, OptP (s.A[b]?) (fun y => y.active = true →
        b ∉ src :: s.ancs src → (∃ l ∈ region, l ∈ y.footprint) →
          y.mode = .observe ∧ m = .observe) True :=
    α.forall_mem_iff h.mem_rangeA fun b => h.optP_A Iff.rfl (fun y y' hr => by
      simp only [hr.active, hr.mode, π.exists_mem_iff hreg hr.mem_footprint, List.mem_cons,
        α.f_inj, h.mem_ancs hd hd']) b
  have e8 : s'.top ∈ s'.F ↔ s.top ∈ s.F := by rw [h.top, h.F]
  exact ⟨fun p => ⟨e1.1 p.active, e2.1 p.exercisable, e3.1 p.chainActive, e4.1 p.leaves,
      e5.1 p.within, e6.1 p.modeOK, e7.1 p.exclusive, e8.1 p.frameLive⟩,
    fun p => ⟨e1.2 p.active, e2.2 p.exercisable, e3.2 p.chainActive, e4.2 p.leaves,
      e5.2 p.within, e6.2 p.modeOK, e7.2 p.exclusive, e8.2 p.frameLive⟩⟩

/-- The steps of `derive` correspond (§60, §58; §49, last paragraph). -/
theorem derive_corr (hS : Sim π α s s') (src : Nat) (region : List Nat) (m : Mode) :
    StepCorr π α (DeriveStep src region m s) (DeriveStep (α.f src) (region.map π.f) m s') :=
  guarded_corr (derivePre_ren hS src region m) fun _ => deriveEff_ren hS.rel src region m

/-- An `ok` outcome of `derive` keeps downward links (§60; §49.5; §49, last paragraph). -/
theorem derive_down (hd : Down s) {src : Nat} {region : List Nat} {m : Mode}
    (hst : DeriveStep src region m s (.ok t)) : Down t := by
  obtain ⟨hp, rfl⟩ := Guarded.ok_iff.1 hst
  obtain ⟨_, hy, -⟩ := hp.active
  exact deriveEff_down hd (lt_of_getElem? hy) region m

/-- An `ok` outcome of `derive` keeps the field order of `π` (§60, §63.2; §49, last
paragraph). -/
theorem derive_sib (hs : SibMono π s.P) {src : Nat} {region : List Nat} {m : Mode}
    (hst : DeriveStep src region m s (.ok t)) : SibMono π t.P := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hst; exact hs

/-! ## O2 `split` (§61) -/

/-- The effects of `split` are related (§61, `ok` effect; §49, last paragraph). -/
theorem splitEff_ren (h : SRel π α s s') (src : Nat) (rs : List (List Nat)) :
    SRel π α (splitEff s src rs) (splitEff s' (α.f src) (rs.map (·.map π.f))) := by
  refine h.appendA (by simp) fun i => ?_
  simp only [List.getElem?_map, Option.map_map]
  cases rs[i]? with
  | none => exact .none
  | some r => exact .some ⟨rfl, rfl, .refl _, by rw [h.top]; rfl, rfl⟩

/-- The effect of `split` keeps downward links (§61, `ok` effect; §49.5; §49, last
paragraph). -/
theorem splitEff_down (hd : Down s) {src : Nat} (hsrc : src < s.A.length)
    (rs : List (List Nat)) : Down (splitEff s src rs) :=
  down_appendA hd fun y hy o ho => by
    obtain ⟨r, -, rfl⟩ := List.mem_map.1 hy; cases ho; exact hsrc

/-- An exclusive right already distributed corresponds (§61.3; §49, last paragraph). -/
theorem SRel.distribExcl (h : SRel π α s s') (hd : Down s) (hd' : Down s') (src j p : Nat) :
    DistribExcl s' (α.f src) (α.f j) (π.f p) ↔ DistribExcl s src j p :=
  h.optP_A Iff.rfl (fun y y' hr => by
    simp only [hr.active, hr.mode, h.mem_ancs hd hd', hr.mem_footprint]) j

/-- The preconditions of `split` correspond, for contracts corresponding under the renaming (§61,
§48; §49, last paragraph). -/
theorem splitPre_ren (hK : KCorr π α k k') (hS : Sim π α s s') (src : Nat)
    (rs : List (List Nat)) :
    SplitPre k' s' (α.f src) (rs.map (·.map π.f)) ↔ SplitPre k s src rs := by
  have h := hS.rel; have hd := hS.down; have hd' := hS.down'
  have hR : ∀ {Q' Q : Nat → Prop}, (∀ p, Q' (π.f p) ↔ Q p) →
      ((∀ r ∈ rs.map (·.map π.f), ∀ p ∈ r, Q' p) ↔ ∀ r ∈ rs, ∀ p ∈ r, Q p) := fun hQ => by
    rw [List.forall_mem_map]
    exact forall₂_congr fun r _ => π.forall_mem_iff (π.mem_map_f r) hQ
  have e1 := h.active src
  have e2 := h.exercisableAt hd hd' src .modify
  have e3 : (∀ r ∈ rs.map (·.map π.f), ∀ p ∈ r, effective s' (α.f src) p = some .modify) ↔
      ∀ r ∈ rs, ∀ p ∈ r, effective s src p = some .modify :=
    hR fun p => by rw [h.effective hd hd']
  have e4 : (∀ r ∈ rs.map (·.map π.f), ∀ p ∈ r,
      p ∈ s'.afp (α.f src) ∧ effective s' (α.f src) p ≠ none) ↔
      ∀ r ∈ rs, ∀ p ∈ r, p ∈ s.afp src ∧ effective s src p ≠ none :=
    hR fun p => by rw [h.mem_afp, h.effective hd hd']
  have e5 : (rs.map (·.map π.f)).Pairwise
      (fun r r' => (∀ l ∈ r, l ∉ r') ∨ k'.DeclaredDisjoint r r') ↔
      rs.Pairwise (fun r r' => (∀ l ∈ r, l ∉ r') ∨ k.DeclaredDisjoint r r') := by
    rw [List.pairwise_map]
    exact List.Pairwise.iff fun r r' => or_congr
      (π.forall_mem_iff (π.mem_map_f r) fun l => not_congr (π.mem_map_f r' l)) (hK.dd r r')
  have e6 : (∀ r ∈ rs.map (·.map π.f), ∀ p ∈ r,
      ∀ j ∈ List.range s'.A.length, ¬ DistribExcl s' (α.f src) j p) ↔
      ∀ r ∈ rs, ∀ p ∈ r, ∀ j ∈ List.range s.A.length, ¬ DistribExcl s src j p :=
    hR fun p => α.forall_mem_iff h.mem_rangeA fun j => not_congr (h.distribExcl hd hd' src j p)
  exact ⟨fun q => ⟨e1.1 q.active, e2.1 q.exercisable, e3.1 q.modifyOn, e4.1 q.within,
      e5.1 q.disjoint, e6.1 q.notDistributed⟩,
    fun q => ⟨e1.2 q.active, e2.2 q.exercisable, e3.2 q.modifyOn, e4.2 q.within,
      e5.2 q.disjoint, e6.2 q.notDistributed⟩⟩

/-- The steps of `split` correspond, for contracts corresponding under the renaming (§61, §48,
§58; §49, last paragraph). -/
theorem split_corr_of (hK : KCorr π α k k') (hS : Sim π α s s') (src : Nat)
    (rs : List (List Nat)) :
    StepCorr π α (SplitStep k src rs s) (SplitStep k' (α.f src) (rs.map (·.map π.f)) s') :=
  guarded_corr (splitPre_ren hK hS src rs) fun _ => splitEff_ren hS.rel src rs

/-- The steps of `split` correspond, with the renamed contract (§61, §48, §58; §49, last
paragraph). -/
theorem split_corr (hS : Sim π α s s') (src : Nat) (rs : List (List Nat)) :
    StepCorr π α (SplitStep k src rs s)
      (SplitStep (k.rename π α) (α.f src) (rs.map (·.map π.f)) s') :=
  split_corr_of (KCorr.rename π α k) hS src rs

/-- An `ok` outcome of `split` keeps downward links (§61; §49.5; §49, last paragraph). -/
theorem split_down (hd : Down s) {src : Nat} {rs : List (List Nat)}
    (hst : SplitStep k src rs s (.ok t)) : Down t := by
  obtain ⟨hp, rfl⟩ := Guarded.ok_iff.1 hst
  obtain ⟨_, hy, -⟩ := hp.active
  exact splitEff_down hd (lt_of_getElem? hy) rs

/-- An `ok` outcome of `split` keeps the field order of `π` (§61, §63.2; §49, last
paragraph). -/
theorem split_sib (hs : SibMono π s.P) {src : Nat} {rs : List (List Nat)}
    (hst : SplitStep k src rs s (.ok t)) : SibMono π t.P := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hst; exact hs

/-! ## O3 `release` (§62) -/

/-- The effects of `release` are related (§62, `ok` effect; §49, last paragraph). -/
theorem releaseEff_ren (h : SRel π α s s') (a : Nat) :
    SRel π α (releaseEff s a) (releaseEff s' (α.f a)) := by
  cases hx : s.A[a]? with
  | none =>
    simp only [releaseEff, hx, (h.A_none a).1 hx]; exact h
  | some x =>
    obtain ⟨x', hx', hr⟩ := h.A_some hx
    simp only [releaseEff, hx, hx']
    exact { h with
      Alen := by simp only [List.length_set, h.Alen]
      A := h.setA ⟨hr.mode, hr.origin, hr.footprint, hr.holder, rfl⟩
      Afix := fun j hj => h.Afix j (by simpa using hj)
      D := fun q => by
        show List.Perm (if x'.holder = Holder.place (π.f q) then _ else _)
          (List.map α.f (if x.holder = Holder.place q then _ else _))
        rw [hr.holder]
        by_cases hq : x.holder = .place q
        · rw [ite_eq_left ((ren_eq_place π _ q).2 hq), ite_eq_left hq]
          refine ((h.D q).filter _).trans ?_
          rw [List.filter_map]
          refine .of_eq (congrArg _ (List.filter_congr fun z _ => ?_))
          simp only [Function.comp_def, bne, Bool.beq_eq_decide_eq, α.f_inj]
        · rw [ite_eq_right (fun e => hq ((ren_eq_place π _ q).1 e)), ite_eq_right hq]; exact h.D q }

/-- The effect of `release` keeps downward links (§62, `ok` effect; §49.5; §49, last
paragraph). -/
theorem releaseEff_down (hd : Down s) (a : Nat) : Down (releaseEff s a) := by
  unfold releaseEff
  split
  · rename_i x hx; exact down_setA hd hx rfl rfl rfl
  · exact hd

/-- The right of the current frame on a holder corresponds (§62.2; §49, last paragraph). -/
theorem SRel.holderRight (h : SRel π α s s') (hd : Down s) (hd' : Down s') (o : Holder) :
    HolderRight s' (o.ren π) ↔ HolderRight s o := by
  cases o with
  | frame f => show f = s'.top ↔ f = s.top; rw [h.top]
  | place p => exact h.hasRight hd hd' .modify p

/-- The preconditions of `release` correspond (§62; §49, last paragraph). -/
theorem releasePre_ren (hS : Sim π α s s') (a : Nat) : ReleasePre s' (α.f a) ↔ ReleasePre s a := by
  have h := hS.rel; have hd := hS.down; have hd' := hS.down'
  have e1 := h.active a
  have e2 : OptP (s'.A[α.f a]?) (fun y => y.origin ≠ none) False ↔
      OptP (s.A[a]?) (fun y => y.origin ≠ none) False :=
    h.optP_A Iff.rfl (fun y y' hr => by simp only [hr.origin, ne_eq, Option.map_eq_none_iff]) a
  have e3 : OptP (s'.A[α.f a]?) (fun y => HolderRight s' y.holder) False ↔
      OptP (s.A[a]?) (fun y => HolderRight s y.holder) False :=
    h.optP_A Iff.rfl (fun y y' hr => by rw [hr.holder]; exact h.holderRight hd hd' _) a
  have e4 : (∀ j ∈ List.range s'.A.length, α.f a ∈ s'.ancs j → ¬ s'.Active j) ↔
      ∀ j ∈ List.range s.A.length, a ∈ s.ancs j → ¬ s.Active j :=
    α.forall_mem_iff h.mem_rangeA fun j =>
      imp_congr (h.mem_ancs hd hd' j a) (not_congr (h.active j))
  have e5 : (∀ q ∈ List.range s'.P.length, s'.Usable q → α.f a ∈ s'.D q →
      (s'.A[α.f a]?).map (·.holder) = some (.place q)) ↔
      ∀ q ∈ List.range s.P.length, s.Usable q → a ∈ s.D q →
        (s.A[a]?).map (·.holder) = some (.place q) :=
    π.forall_mem_iff h.P.mem_range fun q => imp_congr (h.usable q) (imp_congr (h.mem_D q a) (by
      cases hy : s.A[a]? with
      | none => rw [(h.A_none a).1 hy]; simp
      | some y =>
        obtain ⟨y', hy', hr⟩ := h.A_some hy
        rw [hy']
        simp only [Option.map_some, Option.some.injEq, hr.holder, ren_eq_place]))
  exact ⟨fun p => ⟨e1.1 p.active, e2.1 p.derived, e3.1 p.holderRight, e4.1 p.noActiveDesc,
      e5.1 p.anchors⟩,
    fun p => ⟨e1.2 p.active, e2.2 p.derived, e3.2 p.holderRight, e4.2 p.noActiveDesc,
      e5.2 p.anchors⟩⟩

/-- The steps of `release` correspond (§62, §58; §49, last paragraph). -/
theorem release_corr (hS : Sim π α s s') (a : Nat) :
    StepCorr π α (ReleaseStep a s) (ReleaseStep (α.f a) s') :=
  guarded_corr (releasePre_ren hS a) fun _ => releaseEff_ren hS.rel a

/-- An `ok` outcome of `release` keeps downward links (§62; §49.5; §49, last paragraph). -/
theorem release_down (hd : Down s) {a : Nat} (hst : ReleaseStep a s (.ok t)) : Down t := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hst
  exact releaseEff_down hd a

/-- An `ok` outcome of `release` keeps the field order of `π` (§62, §63.2; §49, last
paragraph). -/
theorem release_sib (hs : SibMono π s.P) {a : Nat} (hst : ReleaseStep a s (.ok t)) :
    SibMono π t.P := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hst
  unfold releaseEff; split <;> exact hs

/-! ## O5 `depend` (§64) -/

/-- The effects of `depend` are related (§64, `ok` effect; §49, last paragraph). -/
theorem dependEff_ren (h : SRel π α s s') (q x : Nat) :
    SRel π α (dependEff s q x) (dependEff s' (π.f q) (α.f x)) :=
  { h with
    D := fun r => by
      show List.Perm (if π.f r = π.f q then _ else _) (List.map α.f (if r = q then _ else _))
      by_cases e : r = q
      · subst e
        rw [ite_eq_left rfl, ite_eq_left rfl, List.map_append]
        exact (h.D r).append (.refl _)
      · rw [ite_eq_right (fun e' => e (π.f_inj.1 e')), ite_eq_right e]; exact h.D r }

/-- The preconditions of `depend` correspond (§64; §49, last paragraph). -/
theorem dependPre_ren (hS : Sim π α s s') (q x : Nat) :
    DependPre s' (π.f q) (α.f x) ↔ DependPre s q x := by
  have h := hS.rel; have hd := hS.down; have hd' := hS.down'
  have e1 := h.usable q
  have e2 := h.hasRight hd hd' .modify q
  have e3 := h.active x
  have e4 : EffAnchorOK s' (α.f x) (s'.pframe (π.f q)) ↔ EffAnchorOK s x (s.pframe q) := by
    rw [h.pframe]; exact h.effAnchorOK hd hd' x _
  exact ⟨fun p => ⟨e1.1 p.usable, e2.1 p.right, e3.1 p.anchorActive, e4.1 p.anchorOrder⟩,
    fun p => ⟨e1.2 p.usable, e2.2 p.right, e3.2 p.anchorActive, e4.2 p.anchorOrder⟩⟩

/-- The steps of `depend` correspond (§64, §58; §49, last paragraph). -/
theorem depend_corr (hS : Sim π α s s') (q x : Nat) :
    StepCorr π α (DependStep q x s) (DependStep (π.f q) (α.f x) s') :=
  guarded_corr (dependPre_ren hS q x) fun _ => dependEff_ren hS.rel q x

/-- An `ok` outcome of `depend` keeps downward links (§64; §49.5; §49, last paragraph). -/
theorem depend_down (hd : Down s) {q x : Nat} (hst : DependStep q x s (.ok t)) : Down t := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hst; exact hd

/-- An `ok` outcome of `depend` keeps the field order of `π` (§64, §63.2; §49, last
paragraph). -/
theorem depend_sib (hs : SibMono π s.P) {q x : Nat} (hst : DependStep q x s (.ok t)) :
    SibMono π t.P := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hst; exact hs

/-! ## O8 `store` (§65) -/

/-- The effects of `store` are related (§65, `ok` effect; §49, last paragraph). -/
theorem storeEff_ren (h : SRel π α s s') (a p : Nat) :
    SRel π α (storeEff s a p) (storeEff s' (α.f a) (π.f p)) := by
  cases hy : s.A[a]? with
  | none =>
    simp only [storeEff, hy, (h.A_none a).1 hy]; exact h
  | some y =>
    obtain ⟨y', hy', hr⟩ := h.A_some hy
    simp only [storeEff, hy, hy']
    exact { h with
      I := fun l => by
        show (if π.f l = π.f p then _ else _) = if l = p then _ else _
        simp only [π.f_inj, h.I]
      Alen := by simp only [List.length_set, h.Alen]
      A := h.setA ⟨hr.mode, hr.origin, hr.footprint, rfl, hr.active⟩
      Afix := fun j hj => h.Afix j (by simpa using hj)
      D := fun q => by
        show List.Perm (if π.f q = π.f p then _ else _) (List.map α.f (if q = p then _ else _))
        by_cases e : q = p
        · subst e
          rw [ite_eq_left rfl, ite_eq_left rfl, List.map_append]
          exact (h.D q).append (.refl _)
        · rw [ite_eq_right (fun e' => e (π.f_inj.1 e')), ite_eq_right e]; exact h.D q }

/-- The effect of `store` keeps downward links (§65, `ok` effect; §49.5; §49, last
paragraph). -/
theorem storeEff_down (hd : Down s) (a p : Nat) : Down (storeEff s a p) := by
  unfold storeEff
  split
  · rename_i y hy; exact down_setA hd hy rfl rfl rfl
  · exact hd

/-- The preconditions of `store` correspond (§65; §49, last paragraph). -/
theorem storePre_ren (hS : Sim π α s s') (a p : Nat) :
    StorePre s' (α.f a) (π.f p) ↔ StorePre s a p := by
  have h := hS.rel; have hd := hS.down; have hd' := hS.down'
  have e1 : OptP (s'.A[α.f a]?) (fun y => y.active = true ∧ y.origin ≠ none ∧
      y.holder = .frame s'.top) False ↔ OptP (s.A[a]?) (fun y => y.active = true ∧
      y.origin ≠ none ∧ y.holder = .frame s.top) False :=
    h.optP_A Iff.rfl (fun y y' hr => by
      simp only [hr.active, hr.origin, ne_eq, Option.map_eq_none_iff, hr.holder, h.top,
        ren_eq_frame]) a
  have e2 := h.usable p
  have e3 := isLeaf_ren h.P p
  have e4 := h.hasRight hd hd' .modify p
  have e5 : (∀ j ∈ List.range s'.A.length,
      OptP (s'.A[j]?) (fun z => z.active = true → z.holder ≠ .place (π.f p)) True) ↔
      ∀ j ∈ List.range s.A.length,
        OptP (s.A[j]?) (fun z => z.active = true → z.holder ≠ .place p) True :=
    α.forall_mem_iff h.mem_rangeA fun j => h.optP_A Iff.rfl (fun z z' hr => by
      simp only [hr.active, hr.holder, ne_eq, ren_eq_place]) j
  have e6 : (∀ l ∈ s'.afp (α.f a), l ∉ footprint s'.P (π.f p) ∧
      ∀ q ∈ List.range s'.P.length, OwnedIn s'.P (π.f p) q → l ∉ footprint s'.P q) ↔
      ∀ l ∈ s.afp a, l ∉ footprint s.P p ∧
        ∀ q ∈ List.range s.P.length, OwnedIn s.P p q → l ∉ footprint s.P q :=
    π.forall_mem_iff (h.mem_afp a) fun l => and_congr (not_congr (h.mem_footprint hd hd' l p))
      (π.forall_mem_iff h.P.mem_range fun q => imp_congr (ownedIn_ren h.P hd.1 hd'.1 p q)
        (not_congr (h.mem_footprint hd hd' l q)))
  have e7 : EffAnchorOK s' (α.f a) (s'.pframe (π.f p)) ↔ EffAnchorOK s a (s.pframe p) := by
    rw [h.pframe]; exact h.effAnchorOK hd hd' a _
  have hE := storeEff_ren h a p
  have hEd := storeEff_down hd a p
  have hEd' := storeEff_down hd' (α.f a) (π.f p)
  have e8 := hE.hasRight hEd hEd' .modify p
  have e9 := hE.anchorOrderHeld hEd hEd'
  exact ⟨fun q => ⟨e1.1 q.derivedHeld, e2.1 q.usable, e3.1 q.leaf, e4.1 q.right, e5.1 q.free,
      e6.1 q.noCover, e7.1 q.anchorOrder, e8.1 q.keepsTarget, e9.1 q.anchorOrderHeld⟩,
    fun q => ⟨e1.2 q.derivedHeld, e2.2 q.usable, e3.2 q.leaf, e4.2 q.right, e5.2 q.free,
      e6.2 q.noCover, e7.2 q.anchorOrder, e8.2 q.keepsTarget, e9.2 q.anchorOrderHeld⟩⟩

/-- The steps of `store` correspond (§65, §58; §49, last paragraph). -/
theorem store_corr (hS : Sim π α s s') (a p : Nat) :
    StepCorr π α (StoreStep a p s) (StoreStep (α.f a) (π.f p) s') :=
  guarded_corr (storePre_ren hS a p) fun _ => storeEff_ren hS.rel a p

/-- An `ok` outcome of `store` keeps downward links (§65; §49.5; §49, last paragraph). -/
theorem store_down (hd : Down s) {a p : Nat} (hst : StoreStep a p s (.ok t)) : Down t := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hst
  exact storeEff_down hd a p

/-- An `ok` outcome of `store` keeps the field order of `π` (§65, §63.2; §49, last
paragraph). -/
theorem store_sib (hs : SibMono π s.P) {a p : Nat} (hst : StoreStep a p s (.ok t)) :
    SibMono π t.P := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hst
  unfold storeEff; split <;> exact hs

/-! ## O9 `read`, O10 `write`, O11 `writeShared` (§66–§68) -/

/-- The preconditions of `read` correspond, for corresponding lists of leaves (§66; §49, last
paragraph). -/
theorem read3Pre_ren (hS : Sim π α s s') (a : Nat) {ls ls' : List Nat}
    (hls : ∀ l, l ∈ ls' ↔ π.g l ∈ ls) : Read3Pre s' (α.f a) ls' ↔ Read3Pre s a ls := by
  have h := hS.rel; have hd := hS.down; have hd' := hS.down'
  have hf := mem_f_of_g hls
  have e1 : (∀ l ∈ ls', LeafOfUsable s' l) ↔ ∀ l ∈ ls, LeafOfUsable s l :=
    π.forall_mem_iff hf (h.leafOfUsable hd hd')
  have e2 : (∀ l ∈ ls', s'.I l = .init) ↔ ∀ l ∈ ls, s.I l = .init :=
    π.forall_mem_iff hf fun l => by rw [h.I]
  have e3 := h.exercisableAt hd hd' a .observe
  have e4 : (∀ l ∈ ls', effective s' (α.f a) l ≠ none) ↔ ∀ l ∈ ls, effective s a l ≠ none :=
    π.forall_mem_iff hf fun l => by rw [h.effective hd hd']
  have e5 : (∀ l ∈ ls', DepsValid s' l) ↔ ∀ l ∈ ls, DepsValid s l :=
    π.forall_mem_iff hf (h.depsValid hd hd')
  exact ⟨fun p => ⟨e1.1 p.usable, e2.1 p.init, e3.1 p.exercisable, e4.1 p.effectivePresent,
      e5.1 p.anchorsValid⟩,
    fun p => ⟨e1.2 p.usable, e2.2 p.init, e3.2 p.exercisable, e4.2 p.effectivePresent,
      e5.2 p.anchorsValid⟩⟩

/-- The steps of `read` correspond (§66, §58; §49, last paragraph). -/
theorem read_corr (hS : Sim π α s s') (a : Nat) (ls : List Nat) :
    StepCorr π α (Read3Step a ls s) (Read3Step (α.f a) (ls.map π.f) s') :=
  guarded_corr (read3Pre_ren hS a (π.mem_map ls)) fun _ => hS.rel

/-- An `ok` outcome of `read` keeps downward links (§66; §49.5; §49, last paragraph). -/
theorem read_down (hd : Down s) {a : Nat} {ls : List Nat} (hst : Read3Step a ls s (.ok t)) :
    Down t := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hst; exact hd

/-- An `ok` outcome of `read` keeps the field order of `π` (§66, §63.2; §49, last paragraph). -/
theorem read_sib (hs : SibMono π s.P) {a : Nat} {ls : List Nat}
    (hst : Read3Step a ls s (.ok t)) : SibMono π t.P := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hst; exact hs

/-- The effects of `write` and `writeShared` are related, for corresponding lists of leaves
(§67, §68, `ok` effect; §49, last paragraph). -/
theorem write3Eff_ren (h : SRel π α s s') {ls ls' : List Nat}
    (hls : ∀ l, l ∈ ls' ↔ π.g l ∈ ls) : SRel π α (write3Eff s ls) (write3Eff s' ls') :=
  { h with
    I := fun l => by
      show (if π.f l ∈ ls' then _ else _) = if l ∈ ls then _ else _
      simp only [mem_f_of_g hls, h.I] }

/-- The preconditions of `write` correspond, for corresponding lists of leaves (§67; §49, last
paragraph). -/
theorem write3Pre_ren (hS : Sim π α s s') (a : Nat) {ls ls' : List Nat}
    (hls : ∀ l, l ∈ ls' ↔ π.g l ∈ ls) : Write3Pre s' (α.f a) ls' ↔ Write3Pre s a ls := by
  have h := hS.rel; have hd := hS.down; have hd' := hS.down'
  have hf := mem_f_of_g hls
  have e1 : (∀ l ∈ ls', LeafOfUsable s' l) ↔ ∀ l ∈ ls, LeafOfUsable s l :=
    π.forall_mem_iff hf (h.leafOfUsable hd hd')
  have e2 := h.exercisableAt hd hd' a .modify
  have e3 : (∀ l ∈ ls', effective s' (α.f a) l = some .modify) ↔
      ∀ l ∈ ls, effective s a l = some .modify :=
    π.forall_mem_iff hf fun l => by rw [h.effective hd hd']
  have e4 : (∀ l ∈ ls', ∀ b ∈ List.range s'.A.length, b ≠ α.f a → effective s' b l = none) ↔
      ∀ l ∈ ls, ∀ b ∈ List.range s.A.length, b ≠ a → effective s b l = none :=
    π.forall_mem_iff hf fun l => α.forall_mem_iff h.mem_rangeA fun b =>
      imp_congr (not_congr α.f_inj) (by rw [h.effective hd hd'])
  have e5 : (∀ l ∈ ls', DepsValid s' l) ↔ ∀ l ∈ ls, DepsValid s l :=
    π.forall_mem_iff hf (h.depsValid hd hd')
  exact ⟨fun p => ⟨e1.1 p.usable, e2.1 p.exercisable, e3.1 p.effectiveModify, e4.1 p.exclusive,
      e5.1 p.anchorsValid⟩,
    fun p => ⟨e1.2 p.usable, e2.2 p.exercisable, e3.2 p.effectiveModify, e4.2 p.exclusive,
      e5.2 p.anchorsValid⟩⟩

/-- The steps of `write` correspond (§67, §58; §49, last paragraph). -/
theorem write_corr (hS : Sim π α s s') (a : Nat) (ls : List Nat) :
    StepCorr π α (Write3Step a ls s) (Write3Step (α.f a) (ls.map π.f) s') :=
  guarded_corr (write3Pre_ren hS a (π.mem_map ls)) fun _ => write3Eff_ren hS.rel (π.mem_map ls)

/-- An `ok` outcome of `write` keeps downward links (§67; §49.5; §49, last paragraph). -/
theorem write_down (hd : Down s) {a : Nat} {ls : List Nat} (hst : Write3Step a ls s (.ok t)) :
    Down t := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hst; exact hd

/-- An `ok` outcome of `write` keeps the field order of `π` (§67, §63.2; §49, last paragraph). -/
theorem write_sib (hs : SibMono π s.P) {a : Nat} {ls : List Nat}
    (hst : Write3Step a ls s (.ok t)) : SibMono π t.P := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hst; exact hs

/-- The preconditions of `writeShared` correspond, for contracts and lists of leaves
corresponding under the renaming (§68, §48; §49, last paragraph). -/
theorem writeSharedPre_ren (hK : KCorr π α k k') (hS : Sim π α s s') (a : Nat)
    {ls ls' : List Nat} (hls : ∀ l, l ∈ ls' ↔ π.g l ∈ ls) :
    WriteSharedPre k' s' (α.f a) ls' ↔ WriteSharedPre k s a ls := by
  have h := hS.rel; have hd := hS.down; have hd' := hS.down'
  have hf := mem_f_of_g hls
  have e1 : (∀ l ∈ ls', LeafOfUsable s' l) ↔ ∀ l ∈ ls, LeafOfUsable s l :=
    π.forall_mem_iff hf (h.leafOfUsable hd hd')
  have e2 : (∀ l ∈ ls', k'.SharedMutable l) ↔ ∀ l ∈ ls, k.SharedMutable l :=
    π.forall_mem_iff hf hK.shared
  have e3 := h.exercisableAt hd hd' a .observe
  have e4 : (∀ l ∈ ls', effective s' (α.f a) l ≠ none) ↔ ∀ l ∈ ls, effective s a l ≠ none :=
    π.forall_mem_iff hf fun l => by rw [h.effective hd hd']
  have e5 : (∀ l ∈ ls', DepsValid s' l) ↔ ∀ l ∈ ls, DepsValid s l :=
    π.forall_mem_iff hf (h.depsValid hd hd')
  exact ⟨fun p => ⟨e1.1 p.usable, e2.1 p.shared, e3.1 p.exercisable, e4.1 p.effectivePresent,
      e5.1 p.depsValid⟩,
    fun p => ⟨e1.2 p.usable, e2.2 p.shared, e3.2 p.exercisable, e4.2 p.effectivePresent,
      e5.2 p.depsValid⟩⟩

/-- The steps of `writeShared` correspond, for contracts corresponding under the renaming (§68,
§48, §58; §49, last paragraph). -/
theorem writeShared_corr_of (hK : KCorr π α k k') (hS : Sim π α s s') (a : Nat)
    (ls : List Nat) :
    StepCorr π α (WriteSharedStep k a ls s) (WriteSharedStep k' (α.f a) (ls.map π.f) s') :=
  guarded_corr (writeSharedPre_ren hK hS a (π.mem_map ls)) fun _ =>
    write3Eff_ren hS.rel (π.mem_map ls)

/-- The steps of `writeShared` correspond, with the renamed contract (§68, §48, §58; §49, last
paragraph). -/
theorem writeShared_corr (hS : Sim π α s s') (a : Nat) (ls : List Nat) :
    StepCorr π α (WriteSharedStep k a ls s)
      (WriteSharedStep (k.rename π α) (α.f a) (ls.map π.f) s') :=
  writeShared_corr_of (KCorr.rename π α k) hS a ls

/-- An `ok` outcome of `writeShared` keeps downward links (§68; §49.5; §49, last paragraph). -/
theorem writeShared_down (hd : Down s) {a : Nat} {ls : List Nat}
    (hst : WriteSharedStep k a ls s (.ok t)) : Down t := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hst; exact hd

/-- An `ok` outcome of `writeShared` keeps the field order of `π` (§68, §63.2; §49, last
paragraph). -/
theorem writeShared_sib (hs : SibMono π s.P) {a : Nat} {ls : List Nat}
    (hst : WriteSharedStep k a ls s (.ok t)) : SibMono π t.P := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hst; exact hs

/-! ## O15 `pin`, O16 `unpin` (§74, §75) -/

/-- Related states have as many pinning obligations (§74, §75; §49, last paragraph). -/
private theorem SRel.pins_length (h : SRel π α s s') : s'.pins.length = s.pins.length := by
  have h1 := (h.pins_none s.pins.length).1 (List.getElem?_eq_none_iff.2 (Nat.le_refl _))
  have h2 := (h.pins_none s'.pins.length).2 (List.getElem?_eq_none_iff.2 (Nat.le_refl _))
  rw [List.getElem?_eq_none_iff] at h1 h2
  omega

/-- The preconditions of `pin` correspond (§74; §49, last paragraph). -/
theorem pinPre_ren (hS : Sim π α s s') (p : Nat) : PinPre s' (π.f p) ↔ PinPre s p := by
  have e1 := hS.rel.usable p
  have e2 := hS.rel.hasRight hS.down hS.down' .modify p
  exact ⟨fun q => ⟨e1.1 q.usable, e2.1 q.right⟩, fun q => ⟨e1.2 q.usable, e2.2 q.right⟩⟩

/-- The effects of `pin` are related; obligations keep their identities (§74, `ok` effect; §75;
§49, last paragraph). -/
theorem pinEff_ren (h : SRel π α s s') (hd : Down s) (hd' : Down s') (p : Nat) :
    SRel π α (pinEff s p) (pinEff s' (π.f p)) :=
  { h with
    pins := fun o => by
      show Option.Rel _ ((s.pins ++ _)[o]?) ((s'.pins ++ _)[o]?)
      rw [List.getElem?_append, List.getElem?_append, h.pins_length]
      by_cases ho : o < s.pins.length
      · rw [ite_eq_left ho, ite_eq_left ho]; exact h.pins o
      · rw [ite_eq_right ho, ite_eq_right ho]
        cases o - s.pins.length with
        | zero => exact .some ⟨rfl, h.footprint_perm hd hd' p, rfl⟩
        | succ i => exact .none }

/-- The steps of `pin` correspond (§74, §58; §49, last paragraph). -/
theorem pin_corr (hS : Sim π α s s') (p : Nat) :
    StepCorr π α (PinStep p s) (PinStep (π.f p) s') :=
  guarded_corr (pinPre_ren hS p) fun _ => pinEff_ren hS.rel hS.down hS.down' p

/-- An `ok` outcome of `pin` keeps downward links (§74; §49.5; §49, last paragraph). -/
theorem pin_down (hd : Down s) {p : Nat} (hst : PinStep p s (.ok t)) : Down t := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hst; exact hd

/-- An `ok` outcome of `pin` keeps the field order of `π` (§74, §63.2; §49, last paragraph). -/
theorem pin_sib (hs : SibMono π s.P) {p : Nat} (hst : PinStep p s (.ok t)) : SibMono π t.P := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hst; exact hs

/-- The preconditions of `unpin` correspond, for contracts corresponding under the renaming; the
obligation identity is kept (§75, §48; §49, last paragraph). -/
theorem unpinPre_ren (hK : KCorr π α k k') (hS : Sim π α s s') (o : Nat) :
    UnpinPre k' s' o ↔ UnpinPre k s o := by
  have h := hS.rel; have hd := hS.down; have hd' := hS.down'
  have e1 : OptP (s'.pins[o]?) (fun ob => ob.active = true) False ↔
      OptP (s.pins[o]?) (fun ob => ob.active = true) False :=
    h.optP_pins Iff.rfl (fun ob ob' hr => by rw [hr.active]) o
  have e2 : OptP (s'.pins[o]?) (fun ob => s'.Usable ob.place) False ↔
      OptP (s.pins[o]?) (fun ob => s.Usable ob.place) False :=
    h.optP_pins Iff.rfl (fun ob ob' hr => by rw [hr.place]; exact h.usable _) o
  have e3 : OptP (s'.pins[o]?) (fun ob => HasRight s' .modify ob.place) False ↔
      OptP (s.pins[o]?) (fun ob => HasRight s .modify ob.place) False :=
    h.optP_pins Iff.rfl (fun ob ob' hr => by rw [hr.place]; exact h.hasRight hd hd' .modify _) o
  have e4 := hK.done o
  exact ⟨fun p => ⟨e1.1 p.active, e2.1 p.usable, e3.1 p.right, e4.1 p.externalDone⟩,
    fun p => ⟨e1.2 p.active, e2.2 p.usable, e3.2 p.right, e4.2 p.externalDone⟩⟩

/-- The effects of `unpin` are related; obligations keep their identities (§75, `ok` effect;
§49, last paragraph). -/
theorem unpinEff_ren (h : SRel π α s s') (o : Nat) : SRel π α (unpinEff s o) (unpinEff s' o) :=
  { h with
    pins := fun i => by
      rw [pins_unpinEff, pins_unpinEff]
      by_cases e : o = i
      · rw [ite_eq_left e, ite_eq_left e]
        cases hob : s.pins[i]? with
        | none => rw [(h.pins_none i).1 hob]; exact .none
        | some ob =>
          obtain ⟨ob', hob', hr⟩ := h.pins_some hob
          rw [hob']; exact .some ⟨hr.place, hr.leaves, rfl⟩
      · rw [ite_eq_right e, ite_eq_right e]; exact h.pins i }

/-- The steps of `unpin` correspond, for contracts corresponding under the renaming (§75, §48,
§58; §49, last paragraph). -/
theorem unpin_corr_of (hK : KCorr π α k k') (hS : Sim π α s s') (o : Nat) :
    StepCorr π α (UnpinStep k o s) (UnpinStep k' o s') :=
  guarded_corr (unpinPre_ren hK hS o) fun _ => unpinEff_ren hS.rel o

/-- The steps of `unpin` correspond, with the renamed contract (§75, §48, §58; §49, last
paragraph). -/
theorem unpin_corr (hS : Sim π α s s') (o : Nat) :
    StepCorr π α (UnpinStep k o s) (UnpinStep (k.rename π α) o s') :=
  unpin_corr_of (KCorr.rename π α k) hS o

/-- An `ok` outcome of `unpin` keeps downward links (§75; §49.5; §49, last paragraph). -/
theorem unpin_down (hd : Down s) {o : Nat} (hst : UnpinStep k o s (.ok t)) : Down t := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hst; exact hd

/-- An `ok` outcome of `unpin` keeps the field order of `π` (§75, §63.2; §49, last
paragraph). -/
theorem unpin_sib (hs : SibMono π s.P) {o : Nat} (hst : UnpinStep k o s (.ok t)) :
    SibMono π t.P := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hst; exact hs

end Ern.MemoryModel.Access.Rename
