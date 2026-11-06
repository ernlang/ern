import Ern.MemoryModel.Access.Rename.Derived

/-!
# Renaming of identities: `enterFrame` and `exitFrame`

Correspondence of the operations O6 `enterFrame` (§72) and O7 `exitFrame` (§73) of
`specs/ERN_Memory_Model_Specification.md` under a renaming of identities (§49, last
paragraph): related effects, invariant preconditions, corresponding outcomes (§58), and the order
facts `Down` and `SibMono` kept by an `ok` step. Parameters are renamed; the shape of the locals is
not (its parents are fresh, §72.2).
-/

namespace Ern.MemoryModel.Access.Rename

variable {π α : Ren} {s s' : S3} {k k' : K}

/-! ## O6 `enterFrame` (§72) -/

/-- Holder renamed to a frame (§39: frames are not renamed; §49, last paragraph). -/
private theorem enter_ren_eq_frame (π : Ren) (o : Holder) (f : Nat) :
    o.ren π = .frame f ↔ o = .frame f :=
  Holder.ren_inj π (b := .frame f)

/-- Authority `x` after `enterFrame` (§72 `ok` effect). -/
private theorem enter_A_get (s : S3) (ps : List Nat) (ls : LocalShape) (x : Nat) :
    (enterEff s ps ls).A[x]? = if x < s.A.length then
      (s.A[x]?).map (fun y => if x ∈ ps then { y with holder := .frame s.nF } else y)
    else ((rootIdx ls.toShape)[x - s.A.length]?).map fun i =>
      ⟨.modify, none, footprint (enterP s ls) (s.P.length + i), .frame s.nF, true⟩ := by
  split
  · rename_i hx; exact Frames.enter_lt hx
  · rename_i hx
    simp only [enterEff]
    rw [List.getElem?_append_right (by rw [length_mapI]; omega), length_mapI, List.getElem?_map]
    simp only [Frames.shapeOwner_toShape]

/-- The places after `enterFrame` on related states are related, the shape of the locals not
renamed (§72 `ok` effect; §72.2: fresh parents; §49, last paragraph). -/
theorem enterP_ren (h : SRel π α s s') (ls : LocalShape) (hok : ShapeOK s.P.length ls.toShape) :
    PRel π (enterP s ls) (enterP s' ls) := by
  show PRel π (shapeP s.P (.frame s.nF) _) (shapeP s'.P (.frame s'.nF) _)
  rw [h.nF]; exact shapeP_ren h.P hok _

/-- The effects of `enterFrame` on related states are related, parameters renamed and the shape
of the locals not renamed (§72 `ok` effect; §72.2: fresh parents; §49, last paragraph). -/
theorem enterEff_ren (h : SRel π α s s') (hd : Down s) (hd' : Down s') (ps : List Nat)
    (ls : LocalShape) (hok : ShapeOK s.P.length ls.toShape) :
    SRel π α (enterEff s ps ls) (enterEff s' (ps.map α.f) ls) := by
  have hle : ∀ q, s'.P.length ≤ π.f q ↔ s.P.length ≤ q := fun q => by
    have := h.P.lt_iff q; omega
  have hPe := enterP_ren h ls hok
  have hdPe : DownP (enterP s ls) := shapeP_down hd.1 hok
  have hdPe' : DownP (enterP s' ls) := shapeP_down hd'.1 (by rw [h.P.len]; exact hok)
  refine
    { F := ?_, nF := ?_, P := hPe, I := ?_, Alen := ?_, A := ?_, Afix := ?_, D := ?_,
      dead := ?_, pins := h.pins }
  · show s'.nF :: s'.F = s.nF :: s.F; rw [h.nF, h.F]
  · show s'.nF + 1 = s.nF + 1; rw [h.nF]
  · intro l
    show (if s'.P.length ≤ π.f l then InitSt.uninit else s'.I (π.f l)) =
      if s.P.length ≤ l then InitSt.uninit else s.I l
    by_cases hl : s.P.length ≤ l
    · rw [ite_eq_left ((hle l).2 hl), ite_eq_left hl]
    · rw [ite_eq_right (fun e => hl ((hle l).1 e)), ite_eq_right hl, h.I]
  · simp only [enterEff, List.length_append, length_mapI, List.length_map, h.Alen]
  · intro x
    rw [enter_A_get, enter_A_get]
    by_cases hx : x < s.A.length
    · rw [ite_eq_left ((h.Alt x).2 hx), ite_eq_left hx]
      cases hy : s.A[x]? with
      | none => rw [(h.A_none x).1 hy]; exact .none
      | some y =>
        obtain ⟨y', hy', hr⟩ := h.A_some hy
        rw [hy', Option.map_some, Option.map_some]
        refine .some ?_
        by_cases hp : x ∈ ps
        · rw [ite_eq_left ((α.mem_map_f ps x).2 hp), ite_eq_left hp, h.nF]
          exact ⟨hr.mode, hr.origin, hr.footprint, rfl, hr.active⟩
        · rw [ite_eq_right (fun e => hp ((α.mem_map_f ps x).1 e)), ite_eq_right hp]
          exact hr
    · have hfx := h.Afix x (by omega)
      rw [ite_eq_right (show ¬ α.f x < s'.A.length by rw [hfx, h.Alen]; exact hx),
        ite_eq_right hx, hfx,
        h.Alen, h.P.len, h.nF]
      cases (rootIdx ls.toShape)[x - s.A.length]? with
      | none => exact .none
      | some i =>
        refine .some ⟨rfl, rfl, ?_, rfl, rfl⟩
        have := footprint_perm_ren hPe hdPe hdPe' (s.P.length + i)
        rwa [h.P.fix _ (Nat.le_add_right _ _)] at this
  · intro x hx
    simp only [enterEff, List.length_append, length_mapI] at hx
    exact h.Afix x (by omega)
  · intro q
    show (if s'.P.length ≤ π.f q then [] else s'.D (π.f q)).Perm
      ((if s.P.length ≤ q then [] else s.D q).map α.f)
    by_cases hq : s.P.length ≤ q
    · rw [ite_eq_left ((hle q).2 hq), ite_eq_left hq]; exact .nil
    · rw [ite_eq_right (fun e => hq ((hle q).1 e)), ite_eq_right hq]; exact h.D q
  · intro q
    show (if s'.P.length ≤ π.f q then false else s'.dead (π.f q)) =
      if s.P.length ≤ q then false else s.dead q
    by_cases hq : s.P.length ≤ q
    · rw [ite_eq_left ((hle q).2 hq), ite_eq_left hq]
    · rw [ite_eq_right (fun e => hq ((hle q).1 e)), ite_eq_right hq, h.dead]

/-- `enterFrame` keeps parent and origin links downward (§72 `ok` effect, §72.2: locals have
earlier parents, root authorities of locals have no origin; §49, last paragraph). -/
theorem enterEff_down {ps : List Nat} {ls : LocalShape} (hd : Down s)
    (hok : ShapeOK s.P.length ls.toShape) : Down (enterEff s ps ls) := by
  refine ⟨shapeP_down hd.1 hok, fun j o hj => ?_⟩
  obtain ⟨z, hz, hzo⟩ := Option.bind_eq_some_iff.1 hj
  rcases Frames.enter_get hz with ⟨_, y, hy, rfl⟩ | ⟨_, i, _, rfl⟩
  · apply hd.2 j o
    simp only [S3.org, hy, Option.bind_some]
    split at hzo <;> exact hzo
  · cases hzo

/-- Origin protection on entry is invariant (§72.3; §49, last paragraph). -/
theorem SRel.paramOriginHidden (h : SRel π α s s') (hd : Down s) (hd' : Down s') (p : Nat) :
    ParamOriginHidden s' (α.f p) ↔ ParamOriginHidden s p := by
  unfold ParamOriginHidden
  cases hy : s.A[p]? with
  | none => rw [(h.A_none p).1 hy]; exact Iff.rfl
  | some y =>
    obtain ⟨y', hy', hr⟩ := h.A_some hy
    rw [hy']
    simp only [OptP, hr.mode, hr.origin]
    cases y.origin with
    | none => exact Iff.rfl
    | some o => simp only [Option.map_some, h.exercisableAt hd hd']

/-- The preconditions of `enterFrame` are invariant, parameters renamed and the shape of the
locals not renamed (§72.1–§72.4; §49, last paragraph). -/
theorem enterPre_ren (hS : Sim π α s s') (ps : List Nat) (ls : LocalShape) :
    EnterPre s' (ps.map α.f) ls ↔ EnterPre s ps ls := by
  have h := hS.rel
  have hpar : (∀ a ∈ ps.map α.f, OptP (s'.A[a]?) (fun y => y.active = true ∧
        y.holder = .frame s'.top ∧ y.origin ≠ none) False) ↔
      ∀ a ∈ ps, OptP (s.A[a]?) (fun y => y.active = true ∧ y.holder = .frame s.top ∧
        y.origin ≠ none) False := by
    rw [List.forall_mem_map]
    refine forall_congr' fun a => imp_congr_right fun _ => ?_
    cases hy : s.A[a]? with
    | none => rw [(h.A_none a).1 hy]; exact Iff.rfl
    | some y =>
      obtain ⟨y', hy', hr⟩ := h.A_some hy
      rw [hy']
      simp only [OptP, hr.active, hr.holder, h.top, hr.origin, ne_eq, Option.map_eq_none_iff,
        enter_ren_eq_frame]
  have hl : ShapeOK s'.P.length ls.toShape ↔ ShapeOK s.P.length ls.toShape := by rw [h.P.len]
  have hrest : ShapeOK s.P.length ls.toShape →
      ((∀ p ∈ ps.map α.f, ParamOriginHidden (enterEff s' (ps.map α.f) ls) p) ∧
        AnchorOrderHeld (enterEff s' (ps.map α.f) ls) ↔
      (∀ p ∈ ps, ParamOriginHidden (enterEff s ps ls) p) ∧
        AnchorOrderHeld (enterEff s ps ls)) := by
    intro hok
    have he := enterEff_ren h hS.down hS.down' ps ls hok
    have hdE : Down (enterEff s ps ls) := enterEff_down hS.down hok
    have hdE' : Down (enterEff s' (ps.map α.f) ls) := enterEff_down hS.down' (hl.2 hok)
    rw [List.forall_mem_map]
    exact and_congr (forall_congr' fun p => imp_congr_right fun _ =>
      he.paramOriginHidden hdE hdE' p) (he.anchorOrderHeld hdE hdE')
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    have hok := hl.1 h3
    obtain ⟨h4', h5'⟩ := (hrest hok).1 ⟨h4, h5⟩
    exact ⟨by rwa [h.F] at h1, hpar.1 h2, hok, h4', h5'⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    obtain ⟨h4', h5'⟩ := (hrest h3).2 ⟨h4, h5⟩
    exact ⟨by rwa [h.F], hpar.2 h2, hl.2 h3, h4', h5'⟩

/-- `enterFrame` on related states has corresponding outcomes, parameters renamed and the shape of
the locals not renamed (§72, §58; §49, last paragraph). -/
theorem enter_corr (hS : Sim π α s s') (ps : List Nat) (ls : LocalShape) :
    StepCorr π α (EnterStep ps ls s) (EnterStep (ps.map α.f) ls s') :=
  guarded_corr (enterPre_ren hS ps ls) fun hpre =>
    enterEff_ren hS.rel hS.down hS.down' ps ls hpre.localsOK

/-- An `ok` step of `enterFrame` keeps parent and origin links downward (§72; §49, last
paragraph). -/
theorem enter_down {ps : List Nat} {ls : LocalShape} {t : S3} (hd : Down s)
    (h : EnterStep ps ls s (.ok t)) : Down t := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  exact enterEff_down hd hpre.localsOK

/-- An `ok` step of `enterFrame` keeps the field order of `π` (§63.2, §72; §49, last
paragraph). -/
theorem enter_sib {ps : List Nat} {ls : LocalShape} {t : S3} (hP : PRel π s.P s'.P)
    (hs : SibMono π s.P) (h : EnterStep ps ls s (.ok t)) : SibMono π t.P := by
  obtain ⟨_, rfl⟩ := Guarded.ok_iff.1 h
  exact shapeP_sib hP hs

/-! ## O7 `exitFrame` (§73) -/

/-- Survival at the exit is invariant (§73.4; §49, last paragraph). -/
theorem SRel.survives (h : SRel π α s s') (F₀ : Frames) (x : Nat) :
    Survives s' F₀ (α.f x) ↔ Survives s F₀ x := by
  unfold Survives
  cases hy : s.A[x]? with
  | none => rw [(h.A_none x).1 hy]; exact Iff.rfl
  | some y =>
    obtain ⟨y', hy', hr⟩ := h.A_some hy
    rw [hy']
    simp only [OptP, hr.active, hr.holder, (h.withF F₀).holderLive]

/-- The first surviving element of a renamed list is the renamed first surviving element
(§73.4; §49, last paragraph). -/
theorem SRel.firstSurv (h : SRel π α s s') (F₀ : Frames) (l : List Nat) :
    Access.firstSurv s' F₀ (l.map α.f) = (Access.firstSurv s F₀ l).map α.f := by
  unfold Access.firstSurv
  rw [List.find?_map]
  congr 2
  funext z
  simp only [Function.comp, h.survives]

/-- Authorities after the exit correspond (§73 `ok` effect, second and third items; §73.4; §49,
last paragraph). -/
theorem SRel.exitG (h : SRel π α s s') (hd : Down s) (hd' : Down s') (F₀ : Frames) (a : Nat)
    {y y' : Authority} (hr : AuthRel π α y y') :
    AuthRel π α (Access.exitG s F₀ a y) (Access.exitG s' F₀ (α.f a) y') := by
  unfold Access.exitG
  by_cases hs : Survives s F₀ a
  · rw [ite_eq_left ((h.survives F₀ a).2 hs), ite_eq_left hs]
    cases ho : y.origin with
    | none =>
      have ho' : y'.origin = none := by rw [hr.origin, ho]; rfl
      simp only [ho']
      exact hr
    | some o =>
      have ho' : y'.origin = some (α.f o) := by rw [hr.origin, ho]; rfl
      simp only [ho']
      refine ⟨hr.mode, ?_, hr.footprint, hr.holder, hr.active⟩
      show Access.firstSurv s' F₀ (s'.ancs (α.f a)) =
        (Access.firstSurv s F₀ (s.ancs a)).map α.f
      rw [h.ancs hd hd', h.firstSurv]
  · rw [ite_eq_right (fun e => hs ((h.survives F₀ a).1 e)), ite_eq_right hs]
    exact ⟨hr.mode, hr.origin, hr.footprint, hr.holder, rfl⟩

/-- The effects of `exitFrame` on related states are related (§73 `ok` effect; §49, last
paragraph). -/
theorem exitEff_ren (h : SRel π α s s') (hd : Down s) (hd' : Down s') :
    SRel π α (exitEff s) (exitEff s') := by
  have hFt : s'.F.tail = s.F.tail := by rw [h.F]
  refine
    { F := hFt, nF := h.nF, P := h.P, I := h.I, Alen := ?_, A := ?_, Afix := ?_, D := ?_,
      dead := h.dead, pins := h.pins }
  · simp only [exitEff, length_mapI, h.Alen]
  · intro x
    rw [Frames.exit_A_get, Frames.exit_A_get, hFt]
    cases hy : s.A[x]? with
    | none => rw [(h.A_none x).1 hy]; exact .none
    | some y =>
      obtain ⟨y', hy', hr⟩ := h.A_some hy
      rw [hy']
      exact .some (h.exitG hd hd' _ x hr)
  · intro x hx
    simp only [exitEff, length_mapI] at hx
    exact h.Afix x hx
  · intro q
    show ((s'.D (π.f q)).map fun x => (Access.firstSurv s' s'.F.tail (x :: s'.ancs x)).getD x).Perm
      (((s.D q).map fun x => (Access.firstSurv s s.F.tail (x :: s.ancs x)).getD x).map α.f)
    rw [hFt]
    refine ((h.D q).map _).trans (.of_eq ?_)
    rw [List.map_map, List.map_map]
    refine List.map_congr_left fun x _ => ?_
    show (Access.firstSurv s' s.F.tail (α.f x :: s'.ancs (α.f x))).getD (α.f x) =
      α.f ((Access.firstSurv s s.F.tail (x :: s.ancs x)).getD x)
    rw [h.ancs hd hd', ← List.map_cons, h.firstSurv, Option.getD_map]

/-- `exitFrame` keeps parent and origin links downward (§73 `ok` effect: a new origin is an
earlier origin of the chain; §49, last paragraph). -/
theorem exitEff_down (hd : Down s) : Down (exitEff s) := by
  refine ⟨hd.1, fun j o hj => ?_⟩
  obtain ⟨z, hz, hzo⟩ := Option.bind_eq_some_iff.1 hj
  obtain ⟨y, hy, rfl⟩ := Frames.exit_get hz
  rcases Frames.exitG_origin (s := s) (F₀ := s.F.tail) (a := j) (y := y) with he | ⟨_, _, he⟩
  · rw [he] at hzo
    exact hd.2 j o (by simp only [S3.org, hy, Option.bind_some, hzo])
  · rw [he] at hzo
    exact chain_lt (Frames.firstSurv_some hzo).1

/-- The preconditions of `exitFrame` as a conjunction (§73.1–§73.5). -/
private theorem exit_pre_iff (k : K) (s : S3) : ExitPre k s ↔ s.F.tail ≠ [] ∧
    (∀ q ∈ List.range s.P.length, ({ s with F := s.F.tail } : S3).Usable q →
      ∀ x ∈ s.D q, Access.firstSurv s s.F.tail (x :: s.ancs x) ≠ none) ∧
    (∀ a ∈ List.range s.A.length, Survives s s.F.tail a → s.org a ≠ none →
      Access.firstSurv s s.F.tail (s.ancs a) ≠ none) ∧
    (∀ q ∈ List.range s.P.length, s.Usable q → ¬ ({ s with F := s.F.tail } : S3).Usable q →
      ∀ l ∈ footprint s.P q, s.pin l = false ∧ ¬ k.Pinned l) ∧
    AnchorOrderHeld (exitEff s) :=
  ⟨fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩,
   fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩⟩

/-- The preconditions of `exitFrame` are invariant, for any contracts corresponding under the
renaming (§73.1–§73.5, §48; §49, last paragraph). -/
theorem exitPre_ren (hK : KCorr π α k k') (hS : Sim π α s s') :
    ExitPre k' s' ↔ ExitPre k s := by
  have h := hS.rel
  have hd := hS.down
  have hd' := hS.down'
  have hFt : s'.F.tail = s.F.tail := by rw [h.F]
  have hF := h.withF s.F.tail
  have hfs : ∀ l, Access.firstSurv s' s.F.tail (l.map α.f) = none ↔
      Access.firstSurv s s.F.tail l = none := fun l => by
    rw [h.firstSurv, Option.map_eq_none_iff]
  rw [exit_pre_iff, exit_pre_iff, hFt]
  refine and_congr Iff.rfl (and_congr ?_ (and_congr ?_ (and_congr ?_ ?_)))
  · refine π.forall_mem_iff h.P.mem_range fun q => imp_congr (hF.usable q) ?_
    refine α.forall_mem_iff (h.mem_D q) fun x => not_congr ?_
    rw [h.ancs hd hd', ← List.map_cons, hfs]
  · refine α.forall_mem_iff h.mem_rangeA fun a => imp_congr (h.survives _ a) ?_
    refine imp_congr (not_congr ?_) (not_congr ?_)
    · rw [h.org, Option.map_eq_none_iff]
    · rw [h.ancs hd hd', hfs]
  · refine π.forall_mem_iff h.P.mem_range fun q => imp_congr (h.usable q) ?_
    refine imp_congr (not_congr (hF.usable q)) ?_
    refine π.forall_mem_iff (fun l => h.mem_footprint hd hd' l q) fun l => ?_
    exact and_congr (by rw [h.pin]) (not_congr (hK.pinned l))
  · exact (exitEff_ren h hd hd').anchorOrderHeld (exitEff_down hd) (exitEff_down hd')

/-- `exitFrame` on related states has corresponding outcomes, for any contracts corresponding
under the renaming (§73, §58; §49, last paragraph). -/
theorem exit_corr_of (hK : KCorr π α k k') (hS : Sim π α s s') :
    StepCorr π α (ExitStep k s) (ExitStep k' s') :=
  guarded_corr (exitPre_ren hK hS) fun _ => exitEff_ren hS.rel hS.down hS.down'

/-- `exitFrame` on related states has corresponding outcomes under the renamed contract (§73,
§58, §48; §49, last paragraph). -/
theorem exit_corr (hS : Sim π α s s') :
    StepCorr π α (ExitStep k s) (ExitStep (k.rename π α) s') :=
  exit_corr_of (KCorr.rename π α k) hS

/-- An `ok` step of `exitFrame` keeps parent and origin links downward (§73; §49, last
paragraph). -/
theorem exit_down {t : S3} (hd : Down s) (h : ExitStep k s (.ok t)) : Down t := by
  obtain ⟨_, rfl⟩ := Guarded.ok_iff.1 h
  exact exitEff_down hd

/-- An `ok` step of `exitFrame` keeps the field order of `π`: places are unchanged (§63.2, §73;
§49, last paragraph). -/
theorem exit_sib {t : S3} (_hP : PRel π s.P s'.P) (hs : SibMono π s.P)
    (h : ExitStep k s (.ok t)) : SibMono π t.P := by
  obtain ⟨_, rfl⟩ := Guarded.ok_iff.1 h
  exact hs

end Ern.MemoryModel.Access.Rename
