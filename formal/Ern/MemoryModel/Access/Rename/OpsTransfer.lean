import Ern.MemoryModel.Access.Rename.Derived

/-!
# Renaming of identities: `transfer`

Equivariance of O4 `transfer` (`specs/ERN_Memory_Model_Specification_v0.1.md` §63) under related
states (§38; §49, last paragraph): the helpers of its preconditions (§63.4, §63.6–§63.8), its `ok`
effect, its preconditions (§63.1–§63.9) and the correspondence of its outcomes (§58). Positional
field identity (§63.2) needs `SibMono`.

Iff lemmas are proved in one direction and closed by symmetry (`SRel.symm`, `Sim.symm`,
`KCorr.symm`).
-/

namespace Ern.MemoryModel.Access.Rename

variable {π α : Ren} {s s' : S3} {k k' : K}

/-! ## Effect (§63, `ok` effect) -/

/-- A transfer keeps the origin links (§63, `ok` effect: only holders change). -/
private theorem transfer_org (s : S3) (src dst j : Nat) :
    (transferEff s src dst).org j = s.org j := by
  simp only [S3.org, transfer_A_get]
  cases s.A[j]? with
  | none => rfl
  | some y => simp only [Option.map_some, Option.bind_some]; split <;> rfl

/-- Parent and origin links stay downward after a transfer (§63, `ok` effect; §49.2, §49.5;
§49, last paragraph). -/
theorem transferEff_down (hd : Down s) (src dst : Nat) : Down (transferEff s src dst) :=
  ⟨fun j o hj => hd.1 j o (by rwa [transfer_parentOf] at hj),
   fun j o hj => hd.2 j o (by rwa [transfer_org] at hj)⟩

/-- Anchors moved onto a place correspond up to permutation (§63, `ok` effect, fourth item; §63.2;
§44: `D(p)` is a set; §49, last paragraph). -/
theorem movedTo_perm_ren (h : SRel π α s s') (hd : Down s) (hd' : Down s') (hs : SibMono π s.P)
    (src dst q : Nat) :
    (movedTo s' (π.f src) (π.f dst) (π.f q)).Perm ((movedTo s src dst q).map α.f) :=
  h.filter_flatMap_D fun r => decide_eq_decide.2 (and_congr (partOf_ren h.P hd.1 hd'.1 r src)
    (by rw [corr_ren h.P hd.1 hd'.1 hs]; exact π.option_map_eq_some _ _))

/-- The effect of a transfer is equivariant when `π` keeps field order (§63, `ok` effect; §63.2;
§49, last paragraph). -/
theorem transferEff_ren (h : SRel π α s s') (hd : Down s) (hd' : Down s') (hs : SibMono π s.P)
    (src dst : Nat) : SRel π α (transferEff s src dst) (transferEff s' (π.f src) (π.f dst)) where
  F := h.F
  nF := h.nF
  P := {
    len := by rw [transfer_len, transfer_len]; exact h.P.len
    get := fun q => by
      rw [transfer_P_get, transfer_P_get, h.P.get]
      cases s.P[q]? with
      | none => rfl
      | some pl =>
        have hh := heldIn_ren h.P hd.1 hd'.1 src pl.owner
        simp only [Option.map_some, Place.ren]
        by_cases hpl : heldIn s.P src pl.owner
        · rw [ite_eq_left (hh.2 hpl), ite_eq_left hpl, mvTo_ren h.P hd.1 hd'.1 hs]
        · rw [ite_eq_right (mt hh.1 hpl), ite_eq_right hpl]
    fix := fun q hq => h.P.fix q (by rwa [transfer_len] at hq) }
  I l := by
    show (if π.f l ∈ footprint s'.P (π.f dst) then _ else
      if π.f l ∈ footprint s'.P (π.f src) then _ else s'.I (π.f l)) =
      (if l ∈ footprint s.P dst then _ else if l ∈ footprint s.P src then _ else s.I l)
    simp only [h.mem_footprint hd hd', h.I]
  Alen := by simp only [transferEff, List.length_map]; exact h.Alen
  A x := by
    rw [transfer_A_get, transfer_A_get]
    cases hy : s.A[x]? with
    | none => rw [(h.A_none x).1 hy]; exact .none
    | some y =>
      obtain ⟨y', hy', hr⟩ := h.A_some hy
      rw [hy']
      refine .some ?_
      have hh := heldIn_ren h.P hd.1 hd'.1 src y.holder
      rw [← hr.holder] at hh
      dsimp only
      by_cases hyh : heldIn s.P src y.holder
      · rw [ite_eq_left (hh.2 hyh), ite_eq_left hyh]
        refine { hr with holder := ?_ }
        show mvTo s'.P (π.f src) (π.f dst) y'.holder = _
        rw [hr.holder, mvTo_ren h.P hd.1 hd'.1 hs]
      · rw [ite_eq_right (mt hh.1 hyh), ite_eq_right hyh]; exact hr
  Afix x hx := h.Afix x (by simpa only [transferEff, List.length_map] using hx)
  D q := by
    show (if partOf s'.P (π.f q) (π.f src) then [] else
      s'.D (π.f q) ++ movedTo s' (π.f src) (π.f dst) (π.f q)).Perm
      ((if partOf s.P q src then [] else s.D q ++ movedTo s src dst q).map α.f)
    by_cases hq : partOf s.P q src
    · have hq' := (partOf_ren h.P hd.1 hd'.1 q src).2 hq
      rw [ite_eq_left hq', ite_eq_left hq]; exact .nil
    · have hq' := mt (partOf_ren h.P hd.1 hd'.1 q src).1 hq
      rw [ite_eq_right hq', ite_eq_right hq, List.map_append]
      exact (h.D q).append (movedTo_perm_ren h hd hd' hs src dst q)
  dead := h.dead
  pins := h.pins

/-! ## Helpers of the preconditions (§63.4, §63.6–§63.8) -/

/-- `ActiveDerivedOutside` is invariant (§63.4; §49, last paragraph). -/
theorem SRel.activeDerivedOutside (h : SRel π α s s') (hd : Down s) (hd' : Down s')
    (src j : Nat) : ActiveDerivedOutside s' (π.f src) (α.f j) ↔ ActiveDerivedOutside s src j := by
  unfold ActiveDerivedOutside
  cases hy : s.A[j]? with
  | none => rw [(h.A_none j).1 hy]; exact Iff.rfl
  | some y =>
    obtain ⟨y', hy', hr⟩ := h.A_some hy
    rw [hy']
    simp only [OptP, hr.active, hr.origin, hr.holder, heldIn_ren h.P hd.1 hd'.1, Ne,
      Option.map_eq_none_iff]
    exact and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ =>
      π.exists_mem_iff hr.mem_footprint fun l => h.mem_footprint hd hd' l src

/-- `HolderMoves` is invariant (§63.6, §63.7; §49, last paragraph). -/
theorem SRel.holderMoves (h : SRel π α s s') (hd : Down s) (hd' : Down s') (src : Nat)
    (o : Holder) : HolderMoves s' (π.f src) (o.ren π) ↔ HolderMoves s src o := by
  cases o with
  | frame f => exact Iff.rfl
  | place p =>
    exact or_congr (partOf_ren h.P hd.1 hd'.1 p src) (ownedIn_ren h.P hd.1 hd'.1 src p)

/-- `AnchorMoves` is invariant (§63.7; §49, last paragraph). -/
theorem SRel.anchorMoves (h : SRel π α s s') (hd : Down s) (hd' : Down s') (src x : Nat) :
    AnchorMoves s' (π.f src) (α.f x) ↔ AnchorMoves s src x := by
  unfold AnchorMoves
  cases hy : s.A[x]? with
  | none => rw [(h.A_none x).1 hy]; exact Iff.rfl
  | some y =>
    obtain ⟨y', hy', hr⟩ := h.A_some hy
    rw [hy']; simp only [OptP, hr.holder]; exact h.holderMoves hd hd' src y.holder

/-- Dependencies following the value correspond up to permutation (§63.6; §44: `D(p)` is a set;
§49, last paragraph). -/
private theorem movedDeps_perm_ren (h : SRel π α s s') (hd : Down s) (hd' : Down s')
    (src : Nat) : (movedDeps s' (π.f src)).Perm ((movedDeps s src).map α.f) :=
  h.filter_flatMap_D fun r => decide_eq_decide.2 (or_congr (partOf_ren h.P hd.1 hd'.1 r src)
    (and_congr (ownedIn_ren h.P hd.1 hd'.1 src r) (h.usable r)))

/-- Membership in the dependencies following the value is invariant (§63.6; §49, last
paragraph). -/
theorem SRel.mem_movedDeps (h : SRel π α s s') (hd : Down s) (hd' : Down s') (src x : Nat) :
    α.f x ∈ movedDeps s' (π.f src) ↔ x ∈ movedDeps s src :=
  (movedDeps_perm_ren h hd hd' src).mem_iff.trans (α.mem_map_f _ _)

/-- Leaves of a holder are invariant (§63.8; §49, last paragraph). -/
theorem SRel.mem_holderLeaves (h : SRel π α s s') (hd : Down s) (hd' : Down s') (o : Holder)
    (l : Nat) : π.f l ∈ holderLeaves s' (o.ren π) ↔ l ∈ holderLeaves s o := by
  cases o with
  | frame f => simp only [holderLeaves, Holder.ren, List.not_mem_nil]
  | place p => exact h.mem_footprint hd hd' l p

/-- `SelfLock` is invariant (§63.8; §49, last paragraph). -/
theorem SRel.selfLock (h : SRel π α s s') (hd : Down s) (hd' : Down s') (a : Nat) :
    SelfLock s' (α.f a) ↔ SelfLock s a := by
  unfold SelfLock
  cases hy : s.A[a]? with
  | none => rw [(h.A_none a).1 hy]; exact Iff.rfl
  | some y =>
    obtain ⟨y', hy', hr⟩ := h.A_some hy
    rw [hy']
    simp only [OptP, hr.active, hr.holder]
    exact and_congr_right fun _ =>
      π.exists_mem_iff hr.mem_footprint fun l => h.mem_holderLeaves hd hd' y.holder l

/-- Local self-blocking prevention is invariant (§63.8; §49, last paragraph). -/
theorem noLocalSelfLock_ren (hS : Sim π α s s') (src dst : Nat) :
    NoLocalSelfLock s' (π.f src) (π.f dst) ↔ NoLocalSelfLock s src dst := by
  have he := transferEff_ren hS.rel hS.down hS.down' hS.sib src dst
  unfold NoLocalSelfLock
  refine α.forall_mem_iff hS.rel.mem_rangeA fun j => imp_congr ?_ (not_congr
    (he.selfLock (transferEff_down hS.down src dst) (transferEff_down hS.down' _ _) j))
  cases hy : s.A[j]? with
  | none => rw [(hS.rel.A_none j).1 hy]; exact Iff.rfl
  | some y =>
    obtain ⟨y', hy', hr⟩ := hS.rel.A_some hy
    rw [hy']; simp only [OptP, hr.holder]
    exact heldIn_ren hS.rel.P hS.down.1 hS.down'.1 src y.holder

/-! ## Preconditions and outcomes (§63.1–§63.9, §58) -/

/-- The clause of §63.7 read on a pair of related resulting states (§63.7; §49, last
paragraph). -/
private theorem transfer_heldClause_ren {e e' : S3} (he : SRel π α e e') (hde : Down e)
    (hde' : Down e') (x q : Nat) :
    OptP (e'.A[α.f x]?) (fun y => y.active = true → y.holder = .place (π.f q) →
      EffAnchorOK e' (α.f x) (e'.pframe (π.f q))) True ↔
    OptP (e.A[x]?) (fun y => y.active = true → y.holder = .place q →
      EffAnchorOK e x (e.pframe q)) True := by
  cases hy : e.A[x]? with
  | none => rw [(he.A_none x).1 hy]; exact Iff.rfl
  | some y =>
    obtain ⟨y', hy', hr⟩ := he.A_some hy
    rw [hy']
    simp only [OptP, hr.active, hr.holder, he.pframe, he.effAnchorOK hde hde']
    exact imp_congr_right fun _ => imp_congr (Holder.ren_inj π (b := .place q)) Iff.rfl

/-- The preconditions of `transfer` hold forward (§63.1–§63.9; §49, last paragraph). -/
private theorem transferPre_ren_of (hK : KCorr π α k k') (hS : Sim π α s s') {src dst : Nat}
    (hp : TransferPre k s src dst) : TransferPre k' s' (π.f src) (π.f dst) := by
  obtain ⟨h, hd, hd', hs⟩ := hS
  have he := transferEff_ren h hd hd' hs src dst
  have hde := transferEff_down hd src dst
  have hde' := transferEff_down hd' (π.f src) (π.f dst)
  have hfp := fun q l => h.mem_footprint hd hd' l q
  exact {
    srcUsable := (h.usable src).2 hp.srcUsable
    dstUsable := (h.usable dst).2 hp.dstUsable
    srcRight := (h.hasRight hd hd' .modify src).2 hp.srcRight
    dstRight := (h.hasRight hd hd' .modify dst).2 hp.dstRight
    sameShape := (sameShape_ren h.P hd.1 hd'.1 hs src dst).2 hp.sameShape
    srcInit := (π.forall_mem_iff (hfp src) fun l => by rw [h.I]).2 hp.srcInit
    dstNotInit := (π.forall_mem_iff (hfp dst) fun l => by rw [h.I]).2 hp.dstNotInit
    disjoint := mt (overlap_ren h.P hd.1 hd'.1 src dst).1 hp.disjoint
    noOutsideDerived := (α.exists_mem_iff h.mem_rangeA fun g =>
      and_congr (h.grounds hd hd' .modify src g) (α.forall_mem_iff h.mem_rangeA fun j =>
        imp_congr (h.activeDerivedOutside hd hd' src j) (h.rightChain hd hd' g j))).2
      hp.noOutsideDerived
    notPinned := (π.forall_mem_iff (hfp src) fun l =>
      and_congr (not_congr (hK.pinned l)) (by rw [h.pin])).2 hp.notPinned
    depsValid := (α.forall_mem_iff (h.mem_movedDeps hd hd' src) h.active).2 hp.depsValid
    anchorOrder := (he.anchorOrder hde hde').2 hp.anchorOrder
    anchorOrderHeld := (α.forall_mem_iff h.mem_rangeA fun x =>
      imp_congr (h.anchorMoves hd hd' src x) (π.forall_mem_iff h.P.mem_range fun q =>
        imp_congr (he.usable q) (transfer_heldClause_ren he hde hde' x q))).2 hp.anchorOrderHeld
    noSelfLock := (noLocalSelfLock_ren ⟨h, hd, hd', hs⟩ src dst).2 hp.noSelfLock
    dstUsableAfter := (he.usable dst).2 hp.dstUsableAfter }

/-- The preconditions of `transfer` are invariant (§63.1–§63.9; §49, last paragraph). -/
theorem transferPre_ren (hK : KCorr π α k k') (hS : Sim π α s s') (src dst : Nat) :
    TransferPre k' s' (π.f src) (π.f dst) ↔ TransferPre k s src dst :=
  ⟨fun hp => by simpa only [Ren.symm_f, π.gf] using transferPre_ren_of hK.symm hS.symm hp,
   transferPre_ren_of hK hS⟩

/-- The outcomes of `transfer` correspond under corresponding contracts (§63, §58; §49, last
paragraph). -/
theorem transfer_corr_of_kCorr (hK : KCorr π α k k') (hS : Sim π α s s') (src dst : Nat) :
    StepCorr π α (TransferStep k src dst s) (TransferStep k' (π.f src) (π.f dst) s') :=
  guarded_corr (transferPre_ren hK hS src dst) fun _ =>
    transferEff_ren hS.rel hS.down hS.down' hS.sib src dst

/-- The outcomes of `transfer` and of its renaming under the renamed contract correspond (§63,
§58; §48, §80; §49, last paragraph). -/
theorem transfer_corr (hS : Sim π α s s') (src dst : Nat) :
    StepCorr π α (TransferStep k src dst s)
      (TransferStep (k.rename π α) (π.f src) (π.f dst) s') :=
  transfer_corr_of_kCorr (KCorr.rename π α k) hS src dst

/-- An `ok` transfer keeps parent and origin links downward (§63, `ok` effect; §49.2, §49.5; §49,
last paragraph). -/
theorem transfer_down {src dst : Nat} {t : S3} (hd : Down s)
    (hst : TransferStep k src dst s (.ok t)) : Down t := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hst
  exact transferEff_down hd src dst

/-- An `ok` transfer keeps field order: it changes owners, not parents (§63, `ok` effect; §63.2;
§49, last paragraph). -/
theorem transfer_sib {src dst : Nat} {t : S3} (hs : SibMono π s.P)
    (hst : TransferStep k src dst s (.ok t)) : SibMono π t.P := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hst
  exact SibMono.congr (transfer_parentOf s src dst) hs

end Ern.MemoryModel.Access.Rename
