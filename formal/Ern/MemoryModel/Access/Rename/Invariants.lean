import Ern.MemoryModel.Access.Rename.Derived

/-!
# Renaming of identities: invariants

Transfer of the invariants of `specs/ERN_Memory_Model_Specification_v0.1.md` along related states
(§49, last paragraph): `WF3` and its clauses `RootChain`, `RootHeld` (§49), `I1`–`I3` (§50–§52),
`NoDangling` and `NoOrphan` (§54), `Inv3`, the main kernel invariant `KInv` and `I5` (§57). `I4`
holds in every state (`i4_always`) and needs no transfer.

Each invariant is transferred forward (`_of`), and the iff is closed by symmetry (`SRel.symm`).
-/

namespace Ern.MemoryModel.Access.Rename

variable {π α : Ren} {s s' : S3} {k k' : K}

/-- Every identity is a renamed identity (§49, last paragraph). -/
private theorem Ren.exists_f (π : Ren) (y : Nat) : ∃ x, y = π.f x := ⟨π.g y, (π.fg y).symm⟩

/-- A place of the related list is a renamed place (§40; §49, last paragraph). -/
private theorem PRel.get_some' {P P' : List Place} (hP : PRel π P P') {q : Nat} {pl' : Place}
    (hq : P'[π.f q]? = some pl') : ∃ pl, P[q]? = some pl ∧ pl' = pl.ren π := by
  rw [hP.get] at hq
  obtain ⟨pl, hpl, e⟩ := Option.map_eq_some_iff.1 hq
  exact ⟨pl, hpl, e.symm⟩

/-! ## `RootChain`, `RootHeld` (§49.6, §49.7) -/

/-- `RootChain` is preserved forward (§49.6; §49, last paragraph). -/
theorem SRel.rootChain_of (h : SRel π α s s') (hd : Down s) (hd' : Down s')
    (hr : RootChain s) : RootChain s' := by
  intro a' y' l' hy' hl' hleaf
  obtain ⟨a, rfl⟩ := α.exists_f a'
  obtain ⟨l, rfl⟩ := π.exists_f l'
  obtain ⟨y, hy, hyy⟩ := h.A_some' hy'
  obtain ⟨x, z, r, hx, hz, hzo, hroot, hpart, hfp⟩ :=
    hr a y l hy ((hyy.mem_footprint l).1 hl') ((isLeaf_ren h.P l).1 hleaf)
  obtain ⟨z', hz', hzz⟩ := h.A_some hz
  refine ⟨α.f x, z', π.f r, ?_, hz', by rw [hzz.origin, hzo]; rfl,
    (rootPlace_ren h.P r).2 hroot, (partOf_ren h.P hd.1 hd'.1 l r).2 hpart, fun l'' => ?_⟩
  · rcases hx with rfl | hx
    · exact .inl rfl
    · exact .inr ((h.mem_ancs hd hd' a x).2 hx)
  · obtain ⟨m, rfl⟩ := π.exists_f l''
    rw [hzz.mem_footprint, h.mem_footprint hd hd', hfp]

/-- `RootChain` is invariant (§49.6; §49, last paragraph). -/
theorem SRel.rootChain (h : SRel π α s s') (hd : Down s) (hd' : Down s') :
    RootChain s' ↔ RootChain s :=
  ⟨h.symm.rootChain_of hd' hd, h.rootChain_of hd hd'⟩

/-- `RootHeld` is preserved forward (§49.7; §49, last paragraph). -/
theorem SRel.rootHeld_of (h : SRel π α s s') (hd : Down s) (hd' : Down s')
    (hr : RootHeld s) : RootHeld s' := by
  intro r' hroot hu
  obtain ⟨r, rfl⟩ := π.exists_f r'
  obtain ⟨i, z, pr, hz, hza, hzo, hzm, hpr, hzh, hfp⟩ :=
    hr r ((rootPlace_ren h.P r).1 hroot) ((h.usable r).1 hu)
  obtain ⟨z', hz', hzz⟩ := h.A_some hz
  refine ⟨α.f i, z', pr.ren π, hz', by rw [hzz.active]; exact hza,
    by rw [hzz.origin, hzo]; rfl, by rw [hzz.mode]; exact hzm, by rw [h.P.get, hpr]; rfl,
    hzz.holder.trans (congrArg (Holder.ren π) hzh), fun l' => ?_⟩
  obtain ⟨l, rfl⟩ := π.exists_f l'
  rw [hzz.mem_footprint, h.mem_footprint hd hd', hfp]

/-- `RootHeld` is invariant (§49.7; §49, last paragraph). -/
theorem SRel.rootHeld (h : SRel π α s s') (hd : Down s) (hd' : Down s') :
    RootHeld s' ↔ RootHeld s :=
  ⟨h.symm.rootHeld_of hd' hd, h.rootHeld_of hd hd'⟩

/-! ## `WF3` (§49) -/

/-- `WF3` is preserved forward (§49). The order clauses of §49.2 and §49.5 are read on the target
state through `Down s'` (§49, last paragraph: numerical order only represents acyclicity). -/
theorem SRel.wf3_of (h : SRel π α s s') (hd : Down s) (hd' : Down s') (hw : WF3 s) :
    WF3 s' where
  frames := by rw [h.F, h.nF]; exact hw.frames
  places q' pl' r' hq' hr' := by
    obtain ⟨q, rfl⟩ := π.exists_f q'
    obtain ⟨r, rfl⟩ := π.exists_f r'
    obtain ⟨pl, hpl, rfl⟩ := h.P.get_some' hq'
    have hpr : pl.parent = some r := (Ren.option_map_eq_some π _ r).1 hr'
    obtain ⟨pr, hpr', -, ho, hdead⟩ := hw.places q pl r hpl hpr
    refine ⟨pr.ren π, by rw [h.P.get, hpr']; rfl, hd'.1 _ _ ?_,
      congrArg (Holder.ren π) ho, by rw [h.dead, h.dead]; exact hdead⟩
    simp only [Access.parentOf, h.P.get, hpl, Option.map_some, Option.bind_some]
    exact hr'
  owners := by
    refine ⟨fun q' pl' f hq' ho => ?_, fun q' pl' o' hq' ho => ?_, fun q' hu => ?_⟩
    · obtain ⟨q, rfl⟩ := π.exists_f q'
      obtain ⟨pl, hpl, rfl⟩ := h.P.get_some' hq'
      rw [h.nF]
      exact hw.owners.1 q pl f hpl ((Holder.ren_inj π (a := pl.owner) (b := .frame f)).1 ho)
    · obtain ⟨q, rfl⟩ := π.exists_f q'
      obtain ⟨o, rfl⟩ := π.exists_f o'
      obtain ⟨pl, hpl, rfl⟩ := h.P.get_some' hq'
      exact (h.P.lt_iff o).2
        (hw.owners.2.1 q pl o hpl ((Holder.ren_inj π (a := pl.owner) (b := .place o)).1 ho))
    · obtain ⟨q, rfl⟩ := π.exists_f q'
      obtain ⟨f, hf, hfF⟩ := hw.owners.2.2 q ((h.usable q).1 hu)
      exact ⟨f, (h.frameOf q f).2 hf, by rw [h.F]; exact hfF⟩
  footprints a' x' hx' l' hl' := by
    obtain ⟨a, rfl⟩ := α.exists_f a'
    obtain ⟨l, rfl⟩ := π.exists_f l'
    obtain ⟨x, hx, hxx⟩ := h.A_some' hx'
    have := hw.footprints a x hx l ((hxx.mem_footprint l).1 hl')
    exact ⟨(h.P.lt_iff l).2 this.1, (isLeaf_ren h.P l).2 this.2⟩
  origins b' y' a' hy' ho := hd'.2 b' a' (Option.bind_eq_some_iff.2 ⟨y', hy', ho⟩)
  rootChain := h.rootChain_of hd hd' hw.rootChain
  rootHeld := h.rootHeld_of hd hd' hw.rootHeld
  holders a' y' hy' ha := by
    obtain ⟨a, rfl⟩ := α.exists_f a'
    obtain ⟨y, hy, hyy⟩ := h.A_some' hy'
    rw [hyy.holder, h.holderLive]
    exact hw.holders a y hy (by rw [← hyy.active]; exact ha)

/-- `WF3` is invariant (§49; §49, last paragraph). -/
theorem SRel.wf3 (h : SRel π α s s') (hd : Down s) (hd' : Down s') : WF3 s' ↔ WF3 s :=
  ⟨h.symm.wf3_of hd' hd, h.wf3_of hd hd'⟩

/-! ## `I1`–`I3`, `NoDangling`, `Inv3` (§50–§54, §57) -/

/-- `I1` is preserved forward (§50; §49, last paragraph). -/
theorem SRel.i1_of (h : SRel π α s s') (hd : Down s) (hd' : Down s') (hi : I1 s) : I1 s' := by
  intro a' b' x' y' p' hab hx' hy' hxa hya hpx hpy hba hab'
  obtain ⟨a, rfl⟩ := α.exists_f a'
  obtain ⟨b, rfl⟩ := α.exists_f b'
  obtain ⟨p, rfl⟩ := π.exists_f p'
  obtain ⟨x, hx, hxx⟩ := h.A_some' hx'
  obtain ⟨y, hy, hyy⟩ := h.A_some' hy'
  rw [hxx.mode, hyy.mode]
  exact hi a b x y p (fun e => hab (by rw [e])) hx hy (by rw [← hxx.active]; exact hxa)
    (by rw [← hyy.active]; exact hya) ((hxx.mem_footprint p).1 hpx)
    ((hyy.mem_footprint p).1 hpy) (fun e => hba ((h.mem_ancs hd hd' b a).2 e))
    (fun e => hab' ((h.mem_ancs hd hd' a b).2 e))

/-- `I1` is invariant (§50; §49, last paragraph). -/
theorem SRel.i1 (h : SRel π α s s') (hd : Down s) (hd' : Down s') : I1 s' ↔ I1 s :=
  ⟨h.symm.i1_of hd' hd, h.i1_of hd hd'⟩

/-- `I2` is preserved forward (§51; §49, last paragraph). -/
theorem SRel.i2_of (h : SRel π α s s') (hi : I2 s) : I2 s' := by
  intro b' y' a' hy' ho
  obtain ⟨b, rfl⟩ := α.exists_f b'
  obtain ⟨a, rfl⟩ := α.exists_f a'
  obtain ⟨y, hy, hyy⟩ := h.A_some' hy'
  rw [hyy.origin, Ren.option_map_eq_some] at ho
  obtain ⟨x, hx, hm, hfp, hact⟩ := hi b y a hy ho
  obtain ⟨x', hx', hxx⟩ := h.A_some hx
  refine ⟨x', hx', by rw [hxx.mode, hyy.mode]; exact hm, fun p' hp' => ?_, fun ha => ?_⟩
  · obtain ⟨p, rfl⟩ := π.exists_f p'
    exact (hxx.mem_footprint p).2 (hfp p ((hyy.mem_footprint p).1 hp'))
  · rw [hxx.active]; exact hact (by rw [← hyy.active]; exact ha)

/-- `I2` is invariant (§51; §49, last paragraph). -/
theorem SRel.i2 (h : SRel π α s s') : I2 s' ↔ I2 s := ⟨h.symm.i2_of, h.i2_of⟩

/-- `I3` is preserved forward (§52; §49, last paragraph). -/
theorem SRel.i3_of (h : SRel π α s s') (hi : I3 s) : I3 s' := by
  intro q' hq x' hx
  obtain ⟨q, rfl⟩ := π.exists_f q'
  obtain ⟨x, rfl⟩ := α.exists_f x'
  exact (h.active x).2 (hi q ((h.usable q).1 hq) x ((h.mem_D q x).1 hx))

/-- `I3` is invariant (§52; §49, last paragraph). -/
theorem SRel.i3 (h : SRel π α s s') : I3 s' ↔ I3 s := ⟨h.symm.i3_of, h.i3_of⟩

/-- `NoDangling` is preserved forward (§54; §49, last paragraph). -/
theorem SRel.noDangling_of (h : SRel π α s s') (hd : Down s) (hd' : Down s')
    (hn : NoDangling s) : NoDangling s' := by
  intro j' y' hy' ha q' hq l' hl hly
  obtain ⟨j, rfl⟩ := α.exists_f j'
  obtain ⟨q, rfl⟩ := π.exists_f q'
  obtain ⟨l, rfl⟩ := π.exists_f l'
  obtain ⟨y, hy, hyy⟩ := h.A_some' hy'
  exact hn j y hy (by rw [← hyy.active]; exact ha) q (fun hu => hq ((h.usable q).2 hu)) l
    ((h.mem_footprint hd hd' l q).1 hl) ((hyy.mem_footprint l).1 hly)

/-- `NoDangling` is invariant (§54; §49, last paragraph). -/
theorem SRel.noDangling (h : SRel π α s s') (hd : Down s) (hd' : Down s') :
    NoDangling s' ↔ NoDangling s :=
  ⟨h.symm.noDangling_of hd' hd, h.noDangling_of hd hd'⟩

/-- `Inv3` is invariant (§57; §49, last paragraph); `I4` holds in every state (§53). -/
theorem SRel.inv3 (h : SRel π α s s') (hd : Down s) (hd' : Down s') : Inv3 s' ↔ Inv3 s :=
  and_congr
    (and_congr (h.i1 hd hd')
      (and_congr h.i2 (and_congr h.i3 (iff_of_true (i4_always s') (i4_always s)))))
    (and_congr (h.anchorOrder hd hd') (h.noDangling hd hd'))

/-! ## `NoOrphan` (§54) -/

/-- A `CoversHolder` link is preserved forward (§54; §49, last paragraph). -/
theorem SRel.coversHolder_of (h : SRel π α s s') (hd : Down s) (hd' : Down s') {a b : Nat}
    (hc : CoversHolder s a b) : CoversHolder s' (α.f a) (α.f b) := by
  unfold CoversHolder at hc ⊢
  cases hz : s.A[b]? with
  | none => rw [hz] at hc; exact hc.elim
  | some z =>
    obtain ⟨z', hz', hzz⟩ := h.A_some hz
    rw [hz] at hc
    rw [hz']
    simp only [OptP] at hc ⊢
    rw [hzz.holder]
    cases ho : z.holder with
    | frame f => rw [ho] at hc; exact hc.elim
    | place q =>
      rw [ho] at hc
      obtain ⟨ha, hl⟩ := hc
      refine ⟨(h.active a).2 ha, fun l' hl' => ?_⟩
      obtain ⟨l, rfl⟩ := π.exists_f l'
      exact (h.mem_afp a l).2 (hl l ((h.mem_footprint hd hd' l q).1 hl'))

/-- A `CoversHolder` link is invariant (§54; §49, last paragraph). -/
theorem SRel.coversHolder (h : SRel π α s s') (hd : Down s) (hd' : Down s') (a b : Nat) :
    CoversHolder s' (α.f a) (α.f b) ↔ CoversHolder s a b :=
  ⟨fun hc => by simpa only [Ren.symm_f, α.gf] using h.symm.coversHolder_of hd' hd hc,
   h.coversHolder_of hd hd'⟩

/-- A chain linked by `R` is linked by `R'` once mapped, when `f` carries `R` to `R'` (§54). -/
theorem linked_map {R R' : Nat → Nat → Prop} {f : Nat → Nat}
    (hR : ∀ a b, R a b → R' (f a) (f b)) : ∀ {l : List Nat}, Linked R l → Linked R' (l.map f)
  | [], _ => trivial
  | [_], _ => trivial
  | a :: b :: c, hl => ⟨hR a b hl.1, linked_map hR (l := b :: c) hl.2⟩

/-- `NoOrphan` is preserved forward; the witness chain is renamed (§54; §49, last paragraph). -/
theorem SRel.noOrphan_of (h : SRel π α s s') (hd : Down s) (hd' : Down s')
    (hn : NoOrphan s) : NoOrphan s' := by
  intro x' y' q' hy' ha hh
  obtain ⟨x, rfl⟩ := α.exists_f x'
  obtain ⟨q, rfl⟩ := π.exists_f q'
  obtain ⟨y, hy, hyy⟩ := h.A_some' hy'
  rw [hyy.holder] at hh
  obtain ⟨a₀, z, f, c, hz, hza, hzh, hf, hnd, hlast, hlink⟩ :=
    hn x y q hy (by rw [← hyy.active]; exact ha)
      ((Holder.ren_inj π (a := y.holder) (b := .place q)).1 hh)
  obtain ⟨z', hz', hzz⟩ := h.A_some hz
  refine ⟨α.f a₀, z', f, c.map α.f, hz', by rw [hzz.active]; exact hza,
    hzz.holder.trans (congrArg (Holder.ren π) hzh), by rw [h.F]; exact hf, ?_, ?_,
    linked_map (f := α.f) (fun _ _ hc => h.coversHolder_of hd hd' hc) hlink⟩
  · exact List.pairwise_map.2 (hnd.imp fun hab e => hab ((Ren.f_inj α).1 e))
  · show ((a₀ :: c).map α.f).getLast? = _
    rw [List.getLast?_map, hlast]; rfl

/-- `NoOrphan` is invariant (§54; §49, last paragraph). -/
theorem SRel.noOrphan (h : SRel π α s s') (hd : Down s) (hd' : Down s') :
    NoOrphan s' ↔ NoOrphan s :=
  ⟨h.symm.noOrphan_of hd' hd, h.noOrphan_of hd hd'⟩

/-! ## Main kernel invariant and `I5` (§57) -/

/-- The main kernel invariant `WF3 ∧ Inv3 ∧ AnchorOrderHeld ∧ NoOrphan` is invariant (§57; §49,
last paragraph). -/
theorem SRel.kinv (h : SRel π α s s') (hd : Down s) (hd' : Down s') : KInv s' ↔ KInv s :=
  and_congr (h.wf3 hd hd')
    (and_congr (h.inv3 hd hd') (and_congr (h.anchorOrderHeld hd hd') (h.noOrphan hd hd')))

/-- The main kernel invariant is invariant along the simulation (§57; §49, last paragraph). -/
theorem Sim.kinv (hS : Sim π α s s') : KInv s' ↔ KInv s :=
  hS.rel.kinv hS.down hS.down'

/-- `I5` is preserved forward under corresponding contracts (§57, §74, §48; §49, last
paragraph). -/
theorem SRel.i5_of (hK : KCorr π α k k') (h : SRel π α s s') (hd : Down s) (hd' : Down s')
    (hi : I5 k s) : I5 k' s' := by
  intro l' hl hleaf hp
  obtain ⟨l, rfl⟩ := π.exists_f l'
  rw [hK.pinned, h.pin] at hp
  obtain ⟨q, hq, hlq⟩ := hi l ((h.P.lt_iff l).1 hl) ((isLeaf_ren h.P l).1 hleaf) hp
  exact ⟨π.f q, (h.usable q).2 hq, (h.mem_footprint hd hd' l q).2 hlq⟩

/-- `I5` is invariant under corresponding contracts (§57, §74, §48; §49, last paragraph). -/
theorem SRel.i5 (hK : KCorr π α k k') (h : SRel π α s s') (hd : Down s) (hd' : Down s') :
    I5 k' s' ↔ I5 k s :=
  ⟨h.symm.i5_of hK.symm hd' hd, h.i5_of hK hd hd'⟩

/-- `I5` is invariant along the simulation under corresponding contracts (§57, §74, §48; §49,
last paragraph). -/
theorem Sim.i5_corr (hK : KCorr π α k k') (hS : Sim π α s s') : I5 k' s' ↔ I5 k s :=
  hS.rel.i5 hK hS.down hS.down'

/-- `I5` for the renamed contract on the related state is `I5` (§57, §74, §48, §80; §49, last
paragraph). -/
theorem Sim.i5 (hS : Sim π α s s') : I5 (k.rename π α) s' ↔ I5 k s :=
  hS.i5_corr (KCorr.rename π α k)

end Ern.MemoryModel.Access.Rename
