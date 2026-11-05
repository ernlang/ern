import Ern.MemoryModel.Access.Preserve.Common

/-!
# Access kernel: preservation by `derive`, `split` and `release`

O1 `derive` (§60), O2 `split` (§61) and O3 `release` (§62) preserve the kernel invariant `KInv`
(§57) and its auxiliary `KAux`; `split` needs the obligation `DDSound(K)` (§61, §80) for I1 only.
Per-invariant lemmas, the effects of §61 and §62 on effective modes (§43), the failure of I1 after
a `split` without `DDSound` (§61, note), and determinism (§58).
-/

namespace Ern.MemoryModel.Access

/-! ## Helpers -/

/-- An authority exercisable at `m` exists, is active, and its own mode permits `m` (§43). -/
private theorem exercisableAt_mode {s : S3} {a : Nat} {m : Mode} (h : s.ExercisableAt a m) :
    ∃ y, s.A[a]? = some y ∧ y.active = true ∧ m.le y.mode := by
  cases h with
  | base hy ha hm _ => exact ⟨_, hy, ha, hm⟩
  | held hy ha hm _ _ _ => exact ⟨_, hy, ha, hm⟩

/-- The footprint of an existing authority (§42). -/
private theorem afp_eq {s : S3} {a : Nat} {x : Authority} (hx : s.A[a]? = some x) :
    s.afp a = x.footprint := by
  unfold S3.afp; rw [hx]

/-- The effective anchor is `x` or one of its origins (§44). -/
private theorem effAnchor_mem (s : S3) (x : Nat) :
    s.effAnchor x = x ∨ s.effAnchor x ∈ s.ancs x :=
  List.mem_cons.1 (List.getLastD_mem_cons (l := s.ancs x) (a := x))

/-- The effective anchor of `x` is not above `x` (§44, §49.5). -/
private theorem effAnchor_le (s : S3) (x : Nat) : s.effAnchor x ≤ x := by
  rcases effAnchor_mem s x with h | h
  · exact Nat.le_of_eq h
  · exact Nat.le_of_lt (chain_lt h)

/-- An anchor satisfying the rule of §44 is an existing authority. -/
private theorem EffAnchorOK.lt {s : S3} {x : Nat} {fd : Option Nat} (h : EffAnchorOK s x fd) :
    x < s.A.length := by
  unfold EffAnchorOK at h
  cases hz : s.A[s.effAnchor x]? with
  | none => rw [hz] at h; exact h.elim
  | some z =>
    rcases effAnchor_mem s x with e | e
    · rw [e] at hz; exact lt_of_getElem? hz
    · have ho : s.org x ≠ none := fun ho => by rw [S3.ancs, chain_none ho] at e; simp at e
      simp only [S3.org] at ho
      cases hx : s.A[x]? with
      | none => rw [hx] at ho; exact absurd rfl ho
      | some _ => exact lt_of_getElem? hx

/-- An addition keeps the rule of §44 for an existing authority. -/
private theorem effAnchorOK_addAuth {s : S3} {y₀ : Authority} {x : Nat} {fd : Option Nat}
    (hx : x < s.A.length) : EffAnchorOK (s.addAuth y₀) x fd ↔ EffAnchorOK s x fd := by
  have he : (s.addAuth y₀).effAnchor x = s.effAnchor x := by
    simp only [S3.effAnchor, ancs_addAuth_lt hx]
  have hH : (s.addAuth y₀).hframe = s.hframe := funext (S3.hframe_congr (addAuth_P s y₀))
  unfold EffAnchorOK
  rw [he, hH, addAuth_lt (Nat.lt_of_le_of_lt (effAnchor_le s x) hx)]
  exact Iff.rfl

/-! ## Additions of one derived authority (§60, §61) -/

/-- Adding an active authority derived from `src`, within its footprint and held by a live holder,
preserves `WF3` (§49), including §49.4 (the new footprint consists of leaves of the source) and
§49.7 (root authorities are unchanged). -/
private theorem addAuth_wf3 {s : S3} (hwf : WF3 s) {src : Nat} {x : Authority} {m : Mode}
    {fp : List Nat} {hd : Holder} (hx : s.A[src]? = some x) (hfp : ∀ p ∈ fp, p ∈ x.footprint)
    (hl : HolderLive s hd) : WF3 (s.addAuth ⟨m, some src, fp, hd, true⟩) := by
  have hs := lt_of_getElem? hx
  have live := HolderLive.congr (addAuth_P s ⟨m, some src, fp, hd, true⟩) rfl rfl
  have usable := fun q =>
    S3.Usable.congr (q := q) (addAuth_P s ⟨m, some src, fp, hd, true⟩) rfl rfl
  refine ⟨hwf.frames, hwf.places, ⟨hwf.owners.1, hwf.owners.2.1, fun q hq => ?_⟩, ?_, ?_,
    rootChain_addAuth hwf.rootChain hx rfl hfp,
    hwf.rootHeld.transport rfl (fun r => (usable r).1)
      (fun i z hz _ _ => by rw [addAuth_lt (lt_of_getElem? hz)]; exact hz), ?_⟩
  · obtain ⟨f, hf, hfF⟩ := hwf.owners.2.2 q ((usable q).1 hq)
    exact ⟨f, (FrameOf.congr (addAuth_P s _)).2 hf, hfF⟩
  · intro a y hy l hl'
    rcases addAuth_get hy with ⟨-, hy'⟩ | ⟨-, rfl⟩
    · exact hwf.footprints a y hy' l hl'
    · exact hwf.footprints src x hx l (hfp l hl')
  · intro b y a hb ho
    rcases addAuth_get hb with ⟨-, hb''⟩ | ⟨rfl, rfl⟩
    · exact hwf.origins b y a hb'' ho
    · cases ho; exact hs
  · intro a y hy ya
    rcases addAuth_get hy with ⟨-, hy'⟩ | ⟨-, rfl⟩
    · exact (live _).2 (hwf.holders a y hy' ya)
    · exact (live _).2 hl

/-- Adding an authority derived from `src` with a mode not above the mode of `src` and a footprint
within its footprint preserves `I2` (§51). -/
private theorem addAuth_i2 {s : S3} (h2 : I2 s) {src : Nat} {x : Authority} {m : Mode}
    {fp : List Nat} {hd : Holder} (hx : s.A[src]? = some x) (hm : m.le x.mode)
    (hfp : ∀ p ∈ fp, p ∈ x.footprint) : I2 (s.addAuth ⟨m, some src, fp, hd, true⟩) := by
  intro b y a hb ho
  rcases addAuth_get hb with ⟨-, hb''⟩ | ⟨rfl, rfl⟩
  · obtain ⟨x₁, hx₁, h⟩ := h2 b y a hb'' ho
    exact ⟨x₁, by rw [addAuth_lt (lt_of_getElem? hx₁)]; exact hx₁, h⟩
  · cases ho; exact ⟨x, by rw [addAuth_lt (lt_of_getElem? hx)]; exact hx, hm, hfp⟩

/-- An addition keeps the anchors and their activity, so it preserves `I3` (§52). -/
private theorem addAuth_i3 {s : S3} (h3 : I3 s) (y₀ : Authority) : I3 (s.addAuth y₀) :=
  fun q hq x hx => active_addAuth (h3 q ((S3.Usable.congr (addAuth_P s y₀) rfl rfl).1 hq) x hx)

/-- An addition keeps the anchors, origin chains and holders of existing authorities, so it
preserves `AnchorOrder` (§44, §54). -/
private theorem addAuth_anchorOrder {s : S3} (h : AnchorOrder s) (y₀ : Authority) :
    AnchorOrder (s.addAuth y₀) := fun q hq x hx => by
  have hok := h q ((S3.Usable.congr (addAuth_P s y₀) rfl rfl).1 hq) x hx
  rw [S3.pframe_congr (addAuth_P s y₀)]
  exact (effAnchorOK_addAuth hok.lt).2 hok

/-- Adding an authority whose footprint is within the footprint of an active authority preserves
`NoDangling` (§54). -/
private theorem addAuth_noDangling {s : S3} (h : NoDangling s) {src : Nat} {x y₀ : Authority}
    (hx : s.A[src]? = some x) (xa : x.active = true) (hfp : ∀ p ∈ y₀.footprint, p ∈ x.footprint) :
    NoDangling (s.addAuth y₀) := by
  intro j z hz za q hq l hl hlz
  have hq' : ¬ s.Usable q := fun h' => hq ((S3.Usable.congr (addAuth_P s y₀) rfl rfl).2 h')
  rcases addAuth_get hz with ⟨-, hz'⟩ | ⟨-, rfl⟩
  · exact h j z hz' za q hq' l hl hlz
  · exact h src x hx xa q hq' l hl (hfp l hlz)

/-- Adding an authority held by a frame preserves `AnchorOrderHeld` (§44, §54). -/
private theorem addAuth_anchorOrderHeld {s : S3} (h : AnchorOrderHeld s) {y₀ : Authority} {f : Nat}
    (hh : y₀.holder = .frame f) : AnchorOrderHeld (s.addAuth y₀) := by
  intro q hq x y hy ya hyq
  have hq' := (S3.Usable.congr (addAuth_P s y₀) rfl rfl).1 hq
  rcases addAuth_get hy with ⟨hxl, hy'⟩ | ⟨-, rfl⟩
  · rw [S3.pframe_congr (addAuth_P s y₀)]
    exact (effAnchorOK_addAuth hxl).2 (h q hq' x y hy' ya hyq)
  · rw [hh] at hyq; cases hyq

/-- Adding a derived authority preserves the auxiliary `RootHeldConv` (§40, §49.7). -/
private theorem addAuth_rootHeldConv {s : S3} (h : RootHeldConv s) {y₀ : Authority} {src : Nat}
    (ho : y₀.origin = some src) : RootHeldConv (s.addAuth y₀) :=
  h.transport (addAuth_P s y₀) fun x z' hx hzo => by
    rcases addAuth_get hx with ⟨-, hx'⟩ | ⟨-, rfl⟩
    · exact ⟨z', hx', hzo, rfl, rfl⟩
    · rw [ho] at hzo; cases hzo

/-! ## O1 `derive` (§60) -/

/-- `derive` preserves `WF3` (§49, §60): the new authority has an existing source, a footprint
within the footprint of the source (§49.4: leaves), a live holder (§60.4), and no root authority
changes (§49.7). -/
theorem derive_preserves_wf3 {s s' : S3} {src : Nat} {region : List Nat} {m : Mode} (hw : WF3 s)
    (h : DeriveStep src region m s (.ok s')) : WF3 s' := by
  obtain ⟨hp, rfl⟩ := Guarded.ok_iff.1 h
  obtain ⟨x, hx, -⟩ := hp.active
  exact addAuth_wf3 hw hx (fun p hp' => afp_eq hx ▸ hp.within p hp') hp.frameLive

/-- `derive` preserves I1 (§50, §60.2, §60.3), under I1 alone: the requested mode is permitted by
the effective mode of the source on every leaf of the region. -/
theorem derive_preserves_exclusivity {s s' : S3} {src : Nat} {region : List Nat} {m : Mode}
    (h1 : I1 s) (h : DeriveStep src region m s (.ok s')) : I1 s' := by
  obtain ⟨hp, rfl⟩ := Guarded.ok_iff.1 h
  obtain ⟨x, hx, -⟩ := hp.active
  exact addAuth_I1 h1 hx hp.modeOK

/-- `derive` preserves I2 (§51, §60.1, §60.2): the derived mode does not exceed the own mode of the
source, whatever the region, and the region is within the footprint of the source. -/
theorem derive_preserves_i2 {s s' : S3} {src : Nat} {region : List Nat} {m : Mode} (h2 : I2 s)
    (h : DeriveStep src region m s (.ok s')) : I2 s' := by
  obtain ⟨hp, rfl⟩ := Guarded.ok_iff.1 h
  obtain ⟨x, hx, -, hm⟩ := exercisableAt_mode hp.exercisable
  exact addAuth_i2 h2 hx hm fun p hp' => afp_eq hx ▸ hp.within p hp'

/-- `derive` preserves I3 (§52, §60 effect: no anchor is created or removed). -/
theorem derive_preserves_i3 {s s' : S3} {src : Nat} {region : List Nat} {m : Mode} (h3 : I3 s)
    (h : DeriveStep src region m s (.ok s')) : I3 s' := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
  exact addAuth_i3 h3 _

/-- `derive` preserves `AnchorOrder` (§44, §54, §60 effect). -/
theorem derive_preserves_anchorOrder {s s' : S3} {src : Nat} {region : List Nat} {m : Mode}
    (hao : AnchorOrder s) (h : DeriveStep src region m s (.ok s')) : AnchorOrder s' := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
  exact addAuth_anchorOrder hao _

/-- `derive` preserves `NoDangling` (§54, §60.2): the region is within the footprint of the active
source. -/
theorem derive_preserves_noDangling {s s' : S3} {src : Nat} {region : List Nat} {m : Mode}
    (hnd : NoDangling s) (h : DeriveStep src region m s (.ok s')) : NoDangling s' := by
  obtain ⟨hp, rfl⟩ := Guarded.ok_iff.1 h
  obtain ⟨x, hx, xa⟩ := hp.active
  exact addAuth_noDangling hnd hx xa fun p hp' => afp_eq hx ▸ hp.within p hp'

/-- `derive` preserves `AnchorOrderHeld` (§44, §54, §60.4): the new authority is held by the
current frame. -/
theorem derive_preserves_anchorOrderHeld {s s' : S3} {src : Nat} {region : List Nat} {m : Mode}
    (haoh : AnchorOrderHeld s) (h : DeriveStep src region m s (.ok s')) : AnchorOrderHeld s' := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
  exact addAuth_anchorOrderHeld haoh rfl

/-- `derive` preserves the auxiliary `RootHeldConv` (§40, §49.7, §60 effect: the new authority has
an origin). -/
theorem derive_preserves_rootHeldConv {s s' : S3} {src : Nat} {region : List Nat} {m : Mode}
    (hc : RootHeldConv s) (h : DeriveStep src region m s (.ok s')) : RootHeldConv s' := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
  exact addAuth_rootHeldConv hc rfl

/-- `derive` preserves the kernel invariant `KInv` and `KAux` (§57, §58, §60). -/
theorem derive_preserves {s s' : S3} {src : Nat} {region : List Nat} {m : Mode} (hinv : KInv s)
    (haux : KAux s) (h : DeriveStep src region m s (.ok s')) : KInv s' ∧ KAux s' := by
  obtain ⟨hw, ⟨⟨h1, h2, h3, -⟩, hao, hnd⟩, haoh, -⟩ := hinv
  exact ⟨kInv_of (derive_preserves_wf3 hw h)
    ⟨⟨derive_preserves_exclusivity h1 h, derive_preserves_i2 h2 h, derive_preserves_i3 h3 h,
      i4_always _⟩, derive_preserves_anchorOrder hao h, derive_preserves_noDangling hnd h⟩
    (derive_preserves_anchorOrderHeld haoh h), derive_preserves_rootHeldConv haux h⟩

/-! ## O2 `split` (§61) -/

/-- A property preserved by the addition of each region authority of `split` is preserved by the
whole `split` (§61 effect: one authority per region, added in order). -/
private theorem split_induct {src : Nat} {x : Authority} (Q : S3 → Prop)
    (step : ∀ (s : S3) (r : List Nat), Q s → s.A[src]? = some x → (∀ p ∈ r, p ∈ x.footprint) →
      Q (s.addAuth ⟨.modify, some src, r, .frame s.top, true⟩)) :
    ∀ (rs : List (List Nat)) (s : S3), Q s → s.A[src]? = some x →
      (∀ r ∈ rs, ∀ p ∈ r, p ∈ x.footprint) → Q (splitEff s src rs)
  | [], s, hq, _, _ => by simpa [splitEff] using hq
  | r :: rs, s, hq, hx, hr => by
    rw [splitEff_cons]
    exact split_induct Q step rs _ (step s r hq hx (hr r (List.mem_cons_self ..)))
      (by rw [addAuth_lt (lt_of_getElem? hx)]; exact hx)
      fun r' hr' => hr r' (List.mem_cons_of_mem _ hr')

/-- Under I1, adding the authorities of pairwise disjoint regions on which `src` has effective
`Modify` preserves I1 (§50, §61.1, §61.3). -/
private theorem split_i1_aux {src : Nat} {x : Authority} :
    ∀ (rs : List (List Nat)) (s : S3), I1 s → s.A[src]? = some x →
      (∀ r ∈ rs, ∀ p ∈ r, effective s src p = some .modify) →
      rs.Pairwise (fun r r' => ∀ l ∈ r, l ∉ r') → I1 (splitEff s src rs)
  | [], s, h1, _, _, _ => by simpa [splitEff] using h1
  | r :: rs, s, h1, hx, hr, hpw => by
    rw [splitEff_cons]
    have hs := lt_of_getElem? hx
    have h1' := addAuth_I1 (hd := .frame s.top) h1 hx fun p hp => by
      rw [hr r (List.mem_cons_self ..) p hp]; exact Mode.le_refl _
    obtain ⟨hpr, hpw⟩ := List.pairwise_cons.1 hpw
    refine split_i1_aux rs _ h1' (by rw [addAuth_lt hs]; exact hx) (fun r' hr' p hp => ?_) hpw
    rw [effective_addAuth_notin hs fun h => hpr r' hr' p h hp]
    exact hr r' (List.mem_cons_of_mem _ hr') p hp

/-- The source of an accepted `split` and its regions (§61.1, §61.2). -/
private theorem split_src {k : K} {s : S3} {src : Nat} {rs : List (List Nat)}
    (hp : SplitPre k s src rs) : ∃ x, s.A[src]? = some x ∧ x.active = true ∧ x.mode = .modify ∧
      ∀ r ∈ rs, ∀ p ∈ r, p ∈ x.footprint := by
  obtain ⟨x, hx, xa, hm⟩ := exercisableAt_mode hp.exercisable
  refine ⟨x, hx, xa, ?_, fun r hr p hp' => afp_eq hx ▸ (hp.within r hr p hp').1⟩
  cases e : x.mode
  · rw [e] at hm; cases hm with
    | inl h => cases h
    | inr h => cases h
  · rfl

/-- `split` preserves `WF3` (§49, §61): each new authority has an existing source, a footprint
within the footprint of the source (§49.4: leaves), is held by the current frame, and no root
authority changes (§49.7). -/
theorem split_preserves_wf3 {k : K} {s s' : S3} {src : Nat} {rs : List (List Nat)} (hw : WF3 s)
    (h : SplitStep k src rs s (.ok s')) : WF3 s' := by
  obtain ⟨hp, rfl⟩ := Guarded.ok_iff.1 h
  obtain ⟨x, hx, -, -, hfp⟩ := split_src hp
  exact split_induct WF3 (fun s _ hw hx hfp => addAuth_wf3 hw hx hfp (top_mem hw.frames.1))
    rs s hw hx hfp

/-- `split` preserves I1 (§50, §61) under the obligation `DDSound(K)` (§61.3, §80): the regions are
then pairwise disjoint, and `src` has effective `Modify` on each of their leaves. Without
`DDSound`, see `split_unsound_without_DD`. -/
theorem split_preserves_exclusivity {k : K} (hdd : DDSound k) {s s' : S3} {src : Nat}
    {rs : List (List Nat)} (h1 : I1 s) (h : SplitStep k src rs s (.ok s')) : I1 s' := by
  obtain ⟨hp, rfl⟩ := Guarded.ok_iff.1 h
  obtain ⟨x, hx, -⟩ := hp.active
  exact split_i1_aux rs s h1 hx hp.modifyOn
    (hp.disjoint.imp fun {r r'} hd => hd.elim id (hdd r r'))

/-- `split` preserves I2 (§51, §61.1, §61.2): the new authorities are `Modify`, as the source
exercisable in `Modify`, and lie within its footprint. -/
theorem split_preserves_i2 {k : K} {s s' : S3} {src : Nat} {rs : List (List Nat)} (h2 : I2 s)
    (h : SplitStep k src rs s (.ok s')) : I2 s' := by
  obtain ⟨hp, rfl⟩ := Guarded.ok_iff.1 h
  obtain ⟨x, hx, -, hm, hfp⟩ := split_src hp
  exact split_induct I2 (fun _ _ h2 hx hfp => addAuth_i2 h2 hx (by rw [hm]; exact Mode.le_refl _)
    hfp) rs s h2 hx hfp

/-- `split` preserves I3 (§52, §61 effect: no anchor changes). -/
theorem split_preserves_i3 {k : K} {s s' : S3} {src : Nat} {rs : List (List Nat)} (h3 : I3 s)
    (h : SplitStep k src rs s (.ok s')) : I3 s' := by
  obtain ⟨hp, rfl⟩ := Guarded.ok_iff.1 h
  obtain ⟨x, hx, -, -, hfp⟩ := split_src hp
  exact split_induct I3 (fun _ _ h3 _ _ => addAuth_i3 h3 _) rs s h3 hx hfp

/-- `split` preserves `AnchorOrder` (§44, §54, §61 effect). -/
theorem split_preserves_anchorOrder {k : K} {s s' : S3} {src : Nat} {rs : List (List Nat)}
    (hao : AnchorOrder s) (h : SplitStep k src rs s (.ok s')) : AnchorOrder s' := by
  obtain ⟨hp, rfl⟩ := Guarded.ok_iff.1 h
  obtain ⟨x, hx, -, -, hfp⟩ := split_src hp
  exact split_induct AnchorOrder (fun _ _ h _ _ => addAuth_anchorOrder h _) rs s hao hx hfp

/-- `split` preserves `NoDangling` (§54, §61.2): each region is within the footprint of the active
source. -/
theorem split_preserves_noDangling {k : K} {s s' : S3} {src : Nat} {rs : List (List Nat)}
    (hnd : NoDangling s) (h : SplitStep k src rs s (.ok s')) : NoDangling s' := by
  obtain ⟨hp, rfl⟩ := Guarded.ok_iff.1 h
  obtain ⟨x, hx, xa, -, hfp⟩ := split_src hp
  exact split_induct NoDangling (fun _ _ h hx hfp => addAuth_noDangling h hx xa hfp)
    rs s hnd hx hfp

/-- `split` preserves `AnchorOrderHeld` (§44, §54, §61 effect: the new authorities are held by the
current frame). -/
theorem split_preserves_anchorOrderHeld {k : K} {s s' : S3} {src : Nat} {rs : List (List Nat)}
    (haoh : AnchorOrderHeld s) (h : SplitStep k src rs s (.ok s')) : AnchorOrderHeld s' := by
  obtain ⟨hp, rfl⟩ := Guarded.ok_iff.1 h
  obtain ⟨x, hx, -, -, hfp⟩ := split_src hp
  exact split_induct AnchorOrderHeld (fun _ _ h _ _ => addAuth_anchorOrderHeld h rfl)
    rs s haoh hx hfp

/-- `split` preserves the auxiliary `RootHeldConv` (§40, §49.7, §61 effect: the new authorities have
an origin). -/
theorem split_preserves_rootHeldConv {k : K} {s s' : S3} {src : Nat} {rs : List (List Nat)}
    (hc : RootHeldConv s) (h : SplitStep k src rs s (.ok s')) : RootHeldConv s' := by
  obtain ⟨hp, rfl⟩ := Guarded.ok_iff.1 h
  obtain ⟨x, hx, -, -, hfp⟩ := split_src hp
  exact split_induct RootHeldConv (fun _ _ h _ _ => addAuth_rootHeldConv h rfl) rs s hc hx hfp

/-- `split` preserves the kernel invariant `KInv` and `KAux` (§57, §58, §61) under the obligation
`DDSound(K)` (§57, §80). -/
theorem split_preserves {k : K} (hdd : DDSound k) {s s' : S3} {src : Nat} {rs : List (List Nat)}
    (hinv : KInv s) (haux : KAux s) (h : SplitStep k src rs s (.ok s')) : KInv s' ∧ KAux s' := by
  obtain ⟨hw, ⟨⟨h1, h2, h3, -⟩, hao, hnd⟩, haoh, -⟩ := hinv
  exact ⟨kInv_of (split_preserves_wf3 hw h)
    ⟨⟨split_preserves_exclusivity hdd h1 h, split_preserves_i2 h2 h, split_preserves_i3 h3 h,
      i4_always _⟩, split_preserves_anchorOrder hao h, split_preserves_noDangling hnd h⟩
    (split_preserves_anchorOrderHeld haoh h), split_preserves_rootHeldConv haux h⟩

/-- Adding an authority not covering `p` keeps the effective mode of `src` on `p`, through the
whole `split` (§43, §61 effect). -/
private theorem split_effective_notin {src p : Nat} {x : Authority} :
    ∀ (rs : List (List Nat)) (s : S3), s.A[src]? = some x → (∀ r ∈ rs, p ∉ r) →
      effective (splitEff s src rs) src p = effective s src p
  | [], s, _, _ => by simp [splitEff]
  | r :: rs, s, hx, hp => by
    have hs := lt_of_getElem? hx
    rw [splitEff_cons, split_effective_notin rs _ (by rw [addAuth_lt hs]; exact hx)
      (fun r' hr' => hp r' (List.mem_cons_of_mem _ hr')),
      effective_addAuth_notin hs (hp r (List.mem_cons_self ..))]

/-- An absent effective mode stays absent when an authority is added (§43, case 1 or 3). -/
private theorem effective_addAuth_none {s : S3} {y₀ : Authority} {a p : Nat} (ha : a < s.A.length)
    (h : effective s a p = none) : effective (s.addAuth y₀) a p = none := by
  unfold effective at h ⊢
  rw [addAuth_lt ha]
  cases hx : s.A[a]? with
  | none => rfl
  | some x =>
    rw [hx] at h; simp only at h ⊢
    split
    · rename_i hc
      rw [ite_eq_left hc] at h
      rw [descModes_addAuth]
      unfold effOf at h ⊢
      by_cases h0 : descModes s a p = []
      · rw [ite_eq_left h0] at h; cases h
      · rw [ite_eq_right h0] at h
        by_cases hm : Mode.modify ∈ descModes s a p
        · rw [ite_eq_right (fun e => h0 (List.append_eq_nil_iff.1 e).1),
            ite_eq_left (List.mem_append_left _ hm)]
        · rw [ite_eq_right hm] at h; cases h
    · rfl

/-- Adding a `Modify` authority derived from `src` and covering `p` removes the effective mode of
`src` on `p` (§43, case 3). -/
private theorem effective_addAuth_desc {s : S3} {src p : Nat} {r : List Nat} {hd : Holder}
    (hs : src < s.A.length) (hp : p ∈ r) :
    effective (s.addAuth ⟨.modify, some src, r, hd, true⟩) src p = none := by
  unfold effective
  rw [addAuth_lt hs]
  cases hx : s.A[src]? with
  | none => rfl
  | some x =>
    simp only
    split
    · rw [descModes_addAuth, ite_eq_left ⟨rfl, hp, by rw [ancs_addAuth_self rfl hs]; exact
        List.mem_cons_self⟩]
      unfold effOf
      rw [ite_eq_right (fun e => List.cons_ne_nil _ _ (List.append_eq_nil_iff.1 e).2),
        ite_eq_left (List.mem_append_right _ (List.mem_singleton_self _))]
    · rfl

/-- After a `split`, `src` has no effective mode on a leaf of a region (§43, case 3, §61 effect). -/
private theorem split_effective_in {src p : Nat} :
    ∀ (rs : List (List Nat)) (s : S3), src < s.A.length →
      (effective s src p = none ∨ ∃ r ∈ rs, p ∈ r) → effective (splitEff s src rs) src p = none
  | [], s, _, h => by
    rcases h with h | ⟨r, hr, -⟩
    · simpa [splitEff] using h
    · cases hr
  | r :: rs, s, hs, h => by
    rw [splitEff_cons]
    refine split_effective_in rs _ (by simp only [S3.addAuth, List.length_append]; omega) ?_
    rcases h with h | ⟨r', hr', hp⟩
    · exact .inl (effective_addAuth_none hs h)
    · rcases List.mem_cons.1 hr' with rfl | hr'
      · exact .inl (effective_addAuth_desc hs hp)
      · exact .inr ⟨r', hr', hp⟩

/-- Effect of `split` on its source (§61 effect, §43): on a leaf of no region (undistributed), the
effective mode of `src` is unchanged; on a leaf of a region (distributed), it becomes absent, so in
particular `src` loses effective `Modify` there. -/
theorem split_keeps_undistributed {k : K} {s s' : S3} {src : Nat} {rs : List (List Nat)}
    (h : SplitStep k src rs s (.ok s')) (p : Nat) :
    ((∀ r ∈ rs, p ∉ r) → effective s' src p = effective s src p) ∧
      ((∃ r ∈ rs, p ∈ r) → effective s' src p = none) := by
  obtain ⟨hp, rfl⟩ := Guarded.ok_iff.1 h
  obtain ⟨x, hx, -⟩ := hp.active
  exact ⟨split_effective_notin rs s hx, fun hin =>
    split_effective_in rs s (lt_of_getElem? hx) (.inr hin)⟩

/-! ## O3 `release` (§62) -/

/-- The authorities after a release (§62 effect). -/
private theorem release_get {s : S3} {a : Nat} {x : Authority} (hx : s.A[a]? = some x) (j : Nat) :
    (releaseEff s a).A[j]? = if a = j then some { x with active := false } else s.A[j]? := by
  rw [releaseEff_eq hx]; exact set_get (lt_of_getElem? hx)

/-- A release keeps the places (§62 effect). -/
private theorem release_P (s : S3) (a : Nat) : (releaseEff s a).P = s.P := by
  unfold releaseEff; split <;> rfl

/-- A release keeps the stack (§62 effect). -/
private theorem release_F (s : S3) (a : Nat) : (releaseEff s a).F = s.F := by
  unfold releaseEff; split <;> rfl

/-- A release keeps the death markers (§62 effect). -/
private theorem release_dead (s : S3) (a : Nat) : (releaseEff s a).dead = s.dead := by
  unfold releaseEff; split <;> rfl

/-- A release keeps the next frame identity (§62 effect). -/
private theorem release_nF (s : S3) (a : Nat) : (releaseEff s a).nF = s.nF := by
  unfold releaseEff; split <;> rfl

/-- An authority after a release is an authority before, with the same fields, active only if it
was active and is not the released one (§62 effect). -/
private theorem release_back {s : S3} {a : Nat} {x : Authority} (hx : s.A[a]? = some x) {j : Nat}
    {z : Authority} (hz : (releaseEff s a).A[j]? = some z) :
    ∃ z₀, s.A[j]? = some z₀ ∧ z.mode = z₀.mode ∧ z.origin = z₀.origin ∧
      z.footprint = z₀.footprint ∧ z.holder = z₀.holder ∧
      (z.active = true → z₀.active = true ∧ j ≠ a) := by
  rw [release_get hx] at hz; split at hz
  · subst_vars; cases hz; exact ⟨x, hx, rfl, rfl, rfl, rfl, by simp⟩
  · exact ⟨z, hz, rfl, rfl, rfl, rfl, fun hz' => ⟨hz', Ne.symm ‹_›⟩⟩

/-- An authority before a release is an authority after, with the same fields but its activity
(§62 effect). -/
private theorem release_fwd {s : S3} {a : Nat} {x : Authority} (hx : s.A[a]? = some x) {j : Nat}
    {z : Authority} (hz : s.A[j]? = some z) :
    ∃ z', (releaseEff s a).A[j]? = some z' ∧ z'.mode = z.mode ∧ z'.origin = z.origin ∧
      z'.footprint = z.footprint ∧ z'.holder = z.holder := by
  rw [release_get hx]; split
  · subst_vars; rw [hx] at hz; cases hz; exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨z, hz, rfl, rfl, rfl, rfl⟩

/-- A release keeps the rule of §44 for every anchor: origin chains and holders are unchanged. -/
private theorem effAnchorOK_release {s : S3} {a : Nat} {x : Authority} (hx : s.A[a]? = some x)
    (e : Nat) (fd : Option Nat) : EffAnchorOK (releaseEff s a) e fd ↔ EffAnchorOK s e fd := by
  have he : (releaseEff s a).effAnchor e = s.effAnchor e := by
    simp only [S3.effAnchor, release_ancs hx]
  have hH : (releaseEff s a).hframe = s.hframe := funext (S3.hframe_congr (release_P s a))
  unfold EffAnchorOK
  rw [he, hH, release_F, release_get hx]
  split
  · rename_i h; rw [← h, hx]; exact Iff.rfl
  · exact Iff.rfl

/-- Usability after a release is usability before (§40, §62 effect). -/
private theorem release_usable {s : S3} {a q : Nat} : (releaseEff s a).Usable q ↔ s.Usable q :=
  S3.Usable.congr (release_P s a) (release_F s a) (release_dead s a)

/-- `release` preserves `WF3` (§49, §62): it changes only the activity of a derived authority, so
footprints (§49.4) and active root authorities (§49.7) are unchanged. -/
theorem release_preserves_wf3 {s s' : S3} {a : Nat} (hw : WF3 s)
    (h : ReleaseStep a s (.ok s')) : WF3 s' := by
  obtain ⟨hp, rfl⟩ := Guarded.ok_iff.1 h
  obtain ⟨x, hx, -⟩ := hp.active
  have hder : x.origin ≠ none := by have := hp.derived; rw [hx] at this; exact this
  have hP := release_P s a
  refine ⟨by rw [release_F, release_nF]; exact hw.frames,
    by rw [hP, release_dead]; exact hw.places,
    ⟨by rw [hP, release_nF]; exact hw.owners.1, by rw [hP]; exact hw.owners.2.1, fun q hq => ?_⟩,
    fun b y hb l hl => ?_, fun b y o hb ho => ?_,
    hw.rootChain.transport (by rw [hP]) (by rw [hP]) (fun _ => by rw [release_ancs hx])
      (fun b y' hb => by obtain ⟨y₀, hy₀, -, -, e', -⟩ := release_back hx hb; exact ⟨y₀, hy₀, e'⟩)
      (fun i z hz hzo => by
        obtain ⟨z', hz', -, e1, e2, -⟩ := release_fwd hx hz; exact ⟨z', hz', e1.trans hzo, e2⟩),
    hw.rootHeld.transport hP (fun _ hu => release_usable.1 hu) (fun i z hz _ hzo => ?_),
    fun b y hb ya => ?_⟩
  · obtain ⟨f, hf, hfF⟩ := hw.owners.2.2 q (release_usable.1 hq)
    exact ⟨f, (FrameOf.congr hP).2 hf, by rw [release_F]; exact hfF⟩
  · obtain ⟨y₀, hy₀, -, -, e', -⟩ := release_back hx hb
    rw [hP]; exact hw.footprints b y₀ hy₀ l (e' ▸ hl)
  · obtain ⟨y₀, hy₀, -, e', -⟩ := release_back hx hb
    exact hw.origins b y₀ o hy₀ (e' ▸ ho)
  · rw [release_get hx]; split
    · rename_i e; subst e; rw [hx] at hz; cases hz; exact absurd hzo hder
    · exact hz
  · obtain ⟨y₀, hy₀, -, -, -, eh, ea⟩ := release_back hx hb
    rw [eh, HolderLive.congr hP (release_F s a) (release_dead s a)]
    exact hw.holders b y₀ hy₀ (ea ya).1

/-- `release` preserves I1 (§50, §62 effect): it only deactivates an authority. -/
theorem release_preserves_exclusivity {s s' : S3} {a : Nat} (h1 : I1 s)
    (h : ReleaseStep a s (.ok s')) : I1 s' := by
  obtain ⟨hp, rfl⟩ := Guarded.ok_iff.1 h
  obtain ⟨x, hx, -⟩ := hp.active
  intro a' b' x' y' p hab ha' hb' xa' ya' xp yp hnab hnba
  obtain ⟨x₀, hx₀, m₁, -, f₁, -, ac₁⟩ := release_back hx ha'
  obtain ⟨y₀, hy₀, m₂, -, f₂, -, ac₂⟩ := release_back hx hb'
  rw [release_ancs hx] at hnab hnba; rw [m₁, m₂]
  exact h1 a' b' x₀ y₀ p hab hx₀ hy₀ (ac₁ xa').1 (ac₂ ya').1 (f₁ ▸ xp) (f₂ ▸ yp) hnab hnba

/-- `release` preserves I2 (§51, §62 effect): origins, modes and footprints are unchanged. -/
theorem release_preserves_i2 {s s' : S3} {a : Nat} (h2 : I2 s)
    (h : ReleaseStep a s (.ok s')) : I2 s' := by
  obtain ⟨hp, rfl⟩ := Guarded.ok_iff.1 h
  obtain ⟨x, hx, -⟩ := hp.active
  intro b y o hb ho
  obtain ⟨y₀, hy₀, m₀, e', f₀, -⟩ := release_back hx hb
  obtain ⟨x₁, hx₁, hm, hh⟩ := h2 b y₀ o hy₀ (e' ▸ ho)
  obtain ⟨x₁', hx₁', em, -, ef, -⟩ := release_fwd hx hx₁
  exact ⟨x₁', hx₁', by rw [m₀, em]; exact hm, fun p hp' => by rw [ef]; exact hh p (f₀ ▸ hp')⟩

/-- `release` preserves I3 (§52, §62.3, §62.4): no usable place but the holding place keeps the
released authority as anchor, and the effect removes it from the holding place. -/
theorem release_preserves_i3 {s s' : S3} {a : Nat} (h3 : I3 s)
    (h : ReleaseStep a s (.ok s')) : I3 s' := by
  obtain ⟨hp, rfl⟩ := Guarded.ok_iff.1 h
  obtain ⟨x, hx, -⟩ := hp.active
  intro q hq y hy
  have hq' := release_usable.1 hq
  obtain ⟨hy', hya⟩ := release_D_mem hx hy
  obtain ⟨z, hz, za⟩ := h3 q hq' y hy'
  refine ⟨z, ?_, za⟩
  rw [release_get hx]; split
  · rename_i e; subst e
    have := hp.anchors q (List.mem_range.2 hq'.lt) hq' hy'
    rw [hx] at this; exact absurd (Option.some.inj this) (hya rfl)
  · exact hz

/-- `release` preserves `AnchorOrder` (§44, §54, §62 effect): anchors only disappear; origin chains
and holders are unchanged. -/
theorem release_preserves_anchorOrder {s s' : S3} {a : Nat} (hao : AnchorOrder s)
    (h : ReleaseStep a s (.ok s')) : AnchorOrder s' := by
  obtain ⟨hp, rfl⟩ := Guarded.ok_iff.1 h
  obtain ⟨x, hx, -⟩ := hp.active
  intro q hq y hy
  rw [S3.pframe_congr (release_P s a)]
  exact (effAnchorOK_release hx y _).2 (hao q (release_usable.1 hq) y (release_D_mem hx hy).1)

/-- `release` preserves `NoDangling` (§54, §62 effect): it activates nothing. -/
theorem release_preserves_noDangling {s s' : S3} {a : Nat} (hnd : NoDangling s)
    (h : ReleaseStep a s (.ok s')) : NoDangling s' := by
  obtain ⟨hp, rfl⟩ := Guarded.ok_iff.1 h
  obtain ⟨x, hx, -⟩ := hp.active
  intro j z hz za q hq l hl hlz
  obtain ⟨z₀, hz₀, -, -, ef, -, ea⟩ := release_back hx hz
  rw [release_P] at hl
  exact hnd j z₀ hz₀ (ea za).1 q (fun h' => hq (release_usable.2 h')) l hl (ef ▸ hlz)

/-- `release` preserves `AnchorOrderHeld` (§44, §54, §62 effect): it activates nothing and keeps
holders and origin chains. -/
theorem release_preserves_anchorOrderHeld {s s' : S3} {a : Nat} (haoh : AnchorOrderHeld s)
    (h : ReleaseStep a s (.ok s')) : AnchorOrderHeld s' := by
  obtain ⟨hp, rfl⟩ := Guarded.ok_iff.1 h
  obtain ⟨x, hx, -⟩ := hp.active
  intro q hq e y hy ya hh
  obtain ⟨y₀, hy₀, -, -, -, eh, ea⟩ := release_back hx hy
  rw [S3.pframe_congr (release_P s a)]
  exact (effAnchorOK_release hx e _).2 (haoh q (release_usable.1 hq) e y₀ hy₀ (ea ya).1 (eh ▸ hh))

/-- `release` preserves the auxiliary `RootHeldConv` (§40, §49.7, §62 effect). -/
theorem release_preserves_rootHeldConv {s s' : S3} {a : Nat} (hc : RootHeldConv s)
    (h : ReleaseStep a s (.ok s')) : RootHeldConv s' := by
  obtain ⟨hp, rfl⟩ := Guarded.ok_iff.1 h
  obtain ⟨x, hx, -⟩ := hp.active
  exact hc.transport (release_P s a) fun i z' hz hzo => by
    obtain ⟨z₀, hz₀, -, e1, e2, e3, -⟩ := release_back hx hz
    exact ⟨z₀, hz₀, e1 ▸ hzo, e2, e3⟩

/-- `release` preserves the kernel invariant `KInv` and `KAux` (§57, §58, §62). -/
theorem release_preserves {s s' : S3} {a : Nat} (hinv : KInv s) (haux : KAux s)
    (h : ReleaseStep a s (.ok s')) : KInv s' ∧ KAux s' := by
  obtain ⟨hw, ⟨⟨h1, h2, h3, -⟩, hao, hnd⟩, haoh, -⟩ := hinv
  exact ⟨kInv_of (release_preserves_wf3 hw h)
    ⟨⟨release_preserves_exclusivity h1 h, release_preserves_i2 h2 h, release_preserves_i3 h3 h,
      i4_always _⟩, release_preserves_anchorOrder hao h, release_preserves_noDangling hnd h⟩
    (release_preserves_anchorOrderHeld haoh h), release_preserves_rootHeldConv haux h⟩

/-- Restoration of rights by `release` (§62 effect, §26, §32): if `b`, derived from `a`, is the
only active descendant of `a` covering `p`, then before the release `a` has no effective mode on `p`
when `b` is a `Modify` authority covering `p`, and after it the effective mode of `a` on `p` is its
own mode. -/
theorem release_restores_authority {s s' : S3} {b a p : Nat} {y x : Authority} (hw : WF3 s)
    (h : ReleaseStep b s (.ok s')) (hy : s.A[b]? = some y) (ho : y.origin = some a)
    (hx : s.A[a]? = some x) (xa : x.active = true) (xp : p ∈ x.footprint)
    (honly : ∀ j z, s.A[j]? = some z → z.active = true → p ∈ z.footprint → a ∈ s.ancs j →
      j = b) :
    (y.mode = .modify → p ∈ y.footprint → effective s a p = none) ∧
      effective s' a p = some x.mode := by
  obtain ⟨hp, rfl⟩ := Guarded.ok_iff.1 h
  obtain ⟨y', hy', ya⟩ := hp.active
  rw [hy] at hy'; cases hy'
  have hab : a < b := hw.origins b y a hy ho
  have hanc : a ∈ s.ancs b := by
    unfold S3.ancs; rw [chain_cons (by simp [S3.org, hy, ho]) hab]; exact List.mem_cons_self ..
  refine ⟨fun hm hpy => ?_, ?_⟩
  · rw [effective_eq hx xa xp]
    have hmem : Mode.modify ∈ descModes s a p := mem_descModes.2 ⟨b, y, hy, ya, hpy, hanc, hm⟩
    unfold effOf
    rw [ite_eq_right (List.ne_nil_of_mem hmem), ite_eq_left hmem]
  · have hx' : (releaseEff s b).A[a]? = some x := by
      rw [release_get hy, ite_eq_right (Nat.ne_of_lt hab).symm]; exact hx
    rw [effective_eq hx' xa xp]
    have hnil : descModes (releaseEff s b) a p = [] := by
      apply nil_of_forall_not_mem; intro e he
      obtain ⟨j, z, hz, za, zp, hj, -⟩ := mem_descModes.1 he
      rw [release_ancs hy] at hj
      obtain ⟨z₀, hz₀, -, -, ef, -, ea⟩ := release_back hy hz
      exact (ea za).2 (honly j z₀ hz₀ (ea za).1 (ef ▸ zp) hj)
    rw [hnil]; rfl

/-! ## Determinism and `ok` outcomes (§58) -/

/-- `derive` has one outcome (§58, §60). -/
theorem derive_det {src : Nat} {region : List Nat} {m : Mode} {s : S3} {o₁ o₂ : Outcome3 S3}
    (h₁ : DeriveStep src region m s o₁) (h₂ : DeriveStep src region m s o₂) : o₁ = o₂ :=
  Guarded.det h₁ h₂

/-- The `ok` outcome of `derive`: its preconditions hold and the state is its effect (§58,
§60). -/
theorem derive_ok_iff {src : Nat} {region : List Nat} {m : Mode} {s s' : S3} :
    DeriveStep src region m s (.ok s') ↔
      DerivePre s src region m ∧ s' = deriveEff s src region m :=
  Guarded.ok_iff

/-- `split` has one outcome (§58, §61). -/
theorem split_det {k : K} {src : Nat} {rs : List (List Nat)} {s : S3} {o₁ o₂ : Outcome3 S3}
    (h₁ : SplitStep k src rs s o₁) (h₂ : SplitStep k src rs s o₂) : o₁ = o₂ := Guarded.det h₁ h₂

/-- The `ok` outcome of `split`: its preconditions hold and the state is its effect (§58, §61). -/
theorem split_ok_iff {k : K} {src : Nat} {rs : List (List Nat)} {s s' : S3} :
    SplitStep k src rs s (.ok s') ↔ SplitPre k s src rs ∧ s' = splitEff s src rs :=
  Guarded.ok_iff

/-- `release` has one outcome (§58, §62). -/
theorem release_det {a : Nat} {s : S3} {o₁ o₂ : Outcome3 S3}
    (h₁ : ReleaseStep a s o₁) (h₂ : ReleaseStep a s o₂) : o₁ = o₂ := Guarded.det h₁ h₂

/-- The `ok` outcome of `release`: its preconditions hold and the state is its effect (§58,
§62). -/
theorem release_ok_iff {a : Nat} {s s' : S3} :
    ReleaseStep a s (.ok s') ↔ ReleasePre s a ∧ s' = releaseEff s a :=
  Guarded.ok_iff

/-! ## `split` without `DDSound` (§61, note) -/

namespace SplitWithoutDD

/-- A contract declaring every pair of regions disjoint (§61.3), which violates `DDSound` (§80);
its other components are irrelevant to `split`. -/
def KDD : K := ⟨fun _ _ => True, fun _ => False, fun _ => False, fun _ => False, fun _ => False,
  fun _ _ => False, fun _ _ _ => False⟩

/-- Decidability of `KDD.DeclaredDisjoint` (§61.3). -/
instance : ∀ r r', Decidable (KDD.DeclaredDisjoint r r') := fun _ _ => instDecidableTrue

/-- One static root leaf, `Init`, owned by the base frame (§47). -/
def cst : Statics := [((none, none, 0), true)]

/-- The initial state of `cst` (§47). -/
def cs0 : S3 := S3.init cst

/-- The places of `cs0` (§47). -/
theorem cs0_P : cs0.P = [⟨none, .frame 0, 0⟩] := by decide

/-- The authorities of `cs0`: the root authority of place 0 (§47). -/
theorem cs0_A : cs0.A = [⟨.modify, none, [0], .frame 0, true⟩] := by decide

/-- The only element of a singleton list (§38: identities are list indices). -/
private theorem get_one {α : Type} {a v : α} : ∀ {q : Nat}, [a][q]? = some v → q = 0 ∧ v = a
  | 0, h => by simp at h; exact ⟨rfl, h.symm⟩
  | _ + 1, h => by simp at h

/-- `cs0` satisfies the kernel invariant `KInv` (§57). -/
theorem cs0_kInv : KInv cs0 := by
  have hP := cs0_P
  have hA := cs0_A
  have fp0 : footprint cs0.P 0 = [0] := by decide
  have hlt : ∀ r, r < cs0.P.length → r = 0 := fun r hr => by
    rw [hP] at hr; exact Nat.lt_one_iff.1 hr
  have hwf : WF3 cs0 :=
    { frames := by decide
      places := fun q pl r hq hr => by
        rw [hP] at hq; obtain ⟨rfl, rfl⟩ := get_one hq; cases hr
      owners := ⟨fun q pl f hq ho => by
          rw [hP] at hq; obtain ⟨rfl, rfl⟩ := get_one hq; cases ho; decide,
        fun q pl o hq ho => by (rw [hP] at hq; obtain ⟨rfl, rfl⟩ := get_one hq; cases ho),
        fun q hq => hq.frameOf⟩
      footprints := fun a x hx l hl => by
        rw [hA] at hx; obtain ⟨rfl, rfl⟩ := get_one hx
        rw [List.mem_singleton.1 hl]; decide
      origins := fun b y a hb ho => by
        rw [hA] at hb; obtain ⟨rfl, rfl⟩ := get_one hb; cases ho
      rootChain := fun a y l ha hl _ => by
        rw [hA] at ha; obtain ⟨rfl, rfl⟩ := get_one ha
        rw [List.mem_singleton.1 hl]
        exact ⟨0, _, 0, .inl rfl, by rw [hA]; rfl, rfl, by decide, by decide,
          fun l' => by rw [fp0]⟩
      rootHeld := fun r hr _ => by
        obtain rfl := hlt r hr.1
        exact ⟨0, _, _, by rw [hA]; rfl, rfl, rfl, rfl, by rw [hP]; rfl, rfl,
          fun l => by rw [fp0]⟩
      holders := fun a y hy _ => by
        rw [hA] at hy; obtain ⟨rfl, rfl⟩ := get_one hy; decide }
  refine kInv_of hwf ⟨⟨fun a b x y p hab ha hb _ _ _ _ _ _ => ?_, fun b y a hb ho => ?_,
    fun q _ x hx => ?_, i4_always _⟩, fun q _ x hx => ?_, fun j y hy _ q hq l hl hly => ?_⟩
    fun q _ x y hy _ hh => ?_
  · rw [hA] at ha hb
    obtain ⟨rfl, -⟩ := get_one ha; obtain ⟨rfl, -⟩ := get_one hb; exact absurd rfl hab
  · rw [hA] at hb; obtain ⟨rfl, rfl⟩ := get_one hb; cases ho
  · simp [cs0, S3.init] at hx
  · simp [cs0, S3.init] at hx
  · rw [hA] at hy; obtain ⟨rfl, rfl⟩ := get_one hy
    rw [List.mem_singleton.1 hly] at hl
    obtain ⟨-, -, -, h0⟩ := mem_footprint.1 hl
    rcases h0 with rfl | h0
    · exact hq (by decide)
    · simp [chain, chainF] at h0
  · rw [hA] at hy; obtain ⟨rfl, rfl⟩ := get_one hy; cases hh

/-- `cs0` satisfies the auxiliary `KAux` (§40, §49.7). -/
theorem cs0_kAux : KAux cs0 := by
  intro x z l r hx _ _ hr _
  rw [cs0_A] at hx; obtain ⟨rfl, rfl⟩ := get_one hx
  have : r = 0 := by have := hr.1; rw [cs0_P] at this; exact Nat.lt_one_iff.1 this
  subst this
  exact ⟨_, by rw [cs0_P]; rfl, rfl⟩

end SplitWithoutDD

open SplitWithoutDD in
/-- Without the obligation `DDSound(K)` (§61, note; §80), an accepted `split` may violate I1 (§50):
from `S3.init cst`, a state satisfying `KInv` and `KAux` (§57), `split` of the root authority into
two copies of the same leaf, declared disjoint by `KDD`, is `ok` and reaches a state with two
active unrelated `Modify` authorities on that leaf. -/
theorem split_unsound_without_DD :
    ¬ DDSound KDD ∧ KInv cs0 ∧ KAux cs0 ∧
      SplitStep KDD 0 [[0], [0]] cs0 (.ok (splitEff cs0 0 [[0], [0]])) ∧
      Reachable KDD cst (splitEff cs0 0 [[0], [0]]) ∧ ¬ I1 (splitEff cs0 0 [[0], [0]]) := by
  have hstep : SplitStep KDD 0 [[0], [0]] cs0 (.ok (splitEff cs0 0 [[0], [0]])) :=
    .ok (by decide)
  refine ⟨fun h => h [0] [0] trivial 0 (List.mem_singleton_self 0) (List.mem_singleton_self 0),
    cs0_kInv, cs0_kAux, hstep, .step .init (.split hstep), fun h => ?_⟩
  have := h 1 2 ⟨.modify, some 0, [0], .frame 0, true⟩ ⟨.modify, some 0, [0], .frame 0, true⟩ 0
    (by decide) (by decide) (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide)
  cases this.1

end Ern.MemoryModel.Access
