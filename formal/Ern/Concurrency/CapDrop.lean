import Ern.Concurrency.CapPreserve

/-!
# L1 on `cap5`: the remaining labels

Continuation of `Ern.Concurrency.CapPreserve` for `cap5_drop_own` (L1, WC5 C45, `OB-C17`; brief
of milestone 4, task 4). A transport of `Attr5` restricted to the authorities that carry a mode
somewhere (`Useful`), then one lemma per label: the labels that append authorities (`split`,
`alloc`, `enterFrame`, `spawn`), the composites (`issue`, `reset`, `spawnVal`), the labels that
release or reanchor authorities (`exitFrame`, `terminate`, `endUse`, `free`), and the assembly of
`Cap5DropOwn`.
-/

namespace Ern.Concurrency

open Ern.MemoryModel.Access

/-! ## Transport restricted to useful authorities -/

/-- An authority attributable in mode `m` contributes somewhere: its effective mode permits `m`
on some leaf (Spec 1 §43; WC5 C43). -/
def Useful (s : SC) (u : Nat) (m : Mode) : Prop := ∃ l, Allows (effective s.flat u l) m

/-- Parents precede their children (Spec 1 §49.2). -/
theorem parents_lt {t : S3} (hw : WF3 t) : ∀ q o, parentOf t.P q = some o → o < q := fun q o h => by
  unfold parentOf at h
  cases hq : t.P[q]? with
  | none => rw [hq] at h; cases h
  | some pl =>
    rw [hq] at h
    obtain ⟨_, _, hlt, _⟩ := hw.places q pl o hq h
    exact hlt

/-- Transport of `Attr5` from `s` to `s'` for context `c`, for the useful authorities only (brief
of milestone 4, task 3; WC5 C43): the frames of `c` stay live, the footprints of existing places
do not grow, and every useful authority attributable to `c` keeps its activity, own mode and
holder, stays outside the live `guarded` set, and keeps an effective mode permitting the mode in
which it is attributable. -/
theorem attr5_transport_u {s s' : SC} {reg reg' : SyncReg} {c : Nat} (hw : WF3 s.flat)
    (hstk : ∀ f ∈ s.stk c, f ∈ s'.stk c)
    (hfp : ∀ p, p < s.P.length → ∀ l ∈ footprint s'.P p, l ∈ footprint s.P p)
    (hA : ∀ u m y, Attr5 s reg c u m → Useful s u m → s.A[u]? = some y → ∃ y', s'.A[u]? = some y' ∧
      y'.active = y.active ∧ y'.mode = y.mode ∧ y'.holder = y.holder)
    (hng : ∀ u m, Attr5 s reg c u m → Useful s u m → NotGuarded s' reg' u)
    (heff : ∀ u m l, Attr5 s reg c u m → Allows (effective s.flat u l) m →
      Allows (effective s'.flat u l) m)
    {u : Nat} {m : Mode} (h : Attr5 s reg c u m) (hu : Useful s u m) : Attr5 s' reg' c u m := by
  have hP := parents_lt hw
  induction h with
  | @base a m y f hg hy ha hm hf hin =>
    have hab : Attr5 s reg c a m := .base hg hy ha hm hf hin
    obtain ⟨y', hy', ha', hm', hf'⟩ := hA a m y hab hu hy
    exact .base (hng a m hab hu) hy' (ha'.trans ha) (hm' ▸ hm) (hf'.trans hf) (hstk f hin)
  | @held a p b m y hg hy ha hm hp hb hc ih =>
    have hab : Attr5 s reg c a m := .held hg hy ha hm hp hb hc
    obtain ⟨y', hy', ha', hm', hp'⟩ := hA a m y hab hu hy
    have hup : s.flat.Usable p := by
      have := hw.holders a _ hy ha; rw [hp] at this; exact this
    obtain ⟨l₀, hl₀⟩ := footprint_ne hP _ p (Nat.le_refl _) hup.lt
    refine .held (hng a m hab hu) hy' (ha'.trans ha) (hm' ▸ hm) (hp'.trans hp)
      (ih ⟨l₀, hc l₀ hl₀⟩) fun l hl => heff b m l hb (hc l (hfp p hup.lt l hl))

/-- `cap5` of `c` does not decrease under the hypotheses of `attr5_transport_u`. -/
theorem cap5_transport_u {s s' : SC} {reg reg' : SyncReg} {c : Nat} (hw : WF3 s.flat)
    (hstk : ∀ f ∈ s.stk c, f ∈ s'.stk c)
    (hfp : ∀ p, p < s.P.length → ∀ l ∈ footprint s'.P p, l ∈ footprint s.P p)
    (hA : ∀ u m y, Attr5 s reg c u m → Useful s u m → s.A[u]? = some y → ∃ y', s'.A[u]? = some y' ∧
      y'.active = y.active ∧ y'.mode = y.mode ∧ y'.holder = y.holder)
    (hng : ∀ u m, Attr5 s reg c u m → Useful s u m → NotGuarded s' reg' u)
    (heff : ∀ u m l, Attr5 s reg c u m → Allows (effective s.flat u l) m →
      Allows (effective s'.flat u l) m) (l : Nat) :
    capRank (cap5 s reg c l) ≤ capRank (cap5 s' reg' c l) := by
  refine cap5_rank_mono fun m ⟨x, hx, ha, he⟩ =>
    ⟨x, ?_, attr5_transport_u hw hstk hfp hA hng heff ha ⟨l, he⟩, heff x m l ha he⟩
  have hlt := List.mem_range.1 hx
  obtain ⟨y, hy⟩ : ∃ y, s.A[x]? = some y := ⟨_, List.getElem?_eq_getElem hlt⟩
  obtain ⟨y', hy', -⟩ := hA x m y ha ⟨l, he⟩ hy
  exact List.mem_range.2 (lt_of_getElem? hy')

/-- A context without frames has no `cap5` (WC5 C43: attribution ends at a live frame). -/
theorem cap5_nil {s : SC} {reg : SyncReg} {c l : Nat} (h : s.stk c = []) :
    cap5 s reg c l = none := by
  have hno : ∀ u m, ¬ Attr5 s reg c u m := fun u m hu => by
    induction hu with
    | base _ _ _ _ _ hin => rw [h] at hin; simp at hin
    | held _ _ _ _ _ _ _ ih => exact ih
  unfold cap5
  have h1 : ¬ CapAt5 s reg c l .modify := fun ⟨x, _, hx, _⟩ => hno x _ hx
  have h2 : ¬ CapAt5 s reg c l .observe := fun ⟨x, _, hx, _⟩ => hno x _ hx
  simp only [h1, h2, ↓reduceIte]

/-- Fewer covering descendants keep an allowed mode (Spec 1 §43): if every active descendant of
`u` covering `l` in `t'` was an active descendant of `u` covering `l` in `t`, with the same mode,
and `u` keeps its activity, mode and footprint, an effective mode allowed in `t` is allowed in
`t'`. -/
theorem eff_keep_sub {t t' : S3} {u l : Nat} {m : Mode}
    (hu : ∀ z, t.A[u]? = some z → ∃ z', t'.A[u]? = some z' ∧ z'.active = z.active ∧
      z'.mode = z.mode ∧ z'.footprint = z.footprint)
    (hd : ∀ j y, t'.A[j]? = some y → y.active = true → l ∈ y.footprint → u ∈ t'.ancs j →
      ∃ y₀, t.A[j]? = some y₀ ∧ y₀.active = true ∧ l ∈ y₀.footprint ∧ u ∈ t.ancs j ∧
        y₀.mode = y.mode)
    (h : Allows (effective t u l) m) : Allows (effective t' u l) m := by
  obtain ⟨z, hz, hza, hzl, -⟩ := eff_present (allows_present h)
  obtain ⟨z', hz', ha', hm', hf'⟩ := hu z hz
  rw [effective_eq hz hza hzl] at h
  rw [effective_eq hz' (ha'.trans hza) (hf' ▸ hzl), hm']
  refine allows_effOf_sub (fun md hmd => ?_) h
  obtain ⟨j, y, hy, hya, hyl, hj, rfl⟩ := Ern.MemoryModel.Access.mem_descModes.1 hmd
  obtain ⟨y₀, hy₀, h1, h2, h3, h4⟩ := hd j y hy hya hyl hj
  exact Ern.MemoryModel.Access.mem_descModes.2 ⟨j, y₀, hy₀, h1, h2, h3, h4⟩

/-- An active `Modify` authority covering `l` below `u` leaves `u` no effective mode on `l`
(Spec 1 §43, case 3). -/
theorem no_eff_below_modify {t : S3} {src u l : Nat} {x : Authority} {m : Mode}
    (hx : t.A[src]? = some x) (hxa : x.active = true) (hxm : x.mode = .modify)
    (hxl : l ∈ x.footprint) (hanc : u ∈ t.ancs src) (h : Allows (effective t u l) m) : False := by
  obtain ⟨z, hz, hza, hzl, -⟩ := eff_present (allows_present h)
  rw [effective_eq hz hza hzl] at h
  have hin : x.mode ∈ descModes t u l := mem_descModes hx hxa hxl hanc
  rw [hxm] at hin
  rcases allows_effOf h with ⟨h0, -⟩ | ⟨hn, -⟩
  · rw [h0] at hin; simp at hin
  · exact hn hin

/-- `NotGuarded` when the former authorities keep their activity (WC4 C12): an entry live
afterwards was live before, or its `guarded` is a fresh identity. -/
theorem notGuarded_prefix {s s' : SC} {reg : SyncReg}
    (hact : ∀ j < s.A.length, ∀ y', s'.A[j]? = some y' → y'.active = true → s.flat.Active j)
    {u : Nat} (hu : u < s.A.length) (h : NotGuarded s reg u) : NotGuarded s' reg u :=
  fun e he hl => by
    obtain ⟨y', hy', hya⟩ := hl
    by_cases hlt : e.guarded < s.A.length
    · exact h e he (hact _ hlt y' hy' hya)
    · exact fun h' => hlt (h' ▸ hu)

/-- An attributable authority exists (WC5 C43). -/
theorem Attr5.lt {s : SC} {reg : SyncReg} {c u : Nat} {m : Mode} (h : Attr5 s reg c u m) :
    u < s.A.length := by
  cases h with
  | base _ hy => exact lt_of_getElem? hy
  | held _ hy => exact lt_of_getElem? hy

/-- Origin chains of the former authorities are kept when their origins are (Spec 1 §42). -/
theorem ancs_prefix {t t' : S3} (hold : ∀ i < t.A.length, t'.org i = t.org i) {j : Nat}
    (hj : j < t.A.length) : t'.ancs j = t.ancs j :=
  chain_congr fun i hi => hold i (Nat.lt_of_le_of_lt hi hj)

/-! ## `split` (Spec 1 §61) -/

/-- The authorities after `split` (Spec 1 §61, `ok` effect): the former ones, then one `Modify`
descendant of `src` per region. -/
theorem split_get {t : S3} {src : Nat} {rs : List (List Nat)} {j : Nat} {y : Authority}
    (h : (splitEff t src rs).A[j]? = some y) :
    (j < t.A.length ∧ t.A[j]? = some y) ∨
    (t.A.length ≤ j ∧ ∃ r ∈ rs, y = ⟨.modify, some src, r, .frame t.top, true⟩) := by
  simp only [splitEff] at h
  by_cases hj : j < t.A.length
  · rw [List.getElem?_append_left hj] at h; exact .inl ⟨hj, h⟩
  · rw [List.getElem?_append_right (by omega), List.getElem?_map] at h
    cases hr : rs[j - t.A.length]? with
    | none => rw [hr] at h; cases h
    | some r =>
      rw [hr] at h; cases h
      exact .inr ⟨by omega, r, List.mem_of_getElem? hr, rfl⟩

/-- `split` by context `c'` (Spec 1 §61) does not lower `cap5` of another context `c`: the new
authorities are `Modify` descendants of the source over leaves where the source has effective
`Modify` (§61.1), which excludes, for `c`, the source (`attr_compat`) and its ancestors (Spec 1
§43, case 3). -/
theorem split_cap5_mono {k : K} {s : SC} {reg : SyncReg} (hF : FramesC s) (hI : I1 s.flat)
    (hw : WF3 s.flat) {c c' src : Nat} {rs : List (List Nat)} (hcc : c ≠ c') (hlive : s.Live c')
    (hp : SplitPre k (s.view c') src rs) (l : Nat) :
    capRank (cap5 s reg c l) ≤ capRank (cap5 (s.set (splitEff (s.view c') src rs)) reg c l) := by
  have hne := hF.nonempty c' hlive
  have hvA : ∀ a l, effective (s.view c') a l = effective s.flat a l :=
    fun a l => effective_of_A rfl a l
  have hc'src : Attr s c' src .modify := attr_of_exercisable hne hp.exercisable
  obtain ⟨x, hx, hxa⟩ := hp.active
  have hxm : x.mode = .modify := by
    rcases exer_mode hp.exercisable hx with h | h
    · cases h
    · exact h
  have hsl : src < s.A.length := lt_of_getElem? hx
  have hpre : ∀ j < s.A.length, (splitEff (s.view c') src rs).A[j]? = s.A[j]? :=
    fun j hj => List.getElem?_append_left hj
  have horg : ∀ i < (s.view c').A.length, (splitEff (s.view c') src rs).org i = (s.view c').org i :=
    fun i hi => by unfold S3.org; rw [hpre i hi]; rfl
  refine cap5_transport_u (s' := s.set (splitEff (s.view c') src rs)) (reg' := reg) hw
    (fun f hf => hf) (fun p _ l hl => hl)
    (fun u m y hu _ hy => ⟨y, (by show (splitEff (s.view c') src rs).A[u]? = _
                                  rw [hpre u hu.lt]; exact hy), rfl, rfl, rfl⟩)
    (fun u m hu _ => notGuarded_prefix (fun j hj y' hy' hya => ⟨y', by
        have : (splitEff (s.view c') src rs).A[j]? = some y' := hy'
        rwa [hpre j hj] at this, hya⟩) hu.lt hu.notGuarded)
    (fun u m l hu hal => ?_) l
  show Allows (effective (splitEff (s.view c') src rs) u l) m
  rw [← hvA] at hal
  refine eff_keep_sub (fun z hz => ⟨z, by rw [hpre u hu.lt]; exact hz, rfl, rfl, rfl⟩)
    (fun j y hy hya hyl hj => ?_) hal
  rcases split_get hy with ⟨hjl, hy'⟩ | ⟨hjl, r, hr, rfl⟩
  · exact ⟨y, hy', hya, hyl, by rwa [ancs_prefix horg hjl] at hj, rfl⟩
  · exfalso
    have horg' : (splitEff (s.view c') src rs).org j = some src := by
      unfold S3.org; rw [hy]; rfl
    have hanc : (splitEff (s.view c') src rs).ancs j = src :: (s.view c').ancs src := by
      unfold S3.ancs
      rw [chain_cons horg' (by have : (s.view c').A.length = s.A.length := rfl; omega)]
      exact congrArg _ (ancs_prefix horg hsl)
    rw [hanc] at hj
    have hmod : effective s.flat src l = some .modify := by rw [← hvA]; exact hp.modifyOn r hr l hyl
    rcases List.mem_cons.1 hj with rfl | hanc'
    · exact attr_compat hF.nodup hI hw (Ne.symm hcc) hc'src rfl _ l m hmod hu.attr
        (by rw [← hvA]; exact hal)
    · have hxl : l ∈ x.footprint := by
        have := (hp.within r hr l hyl).1; unfold S3.afp at this; rw [hx] at this; exact this
      exact no_eff_below_modify hx hxa hxm hxl hanc' hal

/-! ## `alloc` (Spec 1 §71) -/

/-- `alloc` by context `c'` (Spec 1 §71) does not lower `cap5` of another context: the new root
authority has no origin, so it is a descendant of nothing, and the footprints of the former places
are kept (§71, `ok` effect). -/
theorem alloc_cap5_mono {k : K} {s : SC} {reg : SyncReg} (hw : WF3 s.flat) {c c' pr ow : Nat}
    {ls : LocalShape} (hst : AllocStatic k (s.view c') pr ow ls) (l : Nat) :
    capRank (cap5 s reg c l) ≤ capRank (cap5 (s.set (allocEff (s.view c') ow ls)) reg c l) := by
  have hvA : ∀ a l, effective (s.view c') a l = effective s.flat a l :=
    fun a l => effective_of_A rfl a l
  have hpre : ∀ j < s.A.length, (allocEff (s.view c') ow ls).A[j]? = s.A[j]? :=
    fun j hj => Alloc.A_lt hj
  refine cap5_transport_u (s' := s.set (allocEff (s.view c') ow ls)) (reg' := reg) hw
    (fun f hf => hf)
    (fun p hp l hl => (Alloc.footprint_old (s := s.view c') hst.shapeOK hp l).1 hl)
    (fun u m y hu _ hy => ⟨y, (by show (allocEff (s.view c') ow ls).A[u]? = _
                                  rw [hpre u hu.lt]; exact hy), rfl, rfl, rfl⟩)
    (fun u m hu _ => notGuarded_prefix (fun j hj y' hy' hya => ⟨y', by
        have : (allocEff (s.view c') ow ls).A[j]? = some y' := hy'
        rwa [hpre j hj] at this, hya⟩) hu.lt hu.notGuarded)
    (fun u m l hu hal => ?_) l
  show Allows (effective (allocEff (s.view c') ow ls) u l) m
  rw [← hvA] at hal
  refine eff_keep_sub (fun z hz => ⟨z, by rw [hpre u hu.lt]; exact hz, rfl, rfl, rfl⟩)
    (fun j y hy hya hyl hj => ?_) hal
  rw [Alloc.ancs_eq hst] at hj
  rcases Alloc.allocA_get hst hy with ⟨-, hy'⟩ | ⟨rfl, rfl⟩
  · exact ⟨y, hy', hya, hyl, hj, rfl⟩
  · exfalso
    have : (s.view c').org (s.view c').A.length = none := by
      unfold S3.org; rw [List.getElem?_eq_none (Nat.le_refl _)]; rfl
    rw [S3.ancs, chain_none this] at hj; simp at hj

/-! ## `enterFrame` and `spawn` (Spec 1 §72; WC4 C4) -/

/-- The kernel effect of `enterFrame` executed by `c'` (Spec 1 §72), read from another context `c`
holding none of the parameters: `cap5` of `c` does not decrease when the stack of `c` and the
registry are kept. The parameters are held by the current frame of `c'` (§72.1), the new root
authorities have no origin, and the footprints of the former places are kept (§72, `ok`
effect). -/
theorem enter_cap5_mono {s s' : SC} {reg : SyncReg} (hF : FramesC s) (hw : WF3 s.flat)
    {c c' : Nat} {ps : List Nat} {ls : LocalShape} (hcc : c ≠ c') (hne : s.stk c' ≠ [])
    (hparams : ∀ a ∈ ps, OptP ((s.view c').A[a]?) (fun y => y.active = true ∧
      y.holder = .frame (s.view c').top ∧ y.origin ≠ none) False)
    (hsh : ShapeOK s.P.length ls.toShape)
    (hk : s'.A = (enterEff (s.view c') ps ls).A ∧ s'.P = (enterEff (s.view c') ps ls).P)
    (hstk : ∀ f ∈ s.stk c, f ∈ s'.stk c) (l : Nat) :
    capRank (cap5 s reg c l) ≤ capRank (cap5 s' reg c l) := by
  have hvA : ∀ a l, effective (s.view c') a l = effective s.flat a l :=
    fun a l => effective_of_A rfl a l
  have hnp : ∀ u m, Attr5 s reg c u m → u ∉ ps := fun u m hu hup => by
    have hpu := hparams u hup
    unfold OptP at hpu
    split at hpu
    · rename_i y hy
      exact not_attr_frame (c := c) (c' := c') hF.nodup hcc hy hpu.2.1 (view_top_mem hne) hu.attr
    · exact hpu.elim
  have hpre : ∀ u m, Attr5 s reg c u m → s'.A[u]? = s.A[u]? := fun u m hu => by
    rw [hk.1, Frames.enter_lt (s := s.view c') hu.lt]
    show Option.map _ (s.A[u]?) = _
    simp [hnp u m hu]
  have hact : ∀ j < s.A.length, ∀ y', s'.A[j]? = some y' → y'.active = true → s.flat.Active j :=
    fun j hj y' hy' hya => by
      rw [hk.1] at hy'
      rcases Frames.enter_get hy' with ⟨-, y, hy, rfl⟩ | ⟨hjl, -⟩
      · refine ⟨y, hy, ?_⟩
        split at hya
        · exact hya
        · exact hya
      · exact absurd hj (Nat.not_lt.2 hjl)
  have heq : ∀ a l, effective s'.flat a l = effective (enterEff (s.view c') ps ls) a l :=
    fun a l => effective_of_A hk.1 a l
  refine cap5_transport_u (s' := s') (reg' := reg) hw hstk
    (fun p hp l hl => by
      rw [show s'.P = _ from hk.2] at hl
      exact (Frames.enter_footprint_old (s := s.view c') hsh hp l).1 hl)
    (fun u m y hu _ hy => ⟨y, by rw [hpre u m hu]; exact hy, rfl, rfl, rfl⟩)
    (fun u m hu _ => notGuarded_prefix hact hu.lt hu.notGuarded)
    (fun u m l hu hal => ?_) l
  rw [heq]
  rw [← hvA] at hal
  refine eff_keep_sub (fun z hz => ⟨z, by rw [← hk.1, hpre u m hu]; exact hz, rfl, rfl, rfl⟩)
    (fun j y hy hya hyl hj => ?_) hal
  rcases Frames.enter_get hy with ⟨hjl, y₀, hy₀, rfl⟩ | ⟨hjl, i, -, rfl⟩
  · refine ⟨y₀, hy₀, ?_, ?_, by rwa [Frames.enter_ancs_lt hjl] at hj, ?_⟩ <;>
      split at hya <;> first | exact hya | (split at hyl <;> exact hyl) | (split <;> rfl)
  · exfalso
    have : (enterEff (s.view c') ps ls).org j = none := by unfold S3.org; rw [hy]; rfl
    rw [S3.ancs, chain_none this] at hj; simp at hj

/-! ## State-level forms of `derive`, `store` and `transfer` -/

/-- `derive` by context `c'` (Spec 1 §60) does not lower `cap5` of another context (state form of
`cap5_drop_own_derive`). -/
theorem derive_cap5_mono {s : SC} {reg : SyncReg} (hF : FramesC s) (hI : I1 s.flat)
    (hw : WF3 s.flat) {c c' src : Nat} {region : List Nat} {md : Mode} (hcc : c ≠ c')
    (hlive : s.Live c') (hp : DerivePre (s.view c') src region md) (l : Nat) :
    capRank (cap5 s reg c l) ≤
      capRank (cap5 (s.set (deriveEff (s.view c') src region md)) reg c l) := by
  have hne := hF.nonempty c' hlive
  have hpre : ∀ j < s.A.length, (deriveEff (s.view c') src region md).A[j]? = s.A[j]? :=
    fun j hj => addAuth_lt (s := s.view c') hj
  refine cap5_transport_u (s' := s.set (deriveEff (s.view c') src region md)) (reg' := reg) hw
    (fun f hf => hf) (fun p _ l hl => hl)
    (fun u m y hu _ hy => ⟨y, (by show (deriveEff (s.view c') src region md).A[u]? = _
                                  rw [hpre u hu.lt]; exact hy), rfl, rfl, rfl⟩)
    (fun u m hu _ => notGuarded_prefix (fun j hj y' hy' hya => ⟨y', by
        have : (deriveEff (s.view c') src region md).A[j]? = some y' := hy'
        rwa [hpre j hj] at this, hya⟩) hu.lt hu.notGuarded)
    (fun u m l hu hal => ?_) l
  have := derive_eff_keep hF.nodup hI hw hcc hne hp hu.attr hal
  rw [effective_of_A (t := (s.set (deriveEff (s.view c') src region md)).flat)
    (t' := s.flat.addAuth ⟨md, some src, region, .frame (s.view c').top, true⟩) rfl]
  exact this

/-- `store` by context `c'` (Spec 1 §65) does not lower `cap5` of another context (state form of
`cap5_drop_own_store`). -/
theorem store_cap5_mono {s : SC} {reg : SyncReg} (hF : FramesC s) (hw : WF3 s.flat)
    {c c' a p : Nat} (hcc : c ≠ c') (hlive : s.Live c') (hp : StorePreC s c' a p) (l : Nat) :
    capRank (cap5 s reg c l) ≤ capRank (cap5 (storeEffC s c' a p) reg c l) := by
  have hne := hF.nonempty c' hlive
  have hsk : SameSkel s.flat (storeEffC s c' a p).flat := store_skel (s.view c') a p
  have hfa : ∀ u m, Attr5 s reg c u m → u ≠ a := fun u m hu hua => by
    subst hua
    have hd := hp.derivedHeld
    unfold OptP at hd
    split at hd
    · rename_i y hy
      exact not_attr_frame (c := c) (c' := c') hF.nodup hcc hy hd.2.2 (view_top_mem hne) hu.attr
    · exact hd.elim
  refine cap5_transport_u (s' := storeEffC s c' a p) (reg' := reg) hw (fun f hf => hf)
    (fun q _ l hl => by rwa [show (storeEffC s c' a p).P = s.P from storeEff_P _ a p] at hl)
    (fun u m y hu _ hy => ⟨y, ?_, rfl, rfl, rfl⟩)
    (fun u m hu _ => notGuarded_of_skel hsk (fun e he => ⟨e, he, rfl⟩) hu.notGuarded)
    (fun u m l _ hal => by rw [hsk.effective]; exact hal) l
  show (storeEff (s.view c') a p).A[u]? = some y
  unfold storeEff
  split
  · rw [List.getElem?_set_ne (Ne.symm (hfa u m hu))]; exact hy
  · exact hy

/-- `transfer` by context `c'` (Spec 1 §63) does not lower `cap5` of another context (state form of
`cap5_drop_own_transfer`). -/
theorem transfer_cap5_mono {k : K} {s : SC} {reg : SyncReg} (hF : FramesC s) (hI : I1 s.flat)
    (hw : WF3 s.flat) {c c' src dst : Nat} (hcc : c ≠ c') (hlive : s.Live c')
    (hp : TransferPreC k s c' src dst) (l : Nat) :
    capRank (cap5 s reg c l) ≤ capRank (cap5 (transferEffC s c' src dst) reg c l) := by
  have hne := hF.nonempty c' hlive
  have hsk : SameSkel s.flat (transferEffC s c' src dst).flat :=
    transfer_skel (s.view c') src dst
  obtain ⟨g, -, hgx, hge⟩ := hp.srcRight
  have hg : Attr s c' g .modify := attr_of_exercisable hne hgx
  have hge' : ∀ l ∈ footprint s.P src, Allows (effective s.flat g l) .modify :=
    fun l hl => by rw [← effective_of_A (t := s.view c') (t' := s.flat) rfl]; exact hge l hl
  have hkeep : ∀ u m y, Attr5 s reg c u m → s.A[u]? = some y → ¬ heldIn s.P src y.holder :=
    fun u m y hu hy hh => by
      cases hh' : y.holder with
      | frame f => rw [hh'] at hh; exact hh
      | place q =>
        rw [hh'] at hh
        exact not_attr_place hF.nodup hI hw hcc hy hh' hg
          (fun l hl => hge' l (footprint_sub hw hh hl)) hu.attr
  refine cap5_transport_u (s' := transferEffC s c' src dst) (reg' := reg) hw (fun f hf => hf)
    (fun p _ l hl => by
      have hl' : l ∈ footprint (transferEff (s.view c') src dst).P p := hl
      rwa [transfer_footprint] at hl')
    (fun u m y hu _ hy => ⟨y, ?_, rfl, rfl, rfl⟩)
    (fun u m hu _ => notGuarded_of_skel hsk (fun e he => ⟨e, he, rfl⟩) hu.notGuarded)
    (fun u m l _ hal => by rw [hsk.effective]; exact hal) l
  show (transferEff (s.view c') src dst).A[u]? = some y
  unfold transferEff
  simp only [List.getElem?_map]
  rw [show (s.view c').A[u]? = some y from hy]
  have hk : ¬ heldIn (s.view c').P src y.holder := hkeep u m y hu hy
  simp [hk]

/-! ## Trace-level lemmas -/

/-- The invariants of the states reached by an `EncapsulatedTrace5` from an initial state (T2,
T4: `trace_inv`), under `DDSound` (Spec 1 §80). -/
theorem trace5_kInvCA {k : K} {L : MutexLayout} {statics : Statics} {lbls : List Label}
    {st : SC × SyncReg × ArenaReg} (hdd : DDSound k) (hst : StaticsOK statics)
    (htr : EncapsulatedTrace5 k L (SC.ofS3 (S3.init statics), [], []) lbls st) : KInvCA st.1 :=
  (trace_inv hdd (encapsulatedTrace5_imp htr) (init_inv hdd hst L).1 (init_inv hdd hst L).2).1

/-- The frame structure, `WF3` and `I1` of a state satisfying `KInvCA` (WC4 C20; Spec 1 §49,
§50). -/
theorem KInvCA.parts {s : SC} (hk : KInvCA s) : FramesC s ∧ WF3 s.flat ∧ I1 s.flat :=
  ⟨hk.1.1.1, hk.1.1.2, hk.1.2.1.1.1⟩

/-- L1 (`cap5_drop_own`, WC5 C45) for `split` (Spec 1 §61). Under `DDSound` (Spec 1 §80), from a
state reached by an `EncapsulatedTrace5` from an initial state (Spec 1 §47). -/
theorem cap5_drop_own_split {k : K} {L : MutexLayout} {statics : Statics} {lbls : List Label}
    {st st' : SC × SyncReg × ArenaReg} {c' src : Nat} {rs : List (List Nat)} (hdd : DDSound k)
    (hst : StaticsOK statics)
    (htr : EncapsulatedTrace5 k L (SC.ofS3 (S3.init statics), [], []) lbls st)
    (h : LStep k L (.kernel c' (.split src rs)) st st') (c l : Nat)
    (hd : capRank (cap5 st'.1 st'.2.1 c l) < capRank (cap5 st.1 st.2.1 c l)) :
    (Label.kernel c' (.split src rs)).ctx = c := by
  obtain ⟨hF, hw, hI⟩ := (trace5_kInvCA hdd hst htr).parts
  refine Decidable.byContradiction fun hctx => ?_
  have hcc : c ≠ c' := fun e => hctx (e ▸ rfl)
  cases h with
  | @kernel s s' reg ar _ _ hk =>
    obtain ⟨hlive, o, hR, ho⟩ := hk
    cases hR with
    | reject => cases ho
    | ok hp =>
      cases ho
      exact absurd hd (Nat.not_lt.2 (split_cap5_mono hF hI hw hcc hlive hp l))

/-- L1 (`cap5_drop_own`, WC5 C45) for `alloc` (Spec 1 §71). Under `DDSound` (Spec 1 §80), from a
state reached by an `EncapsulatedTrace5` from an initial state (Spec 1 §47). -/
theorem cap5_drop_own_alloc {k : K} {L : MutexLayout} {statics : Statics} {lbls : List Label}
    {st st' : SC × SyncReg × ArenaReg} {c' pr ow : Nat} {ls : LocalShape} (hdd : DDSound k)
    (hst : StaticsOK statics)
    (htr : EncapsulatedTrace5 k L (SC.ofS3 (S3.init statics), [], []) lbls st)
    (h : LStep k L (.kernel c' (.alloc pr ow ls)) st st') (c l : Nat)
    (hd : capRank (cap5 st'.1 st'.2.1 c l) < capRank (cap5 st.1 st.2.1 c l)) :
    (Label.kernel c' (.alloc pr ow ls)).ctx = c := by
  obtain ⟨-, hw, -⟩ := (trace5_kInvCA hdd hst htr).parts
  exfalso
  cases h with
  | @kernel s s' reg ar _ _ hk =>
    obtain ⟨-, o, hR, ho⟩ := hk
    cases hR with
    | ok hsa _ => cases ho; exact absurd hd (Nat.not_lt.2 (alloc_cap5_mono hw hsa l))
    | fail => cases ho
    | reject => cases ho

/-- L1 (`cap5_drop_own`, WC5 C45) for `enterFrame` (Spec 1 §72). Under `DDSound` (Spec 1 §80),
from a state reached by an `EncapsulatedTrace5` from an initial state (Spec 1 §47). -/
theorem cap5_drop_own_enter {k : K} {L : MutexLayout} {statics : Statics} {lbls : List Label}
    {st st' : SC × SyncReg × ArenaReg} {c' : Nat} {ps : List Nat} {ls : LocalShape}
    (hdd : DDSound k) (hst : StaticsOK statics)
    (htr : EncapsulatedTrace5 k L (SC.ofS3 (S3.init statics), [], []) lbls st)
    (h : LStep k L (.kernel c' (.enter ps ls)) st st') (c l : Nat)
    (hd : capRank (cap5 st'.1 st'.2.1 c l) < capRank (cap5 st.1 st.2.1 c l)) :
    (Label.kernel c' (.enter ps ls)).ctx = c := by
  obtain ⟨hF, hw, -⟩ := (trace5_kInvCA hdd hst htr).parts
  refine Decidable.byContradiction fun hctx => ?_
  have hcc : c ≠ c' := fun e => hctx (e ▸ rfl)
  cases h with
  | @kernel s s' reg ar _ _ hk =>
    obtain ⟨-, hR⟩ := hk
    cases hR with
    | ok hp =>
      have hstk : ∀ f ∈ s.stk c, f ∈ (enterEffC s c' ps ls).stk c := fun f hf => by
        simp only [PreservationAux.enter_stk hp.callerLive c, hcc, ↓reduceIte]; exact hf
      exact absurd hd (Nat.not_lt.2 (enter_cap5_mono hF hw hcc hp.callerLive hp.params hp.localsOK
        ⟨rfl, rfl⟩ hstk l))

/-- L1 (`cap5_drop_own`, WC5 C45) for `spawn` (WC4 C4): the parameters go to the initial frame of
the new context, which had no `cap5` before the step. Under `DDSound` (Spec 1 §80), from a state
reached by an `EncapsulatedTrace5` from an initial state (Spec 1 §47). -/
theorem cap5_drop_own_spawn {k : K} {L : MutexLayout} {statics : Statics} {lbls : List Label}
    {st st' : SC × SyncReg × ArenaReg} {c' : Nat} {ps : List Nat} {ls : LocalShape}
    (hdd : DDSound k) (hst : StaticsOK statics)
    (htr : EncapsulatedTrace5 k L (SC.ofS3 (S3.init statics), [], []) lbls st)
    (h : LStep k L (.spawn c' ps ls) st st') (c l : Nat)
    (hd : capRank (cap5 st'.1 st'.2.1 c l) < capRank (cap5 st.1 st.2.1 c l)) :
    (Label.spawn c' ps ls).ctx = c := by
  obtain ⟨hF, hw, -⟩ := (trace5_kInvCA hdd hst htr).parts
  refine Decidable.byContradiction fun hctx => ?_
  have hcc : c ≠ c' := fun e => hctx (e ▸ rfl)
  cases h with
  | @spawn s s' reg ar _ _ _ hs =>
    obtain ⟨-, hR⟩ := hs
    cases hR with
    | ok hp =>
      by_cases hcl : c < s.C.length
      · have hstk : (spawnEff s c' ps ls).stk c = s.stk c := by
          unfold SC.stk
          rw [show (spawnEff s c' ps ls).C[c]? = s.C[c]? from List.getElem?_append_left hcl]
        exact absurd hd (Nat.not_lt.2 (enter_cap5_mono hF hw hcc hp.creatorLive hp.params
          hp.localsOK ⟨rfl, rfl⟩ (fun f hf => by rw [hstk]; exact hf) l))
      · have hnil : s.stk c = [] := by
          unfold SC.stk; rw [List.getElem?_eq_none (Nat.le_of_not_lt hcl)]
        have h0 := cap5_nil (reg := reg) (l := l) hnil
        rw [show cap5 (s, reg, ar).1 (s, reg, ar).2.1 c l = none from h0] at hd
        exact absurd hd (Nat.not_lt_zero _)

/-- L1 (`cap5_drop_own`, WC5 C45) for `issue` (Spec 1 §77, Part XIV: `split` then `store`, both by
the actor; WC4 C2): each phase lowers no `cap5` of another context, the invariants holding after
the `split` (T2, `opStepC_preservesC`). Under `DDSound` (Spec 1 §80), from a state reached by an
`EncapsulatedTrace5` from an initial state (Spec 1 §47). -/
theorem cap5_drop_own_issue {k : K} {L : MutexLayout} {statics : Statics} {lbls : List Label}
    {st st' : SC × SyncReg × ArenaReg} {c' i dst : Nat} {region : List Nat} (hdd : DDSound k)
    (hst : StaticsOK statics)
    (htr : EncapsulatedTrace5 k L (SC.ofS3 (S3.init statics), [], []) lbls st)
    (h : LStep k L (.issue c' i region dst) st st') (c l : Nat)
    (hd : capRank (cap5 st'.1 st'.2.1 c l) < capRank (cap5 st.1 st.2.1 c l)) :
    (Label.issue c' i region dst).ctx = c := by
  have hk := trace5_kInvCA hdd hst htr
  refine Decidable.byContradiction fun hctx => ?_
  have hcc : c ≠ c' := fun e => hctx (e ▸ rfl)
  cases h with
  | @issue s reg ar _ _ _ _ st₁ hi =>
    cases hi with
    | @ok E s₁ s₂ _ _ _ h₁ h₂ =>
      obtain ⟨hF, hw, hI⟩ := hk.parts
      have hk₁ := opStepC_preservesC hdd hk (by intro h; cases h) h₁
      obtain ⟨hF₁, hw₁, -⟩ := hk₁.parts
      obtain ⟨hlive, o, hR, ho⟩ := h₁
      cases hR with
      | reject => cases ho
      | ok hp =>
        cases ho
        obtain ⟨hlive₁, hR₂⟩ := h₂
        cases hR₂ with
        | ok hp₂ =>
          exact absurd hd (Nat.not_lt.2 (Nat.le_trans (split_cap5_mono hF hI hw hcc hlive hp l)
            (store_cap5_mono hF₁ hw₁ hcc hlive₁ hp₂ l)))

/-- L1 (`cap5_drop_own`, WC5 C45) for `reset` (Spec 1 §78, Part XIV: `derive` of `internal` then
`release`, on the view of the actor; WC4 C2): each phase lowers no `cap5` of another context, the
invariants holding after the `derive` (T2). Under `DDSound` (Spec 1 §80), from a state reached by
an `EncapsulatedTrace5` from an initial state (Spec 1 §47). -/
theorem cap5_drop_own_reset {k : K} {L : MutexLayout} {statics : Statics} {lbls : List Label}
    {st st' : SC × SyncReg × ArenaReg} {c' i : Nat} (hdd : DDSound k) (hst : StaticsOK statics)
    (htr : EncapsulatedTrace5 k L (SC.ofS3 (S3.init statics), [], []) lbls st)
    (h : LStep k L (.reset c' i) st st') (c l : Nat)
    (hd : capRank (cap5 st'.1 st'.2.1 c l) < capRank (cap5 st.1 st.2.1 c l)) :
    (Label.reset c' i).ctx = c := by
  have hk := trace5_kInvCA hdd hst htr
  refine Decidable.byContradiction fun hctx => ?_
  have hcc : c ≠ c' := fun e => hctx (e ▸ rfl)
  cases h with
  | @reset s reg ar _ _ st₁ hr =>
    obtain ⟨hlive, o₃, hD, ho⟩ := hr
    cases hD with
    | @ok E s₁ s₂ _ hd₁ hr₂ _ =>
      cases ho
      obtain ⟨hF, hw, hI⟩ := hk.parts
      cases hd₁ with
      | ok hp₁ =>
        have hmid : opStepC k (.derive E.internal (footprint (s.view c').P E.storage) .modify) c' s
            (.ok (s.set (deriveEff (s.view c') E.internal (footprint (s.view c').P E.storage)
              .modify))) := ⟨hlive, _, .ok hp₁, rfl⟩
        have hk₁ := opStepC_preservesC hdd hk (by intro h; cases h) hmid
        obtain ⟨hF₁, hw₁, hI₁⟩ := hk₁.parts
        have hv : (s.set (deriveEff (s.view c') E.internal (footprint (s.view c').P E.storage)
            .modify)).view c' =
            deriveEff (s.view c') E.internal (footprint (s.view c').P E.storage) .modify :=
          SC.view_set rfl
        cases hr₂ with
        | ok hp₂ =>
          have h2 := release_cap5_mono (reg := reg) (reg' := reg) hF₁ hI₁ hw₁ hcc hlive
            (by rw [hv]; exact hp₂) (fun e he => ⟨e, he, rfl⟩) l
          rw [hv] at h2
          exact absurd hd (Nat.not_lt.2 (Nat.le_trans (derive_cap5_mono hF hI hw hcc hlive hp₁ l)
            h2))
    | _ => cases ho

/-! ## `exitFrame` and `terminate` (Spec 1 §73; WC4 C6, C7) -/

/-- After the exit, the origin chain of an authority keeps only former ancestors (Spec 1 §73 `ok`
effect, third item: reanchoring to the first surviving ancestor). -/
theorem exit_ancs_sub {t : S3}
    (ho : ∀ (b : Nat) (y : Authority) (a : Nat), t.A[b]? = some y → y.origin = some a → a < b) :
    ∀ n x, x < n → ∀ w ∈ (exitEff t).ancs x, w ∈ t.ancs x
  | 0, _, h, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, x, hx, w, hw => by
    have hlt : ∀ i o, t.org i = some o → o < i := fun i o h => by
      unfold S3.org at h
      cases hy : t.A[i]? with
      | none => rw [hy] at h; cases h
      | some y => rw [hy] at h; exact ho i y o hy h
    cases hy : t.A[x]? with
    | none =>
      have : (exitEff t).org x = none := by simp [S3.org, Frames.exit_A_get, hy]
      rw [S3.ancs, chain_none this] at hw; simp at hw
    | some y =>
      have e' : (exitEff t).org x = (exitG t t.F.tail x y).origin := by
        simp [S3.org, Frames.exit_A_get, hy]
      rcases Frames.exitG_origin (s := t) (F₀ := t.F.tail) (a := x) (y := y) with e | ⟨-, -, e⟩
      · rw [e] at e'
        cases hoy : y.origin with
        | none => rw [hoy] at e'; rw [S3.ancs, chain_none e'] at hw; simp at hw
        | some o =>
          rw [hoy] at e'
          have hox := ho x y o hy hoy
          have hob : t.org x = some o := by simp [S3.org, hy, hoy]
          rw [S3.ancs, chain_cons e' hox] at hw
          rw [S3.ancs, chain_cons hob hox]
          rcases List.mem_cons.1 hw with rfl | hw
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (exit_ancs_sub ho n o (by omega) w hw)
      · rw [e] at e'
        cases hz : firstSurv t t.F.tail (t.ancs x) with
        | none => rw [hz] at e'; rw [S3.ancs, chain_none e'] at hw; simp at hw
        | some z =>
          rw [hz] at e'
          have hzx : z ∈ t.ancs x := (Frames.firstSurv_some hz).1
          have hzlt := chain_lt hzx
          rw [S3.ancs, chain_cons e' hzlt] at hw
          rcases List.mem_cons.1 hw with rfl | hw
          · exact hzx
          · exact chain_trans hlt (x + 1) x (Nat.lt_succ_self x) z hzx w
              (exit_ancs_sub ho n z (by omega) w hw)

/-- A live frame other than the top frame of `c` is in the tail of the stack of the view of `c`
(WC4 C2). -/
theorem mem_view_tail {s : SC} {c y : Nat} (hne : s.stk c ≠ []) (hy : y ∈ s.frames)
    (hyt : y ≠ (s.stk c).headD 0) : y ∈ (s.view c).F.tail := by
  obtain ⟨f, r, hfr⟩ := List.exists_cons_of_ne_nil hne
  show y ∈ (s.stk c ++ s.frames.filter fun f => decide (f ∉ s.stk c)).tail
  rw [hfr] at hyt ⊢
  simp only [List.headD_cons] at hyt
  simp only [List.cons_append, List.tail_cons, List.mem_append, List.mem_filter,
    decide_eq_true_eq]
  by_cases hin : y ∈ f :: r
  · rcases List.mem_cons.1 hin with rfl | h
    · exact absurd rfl hyt
    · exact .inl h
  · exact .inr ⟨hy, hin⟩

/-- The top frame of `c` after a pop is the head of its stack (WC4 C6). -/
theorem ReparentAux.Pop.f_eq {s s' : SC} {c f p : Nat} (h : ReparentAux.Pop s s' c f p) :
    f = (s.stk c).headD 0 := by
  have := h.head
  cases e : s.stk c with
  | nil => rw [e] at this; cases this
  | cons a l => rw [e] at this; cases this; rfl

/-- Every useful authority attributable to another context survives the exit of the top frame of
`c'` (Spec 1 §73, `Survives`): frame-held ones are held by a frame of their own context, and
place-held ones by a place that stays usable, by `NoDangling` after the step (Spec 1 §54, §57;
T2). -/
theorem exit_survives {s s' : SC} {reg : SyncReg} (hF : FramesC s) (hw : WF3 s.flat)
    {c c' f p : Nat} (hcc : c ≠ c') (hne : s.stk c' ≠ []) (hpop : ReparentAux.Pop s s' c' f p)
    (hA' : s'.A = (exitEff (s.view c')).A) (hP' : s'.P = s.P) (hd' : s'.dead = s.dead)
    (hND : NoDangling s'.flat) {u : Nat} {m : Mode} (h : Attr5 s reg c u m) (hu : Useful s u m) :
    Survives (s.view c') (s.view c').F.tail u := by
  have hP := parents_lt hw
  have hf := hpop.f_eq
  have hfc' : f ∈ s.stk c' := by rw [hpop.stk_c]; exact List.mem_cons_self ..
  induction h with
  | @base a m y f₀ hg hy ha hm hfr hin =>
    show OptP ((s.view c').A[a]?) _ False
    rw [show (s.view c').A[a]? = some y from hy]
    refine ⟨ha, ?_⟩
    rw [hfr]
    refine mem_view_tail hne (SC.mem_frames_of hin) fun he => hcc ?_
    exact ReparentAux.stk_unique hF.nodup hin (he ▸ hf ▸ hfc')
  | @held a q b m y hg hy ha hm hp hb hc ih =>
    have hup : s.flat.Usable q := by
      have := hw.holders a _ hy ha; rw [hp] at this; exact this
    obtain ⟨l₀, hl₀⟩ := footprint_ne hP _ q (Nat.le_refl _) hup.lt
    have hsb := ih ⟨l₀, hc l₀ hl₀⟩
    obtain ⟨zb, hzb, -, hzl, -⟩ := eff_present (allows_present (hc l₀ hl₀))
    have hu' : s'.flat.Usable q := by
      refine Decidable.byContradiction fun hnu => ?_
      have hb' : s'.flat.A[b]? = some (exitG (s.view c') (s.view c').F.tail b zb) := by
        show s'.A[b]? = _
        rw [hA', Frames.exit_A_get, show (s.view c').A[b]? = some zb from hzb]; rfl
      have hact := Frames.exitG_surv (s := s.view c') (show (s.view c').A[b]? = some zb from hzb)
        hsb
      have := hND b _ hb' hact q hnu l₀ (by show l₀ ∈ footprint s'.P q; rw [hP']; exact hl₀)
      rw [(Frames.exitG_same _ _ _ _).2.1] at this
      exact this hzl
    have hut : ({ s.view c' with F := (s.view c').F.tail } : S3).Usable q := by
      refine S3.Usable.mono (s := { s.view c' with F := (s.view c').F.tail }) (s' := s'.flat)
        (show s'.flat.P = ({ s.view c' with F := (s.view c').F.tail } : S3).P from hP')
        (fun f' hf' => ?_)
        (fun q hq => by rwa [show s'.flat.dead = s.dead from hd'] at hq) hu'
      obtain ⟨hf1, hf2⟩ := (hpop.mem_frames hF.nodup).1 hf'
      exact mem_view_tail hne hf1 (hf ▸ hf2)
    show OptP ((s.view c').A[a]?) _ False
    rw [show (s.view c').A[a]? = some y from hy]
    refine ⟨ha, ?_⟩
    rw [hp]; exact hut

/-- The exit of the top frame of `c'` (Spec 1 §73; WC4 C6, C7), read from another context `c`:
`cap5` of `c` does not decrease. The useful authorities of `c` survive (`exit_survives`);
reanchoring only shortens origin chains (`exit_ancs_sub`), so effective modes can only rise. -/
theorem exit_cap5_mono {s s' : SC} {reg : SyncReg} (hF : FramesC s) (hw : WF3 s.flat)
    {c c' f p : Nat} (hcc : c ≠ c') (hne : s.stk c' ≠ []) (hpop : ReparentAux.Pop s s' c' f p)
    (hA' : s'.A = (exitEff (s.view c')).A) (hP' : s'.P = s.P) (hd' : s'.dead = s.dead)
    (hND : NoDangling s'.flat) (l : Nat) :
    capRank (cap5 s reg c l) ≤ capRank (cap5 s' reg c l) := by
  have ho : ∀ (b : Nat) (y : Authority) (a : Nat), (s.view c').A[b]? = some y →
      y.origin = some a → a < b :=
    fun b y a hy hoy => hw.origins b y a hy hoy
  have hget : ∀ u y, s.A[u]? = some y →
      s'.A[u]? = some (exitG (s.view c') (s.view c').F.tail u y) := fun u y hy => by
    rw [hA', Frames.exit_A_get, show (s.view c').A[u]? = some y from hy]; rfl
  have hsurv : ∀ u m y, Attr5 s reg c u m → Useful s u m → s.A[u]? = some y →
      (exitG (s.view c') (s.view c').F.tail u y).active = true := fun u m y hu hus hy =>
    Frames.exitG_surv (s := s.view c') hy (exit_survives hF hw hcc hne hpop hA' hP' hd' hND hu hus)
  have hyact : ∀ u m y, Attr5 s reg c u m → s.A[u]? = some y → y.active = true :=
    fun u m y hu hy => by
      cases hu with
      | base _ hy' ha => rw [hy] at hy'; cases hy'; exact ha
      | held _ hy' ha => rw [hy] at hy'; cases hy'; exact ha
  refine cap5_transport_u (s' := s') (reg' := reg) hw
    (fun f' hf' => by rw [hpop.stk c]; simp only [hcc, ↓reduceIte]; exact hf')
    (fun q _ l hl => by rwa [hP'] at hl)
    (fun u m y hu hus hy => ⟨_, hget u y hy, by rw [hsurv u m y hu hus hy, hyact u m y hu hy],
      (Frames.exitG_same _ _ _ _).1, (Frames.exitG_same _ _ _ _).2.2⟩)
    (fun u m hu _ e he hl => ?_) (fun u m l hu hal => ?_) l
  · obtain ⟨y', hy', hya⟩ := hl
    have hy'' : (exitEff (s.view c')).A[e.guarded]? = some y' := by rw [← hA']; exact hy'
    obtain ⟨y₀, hy₀, rfl⟩ := Frames.exit_get hy''
    exact hu.notGuarded e he ⟨y₀, hy₀, Frames.exitG_active' (s := s.view c') hy₀ hya⟩
  · rw [effective_of_A (t := s'.flat) (t' := exitEff (s.view c')) hA']
    rw [← effective_of_A (t := s.view c') (t' := s.flat) rfl] at hal
    refine eff_keep_sub (fun z hz => ⟨_, by rw [← hA']; exact hget u z hz, ?_,
      (Frames.exitG_same _ _ _ _).1, (Frames.exitG_same _ _ _ _).2.1⟩)
      (fun j y hy hya hyl hj => ?_) hal
    · have hus : Useful s u m :=
        ⟨l, by rw [← effective_of_A (t := s.view c') (t' := s.flat) rfl]; exact hal⟩
      rw [hsurv u m z hu hus hz, hyact u m z hu hz]
    · obtain ⟨y₀, hy₀, rfl⟩ := Frames.exit_get hy
      refine ⟨y₀, hy₀, Frames.exitG_active' (s := s.view c') hy₀ hya, ?_, ?_,
        (Frames.exitG_same _ _ _ _).1.symm⟩
      · rw [(Frames.exitG_same _ _ _ _).2.1] at hyl; exact hyl
      · exact exit_ancs_sub ho (j + 1) j (Nat.lt_succ_self j) u hj

/-- L1 (`cap5_drop_own`, WC5 C45) for `exitFrame` (Spec 1 §73; WC4 C6). Under `DDSound` (Spec 1
§80), from a state reached by an `EncapsulatedTrace5` from an initial state (Spec 1 §47). -/
theorem cap5_drop_own_exit {k : K} {L : MutexLayout} {statics : Statics} {lbls : List Label}
    {st st' : SC × SyncReg × ArenaReg} {c' : Nat} (hdd : DDSound k) (hst : StaticsOK statics)
    (htr : EncapsulatedTrace5 k L (SC.ofS3 (S3.init statics), [], []) lbls st)
    (h : LStep k L (.kernel c' .exit) st st') (c l : Nat)
    (hd : capRank (cap5 st'.1 st'.2.1 c l) < capRank (cap5 st.1 st.2.1 c l)) :
    (Label.kernel c' .exit).ctx = c := by
  have hk := trace5_kInvCA hdd hst htr
  have hk' := lstep_kInvCA hdd h hk
  refine Decidable.byContradiction fun hctx => ?_
  have hcc : c ≠ c' := fun e => hctx (e ▸ rfl)
  cases h with
  | @kernel s s' reg ar _ _ hs =>
    obtain ⟨hF, hw, -⟩ := hk.parts
    obtain ⟨hlive, hR⟩ := hs
    cases hR with
    | ok hp =>
      exact absurd hd (Nat.not_lt.2 (exit_cap5_mono hF hw hcc (hF.nonempty c' hlive)
        (exitEffC_pop hF.nodup hp.hasCaller) rfl rfl rfl hk'.1.2.1.2.2 l))

/-- L1 (`cap5_drop_own`, WC5 C45) for `terminate` (WC4 C7): the initial frame of the actor is
popped as by `exitFrame` (Spec 1 §73). Under `DDSound` (Spec 1 §80), from a state reached by an
`EncapsulatedTrace5` from an initial state (Spec 1 §47). -/
theorem cap5_drop_own_terminate {k : K} {L : MutexLayout} {statics : Statics} {lbls : List Label}
    {st st' : SC × SyncReg × ArenaReg} {c' : Nat} (hdd : DDSound k) (hst : StaticsOK statics)
    (htr : EncapsulatedTrace5 k L (SC.ofS3 (S3.init statics), [], []) lbls st)
    (h : LStep k L (.terminate c') st st') (c l : Nat)
    (hd : capRank (cap5 st'.1 st'.2.1 c l) < capRank (cap5 st.1 st.2.1 c l)) :
    (Label.terminate c').ctx = c := by
  have hk := trace5_kInvCA hdd hst htr
  have hk' := lstep_kInvCA hdd h hk
  refine Decidable.byContradiction fun hctx => ?_
  have hcc : c ≠ c' := fun e => hctx (e ▸ rfl)
  cases h with
  | @terminate s s' reg ar _ ht =>
    obtain ⟨hF, hw, -⟩ := hk.parts
    obtain ⟨hlive, hR⟩ := ht
    cases hR with
    | ok hp =>
      have hpar : s.ctxParent c' ≠ none := fun he => by
        have := hp.hasParent; rw [he] at this; exact this
      exact absurd hd (Nat.not_lt.2 (exit_cap5_mono hF hw hcc (hF.nonempty c' hlive)
        (termEffC_pop hF.nodup hp.initialOnly hpar) rfl rfl rfl hk'.1.2.1.2.2 l))

/-! ## Steps that only release authorities: `endUse`, `free` (Spec 1 §69, §70) -/

/-- A live frame is in the stack of the view of any context (WC4 C2). -/
theorem mem_view_F {s : SC} {c y : Nat} (hy : y ∈ s.frames) : y ∈ (s.view c).F := by
  show y ∈ s.stk c ++ s.frames.filter fun f => decide (f ∉ s.stk c)
  by_cases h : y ∈ s.stk c
  · exact List.mem_append_left _ h
  · exact List.mem_append_right _ (List.mem_filter.2 ⟨hy, decide_eq_true h⟩)

/-- An attributable authority is active (WC5 C43). -/
theorem Attr5.active {s : SC} {reg : SyncReg} {c u : Nat} {m : Mode} {y : Authority}
    (h : Attr5 s reg c u m) (hy : s.A[u]? = some y) : y.active = true := by
  cases h with
  | base _ hy' ha => rw [hy] at hy'; cases hy'; exact ha
  | held _ hy' ha => rw [hy] at hy'; cases hy'; exact ha

/-- A step that only releases authorities (`OnlyReleases`, Spec 1 §69, §70) and keeps the places
and the frames of `c` does not lower `cap5` of `c` when every useful authority attributable to
`c` stays active: effective modes can only rise. -/
theorem releases_cap5_mono {s s' : SC} {reg : SyncReg} (hw : WF3 s.flat) {c : Nat}
    (hr : EndFree.OnlyReleases s.flat s'.flat) (hstk : ∀ f ∈ s.stk c, f ∈ s'.stk c)
    (hP : s'.P = s.P)
    (hkeep : ∀ u m, Attr5 s reg c u m → Useful s u m → s'.flat.Active u) (l : Nat) :
    capRank (cap5 s reg c l) ≤ capRank (cap5 s' reg c l) := by
  have hact : ∀ u m z, Attr5 s reg c u m → Useful s u m → s'.A[u]? = some z → z.active = true :=
    fun u m z hu hus hz => by
      obtain ⟨z', hz', hza⟩ := hkeep u m hu hus
      have : s'.A[u]? = some z' := hz'
      rw [hz] at this; cases this; exact hza
  refine cap5_transport_u (s' := s') (reg' := reg) hw hstk (fun q _ l hl => by rwa [hP] at hl)
    (fun u m y hu hus hy => ?_) (fun u m hu _ e he hl => ?_) (fun u m l hu hal => ?_) l
  · obtain ⟨z, hz, hm, -, -, hh⟩ := hr.get' (show s.flat.A[u]? = some y from hy)
    exact ⟨z, hz, by rw [hact u m z hu hus hz, hu.active hy], hm, hh⟩
  · obtain ⟨y', hy', hya⟩ := hl
    obtain ⟨y, hy, -, -, -, -, ha⟩ := hr.2 e.guarded y' hy'
    exact hu.notGuarded e he ⟨y, hy, ha hya⟩
  · refine eff_keep_sub (t := s.flat) (t' := s'.flat) (fun z hz => ?_) (fun j y hy hya hyl hj => ?_)
      hal
    · obtain ⟨z', hz', hm, -, hf, -⟩ := hr.get' hz
      exact ⟨z', hz', by rw [hact u m z' hu ⟨l, hal⟩ hz', hu.active hz], hm, hf⟩
    · obtain ⟨y₀, hy₀, hm, -, hf, -, ha⟩ := hr.2 j y hy
      exact ⟨y₀, hy₀, ha hya, hf ▸ hyl, by rwa [hr.ancs] at hj, hm.symm⟩

/-- `endUse` by context `c'` (Spec 1 §69) keeps active every useful authority attributable to
another context: it is held neither within the place, over which `c'` exercises `Modify`
(§69.1; `not_attr_place`), nor by a place that dies, by `NoDangling` after the step (Spec 1 §54,
§57; T2). -/
theorem endUse_keeps {k : K} {s s' : SC} {reg : SyncReg} (hF : FramesC s) (hI : I1 s.flat)
    (hw : WF3 s.flat) {c c' p : Nat} (hcc : c ≠ c') (hne : s.stk c' ≠ [])
    (hp : EndUsePre k (s.view c') p) (hs' : s' = s.set (endUseEff (s.view c') p))
    (hND : NoDangling s'.flat) {u : Nat} {m : Mode} (h : Attr5 s reg c u m) (hu : Useful s u m) :
    ∀ y, s.A[u]? = some y → s'.A[u]? = some y := by
  have hP := parents_lt hw
  obtain ⟨g, -, hgx, hge⟩ := hp.right
  have hg : Attr s c' g .modify := attr_of_exercisable hne hgx
  have hge' : ∀ l ∈ footprint s.P p, Allows (effective s.flat g l) .modify :=
    fun l hl => by rw [← effective_of_A (t := s.view c') (t' := s.flat) rfl]; exact hge l hl
  have hget : ∀ (a : Nat) (y : Authority), s.A[a]? = some y → ¬ heldIn s.P p y.holder →
      HolderLive (endUseS (s.view c') p) y.holder → s'.A[a]? = some y := fun a y hy hnh hl => by
    subst hs'
    show (cleanup (endUseS (s.view c') p)).A[a]? = some y
    rw [EndFree.cleanup_get, EndFree.endUseS_get,
      show (s.view c').A[a]? = some y from hy]
    simp only [Option.map_some, show ¬ heldIn (s.view c').P p y.holder from hnh, ↓reduceIte]
    simp only [show HolderLive (endUseS (s.view c') p) y.holder from hl, ↓reduceIte]
  induction h with
  | @base a m y f₀ hg' hy ha hm hfr hin =>
    intro y' hy'
    rw [hy] at hy'; cases hy'
    refine hget a y hy (by rw [hfr]; exact id) ?_
    rw [hfr]
    exact mem_view_F (SC.mem_frames_of hin)
  | @held a q b m y hg' hy ha hm hp' hb hc ih =>
    intro y' hy'
    rw [hy] at hy'; cases hy'
    have hup : s.flat.Usable q := by
      have := hw.holders a _ hy ha; rw [hp'] at this; exact this
    obtain ⟨l₀, hl₀⟩ := footprint_ne hP _ q (Nat.le_refl _) hup.lt
    obtain ⟨zb, hzb, -, hzl, -⟩ := eff_present (allows_present (hc l₀ hl₀))
    have hbk := ih ⟨l₀, hc l₀ hl₀⟩ zb hzb
    refine hget a y hy (fun hh => ?_) ?_
    · rw [hp'] at hh
      exact not_attr_place hF.nodup hI hw hcc hy hp' hg
        (fun l hl => hge' l (footprint_sub hw hh hl)) (.held hy ha hm hp' hb.attr hc)
    · rw [hp']
      refine Decidable.byContradiction fun hnu => ?_
      have hnu' : ¬ s'.flat.Usable q := fun hu' => hnu (by
        refine S3.Usable.mono (s := endUseS (s.view c') p) (s' := s'.flat)
          (by rw [hs']; rfl) (fun f hf => ?_) (fun q hq => by rw [hs'] at hq; exact hq) hu'
        exact mem_view_F (s := s) (c := c') (by rw [hs'] at hf; exact hf))
      have hza : zb.active = true := hb.active hzb
      exact hND b zb hbk hza q hnu' l₀ (by rw [hs']; exact hl₀) hzl

/-- L1 (`cap5_drop_own`, WC5 C45) for `endUse` (Spec 1 §69). Under `DDSound` (Spec 1 §80), from a
state reached by an `EncapsulatedTrace5` from an initial state (Spec 1 §47). -/
theorem cap5_drop_own_endUse {k : K} {L : MutexLayout} {statics : Statics} {lbls : List Label}
    {st st' : SC × SyncReg × ArenaReg} {c' p : Nat} (hdd : DDSound k) (hst : StaticsOK statics)
    (htr : EncapsulatedTrace5 k L (SC.ofS3 (S3.init statics), [], []) lbls st)
    (h : LStep k L (.kernel c' (.endUse p)) st st') (c l : Nat)
    (hd : capRank (cap5 st'.1 st'.2.1 c l) < capRank (cap5 st.1 st.2.1 c l)) :
    (Label.kernel c' (.endUse p)).ctx = c := by
  have hk := trace5_kInvCA hdd hst htr
  have hk' := lstep_kInvCA hdd h hk
  refine Decidable.byContradiction fun hctx => ?_
  have hcc : c ≠ c' := fun e => hctx (e ▸ rfl)
  cases h with
  | @kernel s s' reg ar _ _ hs =>
    obtain ⟨hF, hw, hI⟩ := hk.parts
    obtain ⟨hlive, o, hR, ho⟩ := hs
    cases hR with
    | reject => cases ho
    | ok hp =>
      cases ho
      have hr : EndFree.OnlyReleases s.flat (s.set (endUseEff (s.view c') p)).flat :=
        (EndFree.endUseS_releases (s.view c') p).trans (EndFree.cleanup_releases _)
      refine absurd hd (Nat.not_lt.2 (releases_cap5_mono (s' := s.set (endUseEff (s.view c') p))
        (reg := reg) hw hr (fun f hf => hf) rfl
        (fun u m hu hus => ?_) l))
      obtain ⟨y, hy⟩ : ∃ y, s.A[u]? = some y := ⟨_, List.getElem?_eq_getElem hu.lt⟩
      exact ⟨y, endUse_keeps hF hI hw hcc (hF.nonempty c' hlive) hp rfl hk'.1.2.1.2.2 hu hus y hy,
        hu.active hy⟩

/-- Transitive ownership through `p` goes up the structure (Spec 1 §40, §49.2: parts share their
parent's owner). -/
theorem ownedIn_up {t : S3} (hw : WF3 t) {p : Nat} :
    ∀ n l, l < n → ∀ r, partOf t.P l r → OwnedIn t.P p l → OwnedIn t.P p r
  | 0, _, h, _, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, l, hl, r, ⟨hlP, hlr⟩, ho => by
    rcases hlr with rfl | hc
    · exact ho
    · cases hq : t.P[l]? with
      | none => simp [List.getElem?_eq_getElem hlP] at hq
      | some pl =>
        cases hpo : pl.parent with
        | none =>
          have : parentOf t.P l = none := by simp [parentOf, hq, hpo]
          rw [chain_none this] at hc; simp at hc
        | some o =>
          obtain ⟨pr, hpr, hol, -, -⟩ := hw.places l pl o hq hpo
          have hpar : parentOf t.P l = some o := by simp [parentOf, hq, hpo]
          rw [chain_cons hpar hol] at hc
          have hoo : OwnedIn t.P p o := (EndFree.ownedIn_parent hw hq hpo).2 ho
          rcases List.mem_cons.1 hc with rfl | hc
          · exact hoo
          · exact ownedIn_up hw n o (by omega) r ⟨lt_of_getElem? hpr, .inr hc⟩ hoo

/-- An authority on the origin chain above an authority `g` that has effective `Modify` on every
leaf of a root place `p` has an effective mode on no leaf (Spec 1 §43, §49.6): its leaves are
leaves of `p`, which `g` covers in `Modify`. -/
theorem above_root_ground {t : S3} (hw : WF3 t) {p g u l : Nat} {m : Mode} (hp : RootPlace t.P p)
    (hg : ∀ l ∈ footprint t.P p, Allows (effective t g l) .modify) (hu : u ∈ t.ancs g)
    (h : Allows (effective t u l) m) : False := by
  have hlt : ∀ i o, t.org i = some o → o < i := fun i o h => by
    simp only [S3.org] at h
    cases hi : t.A[i]? with
    | none => rw [hi] at h; cases h
    | some y => rw [hi] at h; exact hw.origins i y o hi h
  obtain ⟨z, hz, -, hzl, -⟩ := eff_present (allows_present h)
  obtain ⟨-, hleaf⟩ := hw.footprints u z hz l hzl
  obtain ⟨xu, wu, ru, hxu, hwu, wuo, hru, hlru, hwuf⟩ := hw.rootChain u z l hz hzl hleaf
  obtain ⟨lp, hlp⟩ := exists_mem_footprint hw (t.P.length - p + 1) p (by omega) hp.1
  obtain ⟨yg, hyg, -, hlpg, -, -⟩ := eff_modify (allows_modify (hg lp hlp))
  have hlpleaf := (mem_footprint.1 hlp).2.1
  obtain ⟨xg, wg, rg, hxg, hwg, wgo, hrg, hlprg, hwgf⟩ := hw.rootChain g yg lp hyg hlpg hlpleaf
  have hxu' : xu = g ∨ xu ∈ t.ancs g := by
    rcases hxu with rfl | hxu
    · exact .inr hu
    · exact .inr (chain_trans hlt (g + 1) g (Nat.lt_succ_self g) u hu xu hxu)
  have e : xu = xg := EndFree.chain_root_unique hlt (g + 1) g (Nat.lt_succ_self g) xu xg hxu' hxg
    (by simp [S3.org, hwu, wuo]) (by simp [S3.org, hwg, wgo])
  subst e
  rw [hwu] at hwg; cases hwg
  obtain rfl : rg = p := rootOf_unique hrg hp hlprg (mem_footprint.1 hlp).2.2
  have hlp' : l ∈ footprint t.P rg :=
    (hwgf l).1 ((hwuf l).2 (mem_footprint.2 ⟨(mem_footprint.1 (footprint_sub hw hlru
      (mem_footprint.2 ⟨by have := (mem_footprint.1 hlp).1; exact (hw.footprints u z hz l hzl).1,
        hleaf, ⟨(hw.footprints u z hz l hzl).1, .inl rfl⟩⟩))).1, hleaf, hlru⟩))
  obtain ⟨yg', hyg', hyga, hlg, hgm, -⟩ := eff_modify (allows_modify (hg l hlp'))
  exact no_eff_below_modify hyg' hyga hgm hlg hu h

/-- `free` by context `c'` (Spec 1 §70) keeps every useful authority attributable to another
context: it is held neither within the released place nor by a place that dies (as for `endUse`),
and it covers no leaf of the released unit: it is not the grounding authority of `c'`
(`attr_excl`), not above it (`above_root_ground`), and otherwise §70.3 (`FreeAccessOK`) or, for a
root authority, its holder (`rootHeldConv_active`) and `I1` exclude it. -/
theorem free_keeps {k : K} {s s' : SC} {reg : SyncReg} (hF : FramesC s) (hI : I1 s.flat)
    (hw : WF3 s.flat) (hND0 : NoDangling s.flat) {c c' p auth : Nat} (hcc : c ≠ c')
    (hne : s.stk c' ≠ []) (hp : FreePre k (s.view c') p auth)
    (hs' : s' = s.set (freeEff (s.view c') p)) (hND : NoDangling s'.flat) {u : Nat} {m : Mode}
    (h : Attr5 s reg c u m) (hu : Useful s u m) : ∀ y, s.A[u]? = some y → s'.A[u]? = some y := by
  have hP := parents_lt hw
  have hlt : ∀ i o, s.flat.org i = some o → o < i := fun i o h => by
    simp only [S3.org] at h
    cases hi : s.flat.A[i]? with
    | none => rw [hi] at h; cases h
    | some y => rw [hi] at h; exact hw.origins i y o hi h
  have hvA : ∀ a l, effective (s.view c') a l = effective s.flat a l :=
    fun a l => effective_of_A rfl a l
  have hroot : RootPlace s.P p := EndFree.rootPlace_of_ownedRoot hp.ownedRoot
  obtain ⟨g, -, ⟨-, hgx, hge⟩, hall⟩ := hp.access
  have hg : Attr s c' g .modify := attr_of_exercisable hne hgx
  have hge' : ∀ l ∈ footprint s.P p, Allows (effective s.flat g l) .modify :=
    fun l hl => by rw [← hvA]; exact hge l hl
  have hget : ∀ (a : Nat) (y : Authority), s.A[a]? = some y →
      ¬ ((∃ l ∈ y.footprint, FreedPlace s.P p l) ∨ heldIn s.P p y.holder) →
      HolderLive (freeS (s.view c') p) y.holder → s'.A[a]? = some y := fun a y hy hn hl => by
    subst hs'
    show (cleanup (freeS (s.view c') p)).A[a]? = some y
    rw [EndFree.cleanup_get, EndFree.freeS_get, show (s.view c').A[a]? = some y from hy]
    simp only [Option.map_some, show ¬ ((∃ l ∈ y.footprint, FreedPlace (s.view c').P p l) ∨
      heldIn (s.view c').P p y.holder) from hn, ↓reduceIte]
    simp only [show HolderLive (freeS (s.view c') p) y.holder from hl, ↓reduceIte]
  have hfreeDead : ∀ q, FreedPlace s.P p q → ¬ (freeS (s.view c') p).Usable q := fun q hq hu => by
    have := EndFree.dead_false hu
    simp [freeS, show FreedPlace (s.view c').P p q from hq] at this
  -- the covering condition, given the two holder conditions
  have hcov : ∀ (a : Nat) (y : Authority) (m : Mode), Attr5 s reg c a m → Useful s a m →
      s.A[a]? = some y → ¬ heldIn s.P p y.holder → HolderLive (freeS (s.view c') p) y.holder →
      ¬ ∃ l ∈ y.footprint, FreedPlace s.P p l := fun a y m ha has hy hnh hl ⟨l₀, hl₀, hfr⟩ => by
    obtain ⟨l₁, hl₁⟩ := has
    have hya : y.active = true := ha.active hy
    by_cases hag : a = g
    · subst hag; exact attr_excl hF.nodup hI hw hcc hg ha.attr
    by_cases hanc : a ∈ s.flat.ancs g
    · exact above_root_ground hw hroot hge' hanc hl₁
    have hleaf := (hw.footprints a y hy l₀ hl₀)
    cases hyo : y.origin with
    | some o =>
      have hok := (hall a (List.mem_range.2 (lt_of_getElem? hy))).resolve_left (by
        rintro (h | h)
        · exact hag h
        · exact hanc h)
      unfold FreeAccessOK OptP at hok
      rw [show (s.view c').A[a]? = some y from hy] at hok
      have hfl : FreedLeaf (s.view c') p l₀ := by
        rcases hfr with hpart | hown
        · exact .inl (mem_footprint.2 ⟨hleaf.1, hleaf.2, hpart⟩)
        · refine .inr ⟨hleaf.2, ?_, hfreeDead l₀ (.inr hown)⟩
          have hus : s.flat.Usable l₀ := Decidable.byContradiction fun hnu =>
            hND0 a y hy hya l₀ hnu l₀ (mem_footprint.2 ⟨hleaf.1, hleaf.2, hleaf.1, .inl rfl⟩) hl₀
          exact S3.Usable.mono (s := s.view c') (s' := s.flat) rfl
            (fun f hf => mem_view_F hf) (fun q h => h) hus
      rcases hok hya (by rw [hyo]; simp) ⟨l₀, hl₀, hfl⟩ with h | h
      · exact hnh h
      · exact h hl
    | none =>
      obtain ⟨r, hr, hl₀r⟩ := exists_rootPlace hw (l₀ + 1) l₀ (Nat.lt_succ_self _) hleaf.1
      obtain ⟨pr, hpr, hho⟩ := rootHeldConv_active hw hI hND0 a y l₀ r hy hya hyo hl₀ hr hl₀r
      rcases hfr with hpart | hown
      · obtain rfl : r = p := rootOf_unique hr hroot hl₀r hpart
        obtain ⟨xa, wa, ra, hxa, hwa, wao, hra, hl₀ra, hwaf⟩ :=
          hw.rootChain a y l₀ hy hl₀ hleaf.2
        have horg : s.flat.org a = none := by
          show (s.A[a]?).bind (·.origin) = none
          rw [hy]; exact hyo
        have hxa' : xa = a := by
          rcases hxa with h | h
          · exact h
          · rw [S3.ancs, chain_none horg] at h; simp at h
        rw [hxa'] at hwa
        have hwa' : wa = y := by
          have h2 : s.flat.A[a]? = some y := hy
          rw [h2] at hwa; cases hwa; rfl
        rw [hwa'] at hwaf
        obtain rfl : ra = r := rootOf_unique hra hroot hl₀ra hpart
        obtain ⟨lp, hlp⟩ := exists_mem_footprint hw (s.flat.P.length - ra + 1) ra (by omega) hroot.1
        obtain ⟨yg, hyg, hyga, hlpg, hgm, -⟩ := eff_modify (allows_modify (hge' lp hlp))
        have hga : g ∉ s.flat.ancs a := by rw [S3.ancs, chain_none horg]; simp
        have := (hI a g y yg lp hag hy hyg hya hyga ((hwaf lp).2 hlp) hlpg hanc hga).2
        rw [hgm] at this; cases this
      · have hor : OwnedIn s.P p r := ownedIn_up hw (l₀ + 1) l₀ (Nat.lt_succ_self _) r hl₀r hown
        have hpr' : s.P[r]? = some pr := hpr
        cases hor with
        | direct hq ho hpo =>
          rw [hpr'] at hq; cases hq
          exact hnh (by rw [hho, ho]; exact hpo)
        | step hq ho hown' =>
          rw [hpr'] at hq; cases hq
          rw [hho, ho] at hl
          exact hfreeDead _ (.inr hown') hl
  induction h with
  | @base a m y f₀ hg' hy ha hm hfr hin =>
    intro y' hy'
    rw [hy] at hy'; cases hy'
    have hab : Attr5 s reg c a m := .base hg' hy ha hm hfr hin
    have hnh : ¬ heldIn s.P p y.holder := by rw [hfr]; exact id
    have hl : HolderLive (freeS (s.view c') p) y.holder := by
      rw [hfr]; exact mem_view_F (SC.mem_frames_of hin)
    exact hget a y hy (fun h => h.elim (hcov a y m hab hu hy hnh hl) hnh) hl
  | @held a q b m y hg' hy ha hm hp' hb hc ih =>
    intro y' hy'
    rw [hy] at hy'; cases hy'
    have hab : Attr5 s reg c a m := .held hg' hy ha hm hp' hb hc
    have hup : s.flat.Usable q := by
      have := hw.holders a _ hy ha; rw [hp'] at this; exact this
    obtain ⟨l₀, hl₀⟩ := footprint_ne hP _ q (Nat.le_refl _) hup.lt
    obtain ⟨zb, hzb, -, hzl, -⟩ := eff_present (allows_present (hc l₀ hl₀))
    have hbk := ih ⟨l₀, hc l₀ hl₀⟩ zb hzb
    have hnh : ¬ heldIn s.P p y.holder := fun hh => by
      rw [hp'] at hh
      exact not_attr_place hF.nodup hI hw hcc hy hp' hg
        (fun l hl => hge' l (footprint_sub hw hh hl)) hab.attr
    have hl : HolderLive (freeS (s.view c') p) y.holder := by
      rw [hp']
      refine Decidable.byContradiction fun hnu => ?_
      have hnu' : ¬ s'.flat.Usable q := fun hu' => hnu (by
        refine S3.Usable.mono (s := freeS (s.view c') p) (s' := s'.flat)
          (by rw [hs']; rfl) (fun f hf => ?_) (fun q hq => by rw [hs'] at hq; exact hq) hu'
        exact mem_view_F (s := s) (c := c') (by rw [hs'] at hf; exact hf))
      exact hND b zb hbk (hb.active hzb) q hnu' l₀ (by rw [hs']; exact hl₀) hzl
    exact hget a y hy (fun h => h.elim (hcov a y m hab hu hy hnh hl) hnh) hl

/-- L1 (`cap5_drop_own`, WC5 C45) for `free` (Spec 1 §70). Under `DDSound` (Spec 1 §80), from a
state reached by an `EncapsulatedTrace5` from an initial state (Spec 1 §47). -/
theorem cap5_drop_own_free {k : K} {L : MutexLayout} {statics : Statics} {lbls : List Label}
    {st st' : SC × SyncReg × ArenaReg} {c' p auth : Nat} (hdd : DDSound k)
    (hst : StaticsOK statics)
    (htr : EncapsulatedTrace5 k L (SC.ofS3 (S3.init statics), [], []) lbls st)
    (h : LStep k L (.kernel c' (.free p auth)) st st') (c l : Nat)
    (hd : capRank (cap5 st'.1 st'.2.1 c l) < capRank (cap5 st.1 st.2.1 c l)) :
    (Label.kernel c' (.free p auth)).ctx = c := by
  have hk := trace5_kInvCA hdd hst htr
  have hk' := lstep_kInvCA hdd h hk
  refine Decidable.byContradiction fun hctx => ?_
  have hcc : c ≠ c' := fun e => hctx (e ▸ rfl)
  cases h with
  | @kernel s s' reg ar _ _ hs =>
    obtain ⟨hF, hw, hI⟩ := hk.parts
    obtain ⟨hlive, o, hR, ho⟩ := hs
    cases hR with
    | reject => cases ho
    | ok hp =>
      cases ho
      have hr : EndFree.OnlyReleases s.flat (s.set (freeEff (s.view c') p)).flat :=
        (EndFree.freeS_releases (s.view c') p).trans (EndFree.cleanup_releases _)
      refine absurd hd (Nat.not_lt.2 (releases_cap5_mono (s' := s.set (freeEff (s.view c') p))
        (reg := reg) hw hr (fun f hf => hf) rfl (fun u m hu hus => ?_) l))
      obtain ⟨y, hy⟩ : ∃ y, s.A[u]? = some y := ⟨_, List.getElem?_eq_getElem hu.lt⟩
      exact ⟨y, free_keeps hF hI hw hk.1.2.1.2.2 hcc (hF.nonempty c' hlive) hp rfl
        hk'.1.2.1.2.2 hu hus y hy, hu.active hy⟩

end Ern.Concurrency
