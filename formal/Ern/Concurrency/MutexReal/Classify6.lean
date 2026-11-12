import Ern.Concurrency.MutexReal.Amend
import Ern.Concurrency.MutexReal.Bridge
import Ern.MemoryModel.Arena

/-!
# The classification replayed under the proposed C22 item 4

Brief of milestone 4, slice 2, layer R, corrective pass, task 4
(`formal/reports/spec2-m4-mutexreal.md`, § Passe corrective):

* `classified6_sound`: under `Encap6`, the kinds `exclu` and `fin de vie` of the previous pass and
  the three former counter-examples (`store`, `alloc`, `issue`) do not have the controller of an
  entry live before and after the step in their enlarged footprint, and keep it. The first half is
  the restriction itself (proposed C22 item 4); the second is proved;
* `spawnVal_fixed_sound`: the statement left open by the previous pass, by-value `spawn` under
  hypothesis 3;
* `completeness6`, `completeness6_run`: completeness without restriction of kind, under
  hypothesis 3.
-/

set_option autoImplicit false

namespace Ern.Concurrency.MutexReal

open Ern.MemoryModel.Access Ern.Concurrency
open SyncPreserveAux SyncInitAux

/-! ## Exclusion by the restriction -/

/-- The kinds of the three counter-examples of the previous pass: `store`, `alloc`, `issue`. -/
def CexKind : Label → Prop
  | .kernel _ (.store _ _) | .kernel _ (.alloc _ _ _) | .issue _ _ _ _ => True
  | _ => False

/-- A step of a kind `exclu`, `fin de vie` or of a former counter-example is no protocol step and
no move admitted by C22 item 3. -/
theorem kind_not_proto {L : MutexLayout} {lbl : Label}
    (hkind : ExclKind lbl ∨ FinKind lbl ∨ CexKind lbl) :
    (∀ i, ctlOp i lbl = none) ∧ ∀ st, ¬ C223Move L st lbl := by
  cases lbl with
  | kernel c op =>
    cases op <;> simp_all [ExclKind, FinKind, CexKind, ctlOp, C223Move]
  | _ => simp_all [ExclKind, FinKind, CexKind, ctlOp, C223Move]

/-- Under the restriction of the controller, a step that is no protocol step of entry `i` and no
move admitted by C22 item 3, after which entry `i` is still live, does not have its controller in
its enlarged footprint (proposed C22 item 4). -/
theorem restr_not_touch {L : MutexLayout} {st st' : SC × SyncReg × ArenaReg} {lbl : Label}
    (h : CtlRestr L st lbl st') {i : Nat} {x : SyncEntry} (hx : st.2.1[i]? = some x)
    (hl : x.Live st.1) (hl' : x.Live st'.1) {ctl : Nat} (hc : ControlOf L st.1 x = some ctl)
    (hp : ctlOp i lbl = none) (hm : ¬ C223Move L (st.1, st.2.1) lbl) :
    ¬ TouchesX L st lbl ctl := fun ht => by
  rcases h.apply hx hl hc ht with h1 | h1 | h1
  · exact h1 hp
  · exact hm h1
  · exact h1 hl'

/-- A former counter-example kind (`store`, `alloc`, `issue`) keeps the controller of an entry live
after the step (WC5.1 corrigé C12, positional `ControlOf`): the kernel steps other than
`transfer` keep the holders of places and the parents (`opStep_facts`); `issue` is a `split` then a
`store` (Spec 1 §77, Part XIV), the `split` of `internal` admitted by `Encap` through the separation
of the registries. -/
theorem cex_ctl_same {k : K} {L : MutexLayout} {lbl : Label} {st st' : SC × SyncReg × ArenaReg}
    (hk : KInvCA st.1) (hsep : AdminSep st.1 st.2.1 st.2.2) (hkind : CexKind lbl)
    (he : Encap5R k L st lbl) (h : LStep k L lbl st st') {x : SyncEntry} (hl' : x.Live st'.1)
    {ctl : Nat} (hc : ControlOf L st.1 x = some ctl) : ControlOf L st'.1 x = some ctl := by
  have hw : WF3 st.1.flat := hk.1.1.2
  have hb : x.guarded < st'.1.A.length := active_lt hl'
  cases h with
  | @kernel s s' reg ar c op hop =>
    cases op <;> simp only [CexKind] at hkind
    · exact kernel_ctl_same hop he.1.1 (fun _ _ h => by cases h) hw hb hc
    · exact kernel_ctl_same hop he.1.1 (fun _ _ h => by cases h) hw hb hc
  | @issue s reg ar c i region dst st' hi =>
    obtain ⟨E, s₁, hE, -, -, hsp, hsto, -⟩ := issueStepC_ok hi
    have hsep' : Encap L (s, reg) (.kernel c (.split E.internal [region])) :=
      fun e hm hl₀ heq => hsep e hm E (List.mem_of_getElem? hE) hl₀
        (by show s.flat.Active E.internal; rw [heq]; exact hl₀) heq.symm
    have hw₁ : WF3 s₁.flat := wf3_after_view hk.1.1.1
      (show ViewStep ((KernelOp.split E.internal [region]).Step k) c s (.ok s₁) from hsp)
      fun t' hR => by
        have hR' : SplitStep k E.internal [region] (s.view c) (.ok t') := hR
        refine ⟨split_preserves_wf3 (SC.wf3_view hk.1.1.1 hw) hR', ?_⟩
        obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hR'; rfl
    have hb₀ : x.guarded < s.A.length := by
      obtain ⟨y, -, -, hy, -⟩ := controlOf_spec hc
      exact lt_of_getElem? hy
    have hb₁ : x.guarded < s₁.A.length := Nat.lt_of_lt_of_le hb₀
      (opStep_facts (L := L) (reg := reg) hsp hsep' (fun _ _ h => by cases h) hw).skel.len
    exact kernel_ctl_same hsto (reg := reg) trivial (fun _ _ h => by cases h) hw₁ hb
      (kernel_ctl_same hsp hsep' (fun _ _ h => by cases h) hw hb₁ hc)
  | _ => simp only [CexKind] at hkind

/-- Brief, corrective pass, task 4: under `Encap6`, from a state satisfying `KInvCA`, `SyncState`
and the separation of the registries, to a state satisfying `WF3`, an `ok` step of a kind `exclu`
or `fin de vie` of the previous pass, or of a former counter-example kind, with entry `i` live
before and after it, does not have the controller of entry `i` in its enlarged footprint and does
not change it. The first conclusion is the restriction of the controller (proposed C22 item 4);
the second is `classified_sound` and `cex_ctl_same`. -/
theorem classified6_sound {k : K} {L : MutexLayout} {lbl : Label}
    {st st' : SC × SyncReg × ArenaReg} (hk : KInvCA st.1) (hw' : WF3 st'.1.flat)
    (hs : SyncState L st.1 st.2.1) (hsep : AdminSep st.1 st.2.1 st.2.2)
    (hkind : ExclKind lbl ∨ FinKind lbl ∨ CexKind lbl) (he : Encap6 k L st lbl st')
    (h : LStep k L lbl st st') {i : Nat} {x : SyncEntry} (hx : st.2.1[i]? = some x)
    (hl : x.Live st.1) (hl' : x.Live st'.1) {ctl : Nat} (hc : ControlOf L st.1 x = some ctl) :
    ¬ TouchesX L st lbl ctl ∧ ControlOf L st'.1 x = some ctl := by
  obtain ⟨hp, hm⟩ := kind_not_proto (L := L) hkind
  refine ⟨restr_not_touch he.2 hx hl hl' hc (hp i) (hm _), ?_⟩
  rcases hkind with hkind | hkind | hkind
  · exact (classified_sound hk hw' hs hsep (.inl hkind) he.1 h (List.mem_of_getElem? hx) hl hl'
      hc).2
  · exact (classified_sound hk hw' hs hsep (.inr hkind) he.1 h (List.mem_of_getElem? hx) hl hl'
      hc).2
  · exact cex_ctl_same hk hsep hkind he.1 h hl' hc

/-! ## By-value `spawn` under hypothesis 3 -/

/-- The footprints of a place are kept by a `transfer` (Spec 1 §63: parents are unchanged). -/
theorem footprint_transferEffC (t : SC) (c src dst q : Nat) :
    footprint (transferEffC t c src dst).P q = footprint t.P q :=
  footprint_congr (by simp [transferEff])
    (transfer_parentOf (t.view c) src dst) q

/-- Along the transfer phases of the by-value composite, a leaf that lies in no destination and
was `Moved`, or lies in some source, is `Moved` at the end (Spec 1 §63 effect: the source leaves
become `Moved`, only the destination leaves become `Init`). -/
theorem transfers_moved (c l : Nat) : ∀ (t : SC) (vs : List (Nat × Nat)),
    (∀ v ∈ vs, l ∉ footprint t.P v.2) → (t.I l = .moved ∨ ∃ v ∈ vs, l ∈ footprint t.P v.1) →
    (transfersEff c t vs).I l = .moved
  | t, [], _, h => by
    rcases h with h | ⟨v, hv, -⟩
    · exact h
    · cases hv
  | t, v :: vs, hd, h => by
    have hI : (transferEffC t c v.1 v.2).I l = if l ∈ footprint t.P v.2 then .init
        else if l ∈ footprint t.P v.1 then .moved else t.I l := rfl
    have hnd := hd v List.mem_cons_self
    show (transfersEff c (transferEffC t c v.1 v.2) vs).I l = .moved
    refine transfers_moved c l (transferEffC t c v.1 v.2) vs
      (fun w hw => by rw [footprint_transferEffC]; exact hd w (List.mem_cons_of_mem _ hw)) ?_
    rw [hI]
    simp only [hnd, ↓reduceIte]
    rcases h with h | ⟨w, hw, hlw⟩
    · left; split <;> first | rfl | exact h
    · rcases List.mem_cons.1 hw with rfl | hw
      · left; simp [hlw]
      · by_cases hs : l ∈ footprint t.P v.1
        · left; simp [hs]
        · right; exact ⟨w, hw, by rw [footprint_transferEffC]; exact hlw⟩

/-- Brief, corrective pass, task 4, the statement left open by the previous pass: an `ok` by-value
`spawn` admitted by `Encap5R`, from a state satisfying `KInvCA` and `SyncState`, after which the
controller of an entry live after the step is unchanged (hypothesis 3), does not touch it. If the
controller were a leaf of a transfer source, it would be `Moved` after the step (no destination,
all fresh locals of the child, contains it), while `SyncInv` makes the controller of a live entry
`Init` (WC5.1 corrigé C21 item 7; `spawnVal_syncState`). -/
theorem spawnVal_fixed_sound {k : K} {L : MutexLayout} {s s' : SC} {reg : SyncReg}
    {ar : ArenaReg} {c : Nat} {ps : List Nat} {ls : LocalShape} {vs : List (Nat × Nat)}
    (hk : KInvCA s) (hs : SyncState L s reg) (he : Encap5R k L (s, reg, ar) (.spawnVal c ps ls vs))
    (h : SpawnValStep k s c ps ls vs (.ok s')) {x : SyncEntry} (hx : x ∈ reg)
    (hl' : x.Live s') {ctl : Nat} (hc : ControlOf L s x = some ctl)
    (hfix : ControlOf L s' x = some ctl) :
    ¬ Touches L (s, reg, ar) (.spawnVal c ps ls vs) ctl := by
  have hs' := spawnVal_syncState hk h he.1.1 hs
  have hinit : s'.I ctl = .init := by
    have := hs'.1.ctlInit x hx hl'
    rw [hfix] at this
    exact this
  have hlt := ctl_lt hc
  rintro (hle | ⟨v, hv, hmem⟩)
  · exact absurd hlt (Nat.not_lt.2 hle)
  obtain ⟨-, hg⟩ := h
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 hg
  have hv1 : v.1 < s.P.length :=
    Nat.lt_of_le_of_lt (Frames.partOf_le (partOf_of_mem_footprint (t := s.flat) hmem)) hlt
  have hsrc : ctl ∈ footprint (spawnCreate s c ls).P v.1 :=
    (Ern.MemoryModel.Arena.footprint_shapeP (hd := .frame s.nF) hpre.localsOK hv1 ctl).2 hmem
  have hdst : ∀ w ∈ vs, ctl ∉ footprint (spawnCreate s c ls).P w.2 := fun w hw hcw => by
    obtain ⟨j, -, hj⟩ := hpre.freshDst w hw
    have := Frames.partOf_le (partOf_of_mem_footprint (t := (spawnCreate s c ls).flat) hcw)
    omega
  have hmoved := transfers_moved c ctl (spawnCreate s c ls) vs hdst (.inr ⟨v, hv, hsrc⟩)
  have : (spawnValEff s c ps ls vs).I ctl = (transfersEff c (spawnCreate s c ls) vs).I ctl := rfl
  rw [this, hmoved] at hinit
  cases hinit

/-! ## Completeness without restriction of kind -/

/-- A move admitted by C22 item 3 (`transfer`, by-value `spawn`) that keeps the controller of an
entry live before and after it (hypothesis 3) does not have it in its enlarged footprint:
`transfer_fixed_sound`, `spawnVal_fixed_sound`. -/
theorem move_not_touch {k : K} {L : MutexLayout} {lbl : Label} {st st' : SC × SyncReg × ArenaReg}
    (h : LStep k L lbl st st') (he : Encap5R k L st lbl) (hm : C223Move L (st.1, st.2.1) lbl)
    (hk : KInvCA st.1) (hs : SyncState L st.1 st.2.1) {x : SyncEntry} (hx : x ∈ st.2.1)
    (hl : x.Live st.1) (hl' : x.Live st'.1) {ctl : Nat} (hc : ControlOf L st.1 x = some ctl)
    (hfix : ControlOf L st'.1 x = some ctl) : ¬ TouchesX L st lbl ctl := by
  cases h with
  | @kernel s s' reg ar c op hop =>
    cases op with
    | transfer src dst =>
      rintro (ht | ht)
      · exact transfer_fixed_sound hk hs he hop hx hl hc hfix ht
      · exact ht
    | _ => exact absurd hm (by simp [C223Move])
  | spawnVal hsv =>
    rintro (ht | ht)
    · exact spawnVal_fixed_sound hk hs he hsv hx hl' hc hfix ht
    · exact ht
  | _ => exact absurd hm (by simp [C223Move])

/-- Brief, corrective pass, task 4, completeness without restriction of kind: at a step `i` taken
under `Encap6`, from a state satisfying `KInvCA` and `SyncState`, while entry `e` is live before
and after the step and its controller is unchanged by the step (hypothesis 3), a step whose enlarged
footprint contains the controller is a protocol step on `e`, hence the event `ctlIdx e lbls i` of
the controller graph. By the restriction, the step is a protocol step of `e`, a move admitted by
C22 item 3 (excluded by `move_not_touch`), or ends the entry. `KInvCA`, `SyncState` and
hypothesis 3 are used only for the moves. -/
theorem completeness6 {k : K} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg}
    {lbls : List Label} {i : Nat} (hi : i < lbls.length) (hst : LStep k L lbls[i] (σ i) (σ (i + 1)))
    (he : Encap6 k L (σ i) lbls[i] (σ (i + 1))) (hk : KInvCA (σ i).1)
    (hs : SyncState L (σ i).1 (σ i).2.1) {e : Nat} {x : SyncEntry}
    (hx : (σ i).2.1[e]? = some x) (hl : x.Live (σ i).1) (hl' : x.Live (σ (i + 1)).1)
    {ctl : Nat} (hc : ControlOf L (σ i).1 x = some ctl)
    (hfix : ControlOf L (σ (i + 1)).1 x = some ctl) (ht : TouchesX L (σ i) lbls[i] ctl)
    (o : Ords) :
    ∃ c op, ctlOp e lbls[i] = some (c, op) ∧
      (ctlGraph o e lbls).ev? (ctlIdx e lbls i) = some ⟨c, op.kind o⟩ := by
  rcases he.2.apply hx hl hc ht with hp | hm | hd
  · cases hop : ctlOp e lbls[i] with
    | none => exact absurd hop hp
    | some p => exact ⟨p.1, p.2, rfl, ctlGraph_ev o e hi hop⟩
  · exact absurd ht (move_not_touch hst he.1 hm hk hs (List.mem_of_getElem? hx) hl hl' hc hfix)
  · exact absurd hl' hd

/-- `ControlOf` reads only the `guarded` identity of the entry. -/
theorem controlOf_guarded_eq {L : MutexLayout} {s : SC} {x y : SyncEntry}
    (h : y.guarded = x.guarded) : ControlOf L s y = ControlOf L s x := by
  unfold ControlOf; rw [h]

/-- After a step, a registered entry is still registered with the same `guarded` identity
(`EntryStep`). -/
theorem entry_kept {k : K} {L : MutexLayout} {lbl : Label} {st st' : SC × SyncReg × ArenaReg}
    (h : LStep k L lbl st st') {e : Nat} {x : SyncEntry} (hx : st.2.1[e]? = some x) :
    ∃ y, st'.2.1[e]? = some y ∧ y.guarded = x.guarded := by
  have hst := lstep_entry h e
  unfold EntryStep at hst
  cases hop : ctlOp e lbl with
  | none =>
    rw [hop] at hst
    rcases hst with hst | ⟨hn, -⟩
    · exact ⟨x, by rw [hst, hx], rfl⟩
    · rw [hx] at hn; cases hn
  | some p =>
    obtain ⟨c, op⟩ := p
    rw [hop] at hst
    cases op with
    | acq =>
      obtain ⟨x', hx', -, g, hy, -⟩ := hst
      rw [hx] at hx'; cases hx'
      exact ⟨_, hy, rfl⟩
    | unl =>
      obtain ⟨x', hx', hy⟩ := hst
      rw [hx] at hx'; cases hx'
      exact ⟨_, hy, rfl⟩
    | rst =>
      obtain ⟨x', hx', hy⟩ := hst
      rw [hx] at hx'; cases hx'
      exact ⟨_, hy, rfl⟩

/-- Brief, corrective pass, task 4, completeness without restriction of kind on a `Run6` from the
initial state of Spec 1 §47, under `DDSound` (Spec 1 §80) and hypothesis 3 (`CtlFixed`): a step
whose enlarged footprint contains the controller of an entry live before and after it is an event
of the controller graph. -/
theorem completeness6_run {k : K} {L : MutexLayout} {statics : Statics}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} (hdd : DDSound k)
    (hstat : StaticsOK statics) (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], []))
    (hr : Run6 k L σ lbls) {e : Nat} (h3 : CtlFixed σ L lbls e) {i : Nat} (hi : i < lbls.length)
    {x : SyncEntry} (hx : (σ i).2.1[e]? = some x) (hl : x.Live (σ i).1)
    (hl' : x.Live (σ (i + 1)).1) {ctl : Nat} (hc : ControlOf L (σ i).1 x = some ctl)
    (ht : TouchesX L (σ i) lbls[i] ctl) (o : Ords) :
    ∃ c op, ctlOp e lbls[i] = some (c, op) ∧
      (ctlGraph o e lbls).ev? (ctlIdx e lbls i) = some ⟨c, op.kind o⟩ := by
  have hr5 := run6_run5R hr
  have htr := run5R_prefix hr5 (Nat.le_of_lt hi)
  rw [h0] at htr
  obtain ⟨hk₀, hs₀⟩ := init_inv (k := k) hdd hstat L
  obtain ⟨hk, hs, -, -⟩ := trace_inv hdd htr hk₀ hs₀
  have hst := (hr i hi).2
  obtain ⟨y, hy, hyg⟩ := entry_kept hst hx
  obtain ⟨ctl₀, hctl⟩ := h3
  have h1 := hctl i (Nat.le_of_lt hi) (by rw [hx]; rfl)
  have h2 := hctl (i + 1) hi (by rw [hy]; rfl)
  simp only [ctlAt, hx, hy, Option.bind_some] at h1 h2
  rw [hc] at h1
  cases h1
  rw [controlOf_guarded_eq hyg] at h2
  exact completeness6 hi hst (hr i hi).1 hk hs hx hl hl' hc h2 ht o

end Ern.Concurrency.MutexReal
