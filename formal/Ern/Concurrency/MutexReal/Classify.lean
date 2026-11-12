import Ern.Concurrency.MutexReal.Coherence
import Ern.Concurrency.Reachable

/-!
# Classification of the steps that touch the controller

Brief of milestone 4, slice 2, layer R, task 4 (`formal/reports/spec2-m4-mutexreal.md`): for a
live entry `e`, each of the 28 kinds of labels (the 16 kernel operations and the 12 other labels
of `Label`) gets one status. The footprint of a step (`Touches`) is the notion of the brief:
the accesses of `read3`, `write3`, `writeShared` (`Label.Access`), and the source and destination
places of the steps that change an initialization state or a holder (`KernelOp.Writes` of Spec 1
§59 for `store` and `transfer`, extended to the source of `transfer`, to `endUse`, `alloc`,
`issue`, the by-value composite and the fresh locals); for the protocol steps, the controller of
their entry, by the declared realization (`corpus-spec2-m3.md` v10 §2 nonies).

This module proves the statuses `exclu` and `fin de vie` (`classified_sound`) and completeness
for those kinds and the protocol kinds (`completeness`). The witnesses of the statuses
`déplacement`, `fin de vie` and `contre-exemple` are in `Ern.Concurrency.MutexReal.Witness`.
-/

set_option autoImplicit false

namespace Ern.Concurrency.MutexReal

open Ern.MemoryModel Ern.MemoryModel.Access Ern.Concurrency
open SyncPreserveAux SyncInitAux

/-! ## Footprint -/

/-- The leaves usable in `s` and no longer usable in `s'`: the leaves whose storage dies with a step
from `s` to `s'` (Spec 1 §69, §70, §73 effects: dead or unusable places). -/
def Dying (s s' : SC) (l : Nat) : Prop := isLeaf s.P l ∧ s.flat.Usable l ∧ ¬ s'.flat.Usable l

/-- Decidability of `Dying`. -/
instance (s s' : SC) (l : Nat) : Decidable (Dying s s' l) := by unfold Dying; infer_instance

/-- The footprint of step `lbl` from state `st` (brief, task 4): the leaves the step reads or
writes, or whose initialization state or holder relation it changes. `read3`, `write3`,
`writeShared`: their leaves (`Label.Access`). `store`: its target (Spec 1 §59, `KernelOp.Writes`;
§65 effect: the holder of the authority becomes the target). `transfer`: the leaves of the source
(they become `Moved`) and of the destination (written, §59). `endUse`: the leaves of the place
(they become `Uninit`, §69) and the leaves that die with it. `free`, `exitFrame`, `terminate`: the
leaves that die (`Dying`; §70, §73 effects), the wider notion the model has (`FreedLeaf`,
`EndingLeaf`). `alloc`: the provider (§71.2: its metadata is updated), the owner (holder of the new
root, §71) and the fresh leaves. `enterFrame`, `spawn`: the fresh locals. By-value `spawn`: the
fresh locals and the sources of its transfers. `issue`: its destination (§77: an explicit write to
the destination, which holds the block). `newMutex`, `acquire`, `unlock`, `resetLock`: the
controller of their entry, by the declared realization. The other steps (`derive`, `split`,
`release`, `depend`, `pin`, `unpin`, `join`, `deriveSync`, `newArena`, `reset`) create no physical
access by their abstract effect (WC5.1 corrigé C27) and change neither an initialization state, a
holder nor the life of a place: empty. -/
def Touches (L : MutexLayout) (st : SC × SyncReg × ArenaReg) : Label → Nat → Prop
  | .kernel _ (.read _ ls), l | .kernel _ (.write _ ls), l | .kernel _ (.writeShared _ ls), l =>
    l ∈ ls
  | .kernel _ (.store _ p), l => l = p
  | .kernel _ (.transfer src dst), l => l ∈ footprint st.1.P src ∨ l ∈ footprint st.1.P dst
  | .kernel c (.endUse p), l =>
    l ∈ footprint st.1.P p ∨ Dying st.1 (st.1.set (endUseEff (st.1.view c) p)) l
  | .kernel c (.free p _), l => Dying st.1 (st.1.set (freeEff (st.1.view c) p)) l
  | .kernel c .exit, l => Dying st.1 (exitEffC st.1 c) l
  | .terminate c, l => Dying st.1 (termEffC st.1 c) l
  | .kernel _ (.alloc pr ow _), l =>
    l ∈ footprint st.1.P pr ∨ l ∈ footprint st.1.P ow ∨ st.1.P.length ≤ l
  | .kernel _ (.enter _ _), l | .spawn _ _ _, l => st.1.P.length ≤ l
  | .spawnVal _ _ _ vs, l => st.1.P.length ≤ l ∨ ∃ v ∈ vs, l ∈ footprint st.1.P v.1
  | .issue _ _ _ dst, l => l = dst
  | .newMutex _ g, l => ControlOf L st.1 ⟨g, none⟩ = some l
  | .acquire _ i, l | .unlock _ i, l | .resetLock _ i, l =>
    (st.2.1[i]?).bind (ControlOf L st.1) = some l
  | _, _ => False

/-- Decidability of `Touches`. -/
instance (L : MutexLayout) (st : SC × SyncReg × ArenaReg) (lbl : Label) (l : Nat) :
    Decidable (Touches L st lbl l) := by
  unfold Touches; split <;> infer_instance

/-! ## Kinds -/

/-- The kinds of status `exclu` (brief, task 4): `derive`, `split`, `depend`, `enterFrame`,
`exitFrame`, `read3`, `write3`, `writeShared`, `pin`, `unpin`, `free`, `spawn`, `terminate`,
`join`, `deriveSync`, `newArena`, `reset`. -/
def ExclKind : Label → Prop
  | .kernel _ (.derive _ _ _) | .kernel _ (.split _ _) | .kernel _ (.depend _ _)
  | .kernel _ (.enter _ _) | .kernel _ .exit | .kernel _ (.read _ _) | .kernel _ (.write _ _)
  | .kernel _ (.writeShared _ _) | .kernel _ (.pin _) | .kernel _ (.unpin _)
  | .kernel _ (.free _ _) | .spawn _ _ _ | .terminate _ | .join _ _ | .deriveSync _ _
  | .newArena _ _ _ | .reset _ _ => True
  | _ => False

/-- The kinds of status `fin de vie` (brief, task 4): `release`, `endUse`. -/
def FinKind : Label → Prop
  | .kernel _ (.release _) | .kernel _ (.endUse _) => True
  | _ => False

/-- The kinds of status `protocole` (brief, task 4). -/
def ProtoKind : Label → Prop
  | .newMutex _ _ | .acquire _ _ | .unlock _ _ | .resetLock _ _ => True
  | _ => False

/-! ## `exclu` and `fin de vie` -/

/-- An authority exercisable from a frame is active (Spec 1 §43). -/
theorem active_of_exercisable {t : S3} {a : Nat} {m : Mode} (h : t.ExercisableAt a m) :
    t.Active a := by
  cases h with
  | base hy ha => exact ⟨_, hy, ha⟩
  | held hy ha => exact ⟨_, hy, ha⟩

/-- A kernel step other than `transfer`, admitted by `Encap`, keeps the controller of an entry
(WC5.1 corrigé C12: positional `ControlOf`). -/
theorem kernel_ctl_same {k : K} {L : MutexLayout} {reg : SyncReg} {c : Nat} {op : KernelOp}
    {s s' : SC} (hop : opStepC k op c s (.ok s')) (hEnc : Encap L (s, reg) (.kernel c op))
    (hnt : ∀ src dst, op ≠ .transfer src dst) (hw : WF3 s.flat) {x : SyncEntry} {ctl : Nat}
    (hb : x.guarded < s'.A.length) (hc : ControlOf L s x = some ctl) :
    ControlOf L s' x = some ctl :=
  have hf := opStep_facts (reg := reg) hop hEnc hnt hw
  ctl_same_eq hw hf.pskel hb hf.hold hc

/-- The controller of an entry is an existing place. -/
theorem ctl_lt {L : MutexLayout} {s : SC} {x : SyncEntry} {ctl : Nat}
    (hc : ControlOf L s x = some ctl) : ctl < s.P.length := by
  obtain ⟨y, hp, m, -, -, -, -, hkc⟩ := controlOf_spec hc
  exact (mem_kids.1 (List.mem_of_getElem? hkc)).1

/-- `endUse(p)` admitted by `Encap` after which the entry is still live does not touch its
controller (WC5.1 corrigé C22 item 5; Spec 1 §69): if the controller were a leaf of `p`, then `p`,
which is not the controller, would contain the mutex value and the place `slot` holding
`guarded`, and `guarded` would become inactive. -/
theorem endUse_ctl_not_touched {k : K} {L : MutexLayout} {reg : SyncReg} {c p : Nat} {s s' : SC}
    (hop : opStepC k (.endUse p) c s (.ok s')) (hEnc : Encap L (s, reg) (.kernel c (.endUse p)))
    (hw : WF3 s.flat) {x : SyncEntry} (hx : x ∈ reg) (hl : x.Live s) (hl' : x.Live s')
    {ctl : Nat} (hc : ControlOf L s x = some ctl) : ctl ∉ footprint s.P p := by
  have hE : ∀ e ∈ reg, e.Live s → ControlOf L s e ≠ some p ∧
      OptP (slotOf s e.guarded) (fun q => partOf s.P p q → p = q) True := hEnc
  obtain ⟨t, hR, rfl⟩ := viewStep_ok hop
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hR
  intro hmem
  obtain ⟨y', hy', ya'⟩ := hl'
  obtain ⟨y, hy, hnh⟩ := endUse_active (v := s.view c) hy' ya'
  obtain ⟨y₀, hp, m, hy₀, hh, hm, -, hkc⟩ := controlOf_spec hc
  have hy₁ : s.A[x.guarded]? = some y := hy
  rw [hy₀] at hy₁
  cases hy₁
  have hne : ctl ≠ p := fun h => (hE x hx hl).1 (h ▸ hc)
  have hcm : parentOf s.P ctl = some m := (mem_kids.1 (List.mem_of_getElem? hkc)).2
  have hmp := partOf_parent (t := s.flat) hw (partOf_of_mem_footprint (t := s.flat) hmem) hne hcm
  have hpP : hp < s.P.length := by
    simp only [parentOf] at hm
    cases hq : s.P[hp]? with
    | none => rw [hq] at hm; cases hm
    | some _ => exact lt_of_getElem? hq
  have hpm : partOf s.P hp m := ⟨hpP, .inr (by
    rw [chain_cons hm (WF3.parent_lt (s := s.flat) hw hm).1]; exact List.mem_cons_self ..)⟩
  exact hnh (by rw [hh]; exact partOf_trans (t := s.flat) hw hpm hmp)

/-- Brief, task 4, statuses `exclu` and `fin de vie`: an `ok` step of one of these kinds, admitted
by `Encap5R`, from a state satisfying `KInvCA`, `SyncState` and the separation of the registries,
to a state satisfying `WF3` (all hold along every encapsulated trace from the initial state,
`trace_inv`), with a registered entry live before and after the step, does not have the controller
of the entry in its footprint and does not change it. For the leaves that die (`free`,
`exitFrame`, `terminate`, `endUse`), the controller of an entry live after the step is usable
after it (`SyncInv`, WC5.1 corrigé C21 item 3, preserved by `lstep_preserves`). -/
theorem classified_sound {k : K} {L : MutexLayout} {lbl : Label}
    {st st' : SC × SyncReg × ArenaReg} (hk : KInvCA st.1) (hw' : WF3 st'.1.flat)
    (hs : SyncState L st.1 st.2.1) (hsep : AdminSep st.1 st.2.1 st.2.2)
    (hkind : ExclKind lbl ∨ FinKind lbl) (he : Encap5R k L st lbl) (h : LStep k L lbl st st')
    {x : SyncEntry} (hx : x ∈ st.2.1) (hl : x.Live st.1) (hl' : x.Live st'.1) {ctl : Nat}
    (hc : ControlOf L st.1 x = some ctl) :
    ¬ Touches L st lbl ctl ∧ ControlOf L st'.1 x = some ctl := by
  have hw : WF3 st.1.flat := hk.1.1.2
  have hb : x.guarded < st'.1.A.length := active_lt hl'
  have hs' := lstep_preserves h he.1.1 hk hw' (fun _ => hsep) hs
  -- the controller of a live entry is usable after the step (WC5.1 corrigé C21 item 3)
  have usable : ∀ {s' : SC} {reg : SyncReg}, SyncState L s' reg → x ∈ reg → x.Live s' →
      ControlOf L s' x = some ctl → s'.flat.Usable ctl := fun hs₁ hx₁ hl₁ hc₁ => by
    have := hs₁.1.control x hx₁ hl₁
    rw [hc₁] at this
    exact this.1
  cases h with
  | @kernel s s' reg ar c op hop =>
    have hEnc : Encap L (s, reg) (.kernel c op) := he.1.1
    have hctl : (∀ src dst, op ≠ .transfer src dst) → ControlOf L s' x = some ctl :=
      fun hnt => kernel_ctl_same hop hEnc hnt hw hb hc
    cases op with
    | transfer => simp [ExclKind, FinKind] at hkind
    | store => simp [ExclKind, FinKind] at hkind
    | alloc => simp [ExclKind, FinKind] at hkind
    | read a ls =>
      have hx' := he.1.2.2 x hx hl
      rw [hc] at hx'
      exact ⟨hx', hctl fun _ _ h => by cases h⟩
    | write a ls =>
      have hx' := he.1.2.2 x hx hl
      rw [hc] at hx'
      exact ⟨hx', hctl fun _ _ h => by cases h⟩
    | writeShared a ls =>
      have hx' := he.1.2.2 x hx hl
      rw [hc] at hx'
      exact ⟨hx', hctl fun _ _ h => by cases h⟩
    | enter ps ls =>
      exact ⟨fun ht => Nat.not_lt.2 ht (ctl_lt hc), hctl fun _ _ h => by cases h⟩
    | endUse p =>
      have hc' := hctl fun _ _ h => by cases h
      have hu := usable hs' hx hl' hc'
      refine ⟨fun ht => ht.elim (endUse_ctl_not_touched hop hEnc hw hx hl hl' hc) fun hd => ?_, hc'⟩
      obtain ⟨t, hR, rfl⟩ := viewStep_ok hop
      obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hR
      exact hd.2.2 hu
    | derive => exact ⟨id, hctl fun _ _ h => by cases h⟩
    | split => exact ⟨id, hctl fun _ _ h => by cases h⟩
    | release => exact ⟨id, hctl fun _ _ h => by cases h⟩
    | depend => exact ⟨id, hctl fun _ _ h => by cases h⟩
    | exit =>
      have hc' := hctl fun _ _ h => by cases h
      have hu := usable hs' hx hl' hc'
      refine ⟨fun hd => ?_, hc'⟩
      obtain ⟨-, hg⟩ := hop
      obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hg
      exact hd.2.2 hu
    | pin => exact ⟨id, hctl fun _ _ h => by cases h⟩
    | unpin => exact ⟨id, hctl fun _ _ h => by cases h⟩
    | free p auth =>
      have hc' := hctl fun _ _ h => by cases h
      have hu := usable hs' hx hl' hc'
      refine ⟨fun hd => ?_, hc'⟩
      obtain ⟨t, hR, rfl⟩ := viewStep_ok hop
      obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hR
      exact hd.2.2 hu
  | @spawn s s' reg ar c ps ls hsp =>
    have hf := spawn_facts (reg := reg) hsp
    exact ⟨fun ht => Nat.not_lt.2 ht (ctl_lt hc), ctl_same_eq hw hf.pskel hb hf.hold hc⟩
  | @terminate s s' reg ar c ht =>
    have hf := term_facts (reg := reg) hw ht
    have hc' := ctl_same_eq hw hf.pskel hb hf.hold hc
    have hu := usable hs' hx hl' hc'
    refine ⟨fun hd => ?_, hc'⟩
    obtain ⟨-, hg⟩ := ht
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hg
    exact hd.2.2 hu
  | @join s s' reg ar c d hj =>
    have hf := join_facts (reg := reg) hj
    exact ⟨id, ctl_same_eq hw hf.pskel hb hf.hold hc⟩
  | deriveSync hd => exact (deriveSync_excluded hd he.1.1).elim
  | newArena hn =>
    obtain ⟨-, -, rfl⟩ := newArenaStepC_ok hn
    exact ⟨id, hc⟩
  | @reset s reg ar c i st' hr =>
    obtain ⟨E, s₁, hE, hd, hrl, -, -⟩ := resetStepC_ok (k := k) hr
    have hsep' :
        Encap L (s, reg) (.kernel c (.derive E.internal (footprint s.P E.storage) .modify)) :=
      fun e hm hl₀ heq => hsep e hm E (List.mem_of_getElem? hE) hl₀
        (by show s.flat.Active E.internal; rw [heq]; exact hl₀) heq.symm
    have hw₁ : WF3 s₁.flat := wf3_after_view hk.1.1.1
      (show ViewStep ((KernelOp.derive E.internal (footprint s.P E.storage) .modify).Step k) c s
        (.ok s₁) from hd)
      fun t' hR => by
        have hR' : DeriveStep E.internal (footprint s.P E.storage) .modify (s.view c) (.ok t') := hR
        refine ⟨derive_preserves_wf3 (SC.wf3_view hk.1.1.1 hw) hR', ?_⟩
        obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hR'; rfl
    have hf₂ := opStep_facts (L := L) (reg := reg) hrl trivial (fun _ _ h => by cases h) hw₁
    have hb₁ : x.guarded < s₁.A.length := Nat.lt_of_lt_of_le (active_lt hl) (opStep_facts
      (reg := reg) hd hsep' (fun _ _ h => by cases h) hw).skel.len
    exact ⟨id, ctl_same_eq hw₁ hf₂.pskel hb hf₂.hold
      (kernel_ctl_same hd hsep' (fun _ _ h => by cases h) hw hb₁ hc)⟩
  | newMutex => simp [ExclKind, FinKind] at hkind
  | acquire => simp [ExclKind, FinKind] at hkind
  | unlock => simp [ExclKind, FinKind] at hkind
  | resetLock => simp [ExclKind, FinKind] at hkind
  | spawnVal => simp [ExclKind, FinKind] at hkind
  | issue => simp [ExclKind, FinKind] at hkind

/-! ## `transfer` under hypothesis 3 -/

/-- Brief, task 4, `transfer` under hypothesis 3 (controller fixed): an `ok` `transfer` admitted by
`Encap5R` (WC5.1 corrigé C22 item 3), from a state satisfying `KInvCA` and `SyncState`, after which
the controller of a live entry is unchanged, does not touch it. Either the controller moves with the
mutex value to the corresponding leaf of the destination, which differs from it (Spec 1 §63.3: the
source and the destination do not overlap), or it lies outside the source and the destination
(`transfer_ctl_cases`). -/
theorem transfer_fixed_sound {k : K} {L : MutexLayout} {s s' : SC} {reg : SyncReg}
    {ar : ArenaReg} {c src dst : Nat} (hk : KInvCA s) (hs : SyncState L s reg)
    (he : Encap5R k L (s, reg, ar) (.kernel c (.transfer src dst)))
    (hop : opStepC k (.transfer src dst) c s (.ok s')) {x : SyncEntry} (hx : x ∈ reg)
    (hl : x.Live s) {ctl : Nat} (hc : ControlOf L s x = some ctl)
    (hfix : ControlOf L s' x = some ctl) :
    ¬ Touches L (s, reg, ar) (.kernel c (.transfer src dst)) ctl := by
  have hw : WF3 s.flat := hk.1.1.2
  have hx' : TransferExcl L (s, reg) src := he.1.1
  obtain ⟨-, hg⟩ := hop
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 hg
  obtain ⟨hcore, -, -, hci⟩ := syncState_iff.1 hs
  have hctl := (hcore.1 x hx).control hl
  rw [hc] at hctl
  simp only [OptP] at hctl
  rcases transfer_ctl_cases hpre.sameShape hpre.dstNotInit hpre.dstUsable.lt hx' hw hcore hci hx hl
      hc with ⟨hcs, ctl', -, hc', hmem⟩ | ⟨-, hns, hnd⟩
  · rw [hfix] at hc'
    cases hc'
    exact absurd ⟨ctl, mem_footprint.2 ⟨hctl.1.lt, hctl.2, hcs⟩, hmem⟩ hpre.disjoint
  · rintro (h | h)
    · exact hns h
    · exact hnd h

/-! ## Completeness -/

/-- The event of the controller graph for the protocol step `i` on `e`. -/
theorem ctlGraph_ev (o : Ords) (e : Nat) {lbls : List Label} {i : Nat} (hi : i < lbls.length)
    {c : Nat} {op : CtlOp} (h : ctlOp e lbls[i] = some (c, op)) :
    (ctlGraph o e lbls).ev? (ctlIdx e lbls i) = some ⟨c, op.kind o⟩ := by
  simp only [EventModel.Graph.ev?, ctlIdx, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
  exact ctlEvs_at o e hi h

/-- A protocol step that touches the controller of a live entry `e` is a protocol step on `e`:
the controller of another live entry is another leaf (WC5.1 corrigé C21 item 4 for `acquire`,
`unlock` and `resetLock`, whose entry is live; C13 item 8 for `newMutex`). -/
theorem proto_touch {k : K} {L : MutexLayout} {lbl : Label} {st st' : SC × SyncReg × ArenaReg}
    (h : LStep k L lbl st st') (hp : ProtoKind lbl) (hinv : SyncInv L st.1 st.2.1) {e : Nat}
    {x : SyncEntry} (hx : st.2.1[e]? = some x) (hl : x.Live st.1) {ctl : Nat}
    (hc : ControlOf L st.1 x = some ctl) (ht : Touches L st lbl ctl) :
    ∃ c op, ctlOp e lbl = some (c, op) := by
  have other : ∀ (j : Nat) (y : SyncEntry), st.2.1[j]? = some y → y.Live st.1 →
      ControlOf L st.1 y = some ctl → j = e := fun j y hy hyl hyc =>
    hinv.ctlUnique j e y x ctl hy hx hyl hl hyc hc
  cases h with
  | newMutex hn =>
    exfalso
    obtain ⟨-, hpre, -⟩ := hn
    have hcu := hpre.ctlUnique
    simp only [Touches] at ht
    rw [ht] at hcu
    exact hcu x (List.mem_of_getElem? hx) hl hc
  | @acquire s reg ar c j st' ha =>
    obtain ⟨-, y, hy, ⟨hyl, -⟩, -⟩ := ha
    simp only [Touches, hy, Option.bind_some] at ht
    obtain rfl := other j y hy hyl ht
    exact ⟨c, .acq, by simp [ctlOp]⟩
  | @unlock s reg ar c j st' hu =>
    obtain ⟨-, y, -, hy, hyl, -⟩ := hu
    simp only [Touches, hy, Option.bind_some] at ht
    obtain rfl := other j y hy hyl ht
    exact ⟨c, .unl, by simp [ctlOp]⟩
  | @resetLock s reg ar c j st' hr =>
    obtain ⟨-, y, hy, hex, -⟩ := hr
    simp only [Touches, hy, Option.bind_some] at ht
    have hyl : y.Live s := by
      obtain ⟨z, hz, hza⟩ := active_of_exercisable hex; exact ⟨z, hz, hza⟩
    obtain rfl := other j y hy hyl ht
    exact ⟨c, .rst, by simp [ctlOp]⟩
  | _ => simp [ProtoKind] at hp

/-- Brief, task 4, completeness, for the kinds `protocole`, `exclu` and `fin de vie`: at a step
`i` of a trace, taken under `Encap5R` from a state satisfying `KInvCA`, `SyncInv` and the
separation of the registries, while entry `e` is live before and after the step, a step that
touches the controller of `e` is a protocol step on `e`, hence an event of the controller graph,
the event `ctlIdx e lbls i`. The protocol steps of another entry touch another controller (WC5.1
corrigé C21 item 4, C13 item 8). Hypothesis 3 of the brief is not used: the kinds `déplacement`
are outside the statement. `newMutex(e)` itself is not covered: entry `e` does not exist before
it. -/
theorem completeness {k : K} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg}
    {lbls : List Label} {i : Nat} (hi : i < lbls.length) (hst : LStep k L lbls[i] (σ i) (σ (i + 1)))
    (he : Encap5R k L (σ i) lbls[i]) (hk : KInvCA (σ i).1) (hw' : WF3 (σ (i + 1)).1.flat)
    (hs : SyncState L (σ i).1 (σ i).2.1) (hsep : AdminSep (σ i).1 (σ i).2.1 (σ i).2.2)
    (hkind : ProtoKind lbls[i] ∨ ExclKind lbls[i] ∨ FinKind lbls[i]) {e : Nat} {x : SyncEntry}
    (hx : (σ i).2.1[e]? = some x) (hl : x.Live (σ i).1) (hl' : x.Live (σ (i + 1)).1)
    {ctl : Nat} (hc : ControlOf L (σ i).1 x = some ctl) (ht : Touches L (σ i) lbls[i] ctl)
    (o : Ords) :
    ∃ c op, ctlOp e lbls[i] = some (c, op) ∧
      (ctlGraph o e lbls).ev? (ctlIdx e lbls i) = some ⟨c, op.kind o⟩ := by
  suffices hp : ∃ c op, ctlOp e lbls[i] = some (c, op) by
    obtain ⟨c, op, h⟩ := hp
    exact ⟨c, op, h, ctlGraph_ev o e hi h⟩
  rcases hkind with hp | hkind
  · exact proto_touch hst hp hs.1 hx hl hc ht
  · exact absurd ht
      (classified_sound hk hw' hs hsep hkind he hst (List.mem_of_getElem? hx) hl hl' hc).1

/-! ## From the initial state -/

/-- The prefix of a `Run5R` is an encapsulated trace (WC5.1 corrigé C22, C23). -/
theorem run5R_prefix {k : K} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg}
    {lbls : List Label} (hr : Run5R k L σ lbls) {i : Nat} (hi : i ≤ lbls.length) :
    EncapsulatedTrace k L (σ 0) (lbls.take i) (σ i) := by
  have hr' : Run5R k L σ (lbls.take i) := fun j hj => by
    have hj' : j < lbls.length := by simp at hj; omega
    have := hr j hj'
    simp only [List.getElem_take]
    exact this
  have h := run5R_trace hr'
  rw [List.length_take, Nat.min_eq_left hi] at h
  exact encapsulatedTrace5_imp (encapsulatedTrace5C_imp (encapsulatedTrace5R_imp h))

/-- Brief, task 4, completeness on a `Run5R` from the initial state of Spec 1 §47, under `DDSound`
(Spec 1 §80): the invariants of `completeness` hold at every step (`trace_inv`). -/
theorem completeness_run {k : K} {L : MutexLayout} {statics : Statics}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} (hdd : DDSound k)
    (hstat : StaticsOK statics) (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], []))
    (hr : Run5R k L σ lbls) {i : Nat} (hi : i < lbls.length)
    (hkind : ProtoKind lbls[i] ∨ ExclKind lbls[i] ∨ FinKind lbls[i]) {e : Nat} {x : SyncEntry}
    (hx : (σ i).2.1[e]? = some x) (hl : x.Live (σ i).1) (hl' : x.Live (σ (i + 1)).1)
    {ctl : Nat} (hc : ControlOf L (σ i).1 x = some ctl) (ht : Touches L (σ i) lbls[i] ctl)
    (o : Ords) :
    ∃ c op, ctlOp e lbls[i] = some (c, op) ∧
      (ctlGraph o e lbls).ev? (ctlIdx e lbls i) = some ⟨c, op.kind o⟩ := by
  have htr := run5R_prefix hr (Nat.le_of_lt hi)
  have htr' := run5R_prefix hr hi
  rw [h0] at htr htr'
  obtain ⟨hk₀, hs₀⟩ := init_inv (k := k) hdd hstat L
  obtain ⟨hk, hs, hsep, -⟩ := trace_inv hdd htr hk₀ hs₀
  have hw' : WF3 (σ (i + 1)).1.flat := (trace_inv hdd htr' hk₀ hs₀).1.1.1.2
  exact completeness hi (hr i hi).2 (hr i hi).1 hk hw' hs hsep hkind hx hl hl' hc ht o

end Ern.Concurrency.MutexReal
