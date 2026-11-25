import Ern.ConcurrencyModel.RunRefinement

/-!
# Theorem 9e: the modelled steps exercise no invalidated authority (C50; Spec 1 §82.7)

At the grain of abstract steps, for the authorities that the modelled steps use, as
`RefinementArena.usedAuth` and `RefinementArena.lpath_unused` do for the library runs of Spec 1:

* `usesOf`: the authorities a labelled step uses, each with the state in which the sub-step that
  uses it starts; `usesOf_active`: each is active there;
* `lrun_inactive`: an authority that exists and is inactive in a state is active in no later
  state of a run (Spec 1 §42, §58: no authority is reactivated);
* `modeled_steps_skip_invalidated`: no later step uses an authority that a step left inactive.

Limit of these statements: they are about the authorities that the modelled steps use. They do
not discharge the obligation of C50 on the physical accesses after invalidation: those of the
realizations that are not modelled, the controller of the mutex included, stay exported (`OB-C05`,
`OB-C12`, `OB-C20`).
-/

namespace Ern.ConcurrencyModel

open Ern.MemoryModel Ern.MemoryModel.Access Ern.MemoryModel.Refinement ArenaAux

/-! ## The authorities used by a step (Spec 1 §82.7; C2, C13–C19, C37–C39) -/

/-- The authority that an inherited operation O1–O16 uses as a means of access or as the source of
new means of access: that of `read`, `write`, `writeShared` (Spec 1 §66.2, §67.1, §68.2), the
authority whose reference `store` writes (§65, §82.3), the source of `derive` and `split` (§60.1,
§61.1); none for the other operations. It is `RefinementArena.usedAuth` of `kopOf op w`
(`usedAuth_kopOf`). -/
def usedAuthK : KernelOp → Option Nat
  | .read a _ | .write a _ | .writeShared a _ | .store a _ => some a
  | .derive src _ _ | .split src _ => some src
  | _ => none

/-- `usedAuthK` is `RefinementArena.usedAuth`, which does not read the written representation. -/
theorem usedAuth_kopOf (op : KernelOp) (w : WriteRepr) :
    RefinementArena.usedAuth (kopOf op w) = usedAuthK op := by
  cases op <;> rfl

/-- The authorities that a labelled step from `st` uses, each with the state in which the
sub-step that uses it starts (Spec 1 §82.7):

* an inherited operation executed by `c` (C2): `usedAuthK`, in the source state;
* `deriveSync` (C15.1: derived from `guarded`) and `newMutex` (C13.2: exercisable `Modify` over
  `guarded`): `guarded`;
* `acquire` (C16: `deriveSync` from `guarded`) and `resetLock` (C18.1: exercisable `Modify` over
  `guarded`): the `guarded` of the registered entry;
* `newArena` (Spec 1 §76.2: exercisable `Modify` over `internal`): `internal`;
* `issue` (Spec 1 §77, Part XIV): `internal`, source of the `split`, in the source state; then the
  block `|A|`, whose reference the `store` writes, in the state after the `split`;
* `reset` (Spec 1 §78, Part XIV): `internal`, source of the `derive`; the `release` of the derived
  authority uses none (Spec 1 §62);
* `readShared` (C37.2), the concurrent `writeShared` (Spec 1 §68.2, C39), the compare-and-exchange
  (C39): `access`.

`spawn`, the by-value composite (parameters yielded, Spec 1 §72.1; transfers, §63, which use no
authority as a means of access, as `RefinementArena.usedAuth`), `terminate`, `join` and `unlock`
(the release of the grant, Spec 1 §62) use none. The controller-access rights read by C13.11,
C14.3, C17.4 and C18.4 are rights over the controller, read existentially; the physical accesses
they justify are not modelled (`OB-C05`). -/
def usesOf : Label → SC × SyncReg × ArenaReg → List (Nat × SC)
  | .kernel _ op, st => match usedAuthK op with
    | some j => [(j, st.1)]
    | none => []
  | .deriveSync _ g, st => [(g, st.1)]
  | .newMutex _ g, st => [(g, st.1)]
  | .acquire _ i, st => match st.2.1[i]? with
    | some e => [(e.guarded, st.1)]
    | none => []
  | .resetLock _ i, st => match st.2.1[i]? with
    | some e => [(e.guarded, st.1)]
    | none => []
  | .newArena _ _ internal, st => [(internal, st.1)]
  | .issue c i region _, st => match st.2.2[i]? with
    | some E => [(E.internal, st.1),
        (st.1.A.length, st.1.set (splitEff (st.1.view c) E.internal [region]))]
    | none => []
  | .reset _ i, st => match st.2.2[i]? with
    | some E => [(E.internal, st.1)]
    | none => []
  | .readShared _ a _ _ _, st => [(a, st.1)]
  | .writeShared _ a _ _ _, st => [(a, st.1)]
  | .cas _ a _ _ _ _, st => [(a, st.1)]
  | _, _ => []

/-- An authority exercisable on a view is active in the global state (Spec 1 §43; C2). -/
theorem active_of_exercisable_view {s : SC} {c a : Nat} {m : Mode}
    (h : (s.view c).ExercisableAt a m) : s.flat.Active a :=
  have ha : (s.view c).Active a := RefinementArena.active_of_exercisable h
  ha

/-- An inherited operation executed by `c` uses only an authority active in its source state
(Spec 1 §60.1, §61.1, §65.1, §66.2, §67.1, §68.2; C2): `RefinementArena.usedAuth_active` on the
view, and §65.1 of the re-indexed `store`. -/
theorem kernel_uses_active {k : K} {op : KernelOp} {c : Nat} {s s' : SC} {j : Nat}
    (h : opStepC k op c s (.ok s')) (hj : usedAuthK op = some j) : s.flat.Active j := by
  cases op with
  | store a p =>
    obtain rfl : a = j := Option.some.inj hj
    have hd := (Guarded.ok_iff.1 h).1.derivedHeld
    unfold OptP at hd
    split at hd
    · exact ⟨_, ‹_›, hd.1⟩
    · exact hd.elim
  | transfer => cases hj
  | depend => cases hj
  | enter => cases hj
  | exit => cases hj
  | _ =>
    obtain ⟨t, hst, -⟩ := viewStep_ok h
    have := RefinementArena.usedAuth_active (opStep_kopOf (w := fun _ _ => (0, none)) |>.2 hst)
      (by rw [usedAuth_kopOf]; exact hj)
    exact this

/-- **Theorem 9e**, first part (Spec 1 §82.7; C2, C13–C19, C37–C39), for every label: every
authority that a labelled step uses (`usesOf`) is active in the state where the sub-step that uses
it starts, and that state keeps the authorities of the source state and is kept by the target
state (Spec 1 §42, §58). For every label but `issue`, that state is the source state of the step;
for the block of `issue`, it is the state after the internal `split`, which creates the block.
Fragment: every labelled step, every state. The authorities used by the physical accesses that are
not modelled are not in `usesOf` (`OB-C05`, `OB-C12`, `OB-C20`). -/
theorem usesOf_active {ks : KShared} {ML : MutexLayout} {lbl : Label}
    {st st' : SC × SyncReg × ArenaReg} (h : LStep ks ML lbl st st') :
    ∀ u ∈ usesOf lbl st, u.2.flat.Active u.1 ∧ Arena.AKeep st.1.flat u.2.flat ∧
      Arena.AKeep u.2.flat st'.1.flat := by
  have hk := (lstep_keep h).1
  have here : ∀ {u : Nat × SC}, u.2 = st.1 → u.2.flat.Active u.1 →
      u.2.flat.Active u.1 ∧ Arena.AKeep st.1.flat u.2.flat ∧ Arena.AKeep u.2.flat st'.1.flat :=
    fun e ha => ⟨ha, by rw [e]; exact Arena.akeep_of_eq rfl, by rw [e]; exact hk⟩
  intro u hu
  cases h with
  | @kernel s s' reg ar c op hop =>
    simp only [usesOf] at hu
    split at hu
    · rename_i j hj
      rw [List.mem_singleton] at hu; subst hu
      exact here rfl (kernel_uses_active hop hj)
    · cases hu
  | spawn => cases hu
  | terminate => cases hu
  | join => cases hu
  | spawnVal => cases hu
  | unlock => cases hu
  | deriveSync hd =>
    rw [usesOf, List.mem_singleton] at hu; subst hu
    exact here rfl (Guarded.ok_iff.1 hd).1.active
  | newMutex hn =>
    rw [usesOf, List.mem_singleton] at hu; subst hu
    exact here rfl (active_of_exercisable_view hn.1.exercisable)
  | @acquire s reg ar c i st₂ ha =>
    obtain ⟨e, hi, -, hp, -⟩ := ha
    simp only [usesOf, hi, List.mem_singleton] at hu; subst hu
    exact here rfl hp.active
  | @resetLock s reg ar c i st₂ hr =>
    obtain ⟨e, hi, hx, -⟩ := hr
    simp only [usesOf, hi, List.mem_singleton] at hu; subst hu
    exact here rfl (active_of_exercisable_view hx)
  | newArena hn =>
    rw [usesOf, List.mem_singleton] at hu; subst hu
    exact here rfl (active_of_exercisable_view (newArenaStepC_ok hn).2.1.exercisable)
  | @issue s reg ar c i region dst st₂ hi =>
    obtain ⟨E, s₁, hE, -, -, hsp, hsto, -⟩ := issueStepC_ok hi
    obtain ⟨t, hst, rfl⟩ := viewStep_ok hsp
    have hst' : SplitStep ks.toK E.internal [region] (s.view c) (.ok t) := hst
    obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 hst'
    simp only [usesOf, hE, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl
    · exact here rfl hpre.active
    · refine ⟨kernel_uses_active (op := .store s.A.length dst) hsto rfl,
        (opStepC_keep hsp).1, (opStepC_keep hsto).1⟩
  | @reset s reg ar c i st₂ hr =>
    obtain ⟨E, s₁, hE, hd, -⟩ := resetStepC_ok (k := ks.toK) hr
    simp only [usesOf, hE, List.mem_singleton] at hu; subst hu
    exact here rfl (kernel_uses_active (op := .derive E.internal (footprint s.P E.storage) .modify)
      hd rfl)
  | readShared hr =>
    rw [usesOf, List.mem_singleton] at hu; subst hu
    exact here rfl (active_of_exercisable_view (Guarded.ok_iff.1 hr).1.read.exercisable)
  | writeShared hw =>
    rw [usesOf, List.mem_singleton] at hu; subst hu
    exact here rfl (active_of_exercisable_view (Guarded.ok_iff.1 hw).1.o11.exercisable)
  | @cas s s' reg ar c a l succ fail br hc =>
    rw [usesOf, List.mem_singleton] at hu; subst hu
    rcases hc with ⟨-, hc⟩ | ⟨-, hc⟩
    · cases hc
    · cases br with
      | success v =>
        exact here rfl (active_of_exercisable_view (Guarded.ok_iff.1 hc).1.o11.exercisable)
      | failure v =>
        exact here rfl (active_of_exercisable_view (Guarded.ok_iff.1 hc).1.read.exercisable)

/-! ## No reactivation along runs (Spec 1 §42, §58) -/

/-- **Theorem 9e**, second part (Spec 1 §42, §58): along every run of labelled steps, an authority
that exists and is inactive in a state is active in no later state. Fragment: every run, every
label. -/
theorem lrun_inactive {ks : KShared} {ML : MutexLayout} {st st' : SC × SyncReg × ArenaReg}
    {lbls : List Label} (h : LRun ks ML st lbls st') {j : Nat} (hj : j < st.1.A.length)
    (hd : ¬ st.1.flat.Active j) : ¬ st'.1.flat.Active j := by
  induction h with
  | nil => exact hd
  | cons hs _ ih =>
    have hk := (lstep_keep hs).1
    exact ih (hk.lt hj) fun ha => hd (hk.active_back ha hj)

/-- Runs of labelled steps, each label listed with the state it starts from (C1: the ordered
operations of the contexts, interleaved at the grain of abstract steps). -/
inductive LTrace (ks : KShared) (ML : MutexLayout) :
    SC × SyncReg × ArenaReg → List (Label × (SC × SyncReg × ArenaReg)) →
      SC × SyncReg × ArenaReg → Prop where
  | nil (st : SC × SyncReg × ArenaReg) : LTrace ks ML st [] st
  | cons {lbl : Label} {st st₁ st' : SC × SyncReg × ArenaReg}
      {t : List (Label × (SC × SyncReg × ArenaReg))} :
      LStep ks ML lbl st st₁ → LTrace ks ML st₁ t st' → LTrace ks ML st ((lbl, st) :: t) st'

/-- Every run of labelled steps lists its steps with the states they start from. -/
theorem LRun.trace {ks : KShared} {ML : MutexLayout} {st st' : SC × SyncReg × ArenaReg}
    {lbls : List Label} (h : LRun ks ML st lbls st') :
    ∃ t, LTrace ks ML st t st' ∧ t.map Prod.fst = lbls := by
  induction h with
  | nil => exact ⟨[], .nil _, rfl⟩
  | cons hs _ ih =>
    obtain ⟨t, ht, e⟩ := ih
    exact ⟨_, .cons hs ht, by rw [List.map_cons, e]⟩

/-- Along a run, no step uses an authority that exists and is inactive in the starting state
(Spec 1 §42, §58, §82.7). -/
theorem ltrace_unused {ks : KShared} {ML : MutexLayout} {s₀ : SC} {j : Nat}
    (hj : j < s₀.A.length) (hd : ¬ s₀.flat.Active j) {st st' : SC × SyncReg × ArenaReg}
    {t : List (Label × (SC × SyncReg × ArenaReg))} (hp : LTrace ks ML st t st') :
    Arena.AKeep s₀.flat st.1.flat → ∀ q ∈ t, ∀ u ∈ usesOf q.1 q.2, u.1 ≠ j := by
  induction hp with
  | nil => intro _ q hq; cases hq
  | cons hs _ ih =>
    intro hk q hq u hu e
    rcases List.mem_cons.1 hq with rfl | hq
    · obtain ⟨ha, hk', -⟩ := usesOf_active hs u hu
      rw [e] at ha
      exact hd ((hk.trans hk').active_back ha hj)
    · exact ih (hk.trans (lstep_keep hs).1) q hq u hu e

/-- **Theorem 9e**, third part (Spec 1 §82.7, §42, §58; C50), for the authorities that the
modelled steps use: whatever the context that executes it, no step taken after a step that
invalidates an authority `j` (active before the step, inactive after it) uses `j`. This covers a legal `reset` (the authorities derived
from `internal` that covered the administered storage, Spec 1 §78), an `unlock` (the released
grant, C17), the exit of a frame (C6) and a `terminate` (C7) (the authorities released with the
frame, Spec 1 §73). Fragment: every run of labelled steps, every label.

The statement is limited to the authorities that the modelled steps use (`usesOf`). It does not
discharge the obligation of C50 on the physical accesses after invalidation: those of the
realizations that are not modelled, the controller of the mutex included, stay exported
(`OB-C05`, `OB-C12`, `OB-C20`). -/
theorem modeled_steps_skip_invalidated {ks : KShared} {ML : MutexLayout} {lbl : Label}
    {st₁ st₂ st₃ : SC × SyncReg × ArenaReg} {t : List (Label × (SC × SyncReg × ArenaReg))}
    (h : LStep ks ML lbl st₁ st₂) (hp : LTrace ks ML st₂ t st₃) {j : Nat}
    (ha : st₁.1.flat.Active j) (hd : ¬ st₂.1.flat.Active j) :
    ∀ q ∈ t, ∀ u ∈ usesOf q.1 q.2, u.1 ≠ j := by
  obtain ⟨y, hy, -⟩ := ha
  exact ltrace_unused ((lstep_keep h).1.lt (lt_of_getElem? hy)) hd hp (Arena.akeep_of_eq rfl)

end Ern.ConcurrencyModel
