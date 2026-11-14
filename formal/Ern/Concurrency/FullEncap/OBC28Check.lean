import Ern.Concurrency.FullEncap.HandoffExtSame
import Ern.Concurrency.FullEncap.ResetException

/-!
# Targeted compatibility check of `OB-C28`

Brief of milestone 4, slice 4, task 6 (`formal/reports/spec2-m4-handoff-ext.md`): does closing the
two gaps of WC5.3 `OB-C28` require changing a rule of WC5.3, or only the encoding? No rule and no
existing definition is changed here.

* §78.1 (`MetaRight` of `reset`): on a `RunFull` from the initial state, every `reset` step
  satisfies `MetaRightG` (the guard-free form of Spec 1 §78.1) in the state before it
  (`reset_metaRightG_run`): the guard-free exercise of `internal` that `PremG` reads goes through
  the place holding it, the arena value (§55, item 2, `ArenaInv.shape`).
* Inventory points established by reading in slice 3: `AcquireOk`, `UnlockOk`, `ResetLockOk` are
  the rights of the table and a remainder (`acquireOk_iff`, `unlockOk_iff`, `resetLockOk_iff`;
  the remainder is checked by `ScanRights`, outside the build); `IssueStepC` calls `opStepC` only
  for `split` and `store` (`issueStepC_iff`); `ParamOriginHidden` is a negative reading
  (`paramOriginHidden_iff`, `paramOriginHidden_no_exer5`).
-/

set_option autoImplicit false

namespace Ern.Concurrency.FullEncap.OBC28

open Ern.MemoryModel Ern.MemoryModel.Access Ern.Concurrency Ern.Concurrency.MutexReal
open Ern.Concurrency.FullEncap

/-! ## §78.1 on `reset` -/

/-- An exercise of an authority held by the place `p`, through an authority with effective
`Modify` over the leaves of `p`, is `MetaRightG` when that authority is `internal` (§46: the arena
value is the place holding `internal`). -/
theorem metaRightG_of_held {s : SC} {reg : SyncReg} {c : Nat} {E : Arena.ArenaEntry}
    {y : Authority} {p b : Nat} (hy : s.A[E.internal]? = some y) (hp : y.holder = .place p)
    (hb : Exer5 s reg c b .modify)
    (hall : ∀ l ∈ footprint s.P p, Allows (effective s.flat b l) .modify) :
    MetaRightG (s, reg) c E := by
  dsimp only [MetaRightG, Arena.arenaValue]
  rw [show s.flat.A[E.internal]? = some y from hy]
  dsimp only
  rw [hp]
  exact ⟨b, List.mem_range.2 (exer5_lt hb), hb, hall⟩

/-- Under the arena invariant (`ArenaInvC`, Spec 1 §55), the guard-free premise of `reset`
(`PremG`: `internal` exercisable at `Modify` without a live `guarded`) gives `MetaRightG`, the
guard-free form of §78.1 (`MetaRight(s, arena)`: exercisable `Modify` over the arena value):
`internal` is held by a place (§55, item 2), so its exercise goes through a right over that place,
which is the arena value (§46). -/
theorem reset_metaRightG_step {k : K} {L : MutexLayout} {st : SC × SyncReg × ArenaReg}
    {c ai : Nat} (hlib : LibInv L st) (hp : PremG k L st (.reset c ai)) :
    OptP (st.2.2[ai]?) (fun E => MetaRightG (st.1, st.2.1) c E) False := by
  have hp' := hp
  simp only [PremG] at hp'
  revert hp'
  cases hE : st.2.2[ai]? with
  | none => exact id
  | some E =>
    rintro ⟨hx, -⟩
    show MetaRightG (st.1, st.2.1) c E
    have hmem : E ∈ st.2.2 := List.mem_of_getElem? hE
    obtain ⟨-, hinv⟩ := hlib.2.2 E hmem
    have hlive : Arena.Live st.1.flat E := by
      cases hx with
      | base _ hy ha => exact ⟨_, hy, ha⟩
      | held _ hy ha => exact ⟨_, hy, ha⟩
    have hshape := (hinv hlive).1.shape
    cases hx with
    | @base _ _ y _ hy _ _ hf =>
      have hs : y.mode = .modify ∧ y.holder.isPlace = true := by
        have hy' : st.1.flat.A[E.internal]? = some y := hy
        rw [hy'] at hshape; exact hshape
      rw [hf] at hs
      exact absurd hs.2 (by simp [Holder.isPlace])
    | @held _ p b _ y _ hy _ _ hp' hb hall => exact metaRightG_of_held hy hp' hb hall

/-- Brief, task 6, "Droit de §78.1": on a `RunFull` from the initial state, under `DDSound` and
`StaticsOK`, every `reset` step satisfies `MetaRightG` (Spec 1 §78.1 without a live `guarded`) in
the state before the step, hence `MetaRight` (§78.1) from the current frame of its context. -/
theorem reset_metaRightG_run {k : K} {L : MutexLayout} {statics : Statics}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} (hdd : DDSound k)
    (hstat : StaticsOK statics) (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], []))
    (h : RunFull k L σ lbls) {n : Nat} (hn : n < lbls.length) {c ai : Nat}
    (hl : lbls[n] = .reset c ai) :
    OptP ((σ n).2.2[ai]?) (fun E => MetaRightG ((σ n).1, (σ n).2.1) c E ∧
      Arena.MetaRight ((σ n).1.view c) E) False := by
  have hp := (h n hn).1.2
  rw [hl] at hp
  have hm := reset_metaRightG_step (runFull_inv hdd hstat h0 h (Nat.le_of_lt hn)).2 hp
  revert hm
  cases (σ n).2.2[ai]? with
  | none => exact id
  | some E => exact fun hm => ⟨hm, metaRight_of_metaRightG hm⟩

/-- Brief, task 6: the only `reset` step of the `RunFull` traces of the repository, step 6 of the
trace of legitimate uses (`NonRegression.lv`), satisfies `MetaRightG`. -/
theorem reset_metaRightG_lv :
    NonRegression.lvLbls[6]? = some (.reset 0 0) ∧
    OptP ((NonRegression.lvσ 6).2.2[0]?) (fun E =>
      MetaRightG ((NonRegression.lvσ 6).1, (NonRegression.lvσ 6).2.1) 0 E) False :=
  ⟨rfl, by decide⟩

/-! ## `AcquireOk`, `UnlockOk`, `ResetLockOk`: the rights of the table and a remainder -/

/-- The preconditions of `deriveSync` other than its authorization (`DeriveSyncPre` without
`authorized`, WC5.3 C15 items 1, 2, 4–6). -/
def DeriveSyncRest (s : SC) (c g : Nat) : Prop :=
  (s.view c).Active g ∧ OptP ((s.view c).A[g]?) (fun y => Mode.modify.le y.mode) False ∧
    (∀ x ∈ (s.view c).ancs g, (s.view c).Active x) ∧
    (∀ l ∈ (s.view c).afp g, l < s.P.length ∧ isLeaf s.P l) ∧
    (∀ l ∈ (s.view c).afp g, l ∈ (s.view c).afp g) ∧
    (∀ l ∈ (s.view c).afp g, Allows (effective (s.view c) g l) .modify) ∧
    (∀ b ∈ List.range s.A.length, OptP (s.A[b]?) (fun y => y.active = true →
      b ∉ g :: (s.view c).ancs g → (∃ l ∈ (s.view c).afp g, l ∈ y.footprint) →
        y.mode = .observe ∧ Mode.modify = .observe) True) ∧
    (s.view c).top ∈ (s.view c).F

/-- `DeriveSyncPre` is its authorization and `DeriveSyncRest`. -/
theorem deriveSyncPre_iff {R : Type} {kc : KC R} {r : R} {s : SC} {c g : Nat} :
    DeriveSyncPre kc r s c g ↔ kc.SyncAuthorized r s g (s.view c).top ∧ DeriveSyncRest s c g :=
  ⟨fun h => ⟨h.authorized, h.active, h.mode, h.chainActive, h.leaves, h.within, h.modeOK,
      h.exclusive, h.frameLive⟩,
   fun ⟨ha, h1, h2, h3, h4, h5, h6, h7, h8⟩ => ⟨h1, h2, ha, h3, h4, h5, h6, h7, h8⟩⟩

/-- The remainder of `AcquireOk` (WC5.3 C16): the live context, C14 items 1 and 2, the
preconditions of `deriveSync` other than its authorization, the effect. -/
def AcquireRest (s : SC) (reg : SyncReg) (c i : Nat) (e : SyncEntry) (st' : SC × SyncReg) :
    Prop :=
  s.Live c ∧ e.Live s ∧ e.grant = none ∧ DeriveSyncRest s c e.guarded ∧
    st' = (deriveSyncEff s c e.guarded, reg.set i { e with grant := some s.A.length })

/-- Brief, task 6: `AcquireOk` is the rights of the table, C14 item 3 (`CtrlRight`) and C15 item 3
(`DeriveSyncPre.authorized`, `LibSyncAuthorized`), and the remainder `AcquireRest`. -/
theorem acquireOk_iff {k : K} {L : MutexLayout} {s : SC} {reg : SyncReg} {c i : Nat}
    {st' : SC × SyncReg} :
    AcquireOk k L s reg c i st' ↔ ∃ e, reg[i]? = some e ∧ CtrlRight L s e (s.view c).top ∧
      LibSyncAuthorized L reg s e.guarded (s.view c).top ∧ AcquireRest s reg c i e st' := by
  constructor
  · rintro ⟨hl, e, he, ⟨hlive, hg, hc⟩, hd, rfl⟩
    obtain ⟨ha, hr⟩ := deriveSyncPre_iff.1 hd
    exact ⟨e, he, hc, ha, hl, hlive, hg, hr, rfl⟩
  · rintro ⟨e, he, hc, ha, hl, hlive, hg, hr, rfl⟩
    exact ⟨hl, e, he, ⟨hlive, hg, hc⟩, deriveSyncPre_iff.2 ⟨ha, hr⟩, rfl⟩

/-- The preconditions of `release` other than §62.2 (`ReleasePre` without `holderRight`). -/
def ReleaseRest (s : S3) (a : Nat) : Prop :=
  s.Active a ∧ OptP (s.A[a]?) (fun y => y.origin ≠ none) False ∧
    (∀ j ∈ List.range s.A.length, a ∈ s.ancs j → ¬ s.Active j) ∧
    (∀ q ∈ List.range s.P.length, s.Usable q → a ∈ s.D q →
      (s.A[a]?).map (·.holder) = some (.place q))

/-- `ReleasePre` is §62.2 and `ReleaseRest`. -/
theorem releasePre_iff {s : S3} {a : Nat} :
    ReleasePre s a ↔ OptP (s.A[a]?) (fun y => HolderRight s y.holder) False ∧ ReleaseRest s a :=
  ⟨fun h => ⟨h.holderRight, h.active, h.derived, h.noActiveDesc, h.anchors⟩,
   fun ⟨hh, h1, h2, h3, h4⟩ => ⟨h1, h2, hh, h3, h4⟩⟩

/-- The remainder of `UnlockOk` (WC5.3 C17): the live context, items 1 and 3 (with §62.1, §62.3,
§62.4), the effect. -/
def UnlockRest (s : SC) (reg : SyncReg) (c i : Nat) (e : SyncEntry) (g : Nat)
    (st' : SC × SyncReg) : Prop :=
  s.Live c ∧ e.Live s ∧ ReleaseRest (s.view c) g ∧
    st' = (s.set (releaseEff (s.view c) g), reg.set i { e with grant := none })

/-- Brief, task 6: `UnlockOk` is the rights of the table, C17 item 2 (§62.2,
`ReleasePre.holderRight` of the grant) and C17 item 4 (`CtrlRight`), and the remainder
`UnlockRest`. -/
theorem unlockOk_iff {L : MutexLayout} {s : SC} {reg : SyncReg} {c i : Nat}
    {st' : SC × SyncReg} :
    UnlockOk L s reg c i st' ↔ ∃ e g, reg[i]? = some e ∧ e.grant = some g ∧
      OptP ((s.view c).A[g]?) (fun y => HolderRight (s.view c) y.holder) False ∧
      CtrlRight L s e (s.view c).top ∧ UnlockRest s reg c i e g st' := by
  constructor
  · rintro ⟨hl, e, g, he, hlive, hg, hrel, hc, rfl⟩
    obtain ⟨hh, hr⟩ := releasePre_iff.1 hrel
    exact ⟨e, g, he, hg, hh, hc, hl, hlive, hr, rfl⟩
  · rintro ⟨e, g, he, hg, hh, hc, hl, hlive, hr, rfl⟩
    exact ⟨hl, e, g, he, hlive, hg, releasePre_iff.2 ⟨hh, hr⟩, hc, rfl⟩

/-- The remainder of `ResetLockOk` (WC5.3 C18): the live context, items 2 and 3, the effect. -/
def ResetLockRest (L : MutexLayout) (s : SC) (reg : SyncReg) (c i : Nat) (e : SyncEntry)
    (st' : SC × SyncReg) : Prop :=
  s.Live c ∧ NoCoveringDesc s e.guarded ∧
    OptP (ControlOf L s e) (fun ctl => s.flat.Usable ctl ∧ isLeaf s.P ctl) False ∧
    st' = (s, reg.set i { e with grant := none })

/-- Brief, task 6: `ResetLockOk` is the right of the table, C18 item 1 (`ExercisableAt` of
`guarded`), and the remainder `ResetLockRest`; C18 item 4 is outside `ResetLockOk` (`AmCondF`). -/
theorem resetLockOk_iff {L : MutexLayout} {s : SC} {reg : SyncReg} {c i : Nat}
    {st' : SC × SyncReg} :
    ResetLockOk L s reg c i st' ↔ ∃ e, reg[i]? = some e ∧
      (s.view c).ExercisableAt e.guarded .modify ∧ ResetLockRest L s reg c i e st' := by
  constructor
  · rintro ⟨hl, e, he, hx, hn, hc, rfl⟩
    exact ⟨e, he, hx, hl, hn, hc, rfl⟩
  · rintro ⟨e, he, hx, hl, hn, hc, rfl⟩
    exact ⟨hl, e, he, hx, hn, hc, rfl⟩

/-! ## `IssueStepC` calls `opStepC` only for `split` and `store` -/

/-- The outcomes of `issue` (Spec 1 §77; Part XIV: `split` then `store`), with `opStepC` applied
only to `split(internal, [region])` and `store(|A|, dst)`. -/
def IssueSplitStore (k : K) (s : SC) (ar : ArenaReg) (c i : Nat) (region : List Nat) (dst : Nat)
    (o : Outcome3 (SC × ArenaReg)) : Prop :=
  (s.Live c ∧ ar[i]? = none ∧ o = .reject) ∨
  (∃ E, s.Live c ∧ ar[i]? = some E ∧ ¬ Arena.IssueStatic (s.view c) E region dst ∧
    o = .reject) ∨
  (∃ E, s.Live c ∧ ar[i]? = some E ∧ Arena.IssueStatic (s.view c) E region dst ∧
    ¬ Arena.Avail E region ∧ o = .fail) ∨
  (∃ E, ar[i]? = some E ∧ Arena.IssueStatic (s.view c) E region dst ∧ Arena.Avail E region ∧
    opStepC k (.split E.internal [region]) c s .reject ∧ o = .reject) ∨
  (∃ E s₁, ar[i]? = some E ∧ Arena.IssueStatic (s.view c) E region dst ∧ Arena.Avail E region ∧
    opStepC k (.split E.internal [region]) c s (.ok s₁) ∧
    opStepC k (.store s.A.length dst) c s₁ .reject ∧ o = .reject) ∨
  (∃ E s₁ s₂, ar[i]? = some E ∧ Arena.IssueStatic (s.view c) E region dst ∧
    Arena.Avail E region ∧ opStepC k (.split E.internal [region]) c s (.ok s₁) ∧
    opStepC k (.store s.A.length dst) c s₁ (.ok s₂) ∧
    o = .ok (s₂, ar.set i (Arena.issueMeta s.flat E region)))

/-- Brief, task 6: in `IssueStepC`, `opStepC` is applied only to `split` and `store` (the point of
slice 3 established by reading; `ScanRights` over-approximates by following every operation of
`opStepC`). -/
theorem issueStepC_iff {k : K} {s : SC} {ar : ArenaReg} {c i : Nat} {region : List Nat}
    {dst : Nat} {o : Outcome3 (SC × ArenaReg)} :
    IssueStepC k s ar c i region dst o ↔ IssueSplitStore k s ar c i region dst o := by
  constructor
  · intro h
    cases h with
    | noEntry hl he => exact .inl ⟨hl, he, rfl⟩
    | static hl he hs => exact .inr (.inl ⟨_, hl, he, hs, rfl⟩)
    | fail hl he hs ha => exact .inr (.inr (.inl ⟨_, hl, he, hs, ha, rfl⟩))
    | split he hs ha hsp => exact .inr (.inr (.inr (.inl ⟨_, he, hs, ha, hsp, rfl⟩)))
    | store he hs ha hsp hst =>
      exact .inr (.inr (.inr (.inr (.inl ⟨_, _, he, hs, ha, hsp, hst, rfl⟩))))
    | ok he hs ha hsp hst =>
      exact .inr (.inr (.inr (.inr (.inr ⟨_, _, _, he, hs, ha, hsp, hst, rfl⟩))))
  · rintro (⟨hl, he, rfl⟩ | ⟨E, hl, he, hs, rfl⟩ | ⟨E, hl, he, hs, ha, rfl⟩ |
      ⟨E, he, hs, ha, hsp, rfl⟩ | ⟨E, s₁, he, hs, ha, hsp, hst, rfl⟩ |
      ⟨E, s₁, s₂, he, hs, ha, hsp, hst, rfl⟩)
    · exact .noEntry hl he
    · exact .static hl he hs
    · exact .fail hl he hs ha
    · exact .split he hs ha hsp
    · exact .store he hs ha hsp hst
    · exact .ok he hs ha hsp hst

/-! ## `ParamOriginHidden` is a negative reading -/

/-- Brief, task 6: `ParamOriginHidden` (Spec 1 §72.3; WC5.3 C4 item 5) reads `ExercisableAt`
under a negation only: for a `Modify` parameter with an origin, the origin is exercisable in no
mode. It is no right on which the step rests. -/
theorem paramOriginHidden_iff {s : S3} {p : Nat} :
    ParamOriginHidden s p ↔ OptP (s.A[p]?) (fun y => y.mode = .modify →
      OptP y.origin (fun o => ∀ m, ¬ s.ExercisableAt o m) True) True := by
  unfold ParamOriginHidden
  cases s.A[p]? with
  | none => exact Iff.rfl
  | some y =>
    simp only [OptP]
    constructor
    · intro h hm
      have h' := h hm
      revert h'
      cases y.origin with
      | none => exact id
      | some o => exact fun ⟨h1, h2⟩ m => by cases m; exact h1; exact h2
    · intro h hm
      have h' := h hm
      revert h'
      cases y.origin with
      | none => exact id
      | some o => exact fun h => ⟨h .observe, h .modify⟩

/-- `ParamOriginHidden` on the view of a context implies its guard-free form: the origin has no
guard-free exercise either (`exercisable_of_exer5`); substituting `Exer5` would change no accepted
step. -/
theorem paramOriginHidden_no_exer5 {s : SC} {reg : SyncReg} {c p : Nat}
    (h : ParamOriginHidden (s.view c) p) :
    OptP ((s.view c).A[p]?) (fun y => y.mode = .modify →
      OptP y.origin (fun o => ∀ m, ¬ Exer5 s reg c o m) True) True := by
  have h' := paramOriginHidden_iff.1 h
  revert h'
  cases (s.view c).A[p]? with
  | none => exact id
  | some y =>
    intro h' hm
    have h'' := h' hm
    revert h''
    cases y.origin with
    | none => exact id
    | some o => exact fun hn m hx => hn m (exercisable_of_exer5 hx)

end Ern.Concurrency.FullEncap.OBC28
