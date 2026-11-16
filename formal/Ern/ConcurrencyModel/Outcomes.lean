import Ern.ConcurrencyModel.Library

/-!
# Theorem 7: outcomes and enabledness (C8, C15–C18)

Theorem 7 of `formal/DESIGN.md`, Milestone 4, target theorems. Each outcome class is defined from
the conditions of its own clause; the outcome type is that of Spec 1 §58 (`Outcome3`), with no
added constructor; a legal request that is not enabled has no outcome (DESIGN.md, "Abstract
steps").

* `join` (C8): `reject` for an unknown identifier, legal and not enabled for a live target, `ok`
  with the state unchanged for a completed target.
* `acquire` (C16): `reject` for an invalid requester-side request (C16.1), legal and not enabled
  when the recorded grant is not `none` (C16.2), `ok` otherwise (C16.3); invalid requester-side
  conditions take precedence for the same state.
* `deriveSync` (C15), `unlock` (C17), `resetLock` (C18): `ok` or `reject`, no waiting class;
  `resetLock` does not require `grant = none`.

The logical controller state is the recorded grant of the entry (C12, C17 effect); `acquire` is
one coherent abstract step (C16), so no abstract state has the controller occupied by another
acquisition with `grant = none`.
-/

namespace Ern.ConcurrencyModel

open Ern.MemoryModel.Access

/-! ## `join` (C8) -/

/-- C8: the identifier is unknown to the execution: `reject`. -/
def JoinReject (s : SC) (c d : Nat) : Prop := s.Live c ∧ s.C[d]? = none

/-- C8: a legal `join` whose target is live is not activable as a successful abstract step. -/
def JoinNotEnabled (s : SC) (c d : Nat) : Prop :=
  s.Live c ∧ OptP (s.C[d]?) (fun x => x.life = .live) False

/-- C8: the target has a recorded completed lifecycle state: `ok`. -/
def JoinOkClass (s : SC) (c d : Nat) : Prop :=
  s.Live c ∧ OptP (s.C[d]?) (fun x => x.life = .done) False

/-- **Theorem 7**, `join` (C8): for a live requester, exactly one class applies; `reject` and `ok`
are its outcomes, the `ok` state being unchanged; a non-enabled request has no outcome; `fail`
is never produced. Fragment: every state. -/
theorem join_classes {s : SC} {c d : Nat} (hl : s.Live c) :
    ((JoinReject s c d ∧ ¬ JoinNotEnabled s c d ∧ ¬ JoinOkClass s c d) ∨
      (¬ JoinReject s c d ∧ JoinNotEnabled s c d ∧ ¬ JoinOkClass s c d) ∨
      (¬ JoinReject s c d ∧ ¬ JoinNotEnabled s c d ∧ JoinOkClass s c d)) ∧
    (JoinReject s c d → JoinStep s c d .reject) ∧
    (JoinOkClass s c d → JoinStep s c d (.ok s)) ∧
    (JoinNotEnabled s c d → ∀ o, ¬ JoinStep s c d o) ∧
    (∀ o, JoinStep s c d o → o ≠ .fail) ∧
    (∀ s', JoinStep s c d (.ok s') → s' = s) := by
  refine ⟨?_, fun h => .reject h.1 h.2, fun h => .ok h.1 h.2, ?_, ?_, ?_⟩
  · cases hd : s.C[d]? with
    | none =>
      refine .inl ⟨⟨hl, hd⟩, fun h => ?_, fun h => ?_⟩
      · have h2 := h.2; rw [hd] at h2; exact h2
      · have h2 := h.2; rw [hd] at h2; exact h2
    | some x =>
      have hn : ¬ JoinReject s c d := fun h => by rw [h.2] at hd; cases hd
      cases hx : x.life with
      | live =>
        refine .inr (.inl ⟨hn, ⟨hl, ?_⟩, fun h => ?_⟩)
        · show OptP (s.C[d]?) _ False; rw [hd]; exact hx
        · have h2 := h.2; rw [hd] at h2; change x.life = .done at h2; rw [hx] at h2; cases h2
      | done =>
        refine .inr (.inr ⟨hn, fun h => ?_, ⟨hl, ?_⟩⟩)
        · have h2 := h.2; rw [hd] at h2; change x.life = .live at h2; rw [hx] at h2; cases h2
        · show OptP (s.C[d]?) _ False; rw [hd]; exact hx
  · rintro ⟨-, hn⟩ o h
    cases h with
    | ok _ hdn =>
      revert hn hdn; cases s.C[d]? with
      | none => intro hn; exact hn.elim
      | some x => simp only [OptP]; intro h1 h2; rw [h1] at h2; cases h2
    | reject _ hu => rw [hu] at hn; exact hn
  · intro o h; cases h <;> (intro e; cases e)
  · intro s' h; cases h; rfl

/-! ## `acquire` (C16) -/

/-- The conditions of `deriveSync` (C15, O1) on `guarded = g` that no recorded grant can make
false: own mode `Modify` (C15.1), active origin chain (C15.2), existing leaves (C15.4), live
current frame (C15.6). Their failure is an independently invalid request (C16.1). -/
def AcquireIndependent (s : SC) (c g : Nat) : Prop :=
  OptP ((s.view c).A[g]?) (fun y => Mode.modify.le y.mode) False ∧
    (∀ x ∈ (s.view c).ancs g, (s.view c).Active x) ∧
    (∀ l ∈ (s.view c).afp g, l < s.P.length ∧ isLeaf s.P l) ∧ (s.view c).top ∈ (s.view c).F

/-- The conditions of `deriveSync` (C15.4, C15.5: O1.2 effective mode `Modify` on the protected
footprint, O1.3 exclusivity) that a covering active descendant of `guarded` makes false. With a
recorded grant, that inability is non-enablement (C16.2: "The inability to derive `guarded`
attributable to such a recorded grant is also non-enablement"); with `grant = none` it is an
independently invalid request (C16.1: "with `grant = none`, an independently invalid
protected-authority invariant is `reject`"). -/
def AcquireGrantSensitive (s : SC) (c g : Nat) : Prop :=
  (∀ l ∈ (s.view c).afp g, Allows (effective (s.view c) g l) .modify) ∧
    ∀ b ∈ List.range s.A.length, OptP (s.A[b]?) (fun y => y.active = true →
      b ∉ g :: (s.view c).ancs g → (∃ l ∈ (s.view c).afp g, l ∈ y.footprint) →
        y.mode = .observe ∧ Mode.modify = .observe) True

/-- C16.1: `acquire` of entry `i` by `c` is an invalid request (`reject`): a failure of entry
existence or liveness (C14.1), of the requester's controller-access authority (C14.3, Spec 1
§68.2), of frame and anchor legality or another condition that no recorded grant explains
(`AcquireIndependent`), or, with `grant = none`, of the protected-authority conditions
(`AcquireGrantSensitive`). These hold whatever the grant (precedence over contention). -/
def AcquireReject (L : MutexLayout) (s : SC) (reg : SyncReg) (c i : Nat) : Prop :=
  s.Live c ∧ (reg[i]? = none ∨ ∃ e, reg[i]? = some e ∧
    (¬ e.Live s ∨ ¬ CtrlRight L s e (s.view c).top ∨ ¬ AcquireIndependent s c e.guarded ∨
      (e.grant = none ∧ ¬ AcquireGrantSensitive s c e.guarded)))

/-- C16.1, C16.2: the request is legal: no requester-side invalidity. -/
def AcquireLegal (L : MutexLayout) (s : SC) (reg : SyncReg) (c i : Nat) : Prop :=
  s.Live c ∧ ∃ e, reg[i]? = some e ∧ e.Live s ∧ CtrlRight L s e (s.view c).top ∧
    AcquireIndependent s c e.guarded ∧ (e.grant = none → AcquireGrantSensitive s c e.guarded)

/-- C16.2: a legal request whose entry records a grant (`grant ≠ none`, C14.2), active or
inactive with surviving derived authorities, is temporarily non-enabled. -/
def AcquireNotEnabled (L : MutexLayout) (s : SC) (reg : SyncReg) (c i : Nat) : Prop :=
  AcquireLegal L s reg c i ∧ ∃ e, reg[i]? = some e ∧ e.grant ≠ none

/-- C16.3: a legal request whose grant is available: successful acquisition. -/
def AcquireOkClass (L : MutexLayout) (s : SC) (reg : SyncReg) (c i : Nat) : Prop :=
  AcquireLegal L s reg c i ∧ ∃ e, reg[i]? = some e ∧ e.grant = none

/-- The outcomes of `acquire` of entry `i` by `c` (C16): `ok` with the effect of C16 (`AcquireOk`),
or `reject` for an invalid request. A non-enabled request has none; there is no `fail` (C16:
"neither `ok`, `reject`, `fail`, nor any new `Outcome3` value"). -/
inductive AcquireOutcome (ks : KShared) (L : MutexLayout) (s : SC) (reg : SyncReg) (c i : Nat) :
    Outcome3 (SC × SyncReg) → Prop where
  | ok {st' : SC × SyncReg} : AcquireOk ks L s reg c i st' → AcquireOutcome ks L s reg c i (.ok st')
  | reject : AcquireReject L s reg c i → AcquireOutcome ks L s reg c i .reject

/-- `AcquireOk` is exactly the `ok` class with its effect (C16.3, C15). -/
theorem acquireOk_iff {ks : KShared} {L : MutexLayout} {s : SC} {reg : SyncReg} {c i : Nat}
    {st' : SC × SyncReg} : AcquireOk ks L s reg c i st' ↔ AcquireOkClass L s reg c i ∧
      ∃ e, reg[i]? = some e ∧
        st' = (deriveSyncEff s c e.guarded, reg.set i { e with grant := some s.A.length }) := by
  constructor
  · rintro ⟨hl, e, hi, ⟨he, hn, hcr⟩, hp, rfl⟩
    exact ⟨⟨⟨hl, e, hi, he, hcr, ⟨hp.mode, hp.chainActive, hp.leaves, hp.frameLive⟩,
      fun _ => ⟨hp.modeOK, hp.exclusive⟩⟩, e, hi, hn⟩, e, hi, rfl⟩
  · rintro ⟨⟨⟨hl, e, hi, he, hcr, ⟨hm, hca, hle, hfl⟩, hgs⟩, e', hi', hn⟩, e'', hi'', rfl⟩
    rw [hi] at hi' hi''; cases hi'; cases hi''
    obtain ⟨hmo, hex⟩ := hgs hn
    exact ⟨hl, e, hi, ⟨he, hn, hcr⟩, ⟨he, hm, ⟨e, List.mem_of_getElem? hi, rfl, he, hn, hcr⟩, hca,
      hle, fun _ h => h, hmo, hex, hfl⟩, rfl⟩

/-- **Theorem 7**, `acquire` (C16): for a live requester, exactly one of the three classes of C16
applies, in every state (C16: the classification is per abstract state); the `ok` class is
exactly the existence of an `AcquireOk` step; a non-enabled request has no outcome and no labelled
step; `fail` is never produced. Fragment: every state, every registry. -/
theorem acquire_classes {ks : KShared} {L : MutexLayout} {s : SC} {reg : SyncReg} {ar : ArenaReg}
    {c i : Nat} (hl : s.Live c) :
    ((AcquireReject L s reg c i ∧ ¬ AcquireNotEnabled L s reg c i ∧ ¬ AcquireOkClass L s reg c i) ∨
      (¬ AcquireReject L s reg c i ∧ AcquireNotEnabled L s reg c i ∧
        ¬ AcquireOkClass L s reg c i) ∨
      (¬ AcquireReject L s reg c i ∧ ¬ AcquireNotEnabled L s reg c i ∧
        AcquireOkClass L s reg c i)) ∧
    (AcquireOkClass L s reg c i ↔ ∃ st', AcquireOk ks L s reg c i st') ∧
    (AcquireNotEnabled L s reg c i → (∀ o, ¬ AcquireOutcome ks L s reg c i o) ∧
      ∀ st', ¬ LStep ks L (.acquire c i) (s, reg, ar) st') ∧
    (∀ o, AcquireOutcome ks L s reg c i o → o ≠ .fail) := by
  have hrl : AcquireReject L s reg c i → ¬ AcquireLegal L s reg c i := by
    rintro ⟨-, hn | ⟨e, hi, hb⟩⟩ ⟨-, e', hi', he, hcr, hind, hgs⟩
    · rw [hn] at hi'; cases hi'
    · rw [hi] at hi'; cases hi'
      rcases hb with hb | hb | hb | ⟨hn, hb⟩
      · exact hb he
      · exact hb hcr
      · exact hb hind
      · exact hb (hgs hn)
  have hlr : ¬ AcquireReject L s reg c i → AcquireLegal L s reg c i := by
    intro hnr
    cases hi : reg[i]? with
    | none => exact absurd ⟨hl, .inl hi⟩ hnr
    | some e =>
      have hn' : ¬ (¬ e.Live s ∨ ¬ CtrlRight L s e (s.view c).top ∨
          ¬ AcquireIndependent s c e.guarded ∨
          (e.grant = none ∧ ¬ AcquireGrantSensitive s c e.guarded)) := fun hx =>
        hnr ⟨hl, .inr ⟨e, hi, hx⟩⟩
      refine ⟨hl, e, hi, Classical.byContradiction fun h => hn' (.inl h),
        Classical.byContradiction fun h => hn' (.inr (.inl h)),
        Classical.byContradiction fun h => hn' (.inr (.inr (.inl h))), fun hg =>
        Classical.byContradiction fun h => hn' (.inr (.inr (.inr ⟨hg, h⟩)))⟩
  have hok : AcquireOkClass L s reg c i ↔ ∃ st', AcquireOk ks L s reg c i st' := by
    constructor
    · rintro ⟨hlg, e, hi, hn⟩
      exact ⟨_, acquireOk_iff.2 ⟨⟨hlg, e, hi, hn⟩, e, hi, rfl⟩⟩
    · rintro ⟨st', h⟩; exact (acquireOk_iff.1 h).1
  have hne_ok : AcquireNotEnabled L s reg c i → ¬ AcquireOkClass L s reg c i := by
    rintro ⟨-, e, hi, hn⟩ ⟨-, e', hi', hn'⟩
    rw [hi] at hi'; cases hi'; exact hn hn'
  refine ⟨?_, hok, fun hne => ⟨?_, ?_⟩, ?_⟩
  · by_cases hr : AcquireReject L s reg c i
    · exact .inl ⟨hr, fun h => hrl hr h.1, fun h => hrl hr h.1⟩
    · have hlg := hlr hr
      obtain ⟨-, e, hi, -⟩ := id hlg
      by_cases hg : e.grant = none
      · exact .inr (.inr ⟨hr, fun h => hne_ok h ⟨hlg, e, hi, hg⟩, ⟨hlg, e, hi, hg⟩⟩)
      · exact .inr (.inl ⟨hr, ⟨hlg, e, hi, hg⟩, fun h => hne_ok ⟨hlg, e, hi, hg⟩ h⟩)
  · intro o h
    cases h with
    | ok h => exact hne_ok hne (hok.2 ⟨_, h⟩)
    | reject h => exact hrl h hne.1
  · intro st' h
    cases h with
    | acquire h => exact hne_ok hne (hok.2 ⟨_, h⟩)
  · intro o h; cases h <;> (intro e; cases e)

/-- C16, precedence: an invalid requester-side condition makes `acquire` `reject` whatever the
recorded grant, for the same abstract state; in particular a missing controller-access right
(C14.3) is `reject` even when the grant is taken. -/
theorem acquire_reject_precedence {L : MutexLayout} {s : SC} {reg : SyncReg} {c i : Nat}
    {e : SyncEntry} (hl : s.Live c) (hi : reg[i]? = some e)
    (hcr : ¬ CtrlRight L s e (s.view c).top) : AcquireReject L s reg c i :=
  ⟨hl, .inr ⟨e, hi, .inr (.inl hcr)⟩⟩

/-! ## `deriveSync` (C15) -/

/-- **Theorem 7**, `deriveSync` (C15): for a live context, the outcome is `ok` exactly when the
preconditions of C15 hold and `reject` otherwise; there is no waiting class and no `fail`.
Fragment: every state, every contract `K_C` and registry. -/
theorem deriveSync_outcomes {R : Type} {kc : KC R} {r : R} {s : SC} {c g : Nat}
    (hl : s.Live c) :
    (DeriveSyncPre kc r s c g → DeriveSyncStep kc r s c g (.ok (deriveSyncEff s c g))) ∧
      (¬ DeriveSyncPre kc r s c g → DeriveSyncStep kc r s c g .reject) ∧
      (∀ o, DeriveSyncStep kc r s c g o → o ≠ .fail) :=
  ⟨fun h => ⟨hl, .ok h⟩, fun h => ⟨hl, .reject h⟩, fun o ⟨_, h⟩ e => by subst e; cases h⟩

/-! ## `unlock` (C17) -/

/-- The preconditions of `unlock` of entry `i` by `c` (C17.1–C17.4). -/
def UnlockPre (L : MutexLayout) (s : SC) (reg : SyncReg) (c i : Nat) : Prop :=
  s.Live c ∧ ∃ e g, reg[i]? = some e ∧ e.Live s ∧ e.grant = some g ∧ ReleasePre (s.view c) g ∧
    CtrlRight L s e (s.view c).top ∧ CtrlRight L (prospectiveUnlock s c g) e (s.view c).top

/-- The outcomes of `unlock` (C17): `ok` with the coherent effect, `reject` when a precondition
fails (a recorded grant that has become inactive included); no waiting outcome, no `fail`. -/
inductive UnlockOutcome (L : MutexLayout) (s : SC) (reg : SyncReg) (c i : Nat) :
    Outcome3 (SC × SyncReg) → Prop where
  | ok {st' : SC × SyncReg} : UnlockOk L s reg c i st' → UnlockOutcome L s reg c i (.ok st')
  | reject : s.Live c → ¬ UnlockPre L s reg c i → UnlockOutcome L s reg c i .reject

/-- **Theorem 7**, `unlock` (C17): for a live context, `ok` exactly when C17.1–C17.4 hold, else
`reject`; there is no waiting class and no `fail`. Fragment: every state. -/
theorem unlock_outcomes {L : MutexLayout} {s : SC} {reg : SyncReg} {c i : Nat} (hl : s.Live c) :
    (UnlockPre L s reg c i ↔ ∃ st', UnlockOk L s reg c i st') ∧
      (∀ o, UnlockOutcome L s reg c i o → o ≠ .fail) ∧
      (UnlockPre L s reg c i ∨ UnlockOutcome L s reg c i .reject) := by
  refine ⟨⟨?_, ?_⟩, (fun o h => by cases h <;> (intro e; cases e)), ?_⟩
  · rintro ⟨hl, e, g, hi, he, hg, hr, h1, h2⟩
    exact ⟨_, hl, e, g, hi, he, hg, hr, h1, h2, rfl⟩
  · rintro ⟨st', hl, e, g, hi, he, hg, hr, h1, h2, -⟩
    exact ⟨hl, e, g, hi, he, hg, hr, h1, h2⟩
  · by_cases h : UnlockPre L s reg c i
    · exact .inl h
    · exact .inr (.reject hl h)

/-! ## `resetLock` (C18) -/

/-- The preconditions of `resetLock` of entry `i` by `c` (C18.1–C18.4); no prerequisite on the
recorded grant (C18). -/
def ResetLockPre (L : MutexLayout) (s : SC) (reg : SyncReg) (c i : Nat) : Prop :=
  s.Live c ∧ ∃ e, reg[i]? = some e ∧ (s.view c).ExercisableAt e.guarded .modify ∧
    NoCoveringDesc s e.guarded ∧
    OptP (ControlOf L s e) (fun ctl => s.flat.Usable ctl ∧ isLeaf s.P ctl) False ∧
    CtrlRight L s e (s.view c).top

/-- The outcomes of `resetLock` (C18): `ok` with the coherent effect, `reject` when a precondition
fails; no waiting outcome, no `fail`. -/
inductive ResetLockOutcome (L : MutexLayout) (s : SC) (reg : SyncReg) (c i : Nat) :
    Outcome3 (SC × SyncReg) → Prop where
  | ok {st' : SC × SyncReg} : ResetLockOk L s reg c i st' → ResetLockOutcome L s reg c i (.ok st')
  | reject : s.Live c → ¬ ResetLockPre L s reg c i → ResetLockOutcome L s reg c i .reject

/-- **Theorem 7**, `resetLock` (C18): for a live context, `ok` exactly when C18.1–C18.4 hold,
whatever the recorded grant (`none` included), else `reject`; no waiting class, no `fail`.
Fragment: every state. -/
theorem resetLock_outcomes {L : MutexLayout} {s : SC} {reg : SyncReg} {c i : Nat}
    (hl : s.Live c) :
    (ResetLockPre L s reg c i ↔ ∃ st', ResetLockOk L s reg c i st') ∧
      (∀ o, ResetLockOutcome L s reg c i o → o ≠ .fail) ∧
      (ResetLockPre L s reg c i ∨ ResetLockOutcome L s reg c i .reject) := by
  refine ⟨⟨?_, ?_⟩, (fun o h => by cases h <;> (intro e; cases e)), ?_⟩
  · rintro ⟨hl, e, hi, hx, hn, hc, hr⟩
    exact ⟨_, hl, e, hi, hx, hn, hc, hr, rfl⟩
  · rintro ⟨st', hl, e, hi, hx, hn, hc, hr, -⟩
    exact ⟨hl, e, hi, hx, hn, hc, hr⟩
  · by_cases h : ResetLockPre L s reg c i
    · exact .inl h
    · exact .inr (.reject hl h)

end Ern.ConcurrencyModel
