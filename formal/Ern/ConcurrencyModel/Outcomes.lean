import Ern.ConcurrencyModel.Library

/-!
# Theorem 7: outcomes and enabledness (C8, C15–C18)

Theorem 7 of `formal/DESIGN.md`, Milestone 4, target theorems. Each outcome class is defined from
the conditions of its own clause; the outcome type is that of Spec 1 §58 (`Outcome3`), with no
added constructor; a legal request that is not enabled has no outcome (DESIGN.md, "Abstract
steps").

* `join` (C8): `reject` for a requester that is not live (C8, "Requesting-context validity",
  checked first) or an unknown identifier; for a live requester, legal and not enabled for a live
  target, `ok` with the state unchanged for a completed target.
* `acquire` (C16): `reject` for an invalid requester-side request (C16.1), legal and not enabled
  when the recorded grant is not `none` (C16.2), `ok` otherwise (C16.3); invalid requester-side
  conditions take precedence for the same state.
* `deriveSync` (C15), `unlock` (C17), `resetLock` (C18): `ok` or `reject`, no waiting class;
  `resetLock` does not require `grant = none`.
* `newMutex` (C13, "Outcome"): `ok` or `reject`, no `fail`.
* every request of a context that is not live is `reject` (`dead_requests_reject`,
  `dead_only_reject`); every labelled step has a live requester (`lstep_live`); every request
  other than `join` and `acquire` has an outcome (`requests_have_outcome`), and the legal but
  non-enabled class, the absence of an outcome, has a live requester (`notEnabled_live`).

The logical controller state is the recorded grant of the entry (C12, C17 effect); `acquire` is
one coherent abstract step (C16), so no abstract state has the controller occupied by another
acquisition with `grant = none`.
-/

namespace Ern.ConcurrencyModel

open Ern.MemoryModel.Access

/-! ## `join` (C8) -/

/-- C8: `reject`: the requesting context is not live ("Requesting-context validity": whatever the
target identifier or lifecycle state, with precedence over the classification by target), or the
identifier is unknown to the execution. -/
def JoinReject (s : SC) (c d : Nat) : Prop := ¬ s.Live c ∨ s.C[d]? = none

/-- C8: a legal `join` (live requester) whose target is live is not activable as a successful
abstract step. -/
def JoinNotEnabled (s : SC) (c d : Nat) : Prop :=
  s.Live c ∧ OptP (s.C[d]?) (fun x => x.life = .live) False

/-- C8: a legal `join` (live requester) whose target has a recorded completed lifecycle state:
`ok`. -/
def JoinOkClass (s : SC) (c d : Nat) : Prop :=
  s.Live c ∧ OptP (s.C[d]?) (fun x => x.life = .done) False

/-- **Theorem 7**, `join` (C8): for every requester and every target, exactly one class applies;
the outcome is `reject` exactly when the requester is not live or the identifier is unknown (C8,
"Requesting-context validity" first); a completed target with a live requester gives `ok`, the
state unchanged; a non-enabled request has no outcome; `fail` is never produced. Fragment: every
state. -/
theorem join_classes {s : SC} {c d : Nat} :
    ((JoinReject s c d ∧ ¬ JoinNotEnabled s c d ∧ ¬ JoinOkClass s c d) ∨
      (¬ JoinReject s c d ∧ JoinNotEnabled s c d ∧ ¬ JoinOkClass s c d) ∨
      (¬ JoinReject s c d ∧ ¬ JoinNotEnabled s c d ∧ JoinOkClass s c d)) ∧
    (JoinStep s c d .reject ↔ JoinReject s c d) ∧
    (JoinOkClass s c d → JoinStep s c d (.ok s)) ∧
    (JoinNotEnabled s c d → ∀ o, ¬ JoinStep s c d o) ∧
    (∀ o, JoinStep s c d o → o ≠ .fail) ∧
    (∀ s', JoinStep s c d (.ok s') → s' = s) := by
  refine ⟨?_, ⟨fun h => ?_, fun h => ?_⟩, fun h => .ok h.1 h.2, ?_, ?_, ?_⟩
  · unfold JoinReject JoinNotEnabled JoinOkClass
    by_cases hl : s.Live c
    · cases hd : s.C[d]? with
      | none => exact .inl ⟨.inr rfl, fun h => h.2, fun h => h.2⟩
      | some x =>
        change ((¬ s.Live c ∨ some x = none) ∧ ¬ (s.Live c ∧ x.life = .live) ∧
            ¬ (s.Live c ∧ x.life = .done)) ∨
          (¬ (¬ s.Live c ∨ some x = none) ∧ (s.Live c ∧ x.life = .live) ∧
            ¬ (s.Live c ∧ x.life = .done)) ∨
          (¬ (¬ s.Live c ∨ some x = none) ∧ ¬ (s.Live c ∧ x.life = .live) ∧
            (s.Live c ∧ x.life = .done))
        have hnr : ¬ (¬ s.Live c ∨ some x = none) := fun h => by
          rcases h with h | h
          · exact h hl
          · cases h
        cases hx : x.life with
        | live => exact .inr (.inl ⟨hnr, ⟨hl, rfl⟩, (fun h => by cases h.2)⟩)
        | done => exact .inr (.inr ⟨hnr, (fun h => by cases h.2), ⟨hl, rfl⟩⟩)
    · exact .inl ⟨.inl hl, fun h => hl h.1, fun h => hl h.1⟩
  · cases h with
    | deadRequester hl => exact .inl hl
    | unknown hu => exact .inr hu
  · rcases h with hl | hu
    · exact .deadRequester hl
    · exact .unknown hu
  · intro hn o h
    obtain ⟨hl, hn⟩ := hn
    cases h with
    | ok _ hdn =>
      revert hn hdn; cases s.C[d]? with
      | none => intro hn; exact hn.elim
      | some x => simp only [OptP]; intro h1 h2; rw [h1] at h2; cases h2
    | deadRequester hd => exact hd hl
    | unknown hu => rw [hu] at hn; exact hn
  · intro o h; cases h <;> (intro e; cases e)
  · intro s' h; cases h; rfl

/-! ## `acquire` (C16) -/

/-- The conditions of `deriveSync` (C15, O1) on `guarded = g` that no recorded grant can make
false: own mode `Modify` (C15.1), active origin chain (C15.2), existing leaves (C15.4), live
current frame (C15.6, read on the globally live frames, C2). Their failure is an independently
invalid request (C16.1). -/
def AcquireIndependent (s : SC) (c g : Nat) : Prop :=
  OptP ((s.view c).A[g]?) (fun y => Mode.modify.le y.mode) False ∧
    (∀ x ∈ (s.view c).ancs g, (s.view c).Active x) ∧
    (∀ l ∈ (s.view c).afp g, l < s.P.length ∧ isLeaf s.P l) ∧ (s.view c).top ∈ s.frames

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
  reg[i]? = none ∨ ∃ e, reg[i]? = some e ∧
    (¬ e.Live s ∨ ¬ CtrlRight L s e (s.view c).top ∨ ¬ AcquireIndependent s c e.guarded ∨
      (e.grant = none ∧ ¬ AcquireGrantSensitive s c e.guarded))

/-- C16.1, C16.2: the request is legal: no requester-side invalidity. -/
def AcquireLegal (L : MutexLayout) (s : SC) (reg : SyncReg) (c i : Nat) : Prop :=
  ∃ e, reg[i]? = some e ∧ e.Live s ∧ CtrlRight L s e (s.view c).top ∧
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
  · rintro ⟨e, hi, ⟨he, hn, hcr⟩, hp, rfl⟩
    exact ⟨⟨⟨e, hi, he, hcr, ⟨hp.mode, hp.chainActive, hp.leaves, hp.frameLive⟩,
      fun _ => ⟨hp.modeOK, hp.exclusive⟩⟩, e, hi, hn⟩, e, hi, rfl⟩
  · rintro ⟨⟨⟨e, hi, he, hcr, ⟨hm, hca, hle, hfl⟩, hgs⟩, e', hi', hn⟩, e'', hi'', rfl⟩
    rw [hi] at hi' hi''; cases hi'; cases hi''
    obtain ⟨hmo, hex⟩ := hgs hn
    exact ⟨e, hi, ⟨he, hn, hcr⟩, ⟨he, hm, ⟨e, List.mem_of_getElem? hi, rfl, he, hn, hcr⟩, hca,
      hle, fun _ h => h, hmo, hex, hfl⟩, rfl⟩

/-- **Theorem 7**, `acquire` (C16): for every requester, live or not, exactly one of the three
classes of C16 applies, in every state (C16: the classification is per abstract state); the `ok` class is
exactly the existence of an `AcquireOk` step; a non-enabled request has no outcome and no labelled
step; `fail` is never produced. Fragment: every state, every registry. -/
theorem acquire_classes {ks : KShared} {L : MutexLayout} {s : SC} {reg : SyncReg} {ar : ArenaReg}
    {c i : Nat} :
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
    rintro (hn | ⟨e, hi, hb⟩) ⟨e', hi', he, hcr, hind, hgs⟩
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
    | none => exact absurd (.inl hi) hnr
    | some e =>
      have hn' : ¬ (¬ e.Live s ∨ ¬ CtrlRight L s e (s.view c).top ∨
          ¬ AcquireIndependent s c e.guarded ∨
          (e.grant = none ∧ ¬ AcquireGrantSensitive s c e.guarded)) := fun hx =>
        hnr (.inr ⟨e, hi, hx⟩)
      refine ⟨e, hi, Classical.byContradiction fun h => hn' (.inl h),
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
      obtain ⟨e, hi, -⟩ := id hlg
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
    {e : SyncEntry} (hi : reg[i]? = some e)
    (hcr : ¬ CtrlRight L s e (s.view c).top) : AcquireReject L s reg c i :=
  .inr ⟨e, hi, .inr (.inl hcr)⟩

/-- **Theorem 7**, `acquire` (C16.1, C14.3, C2): a request of a context that is not live is
`reject`, never legal and never non-enabled: without a current frame, the requester has no
controller-access right (or the entry is absent). Fragment: every state, every registry. -/
theorem acquire_dead_reject {L : MutexLayout} {s : SC} {reg : SyncReg} {c i : Nat}
    (hc : ¬ s.Live c) : AcquireReject L s reg c i ∧ ¬ AcquireLegal L s reg c i := by
  have hr : AcquireReject L s reg c i := by
    cases hi : reg[i]? with
    | none => exact .inl hi
    | some e => exact .inr ⟨e, hi, .inr (.inl (SC.dead_not_ctrlRight hc))⟩
  exact ⟨hr, fun ⟨_, _, _, hcr, _⟩ => SC.dead_not_ctrlRight hc hcr⟩

/-! ## `deriveSync` (C15) -/

/-- **Theorem 7**, `deriveSync` (C15): for every executing context, live or not, the outcome is
`ok` exactly when the preconditions of C15 hold and `reject` otherwise; there is no waiting class
and no `fail`. Fragment: every state, every contract `K_C` and registry. -/
theorem deriveSync_outcomes {R : Type} {kc : KC R} {r : R} {s : SC} {c g : Nat} :
    (DeriveSyncPre kc r s c g → DeriveSyncStep kc r s c g (.ok (deriveSyncEff s c g))) ∧
      (¬ DeriveSyncPre kc r s c g → DeriveSyncStep kc r s c g .reject) ∧
      (∀ o, DeriveSyncStep kc r s c g o → o ≠ .fail) :=
  ⟨fun h => .ok h, fun h => .reject h, fun o h e => by subst e; cases h⟩

/-! ## `unlock` (C17) -/

/-- The preconditions of `unlock` of entry `i` by `c` (C17.1–C17.4). -/
def UnlockPre (L : MutexLayout) (s : SC) (reg : SyncReg) (c i : Nat) : Prop :=
  ∃ e g, reg[i]? = some e ∧ e.Live s ∧ e.grant = some g ∧ ReleasePre (s.view c) g ∧
    CtrlRight L s e (s.view c).top ∧ CtrlRight L (prospectiveUnlock s c g) e (s.view c).top

/-- The outcomes of `unlock` (C17): `ok` with the coherent effect, `reject` when a precondition
fails (a recorded grant that has become inactive included); no waiting outcome, no `fail`. -/
inductive UnlockOutcome (L : MutexLayout) (s : SC) (reg : SyncReg) (c i : Nat) :
    Outcome3 (SC × SyncReg) → Prop where
  | ok {st' : SC × SyncReg} : UnlockOk L s reg c i st' → UnlockOutcome L s reg c i (.ok st')
  | reject : ¬ UnlockPre L s reg c i → UnlockOutcome L s reg c i .reject

/-- **Theorem 7**, `unlock` (C17): for every acting context, live or not, `ok` exactly when
C17.1–C17.4 hold, else `reject`; there is no waiting class and no `fail`. Fragment: every
state. -/
theorem unlock_outcomes {L : MutexLayout} {s : SC} {reg : SyncReg} {c i : Nat} :
    (UnlockPre L s reg c i ↔ ∃ st', UnlockOk L s reg c i st') ∧
      (∀ o, UnlockOutcome L s reg c i o → o ≠ .fail) ∧
      (UnlockPre L s reg c i ∨ UnlockOutcome L s reg c i .reject) := by
  refine ⟨⟨?_, ?_⟩, (fun o h => by cases h <;> (intro e; cases e)), ?_⟩
  · rintro ⟨e, g, hi, he, hg, hr, h1, h2⟩
    exact ⟨_, e, g, hi, he, hg, hr, h1, h2, rfl⟩
  · rintro ⟨st', e, g, hi, he, hg, hr, h1, h2, -⟩
    exact ⟨e, g, hi, he, hg, hr, h1, h2⟩
  · by_cases h : UnlockPre L s reg c i
    · exact .inl h
    · exact .inr (.reject h)

/-! ## `resetLock` (C18) -/

/-- The preconditions of `resetLock` of entry `i` by `c` (C18.1–C18.4); no prerequisite on the
recorded grant (C18). -/
def ResetLockPre (L : MutexLayout) (s : SC) (reg : SyncReg) (c i : Nat) : Prop :=
  ∃ e, reg[i]? = some e ∧ (s.view c).ExercisableAt e.guarded .modify ∧
    NoCoveringDesc s e.guarded ∧
    OptP (ControlOf L s e) (fun ctl => s.flat.Usable ctl ∧ isLeaf s.P ctl) False ∧
    CtrlRight L s e (s.view c).top

/-- The outcomes of `resetLock` (C18): `ok` with the coherent effect, `reject` when a precondition
fails; no waiting outcome, no `fail`. -/
inductive ResetLockOutcome (L : MutexLayout) (s : SC) (reg : SyncReg) (c i : Nat) :
    Outcome3 (SC × SyncReg) → Prop where
  | ok {st' : SC × SyncReg} : ResetLockOk L s reg c i st' → ResetLockOutcome L s reg c i (.ok st')
  | reject : ¬ ResetLockPre L s reg c i → ResetLockOutcome L s reg c i .reject

/-- **Theorem 7**, `resetLock` (C18): for every acting context, live or not, `ok` exactly when
C18.1–C18.4 hold, whatever the recorded grant (`none` included), else `reject`; no waiting class,
no `fail`. Fragment: every state. -/
theorem resetLock_outcomes {L : MutexLayout} {s : SC} {reg : SyncReg} {c i : Nat} :
    (ResetLockPre L s reg c i ↔ ∃ st', ResetLockOk L s reg c i st') ∧
      (∀ o, ResetLockOutcome L s reg c i o → o ≠ .fail) ∧
      (ResetLockPre L s reg c i ∨ ResetLockOutcome L s reg c i .reject) := by
  refine ⟨⟨?_, ?_⟩, (fun o h => by cases h <;> (intro e; cases e)), ?_⟩
  · rintro ⟨e, hi, hx, hn, hc, hr⟩
    exact ⟨_, e, hi, hx, hn, hc, hr, rfl⟩
  · rintro ⟨st', e, hi, hx, hn, hc, hr, -⟩
    exact ⟨e, hi, hx, hn, hc, hr⟩
  · by_cases h : ResetLockPre L s reg c i
    · exact .inl h
    · exact .inr (.reject h)

/-! ## `newMutex` (C13) -/

/-- The outcomes of `newMutex(guarded)` executed by `c` (C13, "Outcome": "`ok` when all applicable
preconditions hold and the registration effect is established; `reject` when any applicable
precondition fails. This operation defines no `fail` outcome"): `ok` with the effect of C13,
`reject` when a precondition C13.1–C13.11 fails. No waiting outcome. -/
inductive NewMutexOutcome (k : K) (L : MutexLayout) (ar : ArenaReg) (s : SC) (reg : SyncReg)
    (c g : Nat) : Outcome3 (SC × SyncReg) → Prop where
  | ok {st' : SC × SyncReg} : NewMutexOk k L ar s reg c g st' →
      NewMutexOutcome k L ar s reg c g (.ok st')
  | reject : ¬ NewMutexPre k L ar s reg c g → NewMutexOutcome k L ar s reg c g .reject

/-- `newMutex` (C13, "Outcome"): for every constructing context, live or not, `ok` exactly when
C13.1–C13.11 hold, else `reject`; no `fail`. Fragment: every state. -/
theorem newMutex_outcomes {k : K} {L : MutexLayout} {ar : ArenaReg} {s : SC} {reg : SyncReg}
    {c g : Nat} :
    (NewMutexPre k L ar s reg c g ↔ ∃ st', NewMutexOk k L ar s reg c g st') ∧
      (∀ o, NewMutexOutcome k L ar s reg c g o → o ≠ .fail) ∧
      (NewMutexPre k L ar s reg c g ∨ NewMutexOutcome k L ar s reg c g .reject) := by
  refine ⟨⟨fun h => ⟨_, h, rfl⟩, fun ⟨_, h, _⟩ => h⟩,
    (fun o h => by cases h <;> (intro e; cases e)), ?_⟩
  by_cases h : NewMutexPre k L ar s reg c g
  · exact .inl h
  · exact .inr (.reject h)

/-! ## Requests of a context that is not live (C2; Spec 1 §58) -/

/-- **Theorem 7**, requests of a context that is not live (C2: "all occurrences of 'the current
frame' refer to the top of the live local stack of `c`"; Spec 1 §58: every operation has an
outcome): such a context has no current frame, so the requester-side precondition of each clause
fails and every request has the outcome `reject`: the inherited operations O1–O16 (C2), `spawn` and
by-value `spawn` (C4.1), `terminate` (C7), `deriveSync` (C15.6) under every contract `K_C`,
`newMutex` (C13.2), `acquire` (C14.3 by C16.1; never legal, hence never non-enabled), `unlock` and
`resetLock` (C17.4, C18.4), the arena operations (Spec 1 §76.1, §77.1, §78), `readShared` (C37.2),
the concurrent `writeShared` and the compare-and-exchange (Spec 1 §68.2, C39), and `join` (C8,
"Requesting-context validity"), whatever its target. Fragment: every state, every registry. -/
theorem dead_requests_reject {ks : KShared} {L : MutexLayout} {s : SC} {reg : SyncReg}
    {ar : ArenaReg} {c : Nat} (hc : ¬ s.Live c) :
    (∀ op, opStepC ks.toK op c s .reject) ∧
    (∀ ps ls, SpawnStep s c ps ls .reject) ∧
    (∀ ps ls vs, SpawnValStep ks.toK s c ps ls vs .reject) ∧
    TermStep ks.toK s c .reject ∧
    (∀ (R : Type) (kc : KC R) (r : R) (g : Nat), DeriveSyncStep kc r s c g .reject) ∧
    (∀ g, NewMutexOutcome ks.toK L ar s reg c g .reject) ∧
    (∀ i, AcquireOutcome ks L s reg c i .reject ∧ ¬ AcquireNotEnabled L s reg c i) ∧
    (∀ i, UnlockOutcome L s reg c i .reject) ∧
    (∀ i, ResetLockOutcome L s reg c i .reject) ∧
    (∀ st i, NewArenaStepC s reg ar c st i .reject) ∧
    (∀ i region dst, IssueStepC ks.toK s ar c i region dst .reject) ∧
    (∀ i, ResetStepC s ar c i .reject) ∧
    (∀ a l order, ReadSharedStep ks s c a l order .reject) ∧
    (∀ a region ord kind, WriteSharedCStep ks s c a region ord kind .reject) ∧
    (∀ a l succ fail br, CasStep ks s c a l succ fail br .reject) ∧
    (∀ d, JoinStep s c d .reject) := by
  have hx : ∀ {a : Nat} {m : Mode}, ¬ (s.view c).ExercisableAt a m := SC.dead_not_exercisable hc
  have hr : ∀ {q : Nat} {m : Mode}, ¬ HasRight (s.view c) m q := SC.dead_not_hasRight hc
  refine ⟨fun op => ?_, fun _ _ => .reject fun hp => hc (SC.live_of_stk hp.creatorLive),
    fun _ _ _ => .reject fun hp => hc (SC.live_of_stk hp.creatorLive),
    .reject fun hp => hc (SC.live_of_stk fun e => by
      have := hp.initialOnly; rw [e] at this; cases this),
    fun _ _ _ _ => .reject fun hp => hc (SC.live_of_top_mem hp.frameLive),
    fun _ => .reject fun hp => hx hp.exercisable,
    fun _ => ⟨.reject (acquire_dead_reject hc).1, fun hne => (acquire_dead_reject hc).2 hne.1⟩,
    fun _ => .reject fun ⟨_, _, _, _, _, _, h1, _⟩ => SC.dead_not_ctrlRight hc h1,
    fun _ => .reject fun ⟨_, _, _, _, _, h1⟩ => SC.dead_not_ctrlRight hc h1,
    fun _ _ => .reject fun hp => hr hp.storageRight, fun i _ _ => ?_, fun i => ?_,
    fun _ _ _ => .reject fun hp => hx hp.read.exercisable,
    fun _ _ _ _ => .reject fun hp => hx hp.o11.exercisable, fun _ _ succ fail br => ?_,
    fun _ => .deadRequester hc⟩
  · cases op with
    | transfer => exact .reject fun hp => hr hp.srcRight
    | depend => exact .reject fun hp => hr hp.right
    | store => exact .reject fun hp => hr hp.right
    | enter => exact .reject fun hp => hc (SC.live_of_stk hp.callerLive)
    | exit => exact .reject fun hp => hc (SC.live_of_stk fun e => hp.hasCaller (by rw [e]; rfl))
    | derive => exact ⟨.reject, .reject fun hp => hx hp.exercisable, rfl⟩
    | split => exact ⟨.reject, .reject fun hp => hx hp.exercisable, rfl⟩
    | read => exact ⟨.reject, .reject fun hp => hx hp.exercisable, rfl⟩
    | write => exact ⟨.reject, .reject fun hp => hx hp.exercisable, rfl⟩
    | writeShared => exact ⟨.reject, .reject fun hp => hx hp.exercisable, rfl⟩
    | pin => exact ⟨.reject, .reject fun hp => hr hp.right, rfl⟩
    | endUse => exact ⟨.reject, .reject fun hp => hr hp.right, rfl⟩
    | free => exact ⟨.reject, .reject fun hp => hr hp.right, rfl⟩
    | alloc => exact ⟨.reject, .reject fun hst => hr hst.ownerRight, rfl⟩
    | release a =>
      refine ⟨.reject, .reject fun hp => ?_, rfl⟩
      have h := hp.holderRight
      unfold OptP at h; split at h
      · rename_i y hy; exact SC.dead_not_holderRight hc hy h
      · exact h.elim
    | unpin o =>
      refine ⟨.reject, .reject fun hp => ?_, rfl⟩
      have h := hp.right
      unfold OptP at h; split at h
      · exact hr h
      · exact h.elim
  · cases hE : ar[i]? with
    | none => exact .noEntry hE
    | some E =>
      refine .static hE fun hst => ?_
      have h := hst.metaRight
      unfold Ern.MemoryModel.Arena.MetaRight OptP at h; split at h
      · exact hr h
      · exact h.elim
  · refine ⟨.reject, ?_, rfl⟩
    cases hE : ar[i]? with
    | none => exact .noEntry hE
    | some E => exact .derive hE (.reject fun hp => hx hp.exercisable)
  · by_cases ho : CasOrdersOK succ fail
    · refine .inr ⟨ho, ?_⟩
      cases br with
      | success v => exact .reject fun hp => hx hp.o11.exercisable
      | failure v => exact .reject fun hp => hx hp.read.exercisable
    · exact .inl ⟨ho, rfl⟩

/-- C2, C8, Spec 1 §58: a request of a context that is not live has no outcome other than
`reject`: no `ok` (each `ok` step requires a live requester, `opStepC_live`, `joinStep_live`) and
no `fail` (the `fail` of `alloc` and of `issue` requires their static preconditions, which read a
right of the current frame: Spec 1 §71.3, §77.1; `join` defines no `fail`, C8). Fragment: every
state. -/
theorem dead_only_reject {ks : KShared} {s : SC} {ar : ArenaReg} {c : Nat} (hc : ¬ s.Live c) :
    (∀ op o, opStepC ks.toK op c s o → o = .reject) ∧
      (∀ i region dst o, IssueStepC ks.toK s ar c i region dst o → o = .reject) ∧
      (∀ d o, JoinStep s c d o → o = .reject) := by
  refine ⟨fun op o h => ?_, fun i region dst o h => ?_, fun d o h => ?_⟩
  · cases o with
    | ok s' => exact absurd (opStepC_live h) hc
    | reject => rfl
    | fail =>
      cases op with
      | transfer | depend | store | enter | exit => cases h
      | alloc pr ow ls =>
        obtain ⟨o₃, hR, ho⟩ := h
        cases o₃ with
        | ok => cases ho
        | reject => cases ho
        | fail =>
          cases hR with
          | fail hst _ => exact absurd hst.ownerRight (SC.dead_not_hasRight hc)
      | _ =>
        obtain ⟨o₃, hR, ho⟩ := h
        cases o₃ with
        | ok => cases ho
        | reject => cases ho
        | fail => cases hR
  · cases o with
    | ok st' => cases h with | ok _ _ _ hsp _ => exact absurd (opStepC_live hsp) hc
    | reject => rfl
    | fail =>
      cases h with
      | fail _ hst _ =>
        have h := hst.metaRight
        unfold Ern.MemoryModel.Arena.MetaRight OptP at h; split at h
        · exact absurd h (SC.dead_not_hasRight hc)
        · exact h.elim
  · cases h with
    | ok hl _ => exact absurd hl hc
    | deadRequester => rfl
    | unknown => rfl

/-! ## Requesters of labelled steps and the non-enabled class (C2, C8, C16, C26; Spec 1 §58) -/

/-- The requesting context of a labelled step (C1: an operation belongs to the ordered sequence
of operations of an execution context). -/
def Label.requester : Label → Nat
  | .kernel c _ | .spawn c _ _ | .terminate c | .join c _ | .deriveSync c _ | .newMutex c _
  | .acquire c _ | .unlock c _ | .resetLock c _ | .spawnVal c _ _ _ | .newArena c _ _
  | .issue c _ _ _ | .reset c _ | .readShared c _ _ _ _ | .writeShared c _ _ _ _
  | .cas c _ _ _ _ _ => c

/-- **Theorem 7** (C2, C8; C28: `complete(c)` follows the last event of the terminated context
`c`): every labelled step is requested by a context that is live in its source state: an `ok` step
satisfies the requester-side precondition of its clause, which a context that is not live fails
(`dead_requests_reject`). Fragment: every state, every registry. -/
theorem lstep_live {ks : KShared} {L : MutexLayout} {lbl : Label}
    {st st' : SC × SyncReg × ArenaReg} (h : LStep ks L lbl st st') : st.1.Live lbl.requester := by
  cases h with
  | kernel h => exact opStepC_live h
  | spawn h => exact spawnStep_live h
  | terminate h => exact termStep_live h
  | join h => exact joinStep_live h
  | deriveSync h => exact deriveSyncStep_live h
  | newMutex h => exact newMutexOk_live h
  | acquire h => exact acquireOk_live h
  | unlock h => exact unlockOk_live h
  | resetLock h => exact resetLockOk_live h
  | spawnVal h => exact spawnValStep_live h
  | newArena h => exact (newArenaStepC_ok h).1
  | issue h =>
    obtain ⟨_, _, _, _, _, hsp, _⟩ := issueStepC_ok h
    exact opStepC_live hsp
  | reset h =>
    obtain ⟨_, _, _, hd, _⟩ := resetStepC_ok (k := ks.toK) h
    exact opStepC_live hd
  | readShared h => exact SC.live_of_exercisable (Guarded.ok_iff.1 h).1.read.exercisable
  | writeShared h => exact SC.live_of_exercisable (Guarded.ok_iff.1 h).1.o11.exercisable
  | @cas _ _ _ _ _ _ _ _ _ br h =>
    obtain (⟨-, h⟩ | ⟨-, h⟩) := h
    · cases h
    · cases br with
      | success v => exact SC.live_of_exercisable (Guarded.ok_iff.1 h).1.o11.exercisable
      | failure v => exact SC.live_of_exercisable (Guarded.ok_iff.1 h).1.read.exercisable

/-- A guarded transition has an outcome (Spec 1 §58). -/
theorem guarded_exists {σ : Type} {P : Prop} {eff : σ} : ∃ o, Guarded P eff o :=
  (Classical.em P).elim (fun h => ⟨_, .ok h⟩) (fun h => ⟨_, .reject h⟩)

/-- Every operation O1–O16 of Spec 1 has an outcome (Spec 1 §58: "Every operation has a conceptual
outcome"). -/
theorem kernelStep_exists (k : K) (op : KernelOp) (t : S3) : ∃ o, op.Step k t o := by
  cases op with
  | alloc pr ow ls =>
    by_cases hst : AllocStatic k t pr ow ls
    · by_cases hs : k.Satisfiable pr ls t
      · exact ⟨_, .ok hst hs⟩
      · exact ⟨_, .fail hst hs⟩
    · exact ⟨_, .reject hst⟩
  | _ => exact guarded_exists

/-- Every inherited operation O1–O16 requested by any context has an outcome (Spec 1 §58, C2). -/
theorem opStepC_exists (k : K) (op : KernelOp) (c : Nat) (s : SC) : ∃ o, opStepC k op c s o := by
  cases op with
  | transfer => exact guarded_exists
  | depend => exact guarded_exists
  | store => exact guarded_exists
  | enter => exact guarded_exists
  | exit => exact guarded_exists
  | _ =>
    obtain ⟨o₃, h⟩ := kernelStep_exists k _ (s.view c)
    exact ⟨_, o₃, h, rfl⟩

/-- **Theorem 7** (Spec 1 §58: "Every operation has a conceptual outcome"; C26: only a legal but
non-enabled request has no successful transition and no `reject`): every request of the machine
other than `join` and `acquire`, by every requester, live or not, has an outcome among `ok`,
`reject` and `fail`: the inherited operations O1–O16 (C2), `spawn` and by-value `spawn` (C4, C5),
`terminate` (C7), `deriveSync` (C15) under every contract `K_C`, `newMutex` (C13, "Outcome"),
`unlock` (C17), `resetLock` (C18), the arena operations (Spec 1 §76–§78), `readShared` (C37), the
concurrent `writeShared` (C39) and the compare-and-exchange (C39, C40). Fragment: every state,
every registry. -/
theorem requests_have_outcome {ks : KShared} {L : MutexLayout} {s : SC} {reg : SyncReg}
    {ar : ArenaReg} {c : Nat} :
    (∀ op, ∃ o, opStepC ks.toK op c s o) ∧
    (∀ ps ls, ∃ o, SpawnStep s c ps ls o) ∧
    (∀ ps ls vs, ∃ o, SpawnValStep ks.toK s c ps ls vs o) ∧
    (∃ o, TermStep ks.toK s c o) ∧
    (∀ (R : Type) (kc : KC R) (r : R) (g : Nat), ∃ o, DeriveSyncStep kc r s c g o) ∧
    (∀ g, ∃ o, NewMutexOutcome ks.toK L ar s reg c g o) ∧
    (∀ i, ∃ o, UnlockOutcome L s reg c i o) ∧
    (∀ i, ∃ o, ResetLockOutcome L s reg c i o) ∧
    (∀ st i, ∃ o, NewArenaStepC s reg ar c st i o) ∧
    (∀ i region dst, ∃ o, IssueStepC ks.toK s ar c i region dst o) ∧
    (∀ i, ∃ o, ResetStepC s ar c i o) ∧
    (∀ a l order, ∃ o, ReadSharedStep ks s c a l order o) ∧
    (∀ a region ord kind, ∃ o, WriteSharedCStep ks s c a region ord kind o) ∧
    (∀ a l succ fail br, ∃ o, CasStep ks s c a l succ fail br o) := by
  refine ⟨fun op => opStepC_exists _ op c s, fun _ _ => guarded_exists,
    fun _ _ _ => guarded_exists, guarded_exists, fun _ _ _ _ => guarded_exists, fun g => ?_,
    fun i => ?_, fun i => ?_, fun _ _ => guarded_exists, fun i region dst => ?_, fun i => ?_,
    fun _ _ _ => guarded_exists, fun _ _ _ _ => guarded_exists, fun a l succ fail br => ?_⟩
  · obtain ⟨hiff, -, hor⟩ := newMutex_outcomes (k := ks.toK) (L := L) (ar := ar) (s := s)
      (reg := reg) (c := c) (g := g)
    rcases hor with h | h
    · obtain ⟨st', h⟩ := hiff.1 h; exact ⟨_, .ok h⟩
    · exact ⟨_, h⟩
  · obtain ⟨hiff, -, hor⟩ := unlock_outcomes (L := L) (s := s) (reg := reg) (c := c) (i := i)
    rcases hor with h | h
    · obtain ⟨st', h⟩ := hiff.1 h; exact ⟨_, .ok h⟩
    · exact ⟨_, h⟩
  · obtain ⟨hiff, -, hor⟩ := resetLock_outcomes (L := L) (s := s) (reg := reg) (c := c) (i := i)
    rcases hor with h | h
    · obtain ⟨st', h⟩ := hiff.1 h; exact ⟨_, .ok h⟩
    · exact ⟨_, h⟩
  · cases hE : ar[i]? with
    | none => exact ⟨_, .noEntry hE⟩
    | some E =>
      by_cases hst : Ern.MemoryModel.Arena.IssueStatic (s.view c) E region dst
      · by_cases hav : Ern.MemoryModel.Arena.Avail E region
        · obtain ⟨o₁, h₁⟩ := opStepC_exists ks.toK (.split E.internal [region]) c s
          cases o₁ with
          | ok s₁ =>
            obtain ⟨o₂, h₂⟩ := opStepC_exists ks.toK (.store s.A.length dst) c s₁
            cases o₂ with
            | ok s₂ => exact ⟨_, .ok hE hst hav h₁ h₂⟩
            | reject => exact ⟨_, .store hE hst hav h₁ h₂⟩
            | fail => cases h₂
          | reject => exact ⟨_, .split hE hst hav h₁⟩
          | fail =>
            obtain ⟨o₃, hR, ho⟩ := h₁
            cases o₃ with
            | ok => cases ho
            | reject => cases ho
            | fail => cases hR
        · exact ⟨_, .fail hE hst hav⟩
      · exact ⟨_, .static hE hst⟩
  · have : ∃ o₃, Ern.MemoryModel.Arena.ResetD i ⟨s.view c, ar⟩ o₃ := by
      cases hE : ar[i]? with
      | none => exact ⟨_, .noEntry hE⟩
      | some E =>
        obtain ⟨o₁, h₁⟩ := guarded_exists (P := DerivePre (s.view c) E.internal
          (footprint (s.view c).P E.storage) .modify)
          (eff := deriveEff (s.view c) E.internal (footprint (s.view c).P E.storage) .modify)
        cases o₁ with
        | ok s₁ =>
          obtain ⟨o₂, h₂⟩ := kernelStep_exists ks.toK (.release (s.view c).A.length) s₁
          cases o₂ with
          | ok s₂ =>
            by_cases hn : Ern.MemoryModel.Arena.ResetNoDeps (s.view c) E
            · exact ⟨_, .ok hE h₁ h₂ hn⟩
            · exact ⟨_, .contract hE h₁ h₂ hn⟩
          | reject => exact ⟨_, .release hE h₁ h₂⟩
          | fail => cases h₂
        | reject => exact ⟨_, .derive hE h₁⟩
        | fail => cases h₁
    obtain ⟨o₃, h⟩ := this
    exact ⟨_, o₃, h, rfl⟩
  · by_cases ho : CasOrdersOK succ fail
    · cases br with
      | success v =>
        obtain ⟨o, h⟩ := guarded_exists (P := WriteSharedCPre ks s c a [l] (some succ) (.rmw v))
          (eff := writeSharedCEff s c [l])
        exact ⟨o, .inr ⟨ho, h⟩⟩
      | failure v =>
        obtain ⟨o, h⟩ := guarded_exists (P := ReadSharedPre ks s c a l fail) (eff := s)
        exact ⟨o, .inr ⟨ho, h⟩⟩
    · exact ⟨_, .inl ⟨ho, rfl⟩⟩

/-- **Theorem 7** (C8, C16, C26: "A legal but non-enabled request has no successful abstract
transition; an illegal request has the specified `reject` outcome"): the class "legal and not
activable" is inhabited only by a live requester, and only for `join` and `acquire`: for these two
operations it is exactly the absence of an outcome, and every other request has an outcome
(`requests_have_outcome`). Fragment: every state, every registry. -/
theorem notEnabled_live {ks : KShared} {L : MutexLayout} {s : SC} {reg : SyncReg} {c d i : Nat} :
    (JoinNotEnabled s c d → s.Live c) ∧ (AcquireNotEnabled L s reg c i → s.Live c) ∧
    ((¬ ∃ o, JoinStep s c d o) ↔ JoinNotEnabled s c d) ∧
    ((¬ ∃ o, AcquireOutcome ks L s reg c i o) ↔ AcquireNotEnabled L s reg c i) := by
  obtain ⟨hjc, hjr, hjo, hjn, -, -⟩ := join_classes (s := s) (c := c) (d := d)
  obtain ⟨hac, hao, han, -⟩ := acquire_classes (ks := ks) (L := L) (s := s) (reg := reg)
    (ar := []) (c := c) (i := i)
  refine ⟨fun h => h.1, fun h => Decidable.byContradiction fun hl =>
    (acquire_dead_reject hl).2 h.1, ⟨fun hno => ?_, fun h ⟨o, ho⟩ => hjn h o ho⟩,
    ⟨fun hno => ?_, fun h ⟨o, ho⟩ => (han h).1 o ho⟩⟩
  · rcases hjc with ⟨hr, -, -⟩ | ⟨-, hn, -⟩ | ⟨-, -, hk⟩
    · exact absurd ⟨_, hjr.2 hr⟩ hno
    · exact hn
    · exact absurd ⟨_, hjo hk⟩ hno
  · rcases hac with ⟨hr, -, -⟩ | ⟨-, hn, -⟩ | ⟨-, -, hk⟩
    · exact absurd ⟨_, .reject hr⟩ hno
    · exact hn
    · obtain ⟨st', h⟩ := hao.1 hk; exact absurd ⟨_, .ok h⟩ hno

end Ern.ConcurrencyModel
