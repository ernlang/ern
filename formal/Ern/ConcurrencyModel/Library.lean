import Ern.ConcurrencyModel.DeriveSync
import Ern.ConcurrencyModel.Atomic
import Ern.MemoryModel.Arena

/-!
# Reference synchronization library

Library state separate from `S_C` (C2, C12), on the pattern of `Ern.MemoryModel.Arena` (Spec
1 §46, §55, §56):

* the registry of `SyncEntry { guarded, grant }` (C12), liveness of an entry, the positional
  `ControlOf` relationship (C12) for declared field positions `MutexLayout`;
* `SyncInv` (C21.1–C21.7) and `GrantDiscipline` (C22);
* the library instantiation of `K_C.SyncAuthorized` on the registry (C14.1–C14.3), and the
  contract obligation `SyncSound` of C14;
* derived operations `newMutex` (C13), `acquire` (C16), `unlock` (C17), `resetLock` (C18);
* the arena registry of Spec 1 §46 beside the synchronization registry (C2, C19), and the
  derived arena operations O17–O19 of `Ern.MemoryModel.Arena` (Spec 1 §76–§78, Part XIV) executed
  by a context: `newArena`, `issue` (`split` then `store`, both as executed by the context,
  C2), `reset` (`derive` then `release` on the view of the context); the guard of Spec 1 §56
  (§76.4, C13.7) of `newArena` and `newMutex` reads both registries;
* labelled steps, the by-value composite and the atomic cases included (C23, C39), runs, and the
  trace assumption of C23 (`RestrictedTrace`: C22.1–C22.3, C22.5), a predicate on runs, never a
  precondition of a kernel operation.
-/

namespace Ern.ConcurrencyModel

open Ern.MemoryModel Ern.MemoryModel.Access

/-! ## Registry (C12) -/

/-- Synchronization entry (C12): the protected authority `guarded` and the recorded grant. -/
structure SyncEntry where
  guarded : Nat
  grant : Option Nat
deriving DecidableEq, Repr

/-- Synchronization registry (C12), library state separate from `S_C`. -/
abbrev SyncReg := List SyncEntry

/-- Declared field positions of the reference mutex value (C12, `guardedField`, `controlField`): the
position of the field holding `guarded` and that of the controller, among the ordered children of
the mutex value. -/
structure MutexLayout where
  guardedField : Nat
  controlField : Nat
deriving DecidableEq, Repr

/-- An entry is live exactly while `guarded` is active (C12). -/
def SyncEntry.Live (s : SC) (e : SyncEntry) : Prop := s.flat.Active e.guarded

/-- Decidability of liveness of an entry (C12). -/
instance (s : SC) (e : SyncEntry) : Decidable (e.Live s) := by
  unfold SyncEntry.Live; infer_instance

/-- Positional `ControlOf` (C12): `guarded` is held by the field `h` at position
`guardedField` of the mutex value `m` (the structural parent of `h`); the controller is the child
of `m` at position `controlField`. -/
def ControlOf (L : MutexLayout) (s : SC) (e : SyncEntry) : Option Nat :=
  match (s.A[e.guarded]?).map (·.holder) with
  | some (Holder.place h) =>
    match parentOf s.P h with
    | some m =>
      if (kids s.P m)[L.guardedField]? = some h then (kids s.P m)[L.controlField]? else none
    | none => none
  | _ => none

/-- The `S3` whose current frame is `f` (C14: `SyncAuthorized` names the requesting frame;
Spec 1 §43 reads the stack only through its top and membership). -/
def SC.viewAt (s : SC) (f : Nat) : S3 :=
  { s.flat with F := f :: s.frames.filter fun g => decide (g ≠ f) }

/-- C14.3: the frame `f` has effective and exercisable access to `ControlOf(e)` under the
condition of Spec 1 §68.2: some authority exercisable by `f` in a mode at least `Observe` has a
present effective mode on the controller. -/
def CtrlRight (L : MutexLayout) (s : SC) (e : SyncEntry) (f : Nat) : Prop :=
  OptP (ControlOf L s e) (fun ctl => ∃ a ∈ List.range s.A.length,
    (s.viewAt f).ExercisableAt a .observe ∧ effective s.flat a ctl ≠ none) False

/-- Decidability of the controller fact. -/
instance (L : MutexLayout) (s : SC) (e : SyncEntry) (f : Nat) : Decidable (CtrlRight L s e f) := by
  unfold CtrlRight; infer_instance

/-- C2, C14.3: a context that is not live has no current frame, hence no controller-access
right. -/
theorem SC.dead_not_ctrlRight {L : MutexLayout} {s : SC} {e : SyncEntry} {c : Nat}
    (h : ¬ s.Live c) : ¬ CtrlRight L s e (s.view c).top := by
  rw [SC.view_top_dead h]
  unfold CtrlRight
  cases ControlOf L s e with
  | none => exact id
  | some ctl =>
    rintro ⟨a, -, hx, -⟩
    have ht : (s.viewAt s.noFrame).top = s.noFrame := by simp [SC.viewAt, S3.top]
    exact not_exercisable_of_top (fun _ _ hy => by rw [ht]; exact SC.noFrame_holder hy) hx

/-- The authorization facts of C14 for an entry: C14.1 (live), C14.2 (`grant = none`), C14.3
(`CtrlRight`). -/
def EntryAuth (L : MutexLayout) (s : SC) (e : SyncEntry) (f : Nat) : Prop :=
  e.Live s ∧ e.grant = none ∧ CtrlRight L s e f

/-- Decidability of the library authorization of an entry. -/
instance (L : MutexLayout) (s : SC) (e : SyncEntry) (f : Nat) : Decidable (EntryAuth L s e f) := by
  unfold EntryAuth; infer_instance

/-- Instantiation of `K_C.SyncAuthorized(state, sync_registry, guarded, requesting_frame)` by the
library (C14, C25): an entry of the registry with the requested `guarded` identity satisfies
the authorization facts C14.1–C14.3. -/
def LibSyncAuthorized (L : MutexLayout) (reg : SyncReg) (s : SC) (g f : Nat) : Prop :=
  ∃ e ∈ reg, e.guarded = g ∧ EntryAuth L s e f

/-- Decidability of the library instantiation. -/
instance (L : MutexLayout) (reg : SyncReg) (s : SC) (g f : Nat) :
    Decidable (LibSyncAuthorized L reg s g f) := by
  unfold LibSyncAuthorized; infer_instance

/-- C2, C14.3: the library instantiation of `SyncAuthorized` never holds for the current frame of
a context that is not live (it has no controller-access right). -/
theorem SC.dead_not_libSyncAuthorized {L : MutexLayout} {reg : SyncReg} {s : SC} {g c : Nat}
    (h : ¬ s.Live c) : ¬ LibSyncAuthorized L reg s g (s.view c).top :=
  fun ⟨_, _, _, _, _, hcr⟩ => SC.dead_not_ctrlRight h hcr

/-- The contract `K_C` instantiated by the library (C14, C25), the registry type being
`SyncReg` (C2). -/
def libKC (ks : KShared) (L : MutexLayout) : KC SyncReg :=
  { ks with SyncAuthorized := LibSyncAuthorized L }

/-- Decidability of the instantiated predicate. -/
instance (ks : KShared) (L : MutexLayout) (reg : SyncReg) (s : SC) (g f : Nat) :
    Decidable ((libKC ks L).SyncAuthorized reg s g f) :=
  inferInstanceAs (Decidable (LibSyncAuthorized L reg s g f))

/-- Contract obligation of C14, in state `s` with registry `reg`: `SyncAuthorized` holds only for
the `guarded` of a live entry of `reg`. -/
def SyncSound (kc : KC SyncReg) (reg : SyncReg) (s : SC) : Prop :=
  ∀ g f, kc.SyncAuthorized reg s g f → ∃ e ∈ reg, e.guarded = g ∧ e.Live s

/-- The library instantiation satisfies the obligation of C14. -/
theorem libKC_sound (ks : KShared) (L : MutexLayout) (reg : SyncReg) (s : SC) :
    SyncSound (libKC ks L) reg s :=
  fun _ _ ⟨e, he, hg, hl, _⟩ => ⟨e, he, hg, hl⟩

/-- The holder is a usable place (C12, C13.1, C21.1). -/
def PlaceUsable (t : S3) : Holder → Prop
  | .place q => t.Usable q
  | .frame _ => False

/-- Decidability of `PlaceUsable` (C12). -/
instance (t : S3) (h : Holder) : Decidable (PlaceUsable t h) := by
  cases h <;> unfold PlaceUsable <;> infer_instance

/-- Spec 1 §65.3 for an authority held by a place `q`: it covers neither a leaf of `q` nor a leaf
of storage transitively owned by `q` (C13.5). -/
def StoredOK (P : List Place) (y : Authority) : Prop :=
  match y.holder with
  | .place q => ∀ l ∈ y.footprint, l ∉ footprint P q ∧
      ∀ r ∈ List.range P.length, OwnedIn P q r → l ∉ footprint P r
  | .frame _ => True

/-- Decidability of `StoredOK` (Spec 1 §65.3). -/
instance (P : List Place) (y : Authority) : Decidable (StoredOK P y) := by
  unfold StoredOK; split <;> infer_instance

/-- The place `slot` holding `guarded` (C12). -/
def slotOf (s : SC) (g : Nat) : Option Nat :=
  match (s.A[g]?).map (·.holder) with
  | some (Holder.place h) => some h
  | _ => none

/-! ## Arena registry and the registries of live administrations (Spec 1 §46, §56) -/

/-- The arena registry (Spec 1 §46): library state separate from the kernel state and from the
synchronization registry (C2: library administration states remain separate from `S_C`). -/
abbrev ArenaReg := List Arena.ArenaEntry

/-- The synchronization registry as a registry of live administrations (Spec 1 §56; C13.7):
the `guarded` identities of its live entries. -/
def liveGuardeds (s : SC) (reg : SyncReg) : List Nat :=
  (reg.filter fun e => decide (e.Live s)).map (·.guarded)

/-- Separation of the two registries of live administrations (Spec 1 §56; C13.7, OB-C16): no
identity is at once the `guarded` of a live synchronization entry and the `internal` of a live
arena. -/
def AdminSep (s : SC) (reg : SyncReg) (ar : ArenaReg) : Prop :=
  ∀ e ∈ reg, ∀ E ∈ ar, e.Live s → Arena.Live s.flat E → e.guarded ≠ E.internal

/-! ## Invariants (C21, C22) -/

/-- Active descendant of `guarded` covering a protected leaf, a leaf of `footprint(guarded)`
(C13.9, C18.2, C21.5, C22). -/
def CoveringDesc (s : SC) (g j : Nat) : Prop :=
  g ∈ s.flat.ancs j ∧ s.flat.Active j ∧ ∃ l ∈ s.flat.afp j, l ∈ s.flat.afp g

/-- Decidability of `CoveringDesc` (C22). -/
instance (s : SC) (g j : Nat) : Decidable (CoveringDesc s g j) := by
  unfold CoveringDesc; infer_instance

/-- No active descendant of `guarded` covers a protected leaf (C13.9, C18.2, C22). -/
def NoCoveringDesc (s : SC) (g : Nat) : Prop := ∀ j ∈ List.range s.A.length, ¬ CoveringDesc s g j

/-- Decidability of `NoCoveringDesc` (C22). -/
instance (s : SC) (g : Nat) : Decidable (NoCoveringDesc s g) := by
  unfold NoCoveringDesc; infer_instance

/-- `GrantDiscipline` (C22). -/
def GrantDiscipline (s : SC) (reg : SyncReg) : Prop :=
  ∀ e ∈ reg, e.Live s → e.grant = none → NoCoveringDesc s e.guarded

/-- C21.4, first clause: distinct live entries (by position in the registry) have distinct
`ControlOf` leaves. -/
def CtlUnique (L : MutexLayout) (s : SC) (reg : SyncReg) : Prop :=
  ∀ (i j : Nat) (e e' : SyncEntry) (ctl : Nat), reg[i]? = some e → reg[j]? = some e' →
    e.Live s → e'.Live s → ControlOf L s e = some ctl → ControlOf L s e' = some ctl → i = j

/-- C21.7, initialization invariant for `slot`: for every live entry, every structural leaf of
the place holding `guarded` is `Init`. -/
def SlotInit (s : SC) (reg : SyncReg) : Prop :=
  ∀ e ∈ reg, e.Live s →
    OptP (slotOf s e.guarded) (fun q => ∀ l ∈ footprint s.P q, s.I l = .init) False

/-- C21.7, initialization invariant for `ctl`: for every live entry, the controller leaf
`ControlOf(entry)` is `Init`. -/
def CtlInit (L : MutexLayout) (s : SC) (reg : SyncReg) : Prop :=
  ∀ e ∈ reg, e.Live s → OptP (ControlOf L s e) (fun ctl => s.I ctl = .init) False

/-- `SyncInv` (C21.1–C21.7): items 1–5 and 7 over live entries, item 6 over every entry. Item 4
respects the guarded-identity uniqueness guard of C13.7, which concerns every registry of live
administrations (Spec 1 §56): the arena registry `ar` is therefore an argument. -/
structure SyncInv (L : MutexLayout) (s : SC) (reg : SyncReg) (ar : ArenaReg) : Prop where
  /-- C21.1: `guarded` is active (liveness), has own mode `Modify`, and is held by a usable
  place. -/
  guarded : ∀ e ∈ reg, e.Live s → OptP (s.A[e.guarded]?) (fun y => y.mode = .modify ∧
    PlaceUsable s.flat y.holder) False
  /-- C21.2: a recorded grant exists, has origin `guarded` and footprint
  `footprint(guarded)`. -/
  grant : ∀ e ∈ reg, e.Live s → ∀ g, e.grant = some g → OptP (s.A[g]?) (fun y =>
    y.origin = some e.guarded ∧ ∀ l, l ∈ y.footprint ↔ l ∈ s.flat.afp e.guarded) False
  /-- C21.3, with the positional `ControlOf` of C12: the controller exists and is a usable
  leaf. -/
  control : ∀ e ∈ reg, e.Live s → OptP (ControlOf L s e) (fun ctl =>
    s.flat.Usable ctl ∧ isLeaf s.P ctl) False
  /-- C21.4, first clause: controller uniqueness among live entries. -/
  ctlUnique : CtlUnique L s reg
  /-- C21.4, second clause (the guarded-identity uniqueness guard of C13.7): distinct
  live entries have distinct `guarded` identities. -/
  unique : ∀ (i j : Nat) (e e' : SyncEntry), reg[i]? = some e → reg[j]? = some e' →
    e.Live s → e'.Live s →
    e.guarded = e'.guarded → i = j
  /-- C21.4, second clause, across registries (C13.7, Spec 1 §56): no live entry's `guarded`
  is the `internal` identity of a live arena. -/
  adminGuard : AdminSep s reg ar
  /-- C21.5, `GrantSubtree`. -/
  grantSubtree : ∀ e ∈ reg, e.Live s → ∀ g, e.grant = some g → s.flat.Active g →
    ∀ j, CoveringDesc s e.guarded j → j = g ∨ g ∈ s.flat.ancs j
  /-- C21.6, `RegBound`, over every entry: the registered `guarded` identity exists (Spec 1
  §38: identities are indices). -/
  regBound : ∀ e ∈ reg, e.guarded < s.A.length
  /-- C21.7: the structural leaves of `slot` are `Init`. -/
  slotInit : SlotInit s reg
  /-- C21.7: the controller leaf is `Init`. -/
  ctlInit : CtlInit L s reg

/-! ## Derived operations (C13, C16–C18) -/

/-- The mutex value `M` of C12, C13: the immediate structural parent of the place `slot`
holding `guarded`. -/
def mutexOf (s : SC) (g : Nat) : Option Nat :=
  match (s.A[g]?).map (·.holder) with
  | some (Holder.place h) => parentOf s.P h
  | _ => none

/-- Preconditions of `newMutex(guarded)` executed by `c` (C13.1–C13.11), the arena registry
`ar` being the other registry of live administrations (Spec 1 §56). The interface and realization
obligations of C13 (C13, paragraph on these obligations) are not represented: those attached to
C13.3 and C13.6, and the one on the initial physical controller state. The items C13.3 and C13.6
themselves enter only as the preconditions `control` and `sharedMutable`. -/
structure NewMutexPre (k : K) (L : MutexLayout) (ar : ArenaReg) (s : SC) (reg : SyncReg)
    (c g : Nat) : Prop where
  /-- C13.1: `guarded` is active, of own mode `Modify`, and held by a usable place. -/
  guarded : OptP (s.A[g]?) (fun y => y.active = true ∧ y.mode = .modify ∧
    PlaceUsable s.flat y.holder) False
  /-- C13.2: ordinary exercisable `Modify` over `guarded` (Spec 1 §43). -/
  exercisable : (s.view c).ExercisableAt g .modify
  /-- C13.3, with the positional `ControlOf` of C12: the controller exists and is a
  usable leaf. -/
  control : OptP (ControlOf L s ⟨g, none⟩) (fun ctl => s.flat.Usable ctl ∧ isLeaf s.P ctl) False
  /-- C13.4: `footprint(guarded) ∩ footprint(M) = ∅`. -/
  disjointM : OptP (mutexOf s g) (fun m => ∀ l ∈ s.flat.afp g, l ∉ footprint s.P m) False
  /-- C13.10: every structural leaf of `footprint(M)` is `Init`. -/
  initM : OptP (mutexOf s g) (fun m => ∀ l ∈ footprint s.P m, s.I l = .init) False
  /-- C13.5: when `guarded` is stored (derived), Spec 1 §65.3 holds: it covers neither a leaf
  of its holder nor a leaf of storage transitively owned by it. -/
  stored : OptP (s.A[g]?) (fun y => y.origin ≠ none → StoredOK s.P y) False
  /-- C13.6: `K.SharedMutable(ctl)`. -/
  sharedMutable : OptP (ControlOf L s ⟨g, none⟩) k.SharedMutable False
  /-- C13.7, Spec 1 §56: `guarded` is not the identity of another live entry. -/
  unique : ∀ e ∈ reg, e.Live s → e.guarded ≠ g
  /-- C13.7, Spec 1 §56: `guarded` is not the `internal` identity of a live arena of the
  arena registry. -/
  otherAdmin : g ∉ Arena.liveInternals s.flat ar
  /-- C13.8: no other live entry is associated with `ctl`. -/
  ctlUnique : OptP (ControlOf L s ⟨g, none⟩) (fun ctl => ∀ e ∈ reg, e.Live s →
    ControlOf L s e ≠ some ctl) False
  /-- C13.9. -/
  available : NoCoveringDesc s g
  /-- C13.11: the constructing frame has ordinary exercisable `Modify` authority with effective
  mode `Modify` over the controller leaf (Spec 1 §43, O10.1 §67.1), and the ordinary-write
  exclusivity of O10.2 (§67.2) applies to it: no other authority has an effective mode on the
  controller leaf. A right sufficient only for an `Observe`-mode shared mutation (§68.2) does not
  satisfy it. -/
  ctlRight : OptP (ControlOf L s ⟨g, none⟩) (fun ctl => ∃ a ∈ List.range s.A.length,
    (s.view c).ExercisableAt a .modify ∧ effective (s.view c) a ctl = some .modify ∧
    ∀ b ∈ List.range s.A.length, b ≠ a → effective (s.view c) b ctl = none) False

/-- Decidability of the preconditions of `newMutex` (C13). -/
instance (k : K) [DecidablePred k.SharedMutable] (L : MutexLayout) (ar : ArenaReg) (s : SC)
    (reg : SyncReg) (c g : Nat) : Decidable (NewMutexPre k L ar s reg c g) :=
  decidable_of_iff (OptP (s.A[g]?) (fun y => y.active = true ∧ y.mode = .modify ∧
      PlaceUsable s.flat y.holder) False ∧
    (s.view c).ExercisableAt g .modify ∧
    OptP (ControlOf L s ⟨g, none⟩) (fun ctl => s.flat.Usable ctl ∧ isLeaf s.P ctl) False ∧
    OptP (mutexOf s g) (fun m => ∀ l ∈ s.flat.afp g, l ∉ footprint s.P m) False ∧
    OptP (mutexOf s g) (fun m => ∀ l ∈ footprint s.P m, s.I l = .init) False ∧
    OptP (s.A[g]?) (fun y => y.origin ≠ none → StoredOK s.P y) False ∧
    OptP (ControlOf L s ⟨g, none⟩) k.SharedMutable False ∧
    (∀ e ∈ reg, e.Live s → e.guarded ≠ g) ∧ g ∉ Arena.liveInternals s.flat ar ∧
    OptP (ControlOf L s ⟨g, none⟩) (fun ctl => ∀ e ∈ reg, e.Live s →
      ControlOf L s e ≠ some ctl) False ∧
    NoCoveringDesc s g ∧
    OptP (ControlOf L s ⟨g, none⟩) (fun ctl => ∃ a ∈ List.range s.A.length,
      (s.view c).ExercisableAt a .modify ∧ effective (s.view c) a ctl = some .modify ∧
      ∀ b ∈ List.range s.A.length, b ≠ a → effective (s.view c) b ctl = none) False)
    ⟨fun ⟨a, b, c, d, e, f, h, i, j, l, m, n⟩ => ⟨a, b, c, d, e, f, h, i, j, l, m, n⟩,
     fun ⟨a, b, c, d, e, f, h, i, j, l, m, n⟩ => ⟨a, b, c, d, e, f, h, i, j, l, m, n⟩⟩

/-- The `ok` outcome of `newMutex(guarded)` executed by `c` (C13, outcome paragraph): registers the
entry `⟨guarded, none⟩`; the kernel state is unchanged and no authority is created (C13 effect). The
`reject` outcome is `NewMutexOutcome.reject`. -/
def NewMutexOk (k : K) (L : MutexLayout) (ar : ArenaReg) (s : SC) (reg : SyncReg) (c g : Nat)
    (st' : SC × SyncReg) : Prop :=
  NewMutexPre k L ar s reg c g ∧ st' = (s, reg ++ [⟨g, none⟩])

/-- `acquire` on entry `i` executed by `c` (C16): with the library instantiation of
`SyncAuthorized` for the entry, `deriveSync(guarded)` on the registry `reg` and the record of the
fresh grant identity `|A|` in the entry (C16 success, items 1–3). The outcome classes of C16
(`reject`, non-enabled, `ok`) are defined with the outcome theorems. -/
def AcquireOk (ks : KShared) (L : MutexLayout) (s : SC) (reg : SyncReg) (c i : Nat)
    (st' : SC × SyncReg) : Prop :=
  ∃ e, reg[i]? = some e ∧ EntryAuth L s e (s.view c).top ∧
    DeriveSyncPre (libKC ks L) reg s c e.guarded ∧
    st' = (deriveSyncEff s c e.guarded, reg.set i { e with grant := some s.A.length })

/-- `prospectiveUnlock s c g`: the prospective authority state of C17.4, obtained from `s` by
legally releasing the recorded grant `g` under O3 (Spec 1 §62 `ok` effect) on the view of the
executing context `c`; the registry is not an argument. It is evaluated solely for checking C17.4
and is committed only when `unlock` succeeds (C17.4). -/
abbrev prospectiveUnlock (s : SC) (c g : Nat) : SC := s.set (releaseEff (s.view c) g)

/-- `unlock` of entry `i` executed by `c` (C17.1–C17.4): O3 releases the grant and the registry
records `grant = none` (C17 effect). C17.2 and C17.3 are the preconditions of O3 (Spec 1 §62);
C17.4 is `CtrlRight` in the state before `unlock` and in the prospective state
`prospectiveUnlock`. The controller update is a realization obligation (C17), not a
precondition. The outcome classes of C17 are defined with the outcome theorems. -/
def UnlockOk (L : MutexLayout) (s : SC) (reg : SyncReg) (c i : Nat) (st' : SC × SyncReg) :
    Prop :=
  ∃ e g, reg[i]? = some e ∧ e.Live s ∧ e.grant = some g ∧ ReleasePre (s.view c) g ∧
    CtrlRight L s e (s.view c).top ∧ CtrlRight L (prospectiveUnlock s c g) e (s.view c).top ∧
    st' = (prospectiveUnlock s c g, reg.set i { e with grant := none })

/-- `resetLock` of entry `i` executed by `c` (C18.1–C18.4): the entry becomes available; the
kernel state is unchanged (C18 effect), so recovery invalidates no surviving dependent authority
(C18.3) and fabricates none (C18 effect). No prerequisite that the recorded grant be `none` (C18).
C18.3: `ControlOf(entry)` is defined and is a usable leaf (C21.3); the controller-initialization
invariant is not a precondition (C18.3, C21.7). C18.4 is `CtrlRight`. The outcome classes of C18 are
defined with the outcome theorems. -/
def ResetLockOk (L : MutexLayout) (s : SC) (reg : SyncReg) (c i : Nat) (st' : SC × SyncReg) :
    Prop :=
  ∃ e, reg[i]? = some e ∧ (s.view c).ExercisableAt e.guarded .modify ∧
    NoCoveringDesc s e.guarded ∧
    OptP (ControlOf L s e) (fun ctl => s.flat.Usable ctl ∧ isLeaf s.P ctl) False ∧
    CtrlRight L s e (s.view c).top ∧
    st' = (s, reg.set i { e with grant := none })

/-- An `ok` `newMutex` requires the constructing context to be live (C13.2, C2). -/
theorem newMutexOk_live {k : K} {L : MutexLayout} {ar : ArenaReg} {s : SC} {reg : SyncReg}
    {c g : Nat} {st' : SC × SyncReg} (h : NewMutexOk k L ar s reg c g st') : s.Live c :=
  SC.live_of_exercisable h.1.exercisable

/-- An `ok` `acquire` requires the requesting context to be live (C15.6 within C16, C2). -/
theorem acquireOk_live {ks : KShared} {L : MutexLayout} {s : SC} {reg : SyncReg} {c i : Nat}
    {st' : SC × SyncReg} (h : AcquireOk ks L s reg c i st') : s.Live c := by
  obtain ⟨e, -, -, hp, -⟩ := h
  exact SC.live_of_top_mem hp.frameLive

/-- An `ok` `unlock` requires the acting context to be live (C17.2: O3, Spec 1 §62.2; C2). -/
theorem unlockOk_live {L : MutexLayout} {s : SC} {reg : SyncReg} {c i : Nat}
    {st' : SC × SyncReg} (h : UnlockOk L s reg c i st') : s.Live c := by
  obtain ⟨e, g, -, -, -, hr, -⟩ := h
  have hh := hr.holderRight
  unfold OptP at hh; split at hh
  · rename_i y hy; exact SC.live_of_holderRight hy hh
  · exact hh.elim

/-- An `ok` `resetLock` requires the acting context to be live (C18.1, C2). -/
theorem resetLockOk_live {L : MutexLayout} {s : SC} {reg : SyncReg} {c i : Nat}
    {st' : SC × SyncReg} (h : ResetLockOk L s reg c i st') : s.Live c := by
  obtain ⟨e, -, hx, -⟩ := h
  exact SC.live_of_exercisable hx

/-! ## Derived arena operations executed by a context (Spec 1 §76–§78; C2, C19) -/

/-- Preconditions of `newArena(storage, internal)` executed by `c` (Spec 1 §76; C2): the
clauses of `Arena.NewArenaBase` on the view of `c`, §76.6 being read on the concurrent kernel state
(C2, C3, C20: `WF3` and `I1` over the globally live frames, `AnchorOrder` and
`AnchorOrderHeld` on `ancestorC`), and the guard of §76.4 over the arena registry and the
synchronization registry (Spec 1 §56; C13.7, OB-C16), with `Arena.Guard56`. -/
structure NewArenaPreC (s : SC) (reg : SyncReg) (ar : ArenaReg) (c storage internal : Nat) :
    Prop where
  /-- Spec 1 §76.1: `storage` is an existing, usable place. -/
  storageUsable : (s.view c).Usable storage
  /-- Spec 1 §76.1: `storage` is under exercisable `Modify` by the current frame. -/
  storageRight : HasRight (s.view c) .modify storage
  /-- Spec 1 §76.2: `internal` exists, is active and has own mode `Modify`. -/
  internalAuth : OptP (s.A[internal]?) (fun y => y.active = true ∧ y.mode = .modify) False
  /-- Spec 1 §76.2: `ExercisableAt(s, internal, Modify)`. -/
  exercisable : (s.view c).ExercisableAt internal .modify
  /-- Spec 1 §76.3: `internal` is held by a place, the arena value. -/
  heldByPlace : OptP (s.A[internal]?) (fun y => y.holder.isPlace = true) False
  /-- Spec 1 §76.3: `footprint(internal) ⊆ footprint(storage)`. -/
  fpSub : ∀ l ∈ s.flat.afp internal, l ∈ footprint s.P storage
  /-- Spec 1 §76.3: `footprint(storage) ⊆ footprint(internal)`. -/
  fpSup : ∀ l ∈ footprint s.P storage, l ∈ s.flat.afp internal
  /-- Spec 1 §76.5: all leaves of the arena value are already `Init`. -/
  valueInit : OptP (s.A[internal]?) (fun y => Arena.LeavesInit s.flat y.holder) True
  /-- Spec 1 §76.6: `WF3` (§49) over the whole kernel state, the globally live frames (C2). -/
  wf3 : WF3 s.flat
  /-- Spec 1 §76.6: `I1` (§50) over the whole kernel state (C2). -/
  i1 : I1 s.flat
  /-- Spec 1 §76.6 re-indexed (C3): `AnchorOrder` (§44) on `ancestorC`. -/
  anchorOrder : AnchorOrderC s
  /-- Spec 1 §76.6 re-indexed (C3): `AnchorOrderHeld` (§44) on `ancestorC`. -/
  anchorOrderHeld : AnchorOrderHeldC s
  /-- Spec 1 §76.6: the new entry satisfies `ArenaInv` (§55). -/
  arenaInv : Arena.ArenaInv s.flat ⟨storage, internal, footprint s.P storage, []⟩
  /-- Spec 1 §76.4, §56 (C13.7, OB-C16): no live administration of the arena registry nor of
  the synchronization registry uses `internal`. -/
  guard : Arena.Guard56 [Arena.liveInternals s.flat ar, liveGuardeds s reg] internal

/-- Decidability of the preconditions of `newArena` executed by `c` (Spec 1 §76). -/
instance (s : SC) (reg : SyncReg) (ar : ArenaReg) (c storage internal : Nat) :
    Decidable (NewArenaPreC s reg ar c storage internal) :=
  decidable_of_iff ((s.view c).Usable storage ∧ HasRight (s.view c) .modify storage ∧
    OptP (s.A[internal]?) (fun y => y.active = true ∧ y.mode = .modify) False ∧
    (s.view c).ExercisableAt internal .modify ∧
    OptP (s.A[internal]?) (fun y => y.holder.isPlace = true) False ∧
    (∀ l ∈ s.flat.afp internal, l ∈ footprint s.P storage) ∧
    (∀ l ∈ footprint s.P storage, l ∈ s.flat.afp internal) ∧
    OptP (s.A[internal]?) (fun y => Arena.LeavesInit s.flat y.holder) True ∧
    WF3 s.flat ∧ I1 s.flat ∧ AnchorOrderC s ∧ AnchorOrderHeldC s ∧
    Arena.ArenaInv s.flat ⟨storage, internal, footprint s.P storage, []⟩ ∧
    Arena.Guard56 [Arena.liveInternals s.flat ar, liveGuardeds s reg] internal)
    ⟨fun ⟨a, b, c, d, e, f, g, h, i, j, l, m, n, o⟩ => ⟨a, b, c, d, e, f, g, h, i, j, l, m, n, o⟩,
     fun ⟨a, b, c, d, e, f, g, h, i, j, l, m, n, o⟩ => ⟨a, b, c, d, e, f, g, h, i, j, l, m, n, o⟩⟩

/-- `newArena(storage, internal)` executed by `c` (Spec 1 §76, §58: `ok` or `reject`): the entry of
`Arena.newArenaEff` is registered; the kernel state and the synchronization registry are
unchanged (§76 `ok` effect). A context that is not live has no current frame (C2): §76.1 fails,
`reject`. -/
def NewArenaStepC (s : SC) (reg : SyncReg) (ar : ArenaReg) (c storage internal : Nat)
    (o : Outcome3 (SC × ArenaReg)) : Prop :=
  Guarded (NewArenaPreC s reg ar c storage internal)
    (s, ar ++ [⟨storage, internal, footprint s.P storage, []⟩]) o

/-- `issue(arena, region, destination)` of entry `i` executed by `c` (Spec 1 §77, §58; Part XIV: a
derived operation, on the pattern of `Arena.IssueD`): the static checks (§77.1, §77.2) and the
availability `fail` (§77.4) on the view of `c`; then `split` of `internal` on the region (O2) and
`store` of the block, of fresh identity `|A|`, into the destination (O8), both as executed by `c`
(`opStepC`; C2, C3: §65.4 and §65.5 read `ancestorC`); the metadata is updated on `ok`
(`Arena.issueMeta`). A context that is not live has no current frame (C2): §77.1 fails, `reject`. -/
inductive IssueStepC (k : K) (s : SC) (ar : ArenaReg) (c i : Nat) (region : List Nat)
    (dst : Nat) : Outcome3 (SC × ArenaReg) → Prop where
  | noEntry : ar[i]? = none → IssueStepC k s ar c i region dst .reject
  | static {E : Arena.ArenaEntry} : ar[i]? = some E →
      ¬ Arena.IssueStatic (s.view c) E region dst → IssueStepC k s ar c i region dst .reject
  | fail {E : Arena.ArenaEntry} : ar[i]? = some E →
      Arena.IssueStatic (s.view c) E region dst → ¬ Arena.Avail E region →
      IssueStepC k s ar c i region dst .fail
  | split {E : Arena.ArenaEntry} : ar[i]? = some E → Arena.IssueStatic (s.view c) E region dst →
      Arena.Avail E region → opStepC k (.split E.internal [region]) c s .reject →
      IssueStepC k s ar c i region dst .reject
  | store {E : Arena.ArenaEntry} {s₁ : SC} : ar[i]? = some E →
      Arena.IssueStatic (s.view c) E region dst → Arena.Avail E region →
      opStepC k (.split E.internal [region]) c s (.ok s₁) →
      opStepC k (.store s.A.length dst) c s₁ .reject → IssueStepC k s ar c i region dst .reject
  | ok {E : Arena.ArenaEntry} {s₁ s₂ : SC} : ar[i]? = some E →
      Arena.IssueStatic (s.view c) E region dst → Arena.Avail E region →
      opStepC k (.split E.internal [region]) c s (.ok s₁) →
      opStepC k (.store s.A.length dst) c s₁ (.ok s₂) →
      IssueStepC k s ar c i region dst (.ok (s₂, ar.set i (Arena.issueMeta s.flat E region)))

/-- `reset(arena)` of entry `i` executed by `c` (Spec 1 §78, §58; Part XIV): the derived operation
`Arena.ResetD` (`derive` of `internal` at `Modify` over the storage, `release`, the check of §78.3)
on the view of `c`, written back (C2); `derive` and `release` read neither `ancestor` nor the
stack beyond its top and its membership. A context that is not live has no current frame (C2):
the internal `derive` fails, `reject`. -/
def ResetStepC (s : SC) (ar : ArenaReg) (c i : Nat) (o : Outcome3 (SC × ArenaReg)) : Prop :=
  ∃ o₃, Arena.ResetD i ⟨s.view c, ar⟩ o₃ ∧
    o = omap (fun L' => (s.set L'.kern, L'.arenas)) o₃

/-- Writing back into `s` an `S3` whose stack is that of the view of `c`, then taking the view of
`c`, gives that `S3` back (C2). -/
theorem SC.view_set {s : SC} {c : Nat} {t : S3} (hc : s.Live c) (hF : t.F = (s.view c).F) :
    (s.set t).view c = t := by
  have hc' : (s.set t).Live c := hc
  have h : (s.set t).view c = { t with F := (s.view c).F } := by
    simp only [SC.view, hc, hc', ite_true]; rfl
  rw [h, ← hF]

/-- Writing back into `s` keeps the stack of the view of a live context (C2). -/
theorem SC.view_F_set {s : SC} {c : Nat} {t : S3} (hc : s.Live c) :
    ((s.set t).view c).F = (s.view c).F := by
  have hc' : (s.set t).Live c := hc
  rw [SC.view_F_live hc, SC.view_F_live hc']; rfl

/-- Writing back twice keeps the second state only (C2). -/
theorem SC.set_set (s : SC) (t u : S3) : (s.set t).set u = s.set u := rfl

/-- An `ok` outcome of `newArena` executed by `c` (Spec 1 §76): the preconditions hold and the
entry is registered. -/
theorem newArenaStepC_ok {s : SC} {reg : SyncReg} {ar : ArenaReg} {c st i : Nat}
    {st' : SC × ArenaReg} (h : NewArenaStepC s reg ar c st i (.ok st')) :
    s.Live c ∧ NewArenaPreC s reg ar c st i ∧
      st' = (s, ar ++ [⟨st, i, footprint s.P st, []⟩]) :=
  ⟨SC.live_of_hasRight (Guarded.ok_iff.1 h).1.storageRight, Guarded.ok_iff.1 h⟩

/-- An `ok` outcome of `issue` executed by `c` (Spec 1 §77, Part XIV): the static checks and
availability, then `split` then `store` executed by `c`, then the metadata update. -/
theorem issueStepC_ok {k : K} {s : SC} {ar : ArenaReg} {c i : Nat} {region : List Nat}
    {dst : Nat} {st' : SC × ArenaReg} (h : IssueStepC k s ar c i region dst (.ok st')) :
    ∃ E s₁, ar[i]? = some E ∧ Arena.IssueStatic (s.view c) E region dst ∧
      Arena.Avail E region ∧ opStepC k (.split E.internal [region]) c s (.ok s₁) ∧
      opStepC k (.store s.A.length dst) c s₁ (.ok st'.1) ∧
      st'.2 = ar.set i (Arena.issueMeta s.flat E region) := by
  cases h with
  | ok hE hst hav hsp hsto => exact ⟨_, _, hE, hst, hav, hsp, hsto, rfl⟩

/-- An `ok` outcome of `reset` executed by `c` (Spec 1 §78, Part XIV): `derive` of `internal` at
`Modify` over the storage then `release` of the derived authority, both executed by `c` (C2),
the check of §78.3 holding, then the metadata update. -/
theorem resetStepC_ok {k : K} {s : SC} {ar : ArenaReg} {c i : Nat} {st' : SC × ArenaReg}
    (h : ResetStepC s ar c i (.ok st')) :
    ∃ E s₁, ar[i]? = some E ∧
      opStepC k (.derive E.internal (footprint s.P E.storage) .modify) c s (.ok s₁) ∧
      opStepC k (.release s.A.length) c s₁ (.ok st'.1) ∧ Arena.ResetNoDeps (s.view c) E ∧
      st'.2 = ar.set i (Arena.resetMeta s.flat E) := by
  obtain ⟨o₃, hr, ho⟩ := h
  cases hr with
  | noEntry => cases ho
  | derive => cases ho
  | release => cases ho
  | contract => cases ho
  | @ok E t₁ t₂ hE hd hrl hnd =>
    cases ho
    have hl : s.Live c := SC.live_of_exercisable (Guarded.ok_iff.1 hd).1.exercisable
    have hF : t₁.F = (s.view c).F := by obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hd; rfl
    refine ⟨E, s.set t₁, hE, ⟨.ok t₁, hd, rfl⟩, ?_, hnd, rfl⟩
    refine ⟨.ok t₂, ?_, rfl⟩
    rw [SC.view_set hl hF]; exact hrl

/-! ## Labelled steps, runs, encapsulation (C22, C23) -/

/-- Label of a step of the concurrent authority machine with the synchronization and arena
libraries (C2, C19, C23; Spec 1 §76–§78) and the atomic step cases (C37, C39). -/
inductive Label where
  | kernel (c : Nat) (op : KernelOp)
  | spawn (c : Nat) (ps : List Nat) (ls : LocalShape)
  | terminate (c : Nat)
  | join (c d : Nat)
  | deriveSync (c g : Nat)
  | newMutex (c g : Nat)
  | acquire (c i : Nat)
  | unlock (c i : Nat)
  | resetLock (c i : Nat)
  | spawnVal (c : Nat) (ps : List Nat) (ls : LocalShape) (vs : List (Nat × Nat))
  | newArena (c storage internal : Nat)
  | issue (c arena : Nat) (region : List Nat) (dst : Nat)
  | reset (c arena : Nat)
  | readShared (c access leaf : Nat) (order : MemOrder) (observed : Nat)
  | writeShared (c access : Nat) (region : List Nat) (order : Option MemOrder) (kind : WriteKind)
  | cas (c access leaf : Nat) (succ fail : MemOrder) (branch : CasBranch)

/-- Labelled `ok` step of the concurrent authority machine with the synchronization and arena
libraries (C2, C4, C5, C6–C8, C13, C15–C19, C37–C40; C23 for the by-value composite; Spec 1
§76–§78 for the arenas): kernel and frame steps keep both registries; raw `deriveSync` runs under
the library instantiation of `SyncAuthorized` on the current registry (C14); the mutex
operations change the synchronization registry, the arena operations the arena registry (Spec 1
§46); the atomic cases keep both registries (C39). The label of `readShared` and of a CAS carries
the observed value, which the step does not constrain (C37, C39). -/
inductive LStep (ks : KShared) (L : MutexLayout) :
    Label → SC × SyncReg × ArenaReg → SC × SyncReg × ArenaReg → Prop where
  | kernel {s s' : SC} {reg : SyncReg} {ar : ArenaReg} {c : Nat} {op : KernelOp} :
      opStepC ks.toK op c s (.ok s') → LStep ks L (.kernel c op) (s, reg, ar) (s', reg, ar)
  | spawn {s s' : SC} {reg : SyncReg} {ar : ArenaReg} {c : Nat} {ps : List Nat}
      {ls : LocalShape} :
      SpawnStep s c ps ls (.ok s') → LStep ks L (.spawn c ps ls) (s, reg, ar) (s', reg, ar)
  | terminate {s s' : SC} {reg : SyncReg} {ar : ArenaReg} {c : Nat} :
      TermStep ks.toK s c (.ok s') → LStep ks L (.terminate c) (s, reg, ar) (s', reg, ar)
  | join {s s' : SC} {reg : SyncReg} {ar : ArenaReg} {c d : Nat} :
      JoinStep s c d (.ok s') → LStep ks L (.join c d) (s, reg, ar) (s', reg, ar)
  | deriveSync {s s' : SC} {reg : SyncReg} {ar : ArenaReg} {c g : Nat} :
      DeriveSyncStep (libKC ks L) reg s c g (.ok s') →
      LStep ks L (.deriveSync c g) (s, reg, ar) (s', reg, ar)
  | newMutex {s : SC} {reg : SyncReg} {ar : ArenaReg} {c g : Nat} {st' : SC × SyncReg} :
      NewMutexOk ks.toK L ar s reg c g st' →
      LStep ks L (.newMutex c g) (s, reg, ar) (st'.1, st'.2, ar)
  | acquire {s : SC} {reg : SyncReg} {ar : ArenaReg} {c i : Nat} {st' : SC × SyncReg} :
      AcquireOk ks L s reg c i st' → LStep ks L (.acquire c i) (s, reg, ar) (st'.1, st'.2, ar)
  | unlock {s : SC} {reg : SyncReg} {ar : ArenaReg} {c i : Nat} {st' : SC × SyncReg} :
      UnlockOk L s reg c i st' → LStep ks L (.unlock c i) (s, reg, ar) (st'.1, st'.2, ar)
  | resetLock {s : SC} {reg : SyncReg} {ar : ArenaReg} {c i : Nat} {st' : SC × SyncReg} :
      ResetLockOk L s reg c i st' → LStep ks L (.resetLock c i) (s, reg, ar) (st'.1, st'.2, ar)
  | spawnVal {s s' : SC} {reg : SyncReg} {ar : ArenaReg} {c : Nat} {ps : List Nat}
      {ls : LocalShape} {vs : List (Nat × Nat)} :
      SpawnValStep ks.toK s c ps ls vs (.ok s') →
      LStep ks L (.spawnVal c ps ls vs) (s, reg, ar) (s', reg, ar)
  | newArena {s : SC} {reg : SyncReg} {ar : ArenaReg} {c st i : Nat} {st' : SC × ArenaReg} :
      NewArenaStepC s reg ar c st i (.ok st') →
      LStep ks L (.newArena c st i) (s, reg, ar) (st'.1, reg, st'.2)
  | issue {s : SC} {reg : SyncReg} {ar : ArenaReg} {c i : Nat} {region : List Nat} {dst : Nat}
      {st' : SC × ArenaReg} :
      IssueStepC ks.toK s ar c i region dst (.ok st') →
      LStep ks L (.issue c i region dst) (s, reg, ar) (st'.1, reg, st'.2)
  | reset {s : SC} {reg : SyncReg} {ar : ArenaReg} {c i : Nat} {st' : SC × ArenaReg} :
      ResetStepC s ar c i (.ok st') → LStep ks L (.reset c i) (s, reg, ar) (st'.1, reg, st'.2)
  | readShared {s : SC} {reg : SyncReg} {ar : ArenaReg} {c a l v : Nat} {order : MemOrder} :
      ReadSharedStep ks s c a l order (.ok s) →
      LStep ks L (.readShared c a l order v) (s, reg, ar) (s, reg, ar)
  | writeShared {s s' : SC} {reg : SyncReg} {ar : ArenaReg} {c a : Nat} {region : List Nat}
      {order : Option MemOrder} {kind : WriteKind} :
      WriteSharedCStep ks s c a region order kind (.ok s') →
      LStep ks L (.writeShared c a region order kind) (s, reg, ar) (s', reg, ar)
  | cas {s s' : SC} {reg : SyncReg} {ar : ArenaReg} {c a l : Nat} {succ fail : MemOrder}
      {br : CasBranch} :
      CasStep ks s c a l succ fail br (.ok s') →
      LStep ks L (.cas c a l succ fail br) (s, reg, ar) (s', reg, ar)

/-- C22.3 for the source `src` of a transfer in state `st`: for each live entry, `src` is
neither the place `slot` holding `guarded`, nor a strict structural subplace of `slot`, nor the
controller leaf `ctl`. -/
def TransferExcl (L : MutexLayout) (st : SC × SyncReg) (src : Nat) : Prop :=
  ∀ e ∈ st.2, e.Live st.1 →
    OptP (slotOf st.1 e.guarded) (fun q => ¬ partOf st.1.P src q) True ∧
      ControlOf L st.1 e ≠ some src

/-- Decidability of `TransferExcl` (C22.3). -/
instance (L : MutexLayout) (st : SC × SyncReg) (src : Nat) : Decidable (TransferExcl L st src) := by
  unfold TransferExcl; infer_instance

/-- C22.3 for the transfers of the by-value composite (C23):
the source of every transfer phase satisfies `TransferExcl` in the state where that phase starts
(C5.2), the registry being `reg`. -/
def EncapVals (L : MutexLayout) (reg : SyncReg) (c : Nat) : SC → List (Nat × Nat) → Prop
  | _, [] => True
  | t, v :: vs => TransferExcl L (t, reg) v.1 ∧ EncapVals L reg c (transferEffC t c v.1 v.2) vs

/-- The safe-abstraction restrictions under which C23 requires preservation, for one step taken in
state `st`: C22.1, C22.2, C22.3 and C22.5, for every live entry. They constrain allowed traces,
not kernel transitions (C22, C23).

* C22.1: no `derive` or `split` with `source = guarded`; no compound operation performing an
  internal `derive` or `split` from `guarded`: `issue` splits the arena's `internal`, `reset`
  derives from it (Spec 1 Part XIV), so their `internal` is not a live `guarded`. The synchronized
  grant is created only by `acquire` (C22.1, C22.2).
* C22.2: no raw `deriveSync` of a live `guarded`.
* C22.3: no `transfer` whose source is `slot`, a strict structural subplace of `slot`, or `ctl`,
  each transfer phase of a by-value `spawn` being checked in the state where it starts.
* C22.5: no `endUse` of `ctl` or of a strict structural subplace of `slot`. -/
def RestrictedStep (L : MutexLayout) (st : SC × SyncReg × ArenaReg) : Label → Prop
  | .kernel _ (.derive src _ _) => ∀ e ∈ st.2.1, e.Live st.1 → src ≠ e.guarded
  | .kernel _ (.split src _) => ∀ e ∈ st.2.1, e.Live st.1 → src ≠ e.guarded
  | .kernel _ (.transfer src _) => TransferExcl L (st.1, st.2.1) src
  | .kernel _ (.endUse p) => ∀ e ∈ st.2.1, e.Live st.1 → ControlOf L st.1 e ≠ some p ∧
      OptP (slotOf st.1 e.guarded) (fun q => partOf st.1.P p q → p = q) True
  | .spawnVal c _ ls vs => EncapVals L st.2.1 c (spawnCreate st.1 c ls) vs
  | .deriveSync _ g => ∀ e ∈ st.2.1, e.Live st.1 → g ≠ e.guarded
  | .issue _ i _ _ => OptP (st.2.2[i]?) (fun E => ∀ e ∈ st.2.1, e.Live st.1 →
      E.internal ≠ e.guarded) True
  | .reset _ i => OptP (st.2.2[i]?) (fun E => ∀ e ∈ st.2.1, e.Live st.1 →
      E.internal ≠ e.guarded) True
  | _ => True

/-- Runs of labelled steps. -/
inductive LRun (ks : KShared) (L : MutexLayout) :
    SC × SyncReg × ArenaReg → List Label → SC × SyncReg × ArenaReg → Prop where
  | nil {st : SC × SyncReg × ArenaReg} : LRun ks L st [] st
  | cons {st st₁ st₂ : SC × SyncReg × ArenaReg} {lbl : Label} {lbls : List Label} :
      LStep ks L lbl st st₁ → LRun ks L st₁ lbls st₂ → LRun ks L st (lbl :: lbls) st₂

/-- A run every step of which satisfies `RestrictedStep` in the state where it is taken: the trace
assumption of C23 (C22.1–C22.3, C22.5; C23). It is weaker than `EncapsulatedTrace` (C51.1), which
adds C22.4 and C22.6. -/
inductive RestrictedTrace (ks : KShared) (L : MutexLayout) :
    SC × SyncReg × ArenaReg → List Label → SC × SyncReg × ArenaReg → Prop where
  | nil {st : SC × SyncReg × ArenaReg} : RestrictedTrace ks L st [] st
  | cons {st st₁ st₂ : SC × SyncReg × ArenaReg} {lbl : Label} {lbls : List Label} :
      RestrictedStep L st lbl → LStep ks L lbl st st₁ → RestrictedTrace ks L st₁ lbls st₂ →
      RestrictedTrace ks L st (lbl :: lbls) st₂

/-- A restricted trace is a run. -/
theorem RestrictedTrace.run {ks : KShared} {L : MutexLayout} {st st' : SC × SyncReg × ArenaReg}
    {lbls : List Label} (h : RestrictedTrace ks L st lbls st') : LRun ks L st lbls st' := by
  induction h with
  | nil => exact .nil
  | cons _ hs _ ih => exact .cons hs ih

end Ern.ConcurrencyModel
