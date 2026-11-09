import Ern.Concurrency.Sync
import Ern.Concurrency.Transfer

/-!
# Reference synchronization library

Library state separate from `S_C` (WC4 C2, C12), on the pattern of `Ern.MemoryModel.Arena` (Spec
1 §46, §55, §56):

* the registry of `SyncEntry { guarded, grant }` (WC4 C12), liveness of an entry, the positional
  `ControlOf` relationship (WC4 C12) for declared field positions `MutexLayout`;
* `SyncInv` (WC4 C21.1–C21.7) and `GrantDiscipline` (WC4 C22);
* the library instantiation of `K_C.SyncAuthorized` on the registry (WC4 C14.1–C14.3), and the
  contract obligation `SyncSound` of WC4 C14 ("cannot be used outside the corresponding valid
  synchronization contract");
* derived operations `newMutex` (C13), `acquire` (C16), `unlock` (C17), `resetLock` (C18);
* labelled library steps, the by-value composite included (WC4 C23), runs, and the encapsulation
  hypothesis `EncapsulatedTrace` (WC4 C22.1–C22.3, C22.5; C23), a predicate on runs, never a
  precondition of a kernel operation.
-/

namespace Ern.Concurrency

open Ern.MemoryModel.Access

/-! ## Registry (WC4 C12) -/

/-- Synchronization entry (WC4 C12): the protected authority `guarded` and the recorded grant. -/
structure SyncEntry where
  guarded : Nat
  grant : Option Nat
deriving DecidableEq, Repr

/-- Synchronization registry (WC4 C12), library state separate from `S_C`. -/
abbrev SyncReg := List SyncEntry

/-- Declared field positions of the reference mutex value (WC4 C12: "at its declared field
position", `guardedField`, `controlField`): the position of the field holding `guarded` and that of the controller, among the
ordered children of the mutex value. -/
structure MutexLayout where
  guardedField : Nat
  controlField : Nat
deriving DecidableEq, Repr

/-- An entry is live exactly while `guarded` is active (WC4 C12). -/
def SyncEntry.Live (s : SC) (e : SyncEntry) : Prop := s.flat.Active e.guarded

/-- Decidability of liveness of an entry (WC4 C12). -/
instance (s : SC) (e : SyncEntry) : Decidable (e.Live s) := by
  unfold SyncEntry.Live; infer_instance

/-- Positional `ControlOf` (WC4 C12): `guarded` is held by the field `h` at position
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

/-- The `S3` whose current frame is `f` (WC4 C14: `SyncAuthorized` names the requesting frame;
Spec 1 §43 reads the stack only through its top and membership). -/
def SC.viewAt (s : SC) (f : Nat) : S3 :=
  { s.flat with F := f :: s.frames.filter fun g => decide (g ≠ f) }

/-- WC4 C14.3: the frame `f` has effective and exercisable access to `ControlOf(e)` under the
condition of Spec 1 §68.2: some authority exercisable by `f` in a mode at least `Observe` has a
present effective mode on the controller. -/
def CtrlRight (L : MutexLayout) (s : SC) (e : SyncEntry) (f : Nat) : Prop :=
  OptP (ControlOf L s e) (fun ctl => ∃ a ∈ List.range s.A.length,
    (s.viewAt f).ExercisableAt a .observe ∧ effective s.flat a ctl ≠ none) False

/-- Decidability of the controller fact. -/
instance (L : MutexLayout) (s : SC) (e : SyncEntry) (f : Nat) : Decidable (CtrlRight L s e f) := by
  unfold CtrlRight; infer_instance

/-- The authorization facts of WC4 C14 for an entry: C14.1 (live), C14.2 (`grant = none`), C14.3
(`CtrlRight`). -/
def EntryAuth (L : MutexLayout) (s : SC) (e : SyncEntry) (f : Nat) : Prop :=
  e.Live s ∧ e.grant = none ∧ CtrlRight L s e f

/-- Decidability of the library authorization of an entry. -/
instance (L : MutexLayout) (s : SC) (e : SyncEntry) (f : Nat) : Decidable (EntryAuth L s e f) := by
  unfold EntryAuth; infer_instance

/-- Instantiation of `K_C.SyncAuthorized(state, sync_registry, guarded, requesting_frame)` by the
library (WC4 C14, C25): an entry of the registry with the requested `guarded` identity satisfies
the authorization facts C14.1–C14.3. -/
def LibSyncAuthorized (L : MutexLayout) (reg : SyncReg) (s : SC) (g f : Nat) : Prop :=
  ∃ e ∈ reg, e.guarded = g ∧ EntryAuth L s e f

/-- Decidability of the library instantiation. -/
instance (L : MutexLayout) (reg : SyncReg) (s : SC) (g f : Nat) :
    Decidable (LibSyncAuthorized L reg s g f) := by
  unfold LibSyncAuthorized; infer_instance

/-- The contract `K_C` instantiated by the library (WC4 C14, C25), the registry type being
`SyncReg` (WC4 C2). -/
def libKC (k : K) (L : MutexLayout) : KC SyncReg :=
  { k with SyncAuthorized := LibSyncAuthorized L }

/-- Decidability of the instantiated predicate. -/
instance (k : K) (L : MutexLayout) (reg : SyncReg) (s : SC) (g f : Nat) :
    Decidable ((libKC k L).SyncAuthorized reg s g f) :=
  inferInstanceAs (Decidable (LibSyncAuthorized L reg s g f))

/-- Contract obligation of WC4 C14 ("cannot be used outside the corresponding valid
synchronization contract"), in state `s` with registry `reg`: `SyncAuthorized` holds only for the
`guarded` of a live entry of `reg`. -/
def SyncSound (kc : KC SyncReg) (reg : SyncReg) (s : SC) : Prop :=
  ∀ g f, kc.SyncAuthorized reg s g f → ∃ e ∈ reg, e.guarded = g ∧ e.Live s

/-- The library instantiation satisfies the obligation of WC4 C14. -/
theorem libKC_sound (k : K) (L : MutexLayout) (reg : SyncReg) (s : SC) :
    SyncSound (libKC k L) reg s :=
  fun _ _ ⟨e, he, hg, hl, _⟩ => ⟨e, he, hg, hl⟩

/-- The holder is a usable place (WC4 C12, C13.1, C21.1). -/
def PlaceUsable (t : S3) : Holder → Prop
  | .place q => t.Usable q
  | .frame _ => False

/-- Decidability of `PlaceUsable` (WC4 C12). -/
instance (t : S3) (h : Holder) : Decidable (PlaceUsable t h) := by
  cases h <;> unfold PlaceUsable <;> infer_instance

/-- Spec 1 §65.3 for an authority held by a place `q`: it covers neither a leaf of `q` nor a leaf
of storage transitively owned by `q` (WC4 C13.5). -/
def StoredOK (P : List Place) (y : Authority) : Prop :=
  match y.holder with
  | .place q => ∀ l ∈ y.footprint, l ∉ footprint P q ∧
      ∀ r ∈ List.range P.length, OwnedIn P q r → l ∉ footprint P r
  | .frame _ => True

/-- Decidability of `StoredOK` (Spec 1 §65.3). -/
instance (P : List Place) (y : Authority) : Decidable (StoredOK P y) := by
  unfold StoredOK; split <;> infer_instance

/-- The place `slot` holding `guarded` (WC4 C12). -/
def slotOf (s : SC) (g : Nat) : Option Nat :=
  match (s.A[g]?).map (·.holder) with
  | some (Holder.place h) => some h
  | _ => none

/-! ## Invariants (WC4 C21, C22) -/

/-- Active descendant of `guarded` covering a protected leaf, a leaf of `footprint(guarded)`
(WC4 C13.9, C18.2, C21.5, C22). -/
def CoveringDesc (s : SC) (g j : Nat) : Prop :=
  g ∈ s.flat.ancs j ∧ s.flat.Active j ∧ ∃ l ∈ s.flat.afp j, l ∈ s.flat.afp g

/-- Decidability of `CoveringDesc` (WC4 C22). -/
instance (s : SC) (g j : Nat) : Decidable (CoveringDesc s g j) := by
  unfold CoveringDesc; infer_instance

/-- No active descendant of `guarded` covers a protected leaf (WC4 C13.9, C18.2, C22). -/
def NoCoveringDesc (s : SC) (g : Nat) : Prop := ∀ j ∈ List.range s.A.length, ¬ CoveringDesc s g j

/-- Decidability of `NoCoveringDesc` (WC4 C22). -/
instance (s : SC) (g : Nat) : Decidable (NoCoveringDesc s g) := by
  unfold NoCoveringDesc; infer_instance

/-- `GrantDiscipline` (WC4 C22). -/
def GrantDiscipline (s : SC) (reg : SyncReg) : Prop :=
  ∀ e ∈ reg, e.Live s → e.grant = none → NoCoveringDesc s e.guarded

/-- WC4 C21.4, first clause: distinct live entries (by position in the registry) have distinct
`ControlOf` leaves. -/
def CtlUnique (L : MutexLayout) (s : SC) (reg : SyncReg) : Prop :=
  ∀ (i j : Nat) (e e' : SyncEntry) (ctl : Nat), reg[i]? = some e → reg[j]? = some e' →
    e.Live s → e'.Live s → ControlOf L s e = some ctl → ControlOf L s e' = some ctl → i = j

/-- WC4 C21.7, initialization invariant for `slot`: for every live entry, every structural leaf of
the place holding `guarded` is `Init`. -/
def SlotInit (s : SC) (reg : SyncReg) : Prop :=
  ∀ e ∈ reg, e.Live s →
    OptP (slotOf s e.guarded) (fun q => ∀ l ∈ footprint s.P q, s.I l = .init) False

/-- WC4 C21.7, initialization invariant for `ctl`: for every live entry, the controller leaf
`ControlOf(entry)` is `Init`. -/
def CtlInit (L : MutexLayout) (s : SC) (reg : SyncReg) : Prop :=
  ∀ e ∈ reg, e.Live s → OptP (ControlOf L s e) (fun ctl => s.I ctl = .init) False

/-- `SyncInv` (WC4 C21.1–C21.7): items 1–5 and 7 over live entries, item 6 over every entry. -/
structure SyncInv (L : MutexLayout) (s : SC) (reg : SyncReg) : Prop where
  /-- WC4 C21.1: `guarded` is active (liveness), has own mode `Modify`, and is held by a usable
  place. -/
  guarded : ∀ e ∈ reg, e.Live s → OptP (s.A[e.guarded]?) (fun y => y.mode = .modify ∧
    PlaceUsable s.flat y.holder) False
  /-- WC4 C21.2: a recorded grant exists, has origin `guarded` and footprint
  `footprint(guarded)`. -/
  grant : ∀ e ∈ reg, e.Live s → ∀ g, e.grant = some g → OptP (s.A[g]?) (fun y =>
    y.origin = some e.guarded ∧ ∀ l, l ∈ y.footprint ↔ l ∈ s.flat.afp e.guarded) False
  /-- WC4 C21.3, with the positional `ControlOf` of WC4 C12: the controller exists and is a usable
  leaf. -/
  control : ∀ e ∈ reg, e.Live s → OptP (ControlOf L s e) (fun ctl =>
    s.flat.Usable ctl ∧ isLeaf s.P ctl) False
  /-- WC4 C21.4, first clause: controller uniqueness among live entries. -/
  ctlUnique : CtlUnique L s reg
  /-- WC4 C21.4, second clause (the guarded-identity uniqueness guard of WC4 C13.7): distinct
  live entries have distinct `guarded` identities. -/
  unique : ∀ (i j : Nat) (e e' : SyncEntry), reg[i]? = some e → reg[j]? = some e' →
    e.Live s → e'.Live s →
    e.guarded = e'.guarded → i = j
  /-- WC4 C21.5, `GrantSubtree`. -/
  grantSubtree : ∀ e ∈ reg, e.Live s → ∀ g, e.grant = some g → s.flat.Active g →
    ∀ j, CoveringDesc s e.guarded j → j = g ∨ g ∈ s.flat.ancs j
  /-- WC4 C21.6, `RegBound`, over every entry: the registered `guarded` identity exists (Spec 1
  §38: identities are indices). -/
  regBound : ∀ e ∈ reg, e.guarded < s.A.length
  /-- WC4 C21.7: the structural leaves of `slot` are `Init`. -/
  slotInit : SlotInit s reg
  /-- WC4 C21.7: the controller leaf is `Init`. -/
  ctlInit : CtlInit L s reg

/-! ## Derived operations (WC4 C13, C16–C18) -/

/-- The mutex value `M` of WC4 C12, C13: the immediate structural parent of the place `slot`
holding `guarded`. -/
def mutexOf (s : SC) (g : Nat) : Option Nat :=
  match (s.A[g]?).map (·.holder) with
  | some (Holder.place h) => parentOf s.P h
  | _ => none

/-- Preconditions of `newMutex(guarded)` executed by `c` (WC4 C13.1–C13.10), with `adm` the
identities used by the other live administrations (Spec 1 §56). The interface and realization
obligations of WC4 C13 (C13.3, C13.6, former C13.10) are not represented: WC4 C13 says they "are
not claimed to follow from the authority-only state `S_C`". -/
structure NewMutexPre (k : K) (L : MutexLayout) (adm : List Nat) (s : SC) (reg : SyncReg)
    (c g : Nat) : Prop where
  /-- WC4 C13.1: `guarded` is active, of own mode `Modify`, and held by a usable place. -/
  guarded : OptP (s.A[g]?) (fun y => y.active = true ∧ y.mode = .modify ∧
    PlaceUsable s.flat y.holder) False
  /-- WC4 C13.2: ordinary exercisable `Modify` over `guarded` (Spec 1 §43). -/
  exercisable : (s.view c).ExercisableAt g .modify
  /-- WC4 C13.3, with the positional `ControlOf` of WC4 C12: the controller exists and is a
  usable leaf. -/
  control : OptP (ControlOf L s ⟨g, none⟩) (fun ctl => s.flat.Usable ctl ∧ isLeaf s.P ctl) False
  /-- WC4 C13.4: `footprint(guarded) ∩ footprint(M) = ∅`. -/
  disjointM : OptP (mutexOf s g) (fun m => ∀ l ∈ s.flat.afp g, l ∉ footprint s.P m) False
  /-- WC4 C13.10: every structural leaf of `footprint(M)` is `Init`. -/
  initM : OptP (mutexOf s g) (fun m => ∀ l ∈ footprint s.P m, s.I l = .init) False
  /-- WC4 C13.5: when `guarded` is stored (derived), Spec 1 §65.3 holds: it covers neither a leaf
  of its holder nor a leaf of storage transitively owned by it. -/
  stored : OptP (s.A[g]?) (fun y => y.origin ≠ none → StoredOK s.P y) False
  /-- WC4 C13.6: `K.SharedMutable(ctl)`. -/
  sharedMutable : OptP (ControlOf L s ⟨g, none⟩) k.SharedMutable False
  /-- WC4 C13.7, Spec 1 §56: `guarded` is not the identity of another live entry. -/
  unique : ∀ e ∈ reg, e.Live s → e.guarded ≠ g
  /-- WC4 C13.7, Spec 1 §56: `guarded` is not the identity of another live administration. -/
  otherAdmin : g ∉ adm
  /-- WC4 C13.8: no other live entry is associated with `ctl`. -/
  ctlUnique : OptP (ControlOf L s ⟨g, none⟩) (fun ctl => ∀ e ∈ reg, e.Live s →
    ControlOf L s e ≠ some ctl) False
  /-- WC4 C13.9. -/
  available : NoCoveringDesc s g

/-- Decidability of the preconditions of `newMutex` (WC4 C13). -/
instance (k : K) [DecidablePred k.SharedMutable] (L : MutexLayout) (adm : List Nat) (s : SC)
    (reg : SyncReg) (c g : Nat) : Decidable (NewMutexPre k L adm s reg c g) :=
  decidable_of_iff (OptP (s.A[g]?) (fun y => y.active = true ∧ y.mode = .modify ∧
      PlaceUsable s.flat y.holder) False ∧
    (s.view c).ExercisableAt g .modify ∧
    OptP (ControlOf L s ⟨g, none⟩) (fun ctl => s.flat.Usable ctl ∧ isLeaf s.P ctl) False ∧
    OptP (mutexOf s g) (fun m => ∀ l ∈ s.flat.afp g, l ∉ footprint s.P m) False ∧
    OptP (mutexOf s g) (fun m => ∀ l ∈ footprint s.P m, s.I l = .init) False ∧
    OptP (s.A[g]?) (fun y => y.origin ≠ none → StoredOK s.P y) False ∧
    OptP (ControlOf L s ⟨g, none⟩) k.SharedMutable False ∧
    (∀ e ∈ reg, e.Live s → e.guarded ≠ g) ∧ g ∉ adm ∧
    OptP (ControlOf L s ⟨g, none⟩) (fun ctl => ∀ e ∈ reg, e.Live s →
      ControlOf L s e ≠ some ctl) False ∧
    NoCoveringDesc s g)
    ⟨fun ⟨a, b, c, d, e, f, h, i, j, l, m⟩ => ⟨a, b, c, d, e, f, h, i, j, l, m⟩,
     fun ⟨a, b, c, d, e, f, h, i, j, l, m⟩ => ⟨a, b, c, d, e, f, h, i, j, l, m⟩⟩

/-- `newMutex(guarded)` executed by `c` (WC4 C13): registers the entry `⟨guarded, none⟩`; the
kernel state is unchanged and no authority is created (WC4 C13 effect). WC4 C13 states no outcome
other than success; only `ok` is defined. -/
def NewMutexOk (k : K) (L : MutexLayout) (adm : List Nat) (s : SC) (reg : SyncReg) (c g : Nat)
    (st' : SC × SyncReg) : Prop :=
  s.Live c ∧ NewMutexPre k L adm s reg c g ∧ st' = (s, reg ++ [⟨g, none⟩])

/-- `acquire` on entry `i` executed by `c` (WC4 C16): with the library instantiation of
`SyncAuthorized` for the entry, `deriveSync(guarded)` on the registry `reg` and the record of the
fresh grant identity `|A|` in the entry. A taken controller (`grant ≠ none`) leaves `acquire` not
enabled; WC4 C16 states no other outcome than success, so only `ok` is defined. -/
def AcquireOk (k : K) (L : MutexLayout) (s : SC) (reg : SyncReg) (c i : Nat)
    (st' : SC × SyncReg) : Prop :=
  s.Live c ∧ ∃ e, reg[i]? = some e ∧ EntryAuth L s e (s.view c).top ∧
    DeriveSyncPre (libKC k L) reg s c e.guarded ∧
    st' = (deriveSyncEff s c e.guarded, reg.set i { e with grant := some s.A.length })

/-- `unlock` of entry `i` executed by `c` (WC4 C17.1–C17.4): O3 releases the grant and the registry
records `grant = none` (WC4 C17 effect). C17.2 and C17.3 are the preconditions of O3 (Spec 1 §62);
C17.4 is `CtrlRight`. The controller update is a realization obligation (WC4 C17), not a
precondition; only `ok` is defined. -/
def UnlockOk (L : MutexLayout) (s : SC) (reg : SyncReg) (c i : Nat) (st' : SC × SyncReg) :
    Prop :=
  s.Live c ∧ ∃ e g, reg[i]? = some e ∧ e.Live s ∧ e.grant = some g ∧ ReleasePre (s.view c) g ∧
    CtrlRight L s e (s.view c).top ∧
    st' = (s.set (releaseEff (s.view c) g), reg.set i { e with grant := none })

/-- `resetLock` of entry `i` executed by `c` (WC4 C18.1–C18.3): the entry becomes available; the
kernel state is unchanged (WC4 C18 effect). WC4 C18.3: "`ControlOf(entry)` resolves to an
existing, usable controller **leaf**, as required by C21.3"; the controller-initialization
invariant is not a precondition (WC4 C18.3: "established separately for every live entry by
C21.7"). Only `ok` is defined. -/
def ResetLockOk (L : MutexLayout) (s : SC) (reg : SyncReg) (c i : Nat) (st' : SC × SyncReg) :
    Prop :=
  s.Live c ∧ ∃ e, reg[i]? = some e ∧ (s.view c).ExercisableAt e.guarded .modify ∧
    NoCoveringDesc s e.guarded ∧
    OptP (ControlOf L s e) (fun ctl => s.flat.Usable ctl ∧ isLeaf s.P ctl) False ∧
    st' = (s, reg.set i { e with grant := none })

/-! ## Labelled steps, runs, encapsulation (WC4 C22, C23) -/

/-- Label of a step of the kernel with the synchronization library. -/
inductive Label where
  | kernel (c : Nat) (op : KernelOp)
  | spawn (c : Nat) (ps : List Nat) (ls : LocalShape)
  | terminate (c : Nat)
  | join (c d : Nat)
  | deriveSync (c g : Nat)
  | newMutex (c g : Nat) (adm : List Nat)
  | acquire (c i : Nat)
  | unlock (c i : Nat)
  | resetLock (c i : Nat)
  | spawnVal (c : Nat) (ps : List Nat) (ls : LocalShape) (vs : List (Nat × Nat))

/-- Labelled `ok` step of the concurrent kernel with the synchronization library (WC4 C2, C4,
C5, C6–C8, C13, C15–C18; WC4 C23 for the by-value composite): kernel and
frame steps keep the registry; raw `deriveSync` runs under the
library instantiation of `SyncAuthorized` on the current registry (WC4 C14). -/
inductive LStep (k : K) (L : MutexLayout) : Label → SC × SyncReg → SC × SyncReg → Prop where
  | kernel {s s' : SC} {reg : SyncReg} {c : Nat} {op : KernelOp} :
      opStepC k op c s (.ok s') → LStep k L (.kernel c op) (s, reg) (s', reg)
  | spawn {s s' : SC} {reg : SyncReg} {c : Nat} {ps : List Nat} {ls : LocalShape} :
      SpawnStep s c ps ls (.ok s') → LStep k L (.spawn c ps ls) (s, reg) (s', reg)
  | terminate {s s' : SC} {reg : SyncReg} {c : Nat} :
      TermStep k s c (.ok s') → LStep k L (.terminate c) (s, reg) (s', reg)
  | join {s s' : SC} {reg : SyncReg} {c d : Nat} :
      JoinStep s c d (.ok s') → LStep k L (.join c d) (s, reg) (s', reg)
  | deriveSync {s s' : SC} {reg : SyncReg} {c g : Nat} :
      DeriveSyncStep (libKC k L) reg s c g (.ok s') → LStep k L (.deriveSync c g) (s, reg) (s', reg)
  | newMutex {s : SC} {reg : SyncReg} {c g : Nat} {adm : List Nat} {st' : SC × SyncReg} :
      NewMutexOk k L adm s reg c g st' → LStep k L (.newMutex c g adm) (s, reg) st'
  | acquire {s : SC} {reg : SyncReg} {c i : Nat} {st' : SC × SyncReg} :
      AcquireOk k L s reg c i st' → LStep k L (.acquire c i) (s, reg) st'
  | unlock {s : SC} {reg : SyncReg} {c i : Nat} {st' : SC × SyncReg} :
      UnlockOk L s reg c i st' → LStep k L (.unlock c i) (s, reg) st'
  | resetLock {s : SC} {reg : SyncReg} {c i : Nat} {st' : SC × SyncReg} :
      ResetLockOk L s reg c i st' → LStep k L (.resetLock c i) (s, reg) st'
  | spawnVal {s s' : SC} {reg : SyncReg} {c : Nat} {ps : List Nat} {ls : LocalShape}
      {vs : List (Nat × Nat)} :
      SpawnValStep k s c ps ls vs (.ok s') → LStep k L (.spawnVal c ps ls vs) (s, reg) (s', reg)

/-- WC4 C22.3 for the source `src` of a transfer in state `st`: for each live entry, `src` is
neither the place `slot` holding `guarded`, nor a strict structural subplace of `slot`, nor the
controller leaf `ctl`. -/
def TransferExcl (L : MutexLayout) (st : SC × SyncReg) (src : Nat) : Prop :=
  ∀ e ∈ st.2, e.Live st.1 →
    OptP (slotOf st.1 e.guarded) (fun q => ¬ partOf st.1.P src q) True ∧
      ControlOf L st.1 e ≠ some src

/-- Decidability of `TransferExcl` (WC4 C22.3). -/
instance (L : MutexLayout) (st : SC × SyncReg) (src : Nat) : Decidable (TransferExcl L st src) := by
  unfold TransferExcl; infer_instance

/-- WC4 C22.3 for the transfers of the by-value composite (WC4 C23):
the source of every transfer phase satisfies `TransferExcl` in the state where that phase starts
(WC4 C5.2), the registry being `reg`. -/
def EncapVals (L : MutexLayout) (reg : SyncReg) (c : Nat) : SC → List (Nat × Nat) → Prop
  | _, [] => True
  | t, v :: vs => TransferExcl L (t, reg) v.1 ∧ EncapVals L reg c (transferEffC t c v.1 v.2) vs

/-- Encapsulation of one step in state `st` (hypothesis on traces, WC4 C22, C23): for each live
entry, WC4 C22.1 (`derive`, `split`), C22.2 (raw `deriveSync`), C22.3 (`transfer`, and the
transfer phases of the by-value composite) and C22.5 (`endUse` whose place is the controller leaf
`ctl` or a strict structural subplace of `slot`). WC4 C22.4 (controller-write protocol) is a
realization/interface obligation (WC4 C22) with no content in `S_C`, which has no values (Spec 1
§41), and is not represented. -/
def Encap (L : MutexLayout) (st : SC × SyncReg) : Label → Prop
  | .kernel _ (.derive src _ _) => ∀ e ∈ st.2, e.Live st.1 → src ≠ e.guarded
  | .kernel _ (.split src _) => ∀ e ∈ st.2, e.Live st.1 → src ≠ e.guarded
  | .kernel _ (.transfer src _) => TransferExcl L st src
  | .kernel _ (.endUse p) => ∀ e ∈ st.2, e.Live st.1 → ControlOf L st.1 e ≠ some p ∧
      OptP (slotOf st.1 e.guarded) (fun q => partOf st.1.P p q → p = q) True
  | .spawnVal c _ ls vs => EncapVals L st.2 c (spawnCreate st.1 c ls) vs
  | .deriveSync _ g => ∀ e ∈ st.2, e.Live st.1 → g ≠ e.guarded
  | _ => True

/-- Runs of labelled steps. -/
inductive LRun (k : K) (L : MutexLayout) : SC × SyncReg → List Label → SC × SyncReg → Prop where
  | nil {st : SC × SyncReg} : LRun k L st [] st
  | cons {st st₁ st₂ : SC × SyncReg} {lbl : Label} {lbls : List Label} :
      LStep k L lbl st st₁ → LRun k L st₁ lbls st₂ → LRun k L st (lbl :: lbls) st₂

/-- `EncapsulatedTrace` (WC4 C22, C23: "Any lemma conditional on encapsulation must expose that
condition in its theorem statement or the reachable-trace assumptions"): a run every step of which
satisfies `Encap` in the state where it is taken. -/
inductive EncapsulatedTrace (k : K) (L : MutexLayout) :
    SC × SyncReg → List Label → SC × SyncReg → Prop where
  | nil {st : SC × SyncReg} : EncapsulatedTrace k L st [] st
  | cons {st st₁ st₂ : SC × SyncReg} {lbl : Label} {lbls : List Label} :
      Encap L st lbl → LStep k L lbl st st₁ → EncapsulatedTrace k L st₁ lbls st₂ →
      EncapsulatedTrace k L st (lbl :: lbls) st₂

/-- An encapsulated trace is a run. -/
theorem EncapsulatedTrace.run {k : K} {L : MutexLayout} {st st' : SC × SyncReg}
    {lbls : List Label} (h : EncapsulatedTrace k L st lbls st') : LRun k L st lbls st' := by
  induction h with
  | nil => exact .nil
  | cons _ hs _ ih => exact .cons hs ih

/-! ## Theorem 1, last part: `SyncAuthorized` and `deriveSync` without live entry (WC4 C14, C24) -/

/-- Theorem 1 (WC4 C14, C24): in a state whose registry has no live entry, the obligation of WC4
C14 makes `K_C.SyncAuthorized` false on that registry. Fragment: every state, single-context ones
included. -/
theorem syncAuthorized_false {kc : KC SyncReg} {reg : SyncReg} {s : SC}
    (hsound : SyncSound kc reg s) (hnone : ∀ e ∈ reg, ¬ e.Live s) (g f : Nat) :
    ¬ kc.SyncAuthorized reg s g f := fun h => by
  obtain ⟨e, he, -, hl⟩ := hsound g f h
  exact hnone e he hl

/-- Theorem 1 (WC4 C15, C24): in a state whose registry has no live entry, under the obligation
of WC4 C14, `deriveSync` on that registry is never enabled. -/
theorem conservative_deriveSync {kc : KC SyncReg} {reg : SyncReg} {s : SC}
    (hsound : SyncSound kc reg s) (hnone : ∀ e ∈ reg, ¬ e.Live s) (c g : Nat) (s' : SC) :
    ¬ DeriveSyncStep kc reg s c g (.ok s') :=
  fun ⟨_, h⟩ => syncAuthorized_false hsound hnone g _ (Guarded.ok_iff.1 h).1.authorized

/-! ## Theorem 6: exclusivity of grants (Spec 1 §50; WC4 C15) -/

/-- An ancestor of an authority whose origin is `g` is `g` or below `g` (Spec 1 §42, §49.5). -/
theorem ancs_le_origin {t : S3} (hw : WF3 t) {b g : Nat} {y : Authority} (hy : t.A[b]? = some y)
    (hyo : y.origin = some g) {x : Nat} (hx : x ∈ t.ancs b) : x ≤ g := by
  have hgb : g < b := hw.origins b y g hy hyo
  have horg : t.org b = some g := by simp [S3.org, hy, hyo]
  rw [S3.ancs, chain_cons horg hgb] at hx
  rcases List.mem_cons.1 hx with rfl | hx
  · exact Nat.le_refl _
  · exact Nat.le_of_lt (chain_lt hx)

/-- Theorem 6 (Spec 1 §50, I1; WC4 C15, C21.2): two distinct active authorities of own mode
`Modify` whose origin is the same `guarded` and whose footprint is `footprint(guarded)`, nonempty,
cannot coexist. Fragment: states satisfying `WF3` and `I1` on the globally live frames. -/
theorem grants_exclusive {s : SC} (hw : WF3 s.flat) (h1 : I1 s.flat) {g a b : Nat}
    {x y : Authority} (hab : a ≠ b) (hx : s.A[a]? = some x) (hy : s.A[b]? = some y)
    (xa : x.active = true) (ya : y.active = true) (xm : x.mode = .modify)
    (xo : x.origin = some g) (yo : y.origin = some g)
    (xf : ∀ l, l ∈ x.footprint ↔ l ∈ s.flat.afp g) (yf : ∀ l, l ∈ y.footprint ↔ l ∈ s.flat.afp g)
    {l : Nat} (hl : l ∈ s.flat.afp g) : False := by
  have hga : g < a := hw.origins a x g hx xo
  have hgb : g < b := hw.origins b y g hy yo
  have hna : a ∉ s.flat.ancs b := fun h => by have := ancs_le_origin hw hy yo h; omega
  have hnb : b ∉ s.flat.ancs a := fun h => by have := ancs_le_origin hw hx xo h; omega
  have := h1 a b x y l hab hx hy xa ya ((xf l).2 hl) ((yf l).2 hl) hna hnb
  rw [xm] at this; cases this.1

/-! ## Theorem 5: realizability (WC4 C14, C25) -/

/-- Theorem 5 (WC4 C14, C15, C25): under `SyncInv` and `GrantDiscipline`, and the kernel invariant
re-indexed (`KInvC`: `WF3`, `I1` and `I2` are used), the library instantiation of
`SyncAuthorized` (the facts C14.1–C14.3 only) on the registry, for the current frame of a live
context, entails that no active descendant of `guarded` covers a protected leaf and all the
preconditions of `deriveSync` on that registry, in particular the own mode (C15.1), I1 for the
full-footprint grant (§60.3) and the validity of the origin chain (§60.1). Fragment: states
satisfying `KInvC`. -/
theorem realizability {k : K} {L : MutexLayout} {reg : SyncReg} {s : SC} {c g : Nat}
    (hk : KInvC s) (hsi : SyncInv L s reg) (hgd : GrantDiscipline s reg) (hc : s.stk c ≠ [])
    (ha : LibSyncAuthorized L reg s g (s.view c).top) :
    NoCoveringDesc s g ∧ DeriveSyncPre (libKC k L) reg s c g := by
  obtain ⟨⟨hfr, hw⟩, ⟨⟨h1, h2, -, -⟩, -, -⟩, -, -⟩ := hk
  obtain ⟨e, he, rfl, hl, hn, hcr⟩ := ha
  have hnc := hgd e he hl hn
  obtain ⟨y, hy, ya⟩ := hl
  have hy' : s.A[e.guarded]? = some y := hy
  have hym : y.mode = .modify := by
    have := hsi.guarded e he ⟨y, hy, ya⟩; simp only [OptP, hy'] at this; exact this.1
  have hfp : s.flat.afp e.guarded = y.footprint := by simp [S3.afp, hy]
  have hafp : ∀ {j : Nat} {z : Authority}, s.A[j]? = some z → s.flat.afp j = z.footprint :=
    fun hz => by simp [S3.afp, SC.flat, hz]
  have hmo : OptP (s.A[e.guarded]?) (fun y => Mode.modify.le y.mode) False := by
    rw [hy', OptP, hym]; exact Mode.le_refl _
  refine ⟨hnc, ⟨y, hy, ya⟩, hmo,
    ⟨e, he, rfl, ⟨y, hy, ya⟩, hn, hcr⟩, ?_, ?_, fun l h => h, ?_, ?_, ?_⟩
  · exact I2.ancs_active h2 ⟨y, hy, ya⟩
  · intro l hl'
    have hl'' : l ∈ y.footprint := by rw [← hfp]; exact hl'
    exact hw.footprints _ y hy l hl''
  · intro l hl'
    have hl'' : l ∈ y.footprint := by rw [← hfp]; exact hl'
    have hd : descModes s.flat e.guarded l = [] := by
      apply nil_of_forall_not_mem
      intro m hm
      obtain ⟨j, z, hz, za, hlz, hanc, -⟩ := mem_descModes.1 hm
      exact hnc j (List.mem_range.2 (lt_of_getElem? hz))
        ⟨hanc, ⟨z, hz, za⟩, l, by rw [hafp hz]; exact hlz, hl'⟩
    change Allows (effective s.flat e.guarded l) .modify
    rw [effective_eq hy ya hl'', hd, hym]
    simp [effOf, Allows, OptP, Mode.le]
  · intro b _
    unfold OptP; split
    · rename_i z hz
      intro za hnb hcov
      exfalso
      obtain ⟨l, hl', hlz⟩ := hcov
      have hb : b ≠ e.guarded := fun h => hnb (h ▸ List.mem_cons_self ..)
      have hnanc : b ∉ s.flat.ancs e.guarded := fun h => hnb (List.mem_cons_of_mem _ h)
      by_cases hdesc : e.guarded ∈ s.flat.ancs b
      · exact hnc b (List.mem_range.2 (lt_of_getElem? hz)) ⟨hdesc, ⟨z, hz, za⟩, l,
          by rw [hafp hz]; exact hlz, hl'⟩
      · have hl'' : l ∈ y.footprint := by rw [← hfp]; exact hl'
        have := h1 e.guarded b y z l (Ne.symm hb) hy hz ya za hl'' hlz hdesc hnanc
        rw [hym] at this; cases this.1
    · trivial
  · obtain ⟨f, rest, hf⟩ := List.exists_cons_of_ne_nil hc
    simp [SC.view, S3.top, hf]

end Ern.Concurrency
