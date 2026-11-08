import Ern.Concurrency.Sync

/-!
# Reference synchronization library

Library state separate from `S_C` (WC2 C2, C12), on the pattern of `Ern.MemoryModel.Arena` (Spec
1 §46, §55, §56):

* the registry of `SyncEntry { guarded, grant }` (WC2 C12), liveness of an entry, the positional
  `ControlOf` relationship (WC2 C12) for declared field positions `MutexLayout`;
* `SyncInv` (WC2 C21, items 1, 2, 3 and 5) and `GrantDiscipline` (WC2 C22);
* the library instantiation of `K_C.SyncAuthorized`, limited to registry and controller facts, and
  the contract obligation `SyncSound` of WC2 C14 ("unavailable outside the corresponding valid
  synchronization contract");
* derived operations `newMutex` (C13), `acquire` (C16), `unlock` (C17), `resetLock` (C18);
* labelled library steps, runs, and the encapsulation hypothesis `EncapsulatedTrace` (WC2 C22,
  C23, C25), a predicate on runs, never a precondition of a kernel operation.
-/

namespace Ern.Concurrency

open Ern.MemoryModel.Access

/-! ## Registry (WC2 C12) -/

/-- Synchronization entry (WC2 C12): the protected authority `guarded` and the recorded grant. -/
structure SyncEntry where
  guarded : Nat
  grant : Option Nat
deriving DecidableEq, Repr

/-- Synchronization registry (WC2 C12), library state separate from `S_C`. -/
abbrev SyncReg := List SyncEntry

/-- Declared field positions of the reference mutex value (WC2 C12, "its declared field
positions"): the position of the field holding `guarded` and that of the controller, among the
ordered children of the mutex value. -/
structure MutexLayout where
  guardedField : Nat
  controlField : Nat
deriving DecidableEq, Repr

/-- An entry is live exactly while `guarded` is active (WC2 C12). -/
def SyncEntry.Live (s : SC) (e : SyncEntry) : Prop := s.flat.Active e.guarded

/-- Decidability of liveness of an entry (WC2 C12). -/
instance (s : SC) (e : SyncEntry) : Decidable (e.Live s) := by
  unfold SyncEntry.Live; infer_instance

/-- Positional `ControlOf` (WC2 C12): `guarded` is held by the field `h` at position
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

/-- The `S3` whose current frame is `f` (WC2 C14: `SyncAuthorized` names the requesting frame;
Spec 1 §43 reads the stack only through its top and membership). -/
def SC.viewAt (s : SC) (f : Nat) : S3 :=
  { s.flat with F := f :: s.frames.filter fun g => decide (g ≠ f) }

/-- Controller fact (brief, instantiation of `SyncAuthorized`): the frame `f` has an effective
mode on `ControlOf(e)`: some authority exercisable by `f` in a mode at least `Observe` has a
present effective mode on the controller (the authority condition of Spec 1 §68.2). -/
def CtrlRight (L : MutexLayout) (s : SC) (e : SyncEntry) (f : Nat) : Prop :=
  OptP (ControlOf L s e) (fun ctl => ∃ a ∈ List.range s.A.length,
    (s.viewAt f).ExercisableAt a .observe ∧ effective s.flat a ctl ≠ none) False

/-- Decidability of the controller fact. -/
instance (L : MutexLayout) (s : SC) (e : SyncEntry) (f : Nat) : Decidable (CtrlRight L s e f) := by
  unfold CtrlRight; infer_instance

/-- Library authorization for an entry (brief: registry and controller facts only): the entry is
live, its grant is available (`grant = none`), and the requesting frame has an effective mode on
its controller. -/
def EntryAuth (L : MutexLayout) (s : SC) (e : SyncEntry) (f : Nat) : Prop :=
  e.Live s ∧ e.grant = none ∧ CtrlRight L s e f

/-- Decidability of the library authorization of an entry. -/
instance (L : MutexLayout) (s : SC) (e : SyncEntry) (f : Nat) : Decidable (EntryAuth L s e f) := by
  unfold EntryAuth; infer_instance

/-- Instantiation of `K_C.SyncAuthorized(state, guarded, requesting_frame)` by the library (WC2
C14, C25; brief: registry and controller facts only): an entry of the registry for `guarded`
authorizes the requesting frame. -/
def LibSyncAuthorized (L : MutexLayout) (reg : SyncReg) (s : SC) (g f : Nat) : Prop :=
  ∃ e ∈ reg, e.guarded = g ∧ EntryAuth L s e f

/-- Decidability of the library instantiation. -/
instance (L : MutexLayout) (reg : SyncReg) (s : SC) (g f : Nat) :
    Decidable (LibSyncAuthorized L reg s g f) := by
  unfold LibSyncAuthorized; infer_instance

/-- The contract `K_C` instantiated by the library on the registry `reg` (WC2 C14, C25). -/
def libKC (k : K) (L : MutexLayout) (reg : SyncReg) : KC :=
  { k with SyncAuthorized := LibSyncAuthorized L reg }

/-- Decidability of the instantiated predicate. -/
instance (k : K) (L : MutexLayout) (reg : SyncReg) (s : SC) (g f : Nat) :
    Decidable ((libKC k L reg).SyncAuthorized s g f) :=
  inferInstanceAs (Decidable (LibSyncAuthorized L reg s g f))

/-- Contract obligation of WC2 C14 ("unavailable outside the corresponding valid synchronization
contract"), in state `s` with registry `reg`: `SyncAuthorized` holds only for the `guarded` of a
live entry. -/
def SyncSound (kc : KC) (reg : SyncReg) (s : SC) : Prop :=
  ∀ g f, kc.SyncAuthorized s g f → ∃ e ∈ reg, e.guarded = g ∧ e.Live s

/-- The library instantiation satisfies the obligation of WC2 C14. -/
theorem libKC_sound (k : K) (L : MutexLayout) (reg : SyncReg) (s : SC) :
    SyncSound (libKC k L reg) reg s :=
  fun _ _ ⟨e, he, hg, hl, _⟩ => ⟨e, he, hg, hl⟩

/-- The holder is a usable place (WC2 C12, C21.1). -/
def PlaceUsable (t : S3) : Holder → Prop
  | .place q => t.Usable q
  | .frame _ => False

/-- Decidability of `PlaceUsable` (WC2 C12). -/
instance (t : S3) (h : Holder) : Decidable (PlaceUsable t h) := by
  cases h <;> unfold PlaceUsable <;> infer_instance

/-- Spec 1 §65.3 for an authority held by a place `q`: it covers neither a leaf of `q` nor a leaf
of storage transitively owned by `q` (WC2 C13.5). -/
def StoredOK (P : List Place) (y : Authority) : Prop :=
  match y.holder with
  | .place q => ∀ l ∈ y.footprint, l ∉ footprint P q ∧
      ∀ r ∈ List.range P.length, OwnedIn P q r → l ∉ footprint P r
  | .frame _ => True

/-- Decidability of `StoredOK` (Spec 1 §65.3). -/
instance (P : List Place) (y : Authority) : Decidable (StoredOK P y) := by
  unfold StoredOK; split <;> infer_instance

/-! ## Invariants (WC2 C21, C22) -/

/-- Active descendant of `guarded` covering a protected leaf, a leaf of `footprint(guarded)`
(WC2 C18.2, C22). -/
def CoveringDesc (s : SC) (g j : Nat) : Prop :=
  g ∈ s.flat.ancs j ∧ s.flat.Active j ∧ ∃ l ∈ s.flat.afp j, l ∈ s.flat.afp g

/-- Decidability of `CoveringDesc` (WC2 C22). -/
instance (s : SC) (g j : Nat) : Decidable (CoveringDesc s g j) := by
  unfold CoveringDesc; infer_instance

/-- No active descendant of `guarded` covers a protected leaf (WC2 C18.2, C22). -/
def NoCoveringDesc (s : SC) (g : Nat) : Prop := ∀ j ∈ List.range s.A.length, ¬ CoveringDesc s g j

/-- Decidability of `NoCoveringDesc` (WC2 C22). -/
instance (s : SC) (g : Nat) : Decidable (NoCoveringDesc s g) := by
  unfold NoCoveringDesc; infer_instance

/-- `GrantDiscipline` (WC2 C22): for every live entry with `grant = none`, no active descendant of
`guarded` covers a protected leaf. -/
def GrantDiscipline (s : SC) (reg : SyncReg) : Prop :=
  ∀ e ∈ reg, e.Live s → e.grant = none → NoCoveringDesc s e.guarded

/-- `SyncInv` (WC2 C21), items 1, 2, 3 and 5. Item 4 ("Registry state and the permitted control
operations remain coherent") has no formal content in WC2 and is not formalized (see the
report). -/
structure SyncInv (L : MutexLayout) (s : SC) (reg : SyncReg) : Prop where
  /-- WC2 C21.1: `guarded` is active (liveness), has own mode `Modify`, and is held by a usable
  place. -/
  guarded : ∀ e ∈ reg, e.Live s → OptP (s.A[e.guarded]?) (fun y => y.mode = .modify ∧
    PlaceUsable s.flat y.holder) False
  /-- WC2 C21.2: a recorded grant has origin `guarded` and footprint `footprint(guarded)`. -/
  grant : ∀ e ∈ reg, e.Live s → ∀ g, e.grant = some g → OptP (s.A[g]?) (fun y =>
    y.origin = some e.guarded ∧ ∀ l, l ∈ y.footprint ↔ l ∈ s.flat.afp e.guarded) False
  /-- WC2 C21.3, with the positional `ControlOf` of WC2 C12: the controller exists and is a usable
  leaf. -/
  control : ∀ e ∈ reg, e.Live s → OptP (ControlOf L s e) (fun ctl =>
    s.flat.Usable ctl ∧ isLeaf s.P ctl) False
  /-- WC2 C21.5 (identity uniqueness among live entries, WC2 C13.7). -/
  unique : ∀ (i j : Nat) (e e' : SyncEntry), reg[i]? = some e → reg[j]? = some e' →
    e.Live s → e'.Live s →
    e.guarded = e'.guarded → i = j

/-! ## Derived operations (WC2 C13, C16–C18) -/

/-- Preconditions of `newMutex(guarded)` executed by `c` (WC2 C13), with `adm` the identities used
by the other live administrations (Spec 1 §56). Items C13.3 ("non-falsifiable"), C13.4 and C13.6
are not formalized (see the report). -/
structure NewMutexPreBase (L : MutexLayout) (adm : List Nat) (s : SC) (reg : SyncReg)
    (c g : Nat) : Prop where
  /-- WC2 C13.1: `guarded` is active, of own mode `Modify`, and held by a usable place. -/
  guarded : OptP (s.A[g]?) (fun y => y.active = true ∧ y.mode = .modify ∧
    PlaceUsable s.flat y.holder) False
  /-- WC2 C13.2: ordinary exercisable `Modify` over `guarded`. -/
  exercisable : (s.view c).ExercisableAt g .modify
  /-- WC2 C13.3 with WC2 C12: the positional `ControlOf` designates a controller, and it is a leaf
(WC2 C12: `ControlOf` "identifies the synchronization-control leaf"). -/
  control : OptP (ControlOf L s ⟨g, none⟩) (fun ctl => isLeaf s.P ctl) False
  /-- WC2 C13.5: when `guarded` is stored (derived), Spec 1 §65.3 holds: it covers neither a leaf
  of its holder nor a leaf of storage transitively owned by it. -/
  stored : OptP (s.A[g]?) (fun y => y.origin ≠ none → StoredOK s.P y) False
  /-- WC2 C13.7, Spec 1 §56: `guarded` is not the identity of another live entry. -/
  unique : ∀ e ∈ reg, e.Live s → e.guarded ≠ g
  /-- WC2 C13.7, Spec 1 §56: `guarded` is not the identity of another live administration. -/
  otherAdmin : g ∉ adm
  /-- WC2 C13.8: `GrantDiscipline` is established for the new entry. -/
  available : NoCoveringDesc s g

/-- Decidability of the preconditions of `newMutex` (WC2 C13). -/
instance (L : MutexLayout) (adm : List Nat) (s : SC) (reg : SyncReg) (c g : Nat) :
    Decidable (NewMutexPreBase L adm s reg c g) :=
  decidable_of_iff (OptP (s.A[g]?) (fun y => y.active = true ∧ y.mode = .modify ∧
      PlaceUsable s.flat y.holder) False ∧
    (s.view c).ExercisableAt g .modify ∧
    OptP (ControlOf L s ⟨g, none⟩) (fun ctl => isLeaf s.P ctl) False ∧
    OptP (s.A[g]?) (fun y => y.origin ≠ none → StoredOK s.P y) False ∧
    (∀ e ∈ reg, e.Live s → e.guarded ≠ g) ∧ g ∉ adm ∧ NoCoveringDesc s g)
    ⟨fun ⟨a, b, c, d, e, f, h⟩ => ⟨a, b, c, d, e, f, h⟩,
     fun ⟨a, b, c, d, e, f, h⟩ => ⟨a, b, c, d, e, f, h⟩⟩

/-- `newMutex(guarded)` executed by `c` (WC2 C13): registers the entry `⟨guarded, none⟩`; the
kernel state is unchanged and no authority is created. WC2 C13 states no outcome other than
success; only `ok` is defined. -/
def NewMutexOk (L : MutexLayout) (adm : List Nat) (s : SC) (reg : SyncReg) (c g : Nat)
    (st' : SC × SyncReg) : Prop :=
  s.Live c ∧ NewMutexPreBase L adm s reg c g ∧ st' = (s, reg ++ [⟨g, none⟩])

/-- `acquire` on entry `i` executed by `c` (WC2 C16): with the library instantiation of
`SyncAuthorized` for the entry, `deriveSync(guarded)` and the record of the fresh grant identity
`|A|` in the entry. A taken controller (`grant ≠ none`) leaves `acquire` not enabled; WC2 C16
states no other outcome than success, so only `ok` is defined. -/
def AcquireOk (k : K) (L : MutexLayout) (s : SC) (reg : SyncReg) (c i : Nat)
    (st' : SC × SyncReg) : Prop :=
  s.Live c ∧ ∃ e, reg[i]? = some e ∧ EntryAuth L s e (s.view c).top ∧
    DeriveSyncPre (libKC k L reg) s c e.guarded ∧
    st' = (deriveSyncEff s c e.guarded, reg.set i { e with grant := some s.A.length })

/-- `unlock` of entry `i` executed by `c` (WC2 C17): items 1–4 (item 4 read as the controller
fact of the library instantiation); O3 releases the grant and the registry records
`grant = none`. Item 5 ("a permitted controller update under its declared shared-mutation
discipline") is not formalized (see the report); only `ok` is defined. -/
def UnlockOk (L : MutexLayout) (s : SC) (reg : SyncReg) (c i : Nat) (st' : SC × SyncReg) :
    Prop :=
  s.Live c ∧ ∃ e g, reg[i]? = some e ∧ e.Live s ∧ e.grant = some g ∧ ReleasePre (s.view c) g ∧
    CtrlRight L s e (s.view c).top ∧
    st' = (s.set (releaseEff (s.view c) g), reg.set i { e with grant := none })

/-- `resetLock` of entry `i` executed by `c` (WC2 C18): items 1 and 2; the entry becomes
available; the kernel state is unchanged. Item 3 ("a valid, exclusive recovery contract") is not
formalized and item 4 is an obligation (see the report); only `ok` is defined. -/
def ResetLockOk (s : SC) (reg : SyncReg) (c i : Nat) (st' : SC × SyncReg) : Prop :=
  s.Live c ∧ ∃ e, reg[i]? = some e ∧ (s.view c).ExercisableAt e.guarded .modify ∧
    NoCoveringDesc s e.guarded ∧ st' = (s, reg.set i { e with grant := none })

/-! ## Labelled steps, runs, encapsulation (WC2 C22, C23, C25) -/

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

/-- Labelled `ok` step of the concurrent kernel with the synchronization library (WC2 C2, C4,
C6–C8, C13, C15–C18): kernel and frame steps keep the registry; raw `deriveSync` runs under the
library instantiation of `SyncAuthorized`. -/
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
      DeriveSyncStep (libKC k L reg) s c g (.ok s') → LStep k L (.deriveSync c g) (s, reg) (s', reg)
  | newMutex {s : SC} {reg : SyncReg} {c g : Nat} {adm : List Nat} {st' : SC × SyncReg} :
      NewMutexOk L adm s reg c g st' → LStep k L (.newMutex c g adm) (s, reg) st'
  | acquire {s : SC} {reg : SyncReg} {c i : Nat} {st' : SC × SyncReg} :
      AcquireOk k L s reg c i st' → LStep k L (.acquire c i) (s, reg) st'
  | unlock {s : SC} {reg : SyncReg} {c i : Nat} {st' : SC × SyncReg} :
      UnlockOk L s reg c i st' → LStep k L (.unlock c i) (s, reg) st'
  | resetLock {s : SC} {reg : SyncReg} {c i : Nat} {st' : SC × SyncReg} :
      ResetLockOk s reg c i st' → LStep k L (.resetLock c i) (s, reg) st'

/-- Encapsulation of one step in state `st` (hypothesis on traces, WC2 C22, C23, C25: the
abstraction exposes no safe path compromising its invariant): no inherited `derive` or `split`
from, and no raw `deriveSync` of, the `guarded` of a live entry (only `acquire` derives from it);
no `transfer` whose source is the place holding the `guarded` of a live entry (the mutex value
moves as a whole). -/
def Encap (st : SC × SyncReg) : Label → Prop
  | .kernel _ (.derive src _ _) => ∀ e ∈ st.2, e.Live st.1 → src ≠ e.guarded
  | .kernel _ (.split src _) => ∀ e ∈ st.2, e.Live st.1 → src ≠ e.guarded
  | .kernel _ (.transfer src _) => ∀ e ∈ st.2, e.Live st.1 →
      (st.1.A[e.guarded]?).map (·.holder) ≠ some (.place src)
  | .deriveSync _ g => ∀ e ∈ st.2, e.Live st.1 → g ≠ e.guarded
  | _ => True

/-- Runs of labelled steps. -/
inductive LRun (k : K) (L : MutexLayout) : SC × SyncReg → List Label → SC × SyncReg → Prop where
  | nil {st : SC × SyncReg} : LRun k L st [] st
  | cons {st st₁ st₂ : SC × SyncReg} {lbl : Label} {lbls : List Label} :
      LStep k L lbl st st₁ → LRun k L st₁ lbls st₂ → LRun k L st (lbl :: lbls) st₂

/-- `EncapsulatedTrace` (WC2 C22, C23: "preservation of library invariants may be conditional on
correct encapsulation, but that condition must be stated"): a run every step of which satisfies
`Encap` in the state where it is taken. -/
inductive EncapsulatedTrace (k : K) (L : MutexLayout) :
    SC × SyncReg → List Label → SC × SyncReg → Prop where
  | nil {st : SC × SyncReg} : EncapsulatedTrace k L st [] st
  | cons {st st₁ st₂ : SC × SyncReg} {lbl : Label} {lbls : List Label} :
      Encap st lbl → LStep k L lbl st st₁ → EncapsulatedTrace k L st₁ lbls st₂ →
      EncapsulatedTrace k L st (lbl :: lbls) st₂

/-- An encapsulated trace is a run. -/
theorem EncapsulatedTrace.run {k : K} {L : MutexLayout} {st st' : SC × SyncReg}
    {lbls : List Label} (h : EncapsulatedTrace k L st lbls st') : LRun k L st lbls st' := by
  induction h with
  | nil => exact .nil
  | cons _ hs _ ih => exact .cons hs ih

/-! ## Theorem 1, last part: `SyncAuthorized` and `deriveSync` without live entry (WC2 C14, C24) -/

/-- Theorem 1 (WC2 C14, C24): in a state whose registry has no live entry, the obligation of WC2
C14 makes `K_C.SyncAuthorized` false. Fragment: every state, single-context ones included. -/
theorem syncAuthorized_false {kc : KC} {reg : SyncReg} {s : SC} (hsound : SyncSound kc reg s)
    (hnone : ∀ e ∈ reg, ¬ e.Live s) (g f : Nat) : ¬ kc.SyncAuthorized s g f := fun h => by
  obtain ⟨e, he, -, hl⟩ := hsound g f h
  exact hnone e he hl

/-- Theorem 1 (WC2 C15, C24): in a state whose registry has no live entry, under the obligation
of WC2 C14, `deriveSync` is never enabled. -/
theorem conservative_deriveSync {kc : KC} {reg : SyncReg} {s : SC} (hsound : SyncSound kc reg s)
    (hnone : ∀ e ∈ reg, ¬ e.Live s) (c g : Nat) (s' : SC) : ¬ DeriveSyncStep kc s c g (.ok s') :=
  fun ⟨_, h⟩ => syncAuthorized_false hsound hnone g _ (Guarded.ok_iff.1 h).1.authorized

/-! ## Theorem 6: exclusivity of grants (Spec 1 §50; WC2 C15) -/

/-- An ancestor of an authority whose origin is `g` is `g` or below `g` (Spec 1 §42, §49.5). -/
theorem ancs_le_origin {t : S3} (hw : WF3 t) {b g : Nat} {y : Authority} (hy : t.A[b]? = some y)
    (hyo : y.origin = some g) {x : Nat} (hx : x ∈ t.ancs b) : x ≤ g := by
  have hgb : g < b := hw.origins b y g hy hyo
  have horg : t.org b = some g := by simp [S3.org, hy, hyo]
  rw [S3.ancs, chain_cons horg hgb] at hx
  rcases List.mem_cons.1 hx with rfl | hx
  · exact Nat.le_refl _
  · exact Nat.le_of_lt (chain_lt hx)

/-- Theorem 6 (Spec 1 §50, I1; WC2 C15, C21.2): two distinct active authorities of own mode
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

/-! ## Theorem 5: realizability (WC2 C25) -/

/-- Theorem 5 (WC2 C14, C15, C25): under `SyncInv` and `GrantDiscipline`, and the kernel invariant
re-indexed (`KInvC`: `WF3`, `I1` and `I2` are used), the library instantiation of
`SyncAuthorized` (registry and controller facts only) for the current frame of a live context
entails that no active descendant of `guarded` covers a protected leaf and all the preconditions
of `deriveSync`, in particular I1 for the full-footprint grant (§60.3) and the validity of the
origin chain (§60.1). Fragment: states satisfying `KInvC`. -/
theorem realizability {k : K} {L : MutexLayout} {reg : SyncReg} {s : SC} {c g : Nat}
    (hk : KInvC s) (hsi : SyncInv L s reg) (hgd : GrantDiscipline s reg) (hc : s.stk c ≠ [])
    (ha : LibSyncAuthorized L reg s g (s.view c).top) :
    NoCoveringDesc s g ∧ DeriveSyncPre (libKC k L reg) s c g := by
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
  refine ⟨hnc, ⟨y, hy, ya⟩, ⟨e, he, rfl, ⟨y, hy, ya⟩, hn, hcr⟩, ?_, ?_, fun l h => h, ?_, ?_, ?_⟩
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
