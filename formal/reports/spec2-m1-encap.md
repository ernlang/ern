# Spec 2, jalon 1 — vérification ciblée : `Encap` et transfert de mutex

Branche `formal/spec2-m1` (commit de départ a8ed17b). Formalisation exploratoire, jamais mergée. Aucune définition ni aucun énoncé existant n'a été modifié ; un seul module de test a été ajouté, `formal/Ern/Concurrency/EncapTraces.lean` (commit 08b44a8), enregistré dans `Ern.lean`. `lake build` réussit sans avertissement ; le `grep` d'`AGENTS.md` ne renvoie rien ; l'audit `collectAxioms` des 658 constantes de théorème `Ern.Concurrency*` ne trouve aucun axiome hors `{propext, Quot.sound}`.

Sources : Spec 1 §§40, 43, 44, 46, 63, 65 ; WC2 (non commitée) C12, C13, C21, C22, S7, S10 ; `formal/reports/spec2-m1.md`.

## 1. Définitions et énoncés cités

Texte exact du dépôt (docstring comprise), avec le fichier et la ligne de la déclaration. `CoveringDesc` et `NoCoveringDesc` sont ajoutés parce que `GrantDiscipline` les utilise.

#### `Encap` — `formal/Ern/Concurrency/SyncLib.lean:296`

```lean
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
```

#### `EncapsulatedTrace` — `formal/Ern/Concurrency/SyncLib.lean:313`

```lean
/-- `EncapsulatedTrace` (WC2 C22, C23: "preservation of library invariants may be conditional on
correct encapsulation, but that condition must be stated"): a run every step of which satisfies
`Encap` in the state where it is taken. -/
inductive EncapsulatedTrace (k : K) (L : MutexLayout) :
    SC × SyncReg → List Label → SC × SyncReg → Prop where
  | nil {st : SC × SyncReg} : EncapsulatedTrace k L st [] st
  | cons {st st₁ st₂ : SC × SyncReg} {lbl : Label} {lbls : List Label} :
      Encap st lbl → LStep k L lbl st st₁ → EncapsulatedTrace k L st₁ lbls st₂ →
      EncapsulatedTrace k L st (lbl :: lbls) st₂
```

#### `LStep` — `formal/Ern/Concurrency/SyncLib.lean:271`

```lean
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
```

#### `Label` — `formal/Ern/Concurrency/SyncLib.lean:257`

```lean
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
```

#### `ControlOf` — `formal/Ern/Concurrency/SyncLib.lean:53`

```lean
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
```

#### `MutexLayout` — `formal/Ern/Concurrency/SyncLib.lean:38`

```lean
/-- Declared field positions of the reference mutex value (WC2 C12, "its declared field
positions"): the position of the field holding `guarded` and that of the controller, among the
ordered children of the mutex value. -/
structure MutexLayout where
  guardedField : Nat
  controlField : Nat
deriving DecidableEq, Repr
```

#### `SyncInv` — `formal/Ern/Concurrency/SyncLib.lean:166`

```lean
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
```

#### `CoveringDesc` — `formal/Ern/Concurrency/SyncLib.lean:144`

```lean
/-- Active descendant of `guarded` covering a protected leaf, a leaf of `footprint(guarded)`
(WC2 C18.2, C22). -/
def CoveringDesc (s : SC) (g j : Nat) : Prop :=
  g ∈ s.flat.ancs j ∧ s.flat.Active j ∧ ∃ l ∈ s.flat.afp j, l ∈ s.flat.afp g
```

#### `NoCoveringDesc` — `formal/Ern/Concurrency/SyncLib.lean:152`

```lean
/-- No active descendant of `guarded` covers a protected leaf (WC2 C18.2, C22). -/
def NoCoveringDesc (s : SC) (g : Nat) : Prop := ∀ j ∈ List.range s.A.length, ¬ CoveringDesc s g j
```

#### `GrantDiscipline` — `formal/Ern/Concurrency/SyncLib.lean:160`

```lean
/-- `GrantDiscipline` (WC2 C22): for every live entry with `grant = none`, no active descendant of
`guarded` covers a protected leaf. -/
def GrantDiscipline (s : SC) (reg : SyncReg) : Prop :=
  ∀ e ∈ reg, e.Live s → e.grant = none → NoCoveringDesc s e.guarded
```

#### `GrantSubtree` — `formal/Ern/Concurrency/SyncPreserve.lean:27`

```lean
/-- Auxiliary invariant, not a WC2 clause (needed by `unlock`, WC2 C17): while the recorded grant
of a live entry is active, every active descendant of `guarded` covering a protected leaf is the
grant or one of its descendants. -/
def GrantSubtree (s : SC) (reg : SyncReg) : Prop :=
  ∀ e ∈ reg, e.Live s → ∀ g, e.grant = some g → s.flat.Active g →
    ∀ j, CoveringDesc s e.guarded j → j = g ∨ g ∈ s.flat.ancs j
```

#### `RegBound` — `formal/Ern/Concurrency/SyncPreserve.lean:33`

```lean
/-- Auxiliary invariant, not a WC2 clause: every registered `guarded` identity exists (an entry
cannot become live by the creation of a fresh authority). -/
def RegBound (s : SC) (reg : SyncReg) : Prop := ∀ e ∈ reg, e.guarded < s.A.length
```

#### `DeriveSyncPre` — `formal/Ern/Concurrency/Sync.lean:33`

```lean
/-- Preconditions of `deriveSync(guarded)` executed by `c` (WC2 C15): those of O1 (Spec 1 §60)
for `source = guarded`, `region = footprint(guarded)`, `mode = Modify`, on the view of `c`, with
`ExercisableAt(source, Modify)` replaced by `K_C.SyncAuthorized(state, guarded, current frame)`. -/
structure DeriveSyncPre (kc : KC) (s : SC) (c g : Nat) : Prop where
  /-- Spec 1 §60.1: `source` is active. -/
  active : (s.view c).Active g
  /-- WC2 C15, replacing `ExercisableAt(s, source, mode)` of Spec 1 §60.1. -/
  authorized : kc.SyncAuthorized s g (s.view c).top
  /-- Spec 1 §60.1: every authority of the origin chain of `source` is active. -/
  chainActive : ∀ x ∈ (s.view c).ancs g, (s.view c).Active x
  /-- Spec 1 §60.2: the leaves of `region` exist. -/
  leaves : ∀ l ∈ (s.view c).afp g, l < s.P.length ∧ isLeaf s.P l
  /-- Spec 1 §60.2: the leaves of `region` belong to the footprint of `source`. -/
  within : ∀ l ∈ (s.view c).afp g, l ∈ (s.view c).afp g
  /-- Spec 1 §60.2: `Modify` does not exceed the effective right of `source` on these leaves. -/
  modeOK : ∀ l ∈ (s.view c).afp g, Allows (effective (s.view c) g l) .modify
  /-- Spec 1 §60.3: the addition preserves I1 (§50). -/
  exclusive : ∀ b ∈ List.range s.A.length, OptP (s.A[b]?) (fun y => y.active = true →
    b ∉ g :: (s.view c).ancs g → (∃ l ∈ (s.view c).afp g, l ∈ y.footprint) →
      y.mode = .observe ∧ Mode.modify = .observe) True
  /-- Spec 1 §60.4: the new holding frame is the live current frame. -/
  frameLive : (s.view c).top ∈ (s.view c).F
```

#### `LibSyncAuthorized` — `formal/Ern/Concurrency/SyncLib.lean:91`

```lean
/-- Instantiation of `K_C.SyncAuthorized(state, guarded, requesting_frame)` by the library (WC2
C14, C25; brief: registry and controller facts only): an entry of the registry for `guarded`
authorizes the requesting frame. -/
def LibSyncAuthorized (L : MutexLayout) (reg : SyncReg) (s : SC) (g f : Nat) : Prop :=
  ∃ e ∈ reg, e.guarded = g ∧ EntryAuth L s e f
```

#### `CtrlRight` — `formal/Ern/Concurrency/SyncLib.lean:70`

```lean
/-- Controller fact (brief, instantiation of `SyncAuthorized`): the frame `f` has an effective
mode on `ControlOf(e)`: some authority exercisable by `f` in a mode at least `Observe` has a
present effective mode on the controller (the authority condition of Spec 1 §68.2). -/
def CtrlRight (L : MutexLayout) (s : SC) (e : SyncEntry) (f : Nat) : Prop :=
  OptP (ControlOf L s e) (fun ctl => ∃ a ∈ List.range s.A.length,
    (s.viewAt f).ExercisableAt a .observe ∧ effective s.flat a ctl ≠ none) False
```

#### `EntryAuth` — `formal/Ern/Concurrency/SyncLib.lean:81`

```lean
/-- Library authorization for an entry (brief: registry and controller facts only): the entry is
live, its grant is available (`grant = none`), and the requesting frame has an effective mode on
its controller. -/
def EntryAuth (L : MutexLayout) (s : SC) (e : SyncEntry) (f : Nat) : Prop :=
  e.Live s ∧ e.grant = none ∧ CtrlRight L s e f
```

#### `SpawnPreBase` — `formal/Ern/Concurrency/Frames.lean:293`

```lean
/-- Preconditions of `spawn` without transmitted value (WC2 C4.1–C4.6), except the second half of
WC2 C4.6 ("the global authority invariants hold in the resulting state"), which the candidate does
not define (see the report). C4.2 (fresh identities) and C4.4 (yield without duplication) hold by
construction of `spawnEff`; C4.7 concerns `spawn` with a value (`Ern.Concurrency.Transfer`). -/
structure SpawnPreBase (s : SC) (c : Nat) (ps : List Nat) (ls : LocalShape) : Prop where
  /-- WC2 C4.1: the creating context and its current frame are live. -/
  creatorLive : s.stk c ≠ []
  /-- WC2 C4.3 (Spec 1 §72.1): every transmitted parameter is an active derived authority held by
  the creating frame. -/
  params : ∀ a ∈ ps, OptP ((s.view c).A[a]?) (fun y => y.active = true ∧
    y.holder = .frame (s.view c).top ∧ y.origin ≠ none) False
  /-- WC2 C4.5 (Spec 1 §72.2): the locals of the new frame form a well-formed shape. -/
  localsOK : ShapeOK s.P.length ls.toShape
  /-- WC2 C4.5, C4 effect (Spec 1 §72.3): origin protection evaluated in the resulting state with
  the new context as the executing context. -/
  originHidden : ∀ p ∈ ps, ParamOriginHidden ((spawnEff s c ps ls).view s.C.length) p
  /-- WC2 C4.6, first half (Spec 1 §72.4): `AnchorOrderHeld` (on `ancestorC`) in the resulting
  state. -/
  anchorOrderHeld : AnchorOrderHeldC (spawnEff s c ps ls)
```

#### `SpawnValPreBase` — `formal/Ern/Concurrency/Transfer.lean:46`

```lean
/-- Clauses of the composite whose state of evaluation is fixed by WC2 C4 and C5: C4.1, C4.3,
C4.5 (Spec 1 §72.2); C5.2; the source side of §63.1 without the right (usability); §63.2, §63.3,
§63.5, §63.6 (first half) and §63.8 on the state where the destination exists, after the spawn
part; the resulting-state conditions §63.6 (second half), §63.7 and §63.9 on the final state
(WC2 C5.4). Not included: the source right of §63.1 and §63.4 (two readings below), the
resulting-state conditions of WC2 C4.5–C4.6 (state of evaluation not fixed by WC2: after the
spawn part or after the composite) and WC2 C4.6, C5.8 ("invariants hold", see the report). -/
structure SpawnValPreBase (k : K) (s : SC) (c : Nat) (ps : List Nat) (ls : LocalShape)
    (src dst : Nat) : Prop where
  /-- WC2 C4.1: the creating context and its current frame are live. -/
  creatorLive : s.stk c ≠ []
  /-- WC2 C4.3: every transmitted parameter is an active derived authority held by the creating
  frame. -/
  params : ∀ a ∈ ps, OptP ((s.view c).A[a]?) (fun y => y.active = true ∧
    y.holder = .frame (s.view c).top ∧ y.origin ≠ none) False
  /-- WC2 C4.5 (Spec 1 §72.2): the locals form a well-formed shape. -/
  localsOK : ShapeOK s.P.length ls.toShape
  /-- WC2 C5.2: the destination is a fresh root local of the new frame. -/
  freshDst : FreshRootLocal s ls dst
  /-- WC2 C5.1 (Spec 1 §63.1): the source is usable. -/
  srcUsable : (s.view c).Usable src
  /-- WC2 C5.5 (Spec 1 §63.2): same shape of ordered subtrees. -/
  sameShape : SameShape (spawnEff s c ps ls).P src dst
  /-- Spec 1 §63.3: all source leaves are `Init`. -/
  srcInit : ∀ l ∈ footprint (spawnEff s c ps ls).P src, (spawnEff s c ps ls).I l = .init
  /-- Spec 1 §63.3, WC2 C5.2: no destination leaf is `Init`. -/
  dstNotInit : ∀ l ∈ footprint (spawnEff s c ps ls).P dst, (spawnEff s c ps ls).I l ≠ .init
  /-- WC2 C5.5 (Spec 1 §63.3): disjoint footprints. -/
  disjoint : ¬ overlap (spawnEff s c ps ls).P src dst
  /-- Spec 1 §63.5: no in-place source leaf is pinned. -/
  notPinned : ∀ l ∈ footprint (spawnEff s c ps ls).P src, ¬ k.Pinned l ∧
    (spawnEff s c ps ls).flat.pin l = false
  /-- Spec 1 §63.6: dependencies of the usable places following the value are valid. -/
  depsValid : ∀ x ∈ movedDeps (spawnEff s c ps ls).flat src, (spawnEff s c ps ls).flat.Active x
  /-- Spec 1 §63.6 re-indexed, WC2 C5.4: `AnchorOrder` (on `ancestorC`) in the final state. -/
  anchorOrder : AnchorOrderC (spawnValEff s c ps ls src dst)
  /-- Spec 1 §63.7 re-indexed, WC2 C5.4: moved held authorities satisfy `AnchorOrderHeld` (on
  `ancestorC`) in the final state. -/
  anchorOrderHeld : ∀ x ∈ List.range (spawnEff s c ps ls).A.length,
    AnchorMoves (spawnEff s c ps ls).flat src x → ∀ q ∈ List.range (spawnEff s c ps ls).P.length,
      (spawnValEff s c ps ls src dst).flat.Usable q →
      OptP ((spawnValEff s c ps ls src dst).A[x]?) (fun y => y.active = true →
        y.holder = .place q → EffAnchorOKC (spawnValEff s c ps ls src dst) x
          ((spawnValEff s c ps ls src dst).flat.pframe q)) True
  /-- Spec 1 §63.8: local self-blocking prevention. -/
  noSelfLock : NoLocalSelfLock (spawnEff s c ps ls).flat src dst
  /-- Spec 1 §63.9: the destination is usable in the final state. -/
  dstUsableAfter : (spawnValEff s c ps ls src dst).flat.Usable dst
```

#### `deriveSync_breaks_i2` — `formal/Ern/Concurrency/Preservation.lean:1873`

```lean
/-- WC2 C15 replaces the conjunct `ExercisableAt(source, Modify)` of Spec 1 §60.1, which bounds
the requested mode by the own mode of the source, by `SyncAuthorized`; §60.2 bounds it only leaf
by leaf. With an opaque `SyncAuthorized` that holds, `deriveSync` from an active `Observe`
authority with an empty footprint (authority 3, derived by frame 0 from the root of static 0)
creates a `Modify` derivative and breaks `I2` (Spec 1 §51: "does not elevate its mode"), from a
state satisfying the invariant. -/
theorem deriveSync_breaks_i2 :
    ∃ (kc : KC) (s s' : SC), KInvCA s ∧ DeriveSyncStep kc s 0 3 (.ok s') ∧ ¬ I2 s'.flat :=
```

#### `acquire_blocked_by_derive` — `formal/Ern/Concurrency/Traces.lean:68`

```lean
/-- Theorem 4, second half (WC2 C22): after the non-encapsulated `derive`, the entry is live with
`grant = none`, `GrantDiscipline` fails, and `acquire` is not enabled. -/
theorem acquire_blocked_by_derive : (⟨1, none⟩ : SyncEntry).Live c1 ∧ ¬ GrantDiscipline c1 reg1 ∧
    ∀ st', ¬ AcquireOk K0 L0 c1 reg1 0 0 st' :=
```

#### `realizability_needs_i1` — `formal/Ern/Concurrency/Traces.lean:112`

```lean
/-- Theorem 5 is false without the kernel invariant: in `bad`, `SyncInv`, `GrantDiscipline` and
the library instantiation of `SyncAuthorized` hold for the current frame of context 0, `I1`
fails, and the preconditions of `deriveSync` fail (Spec 1 §60.3). -/
theorem realizability_needs_i1 : SyncInv L0 bad reg1 ∧ GrantDiscipline bad reg1 ∧
    LibSyncAuthorized L0 reg1 bad 1 (bad.view 0).top ∧ ¬ I1 bad.flat ∧
    ¬ DeriveSyncPre (libKC K0 L0 reg1) bad 0 1 :=
```

#### `shared_controller` — `formal/Ern/Concurrency/Traces.lean:207`

```lean
/-- WC2 C12 requires distinct controller associations for different mutex instances; the
preconditions formalized from WC2 C13 accept `newMutex(1)` then `newMutex(2)`, and both entries
have the same positional controller (place 2). -/
theorem shared_controller : NewMutexOk L0 [] d0 [] 0 1 (d0, [⟨1, none⟩]) ∧
    NewMutexOk L0 [] d0 [⟨1, none⟩] 0 2 (d0, [⟨1, none⟩, ⟨2, none⟩]) ∧
    ControlOf L0 d0 ⟨1, none⟩ = some 2 ∧ ControlOf L0 d0 ⟨2, none⟩ = some 2 :=
```

#### `newMutex_nonleaf_rejected` — `formal/Ern/Concurrency/SyncPreserve.lean:1252`

```lean
open SyncPreserveWitness Ern.MemoryModel.Access.Examples in
/-- Role of the leaf clause of `NewMutexPreBase.control` (WC2 C12, C13.3): in `nm0` the positional
controller of `guarded = 1` is place 2, which is not a leaf; `newMutex(1)` is rejected by that
clause, and registering the entry would break `SyncInv.control`. -/
theorem newMutex_nonleaf_rejected :
    KInvC nm0 ∧ ControlOf nmL nm0 ⟨1, none⟩ = some 2 ∧ ¬ isLeaf nm0.P 2 ∧
    ¬ NewMutexPreBase nmL [] nm0 [] 0 1 ∧ ¬ SyncInv nmL nm0 [⟨1, none⟩] :=
```


## 2. Portée de la clause `transfer` d'`Encap`

La clause (`SyncLib.lean:296`, cas `.kernel _ (.transfer src _)`) compare l'argument `source` d'O4 (le premier argument de `KernelOp.transfer`, la racine du transfert au sens de Spec 1 §63) **par égalité** avec la place qui tient `guarded`, pour chaque entrée vivante. Elle ne parle pas des places dont une partie tient `guarded`. `encap_transfer_iff` (`formal/Ern/Concurrency/EncapTraces.lean:106`, preuve `Iff.rfl`) énonce exactement cette lecture.

Quand `guarded` est tenue par `slot`, partie de `M` :

| Transfert | Admis par `Encap` | Fondement |
|---|---|---|
| `transfer(slot, ·)` | non | `holder(guarded) = .place slot = .place src` |
| `transfer(M, ·)` | oui | `slot ≠ M` |
| `transfer(R, ·)`, `R` racine englobant `M` | oui | `slot ≠ R` (`slot` a pour parent `M`, partie de `R` ; liens de parenté acycliques, Spec 1 §49.2) |
| transfert d'une partie de `slot`, ou d'un autre champ de `M` | oui | source différente de `slot` |

Parmi les transferts qui déplacent `guarded` (Spec 1 §63, effet : les autorités tenues par une partie `r` de la source passent à `corr(r)`, soit `partOf slot src`, c'est-à-dire `src = slot` ou `src` contient `M`), `Encap` exclut donc exactement `src = slot`. Instance concrète : `guarded_in_slot` (`formal/Ern/Concurrency/EncapTraces.lean:112`) et `encap_verdicts` (`formal/Ern/Concurrency/EncapTraces.lean:117`).

## 3. Trace légale

Module `formal/Ern/Concurrency/EncapTraces.lean`, contrat de test `K0` de Spec 1 (`Access/Invariants.lean`), disposition `L0 = ⟨0, 1⟩` (`Traces.lean`), contexte unique 0, frame 0.

- Statiques `est` (`:32`) : `0` = `M` ; `1` = `slot`, `2` = `lock` (`Init`), champs de `M` ; `3` = `T` (`Init`), racine possédée par `M` ; `4` = `M′`, champs `5` = `slot′` et `6` = `lock′` (`Uninit`) ; `7` = `Y`, une feuille (`Uninit`). Autorités racines : `0` de `M`, `1` de `T` (tenue par `M`, Spec 1 §40 `RootHeld`), `2` de `M′`, `3` de `Y`, les autres tenues par la frame 0. `M′` a la même forme que `M` et est dans la même frame.
- `e1` (`:47`) : `derive(1, [3], Modify)` (Spec 1 §60) crée `guarded` = autorité 4 ; `step_derive` (`:73`).
- `e2` (`:50`) : `store(4, slot)` (Spec 1 §65) ; `step_store` (`:77`). Dans `e2`, `guarded` est tenue par `slot` (`guarded_in_slot`).
- `newMutex(4)` (WC2 C13) avec le registre `reg1 = [⟨4, none⟩]` ; contrôleur `ControlOf = 2 = lock` ; `step_newMutex` (`:80`).
- Variante A (`grant = none`) : `eA` (`:56`) = `transfer(M, M′)` depuis `e2`.
- Variante B (grant actif tenu par la frame courante) : `acquire` (WC2 C16) crée le grant 5 (mode `Modify`, origine 4, footprint `[3]`, tenu par la frame 0, frame courante) avec `reg2 = [⟨4, some 5⟩]` (`step_acquire`, `:86`) ; `eB` (`:65`) = `transfer(M, M′)` depuis `e3`.
- Les deux variantes sont des traces encapsulées depuis l'état initial à registre vide : `traceA` (`:129`), `traceB` (`:139`).
- Les préconditions d'O4 ré-indexées (`TransferPreC`, quinze clauses) sont vérifiées par `decide` : `stepA_transfer` (`:91`), `stepB_transfer` (`:95`).

## 4. Verdicts

| | Variante A (`grant = none`) | Variante B (grant 5 actif, frame 0) |
|---|---|---|
| (a) pas O4 `ok` | oui : `stepA_transfer` | oui : `stepB_transfer` |
| (b) admis par `Encap` | oui : `encap_verdicts`, première conjonction | oui : `encap_verdicts`, deuxième conjonction |
| (c) `SyncInv`, `GrantDiscipline`, `GrantSubtree`, `RegBound` après le pas | oui (`SyncState`), avec `KInvCA` et l'entrée vivante : `invA` (`:158`) | oui, avec `KInvCA`, l'entrée vivante et le grant 5 toujours actif et tenu par la frame 0 : `invB` (`:165`) |
| (d) `ControlOf` désigne `lock′` | oui : `guarded` est tenue par `slot′` (5) et `ControlOf = 6` : `controlAB` (`:172`) | oui : idem, `controlAB` |

Fondements :

- (a) Spec 1 §63.1–§63.9, lues par `TransferPreC` (`Frames.lean`) : sources et destinations utilisables avec `Modify` exerçable par la frame 0 (autorités racines 0 et 2) (§63.1, §43) ; même forme (§63.2) ; feuilles de `M` `Init` (`slot` par §65, `lock` déclaré) et de `M′` non `Init` (§63.3) ; aucune dérivée active hors de `M` ne couvre une feuille de `M` : `guarded` et le grant couvrent `T`, pas `slot` ni `lock` (§63.4) ; §63.6–§63.7 sur `ancestorC` : la frame de l'ancre effective (l'autorité racine 1 de `T`, qui suit `M′`, `ownerA` `:180`) est la frame 0, celle de `slot′` et de `M′` (§44, et contrepartie positive de S10 : la destination satisfait les contraintes de l'état résultant) ; §63.8 : `guarded` (footprint `[3]`) ne couvre pas `slot′`, l'autorité 1 ne couvre pas `M′` ; §63.9.
- (b) Clause `transfer` d'`Encap` : `holder(guarded) = .place 1` et `src = 0`.
- (c) Application des théorèmes 2 et 4 aux traces encapsulées (`trace_inv`, `Reachable.lean`, depuis `init_inv`), non un calcul direct. `GrantDiscipline` est vacuement vraie en variante B (`grant ≠ none`) ; `GrantSubtree` y porte sur le grant 5, seule autorité que la trace dérive de `guarded`.
- (d) WC2 C12 (`ControlOf` positionnel : parent de la place qui tient `guarded`, enfant de position `guardedField = 0`, contrôleur en position `controlField = 1`) et l'effet de §63 (`corr` : `slot ↦ slot′`, `lock ↦ lock′`).

Avec S7 (« Legal mutex transfer preserves positional controller association », candidate `ok`), les deux variantes sont des transferts de la valeur mutex `ok`, admis par `Encap`, qui préservent l'association positionnelle.

## 5. Le transfert de la valeur mutex n'est pas exclu ; la clause exclut `transfer(slot, ·)`

`transfer(M, M′)` n'est pas exclu par `Encap` (§§2, 4). La clause `transfer` exclut le seul transfert dont la source est la place qui tient `guarded`, ici `transfer(slot, ·)`.

- **Passages de WC2.** Aucun passage ne nomme l'exclusion de `transfer(slot, ·)`. Les passages qui portent sur l'encapsulation ou sur le transfert de l'association sont : C12, « A legal transfer must preserve or correctly transform this association without fabricating rights. » (WC2, ligne 253) ; C22, « A correct safe abstraction must prevent permitted caller behavior from violating this contract. » (ligne 443) ; C23, « Preservation of library invariants may be conditional on correct encapsulation, but that condition must be stated rather than assumed automatically. » (ligne 455) ; C25, « Ordinary writes to a controller that would break its protocol must be prevented by the safe abstraction's encapsulation contract. » (ligne 481). Aucun ne dit quel transfert l'encapsulation doit exclure.
- **Origine de la clause.** Elle a été écrite avec la définition d'`Encap` (commit 1abd1fc), avant la preuve du théorème 4 (commit bb12ec4), en vue de la préservation de `SyncInv.control` sous `transfer` ; sa docstring dit « the mutex value moves as a whole ».
- **Usage dans la preuve.** Elle n'est utilisée qu'en un point : `ctl_transfer` (`SyncPreserve.lean:805`), hypothèse `henc` (`:807`), appelée par `transfer_preserves` (`:900-901`). Ligne 831, dans le cas `heldIn s.P src y.holder` avec `y.holder = .place hp` (`hp` = la place qui tient `guarded`), elle donne `hne : hp ≠ src`, d'où `partOf m src` pour la valeur mutex `m` = `parentOf hp` et le déplacement des deux champs aux mêmes positions.
- **But qui échoue sans elle.** Dans le sous-cas `hp = src`, le but de `ctl_transfer` est :

  `∃ ctl', ControlOf L (s.set (transferEff (s.view c) src dst)) e = some ctl' ∧ isLeaf (s.set (transferEff (s.view c) src dst)).P ctl'`

  avec, après le pas, `guarded` tenue par `corr(src) = dst`. Ce but est faux en général : `ControlOf` exige `parentOf dst = some m'` et `(kids m')[guardedField]? = some dst`. Contre-exemple au § 6.

## 6. Contre-exemple sans l'exclusion

`slot_transfer_breaks_control` (`formal/Ern/Concurrency/EncapTraces.lean:190`) : depuis `e2`, atteint par la trace encapsulée `traceMutex` (`:149`), donc avec `KInvCA e2` et `SyncState L0 e2 reg1` :

- `transfer(slot, Y)` est un pas `ok` d'O4 ré-indexé (`stepC_transfer`, `:99`, préconditions par `decide`) ;
- `Encap` l'exclut ;
- après le pas, `KInvCA` tient (théorème 2, `lstep_kInvCA`), l'entrée est vivante, `guarded` est tenue par `Y` (place 7), `parentOf Y = none`, `ControlOf L0 eC ⟨4, none⟩ = none`, et `SyncInv L0 eC reg1` est fausse (clause `control`, WC2 C21.3).

Le plus petit ensemble de clauses de WC2 concernées :

- C12, `ControlOf` positionnel : « identifies the synchronization-control leaf through the structure of the value holding `guarded` and its declared field positions » ;
- C12, transfert : « A legal transfer must preserve or correctly transform this association without fabricating rights » ;
- C21.3 : « The associated synchronization controller is valid. »

Côté Spec 1, §63 rend le pas `ok` et §65 rend possible la configuration `guarded` stockée dans `slot`. Fait constaté : O4 accepte `transfer(slot, Y)` ; après ce pas, la référence positionnelle de C12 ne désigne plus de contrôleur.
