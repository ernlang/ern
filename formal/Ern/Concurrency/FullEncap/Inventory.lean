import Ern.Concurrency.MutexReal.Final

/-!
# Complete encapsulation: the inventory of right premises and their guard-free forms

Brief of milestone 4, slice 3 (WC5.2 C22 item 6, `OB-C28`; `corpus-spec2-m3.md` v13 §2 duodecies).
C22 item 6 requires every exercisability judgment (Spec 1 §43, `ExercisableAt`) and every right
over a place (`HasRight`) on which an admitted step depends to have a justification whose
authority-holder chain excludes the `guarded` authority of every live entry, including the rights
read in intermediate or resulting states of a composite step.

* `Prem` is the inventory: for each of the 28 step kinds, the conjunction of the right premises of
  its precondition (the fields that read `ExercisableAt`, `HasRight`, `HolderRight`, `CtrlRight`,
  `MetaRight` or a `Grounds` clause), each in the state where the precondition reads it, the
  internal phases of `issue` and `reset`, the transfer phases of the by-value `spawn` and the two
  amended premises (WC5.2 C13 item 11, C18 item 4) included. A negative reading
  (`ParamOriginHidden`, Spec 1 §72.3: an origin exercisable in no mode) is not a right the step
  relies on and is not listed: its guard-free reading is implied by the kernel precondition.
* `PremG` is the same conjunction with `Exer5` in place of `ExercisableAt` (the guard-free form),
  with the `resetLock` exception of C22 item 6 for the check of C18 item 1.
* `EncapFull` is `Encap7` and `PremG`; `RunFull` is the run of `EncapFull` steps.

Every guard-free form entails its original premise (`premG_prem`); every `ok` step whose amended
clauses hold satisfies the inventory (`prem_of_step`); every `RunFull` is a final amended
execution (`runFull_runAmF`). The existing definitions are unchanged.
-/

set_option autoImplicit false

namespace Ern.Concurrency.FullEncap

open Ern.MemoryModel Ern.MemoryModel.Access Ern.Concurrency Ern.Concurrency.MutexReal

/-! ## Primitive guard-free forms -/

/-- `Exer5` entails `ExercisableAt` (Spec 1 §43) from the current frame of `c`: the guard-free
holder chain is a holder chain. -/
theorem exercisable_of_exer5 {s : SC} {reg : SyncReg} {c a : Nat} {m : Mode}
    (h : Exer5 s reg c a m) : (s.view c).ExercisableAt a m := by
  induction h with
  | base _ hy ha hm hf => exact .base hy ha hm hf
  | held _ hy ha hm hp _ hc ih => exact .held hy ha hm hp ih hc

/-- `HasRight5` entails `HasRight` (Spec 1 §43) from the current frame of `c`. -/
theorem hasRight_of_hasRight5 {st : SC × SyncReg} {c : Nat} {m : Mode} {q : Nat}
    (h : HasRight5 st c m q) : HasRight (st.1.view c) m q := by
  obtain ⟨a, ha, hx, hall⟩ := h
  exact ⟨a, ha, exercisable_of_exer5 hx, hall⟩

/-- `Grounds` (Spec 1 §43; §63.4, §69.2, §70.3: "the exercisable authority on which that right
rests") with `Exer5` in place of `ExercisableAt`, from the current frame of `c` (WC5.2 C22 item 6,
the source right of `transfer`, the place right of `endUse` and `free`). -/
def GroundsG (st : SC × SyncReg) (c : Nat) (m : Mode) (q g : Nat) : Prop :=
  g ∈ List.range st.1.A.length ∧ Exer5 st.1 st.2 c g m ∧
    ∀ l ∈ footprint st.1.P q, Allows (effective st.1.flat g l) m

/-- Decidability of `GroundsG`. -/
instance (st : SC × SyncReg) (c : Nat) (m : Mode) (q g : Nat) :
    Decidable (GroundsG st c m q g) := by
  unfold GroundsG; infer_instance

/-- `GroundsG` entails `Grounds` from the current frame of `c`. -/
theorem grounds_of_groundsG {st : SC × SyncReg} {c : Nat} {m : Mode} {q g : Nat}
    (h : GroundsG st c m q g) : Grounds (st.1.view c) m q g :=
  ⟨h.1, exercisable_of_exer5 h.2.1, h.2.2⟩

/-- `HolderRight` (Spec 1 §62.2) with `HasRight5` in its place case; the frame case is that of
`HolderRight`, the current frame of `c` (WC5.2 C22 item 6: a frame holder has no holder chain). -/
def HolderRightG (st : SC × SyncReg) (c : Nat) : Holder → Prop
  | .frame f => f = (st.1.view c).top
  | .place p => HasRight5 st c .modify p

/-- Decidability of `HolderRightG`. -/
instance (st : SC × SyncReg) (c : Nat) (h : Holder) : Decidable (HolderRightG st c h) := by
  cases h <;> unfold HolderRightG <;> infer_instance

/-- `HolderRightG` entails `HolderRight` from the current frame of `c`. -/
theorem holderRight_of_holderRightG {st : SC × SyncReg} {c : Nat} {h : Holder}
    (hr : HolderRightG st c h) : HolderRight (st.1.view c) h := by
  cases h with
  | frame f => exact hr
  | place p => exact hasRight_of_hasRight5 hr

/-- `ExercisableAt` reads the frames only through the current frame (Spec 1 §43): the frame
`(s.view c).top` exercises from `s.viewAt` as from `s.view c`. -/
theorem exercisable_viewAt {s : SC} {c a : Nat} {m : Mode}
    (h : (s.view c).ExercisableAt a m) : (s.viewAt (s.view c).top).ExercisableAt a m := by
  induction h with
  | base hy ha hm hf => exact .base hy ha hm hf
  | held hy ha hm hp _ hc ih => exact .held hy ha hm hp ih hc

/-- `CtrlRight5` entails `CtrlRight` (WC5.2 C14 item 3, C17 item 4, C18 item 4; Spec 1 §68.2) of
the current frame of `c`. -/
theorem ctrlRight_of_ctrlRight5 {L : MutexLayout} {st : SC × SyncReg} {e : SyncEntry} {c : Nat}
    (h : CtrlRight5 L st e c) : CtrlRight L st.1 e (st.1.view c).top := by
  unfold CtrlRight5 at h; unfold CtrlRight
  revert h
  cases ControlOf L st.1 e with
  | none => exact id
  | some ctl =>
    rintro ⟨a, ha, hx, he⟩
    exact ⟨a, ha, exercisable_viewAt (exercisable_of_exer5 hx), he⟩

/-- `MetaRight` (Spec 1 §36, §77.1, §78.1) with `HasRight5` over the arena value; `False` when the
arena value does not exist, as in `MetaRight` (unlike `MetaRight5`). -/
def MetaRightG (st : SC × SyncReg) (c : Nat) (E : Arena.ArenaEntry) : Prop :=
  OptP (Arena.arenaValue st.1.flat E) (fun v => HasRight5 st c .modify v) False

/-- Decidability of `MetaRightG`. -/
instance (st : SC × SyncReg) (c : Nat) (E : Arena.ArenaEntry) : Decidable (MetaRightG st c E) := by
  unfold MetaRightG; infer_instance

/-- `MetaRightG` entails `MetaRight` from the current frame of `c`. -/
theorem metaRight_of_metaRightG {st : SC × SyncReg} {c : Nat} {E : Arena.ArenaEntry}
    (h : MetaRightG st c E) : Arena.MetaRight (st.1.view c) E := by
  unfold MetaRightG at h; unfold Arena.MetaRight
  have h0 : Arena.arenaValue (st.1.view c) E = Arena.arenaValue st.1.flat E := rfl
  rw [h0]; revert h
  cases Arena.arenaValue st.1.flat E with
  | none => exact id
  | some v => exact hasRight_of_hasRight5

/-- WC5.2 C13 item 11 (`NewMutexRight`) with `Exer5` in place of `ExercisableAt`. -/
def NewMutexRightG (L : MutexLayout) (st : SC × SyncReg) (c g : Nat) : Prop :=
  OptP (ControlOf L st.1 ⟨g, none⟩) (fun ctl => ∃ a ∈ List.range st.1.A.length,
    Exer5 st.1 st.2 c a .modify ∧ effective st.1.flat a ctl = some .modify) False

/-- Decidability of `NewMutexRightG`. -/
instance (L : MutexLayout) (st : SC × SyncReg) (c g : Nat) :
    Decidable (NewMutexRightG L st c g) := by
  unfold NewMutexRightG; infer_instance

/-- `NewMutexRightG` entails `NewMutexRight` (WC5.2 C13 item 11). -/
theorem newMutexRight_of_G {L : MutexLayout} {st : SC × SyncReg} {c g : Nat}
    (h : NewMutexRightG L st c g) : NewMutexRight L st.1 c g := by
  unfold NewMutexRightG at h; unfold NewMutexRight
  revert h
  cases ControlOf L st.1 ⟨g, none⟩ with
  | none => exact id
  | some ctl =>
    rintro ⟨a, ha, hx, he⟩
    exact ⟨a, ha, exercisable_of_exer5 hx, he⟩

/-- The check of WC5.2 C18 item 1 under the `resetLock` exception of C22 item 6:
`ExercisableAt(entry.guarded, Modify)` for entry `i` by a holder chain containing the `guarded`
of no live entry other than entry `i`, that is `Exer5` over the registry without entry `i`. The
subject `entry.guarded` is exempt; the right on the holding `slot` is checked against every other
live entry. -/
def ResetExerG (st : SC × SyncReg) (c i : Nat) : Prop :=
  OptP (st.2[i]?) (fun e => Exer5 st.1 (st.2.eraseIdx i) c e.guarded .modify) False

/-- Decidability of `ResetExerG`. -/
instance (st : SC × SyncReg) (c i : Nat) : Decidable (ResetExerG st c i) := by
  unfold ResetExerG; infer_instance

/-- The guard-free form of the source-access clause of `transfer` (Spec 1 §63.4) and of each
transfer phase of the by-value `spawn` (WC5.2 C5 item 4): some authority grounding the `Modify`
right over the source by a guard-free chain, and every active derived authority held outside the
source covering a source leaf is on its origin chain. -/
def OutsideG (st : SC × SyncReg) (c src : Nat) : Prop :=
  ∃ g ∈ List.range st.1.A.length, GroundsG st c .modify src g ∧
    ∀ j ∈ List.range st.1.A.length, ActiveDerivedOutside (st.1.view c) src j →
      RightChain (st.1.view c) g j

/-- Decidability of `OutsideG`. -/
instance (st : SC × SyncReg) (c src : Nat) : Decidable (OutsideG st c src) := by
  unfold OutsideG; infer_instance

/-- The guard-free form of the access clause of `endUse` (Spec 1 §69.2). -/
def EndAccessG (st : SC × SyncReg) (c p : Nat) : Prop :=
  ∃ g ∈ List.range st.1.A.length, GroundsG st c .modify p g ∧
    ∀ j ∈ List.range st.1.A.length, RightChain (st.1.view c) g j ∨ EndUseAccessOK (st.1.view c) p j

/-- Decidability of `EndAccessG`. -/
instance (st : SC × SyncReg) (c p : Nat) : Decidable (EndAccessG st c p) := by
  unfold EndAccessG; infer_instance

/-- The guard-free form of the access clause of `free` (Spec 1 §70.3). -/
def FreeAccessG (st : SC × SyncReg) (c p : Nat) : Prop :=
  ∃ g ∈ List.range st.1.A.length, GroundsG st c .modify p g ∧
    ∀ j ∈ List.range st.1.A.length, RightChain (st.1.view c) g j ∨ FreeAccessOK (st.1.view c) p j

/-- Decidability of `FreeAccessG`. -/
instance (st : SC × SyncReg) (c p : Nat) : Decidable (FreeAccessG st c p) := by
  unfold FreeAccessG; infer_instance

/-- The guard-free form of the library authorization `K_C.SyncAuthorized(state, registry, g,
current frame)` (WC5.2 C14 items 1–3, C15 item 3): an entry of the registry with identity `g`, live,
with `grant = none`, on whose controller `c` has `CtrlRight5`. -/
def AuthG (L : MutexLayout) (st : SC × SyncReg) (c g : Nat) : Prop :=
  ∃ e ∈ st.2, e.guarded = g ∧ e.Live st.1 ∧ e.grant = none ∧ CtrlRight5 L st e c

/-- Decidability of `AuthG`. -/
instance (L : MutexLayout) (st : SC × SyncReg) (c g : Nat) : Decidable (AuthG L st c g) := by
  unfold AuthG; infer_instance

/-- The guard-free forms of the right premises of the transfer phases of the by-value `spawn`
(WC5.2 C5 phase 2, C5 items 1 and 4; Spec 1 §63.1, §63.4): for each phase, in the declared order,
on the state produced by the earlier phases, the source right and the source-access clause. -/
def ValRightsG (reg : SyncReg) (c : Nat) : SC → List (Nat × Nat) → Prop
  | _, [] => True
  | t, v :: vs => (HasRight5 (t, reg) c .modify v.1 ∧ OutsideG (t, reg) c v.1) ∧
      ValRightsG reg c (transferEffC t c v.1 v.2) vs

/-- Decidability of `ValRightsG`. -/
instance instDecidableValRightsG (reg : SyncReg) (c : Nat) :
    (t : SC) → (vs : List (Nat × Nat)) → Decidable (ValRightsG reg c t vs)
  | _, [] => isTrue trivial
  | t, v :: vs =>
    haveI := instDecidableValRightsG reg c (transferEffC t c v.1 v.2) vs
    inferInstanceAs (Decidable ((HasRight5 (t, reg) c .modify v.1 ∧ OutsideG (t, reg) c v.1) ∧ _))

/-! ## The inventory -/

/-- The state after the internal `split` of `issue(arena, region, dst)` by `c` (Spec 1 §77,
Part XIV; `IssueStepC`): the block is `|A|`, held by the current frame. -/
def issueMid (s : SC) (c : Nat) (E : Arena.ArenaEntry) (region : List Nat) : SC :=
  s.set (splitEff (s.view c) E.internal [region])

/-- The state after the internal `derive` of `reset(arena)` by `c` (Spec 1 §78, Part XIV;
`Arena.ResetD`): the derived authority is `|A|`, held by the current frame. -/
def resetMid (s : SC) (c : Nat) (E : Arena.ArenaEntry) : SC :=
  s.set (deriveEff (s.view c) E.internal (footprint s.P E.storage) .modify)

/-- The original right premises of the source-access clause of `transfer` (Spec 1 §63.4). -/
def Outside (s : SC) (c src : Nat) : Prop :=
  ∃ g ∈ List.range (s.view c).A.length, Grounds (s.view c) .modify src g ∧
    ∀ j ∈ List.range (s.view c).A.length, ActiveDerivedOutside (s.view c) src j →
      RightChain (s.view c) g j

/-- The original right premises of the transfer phases of the by-value `spawn` (WC5.2 C5.2;
`ValTransferPre.srcRight`, `.noOutsideDerived`). -/
def ValRights (c : Nat) : SC → List (Nat × Nat) → Prop
  | _, [] => True
  | t, v :: vs => (HasRight (t.view c) .modify v.1 ∧ Outside t c v.1) ∧
      ValRights c (transferEffC t c v.1 v.2) vs

/-- The inventory of right premises (brief of slice 3, task 1), read on the original definitions,
each in the state where the precondition reads it:

* `derive`, `split`, `read3`, `write3`, `writeShared`: the exercise of the authority argument
  (Spec 1 §60.1, §61.1, §66.2, §67.1, §68.2);
* `release`: `HolderRight` of the holder (§62.2);
* `transfer`: the source and destination rights (§63.1) and the source-access clause (§63.4);
* `depend` (§64.1), `pin` (§74), `unpin` (§75): the place right;
* `endUse` (§69.1, §69.2), `free` (§70.3): the place right and the access clause;
* `alloc`: the provider right or its `writeShared` branch (§71.2), the owner right (§71.3);
* `store`: the target right before (§65.2) and in the resulting state (§65.5);
* raw `deriveSync`: `SyncAuthorized` (WC5.2 C15 item 3, C14 items 1–3);
* `newMutex`: C13 item 2 and C13 item 11 (WC5.2);
* `acquire`: C14 item 3 for the entry and `SyncAuthorized` within `deriveSync` (C15 item 3);
* `unlock`: §62.2 for the grant (C17 item 2) and C17 item 4;
* `resetLock`: C18 item 1 and C18 item 4;
* by-value `spawn`: the source right and source-access clause of each transfer phase (C5.2);
* `newArena`: §76.1 and §76.2;
* `issue`: `MetaRight` (§77.1), the destination right (§77.2), the exercise of the internal
  `split` (§61.1), the target rights of the internal `store` in its state and resulting state
  (§65.2, §65.5);
* `reset`: the exercise of the internal `derive` (§60.1) and `HolderRight` of the internal
  `release` in the intermediate state (§62.2);
* `enterFrame`, `exitFrame`, `spawn`, `terminate`, `join`: no positive right premise. -/
def Prem (k : K) (L : MutexLayout) (st : SC × SyncReg × ArenaReg) : Label → Prop
  | .kernel c (.derive a _ m) => (st.1.view c).ExercisableAt a m
  | .kernel c (.split a _) => (st.1.view c).ExercisableAt a .modify
  | .kernel c (.release a) => OptP (st.1.A[a]?) (fun y => HolderRight (st.1.view c) y.holder) False
  | .kernel c (.transfer src dst) => HasRight (st.1.view c) .modify src ∧
      HasRight (st.1.view c) .modify dst ∧ Outside st.1 c src
  | .kernel c (.depend q _) => HasRight (st.1.view c) .modify q
  | .kernel c (.read a _) => (st.1.view c).ExercisableAt a .observe
  | .kernel c (.write a _) => (st.1.view c).ExercisableAt a .modify
  | .kernel c (.writeShared a _) => (st.1.view c).ExercisableAt a .observe
  | .kernel c (.pin p) => HasRight (st.1.view c) .modify p
  | .kernel c (.unpin o) =>
      OptP (st.1.pins[o]?) (fun ob => HasRight (st.1.view c) .modify ob.place) False
  | .kernel c (.endUse p) => HasRight (st.1.view c) .modify p ∧
      ∃ g ∈ List.range (st.1.view c).A.length, Grounds (st.1.view c) .modify p g ∧
        ∀ j ∈ List.range (st.1.view c).A.length,
          RightChain (st.1.view c) g j ∨ EndUseAccessOK (st.1.view c) p j
  | .kernel c (.free p _) => HasRight (st.1.view c) .modify p ∧
      ∃ g ∈ List.range (st.1.view c).A.length, Grounds (st.1.view c) .modify p g ∧
        ∀ j ∈ List.range (st.1.view c).A.length,
          RightChain (st.1.view c) g j ∨ FreeAccessOK (st.1.view c) p j
  | .kernel c (.alloc pr ow _) => (HasRight (st.1.view c) .modify pr ∨
      ∃ via ∈ List.range (st.1.view c).A.length,
        WriteSharedPre k (st.1.view c) via (footprint (st.1.view c).P pr)) ∧
      HasRight (st.1.view c) .modify ow
  | .kernel c (.store a p) => HasRight (st.1.view c) .modify p ∧
      HasRight (storeEff (st.1.view c) a p) .modify p
  | .deriveSync c g => LibSyncAuthorized L st.2.1 st.1 g (st.1.view c).top
  | .newMutex c g => (st.1.view c).ExercisableAt g .modify ∧ NewMutexRight L st.1 c g
  | .acquire c i => OptP (st.2.1[i]?) (fun e => CtrlRight L st.1 e (st.1.view c).top ∧
      LibSyncAuthorized L st.2.1 st.1 e.guarded (st.1.view c).top) False
  | .unlock c i => OptP (st.2.1[i]?) (fun e => OptP e.grant (fun g =>
      OptP (st.1.A[g]?) (fun y => HolderRight (st.1.view c) y.holder) False) False ∧
      CtrlRight L st.1 e (st.1.view c).top) False
  | .resetLock c i => OptP (st.2.1[i]?) (fun e => (st.1.view c).ExercisableAt e.guarded .modify ∧
      CtrlRight L st.1 e (st.1.view c).top) False
  | .spawnVal c _ ls vs => ValRights c (spawnCreate st.1 c ls) vs
  | .newArena c storage internal => HasRight (st.1.view c) .modify storage ∧
      (st.1.view c).ExercisableAt internal .modify
  | .issue c i region dst => OptP (st.2.2[i]?) (fun E => Arena.MetaRight (st.1.view c) E ∧
      HasRight (st.1.view c) .modify dst ∧ (st.1.view c).ExercisableAt E.internal .modify ∧
      HasRight ((issueMid st.1 c E region).view c) .modify dst ∧
      HasRight (storeEff ((issueMid st.1 c E region).view c) st.1.A.length dst) .modify dst) False
  | .reset c i => OptP (st.2.2[i]?) (fun E => (st.1.view c).ExercisableAt E.internal .modify ∧
      OptP ((resetMid st.1 c E).A[st.1.A.length]?)
        (fun y => HolderRight ((resetMid st.1 c E).view c) y.holder) False) False
  | _ => True

/-- The guard-free forms of the inventory (brief of slice 3, "Forme sans `guarded`"): each premise
of `Prem` with `Exer5` in place of `ExercisableAt`, in the state where the precondition reads it,
the registry being that of the step; for `resetLock`, the check of C18 item 1 under the exception
of WC5.2 C22 item 6 (`ResetExerG`). -/
def PremG (k : K) (L : MutexLayout) (st : SC × SyncReg × ArenaReg) : Label → Prop
  | .kernel c (.derive a _ m) => Exer5 st.1 st.2.1 c a m
  | .kernel c (.split a _) => Exer5 st.1 st.2.1 c a .modify
  | .kernel c (.release a) =>
      OptP (st.1.A[a]?) (fun y => HolderRightG (st.1, st.2.1) c y.holder) False
  | .kernel c (.transfer src dst) => HasRight5 (st.1, st.2.1) c .modify src ∧
      HasRight5 (st.1, st.2.1) c .modify dst ∧ OutsideG (st.1, st.2.1) c src
  | .kernel c (.depend q _) => HasRight5 (st.1, st.2.1) c .modify q
  | .kernel c (.read a _) => Exer5 st.1 st.2.1 c a .observe
  | .kernel c (.write a _) => Exer5 st.1 st.2.1 c a .modify
  | .kernel c (.writeShared a _) => Exer5 st.1 st.2.1 c a .observe
  | .kernel c (.pin p) => HasRight5 (st.1, st.2.1) c .modify p
  | .kernel c (.unpin o) =>
      OptP (st.1.pins[o]?) (fun ob => HasRight5 (st.1, st.2.1) c .modify ob.place) False
  | .kernel c (.endUse p) => HasRight5 (st.1, st.2.1) c .modify p ∧ EndAccessG (st.1, st.2.1) c p
  | .kernel c (.free p _) => HasRight5 (st.1, st.2.1) c .modify p ∧ FreeAccessG (st.1, st.2.1) c p
  | .kernel c (.alloc pr ow _) => (HasRight5 (st.1, st.2.1) c .modify pr ∨
      ∃ via ∈ List.range st.1.A.length, WriteSharedPre k (st.1.view c) via (footprint st.1.P pr) ∧
        Exer5 st.1 st.2.1 c via .observe) ∧ HasRight5 (st.1, st.2.1) c .modify ow
  | .kernel c (.store a p) => HasRight5 (st.1, st.2.1) c .modify p ∧
      HasRight5 (storeEffC st.1 c a p, st.2.1) c .modify p
  | .deriveSync c g => AuthG L (st.1, st.2.1) c g
  | .newMutex c g => Exer5 st.1 st.2.1 c g .modify ∧ NewMutexRightG L (st.1, st.2.1) c g
  | .acquire c i => OptP (st.2.1[i]?) (fun e => CtrlRight5 L (st.1, st.2.1) e c ∧
      AuthG L (st.1, st.2.1) c e.guarded) False
  | .unlock c i => OptP (st.2.1[i]?) (fun e => OptP e.grant (fun g =>
      OptP (st.1.A[g]?) (fun y => HolderRightG (st.1, st.2.1) c y.holder) False) False ∧
      CtrlRight5 L (st.1, st.2.1) e c) False
  | .resetLock c i => ResetExerG (st.1, st.2.1) c i ∧
      OptP (st.2.1[i]?) (fun e => CtrlRight5 L (st.1, st.2.1) e c) False
  | .spawnVal c _ ls vs => ValRightsG st.2.1 c (spawnCreate st.1 c ls) vs
  | .newArena c storage internal => HasRight5 (st.1, st.2.1) c .modify storage ∧
      Exer5 st.1 st.2.1 c internal .modify
  | .issue c i region dst => OptP (st.2.2[i]?) (fun E => MetaRightG (st.1, st.2.1) c E ∧
      HasRight5 (st.1, st.2.1) c .modify dst ∧ Exer5 st.1 st.2.1 c E.internal .modify ∧
      HasRight5 (issueMid st.1 c E region, st.2.1) c .modify dst ∧
      HasRight5 (storeEffC (issueMid st.1 c E region) c st.1.A.length dst, st.2.1) c .modify dst)
      False
  | .reset c i => OptP (st.2.2[i]?) (fun E => Exer5 st.1 st.2.1 c E.internal .modify ∧
      OptP ((resetMid st.1 c E).A[st.1.A.length]?)
        (fun y => HolderRightG (resetMid st.1 c E, st.2.1) c y.holder) False) False
  | _ => True

/-- Decidability of `PremG`. -/
instance (k : K) [DecidablePred k.SharedMutable] (L : MutexLayout) (st : SC × SyncReg × ArenaReg)
    (lbl : Label) : Decidable (PremG k L st lbl) := by
  unfold PremG; split <;> infer_instance

/-- The complete encapsulation of a step from `st` to `st'` (brief of slice 3): `Encap7` and the
guard-free forms of the inventory. -/
def EncapFull (k : K) (L : MutexLayout) (st : SC × SyncReg × ArenaReg) (lbl : Label)
    (st' : SC × SyncReg × ArenaReg) : Prop :=
  Encap7 k L st lbl st' ∧ PremG k L st lbl

/-- `RunFull` (brief of slice 3): a run with named states every step of which satisfies
`EncapFull` and is an `ok` step. -/
def RunFull (k : K) (L : MutexLayout) (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) :
    Prop :=
  ∀ i (h : i < lbls.length), EncapFull k L (σ i) lbls[i] (σ (i + 1)) ∧
    LStep k L lbls[i] (σ i) (σ (i + 1))

/-! ## Each guard-free form entails its premise -/

/-- `OutsideG` entails the source-access clause of `transfer` (Spec 1 §63.4). -/
theorem outside_of_outsideG {s : SC} {reg : SyncReg} {c src : Nat} (h : OutsideG (s, reg) c src) :
    Outside s c src := by
  obtain ⟨g, hg, hgr, hall⟩ := h
  exact ⟨g, hg, grounds_of_groundsG hgr, hall⟩

/-- `ValRightsG` entails the right premises of the transfer phases (WC5.2 C5.2). -/
theorem valRights_of_G {reg : SyncReg} {c : Nat} :
    ∀ (t : SC) (vs : List (Nat × Nat)), ValRightsG reg c t vs → ValRights c t vs
  | _, [], _ => trivial
  | _, _ :: vs, ⟨⟨hr, ho⟩, h⟩ =>
    ⟨⟨hasRight_of_hasRight5 hr, outside_of_outsideG ho⟩, valRights_of_G _ vs h⟩

/-- `AuthG` entails the library authorization (WC5.2 C14 items 1–3, C15 item 3). -/
theorem auth_of_authG {L : MutexLayout} {st : SC × SyncReg} {c g : Nat} (h : AuthG L st c g) :
    LibSyncAuthorized L st.2 st.1 g (st.1.view c).top := by
  obtain ⟨e, he, hg, hl, hn, hc⟩ := h
  exact ⟨e, he, hg, hl, hn, ctrlRight_of_ctrlRight5 hc⟩

/-- The view of `c` after a `store` executed by `c` is the `store` on the view (WC5.2 C2). -/
theorem view_storeEffC (s : SC) (c a p : Nat) :
    (storeEffC s c a p).view c = storeEff (s.view c) a p :=
  SC.view_set (by unfold storeEff; split <;> rfl)

/-- Brief of slice 3, task 1: every guard-free form entails the premise of the inventory it
replaces (Spec 1 §43: `Exer5` is an `ExercisableAt` by a restricted holder chain). -/
theorem premG_prem {k : K} {L : MutexLayout} {st : SC × SyncReg × ArenaReg} {lbl : Label}
    (h : PremG k L st lbl) : Prem k L st lbl := by
  obtain ⟨s, reg, ar⟩ := st
  cases lbl with
  | kernel c op =>
    cases op with
    | derive => exact exercisable_of_exer5 h
    | split => exact exercisable_of_exer5 h
    | release a =>
      simp only [PremG, Prem] at h ⊢
      revert h
      cases s.A[a]? with
      | none => exact id
      | some y => exact holderRight_of_holderRightG
    | transfer =>
      exact ⟨hasRight_of_hasRight5 h.1, hasRight_of_hasRight5 h.2.1, outside_of_outsideG h.2.2⟩
    | depend => exact hasRight_of_hasRight5 h
    | read => exact exercisable_of_exer5 h
    | write => exact exercisable_of_exer5 h
    | writeShared => exact exercisable_of_exer5 h
    | pin => exact hasRight_of_hasRight5 h
    | unpin o =>
      simp only [PremG, Prem] at h ⊢
      revert h
      cases s.pins[o]? with
      | none => exact id
      | some ob => exact hasRight_of_hasRight5
    | endUse =>
      obtain ⟨hr, g, hg, hgr, hall⟩ := h
      exact ⟨hasRight_of_hasRight5 hr, g, hg, grounds_of_groundsG hgr, hall⟩
    | free =>
      obtain ⟨hr, g, hg, hgr, hall⟩ := h
      exact ⟨hasRight_of_hasRight5 hr, g, hg, grounds_of_groundsG hgr, hall⟩
    | alloc =>
      obtain ⟨hp, ho⟩ := h
      refine ⟨?_, hasRight_of_hasRight5 ho⟩
      rcases hp with hp | ⟨via, hv, hws, -⟩
      · exact .inl (hasRight_of_hasRight5 hp)
      · exact .inr ⟨via, hv, hws⟩
    | store a p =>
      refine ⟨hasRight_of_hasRight5 h.1, ?_⟩
      have h2 := hasRight_of_hasRight5 h.2
      rw [view_storeEffC] at h2
      exact h2
    | _ => trivial
  | deriveSync => exact auth_of_authG h
  | newMutex => exact ⟨exercisable_of_exer5 h.1, newMutexRight_of_G h.2⟩
  | acquire c i =>
    simp only [PremG, Prem] at h ⊢
    revert h
    cases reg[i]? with
    | none => exact id
    | some e => exact fun ⟨hc, ha⟩ => ⟨ctrlRight_of_ctrlRight5 hc, auth_of_authG ha⟩
  | unlock c i =>
    simp only [PremG, Prem] at h ⊢
    revert h
    cases reg[i]? with
    | none => exact id
    | some e =>
      refine fun ⟨hg, hc⟩ => ⟨?_, ctrlRight_of_ctrlRight5 hc⟩
      revert hg
      cases e.grant with
      | none => exact id
      | some g =>
        simp only [OptP]
        cases s.A[g]? with
        | none => exact id
        | some y => exact holderRight_of_holderRightG
  | resetLock c i =>
    obtain ⟨hx, hc⟩ := h
    simp only [ResetExerG, Prem] at hx hc ⊢
    revert hx hc
    cases reg[i]? with
    | none => exact fun h _ => h
    | some e => exact fun hx hc => ⟨exercisable_of_exer5 hx, ctrlRight_of_ctrlRight5 hc⟩
  | spawnVal c _ ls vs => exact valRights_of_G _ _ h
  | newArena => exact ⟨hasRight_of_hasRight5 h.1, exercisable_of_exer5 h.2⟩
  | issue c i region dst =>
    simp only [PremG, Prem] at h ⊢
    revert h
    cases ar[i]? with
    | none => exact id
    | some E =>
      rintro ⟨hm, hd, hx, h1, h2⟩
      refine ⟨metaRight_of_metaRightG hm, hasRight_of_hasRight5 hd, exercisable_of_exer5 hx,
        hasRight_of_hasRight5 h1, ?_⟩
      have h2' := hasRight_of_hasRight5 h2
      rw [view_storeEffC] at h2'
      exact h2'
  | reset c i =>
    simp only [PremG, Prem] at h ⊢
    revert h
    cases ar[i]? with
    | none => exact id
    | some E =>
      rintro ⟨hx, hr⟩
      refine ⟨exercisable_of_exer5 hx, ?_⟩
      revert hr
      cases (resetMid s c E).A[s.A.length]? with
      | none => exact id
      | some y => exact holderRight_of_holderRightG
  | _ => trivial

/-- `PremG` contains the clauses of the amendments (WC5.2 C18 item 4 for `resetLock`, C13 item 11
for `newMutex`). -/
theorem amCondF_of_premG {k : K} {L : MutexLayout} {st : SC × SyncReg × ArenaReg} {lbl : Label}
    (h : PremG k L st lbl) : AmCondF L st lbl := by
  cases lbl with
  | resetLock c i =>
    have h2 := h.2
    simp only [AmCondF]
    revert h2
    cases st.2.1[i]? with
    | none => exact id
    | some e => exact ctrlRight_of_ctrlRight5
  | newMutex => exact newMutexRight_of_G h.2
  | _ => trivial

/-- Every `RunFull` is a `Run7`. -/
theorem runFull_run7 {k : K} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg}
    {lbls : List Label} (h : RunFull k L σ lbls) : Run7 k L σ lbls :=
  fun i hi => ⟨(h i hi).1.1, (h i hi).2⟩

/-- Brief of slice 3, task 1: every `RunFull` is a final amended execution (`RunAmF`): the clauses
of the amendments follow from their guard-free forms. -/
theorem runFull_runAmF {k : K} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg}
    {lbls : List Label} (h : RunFull k L σ lbls) : RunAmF k L σ lbls :=
  ⟨runFull_run7 h, fun i hi => amCondF_of_premG (h i hi).1.2⟩

/-- A `Run7` whose steps satisfy the guard-free forms is a `RunFull`. -/
theorem runFull_of_run7 {k : K} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg}
    {lbls : List Label} (h : Run7 k L σ lbls)
    (hp : ∀ i (hi : i < lbls.length), PremG k L (σ i) lbls[i]) : RunFull k L σ lbls :=
  fun i hi => ⟨⟨(h i hi).1, hp i hi⟩, (h i hi).2⟩

/-! ## The inventory is read by the step relation -/

/-- The right premises of the transfer phases are those of `ValTransfersPre` (WC5.2 C5.2). -/
theorem valRights_of_pre {k : K} {fin : S3} {c : Nat} :
    ∀ (t : SC) (vs : List (Nat × Nat)), ValTransfersPre k fin c t vs → ValRights c t vs
  | _, [], _ => trivial
  | _, _ :: vs, ⟨hp, h⟩ => ⟨⟨hp.srcRight, hp.noOutsideDerived⟩, valRights_of_pre _ vs h⟩

/-- An `ok` `split` executed by `c` writes back `splitEff` on the view of `c`, under `SplitPre`
(Spec 1 §61). -/
theorem split_ok {k : K} {s s₁ : SC} {c src : Nat} {rs : List (List Nat)}
    (h : opStepC k (.split src rs) c s (.ok s₁)) :
    SplitPre k (s.view c) src rs ∧ s₁ = s.set (splitEff (s.view c) src rs) := by
  obtain ⟨-, o, hR, ho⟩ := h
  cases hR with
  | ok hp => exact ⟨hp, Outcome3.ok.inj ho⟩
  | reject => cases ho

/-- An `ok` `derive` executed by `c` writes back `deriveEff` on the view of `c`, under `DerivePre`
(Spec 1 §60). -/
theorem derive_ok {k : K} {s s₁ : SC} {c src : Nat} {region : List Nat} {m : Mode}
    (h : opStepC k (.derive src region m) c s (.ok s₁)) :
    DerivePre (s.view c) src region m ∧ s₁ = s.set (deriveEff (s.view c) src region m) := by
  obtain ⟨-, o, hR, ho⟩ := h
  cases hR with
  | ok hp => exact ⟨hp, Outcome3.ok.inj ho⟩
  | reject => cases ho

/-- Brief of slice 3, task 1: every premise of the inventory is read by the step relation; an `ok`
step whose amended clauses hold (WC5.2 C13 item 11, C18 item 4: `AmCondF`) satisfies `Prem`. -/
theorem prem_of_step {k : K} {L : MutexLayout} {lbl : Label} {st st' : SC × SyncReg × ArenaReg}
    (h : LStep k L lbl st st') (ha : AmCondF L st lbl) : Prem k L st lbl := by
  cases h with
  | @kernel s s' reg ar c op hk =>
    cases op with
    | derive a region m =>
      obtain ⟨-, o, hR, ho⟩ := hk
      exact (pre_of_ok (P := DerivePre (s.view c) a region m) hR ho).exercisable
    | split a rs =>
      obtain ⟨-, o, hR, ho⟩ := hk
      exact (pre_of_ok (P := SplitPre k (s.view c) a rs) hR ho).exercisable
    | release a =>
      obtain ⟨-, o, hR, ho⟩ := hk
      exact (pre_of_ok (P := ReleasePre (s.view c) a) hR ho).holderRight
    | transfer src dst =>
      have hp := (Guarded.ok_iff.1 hk.2).1
      exact ⟨hp.srcRight, hp.dstRight, hp.noOutsideDerived⟩
    | depend q x => exact (Guarded.ok_iff.1 hk.2).1.right
    | read a ls =>
      obtain ⟨-, o, hR, ho⟩ := hk
      exact (pre_of_ok (P := Read3Pre (s.view c) a ls) hR ho).exercisable
    | write a ls =>
      obtain ⟨-, o, hR, ho⟩ := hk
      exact (pre_of_ok (P := Write3Pre (s.view c) a ls) hR ho).exercisable
    | writeShared a ls =>
      obtain ⟨-, o, hR, ho⟩ := hk
      exact (pre_of_ok (P := WriteSharedPre k (s.view c) a ls) hR ho).exercisable
    | pin p =>
      obtain ⟨-, o, hR, ho⟩ := hk
      exact (pre_of_ok (P := PinPre (s.view c) p) hR ho).right
    | unpin o =>
      obtain ⟨-, o₃, hR, ho⟩ := hk
      exact (pre_of_ok (P := UnpinPre k (s.view c) o) hR ho).right
    | endUse p =>
      obtain ⟨-, o, hR, ho⟩ := hk
      have hp := pre_of_ok (P := EndUsePre k (s.view c) p) hR ho
      exact ⟨hp.right, hp.access⟩
    | free p au =>
      obtain ⟨-, o, hR, ho⟩ := hk
      have hp := pre_of_ok (P := FreePre k (s.view c) p au) hR ho
      exact ⟨hp.right, hp.access⟩
    | alloc pr ow ls =>
      obtain ⟨-, o, hR, ho⟩ := hk
      cases hR with
      | ok hst => exact ⟨hst.providerRight, hst.ownerRight⟩
      | fail => cases ho
      | reject => cases ho
    | store a p =>
      have hp := (Guarded.ok_iff.1 hk.2).1
      exact ⟨hp.right, hp.keepsTarget⟩
    | _ => trivial
  | deriveSync hd => exact (Guarded.ok_iff.1 hd.2).1.authorized
  | newMutex hn => exact ⟨hn.2.1.exercisable, ha⟩
  | @acquire s reg ar c i st₁ hacq =>
    obtain ⟨-, e, he, hauth, hd, -⟩ := hacq
    show OptP (reg[i]?) _ False
    rw [he]
    exact ⟨hauth.2.2, hd.authorized⟩
  | @unlock s reg ar c i st₁ hu =>
    obtain ⟨-, e, g, he, -, hg, hrel, hc, -⟩ := hu
    show OptP (reg[i]?) _ False
    rw [he]
    refine ⟨?_, hc⟩
    show OptP e.grant _ False
    rw [hg]
    exact hrel.holderRight
  | @resetLock s reg ar c i st₁ hr =>
    obtain ⟨-, e, he, hx, -, -, -⟩ := hr
    have ha' : OptP (reg[i]?) (fun e => CtrlRight L s e (s.view c).top) False := ha
    show OptP (reg[i]?) _ False
    rw [he] at ha' ⊢
    exact ⟨hx, ha'⟩
  | spawnVal hs => exact valRights_of_pre _ _ (Guarded.ok_iff.1 hs.2).1.transfers
  | newArena hn =>
    have hp := (newArenaStepC_ok hn).2.1
    exact ⟨hp.storageRight, hp.exercisable⟩
  | @issue s reg ar c i region dst st₁ hs =>
    obtain ⟨E, s₁, hE, hst, -, hsp, hsto, -⟩ := issueStepC_ok hs
    obtain ⟨hsp', rfl⟩ := split_ok hsp
    have hp := (Guarded.ok_iff.1 hsto.2).1
    show OptP (ar[i]?) _ False
    rw [hE]
    exact ⟨hst.metaRight, hst.dstRight, hsp'.exercisable, hp.right, hp.keepsTarget⟩
  | @reset s reg ar c i st₁ hs =>
    obtain ⟨E, s₁, hE, hd, hrl, -, -⟩ := resetStepC_ok (k := k) hs
    obtain ⟨hd', rfl⟩ := derive_ok hd
    obtain ⟨-, o, hR, ho⟩ := hrl
    have hp := pre_of_ok (P := ReleasePre ((resetMid s c E).view c) s.A.length) hR ho
    show OptP (ar[i]?) _ False
    rw [hE]
    exact ⟨hd'.exercisable, hp.holderRight⟩
  | _ => trivial

end Ern.Concurrency.FullEncap
