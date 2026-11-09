import Ern.Concurrency.Frames

/-!
# Concurrent contract `K_C` and the kernel transition `deriveSync`

* `KC R` (WC4 C2, C14): the Spec 1 contract `K` (§48, §80), reached by the projection `KC.toK`,
  extended with the opaque predicate `SyncAuthorized(state, sync_registry, guarded,
  requesting_frame)`, whose registry argument has the type `R` of the library registry; the
  kernel does not depend on the library;
* `deriveSync` (WC4 C15): O1 (Spec 1 §60) on `source = guarded`, `region = footprint(guarded)`,
  `mode = Modify`, executed by a live context;
* `CStepS`, the concurrent kernel steps with `deriveSync` for a given registry.
-/

namespace Ern.Concurrency

open Ern.MemoryModel.Access

/-- External contract `K_C` (WC4 C2, C14): the unchanged Spec 1 contract `K` (§48), its
projection being `KC.toK`, and the opaque predicate `SyncAuthorized(state, sync_registry, guarded,
requesting_frame)` of WC4 C14, the registry being an external argument of type `R` (WC4 C2: not a
component of `S_C`). Obligations of `K_C` are hypotheses of theorems, never fields. -/
structure KC (R : Type) extends K where
  SyncAuthorized : R → SC → Nat → Nat → Prop

/-- Effect of `deriveSync(guarded)` executed by `c` (WC4 C15 effect): a fresh active authority of mode
`Modify`, origin `guarded`, footprint `footprint(guarded)`, held by the current frame of `c`;
this is the `ok` effect of O1 (Spec 1 §60) on the view of `c`. -/
def deriveSyncEff (s : SC) (c g : Nat) : SC :=
  s.set (deriveEff (s.view c) g ((s.view c).afp g) .modify)

/-- Preconditions of `deriveSync(guarded)` executed by `c` with the registry `r` (WC4 C15.1–C15.6):
those of O1 (Spec 1 §60) for `source = guarded`, `region = footprint(guarded)`, `mode = Modify`,
on the view of `c`, with `K_C.SyncAuthorized(state, r, guarded, current frame)` in place of
`ExercisableAt(source, Modify)` of §60.1 as the only authorization (WC4 C15.3). -/
structure DeriveSyncPre {R : Type} (kc : KC R) (r : R) (s : SC) (c g : Nat) : Prop where
  /-- WC4 C15.1, Spec 1 §60.1: `source` is active. -/
  active : (s.view c).Active g
  /-- WC4 C15.1 (Spec 1 §43, §60.1): the own mode of `guarded` permits `Modify`. -/
  mode : OptP ((s.view c).A[g]?) (fun y => Mode.modify.le y.mode) False
  /-- WC4 C15.3: `deriveSync` is authorized exclusively through `K_C.SyncAuthorized`. -/
  authorized : kc.SyncAuthorized r s g (s.view c).top
  /-- WC4 C15.2, Spec 1 §60.1: every authority of the origin chain of `source` is active. -/
  chainActive : ∀ x ∈ (s.view c).ancs g, (s.view c).Active x
  /-- WC4 C15.4, Spec 1 §60.2: the leaves of `region` exist. -/
  leaves : ∀ l ∈ (s.view c).afp g, l < s.P.length ∧ isLeaf s.P l
  /-- WC4 C15.4, Spec 1 §60.2: the leaves of `region` belong to the footprint of `source`. -/
  within : ∀ l ∈ (s.view c).afp g, l ∈ (s.view c).afp g
  /-- WC4 C15.4, Spec 1 §60.2: `Modify` does not exceed the effective right of `source` on these
  leaves. -/
  modeOK : ∀ l ∈ (s.view c).afp g, Allows (effective (s.view c) g l) .modify
  /-- WC4 C15.5, Spec 1 §60.3: the addition preserves I1 (§50). -/
  exclusive : ∀ b ∈ List.range s.A.length, OptP (s.A[b]?) (fun y => y.active = true →
    b ∉ g :: (s.view c).ancs g → (∃ l ∈ (s.view c).afp g, l ∈ y.footprint) →
      y.mode = .observe ∧ Mode.modify = .observe) True
  /-- WC4 C15.6, Spec 1 §60.4: the new holding frame is the live current frame. -/
  frameLive : (s.view c).top ∈ (s.view c).F

/-- Decidability of the preconditions of `deriveSync` (WC4 C15). -/
instance {R : Type} (kc : KC R) (r : R) (s : SC) (c g : Nat)
    [Decidable (kc.SyncAuthorized r s g (s.view c).top)] : Decidable (DeriveSyncPre kc r s c g) :=
  decidable_of_iff ((s.view c).Active g ∧
    OptP ((s.view c).A[g]?) (fun y => Mode.modify.le y.mode) False ∧
    kc.SyncAuthorized r s g (s.view c).top ∧
    (∀ x ∈ (s.view c).ancs g, (s.view c).Active x) ∧
    (∀ l ∈ (s.view c).afp g, l < s.P.length ∧ isLeaf s.P l) ∧
    (∀ l ∈ (s.view c).afp g, l ∈ (s.view c).afp g) ∧
    (∀ l ∈ (s.view c).afp g, Allows (effective (s.view c) g l) .modify) ∧
    (∀ b ∈ List.range s.A.length, OptP (s.A[b]?) (fun y => y.active = true →
      b ∉ g :: (s.view c).ancs g → (∃ l ∈ (s.view c).afp g, l ∈ y.footprint) →
        y.mode = .observe ∧ Mode.modify = .observe) True) ∧
    (s.view c).top ∈ (s.view c).F)
    ⟨fun ⟨a, b, c, d, e, f, g, h, i⟩ => ⟨a, b, c, d, e, f, g, h, i⟩,
     fun ⟨a, b, c, d, e, f, g, h, i⟩ => ⟨a, b, c, d, e, f, g, h, i⟩⟩

/-- `deriveSync(guarded)` executed by `c` with the registry `r` (WC4 C15): `ok` or `reject`; no
outcome if `c` is not live. -/
def DeriveSyncStep {R : Type} (kc : KC R) (r : R) (s : SC) (c g : Nat) (o : Outcome3 SC) : Prop :=
  s.Live c ∧ Guarded (DeriveSyncPre kc r s c g) (deriveSyncEff s c g) o

/-- WC4 C15 effect: the authority created by `deriveSync` is an ordinary authority of mode `Modify`,
origin `guarded`, footprint `footprint(guarded)`, held by the current frame, active, of fresh
identity `|A|`. -/
theorem deriveSync_created {R : Type} {kc : KC R} {r : R} {s s' : SC} {c g : Nat}
    (h : DeriveSyncStep kc r s c g (.ok s')) :
    s'.A = s.A ++ [⟨.modify, some g, (s.view c).afp g, .frame (s.view c).top, true⟩] := by
  obtain ⟨-, h⟩ := h
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
  rfl

/-- One `ok` transition of the concurrent kernel with the registry `r` (WC4 C2, C4, C6–C8, C15): a
step of `CStep` under the projection `K_C.toK`, or `deriveSync`. -/
inductive CStepS {R : Type} (kc : KC R) (r : R) : SC → SC → Prop where
  | base {s s' : SC} : CStep kc.toK s s' → CStepS kc r s s'
  | deriveSync {s s' : SC} {c g : Nat} : DeriveSyncStep kc r s c g (.ok s') → CStepS kc r s s'

end Ern.Concurrency
