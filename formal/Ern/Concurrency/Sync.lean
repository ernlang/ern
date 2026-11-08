import Ern.Concurrency.Frames

/-!
# Concurrent contract `K_C` and the kernel transition `deriveSync`

* `KC` (WC2 C2, C14): the Spec 1 contract `K` (§48, §80), reached by the projection `KC.toK`,
  extended with the opaque predicate `SyncAuthorized(state, guarded, requesting_frame)`;
* `deriveSync` (WC2 C15): O1 (Spec 1 §60) on `source = guarded`, `region = footprint(guarded)`,
  `mode = Modify`, executed by a live context, with the conjunct `ExercisableAt(source, mode)` of
  §60.1 replaced by `K_C.SyncAuthorized`; the other conjuncts of §60.1 and §60.2–§60.4 are kept;
* `CStepS`, the concurrent kernel steps with `deriveSync`.
-/

namespace Ern.Concurrency

open Ern.MemoryModel.Access

/-- External contract `K_C` (WC2 C2, C14): the unchanged Spec 1 contract `K` (§48), its
projection being `KC.toK`, and the opaque predicate `SyncAuthorized(state, guarded,
requesting_frame)` of WC2 C14. Obligations of `K_C` are hypotheses of theorems, never fields. -/
structure KC extends K where
  SyncAuthorized : SC → Nat → Nat → Prop

/-- Effect of `deriveSync(guarded)` executed by `c` (WC2 C15): a fresh active authority of mode
`Modify`, origin `guarded`, footprint `footprint(guarded)`, held by the current frame of `c`;
this is the `ok` effect of O1 (Spec 1 §60) on the view of `c`. -/
def deriveSyncEff (s : SC) (c g : Nat) : SC :=
  s.set (deriveEff (s.view c) g ((s.view c).afp g) .modify)

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

/-- Decidability of the preconditions of `deriveSync` (WC2 C15). -/
instance (kc : KC) (s : SC) (c g : Nat) [Decidable (kc.SyncAuthorized s g (s.view c).top)] :
    Decidable (DeriveSyncPre kc s c g) :=
  decidable_of_iff ((s.view c).Active g ∧ kc.SyncAuthorized s g (s.view c).top ∧
    (∀ x ∈ (s.view c).ancs g, (s.view c).Active x) ∧
    (∀ l ∈ (s.view c).afp g, l < s.P.length ∧ isLeaf s.P l) ∧
    (∀ l ∈ (s.view c).afp g, l ∈ (s.view c).afp g) ∧
    (∀ l ∈ (s.view c).afp g, Allows (effective (s.view c) g l) .modify) ∧
    (∀ b ∈ List.range s.A.length, OptP (s.A[b]?) (fun y => y.active = true →
      b ∉ g :: (s.view c).ancs g → (∃ l ∈ (s.view c).afp g, l ∈ y.footprint) →
        y.mode = .observe ∧ Mode.modify = .observe) True) ∧
    (s.view c).top ∈ (s.view c).F)
    ⟨fun ⟨a, b, c, d, e, f, g, h⟩ => ⟨a, b, c, d, e, f, g, h⟩,
     fun ⟨a, b, c, d, e, f, g, h⟩ => ⟨a, b, c, d, e, f, g, h⟩⟩

/-- `deriveSync(guarded)` executed by `c` (WC2 C15): `ok` or `reject` (Spec 1 §58 for kernel
transitions); no outcome if `c` is not live. -/
def DeriveSyncStep (kc : KC) (s : SC) (c g : Nat) (o : Outcome3 SC) : Prop :=
  s.Live c ∧ Guarded (DeriveSyncPre kc s c g) (deriveSyncEff s c g) o

/-- WC2 C15: the authority created by `deriveSync` is an ordinary authority of mode `Modify`,
origin `guarded`, footprint `footprint(guarded)`, held by the current frame, active, of fresh
identity `|A|`. -/
theorem deriveSync_created {kc : KC} {s s' : SC} {c g : Nat}
    (h : DeriveSyncStep kc s c g (.ok s')) :
    s'.A = s.A ++ [⟨.modify, some g, (s.view c).afp g, .frame (s.view c).top, true⟩] := by
  obtain ⟨-, h⟩ := h
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
  rfl

/-- One `ok` transition of the concurrent kernel (WC2 C2, C4, C6–C8, C15): a step of `CStep`
under the projection `K_C.toK`, or `deriveSync`. -/
inductive CStepS (kc : KC) : SC → SC → Prop where
  | base {s s' : SC} : CStep kc.toK s s' → CStepS kc s s'
  | deriveSync {s s' : SC} {c g : Nat} : DeriveSyncStep kc s c g (.ok s') → CStepS kc s s'

end Ern.Concurrency
