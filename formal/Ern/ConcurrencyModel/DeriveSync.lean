import Ern.ConcurrencyModel.Contract

/-!
# The concurrent transition `deriveSync` (C15)

`deriveSync` executed by a context: O1 (Spec 1 §60) on `source = guarded`,
`region = footprint(guarded)`, `mode = Modify`, authorized only by `K_C.SyncAuthorized` (C15.3).
-/

namespace Ern.ConcurrencyModel

open Ern.MemoryModel.Access

/-- Effect of `deriveSync(guarded)` executed by `c` (C15 effect): a fresh active authority of mode
`Modify`, origin `guarded`, footprint `footprint(guarded)`, held by the current frame of `c`;
this is the `ok` effect of O1 (Spec 1 §60) on the view of `c`. -/
def deriveSyncEff (s : SC) (c g : Nat) : SC :=
  s.set (deriveEff (s.view c) g ((s.view c).afp g) .modify)

/-- Preconditions of `deriveSync(guarded)` executed by `c` with the registry `r` (C15.1–C15.6):
those of O1 (Spec 1 §60) for `source = guarded`, `region = footprint(guarded)`, `mode = Modify`,
on the view of `c`, with `K_C.SyncAuthorized(state, r, guarded, current frame)` in place of
`ExercisableAt(source, Modify)` of §60.1 as the only authorization (C15.3). -/
structure DeriveSyncPre {R : Type} (kc : KC R) (r : R) (s : SC) (c g : Nat) : Prop where
  /-- C15.1, Spec 1 §60.1: `source` is active. -/
  active : (s.view c).Active g
  /-- C15.1 (Spec 1 §43, §60.1): the own mode of `guarded` permits `Modify`. -/
  mode : OptP ((s.view c).A[g]?) (fun y => Mode.modify.le y.mode) False
  /-- C15.3: `deriveSync` is authorized exclusively through `K_C.SyncAuthorized`. -/
  authorized : kc.SyncAuthorized r s g (s.view c).top
  /-- C15.2, Spec 1 §60.1: every authority of the origin chain of `source` is active. -/
  chainActive : ∀ x ∈ (s.view c).ancs g, (s.view c).Active x
  /-- C15.4, Spec 1 §60.2: the leaves of `region` exist. -/
  leaves : ∀ l ∈ (s.view c).afp g, l < s.P.length ∧ isLeaf s.P l
  /-- C15.4, Spec 1 §60.2: the leaves of `region` belong to the footprint of `source`. -/
  within : ∀ l ∈ (s.view c).afp g, l ∈ (s.view c).afp g
  /-- C15.4, Spec 1 §60.2: `Modify` does not exceed the effective right of `source` on these
  leaves. -/
  modeOK : ∀ l ∈ (s.view c).afp g, Allows (effective (s.view c) g l) .modify
  /-- C15.5, Spec 1 §60.3: the addition preserves I1 (§50). -/
  exclusive : ∀ b ∈ List.range s.A.length, OptP (s.A[b]?) (fun y => y.active = true →
    b ∉ g :: (s.view c).ancs g → (∃ l ∈ (s.view c).afp g, l ∈ y.footprint) →
      y.mode = .observe ∧ Mode.modify = .observe) True
  /-- C15.6, Spec 1 §60.4: the new holding frame is the live current frame; its liveness ranges
  over the globally live frames (C2). -/
  frameLive : (s.view c).top ∈ s.frames

/-- Decidability of the preconditions of `deriveSync` (C15). -/
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
    (s.view c).top ∈ s.frames)
    ⟨fun ⟨a, b, c, d, e, f, g, h, i⟩ => ⟨a, b, c, d, e, f, g, h, i⟩,
     fun ⟨a, b, c, d, e, f, g, h, i⟩ => ⟨a, b, c, d, e, f, g, h, i⟩⟩

/-- `deriveSync(guarded)` executed by `c` with the registry `r` (C15): `ok` or `reject`. A context
that is not live has no current frame (C2), so C15.6 fails: `reject`. -/
def DeriveSyncStep {R : Type} (kc : KC R) (r : R) (s : SC) (c g : Nat) (o : Outcome3 SC) : Prop :=
  Guarded (DeriveSyncPre kc r s c g) (deriveSyncEff s c g) o

/-- An `ok` `deriveSync` requires the executing context to be live (C15.6, C2). -/
theorem deriveSyncStep_live {R : Type} {kc : KC R} {r : R} {s s' : SC} {c g : Nat}
    (h : DeriveSyncStep kc r s c g (.ok s')) : s.Live c :=
  SC.live_of_top_mem (Guarded.ok_iff.1 h).1.frameLive

/-- C15 effect: the authority created by `deriveSync` is an ordinary authority of mode `Modify`,
origin `guarded`, footprint `footprint(guarded)`, held by the current frame, active, of fresh
identity `|A|`. -/
theorem deriveSync_created {R : Type} {kc : KC R} {r : R} {s s' : SC} {c g : Nat}
    (h : DeriveSyncStep kc r s c g (.ok s')) :
    s'.A = s.A ++ [⟨.modify, some g, (s.view c).afp g, .frame (s.view c).top, true⟩] := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
  rfl

end Ern.ConcurrencyModel
