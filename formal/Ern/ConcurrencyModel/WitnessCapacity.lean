import Ern.ConcurrencyModel.WitnessLock

/-!
# Witnesses W11, W12: the capability of a context, and the stability of the controller leaf (C43,
C49)

* W11 (C43): after block M, `guarded` is exercisable in `Observe` from the frame of `c1` and
  `cap(c1, T)` is `none` (the chain passes through the `guarded` of a live entry); after
  `c0 : acquire(e)`, `cap(c0, T)` is `Modify`, through the grant held by its frame.
* W12 (C49, last paragraph): after block M and prefix P, a `transfer` of the whole mutex value `M`
  to a second location `M′ = {slot′, lock′}`, then `c0 : acquire(e)`: every step is `ok`; the
  controller of `e` is `lock` before the `transfer` and `lock′` after it, so the stability
  hypothesis of 13e fails. No graph fact: the accesses of the `transfer` are not represented
  (`OB-C20`).
-/

namespace Ern.ConcurrencyModel

open Ern.MemoryModel Ern.MemoryModel.Access Events

variable {pm : ProviderMeta}

/-! ## W11 -/

/-- `c0 : acquire(e)` after block M (grant, authority 4). -/
def w11s6 : SC := deriveSyncEff m4 0 2

/-- The labels of W11: block M, `c0 : acquire(e)`. -/
def w11L : List Label :=
  [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 2 1), .newMutex 0 2,
   .kernel 0 (.derive 0 [1, 2] .observe), .spawn 0 [3] [], .acquire 0 0]

/-- The states of W11. -/
def w11σ : Nat → SC × SyncReg × ArenaReg
  | 0 => (m0, [], []) | 1 => (m1, [], []) | 2 => (m2, [], []) | 3 => (m2, regFree, [])
  | 4 => (m3, regFree, []) | 5 => (m4, regFree, []) | _ => (w11s6, regTaken, [])

/-- W11 is an `EncapsulatedTrace` with named states from the initial state (C51.1). -/
theorem w11_run : EncapRun pm kMutex mutexLayout w11σ w11L := by
  refine encapRun_of_steps fun i hi lbl hl => ?_
  match i, hi with
  | 0, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 1, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel (.ok (by decide))⟩
  | 2, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .newMutex (st' := (m2, regFree)) ⟨by decide, rfl⟩⟩
  | 3, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 4, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .spawn (.ok (by decide))⟩
  | 5, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .acquire (st' := (w11s6, regTaken)) ⟨⟨2, none⟩, rfl, by decide, by decide, rfl⟩⟩

/-- **Witness W11** (C43: `cap` is "not `ExercisableAt`", and excludes "attribution through live
`guarded` authorities"): after block M (state 5), `guarded` (authority 2) is exercisable in
`Observe` from the current frame of `c1`, while `cap(c1, T)` is `none`; after `c0 : acquire(e)`
(state 6), `cap(c0, T)` is `Modify`, through the grant (authority 4), held by the frame of `c0`,
attributable in `Modify` and of effective `Modify` on `T`. -/
theorem witness_w11 :
    w11σ 0 = (SC.ofS3 (S3.init mutexStatics), [], []) ∧ EncapRun pm kMutex mutexLayout w11σ w11L ∧
    ((w11σ 5).1.view 1).ExercisableAt 2 .observe ∧ cap (w11σ 5).1 (w11σ 5).2.1 1 3 = none ∧
    cap (w11σ 6).1 (w11σ 6).2.1 0 3 = some .modify ∧
    ((w11σ 6).1.A[4]?).map (·.holder) = some (.frame 0) ∧
    CapAttr (w11σ 6).1 (w11σ 6).2.1 0 4 .modify ∧
    effective (w11σ 6).1.flat 4 3 = some .modify :=
  ⟨rfl, w11_run, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-! ## W12 -/

/-- Statics of W12 (Spec 1 §47): those of `WitnessMutex` (`0` `M`, `1` `slot`, `2` `lock`, `3` `T`
owned by `M`), and a second location `4` `M′` with its fields `5` `slot′` and `6` `lock′`, not
`Init`. Root authorities: `0` of `M`, `1` of `T`, `2` of `M′`. -/
def mutexStatics3 : Statics :=
  [((none, none, 0), false), ((some 0, none, 0), false), ((some 0, none, 0), true),
   ((none, some 0, 0), true), ((none, none, 0), false), ((some 4, none, 0), false),
   ((some 4, none, 0), false)]

/-- The statics are well formed (Spec 1 §47). -/
theorem mutexStatics3_ok : StaticsOK mutexStatics3 := by decide

/-- Initial state of W12 (Spec 1 §47). -/
def y0 : SC := SC.ofS3 (S3.init mutexStatics3)
/-- `guarded := derive(root_T, Modify)`, authority 3. -/
def y1 : SC := y0.set (deriveEff (y0.view 0) 1 [3] .modify)
/-- `store(guarded, slot)`. -/
def y2 : SC := storeEffC y1 0 3 1
/-- The registry with the entry of `guarded`, available. -/
def regY : SyncReg := [⟨3, none⟩]
/-- `o1 := derive(root_M, Observe, {slot, lock})`, authority 4. -/
def y3 : SC := y2.set (deriveEff (y2.view 0) 0 [1, 2] .observe)
/-- `spawn c1` yielding `o1`. -/
def y4 : SC := spawnEff y3 0 [4] []
/-- `c1 : acquire(e)` (grant, authority 5). -/
def y5 : SC := deriveSyncEff y4 1 3
/-- The registry recording the grant 5. -/
def regY5 : SyncReg := [⟨3, some 5⟩]
/-- `c1 : write3(T)` by the grant. -/
def y6 : SC := y5.set (write3Eff (y5.view 1) [3])
/-- `c1 : unlock(e)`. -/
def y7 : SC := prospectiveUnlock y6 1 5
/-- `c1 : release(o1)`. -/
def y8 : SC := y7.set (releaseEff (y7.view 1) 4)
/-- `c0 : transfer(M, M′)`. -/
def y9 : SC := transferEffC y8 0 0 4
/-- `c0 : acquire(e)` (grant, authority 6). -/
def y10 : SC := deriveSyncEff y9 0 3
/-- The registry recording the grant 6. -/
def regY6 : SyncReg := [⟨3, some 6⟩]

/-- The labels of W12: block M, P, `c0 : transfer(M, M′)`, `c0 : acquire(e)`. -/
def w12L : List Label :=
  [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 3 1), .newMutex 0 3,
   .kernel 0 (.derive 0 [1, 2] .observe), .spawn 0 [4] [], .acquire 1 0,
   .kernel 1 (.write 5 [3]), .unlock 1 0, .kernel 1 (.release 4), .kernel 0 (.transfer 0 4),
   .acquire 0 0]

/-- The states of W12. -/
def w12σ : Nat → SC × SyncReg × ArenaReg
  | 0 => (y0, [], []) | 1 => (y1, [], []) | 2 => (y2, [], []) | 3 => (y2, regY, [])
  | 4 => (y3, regY, []) | 5 => (y4, regY, []) | 6 => (y5, regY5, []) | 7 => (y6, regY5, [])
  | 8 => (y7, regY, []) | 9 => (y8, regY, []) | 10 => (y9, regY, []) | _ => (y10, regY6, [])

/-- W12 is an `EncapsulatedTrace` with named states from the initial state (C51.1): every step is
`ok`. -/
theorem w12_run : EncapRun pm kMutex mutexLayout w12σ w12L := by
  refine encapRun_of_steps fun i hi lbl hl => ?_
  match i, hi with
  | 0, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 1, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel (.ok (by decide))⟩
  | 2, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .newMutex (st' := (y2, regY)) ⟨by decide, rfl⟩⟩
  | 3, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 4, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .spawn (.ok (by decide))⟩
  | 5, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .acquire (st' := (y5, regY5)) ⟨⟨3, none⟩, rfl, by decide, by decide, rfl⟩⟩
  | 6, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 7, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .unlock (st' := (y7, regY)) ⟨⟨3, some 5⟩, 5, rfl, by decide, rfl, by decide, by decide,
        by decide, rfl⟩⟩
  | 8, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel ⟨_, .ok (by decide), rfl⟩⟩
  | 9, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .kernel (.ok (by decide))⟩
  | 10, _ => cases hl; exact ⟨⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
      .acquire (st' := (y10, regY6)) ⟨⟨3, none⟩, rfl, by decide, by decide, rfl⟩⟩

/-- **Witness W12** (C49, last paragraph: "`ControlOf(entry)` becoming undefined or designating
another leaf"; C12: "A legal transfer of the **whole mutex value `M`** ... may carry `slot` and its
controller together and preserve the association positionally"): every step is `ok` in an
`EncapsulatedTrace` from the initial state; the controller of `e` is `lock` (leaf 2) up to the
`transfer` (step 9) and `lock′` (leaf 6) after it, at the `acquire` of `c0` (step 10); the
stability hypothesis of 13e fails for the `unlock` of step 7 and that `acquire`, whatever the
controller unit. -/
theorem witness_w12 :
    w12σ 0 = (SC.ofS3 (S3.init mutexStatics3), [], []) ∧
    EncapRun pm kMutex mutexLayout w12σ w12L ∧
    ctlOf mutexLayout (w12σ 7) 0 = some 2 ∧ ctlOf mutexLayout (w12σ 9) 0 = some 2 ∧
    ctlOf mutexLayout (w12σ 10) 0 = some 6 ∧
    ¬ ∃ x, ∀ k, 7 ≤ k → k ≤ 10 → ProtoOn w12L 0 k → ctlOf mutexLayout (w12σ k) 0 = some x := by
  refine ⟨rfl, w12_run, by decide, by decide, by decide, fun ⟨x, hx⟩ => ?_⟩
  have h7 := hx 7 (by decide) (by decide) (by decide)
  have h10 := hx 10 (by decide) (by decide) (by decide)
  rw [show ctlOf mutexLayout (w12σ 7) 0 = some 2 by decide] at h7
  rw [show ctlOf mutexLayout (w12σ 10) 0 = some 6 by decide] at h10
  cases h7; cases h10

end Ern.ConcurrencyModel
