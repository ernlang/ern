import Ern.Concurrency.Reachable
import Ern.Concurrency.Traces

/-!
# Mutex transfer, `endUse` and `Encap` (test module)

Concrete runs checking `Encap` (WC4 C22.3, C22.5) and the initialization invariant (WC4 C21.7)
against WC4 C12, S7, S16, S17 and S18:

* a mutex value `M = {slot, lock}` owning the protected root `T`; `guarded` is a `Modify`
  derivative of the root authority of `T`, stored in `slot` (Spec 1 §60, §65); `M′ = {slot′, lock′}`
  is a place of the same shape in the same frame; `Y` is a one-leaf place;
* variants A (`grant = none`) and B (an active grant): `transfer(M, M′)` is an `ok` step admitted
  by `Encap`, after which `KInvC`, `SyncInv` and `GrantDiscipline` hold and `ControlOf` designates
  `lock′` (S16, positive half);
* `transfer(slot, Y)` and `transfer(lock, Y)`: `ok` kernel steps excluded by `Encap`, after which
  `SyncInv` fails (S16 and its extension);
* `endUse(lock)`, and `endUse` of a strict part of `slot` (S17a, S17b): `ok` kernel steps excluded
  by `Encap` (WC4 C22.5), after which `SyncInv` fails (`ctlInit`, `slotInit`); `endUse(M)` and
  `endUse(slot)`: `ok` steps admitted by `Encap` that end the entry, after which `SyncInv` holds;
* a run whose `endUse` steps break WC4 C21.7, followed by `transfer(M₁, M₂)`, gives two live
  entries the same controller (`endUse_then_transfer_merges`); it is not an `EncapsulatedTrace`
  (`endUse_then_transfer_merges_false`);
* `newMutex` on a mutex value whose fields are `Uninit` is rejected by WC4 C13.10
  (`newMutex_uninit_rejected`), so the run of `transfer_merges_controllers_false` is not a run.
-/

namespace Ern.Concurrency.EncapTraces

open Ern.MemoryModel.Access Ern.MemoryModel.Access.Examples Ern.Concurrency
open Ern.Concurrency.Traces (L0)

/-! ## States -/

/-- Statics (Spec 1 §47): `0` the mutex value `M`, `1` its field `slot`, `2` its field `lock`
(`Init`), `3` the protected root `T` (`Init`), owned by `M`; `4` the place `M′` with fields `5`
(`slot′`) and `6` (`lock′`), `Uninit`; `7` the one-leaf place `Y`, `Uninit`. Root authorities: `0`
of `M`, `1` of `T` (held by `M`), `2` of `M′`, `3` of `Y`. -/
def est : Statics :=
  [((none, none, 0), false), ((some 0, none, 0), false), ((some 0, none, 0), true),
   ((none, some 0, 0), true), ((none, none, 0), false), ((some 4, none, 0), false),
   ((some 4, none, 0), false), ((none, none, 0), false)]

/-- The statics are well formed (Spec 1 §47). -/
theorem est_ok : StaticsOK est := by decide

/-- `DDSound` for the test contract `K0` (Spec 1 §80): nothing is declared disjoint. -/
theorem ddK0 : DDSound K0 := fun _ _ h => h.elim

/-- Initial single-context state (Spec 1 §47). -/
def e0 : SC := SC.ofS3 (S3.init est)

/-- `derive(1, footprint(T) = [3], Modify)` by context 0 (Spec 1 §60): authority 4, `guarded`. -/
def e1 : SC := e0.set (deriveEff (e0.view 0) 1 [3] .modify)

/-- `store(4, slot = 1)` by context 0 (Spec 1 §65): `guarded` is held by `slot`. -/
def e2 : SC := storeEffC e1 0 4 1

/-- Registry after `newMutex(4)` (WC4 C13). -/
def reg1 : SyncReg := [⟨4, none⟩]

/-- Variant A: `transfer(M = 0, M′ = 4)` by context 0 with `grant = none` (Spec 1 §63). -/
def eA : SC := transferEffC e2 0 0 4

/-- Variant B, first step: `acquire` on entry 0 (WC4 C16): grant authority 5, held by frame 0. -/
def e3 : SC := deriveSyncEff e2 0 4

/-- Registry after `acquire` (WC4 C16). -/
def reg2 : SyncReg := [⟨4, some 5⟩]

/-- Variant B: `transfer(M = 0, M′ = 4)` by context 0 with the grant active (Spec 1 §63). -/
def eB : SC := transferEffC e3 0 0 4

/-- `transfer(slot = 1, Y = 7)` by context 0 after `newMutex` (Spec 1 §63). -/
def eC : SC := transferEffC e2 0 1 7

/-! ## Steps -/

/-- The derivation of `guarded` is an `ok` step (Spec 1 §60). -/
theorem step_derive : opStepC K0 (.derive 1 [3] .modify) 0 e0 (.ok e1) :=
  ⟨by decide, _, .ok (by decide), rfl⟩

/-- The store of `guarded` in `slot` is an `ok` step (Spec 1 §65 re-indexed). -/
theorem step_store : opStepC K0 (.store 4 1) 0 e1 (.ok e2) := ⟨by decide, .ok (by decide)⟩

/-- `newMutex(4)` is enabled (WC4 C13); its controller is `lock` (place 2). -/
theorem step_newMutex : NewMutexOk K0 L0 [] e2 [] 0 4 (e2, reg1) ∧
    ControlOf L0 e2 ⟨4, none⟩ = some 2 :=
  ⟨⟨by decide, by decide, rfl⟩, by decide⟩

/-- `acquire` is enabled (WC4 C16); the grant 5 is an active `Modify` derivative of `guarded` over
`footprint(T)`, held by frame 0, the current frame. -/
theorem step_acquire : AcquireOk K0 L0 e2 reg1 0 0 (e3, reg2) ∧
    e3.A[5]? = some ⟨.modify, some 4, [3], .frame 0, true⟩ ∧ (e3.view 0).top = 0 :=
  ⟨⟨by decide, ⟨4, none⟩, rfl, by decide, by decide, rfl⟩, by decide, by decide⟩

/-- Verdict (a), variant A: `transfer(M, M′)` is an `ok` step of Spec 1 §63 re-indexed. -/
theorem stepA_transfer : opStepC K0 (.transfer 0 4) 0 e2 (.ok eA) :=
  ⟨by decide, .ok (by decide)⟩

/-- Verdict (a), variant B: `transfer(M, M′)` is an `ok` step of Spec 1 §63 re-indexed. -/
theorem stepB_transfer : opStepC K0 (.transfer 0 4) 0 e3 (.ok eB) :=
  ⟨by decide, .ok (by decide)⟩

/-- `transfer(slot, Y)` is an `ok` step of Spec 1 §63 re-indexed. -/
theorem stepC_transfer : opStepC K0 (.transfer 1 7) 0 e2 (.ok eC) :=
  ⟨by decide, .ok (by decide)⟩

/-! ## The transfer clause of `Encap` -/

/-- The transfer clause of `Encap` is WC4 C22.3 (`TransferExcl`): the source is compared with
the place holding `guarded`, its structural subplaces, and the controller leaf, for every live
entry. -/
theorem encap_transfer_iff (st : SC × SyncReg) (c src dst : Nat) :
    Encap L0 st (.kernel c (.transfer src dst)) ↔ TransferExcl L0 st src :=
  Iff.rfl

/-- In `e2`, `guarded` (authority 4) is held by `slot` (place 1), a field of `M` (place 0). -/
theorem guarded_in_slot : (e2.A[4]?).map (·.holder) = some (.place 1) ∧
    parentOf e2.P 1 = some 0 := by decide

/-- Verdict (b): `Encap` admits `transfer(M, M′)` in both variants and excludes
`transfer(slot, Y)` (WC4 C22.3 (a)) and `transfer(lock, Y)` (C22.3 (c)). -/
theorem encap_verdicts : Encap L0 (e2, reg1) (.kernel 0 (.transfer 0 4)) ∧
    Encap L0 (e3, reg2) (.kernel 0 (.transfer 0 4)) ∧
    ¬ Encap L0 (e2, reg1) (.kernel 0 (.transfer 1 7)) ∧
    ¬ Encap L0 (e2, reg1) (.kernel 0 (.transfer 2 7)) :=
  ⟨(by decide : TransferExcl L0 (e2, reg1) 0), (by decide : TransferExcl L0 (e3, reg2) 0),
    (by decide : ¬ TransferExcl L0 (e2, reg1) 1), (by decide : ¬ TransferExcl L0 (e2, reg1) 2)⟩

/-! ## Traces and invariants -/

/-- Variant A as an `EncapsulatedTrace` from the initial state with an empty registry (WC4 C22,
C23). -/
theorem traceA : EncapsulatedTrace K0 L0 (e0, [])
    [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 4 1), .newMutex 0 4 [],
     .kernel 0 (.transfer 0 4)] (eA, reg1) :=
  .cons (fun e he => by cases he) (.kernel step_derive) <|
  .cons trivial (.kernel step_store) <|
  .cons trivial (.newMutex step_newMutex.1) <|
  .cons encap_verdicts.1 (.kernel stepA_transfer) .nil

/-- Variant B as an `EncapsulatedTrace` from the initial state with an empty registry (WC4 C22,
C23). -/
theorem traceB : EncapsulatedTrace K0 L0 (e0, [])
    [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 4 1), .newMutex 0 4 [],
     .acquire 0 0, .kernel 0 (.transfer 0 4)] (eB, reg2) :=
  .cons (fun e he => by cases he) (.kernel step_derive) <|
  .cons trivial (.kernel step_store) <|
  .cons trivial (.newMutex step_newMutex.1) <|
  .cons trivial (.acquire step_acquire.1) <|
  .cons encap_verdicts.2.1 (.kernel stepB_transfer) .nil

/-- The trace up to `newMutex` (WC4 C13) as an `EncapsulatedTrace`. -/
theorem traceMutex : EncapsulatedTrace K0 L0 (e0, [])
    [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 4 1), .newMutex 0 4 []] (e2, reg1) :=
  .cons (fun e he => by cases he) (.kernel step_derive) <|
  .cons trivial (.kernel step_store) <|
  .cons trivial (.newMutex step_newMutex.1) .nil

/-- `KInvCA` and `SyncState` after `newMutex` (`trace_inv`). -/
theorem inv2 : KInvCA e2 ∧ SyncState L0 e2 reg1 := by
  obtain ⟨hk, hs⟩ := init_inv (k := K0) ddK0 est_ok L0
  exact trace_inv ddK0 traceMutex hk hs

/-- Verdict (c), variant A, positive twin of `transfer_into_live_mutex_rejected` (WC4 C22.3,
S16 and S18 positive halves): after `transfer(M, M′)` onto a destination with no entry, `KInvC`
(with the auxiliaries of Spec 1) and `SyncState` (`SyncInv`, `GrantDiscipline`) hold, and the
entry is live. -/
theorem invA : KInvCA eA ∧ SyncState L0 eA reg1 ∧ (⟨4, none⟩ : SyncEntry).Live eA := by
  obtain ⟨hk, hs⟩ := init_inv (k := K0) ddK0 est_ok L0
  exact ⟨(trace_inv ddK0 traceA hk hs).1, (trace_inv ddK0 traceA hk hs).2, by decide⟩

/-- Verdict (c), variant B (from `trace_inv`): after `transfer(M, M′)`, `KInvC` (with the
auxiliaries of Spec 1) and `SyncState` hold; the entry is live and the grant 5 is still active
and held by frame 0. -/
theorem invB : KInvCA eB ∧ SyncState L0 eB reg2 ∧ (⟨4, some 5⟩ : SyncEntry).Live eB ∧
    eB.A[5]? = some ⟨.modify, some 4, [3], .frame 0, true⟩ := by
  obtain ⟨hk, hs⟩ := init_inv (k := K0) ddK0 est_ok L0
  exact ⟨(trace_inv ddK0 traceB hk hs).1, (trace_inv ddK0 traceB hk hs).2, by decide, by decide⟩

/-- Verdict (d), WC4 S16 positive half: after `transfer(M, M′)`, in both variants, `guarded` is
held by `slot′` (place 5) and `ControlOf` designates `lock′` (place 6) (WC4 C12, positional). -/
theorem controlAB : (eA.A[4]?).map (·.holder) = some (.place 5) ∧
    ControlOf L0 eA ⟨4, none⟩ = some 6 ∧
    (eB.A[4]?).map (·.holder) = some (.place 5) ∧ ControlOf L0 eB ⟨4, some 5⟩ = some 6 := by
  decide

/-- After `transfer(M, M′)` (Spec 1 §63 effect: places owned by a part `r` of the source become
owned by `corr(r)`, and their roots follow by `RootHeld`), `T` is owned by `M′` and its root
authority 1 is held by `M′`. -/
theorem ownerA : (eA.P[3]?).map (·.owner) = some (.place 4) ∧
    (eA.A[1]?).map (·.holder) = some (.place 4) := by decide

/-! ## Transfers excluded by WC4 C22.3 (S16) -/

/-- WC4 S16, C22.3 (a): from `e2` (`KInvCA` and `SyncState` hold), `transfer(slot, Y)`
is an `ok` step of Spec 1 §63 re-indexed; `Encap` excludes it; after it, the kernel invariant
`KInvCA` holds, the entry is live, `guarded` is held by `Y`, which has no structural parent,
`ControlOf` is undefined, and `SyncInv` (WC4 C21.3 with the positional `ControlOf` of WC4 C12)
fails. -/
theorem slot_transfer_breaks_control :
    KInvCA e2 ∧ SyncState L0 e2 reg1 ∧ opStepC K0 (.transfer 1 7) 0 e2 (.ok eC) ∧
    ¬ Encap L0 (e2, reg1) (.kernel 0 (.transfer 1 7)) ∧ KInvCA eC ∧
    (⟨4, none⟩ : SyncEntry).Live eC ∧ (eC.A[4]?).map (·.holder) = some (.place 7) ∧
    parentOf eC.P 7 = none ∧ ControlOf L0 eC ⟨4, none⟩ = none ∧ ¬ SyncInv L0 eC reg1 := by
  obtain ⟨hk, hs⟩ := inv2
  refine ⟨hk, hs, stepC_transfer, encap_verdicts.2.2.1,
    lstep_kInvCA ddK0 (L := L0) (lbl := .kernel 0 (.transfer 1 7)) (st := (e2, reg1))
      (st' := (eC, reg1)) (.kernel stepC_transfer) hk, by decide, by decide, by decide, by decide,
    fun h => ?_⟩
  have := h.control ⟨4, none⟩ (List.mem_singleton_self _) (by decide)
  revert this; decide

/-- `transfer(lock = 2, Y = 7)` by context 0 after `newMutex` (Spec 1 §63). -/
def eD : SC := transferEffC e2 0 2 7

/-- WC4 S16 extended, C22.3 (c): from `e2`, `transfer(lock, Y)` is an `ok` step of
Spec 1 §63 re-indexed; `Encap` excludes it; after it, `KInvCA` holds, the entry is live, its
controller is still `lock` (place 2), which is `Moved`, and `SyncInv` fails (`ctlInit`, WC4
C21.7). -/
theorem ctl_transfer_breaks_ctlInit :
    opStepC K0 (.transfer 2 7) 0 e2 (.ok eD) ∧ ¬ Encap L0 (e2, reg1) (.kernel 0 (.transfer 2 7)) ∧
    KInvCA eD ∧ (⟨4, none⟩ : SyncEntry).Live eD ∧ ControlOf L0 eD ⟨4, none⟩ = some 2 ∧
    eD.I 2 = .moved ∧ ¬ SyncInv L0 eD reg1 := by
  have hst : opStepC K0 (.transfer 2 7) 0 e2 (.ok eD) := ⟨by decide, .ok (by decide)⟩
  refine ⟨hst, encap_verdicts.2.2.2,
    lstep_kInvCA ddK0 (L := L0) (lbl := .kernel 0 (.transfer 2 7)) (st := (e2, reg1))
      (st' := (eD, reg1)) (.kernel hst) inv2.1, by decide, by decide, by decide, fun h => ?_⟩
  have := h.ctlInit ⟨4, none⟩ (List.mem_singleton_self _) (by decide)
  revert this; decide

/-! ## `endUse` on the controller or on a strict part of `slot` (Spec 1 §69; WC4 C22.5, S17) -/

/-- `endUse(lock = 2)` by context 0 after `newMutex` (Spec 1 §69). -/
def eU : SC := e2.set (endUseEff (e2.view 0) 2)

/-- WC4 S17a, C22.5 (a): from `e2`, reached by the encapsulated trace `traceMutex`, `endUse(lock)`
is an `ok` step of Spec 1 §69 re-indexed and `Encap` excludes it. Without the exclusion, after the
step `KInvCA` holds, the entry is live, its controller `lock` (place 2) is `Uninit` (Spec 1 §69
effect: "The leaves of value `place` become `Uninit`"), and `SyncInv` fails (`ctlInit`, WC4
C21.7). -/
theorem endUse_ctl_excluded :
    EncapsulatedTrace K0 L0 (e0, [])
      [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 4 1), .newMutex 0 4 []] (e2, reg1) ∧
    opStepC K0 (.endUse 2) 0 e2 (.ok eU) ∧ ¬ Encap L0 (e2, reg1) (.kernel 0 (.endUse 2)) ∧
    KInvCA eU ∧ (⟨4, none⟩ : SyncEntry).Live eU ∧ ControlOf L0 eU ⟨4, none⟩ = some 2 ∧
    eU.I 2 = .uninit ∧ ¬ SyncInv L0 eU reg1 := by
  have hst : opStepC K0 (.endUse 2) 0 e2 (.ok eU) := ⟨by decide, _, .ok (by decide), rfl⟩
  refine ⟨traceMutex, hst,
    fun h => (h ⟨4, none⟩ (List.mem_singleton_self _) (by decide)).1 (by decide),
    lstep_kInvCA ddK0 (L := L0) (lbl := .kernel 0 (.endUse 2)) (st := (e2, reg1))
      (st' := (eU, reg1)) (.kernel hst) inv2.1, by decide, by decide, by decide, fun h => ?_⟩
  have := h.ctlInit ⟨4, none⟩ (List.mem_singleton_self _) (by decide)
  revert this; decide

/-- `endUse(M = 0)` by context 0 after `newMutex` (Spec 1 §69). -/
def eM : SC := e2.set (endUseEff (e2.view 0) 0)

/-- Positive twin of `endUse_ctl_excluded` (WC4 C22.5, S17b positive): from `e2`, `endUse(M)` is
an `ok` step of Spec 1 §69 re-indexed admitted by `Encap`; the entry is live before the step and
not after it (`guarded`, held by `slot`, a place of `M`, becomes inactive), and the encapsulated
trace ending with it reaches a state where `KInvCA` and `SyncState` (`SyncInv`, `GrantDiscipline`)
hold (`trace_inv`). -/
theorem endUse_mutex_kills_entry :
    EncapsulatedTrace K0 L0 (e0, [])
      [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 4 1), .newMutex 0 4 [],
       .kernel 0 (.endUse 0)] (eM, reg1) ∧
    (⟨4, none⟩ : SyncEntry).Live e2 ∧ ¬ (⟨4, none⟩ : SyncEntry).Live eM ∧
    KInvCA eM ∧ SyncState L0 eM reg1 := by
  have hst : opStepC K0 (.endUse 0) 0 e2 (.ok eM) := ⟨by decide, _, .ok (by decide), rfl⟩
  have he : Encap L0 (e2, reg1) (.kernel 0 (.endUse 0)) :=
    (by decide : ∀ e ∈ reg1, e.Live e2 → ControlOf L0 e2 e ≠ some 0 ∧
      OptP (slotOf e2 e.guarded) (fun q => partOf e2.P 0 q → 0 = q) True)
  have ht : EncapsulatedTrace K0 L0 (e0, [])
      [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 4 1), .newMutex 0 4 [],
       .kernel 0 (.endUse 0)] (eM, reg1) :=
    .cons (fun e he => by cases he) (.kernel step_derive) <|
    .cons trivial (.kernel step_store) <| .cons trivial (.newMutex step_newMutex.1) <|
    .cons he (.kernel hst) .nil
  obtain ⟨hk, hs⟩ := init_inv (k := K0) ddK0 est_ok L0
  exact ⟨ht, by decide, by decide, trace_inv ddK0 ht hk hs⟩

/-- Statics (Spec 1 §47): `0` the mutex value `M` with fields `1` (`slot`, a structure with the
leaves `2` and `3`) and `4` (`lock`), all leaves `Init`; `5` the root `T`, owned by `slot`. Root
authorities: `0` of `M`, `1` of `T` (held by `slot`, `guarded`). -/
def sst : Statics :=
  [((none, none, 0), false), ((some 0, none, 0), false), ((some 1, none, 0), true),
   ((some 1, none, 0), true), ((some 0, none, 0), true), ((none, some 1, 0), true)]

/-- The statics are well formed (Spec 1 §47). -/
theorem sst_ok : StaticsOK sst := by decide

/-- Initial single-context state of `sst`. -/
def z0 : SC := SC.ofS3 (S3.init sst)

/-- `newMutex(1)` is enabled in `z0` (WC4 C13). -/
theorem z_newMutex : NewMutexOk K0 L0 [] z0 [] 0 1 (z0, [⟨1, none⟩]) := ⟨by decide, by decide, rfl⟩

/-- `endUse(2)`, a strict part of `slot`, by context 0 (Spec 1 §69). -/
def z1 : SC := z0.set (endUseEff (z0.view 0) 2)

/-- WC4 S17b, C22.5 (b): from the initial state of `sst`, after the encapsulated step
`newMutex(1)`, `endUse(2)` on a strict structural subplace of `slot` is an `ok` step of Spec 1 §69
re-indexed and `Encap` excludes it. Without the exclusion, after the step `KInvCA` holds, the
entry is live, leaf 2 of `slot` is `Uninit`, and `SyncInv` fails (`slotInit`, WC4 C21.7). -/
theorem endUse_slotPart_excluded :
    EncapsulatedTrace K0 L0 (z0, []) [.newMutex 0 1 []] (z0, [⟨1, none⟩]) ∧
    opStepC K0 (.endUse 2) 0 z0 (.ok z1) ∧ ¬ Encap L0 (z0, [⟨1, none⟩]) (.kernel 0 (.endUse 2)) ∧
    KInvCA z1 ∧ (⟨1, none⟩ : SyncEntry).Live z1 ∧ slotOf z1 1 = some 1 ∧ z1.I 2 = .uninit ∧
    ¬ SyncInv L0 z1 [⟨1, none⟩] := by
  have hst : opStepC K0 (.endUse 2) 0 z0 (.ok z1) := ⟨by decide, _, .ok (by decide), rfl⟩
  have hk0 := (init_inv (k := K0) ddK0 sst_ok L0).1
  have hk : KInvCA z0 := lstep_kInvCA ddK0 (L := L0) (st := (z0, [])) (.newMutex z_newMutex) hk0
  refine ⟨.cons trivial (.newMutex z_newMutex) .nil, hst, fun h => ?_,
    lstep_kInvCA ddK0 (L := L0) (lbl := .kernel 0 (.endUse 2))
      (st := (z0, [⟨1, none⟩])) (st' := (z1, [⟨1, none⟩])) (.kernel hst) hk,
    by decide, by decide, by decide, fun h => ?_⟩
  · have := (h ⟨1, none⟩ (List.mem_singleton_self _) (by decide)).2
    revert this; decide
  · have := h.slotInit ⟨1, none⟩ (List.mem_singleton_self _) (by decide)
    revert this; decide

/-- `endUse(slot = 1)` by context 0 after `newMutex(1)` (Spec 1 §69). -/
def z2 : SC := z0.set (endUseEff (z0.view 0) 1)

/-- Positive twin of `endUse_slotPart_excluded` (WC4 C22.5, S17b positive): from `z0` with the
entry of `newMutex(1)`, `endUse(slot)` of the structured `slot` is an `ok` step of Spec 1 §69
re-indexed admitted by `Encap`; the entry is live before the step and not after it (`guarded`,
held by `slot`, becomes inactive), and the encapsulated trace ending with it reaches a state where
`KInvCA` and `SyncState` hold (`trace_inv`). -/
theorem endUse_slot_kills_entry :
    EncapsulatedTrace K0 L0 (z0, []) [.newMutex 0 1 [], .kernel 0 (.endUse 1)]
      (z2, [⟨1, none⟩]) ∧
    (⟨1, none⟩ : SyncEntry).Live z0 ∧ ¬ (⟨1, none⟩ : SyncEntry).Live z2 ∧
    KInvCA z2 ∧ SyncState L0 z2 [⟨1, none⟩] := by
  have hst : opStepC K0 (.endUse 1) 0 z0 (.ok z2) := ⟨by decide, _, .ok (by decide), rfl⟩
  have he : Encap L0 (z0, [⟨1, none⟩]) (.kernel 0 (.endUse 1)) :=
    (by decide : ∀ e ∈ ([⟨1, none⟩] : SyncReg), e.Live z0 → ControlOf L0 z0 e ≠ some 1 ∧
      OptP (slotOf z0 e.guarded) (fun q => partOf z0.P 1 q → 1 = q) True)
  have ht : EncapsulatedTrace K0 L0 (z0, []) [.newMutex 0 1 [], .kernel 0 (.endUse 1)]
      (z2, [⟨1, none⟩]) :=
    .cons trivial (.newMutex z_newMutex) <| .cons he (.kernel hst) .nil
  obtain ⟨hk, hs⟩ := init_inv (k := K0) ddK0 sst_ok L0
  exact ⟨ht, by decide, by decide, trace_inv ddK0 ht hk hs⟩

/-! ## Controller uniqueness after `endUse` (WC4 C21.4, C21.7, C22.3, C22.5) -/

/-- Statics: two mutex values `M₁ = {slot₁ = {a₁, b₁}, lock₁}` (places 0–4) and
`M₂ = {slot₂ = {a₂, b₂}, lock₂}` (places 5–9), all leaves `Init`; `T₁` (10) owned by `slot₁` and
`T₂` (11) owned by `slot₂`. Root authorities: 0 (`M₁`), 1 (`M₂`), 2 (`T₁`, held by `slot₁`), 3
(`T₂`, held by `slot₂`). -/
def ust : Statics :=
  [((none, none, 0), false), ((some 0, none, 0), false), ((some 1, none, 0), true),
   ((some 1, none, 0), true), ((some 0, none, 0), true),
   ((none, none, 0), false), ((some 5, none, 0), false), ((some 6, none, 0), true),
   ((some 6, none, 0), true), ((some 5, none, 0), true),
   ((none, some 1, 0), true), ((none, some 6, 0), true)]

/-- The statics are well formed (Spec 1 §47). -/
theorem ust_ok : StaticsOK ust := by decide

/-- Initial state of `ust`. -/
def u0 : SC := SC.ofS3 (S3.init ust)
/-- Registry after `newMutex(2)` and `newMutex(3)`. -/
def regU : SyncReg := [⟨2, none⟩, ⟨3, none⟩]
/-- `endUse(a₂ = 7)`. -/
def u1 : SC := u0.set (endUseEff (u0.view 0) 7)
/-- `endUse(b₂ = 8)`. -/
def u2 : SC := u1.set (endUseEff (u1.view 0) 8)
/-- `endUse(lock₂ = 9)`. -/
def u3 : SC := u2.set (endUseEff (u2.view 0) 9)
/-- `transfer(M₁ = 0, M₂ = 5)`. -/
def u4 : SC := transferEffC u3 0 0 5

/-- WC4 C21.4 fails along a run whose `endUse` steps break WC4 C21.7: from the initial state of
`ust`, the run `newMutex(2)`, `newMutex(3)`, `endUse` of the two leaves of `slot₂` and of `lock₂`,
then `transfer(M₁, M₂)` reaches a state where `KInvCA` holds, both entries are live, both have the
controller `lock₂` (place 9), and `SyncInv` fails. Its first `endUse` step is excluded by `Encap`
(WC4 C22.5 (b)), so the run is not an `EncapsulatedTrace` (`endUse_then_transfer_merges_false`). -/
theorem endUse_then_transfer_merges :
    LRun K0 L0 (u0, [])
      [.newMutex 0 2 [], .newMutex 0 3 [], .kernel 0 (.endUse 7), .kernel 0 (.endUse 8),
       .kernel 0 (.endUse 9), .kernel 0 (.transfer 0 5)] (u4, regU) ∧
    ¬ Encap L0 (u0, regU) (.kernel 0 (.endUse 7)) ∧ KInvCA u4 ∧
    (⟨2, none⟩ : SyncEntry).Live u4 ∧ (⟨3, none⟩ : SyncEntry).Live u4 ∧
    ControlOf L0 u4 ⟨2, none⟩ = some 9 ∧ ControlOf L0 u4 ⟨3, none⟩ = some 9 ∧
    ¬ SyncInv L0 u4 regU := by
  have h1 : NewMutexOk K0 L0 [] u0 [] 0 2 (u0, [⟨2, none⟩]) := ⟨by decide, by decide, rfl⟩
  have h2 : NewMutexOk K0 L0 [] u0 [⟨2, none⟩] 0 3 (u0, regU) := ⟨by decide, by decide, rfl⟩
  have h3 : opStepC K0 (.endUse 7) 0 u0 (.ok u1) := ⟨by decide, _, .ok (by decide), rfl⟩
  have h4 : opStepC K0 (.endUse 8) 0 u1 (.ok u2) := ⟨by decide, _, .ok (by decide), rfl⟩
  have h5 : opStepC K0 (.endUse 9) 0 u2 (.ok u3) := ⟨by decide, _, .ok (by decide), rfl⟩
  have h6 : opStepC K0 (.transfer 0 5) 0 u3 (.ok u4) := ⟨by decide, .ok (by decide)⟩
  have hr : LRun K0 L0 (u0, [])
      [.newMutex 0 2 [], .newMutex 0 3 [], .kernel 0 (.endUse 7), .kernel 0 (.endUse 8),
       .kernel 0 (.endUse 9), .kernel 0 (.transfer 0 5)] (u4, regU) :=
    .cons (.newMutex h1) <| .cons (.newMutex h2) <| .cons (.kernel h3) <| .cons (.kernel h4) <|
    .cons (.kernel h5) <| .cons (.kernel h6) .nil
  have hk0 := (init_inv (k := K0) ddK0 ust_ok L0).1
  have hk : KInvCA u4 := by
    have := lstep_kInvCA ddK0 (L := L0) (st := (u0, [])) (.newMutex h1) hk0
    have := lstep_kInvCA ddK0 (L := L0) (st := (u0, [⟨2, none⟩])) (.newMutex h2) this
    have := lstep_kInvCA ddK0 (L := L0) (st := (u0, regU)) (.kernel h3) this
    have := lstep_kInvCA ddK0 (L := L0) (st := (u1, regU)) (.kernel h4) this
    have := lstep_kInvCA ddK0 (L := L0) (st := (u2, regU)) (.kernel h5) this
    exact lstep_kInvCA ddK0 (L := L0) (st := (u3, regU)) (.kernel h6) this
  refine ⟨hr, fun h => ?_, hk, by decide, by decide, by decide, by decide, fun h => ?_⟩
  · have := (h ⟨3, none⟩ (by decide) (by decide)).2
    revert this; decide
  · have := h.ctlUnique 0 1 ⟨2, none⟩ ⟨3, none⟩ 9 rfl rfl (by decide) (by decide) (by decide)
      (by decide)
    cases this

/-- The run of `endUse_then_transfer_merges` is not an `EncapsulatedTrace` (WC4 C22.5 (b)): after
the two `newMutex` steps, whose results are determined, `Encap` excludes `endUse(a₂)`. -/
theorem endUse_then_transfer_merges_false (st : SC × SyncReg) :
    ¬ EncapsulatedTrace K0 L0 (u0, [])
      [.newMutex 0 2 [], .newMutex 0 3 [], .kernel 0 (.endUse 7), .kernel 0 (.endUse 8),
       .kernel 0 (.endUse 9), .kernel 0 (.transfer 0 5)] st := by
  intro h
  cases h with
  | cons _ h1 h2 =>
    cases h1 with
    | newMutex hn1 =>
      obtain ⟨-, -, rfl⟩ := hn1
      cases h2 with
      | cons _ h3 h4 =>
        cases h3 with
        | newMutex hn2 =>
          obtain ⟨-, -, rfl⟩ := hn2
          cases h4 with
          | cons he _ _ => exact endUse_then_transfer_merges.2.1 he

/-! ## `newMutex` on `Uninit` fields is rejected (WC4 C13.10) -/

/-- Statics (Spec 1 §47): `0` the mutex value `M` with fields `1` (`slot`) and `2` (`lock`), both
`Init`; `3` the root `T`, owned by `slot`; `4` the mutex value `M′` with fields `5` (`slot′`) and
`6` (`lock′`), both `Uninit`; `7` the root `T′`, owned by `slot′`. -/
def mst : Statics :=
  [((none, none, 0), false), ((some 0, none, 0), true), ((some 0, none, 0), true),
   ((none, some 1, 0), true), ((none, none, 0), false), ((some 4, none, 0), false),
   ((some 4, none, 0), false), ((none, some 5, 0), true)]

/-- Initial single-context state of `mst`. -/
def m0 : SC := SC.ofS3 (S3.init mst)

/-- WC4 C13.10 (`initM`): in `m0`, `newMutex(1)` is accepted and `newMutex(3)` is rejected, the
fields of `M′` being `Uninit`. -/
theorem newMutex_uninit_rejected : NewMutexOk K0 L0 [] m0 [] 0 1 (m0, [⟨1, none⟩]) ∧
    ¬ NewMutexPre K0 L0 [] m0 [⟨1, none⟩] 0 3 :=
  ⟨⟨by decide, by decide, rfl⟩, by decide⟩

/-- The labels `newMutex(1)`, `newMutex(3)`, `transfer(M, M′)` from `m0` form no run: the second
step, `newMutex(3)`, has no `ok` outcome (`newMutex_uninit_rejected`). -/
theorem transfer_merges_controllers_false (st : SC × SyncReg) :
    ¬ LRun K0 L0 (m0, []) [.newMutex 0 1 [], .newMutex 0 3 [], .kernel 0 (.transfer 0 4)] st := by
  intro h
  cases h with
  | cons h1 h2 =>
    cases h1 with
    | newMutex hn1 =>
      obtain ⟨-, -, rfl⟩ := hn1
      cases h2 with
      | cons h3 _ =>
        cases h3 with
        | newMutex hn2 => exact newMutex_uninit_rejected.2 hn2.2.1

end Ern.Concurrency.EncapTraces
