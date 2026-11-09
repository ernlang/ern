import Ern.Concurrency.Reachable
import Ern.Concurrency.Traces

/-!
# Mutex transfer and `Encap` (test module)

Concrete runs checking the transfer clause of `Encap` (WC3 C22.3) against WC3 C12 (a legal
transfer of the whole mutex value preserves the association positionally), S7 and S16:

* a mutex value `M = {slot, lock}` owning the protected root `T`; `guarded` is a `Modify`
  derivative of the root authority of `T`, stored in `slot` (Spec 1 §60, §65); `M′ = {slot′, lock′}`
  is a place of the same shape in the same frame; `Y` is a one-leaf place;
* variant A (`grant = none`) and variant B (an active grant held by the current frame, after
  `acquire`): `transfer(M, M′)` is an `ok` step of Spec 1 §63 re-indexed, admitted by `Encap`;
  `KInvC`, `SyncInv` and `GrantDiscipline` hold after it, and `ControlOf` designates `lock′` (S16,
  positive half);
* `transfer(slot, Y)`: an `ok` step of Spec 1 §63 re-indexed, not admitted by `Encap`, after which
  `KInvC` holds and `SyncInv` fails (`ControlOf` is undefined) (S16);
* `transfer(M, M′)` onto a mutex value `M′` whose field `slot′` owns the protected root of another
  live entry: an `ok` step admitted by `Encap`, after which both entries have the controller
  `lock′` and controller uniqueness (WC3 C21.4) fails (`transfer_merges_controllers`).
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

/-- Registry after `newMutex(4)` (WC3 C13). -/
def reg1 : SyncReg := [⟨4, none⟩]

/-- Variant A: `transfer(M = 0, M′ = 4)` by context 0 with `grant = none` (Spec 1 §63). -/
def eA : SC := transferEffC e2 0 0 4

/-- Variant B, first step: `acquire` on entry 0 (WC3 C16): grant authority 5, held by frame 0. -/
def e3 : SC := deriveSyncEff e2 0 4

/-- Registry after `acquire` (WC3 C16). -/
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

/-- `newMutex(4)` is enabled (WC3 C13); its controller is `lock` (place 2). -/
theorem step_newMutex : NewMutexOk K0 L0 [] e2 [] 0 4 (e2, reg1) ∧
    ControlOf L0 e2 ⟨4, none⟩ = some 2 :=
  ⟨⟨by decide, by decide, rfl⟩, by decide⟩

/-- `acquire` is enabled (WC3 C16); the grant 5 is an active `Modify` derivative of `guarded` over
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

/-- The transfer clause of `Encap` (WC3 C22.3) compares the source of O4 with the place holding
`guarded`, for every live entry; it says nothing of other places. -/
theorem encap_transfer_iff (st : SC × SyncReg) (c src dst : Nat) :
    Encap st (.kernel c (.transfer src dst)) ↔
      ∀ e ∈ st.2, e.Live st.1 → (st.1.A[e.guarded]?).map (·.holder) ≠ some (.place src) :=
  Iff.rfl

/-- In `e2`, `guarded` (authority 4) is held by `slot` (place 1), a field of `M` (place 0). -/
theorem guarded_in_slot : (e2.A[4]?).map (·.holder) = some (.place 1) ∧
    parentOf e2.P 1 = some 0 := by decide

/-- Verdict (b): `Encap` admits `transfer(M, M′)` in both variants and excludes
`transfer(slot, Y)`. -/
theorem encap_verdicts : Encap (e2, reg1) (.kernel 0 (.transfer 0 4)) ∧
    Encap (e3, reg2) (.kernel 0 (.transfer 0 4)) ∧
    ¬ Encap (e2, reg1) (.kernel 0 (.transfer 1 7)) := by
  refine ⟨fun e he _ => ?_, fun e he _ => ?_, fun h => h ⟨4, none⟩ (by decide) (by decide) ?_⟩
  · simp only [reg1, List.mem_singleton] at he; subst he; decide
  · simp only [reg2, List.mem_singleton] at he; subst he; decide
  · decide

/-! ## Encapsulated traces and invariants -/

/-- Variant A as an encapsulated trace from the initial state with an empty registry (WC3 C22,
C23). -/
theorem traceA : EncapsulatedTrace K0 L0 (e0, [])
    [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 4 1), .newMutex 0 4 [],
     .kernel 0 (.transfer 0 4)] (eA, reg1) :=
  .cons (fun e he => by cases he) (.kernel step_derive) <|
  .cons trivial (.kernel step_store) <|
  .cons trivial (.newMutex step_newMutex.1) <|
  .cons encap_verdicts.1 (.kernel stepA_transfer) .nil

/-- Variant B as an encapsulated trace from the initial state with an empty registry (WC3 C22,
C23). -/
theorem traceB : EncapsulatedTrace K0 L0 (e0, [])
    [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 4 1), .newMutex 0 4 [],
     .acquire 0 0, .kernel 0 (.transfer 0 4)] (eB, reg2) :=
  .cons (fun e he => by cases he) (.kernel step_derive) <|
  .cons trivial (.kernel step_store) <|
  .cons trivial (.newMutex step_newMutex.1) <|
  .cons trivial (.acquire step_acquire.1) <|
  .cons encap_verdicts.2.1 (.kernel stepB_transfer) .nil

/-- The trace up to `newMutex` (WC3 C13), encapsulated. -/
theorem traceMutex : EncapsulatedTrace K0 L0 (e0, [])
    [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 4 1), .newMutex 0 4 []] (e2, reg1) :=
  .cons (fun e he => by cases he) (.kernel step_derive) <|
  .cons trivial (.kernel step_store) <|
  .cons trivial (.newMutex step_newMutex.1) .nil

/-- Controller uniqueness (WC3 C21.4) holds for a registry of one entry. -/
theorem ctlUnique_single (L : MutexLayout) (s : SC) (e : SyncEntry) : CtlUnique L s [e] := by
  intro i j _ _ _ hi hj _ _ _ _
  have h1 : i < 1 := lt_of_getElem? hi
  have h2 : j < 1 := lt_of_getElem? hj
  omega

/-- Verdict (c), variant A (from `trace_inv`, `init_inv`, and `ctlUnique_single` for the
registry of one entry): after `transfer(M, M′)`, `KInvC` (with the auxiliaries of Spec 1) and
`SyncState` (`SyncInv`, `GrantDiscipline`) hold, and the entry is live. -/
theorem invA : KInvCA eA ∧ SyncState L0 eA reg1 ∧ (⟨4, none⟩ : SyncEntry).Live eA := by
  obtain ⟨hk, hs⟩ := init_inv (k := K0) ddK0 est_ok L0
  obtain ⟨hk', hs'⟩ := trace_inv ddK0 traceA hk (syncState_iff.1 hs).1
  exact ⟨hk', syncState_iff.2 ⟨hs', ctlUnique_single _ _ _⟩, by decide⟩

/-- Verdict (c), variant B (from `trace_inv`, `init_inv` and `ctlUnique_single`): after
`transfer(M, M′)`, `KInvC` (with the auxiliaries of Spec 1) and `SyncState` hold; the entry is
live and the grant 5 is still active and held by frame 0. -/
theorem invB : KInvCA eB ∧ SyncState L0 eB reg2 ∧ (⟨4, some 5⟩ : SyncEntry).Live eB ∧
    eB.A[5]? = some ⟨.modify, some 4, [3], .frame 0, true⟩ := by
  obtain ⟨hk, hs⟩ := init_inv (k := K0) ddK0 est_ok L0
  obtain ⟨hk', hs'⟩ := trace_inv ddK0 traceB hk (syncState_iff.1 hs).1
  exact ⟨hk', syncState_iff.2 ⟨hs', ctlUnique_single _ _ _⟩, by decide, by decide⟩

/-- Verdict (d), WC3 S16 positive half: after `transfer(M, M′)`, in both variants, `guarded` is
held by `slot′` (place 5) and `ControlOf` designates `lock′` (place 6) (WC3 C12, positional). -/
theorem controlAB : (eA.A[4]?).map (·.holder) = some (.place 5) ∧
    ControlOf L0 eA ⟨4, none⟩ = some 6 ∧
    (eB.A[4]?).map (·.holder) = some (.place 5) ∧ ControlOf L0 eB ⟨4, some 5⟩ = some 6 := by
  decide

/-- After `transfer(M, M′)` (Spec 1 §63 effect: places owned by a part `r` of the source become
owned by `corr(r)`, and their roots follow by `RootHeld`), `T` is owned by `M′` and its root
authority 1 is held by `M′`. -/
theorem ownerA : (eA.P[3]?).map (·.owner) = some (.place 4) ∧
    (eA.A[1]?).map (·.holder) = some (.place 4) := by decide

/-! ## `transfer(slot, Y)` without the exclusion -/

/-- WC3 S16, C22.3: without the transfer clause of `Encap`, `SyncInv` is not preserved: from `e2`
(reached by an encapsulated trace without transfer, so `KInvC` and `SyncState` hold),
`transfer(slot, Y)` is an `ok` step of Spec 1 §63 re-indexed; `Encap` excludes it (WC3 C22.3);
after it, the kernel invariant `KInvCA` holds, the entry is live, `guarded` is held by `Y`, which
has no structural parent, `ControlOf` is undefined, and `SyncInv` (WC3 C21.3 with the positional
`ControlOf` of WC3 C12) fails. -/
theorem slot_transfer_breaks_control :
    KInvCA e2 ∧ SyncState L0 e2 reg1 ∧ opStepC K0 (.transfer 1 7) 0 e2 (.ok eC) ∧
    ¬ Encap (e2, reg1) (.kernel 0 (.transfer 1 7)) ∧ KInvCA eC ∧
    (⟨4, none⟩ : SyncEntry).Live eC ∧ (eC.A[4]?).map (·.holder) = some (.place 7) ∧
    parentOf eC.P 7 = none ∧ ControlOf L0 eC ⟨4, none⟩ = none ∧ ¬ SyncInv L0 eC reg1 := by
  obtain ⟨hk0, hs0⟩ := init_inv (k := K0) ddK0 est_ok L0
  obtain ⟨hk, hs⟩ := trace_inv_noTransfer ddK0 traceMutex (fun l hl => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl <;> trivial) hk0 hs0
  refine ⟨hk, hs, stepC_transfer, encap_verdicts.2.2,
    lstep_kInvCA ddK0 (L := L0) (lbl := .kernel 0 (.transfer 1 7)) (st := (e2, reg1)) (st' := (eC, reg1))
      (.kernel stepC_transfer) hk, by decide, by decide, by decide, by decide, fun h => ?_⟩
  have := h.control ⟨4, none⟩ (List.mem_singleton_self _) (by decide)
  revert this; decide

/-! ## `transfer(M, M′)` onto a live mutex value (WC3 C12, C21.4, C22.3) -/

/-- Statics (Spec 1 §47): `0` the mutex value `M` with fields `1` (`slot`) and `2` (`lock`), both
`Init`; `3` the root `T`, owned by `slot`; `4` the mutex value `M′` with fields `5` (`slot′`) and
`6` (`lock′`), both `Uninit`; `7` the root `T′`, owned by `slot′`. Root authorities: `0` of `M`,
`1` of `T` (held by `slot`), `2` of `M′`, `3` of `T′` (held by `slot′`). -/
def mst : Statics :=
  [((none, none, 0), false), ((some 0, none, 0), true), ((some 0, none, 0), true),
   ((none, some 1, 0), true), ((none, none, 0), false), ((some 4, none, 0), false),
   ((some 4, none, 0), false), ((none, some 5, 0), true)]

/-- The statics are well formed (Spec 1 §47). -/
theorem mst_ok : StaticsOK mst := by decide

/-- Initial single-context state of `mst` (Spec 1 §47). -/
def m0 : SC := SC.ofS3 (S3.init mst)

/-- Registry after `newMutex(1)` and `newMutex(3)` (WC3 C13). -/
def regM : SyncReg := [⟨1, none⟩, ⟨3, none⟩]

/-- `transfer(M = 0, M′ = 4)` by context 0 (Spec 1 §63). -/
def m1 : SC := transferEffC m0 0 0 4

/-- `newMutex(1)` and `newMutex(3)` are enabled (WC3 C13, with C13.8: distinct controllers `lock`
and `lock′`), and `transfer(M, M′)` is an `ok` step of Spec 1 §63 re-indexed, admitted by `Encap`
(WC3 C22.3: its source is `M`, not a place holding a `guarded`). -/
theorem merge_steps : NewMutexOk K0 L0 [] m0 [] 0 1 (m0, [⟨1, none⟩]) ∧
    NewMutexOk K0 L0 [] m0 [⟨1, none⟩] 0 3 (m0, regM) ∧
    ControlOf L0 m0 ⟨1, none⟩ = some 2 ∧ ControlOf L0 m0 ⟨3, none⟩ = some 6 ∧
    opStepC K0 (.transfer 0 4) 0 m0 (.ok m1) ∧ Encap (m0, regM) (.kernel 0 (.transfer 0 4)) := by
  refine ⟨⟨by decide, by decide, rfl⟩, ⟨by decide, by decide, rfl⟩, by decide, by decide,
    ⟨by decide, .ok (by decide)⟩, fun e he _ => ?_⟩
  simp only [regM, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl <;> decide

/-- WC3 C21.4 is not preserved by an encapsulated `transfer(M, M′)`: from the initial state of
`mst` with an empty registry, the encapsulated trace `newMutex(1)`, `newMutex(3)`,
`transfer(M, M′)` reaches a state where `KInvCA` and `SyncCore` hold, both entries are live,
`guarded` 1 and `guarded` 3 are both held by `slot′` (place 5), both have the controller `lock′`
(place 6), and `SyncInv` fails. -/
theorem transfer_merges_controllers :
    EncapsulatedTrace K0 L0 (m0, [])
      [.newMutex 0 1 [], .newMutex 0 3 [], .kernel 0 (.transfer 0 4)] (m1, regM) ∧
    KInvCA m1 ∧ SyncCore L0 m1 regM ∧
    (⟨1, none⟩ : SyncEntry).Live m1 ∧ (⟨3, none⟩ : SyncEntry).Live m1 ∧
    (m1.A[1]?).map (·.holder) = some (.place 5) ∧ (m1.A[3]?).map (·.holder) = some (.place 5) ∧
    ControlOf L0 m1 ⟨1, none⟩ = some 6 ∧ ControlOf L0 m1 ⟨3, none⟩ = some 6 ∧
    ¬ SyncInv L0 m1 regM := by
  obtain ⟨h1, h2, -, -, h3, he⟩ := merge_steps
  have ht : EncapsulatedTrace K0 L0 (m0, [])
      [.newMutex 0 1 [], .newMutex 0 3 [], .kernel 0 (.transfer 0 4)] (m1, regM) :=
    .cons trivial (.newMutex h1) <| .cons trivial (.newMutex h2) <|
    .cons he (.kernel h3) .nil
  obtain ⟨hk0, hs0⟩ := init_inv (k := K0) ddK0 mst_ok L0
  obtain ⟨hk, hs⟩ := trace_inv ddK0 ht hk0 (syncState_iff.1 hs0).1
  refine ⟨ht, hk, hs, by decide, by decide, by decide, by decide, by decide, by decide,
    fun h => ?_⟩
  have := h.ctlUnique 0 1 ⟨1, none⟩ ⟨3, none⟩ 6 rfl rfl (by decide) (by decide) (by decide)
    (by decide)
  cases this

end Ern.Concurrency.EncapTraces
