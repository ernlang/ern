import Ern.Concurrency.Preservation
import Ern.Concurrency.Reparent
import Ern.Concurrency.SyncPreserve

/-!
# Theorems 2 and 4 on labelled steps and traces (WC3 C20–C23)

Assembly of `Ern.Concurrency.Preservation`, `Ern.Concurrency.Reparent` and
`Ern.Concurrency.SyncPreserve`:

* theorem 2 for every labelled step of the kernel with the synchronization library
  (`lstep_kInvCA`);
* theorems 2 and 4 together along an encapsulated trace: `SyncCore` (every clause of `SyncInv` and
  `GrantDiscipline` other than controller uniqueness, WC3 C21.4) on every trace (`trace_inv`,
  `encapsulated_inv`), and `SyncState` on traces without kernel transfer
  (`trace_inv_noTransfer`, `encapsulated_inv_noTransfer`).
-/

namespace Ern.Concurrency

open Ern.MemoryModel.Access

/-- Theorem 2 (WC3 C20, C23) on every labelled step (inherited operations O1–O16 executed by a
context, `spawn`, `terminate`, `join`, `deriveSync` under the library instantiation, `newMutex`,
`acquire`, `unlock`, `resetLock`): the re-indexed kernel invariant with the auxiliaries of Spec 1
(`KInvCA`) is preserved, under `DDSound` (Spec 1 §80, for `split`). Fragment: the concurrent kernel
with the reference synchronization library, without the by-value `spawn` composite. -/
theorem lstep_kInvCA {k : K} {L : MutexLayout} {lbl : Label} {st st' : SC × SyncReg}
    (hdd : DDSound k) (h : LStep k L lbl st st') (hk : KInvCA st.1) : KInvCA st'.1 := by
  cases h with
  | @kernel s s' reg c op h =>
    cases op
    case exit => exact exitFrameC_preserves hk.1 hk.2.1 hk.2.2 h
    all_goals exact opStepC_preservesC hdd hk (fun e => by cases e) h
  | spawn h => exact spawn_preservesC hk h
  | terminate h => exact terminate_preserves hk.1 hk.2.1 hk.2.2 h
  | join h => exact join_preservesC hk h
  | deriveSync h => exact deriveSync_preservesC hk h
  | newMutex h => obtain ⟨-, -, rfl⟩ := h; exact hk
  | acquire h =>
    obtain ⟨hc, e, -, -, hpre, rfl⟩ := h
    exact deriveSync_preservesC (r := _) hk ⟨hc, .ok hpre⟩
  | unlock h =>
    obtain ⟨hc, e, g, -, -, -, hrel, -, rfl⟩ := h
    exact opStepC_preservesC (op := .release g) hdd hk (fun e => by cases e)
      ⟨hc, _, .ok hrel, rfl⟩
  | resetLock h => obtain ⟨-, -, -, -, -, -, rfl⟩ := h; exact hk

/-- Theorems 2 and 4 (WC3 C20–C23) along an encapsulated trace: from a state satisfying `KInvCA`
and `SyncCore`, every state reached by an `EncapsulatedTrace` satisfies both, under `DDSound`
(Spec 1 §80). Controller uniqueness (WC3 C21.4) is not included: see `trace_inv_noTransfer`. -/
theorem trace_inv {k : K} {L : MutexLayout} {st st' : SC × SyncReg} {lbls : List Label}
    (hdd : DDSound k) (h : EncapsulatedTrace k L st lbls st') (hk : KInvCA st.1)
    (hs : SyncCore L st.1 st.2) : KInvCA st'.1 ∧ SyncCore L st'.1 st'.2 := by
  induction h with
  | nil => exact ⟨hk, hs⟩
  | cons he hst _ ih =>
    have hk' := lstep_kInvCA hdd hst hk
    exact ih hk' (lstep_preserves hst he hk.1.1.2 hk'.1.1.2 hs)

/-- Theorems 2 and 4 (WC3 C20–C23) along an encapsulated trace without kernel transfer: from a
state satisfying `KInvCA` and `SyncState`, every state reached satisfies both, under `DDSound`
(Spec 1 §80). -/
theorem trace_inv_noTransfer {k : K} {L : MutexLayout} {st st' : SC × SyncReg}
    {lbls : List Label} (hdd : DDSound k) (h : EncapsulatedTrace k L st lbls st')
    (hnt : ∀ lbl ∈ lbls, lbl.NotTransfer) (hk : KInvCA st.1) (hs : SyncState L st.1 st.2) :
    KInvCA st'.1 ∧ SyncState L st'.1 st'.2 := by
  induction h with
  | nil => exact ⟨hk, hs⟩
  | cons he hst _ ih =>
    have hk' := lstep_kInvCA hdd hst hk
    exact ih (fun l hl => hnt l (List.mem_cons_of_mem _ hl)) hk'
      (lstep_syncState hst he (hnt _ (List.mem_cons_self ..)) hk.1.1.2 hk'.1.1.2 hs)

/-- The initial state of Spec 1 §47 as a single-context state, with an empty registry (WC3 C3,
C12), satisfies `KInvCA` and `SyncState`. -/
theorem init_inv {k : K} {statics : Statics} (hdd : DDSound k) (hst : StaticsOK statics)
    (L : MutexLayout) :
    KInvCA (SC.ofS3 (S3.init statics)) ∧ SyncState L (SC.ofS3 (S3.init statics)) [] := by
  obtain ⟨-, -, -, hkc⟩ := reachable_single (k := k) hdd hst .init
  obtain ⟨-, haux, hh⟩ := init_kinv hst
  have hflat : (SC.ofS3 (S3.init statics)).flat = S3.init statics := by
    rw [single_flat ⟨_, rfl⟩, toS3_ofS3]
  refine ⟨⟨hkc, by rw [hflat]; exact haux, by rw [hflat]; exact hh⟩, ?_⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro e he; cases he
  · intro e he; cases he
  · intro e he; cases he
  · intro i j e e' ctl h; simp at h
  · intro i j e e' h; simp at h
  · intro e he; cases he
  · intro e he; cases he
  · intro e he; cases he

/-- Theorems 2 and 4 (WC3 C20–C23) on encapsulated traces from the initial state, every clause
other than controller uniqueness: every state reached from the initial state of Spec 1 §47 (one
context, empty registry) by an `EncapsulatedTrace` satisfies the re-indexed kernel invariant
`KInvC` and `SyncCore`, under `DDSound` (Spec 1 §80) and well-formed statics (Spec 1 §47).
Fragment: the concurrent kernel with the reference synchronization library, without the by-value
`spawn` composite; encapsulation is the hypothesis `EncapsulatedTrace`. -/
theorem encapsulated_inv {k : K} {L : MutexLayout} {statics : Statics} {lbls : List Label}
    {st' : SC × SyncReg} (hdd : DDSound k) (hst : StaticsOK statics)
    (h : EncapsulatedTrace k L (SC.ofS3 (S3.init statics), []) lbls st') :
    KInvC st'.1 ∧ SyncCore L st'.1 st'.2 := by
  obtain ⟨hk, hs⟩ := init_inv (k := k) hdd hst L
  obtain ⟨hk', hs'⟩ := trace_inv hdd h hk (syncState_iff.1 hs).1
  exact ⟨hk'.1, hs'⟩

/-- Theorems 2 and 4 (WC3 C20–C23) on encapsulated traces without kernel transfer from the initial
state: every reached state satisfies `KInvC`, `SyncInv` and `GrantDiscipline`, under `DDSound`
(Spec 1 §80) and well-formed statics (Spec 1 §47). -/
theorem encapsulated_inv_noTransfer {k : K} {L : MutexLayout} {statics : Statics}
    {lbls : List Label} {st' : SC × SyncReg} (hdd : DDSound k) (hst : StaticsOK statics)
    (h : EncapsulatedTrace k L (SC.ofS3 (S3.init statics), []) lbls st')
    (hnt : ∀ lbl ∈ lbls, lbl.NotTransfer) :
    KInvC st'.1 ∧ SyncInv L st'.1 st'.2 ∧ GrantDiscipline st'.1 st'.2 := by
  obtain ⟨hk, hs⟩ := init_inv (k := k) hdd hst L
  obtain ⟨hk', hs'⟩ := trace_inv_noTransfer hdd h hnt hk hs
  exact ⟨hk'.1, hs'.1, hs'.2⟩

end Ern.Concurrency
