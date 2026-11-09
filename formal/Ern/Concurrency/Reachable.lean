import Ern.Concurrency.Preservation
import Ern.Concurrency.Reparent
import Ern.Concurrency.SyncInit

/-!
# Theorems 2 and 4 on labelled steps and traces (WC4 C20–C23)

Assembly of `Ern.Concurrency.Preservation`, `Ern.Concurrency.TransferPreserve`,
`Ern.Concurrency.Reparent` and `Ern.Concurrency.SyncInit`:

* theorem 2 for every labelled step of the kernel with the synchronization library, the by-value
  composite included (`lstep_kInvCA`);
* theorems 2 and 4 together along an `EncapsulatedTrace` (WC4 C22, C23): `KInvCA` and
  `SyncState` (`trace_inv`, `trace_preserves`, `encapsulated_inv`).
-/

namespace Ern.Concurrency

open Ern.MemoryModel.Access

/-- Theorem 2 (WC4 C20, C23) on every labelled step (inherited operations O1–O16 executed by a
context, `spawn`, the by-value composite, `terminate`, `join`, `deriveSync` under the library
instantiation, `newMutex`, `acquire`, `unlock`, `resetLock`): the re-indexed kernel invariant with
the auxiliaries of Spec 1 (`KInvCA`) is preserved, under `DDSound` (Spec 1 §80, for `split`). -/
theorem lstep_kInvCA {k : K} {L : MutexLayout} {lbl : Label} {st st' : SC × SyncReg}
    (hdd : DDSound k) (h : LStep k L lbl st st') (hk : KInvCA st.1) : KInvCA st'.1 := by
  cases h with
  | @kernel s s' reg c op h =>
    cases op
    case exit => exact exitFrameC_preserves hk.1 hk.2.1 hk.2.2 h
    all_goals exact opStepC_preservesC hdd hk (fun e => by cases e) h
  | spawn h => exact spawn_preservesC hk h
  | spawnVal h => exact spawnVal_preservesC hk h
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

/-- Theorems 2 and 4 (WC4 C20–C23) along an `EncapsulatedTrace`: from a state satisfying
`KInvCA` and `SyncState`, every reached state satisfies both, under `DDSound` (Spec 1 §80). -/
theorem trace_inv {k : K} {L : MutexLayout} {st st' : SC × SyncReg} {lbls : List Label}
    (hdd : DDSound k) (h : EncapsulatedTrace k L st lbls st') (hk : KInvCA st.1)
    (hs : SyncState L st.1 st.2) : KInvCA st'.1 ∧ SyncState L st'.1 st'.2 := by
  induction h with
  | nil => exact ⟨hk, hs⟩
  | cons he hst _ ih =>
    have hk' := lstep_kInvCA hdd hst hk
    exact ih hk' (lstep_preserves hst he hk hk'.1.1.2 hs)

/-- Theorem 4 (WC4 C21–C23), trace form: along an `EncapsulatedTrace` from a state satisfying
`KInvCA`, `SyncState` is preserved, under `DDSound` (Spec 1 §80). -/
theorem trace_preserves {k : K} {L : MutexLayout} {st st' : SC × SyncReg} {lbls : List Label}
    (hdd : DDSound k) (h : EncapsulatedTrace k L st lbls st') (hk : KInvCA st.1)
    (hs : SyncState L st.1 st.2) : SyncState L st'.1 st'.2 :=
  (trace_inv hdd h hk hs).2

/-- The initial state of Spec 1 §47 as a single-context state, with an empty registry (WC4 C3,
C12), satisfies `KInvCA` and `SyncState`. -/
theorem init_inv {k : K} {statics : Statics} (hdd : DDSound k) (hst : StaticsOK statics)
    (L : MutexLayout) :
    KInvCA (SC.ofS3 (S3.init statics)) ∧ SyncState L (SC.ofS3 (S3.init statics)) [] := by
  obtain ⟨-, -, -, hkc⟩ := reachable_single (k := k) hdd hst .init
  obtain ⟨-, haux, hh⟩ := init_kinv hst
  have hflat : (SC.ofS3 (S3.init statics)).flat = S3.init statics := by
    rw [single_flat ⟨_, rfl⟩, toS3_ofS3]
  refine ⟨⟨hkc, by rw [hflat]; exact haux, by rw [hflat]; exact hh⟩, ?_⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro e he; cases he
  · intro e he; cases he
  · intro e he; cases he
  · intro i j e e' ctl h; simp at h
  · intro i j e e' h; simp at h
  · intro e he; cases he
  · intro e he; cases he
  · intro e he; cases he
  · intro e he; cases he
  · intro e he; cases he

/-- Theorems 2 and 4 (WC4 C20–C23) from the initial state: every state reached from the initial
state of Spec 1 §47 (one context, empty registry) by an `EncapsulatedTrace` satisfies the
re-indexed kernel invariant `KInvC`, `SyncInv` and `GrantDiscipline`, under `DDSound` (Spec 1 §80)
and well-formed statics (Spec 1 §47). -/
theorem encapsulated_inv {k : K} {L : MutexLayout} {statics : Statics} {lbls : List Label}
    {st' : SC × SyncReg} (hdd : DDSound k) (hst : StaticsOK statics)
    (h : EncapsulatedTrace k L (SC.ofS3 (S3.init statics), []) lbls st') :
    KInvC st'.1 ∧ SyncInv L st'.1 st'.2 ∧ GrantDiscipline st'.1 st'.2 := by
  obtain ⟨hk, hs⟩ := init_inv (k := k) hdd hst L
  obtain ⟨hk', hs'⟩ := trace_inv hdd h hk hs
  exact ⟨hk'.1, hs'.1, hs'.2⟩

end Ern.Concurrency
