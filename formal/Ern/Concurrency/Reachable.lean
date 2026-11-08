import Ern.Concurrency.Preservation
import Ern.Concurrency.Reparent
import Ern.Concurrency.SyncPreserve

/-!
# Theorems 2 and 4 on labelled steps and traces (WC2 C20–C23)

Assembly of `Ern.Concurrency.Preservation`, `Ern.Concurrency.Reparent` and
`Ern.Concurrency.SyncPreserve`:

* theorem 2 for every labelled step of the kernel with the synchronization library
  (`lstep_kInvCA`): `deriveSync` and `acquire` need the own mode `Modify` of `guarded`, which
  `SyncInv` (WC2 C21.1) provides for the library instantiation of `SyncAuthorized`;
* theorems 2 and 4 together along an encapsulated trace (`trace_inv`), and from the initial state
  of Spec 1 §47 with an empty registry (`encapsulated_inv`).
-/

namespace Ern.Concurrency

open Ern.MemoryModel.Access

/-- WC2 C21.1: under `SyncInv`, the `guarded` of a live entry has own mode `Modify`. -/
theorem guarded_mode {L : MutexLayout} {s : SC} {reg : SyncReg} {e : SyncEntry}
    (hsi : SyncInv L s reg) (he : e ∈ reg) (hl : e.Live s) :
    OptP (s.A[e.guarded]?) (fun y => y.mode = .modify) False := by
  have h := hsi.guarded e he hl
  revert h; unfold OptP
  cases s.A[e.guarded]? with
  | none => exact id
  | some y => exact fun h => h.1

/-- Theorem 2 (WC2 C20, C23) on every labelled step (inherited operations O1–O16 executed by a
context, `spawn`, `terminate`, `join`, `deriveSync` under the library instantiation, `newMutex`,
`acquire`, `unlock`, `resetLock`): the re-indexed kernel invariant with the auxiliaries of Spec 1
(`KInvCA`) is preserved, under `DDSound` (Spec 1 §80, for `split`) and `SyncInv` (WC2 C21, for the
own mode of `guarded` in `deriveSync` and `acquire`). Fragment: the concurrent kernel with the
reference synchronization library, without the by-value `spawn` composite. -/
theorem lstep_kInvCA {k : K} {L : MutexLayout} {lbl : Label} {st st' : SC × SyncReg}
    (hdd : DDSound k) (h : LStep k L lbl st st') (hk : KInvCA st.1) (hsi : SyncInv L st.1 st.2) :
    KInvCA st'.1 := by
  cases h with
  | @kernel s s' reg c op h =>
    by_cases hx : op = .exit
    · subst hx; exact exitFrameC_preserves hk.1 hk.2.1 hk.2.2 h
    · exact opStepC_preservesC hdd hk hx h
  | spawn h => exact spawn_preservesC hk h
  | terminate h => exact terminate_preserves hk.1 hk.2.1 hk.2.2 h
  | join h => exact join_preservesC hk h
  | deriveSync h =>
    have hpre := (Guarded.ok_iff.1 h.2).1
    obtain ⟨e, he, hg, hl, -⟩ := hpre.authorized
    exact deriveSync_preservesC hk (hg ▸ guarded_mode hsi he hl) h
  | newMutex h => obtain ⟨-, -, rfl⟩ := h; exact hk
  | acquire h =>
    obtain ⟨hc, e, hi, ⟨hl, -, -⟩, hpre, rfl⟩ := h
    exact deriveSync_preservesC hk (guarded_mode hsi (List.mem_of_getElem? hi) hl)
      ⟨hc, .ok hpre⟩
  | unlock h =>
    obtain ⟨hc, e, g, -, -, -, hrel, -, rfl⟩ := h
    exact opStepC_preservesC (op := .release g) hdd hk (fun e => by cases e)
      ⟨hc, _, .ok hrel, rfl⟩
  | resetLock h => obtain ⟨-, -, -, -, -, rfl⟩ := h; exact hk

/-- Theorems 2 and 4 (WC2 C20–C23) along an encapsulated trace: from a state satisfying `KInvCA`
and `SyncState` (`SyncInv`, `GrantDiscipline` and their auxiliaries), every state reached by an
`EncapsulatedTrace` satisfies both, under `DDSound` (Spec 1 §80). -/
theorem trace_inv {k : K} {L : MutexLayout} {st st' : SC × SyncReg} {lbls : List Label}
    (hdd : DDSound k) (h : EncapsulatedTrace k L st lbls st') (hk : KInvCA st.1)
    (hs : SyncState L st.1 st.2) : KInvCA st'.1 ∧ SyncState L st'.1 st'.2 := by
  induction h with
  | nil => exact ⟨hk, hs⟩
  | cons he hst _ ih =>
    have hk' := lstep_kInvCA hdd hst hk hs.1
    exact ih hk' (lstep_preserves hst he hk.1.1.2 hk'.1.1.2 hs)

/-- The initial state of Spec 1 §47 as a single-context state, with an empty registry (WC2 C3,
C12), satisfies `KInvCA` and `SyncState`. -/
theorem init_inv {k : K} {statics : Statics} (hdd : DDSound k) (hst : StaticsOK statics)
    (L : MutexLayout) :
    KInvCA (SC.ofS3 (S3.init statics)) ∧ SyncState L (SC.ofS3 (S3.init statics)) [] := by
  obtain ⟨-, -, -, hkc⟩ := reachable_single (k := k) hdd hst .init
  obtain ⟨-, haux, hh⟩ := init_kinv hst
  have hflat : (SC.ofS3 (S3.init statics)).flat = S3.init statics := by
    rw [single_flat ⟨_, rfl⟩, toS3_ofS3]
  refine ⟨⟨hkc, by rw [hflat]; exact haux, by rw [hflat]; exact hh⟩, ?_⟩
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro e he; cases he
  · intro e he; cases he
  · intro e he; cases he
  · intro i j e e' h; simp at h
  · intro e he; cases he
  · intro e he; cases he
  · intro e he; cases he

/-- Theorems 2 and 4 (WC2 C20–C23) on encapsulated traces from the initial state: every state
reached from the initial state of Spec 1 §47 (one context, empty registry) by an
`EncapsulatedTrace` satisfies the re-indexed kernel invariant `KInvC`, `SyncInv` and
`GrantDiscipline`, under `DDSound` (Spec 1 §80) and well-formed statics (Spec 1 §47). Fragment:
the concurrent kernel with the reference synchronization library, without the by-value `spawn`
composite; encapsulation is the hypothesis `EncapsulatedTrace`. -/
theorem encapsulated_inv {k : K} {L : MutexLayout} {statics : Statics} {lbls : List Label}
    {st' : SC × SyncReg} (hdd : DDSound k) (hst : StaticsOK statics)
    (h : EncapsulatedTrace k L (SC.ofS3 (S3.init statics), []) lbls st') :
    KInvC st'.1 ∧ SyncInv L st'.1 st'.2 ∧ GrantDiscipline st'.1 st'.2 := by
  obtain ⟨hk, hs⟩ := init_inv (k := k) hdd hst L
  obtain ⟨hk', hs'⟩ := trace_inv hdd h hk hs
  exact ⟨hk'.1, hs'.1, hs'.2.1⟩

end Ern.Concurrency
