import Ern.ConcurrencyModel.Preservation
import Ern.ConcurrencyModel.Ancestry
import Ern.ConcurrencyModel.SyncInit
import Ern.ConcurrencyModel.ArenaPreserve

/-!
# Theorem 2 on labelled steps and traces (C20–C23; Spec 1 §55, §56)

Theorem 2 of `formal/DESIGN.md` (Milestone 4), assembled from `Preservation`,
`SpawnValuePreserve`, `Ancestry`, `SyncInit` and `ArenaPreserve`:

* the kernel invariant for every labelled step, the by-value composite and the atomic cases
  included (`lstep_kInvCA`);
* `KInvCA`, `SyncState` (`SyncInv` and `GrantDiscipline`) and the arena invariant `ArenaInvC`
  together, on every labelled step admitted by `RestrictedStep` (C22.1–C22.3, C22.5) and along a
  `RestrictedTrace` (C23).

`I5` (Spec 1 §57), which C20 also requires every transition to preserve, is proved for every
labelled step and on every reached state in the module `RefinementPinnedLive` (`lstep_i5`,
`lrun_i5`, `reached_i5`), on the global state.
-/

namespace Ern.ConcurrencyModel

open Ern.MemoryModel.Access

/-- Theorem 2 (C20, C23) on every labelled step (inherited operations O1–O16 executed by a
context, `spawn`, the by-value composite, `terminate`, `join`, `deriveSync` under the library
instantiation, `newMutex`, `acquire`, `unlock`, `resetLock`, `newArena`, `issue`, `reset`, and the
atomic cases `readShared`, concurrent `writeShared`, compare-and-exchange): the re-indexed kernel
invariant with the auxiliaries of Spec 1 (`KInvCA`) is preserved, under `DDSound` (Spec 1 §80,
for `split`). -/
theorem lstep_kInvCA {ks : KShared} {L : MutexLayout} {lbl : Label}
    {st st' : SC × SyncReg × ArenaReg}
    (hdd : DDSound ks.toK) (h : LStep ks L lbl st st') (hk : KInvCA st.1) : KInvCA st'.1 := by
  cases h with
  | @kernel s s' reg ar c op h =>
    cases op
    case exit => exact exitFrameC_preserves hk.1 hk.2.1 hk.2.2 h
    all_goals exact opStepC_preservesC hdd hk (fun e => by cases e) h
  | spawn h => exact spawn_preservesC hk h
  | spawnVal h => exact spawnVal_preservesC hk h
  | terminate h => exact terminate_preserves hk.1 hk.2.1 hk.2.2 h
  | join h => exact join_preservesC hk h
  | deriveSync h => exact deriveSync_preservesC hk h
  | newMutex h => obtain ⟨-, rfl⟩ := h; exact hk
  | acquire h =>
    obtain ⟨e, -, -, hpre, rfl⟩ := h
    exact deriveSync_preservesC (r := _) hk (.ok hpre)
  | unlock h =>
    obtain ⟨e, g, -, -, -, hrel, -, -, rfl⟩ := h
    exact opStepC_preservesC (op := .release g) hdd hk (fun e => by cases e)
      ⟨_, .ok hrel, rfl⟩
  | resetLock h => obtain ⟨-, -, -, -, -, -, rfl⟩ := h; exact hk
  | newArena h => obtain ⟨-, -, rfl⟩ := newArenaStepC_ok h; exact hk
  | issue h =>
    obtain ⟨E, s₁, -, -, -, hsp, hsto, -⟩ := issueStepC_ok h
    exact opStepC_preservesC hdd (opStepC_preservesC hdd hk (fun e => by cases e) hsp)
      (fun e => by cases e) hsto
  | reset h =>
    obtain ⟨E, s₁, -, hd, hrl, -, -⟩ := resetStepC_ok (k := ks.toK) h
    exact opStepC_preservesC hdd (opStepC_preservesC hdd hk (fun e => by cases e) hd)
      (fun e => by cases e) hrl
  | readShared h => exact hk
  | writeShared h =>
    exact opStepC_preservesC hdd hk (fun e => by cases e) (writeSharedC_ok_kernel h)
  | cas h =>
    rcases cas_ok_cases h with hk' | rfl
    · exact opStepC_preservesC hdd hk (fun e => by cases e) hk'
    · exact hk

/-- The library invariants carried along traces: `SyncState` (`SyncInv`, C21, with its guard
across registries, and `GrantDiscipline`, C22) and the arena invariant `ArenaInvC` (Spec 1 §55;
C19). -/
def LibInv (L : MutexLayout) (st : SC × SyncReg × ArenaReg) : Prop :=
  SyncState L st.1 st.2.1 st.2.2 ∧ ArenaInvC st.1 st.2.2

/-- Theorem 2 on one labelled step taken under `RestrictedStep` (C22.1–C22.3, C22.5; C23):
`KInvCA` and `LibInv` are preserved, under `DDSound` (Spec 1 §80). -/
theorem lstep_inv {ks : KShared} {L : MutexLayout} {lbl : Label}
    {st st' : SC × SyncReg × ArenaReg}
    (hdd : DDSound ks.toK) (h : LStep ks L lbl st st') (he : RestrictedStep L st lbl)
    (hk : KInvCA st.1) (hl : LibInv L st) : KInvCA st'.1 ∧ LibInv L st' := by
  obtain ⟨hs, ha⟩ := hl
  obtain ⟨hp, hsep⟩ := syncState_part.1 hs
  have hk' := lstep_kInvCA hdd h hk
  exact ⟨hk', syncState_part.2 ⟨lstep_preserves h he hk hk'.1.1.2 hp,
    lstep_adminSep h hsep (fun e he => (hp.1.1 e he).bound) fun E hE => (ha E hE).1⟩,
    lstep_arenaInv h hk.1.1.2 hk'.1.2.1.2.2 ha⟩

/-- Theorem 2 (C20–C23; Spec 1 §55, §56) along a `RestrictedTrace`: from a state satisfying
`KInvCA` and `LibInv`, every reached state satisfies both, under `DDSound` (Spec 1 §80). -/
theorem trace_inv {ks : KShared} {L : MutexLayout} {st st' : SC × SyncReg × ArenaReg}
    {lbls : List Label}
    (hdd : DDSound ks.toK) (h : RestrictedTrace ks L st lbls st') (hk : KInvCA st.1)
    (hs : LibInv L st) : KInvCA st'.1 ∧ LibInv L st' := by
  induction h with
  | nil => exact ⟨hk, hs⟩
  | cons he hst _ ih =>
    obtain ⟨hk', hs'⟩ := lstep_inv hdd hst he hk hs
    exact ih hk' hs'

/-- The initial state of Spec 1 §47 as a single-context state, with empty registries (C3,
C12; Spec 1 §46, §47), satisfies `KInvCA` and `LibInv`. -/
theorem init_inv {k : K} {statics : Statics} (hdd : DDSound k) (hst : StaticsOK statics)
    (L : MutexLayout) :
    KInvCA (SC.ofS3 (S3.init statics)) ∧ LibInv L (SC.ofS3 (S3.init statics), [], []) := by
  obtain ⟨-, -, -, hkc⟩ := reachable_single (k := k) hdd hst .init
  obtain ⟨-, haux, hh⟩ := init_kinv hst
  have hflat : (SC.ofS3 (S3.init statics)).flat = S3.init statics := by
    rw [single_flat (SC.Single.sole ⟨_, rfl⟩), toS3_ofS3]
  refine ⟨⟨hkc, by rw [hflat]; exact haux, by rw [hflat]; exact hh⟩, ?_, ?_⟩
  · refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
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
    · intro e he; cases he
  · intro E hE; cases hE

/-- **Theorem 2** (C20–C23; Spec 1 §55, §57; `OB-C14`) from the initial state: every state
reached from the initial state of Spec 1 §47 (one context, empty registries) by a
`RestrictedTrace` (C22.1–C22.3, C22.5, and no other restriction) satisfies the re-indexed kernel
invariant `KInvC`, `SyncInv` (C21.1–C21.7) and `GrantDiscipline` (C22), and the arena invariant,
under `DDSound` (Spec 1 §80) and well-formed statics (Spec 1 §47). -/
theorem restricted_inv {ks : KShared} {L : MutexLayout} {statics : Statics} {lbls : List Label}
    {st' : SC × SyncReg × ArenaReg} (hdd : DDSound ks.toK) (hst : StaticsOK statics)
    (h : RestrictedTrace ks L (SC.ofS3 (S3.init statics), [], []) lbls st') :
    KInvC st'.1 ∧ SyncInv L st'.1 st'.2.1 st'.2.2 ∧ GrantDiscipline st'.1 st'.2.1 ∧
      ArenaInvC st'.1 st'.2.2 := by
  obtain ⟨hk, hs⟩ := init_inv hdd hst L
  obtain ⟨hk', hs', ha⟩ := trace_inv hdd h hk hs
  exact ⟨hk'.1, hs'.1, hs'.2, ha⟩

/-- `ArenaReg.unique` (Spec 1 §56, first sentence) along a `RestrictedTrace`, as a trace
invariant separate from `LibInv`: from a state satisfying `KInvCA`, `LibInv` and
`ArenaReg.unique`, every reached state satisfies `ArenaReg.unique`, under `DDSound` (Spec 1
§80). -/
theorem trace_arenaUnique {ks : KShared} {L : MutexLayout} {st st' : SC × SyncReg × ArenaReg}
    {lbls : List Label} (hdd : DDSound ks.toK) (h : RestrictedTrace ks L st lbls st')
    (hk : KInvCA st.1) (hl : LibInv L st) (hu : ArenaReg.unique st.2.2 st.1) :
    ArenaReg.unique st'.2.2 st'.1 := by
  induction h with
  | nil => exact hu
  | cons he hst _ ih =>
    obtain ⟨hk', hl'⟩ := lstep_inv hdd hst he hk hl
    exact ih hk' hl' (lstep_arenaUnique hst hu fun E hE => (hl.2 E hE).1)

end Ern.ConcurrencyModel
