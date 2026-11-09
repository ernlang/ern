import Ern.Concurrency.Preservation
import Ern.Concurrency.Reparent
import Ern.Concurrency.SyncInit
import Ern.Concurrency.ArenaPreserve

/-!
# Theorems 2, 4 and 7 on labelled steps and traces (WC4 C20–C23; Spec 1 §55, §56)

Assembly of `Ern.Concurrency.Preservation`, `Ern.Concurrency.TransferPreserve`,
`Ern.Concurrency.Reparent`, `Ern.Concurrency.SyncInit` and `Ern.Concurrency.ArenaPreserve`:

* theorem 2 for every labelled step of the kernel with the synchronization and arena libraries,
  the by-value composite included (`lstep_kInvCA`);
* theorems 2, 4 and 7 together along an `EncapsulatedTrace` (WC4 C22, C23; Spec 1 §55, §56):
  `KInvCA`, `SyncState`, `AdminSep` and `ArenaInvC` (`trace_inv`, `trace_preserves`,
  `encapsulated_inv`, `encapsulated_arenaInv`).
-/

namespace Ern.Concurrency

open Ern.MemoryModel.Access

/-- Theorem 2 (WC4 C20, C23) on every labelled step (inherited operations O1–O16 executed by a
context, `spawn`, the by-value composite, `terminate`, `join`, `deriveSync` under the library
instantiation, `newMutex`, `acquire`, `unlock`, `resetLock`, `newArena`, `issue`, `reset`): the
re-indexed kernel invariant with the auxiliaries of Spec 1 (`KInvCA`) is preserved, under
`DDSound` (Spec 1 §80, for `split`). -/
theorem lstep_kInvCA {k : K} {L : MutexLayout} {lbl : Label} {st st' : SC × SyncReg × ArenaReg}
    (hdd : DDSound k) (h : LStep k L lbl st st') (hk : KInvCA st.1) : KInvCA st'.1 := by
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
  | newMutex h => obtain ⟨-, -, rfl⟩ := h; exact hk
  | acquire h =>
    obtain ⟨hc, e, -, -, hpre, rfl⟩ := h
    exact deriveSync_preservesC (r := _) hk ⟨hc, .ok hpre⟩
  | unlock h =>
    obtain ⟨hc, e, g, -, -, -, hrel, -, rfl⟩ := h
    exact opStepC_preservesC (op := .release g) hdd hk (fun e => by cases e)
      ⟨hc, _, .ok hrel, rfl⟩
  | resetLock h => obtain ⟨-, -, -, -, -, -, rfl⟩ := h; exact hk
  | newArena h => obtain ⟨-, -, rfl⟩ := newArenaStepC_ok h; exact hk
  | issue h =>
    obtain ⟨E, s₁, -, -, -, hsp, hsto, -⟩ := issueStepC_ok h
    exact opStepC_preservesC hdd (opStepC_preservesC hdd hk (fun e => by cases e) hsp)
      (fun e => by cases e) hsto
  | reset h =>
    obtain ⟨E, s₁, -, hd, hrl, -, -⟩ := resetStepC_ok (k := k) h
    exact opStepC_preservesC hdd (opStepC_preservesC hdd hk (fun e => by cases e) hd)
      (fun e => by cases e) hrl

/-- The library invariants carried along traces: `SyncState` (theorem 4, WC4 C21, C22), the
separation of the registries `AdminSep` (Spec 1 §56; WC4 C13.7, OB-C16) and `ArenaInvC`
(theorem 7, Spec 1 §55). -/
def LibInv (L : MutexLayout) (st : SC × SyncReg × ArenaReg) : Prop :=
  SyncState L st.1 st.2.1 ∧ AdminSep st.1 st.2.1 st.2.2 ∧ ArenaInvC st.1 st.2.2

/-- With an empty arena registry, `LibInv` is `SyncState` (`AdminSep` and `ArenaInvC` range over
the entries of the arena registry). -/
theorem libInv_nil {L : MutexLayout} {s : SC} {reg : SyncReg} :
    LibInv L (s, reg, []) ↔ SyncState L s reg := by
  refine ⟨fun h => h.1, fun h => ⟨h, ?_, ?_⟩⟩
  · intro e _ E hE; cases hE
  · intro E hE; cases hE

/-- Theorems 2, 4 and 7 on one labelled step taken under `Encap`: `KInvCA` and `LibInv` are
preserved, under `DDSound` (Spec 1 §80). -/
theorem lstep_inv {k : K} {L : MutexLayout} {lbl : Label} {st st' : SC × SyncReg × ArenaReg}
    (hdd : DDSound k) (h : LStep k L lbl st st') (he : Encap L (st.1, st.2.1) lbl)
    (hk : KInvCA st.1) (hl : LibInv L st) : KInvCA st'.1 ∧ LibInv L st' := by
  obtain ⟨hs, hsep, ha⟩ := hl
  have hk' := lstep_kInvCA hdd h hk
  exact ⟨hk', lstep_preserves h he hk hk'.1.1.2 (fun _ => hsep) hs,
    lstep_adminSep h hsep hs.1.regBound fun E hE => (ha E hE).1,
    lstep_arenaInv h hk.1.1.2 hk'.1.2.1.2.2 ha⟩

/-- Theorems 2, 4 and 7 (WC4 C20–C23; Spec 1 §55, §56) along an `EncapsulatedTrace`: from a state
satisfying `KInvCA` and `LibInv`, every reached state satisfies both, under `DDSound` (Spec 1
§80). -/
theorem trace_inv {k : K} {L : MutexLayout} {st st' : SC × SyncReg × ArenaReg} {lbls : List Label}
    (hdd : DDSound k) (h : EncapsulatedTrace k L st lbls st') (hk : KInvCA st.1)
    (hs : LibInv L st) : KInvCA st'.1 ∧ LibInv L st' := by
  induction h with
  | nil => exact ⟨hk, hs⟩
  | cons he hst _ ih =>
    obtain ⟨hk', hs'⟩ := lstep_inv hdd hst he hk hs
    exact ih hk' hs'

/-- Theorem 4 (WC4 C21–C23), trace form: along an `EncapsulatedTrace` from a state satisfying
`KInvCA` and `LibInv`, `SyncState` is preserved, under `DDSound` (Spec 1 §80). -/
theorem trace_preserves {k : K} {L : MutexLayout} {st st' : SC × SyncReg × ArenaReg}
    {lbls : List Label} (hdd : DDSound k) (h : EncapsulatedTrace k L st lbls st')
    (hk : KInvCA st.1) (hs : LibInv L st) : SyncState L st'.1 st'.2.1 :=
  (trace_inv hdd h hk hs).2.1

/-- The initial state of Spec 1 §47 as a single-context state, with empty registries (WC4 C3,
C12; Spec 1 §46), satisfies `KInvCA` and `LibInv`. -/
theorem init_inv {k : K} {statics : Statics} (hdd : DDSound k) (hst : StaticsOK statics)
    (L : MutexLayout) :
    KInvCA (SC.ofS3 (S3.init statics)) ∧ LibInv L (SC.ofS3 (S3.init statics), [], []) := by
  obtain ⟨-, -, -, hkc⟩ := reachable_single (k := k) hdd hst .init
  obtain ⟨-, haux, hh⟩ := init_kinv hst
  have hflat : (SC.ofS3 (S3.init statics)).flat = S3.init statics := by
    rw [single_flat ⟨_, rfl⟩, toS3_ofS3]
  refine ⟨⟨hkc, by rw [hflat]; exact haux, by rw [hflat]; exact hh⟩, ?_, ?_, ?_⟩
  · refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
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

/-- Theorems 2 and 4 (WC4 C20–C23) from the initial state: every state reached from the initial
state of Spec 1 §47 (one context, empty registries) by an `EncapsulatedTrace` satisfies the
re-indexed kernel invariant `KInvC`, `SyncInv` and `GrantDiscipline`, under `DDSound` (Spec 1 §80)
and well-formed statics (Spec 1 §47). -/
theorem encapsulated_inv {k : K} {L : MutexLayout} {statics : Statics} {lbls : List Label}
    {st' : SC × SyncReg × ArenaReg} (hdd : DDSound k) (hst : StaticsOK statics)
    (h : EncapsulatedTrace k L (SC.ofS3 (S3.init statics), [], []) lbls st') :
    KInvC st'.1 ∧ SyncInv L st'.1 st'.2.1 ∧ GrantDiscipline st'.1 st'.2.1 := by
  obtain ⟨hk, hs⟩ := init_inv (k := k) hdd hst L
  obtain ⟨hk', hs', -⟩ := trace_inv hdd h hk hs
  exact ⟨hk'.1, hs'.1, hs'.2⟩

/-- **Theorem 7**, trace form (Spec 1 §55, §56; WC4 C19, C23): every state reached from the
initial state of Spec 1 §47 (one context, empty registries) by an `EncapsulatedTrace` satisfies
`ArenaInvC` (`ArenaInv` of every live arena) and the separation of the registries `AdminSep`,
under `DDSound` (Spec 1 §80) and well-formed statics (Spec 1 §47). -/
theorem encapsulated_arenaInv {k : K} {L : MutexLayout} {statics : Statics} {lbls : List Label}
    {st' : SC × SyncReg × ArenaReg} (hdd : DDSound k) (hst : StaticsOK statics)
    (h : EncapsulatedTrace k L (SC.ofS3 (S3.init statics), [], []) lbls st') :
    ArenaInvC st'.1 st'.2.2 ∧ AdminSep st'.1 st'.2.1 st'.2.2 := by
  obtain ⟨hk, hs⟩ := init_inv (k := k) hdd hst L
  obtain ⟨-, -, hsep, ha⟩ := trace_inv hdd h hk hs
  exact ⟨ha, hsep⟩

end Ern.Concurrency
