import Ern.Concurrency.FullEncap.HandoffExtSame

/-!
# Targeted check of the proposed C17 item 4

Brief of milestone 4, "contrôle ciblé de la correction de C17 point 4"
(`formal/reports/spec2-m4-handoff-ext.md`, section « Contrôle de C17 point 4 »). The candidate
text, proposed C17 item 4, not adopted (brief), requires the controller-access right of WC5.3 C17
item 4 (Spec 1 §68.2) both before `unlock` and in the prospective authority state obtained by
releasing the recorded grant under O3 (Spec 1 §62). WC5.3 is unchanged; nothing here modifies an
existing definition (`UnlockOk`, `PremG`, `RunFull`, the definitions of `HandoffExt`).

* `prospUnlock`: the prospective state, the kernel component `UnlockOk` writes (`releaseEff` on
  the view of the acting context), the registry unchanged.
* `KeptRight`: in the prospective state, the controller-access right read as `PremG` reads it
  before the step (`CtrlRight5`, without a live `guarded` in the chain).
* `RunC17`: a `RunFull` every `unlock` step of which satisfies `KeptRight`.
-/

set_option autoImplicit false

namespace Ern.Concurrency.FullEncap.C17Check

open Ern.MemoryModel Ern.MemoryModel.Access Ern.Concurrency Ern.Concurrency.MutexReal
open Ern.Concurrency.FullEncap Ern.Concurrency.FullEncap.HandoffExt
open Ern.Concurrency.FullEncap.HandoffExtSame Ern.Concurrency.Corpus
open Ern.Concurrency.Traces (L0)

/-! ## Definitions -/

/-- The prospective authority state of an `unlock` executed by `c` on an entry recording the grant
`g` (proposed C17 item 4, not adopted (brief)): from the state before the step, `g` released
according to O3 (Spec 1 §62, `ok` effect: `releaseEff` on the view of `c`, written back as
`UnlockOk` writes it), the synchronization registry unchanged (it still records `grant = some g`),
hence the controller's logical state unchanged. It is a precondition state only (brief: neither
committed nor observable). -/
def prospUnlock (st : SC × SyncReg) (c g : Nat) : SC × SyncReg :=
  (st.1.set (releaseEff (st.1.view c) g), st.2)

/-- The kept right of `unlock` of entry `n` by `c` (brief, "Droit conservé"; proposed C17 item 4,
not adopted (brief)): in the prospective state, the acting frame has the controller-access right
of WC5.3 C17 item 4 (Spec 1 §68.2, C14 item 3), read in the form the complete encapsulation reads
it before the step (`PremG`: `CtrlRight5`, no live `guarded` in the holder chain). When entry `n`
does not exist or records no grant, C17 item 1 fails and the prospective state has no meaning
(brief, "Précision de lecture"); the predicate is then false. -/
def KeptRight (L : MutexLayout) (st : SC × SyncReg) (c n : Nat) : Prop :=
  OptP (st.2[n]?) (fun e => OptP e.grant (fun g => CtrlRight5 L (prospUnlock st c g) e c) False)
    False

/-- Decidability of `KeptRight`. -/
instance (L : MutexLayout) (st : SC × SyncReg) (c n : Nat) : Decidable (KeptRight L st c n) := by
  unfold KeptRight; infer_instance

/-- The kept right of a step (brief): `KeptRight` on the state before an `unlock`; no condition on
the other kinds. -/
def UnlockKept (L : MutexLayout) (st : SC × SyncReg × ArenaReg) : Label → Prop
  | .unlock c n => KeptRight L (st.1, st.2.1) c n
  | _ => True

/-- Decidability of `UnlockKept`. -/
instance (L : MutexLayout) (st : SC × SyncReg × ArenaReg) (lbl : Label) :
    Decidable (UnlockKept L st lbl) := by
  unfold UnlockKept; split <;> infer_instance

/-- Every step of the trace satisfies `UnlockKept`. -/
def KeptAll (L : MutexLayout) (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) : Prop :=
  ∀ i (h : i < lbls.length), UnlockKept L (σ i) lbls[i]

/-- Decidability of `KeptAll`. -/
instance (L : MutexLayout) (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) :
    Decidable (KeptAll L σ lbls) := by
  unfold KeptAll; infer_instance

/-- Corrected execution (brief, "Exécution corrigée"; proposed C17 item 4, not adopted (brief)): a
`RunFull` every `unlock` step of which satisfies the kept right. -/
def RunC17 (k : K) (L : MutexLayout) (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) :
    Prop :=
  RunFull k L σ lbls ∧ KeptAll L σ lbls

/-- Brief, "Exécution corrigée": a corrected execution is a `RunFull` (inclusion). -/
theorem runC17_runFull {k : K} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg}
    {lbls : List Label} (h : RunC17 k L σ lbls) : RunFull k L σ lbls :=
  h.1

/-! ## The controller is unchanged in the prospective state -/

/-- The release of the prospective state keeps the holders of the authorities (Spec 1 §62 `ok`
effect: only the activity of `g` and the anchors of its holding place change). -/
theorem prospUnlock_holder (st : SC × SyncReg) (c g a : Nat) :
    ((prospUnlock st c g).1.A[a]?).map (·.holder) = (st.1.A[a]?).map (·.holder) := by
  show ((releaseEff (st.1.view c) g).A[a]?).map (·.holder) = _
  unfold releaseEff
  split
  · rename_i x hx
    show ((st.1.A.set g { x with active := false })[a]?).map (·.holder) = _
    by_cases e : g = a
    · subst e
      have hx' : st.1.A[g]? = some x := hx
      rw [hx']
      simp [lt_of_getElem? hx']
    · simp [e]
  · rfl

/-- The controller of an entry is the same in the prospective state (WC5.3 C12 `ControlOf`,
positional: it reads the holder of `guarded` and the places, which the release keeps; brief,
"le contrôleur restant inchangé"). -/
theorem controlOf_prospUnlock (L : MutexLayout) (st : SC × SyncReg) (c g : Nat) (e : SyncEntry) :
    ControlOf L (prospUnlock st c g).1 e = ControlOf L st.1 e := by
  have hP : (prospUnlock st c g).1.P = st.1.P := by
    show (releaseEff (st.1.view c) g).P = _
    unfold releaseEff; split <;> rfl
  unfold ControlOf
  rw [prospUnlock_holder, hP]

/-! ## Task 1: the two traces of slice 4 -/

/-- Brief (C17 check), task 1, trace `unlock_r_eq_i_no_hb`: the prefix up to index 6 is a corrected
execution (it has no `unlock`); the `unlock` of `c1` at index 7, `ok` under WC5.3 C17 as adopted
and admitted by `PremG`, does not satisfy the kept right (proposed C17 item 4, not adopted
(brief)). The state fact: in the prospective state, grant 5 is inactive, `o1′` (authority 4) is
active and held by the protected leaf `T` (place 3), and `c1` has no `cap5` on `lock` (place 2),
the only chain from `c1` to `T` having passed through grant 5 (WC5.3 C43). -/
theorem ul_kept : RunC17 KM L0 ulσ (ulLbls.take 7) ∧ ulLbls[7] = .unlock 1 0 ∧
    ulσ 7 = (ul6, [⟨3, some 5⟩], []) ∧
    UnlockOk L0 ul6 [⟨3, some 5⟩] 1 0 (ul7, regX) ∧ PremG KM L0 (ulσ 7) (.unlock 1 0) ∧
    ¬ UnlockKept L0 (ulσ 7) ulLbls[7] ∧
    (prospUnlock (ul6, [⟨3, some 5⟩]) 1 5).1.A[5]?.map (·.active) = some false ∧
    (prospUnlock (ul6, [⟨3, some 5⟩]) 1 5).1.A[4]?.map (fun y => (y.active, y.holder)) =
      some (true, .place 3) ∧
    cap5 (prospUnlock (ul6, [⟨3, some 5⟩]) 1 5).1 [⟨3, some 5⟩] 1 2 = none := by
  have hr := unlock_r_eq_i_no_hb.1
  exact ⟨⟨Replay.RunFull.take hr 7, by decide⟩, rfl, rfl, ul_steps.2.2.2.2.1,
    (hr 7 (by decide)).1.2, by decide, by decide, by decide, by decide⟩

/-- Brief (C17 check), task 1, the twin without `resetLock` (`unlock_r_eq_i_twin`): the same
facts; the twin coincides with the trace up to index 7. -/
theorem ulj_kept : RunC17 KM L0 uljσ (uljLbls.take 7) ∧ uljLbls[7] = .unlock 1 0 ∧
    uljσ 7 = (ul6, [⟨3, some 5⟩], []) ∧
    UnlockOk L0 ul6 [⟨3, some 5⟩] 1 0 (ul7, regX) ∧ PremG KM L0 (uljσ 7) (.unlock 1 0) ∧
    ¬ UnlockKept L0 (uljσ 7) uljLbls[7] ∧
    (prospUnlock (ul6, [⟨3, some 5⟩]) 1 5).1.A[5]?.map (·.active) = some false ∧
    (prospUnlock (ul6, [⟨3, some 5⟩]) 1 5).1.A[4]?.map (fun y => (y.active, y.holder)) =
      some (true, .place 3) ∧
    cap5 (prospUnlock (ul6, [⟨3, some 5⟩]) 1 5).1 [⟨3, some 5⟩] 1 2 = none := by
  have hr := unlock_r_eq_i_twin.1
  exact ⟨⟨Replay.RunFull.take hr 7, by decide⟩, rfl, rfl, ul_steps.2.2.2.2.1,
    (hr 7 (by decide)).1.2, by decide, by decide, by decide, by decide⟩

end Ern.Concurrency.FullEncap.C17Check
