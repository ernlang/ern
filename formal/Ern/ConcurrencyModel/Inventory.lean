import Ern.ConcurrencyModel.Encapsulation
import Ern.ConcurrencyModel.SyncContract

/-!
# Theorem 6: the inventory of the rights read under encapsulation (C22.6; `OB-C28`, abstract part)

Theorem 6 of `formal/DESIGN.md`, Milestone 4, target theorems. For each kind of step, the rights it
reads are defined once (`RightsRead`, each entry citing its precondition point, intermediate and
resulting states included), with the guard-free form that C22.6 requires (`RightsReadFree`):

* every listed right holds for an `ok` step: no fictitious premise (`rights_inventory`);
* every guard-free form implies the right it replaces (`rights_inventory`);
* `unlock` reads both rights of C17.4 (`unlock_inventory`);
* the `resetLock` exception is exactly that of C22.6 (`resetLock_inventory`);
* the three atomic cases are in the inventory (`atomic_inventory`).

The form of theorem 4 along an `EncapsulatedTrace` (C51.1) is `synchronization_encapsulated`.
-/

namespace Ern.ConcurrencyModel

open Ern.MemoryModel.Access

variable {pm : ProviderMeta}

/-- **Theorem 6** (C22.6; `OB-C28`, abstract part): every right of the inventory holds for an `ok`
labelled step, in the state where the step relation reads it, so no listed right is fictitious;
and every guard-free form of C22.6 implies the ordinary right it replaces. Fragment: every labelled
step, every state. -/
theorem rights_inventory {ks : KShared} {L : MutexLayout} :
    (∀ (lbl : Label) (st st' : SC × SyncReg × ArenaReg), LStep ks L lbl st st' →
      RightsRead ks L st lbl) ∧
      (∀ (st : SC × SyncReg × ArenaReg) (lbl : Label), RightsReadFree ks L st lbl →
        RightsRead ks L st lbl) :=
  ⟨fun _ _ _ h => rightsRead_of_step h, fun _ _ h => rightsRead_of_free h⟩

/-- **Theorem 6** for `unlock` (C17.4, C22.6: "the premise inventory includes the
controller-access right checked in the state before the operation and the retained
controller-access right in the prospective state after releasing the grant"): for an entry
recording the grant `g`, the guard-free inventory of `unlock` is the holder right of O3 for `g`
(Spec 1 §62.2), the controller-access right before the step, and the controller-access right in
the prospective state, each with a holder chain free of every live `guarded`. -/
theorem unlock_inventory {ks : KShared} {L : MutexLayout} {st : SC × SyncReg × ArenaReg}
    {c i g : Nat} {e : SyncEntry} (hi : st.2.1[i]? = some e) (hg : e.grant = some g) :
    RightsReadFree ks L st (.unlock c i) ↔
      OptP (st.1.A[g]?) (fun y => HolderRightFree (st.1, st.2.1) c y.holder) False ∧
        CtrlRightFree L (st.1, st.2.1) e c ∧
        CtrlRightFree L (prospectiveUnlock st.1 c g, st.2.1) e c := by
  simp only [RightsReadFree, hi, hg, OptP]

/-- **Theorem 6** for `resetLock` (C18.1, C18.4, C22.6, "`resetLock` exception"): the guard-free
inventory of `resetLock` is the check of C18.1 under the exception of C22.6 (`ResetExerciseFree`:
the subject `entry.guarded` is exempt, the right on its holding `slot` excludes every other live
`guarded`) and the controller-access right of C18.4, not exempt. -/
theorem resetLock_inventory {ks : KShared} {L : MutexLayout} {st : SC × SyncReg × ArenaReg}
    {c i : Nat} :
    RightsReadFree ks L st (.resetLock c i) ↔ ResetExerciseFree (st.1, st.2.1) c i ∧
      OptP (st.2.1[i]?) (fun e => CtrlRightFree L (st.1, st.2.1) e c) False :=
  Iff.rfl

/-- **Theorem 6** for the atomic cases (C37, C39, C22.6; `OB-C28`: "its extended atomic cases"):
`readShared`, the concurrent `writeShared` and the compare-and-exchange (both branches) read the
exercise of `access` in `Observe`, guard-free under C22.6. -/
theorem atomic_inventory {ks : KShared} {L : MutexLayout} {st : SC × SyncReg × ArenaReg}
    {c a l v : Nat} {order : MemOrder} {region : List Nat} {ord : Option MemOrder}
    {kind : WriteKind} {succ fail : MemOrder} {br : CasBranch} :
    (RightsReadFree ks L st (.readShared c a l order v) ↔ ExerFree st.1 st.2.1 c a .observe) ∧
      (RightsReadFree ks L st (.writeShared c a region ord kind) ↔
        ExerFree st.1 st.2.1 c a .observe) ∧
      (RightsReadFree ks L st (.cas c a l succ fail br) ↔ ExerFree st.1 st.2.1 c a .observe) :=
  ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩

/-- **Theorem 4** along an `EncapsulatedTrace` (C22, C51.1): every state reached from the initial
state of Spec 1 §47 by an `EncapsulatedTrace` (the six requirements of C22) satisfies `SyncInv`,
`GrantDiscipline` and the exclusivity of C21.5 and C22, under `DDSound` (Spec 1 §80) and
well-formed statics (Spec 1 §47). -/
theorem synchronization_encapsulated {ks : KShared} {L : MutexLayout} {statics : Statics}
    {lbls : List Label} {st' : SC × SyncReg × ArenaReg} (hdd : DDSound ks.toK)
    (hst : StaticsOK statics)
    (h : EncapsulatedTrace pm ks L (SC.ofS3 (S3.init statics), [], []) lbls st') :
    SyncInv L st'.1 st'.2.1 st'.2.2 ∧ GrantDiscipline st'.1 st'.2.1 ∧
      (∀ e ∈ st'.2.1, e.Live st'.1 → ∀ g, e.grant = some g → st'.1.flat.Active g →
        ∀ j, CoveringDesc st'.1 e.guarded j → j = g ∨ g ∈ st'.1.flat.ancs j) ∧
      (∀ e ∈ st'.2.1, e.Live st'.1 → e.grant = none → NoCoveringDesc st'.1 e.guarded) :=
  synchronization_reached hdd hst h.restricted

end Ern.ConcurrencyModel
