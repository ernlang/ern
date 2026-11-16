import Ern.ConcurrencyModel.Reachable

/-!
# Theorem 5: synchronized administration and the guard on administration identities (C13, C19;
`OB-C16`)

Theorem 5 of `formal/DESIGN.md`, Milestone 4, target theorems:

* `newMutex` establishes `SyncInv` and `GrantDiscipline` for the new entry and the entries already
  registered (`newMutex_establishes`, C13 preservation obligation);
* the guard of C13.7 (Spec 1 §56) on reached states: no `guarded` identity is registered as a live
  administration identity by two administrations, among synchronization entries or between a
  synchronization entry and an arena (`admin_guard_reached`);
* C19: an administration operation keeps the inherited administration right of Spec 1
  (`MetaRight`, §36, §77.1, §78.1) unweakened (`issue_metaRight`, `reset_metaRight`), and the
  authority on which that right rests, a grant in particular, covers every leaf of the
  administrative value (`metaRight_covers`).
-/

namespace Ern.ConcurrencyModel

open Ern.MemoryModel Ern.MemoryModel.Access

/-! ## `newMutex` (C13) -/

/-- **Theorem 5** (C13, "The construction must establish the entire `SyncInv` and
`GrantDiscipline` suite for the new and previously live entries"): from a state satisfying the
kernel invariant and the library invariant, an `ok` `newMutex(g)` yields a state where `SyncInv`
and `GrantDiscipline` hold, with the new entry `⟨g, none⟩` registered and live. Under `DDSound`
(Spec 1 §80). Fragment: every state satisfying `KInvCA` and `LibInv`. -/
theorem newMutex_establishes {ks : KShared} {L : MutexLayout} {st st' : SC × SyncReg × ArenaReg}
    {c g : Nat} (hdd : DDSound ks.toK) (hk : KInvCA st.1) (hl : LibInv L st)
    (h : LStep ks L (.newMutex c g) st st') :
    SyncInv L st'.1 st'.2.1 st'.2.2 ∧ GrantDiscipline st'.1 st'.2.1 ∧
      (⟨g, none⟩ : SyncEntry) ∈ st'.2.1 ∧ (⟨g, none⟩ : SyncEntry).Live st'.1 := by
  obtain ⟨-, ⟨hs, hgd⟩, -⟩ := lstep_inv hdd h trivial hk hl
  refine ⟨hs, hgd, ?_⟩
  cases h with
  | newMutex h =>
    obtain ⟨-, hpre, rfl⟩ := h
    refine ⟨List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
    have hg := hpre.guarded
    unfold OptP at hg; split at hg
    · rename_i y hy; exact ⟨y, hy, hg.1⟩
    · exact hg.elim

/-! ## The guard on administration identities (C13.7, Spec 1 §56; `OB-C16`) -/

/-- **Theorem 5** (C13.7, C21.4, Spec 1 §56; `OB-C16`): every state reached from the initial state
of Spec 1 §47 by a trace satisfying the restrictions of C23 has no `guarded` identity registered as
a live administration identity twice: two live synchronization entries with the same `guarded`
are the same entry, and no live entry's `guarded` is the `internal` of a live arena. Under
`DDSound` (Spec 1 §80) and well-formed statics (Spec 1 §47). -/
theorem admin_guard_reached {ks : KShared} {L : MutexLayout} {statics : Statics}
    {lbls : List Label} {st' : SC × SyncReg × ArenaReg} (hdd : DDSound ks.toK)
    (hst : StaticsOK statics)
    (h : RestrictedTrace ks L (SC.ofS3 (S3.init statics), [], []) lbls st') :
    (∀ (i j : Nat) (e e' : SyncEntry), st'.2.1[i]? = some e → st'.2.1[j]? = some e' →
      e.Live st'.1 → e'.Live st'.1 → e.guarded = e'.guarded → i = j) ∧
      AdminSep st'.1 st'.2.1 st'.2.2 := by
  obtain ⟨-, hsi, -, -⟩ := restricted_inv hdd hst h
  exact ⟨hsi.unique, hsi.adminGuard⟩

/-! ## Synchronized administration (C19) -/

/-- C19 ("the grant must therefore cover the entire required administrative footprint"): an
authority whose effective mode permits `m` on every leaf of a place covers every leaf of that
place (Spec 1 §43, case 1: an authority that does not cover a leaf has no effective mode there).
For the administration right `MetaRight` (Spec 1 §36), the authority on which it rests, a grant
in particular, covers every leaf of the administrative value. -/
theorem metaRight_covers {t : S3} {a p : Nat} {m : Mode}
    (h : ∀ l ∈ footprint t.P p, Allows (effective t a l) m) :
    ∀ l ∈ footprint t.P p, ∃ x, t.A[a]? = some x ∧ x.active = true ∧ l ∈ x.footprint := by
  intro l hl
  have hal := h l hl
  cases he : effective t a l with
  | none => rw [he] at hal; exact hal.elim
  | some m' =>
    obtain ⟨x, hx, ha, hlx, -⟩ := effective_some he
    exact ⟨x, hx, ha, hlx⟩

/-- **Theorem 5** (C19, Spec 1 §36, §77.1): an `ok` `issue` executed by `c` satisfies the inherited
administration right `MetaRight` of Spec 1, unweakened, on the view of `c` (C2), and the authority
on which it rests covers every leaf of the arena value. -/
theorem issue_metaRight {k : K} {s : SC} {ar : ArenaReg} {c i : Nat} {region : List Nat}
    {dst : Nat} {st' : SC × ArenaReg} (h : IssueStepC k s ar c i region dst (.ok st')) :
    ∃ E, ar[i]? = some E ∧ Arena.MetaRight (s.view c) E := by
  obtain ⟨E, -, hE, hst, -⟩ := issueStepC_ok h
  exact ⟨E, hE, hst.metaRight⟩

/-- An exercisable authority exists (Spec 1 §43). -/
theorem exercisable_lt {t : S3} {b : Nat} {m : Mode} (h : t.ExercisableAt b m) : b < t.A.length := by
  cases h with
  | base hy => exact lt_of_getElem? hy
  | held hy => exact lt_of_getElem? hy

/-- Spec 1 §43, third clause: an authority held by a place `p` and exercisable in `Modify` gives
the current frame exercisable `Modify` over `p` (`HasRight`). -/
theorem hasRight_of_held_exercisable {t : S3} {a p : Nat} {y : Authority} (hy : t.A[a]? = some y)
    (hh : y.holder = .place p) (hex : t.ExercisableAt a .modify) : HasRight t .modify p := by
  cases hex with
  | base hy' _ _ hh' =>
    rw [hy] at hy'; cases hy'; rw [hh] at hh'; cases hh'
  | held hy' _ _ hh' hb hall =>
    rw [hy] at hy'; cases hy'; rw [hh] at hh'; cases hh'
    exact ⟨_, List.mem_range.2 (exercisable_lt hb), hb, hall⟩

/-- **Theorem 5** (C19, Spec 1 §36, §78.1): an `ok` `reset` executed by `c`, from a state whose
arena registry satisfies the library invariant (Spec 1 §55, `ArenaInvC`), satisfies the inherited
administration right `MetaRight` of Spec 1 on the view of `c`: the derivation of `internal` at
`Modify` (Spec 1 Part XIV) is exercisable, and `internal` is held by the arena value (§55), so the
current frame has exercisable `Modify` over that value (§43). -/
theorem reset_metaRight {k : K} {s : SC} {ar : ArenaReg} {c i : Nat} {st' : SC × ArenaReg}
    (ha : ArenaInvC s ar) (h : ResetStepC s ar c i (.ok st')) :
    ∃ E, ar[i]? = some E ∧ Arena.MetaRight (s.view c) E := by
  obtain ⟨E, s₁, hE, hd, -, -, -⟩ := resetStepC_ok (k := k) h
  refine ⟨E, hE, ?_⟩
  obtain ⟨-, o₃, hR, ho⟩ := hd
  cases o₃ with
  | reject => cases ho
  | fail => cases ho
  | ok t =>
    have hR' : DeriveStep E.internal (footprint s.P E.storage) .modify (s.view c) (.ok t) := hR
    obtain ⟨hpre, -⟩ := Guarded.ok_iff.1 hR'
    obtain ⟨-, hinv⟩ := ha E (List.mem_of_getElem? hE)
    obtain ⟨hai, -⟩ := hinv hpre.active
    have hshape := hai.shape
    unfold OptP at hshape
    split at hshape
    · rename_i y hy
      cases hh : y.holder with
      | frame f => rw [hh] at hshape; cases hshape.2
      | place p =>
        have hy' : (s.view c).A[E.internal]? = some y := hy
        have hv : Arena.arenaValue (s.view c) E = some p := by
          simp [Arena.arenaValue, hy', hh]
        unfold Arena.MetaRight
        rw [hv]
        exact hasRight_of_held_exercisable hy' hh hpre.exercisable
    · exact hshape.elim

end Ern.ConcurrencyModel
