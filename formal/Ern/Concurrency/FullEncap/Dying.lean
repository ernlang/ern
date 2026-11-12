import Ern.Concurrency.FullEncap.Closure
import Ern.Concurrency.FullEncap.CapacityWitness

/-!
# Leaves that die

Brief of milestone 4, slice 3, complement, task 3 (`corpus-spec2-m3.md` v14 §2 terdecies,
"Feuilles qui meurent"). A leaf dies in a step when its place is usable before the step and is not
after it (`Dying`, the definition of slice 3, which also asks the leaf to be a leaf before the
step).

* A leaf of `footprint(e.guarded)` does not die in a step that leaves `e` live
  (`protected_not_dying_run`): the `guarded` of `e` is active after the step and covers it, and
  `NoDangling` (Spec 1 §54) holds after the step; WC5.2 C12 (the entry is live exactly while
  `guarded` is active).
* The step shape `shape_step` (`Skel` and `PSkel` of `SyncPreserve`) is established for every
  kind; it keeps leaves leaves (`PSkel.isLeaf`).
-/

set_option autoImplicit false

namespace Ern.Concurrency.FullEncap

open Ern.MemoryModel Ern.MemoryModel.Access Ern.Concurrency Ern.Concurrency.MutexReal
open SyncPreserveAux SyncInitAux TransferPreserveAux

/-! ## Shape of a step -/

/-- `PSkel` composes. -/
theorem PSkel.comp {P P₁ P₂ : List Place} (h1 : PSkel P P₁) (h2 : PSkel P₁ P₂) : PSkel P P₂ := by
  refine ⟨Nat.le_trans h1.1 h2.1, fun q hq => ?_, fun r q hp hq => ?_⟩
  · rw [h2.2.1 q (Nat.lt_of_lt_of_le hq h1.1), h1.2.1 q hq]
  · have hr₁ := h2.2.2 r q hp (Nat.lt_of_lt_of_le hq h1.1)
    exact h1.2.2 r q (by rw [← h2.2.1 r hr₁]; exact hp) hq

/-- A transfer keeps the structural parents (Spec 1 §63 effect). -/
theorem pskel_transferC (s : SC) (c src dst : Nat) : PSkel s.P (transferEffC s c src dst).P := by
  have hP : (transferEffC s c src dst).P = (transferEff (s.view c) src dst).P := rfl
  refine ⟨by rw [hP, transfer_len]; exact Nat.le_refl _, fun q _ => ?_, fun r q hp _ => ?_⟩
  · rw [hP, transfer_parentOf]; rfl
  · rw [hP, transfer_parentOf] at hp
    have := (pskel_refl s.P).2.2 r q hp
    exact this ‹_›

/-- The transfer phases keep the structural parents (WC5.2 C5 phase 2). -/
theorem pskel_transfers (c : Nat) : ∀ (t : SC) (vs : List (Nat × Nat)),
    PSkel t.P (transfersEff c t vs).P
  | t, [] => pskel_refl t.P
  | t, v :: vs => PSkel.comp (pskel_transferC t c v.1 v.2) (pskel_transfers c _ vs)

/-- The shape of every `ok` step admitted by `Encap` (WC5.2 C22 items 1–3, 5), from a state
satisfying `KInvCA` and `AdminSep`: `Skel` on authorities and `PSkel` on places. -/
theorem shape_step {k : K} {L : MutexLayout} {st st' : SC × SyncReg × ArenaReg} {lbl : Label}
    (hk : KInvCA st.1) (hsep : AdminSep st.1 st.2.1 st.2.2) (he : Encap L (st.1, st.2.1) lbl)
    (hs : LStep k L lbl st st') : Skel st.1 st'.1 ∧ PSkel st.1.P st'.1.P := by
  have hw : WF3 st.1.flat := hk.1.1.2
  cases hs with
  | @kernel s s' reg ar c op h =>
    cases op
    case transfer src dst =>
      obtain ⟨-, h'⟩ := h; obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h'
      exact ⟨(transfer_skel s c src dst).1, pskel_transferC s c src dst⟩
    all_goals
      have hf := opStep_facts (reg := reg) h he (fun _ _ h => by cases h) hw
      exact ⟨hf.skel, hf.pskel⟩
  | @spawn s s' reg ar c ps ls h =>
    obtain ⟨-, h'⟩ := h; obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h'
    have hf := spawnEff_facts (reg := reg) hpre.params hpre.localsOK
    exact ⟨hf.skel, hf.pskel⟩
  | @terminate s s' reg ar c h =>
    have hf := term_facts (reg := reg) hw h
    exact ⟨hf.skel, hf.pskel⟩
  | @join s s' reg ar c d h =>
    have hf := join_facts (reg := reg) h
    exact ⟨hf.skel, hf.pskel⟩
  | deriveSync h => exact (deriveSync_excluded h he).elim
  | newMutex h =>
    obtain ⟨-, -, rfl⟩ := h
    exact ⟨skel_refl _, pskel_refl _⟩
  | @acquire s reg ar c i st₁ h =>
    obtain ⟨-, e₀, -, -, hpre, rfl⟩ := h
    have hA : (deriveSyncEff s c e₀.guarded).A = s.A ++ [⟨.modify, some e₀.guarded,
        (s.view c).afp e₀.guarded, .frame (s.view c).top, true⟩] := rfl
    obtain ⟨hsk, -⟩ := skel_append hA rfl (fun j y' hy' => ⟨y', hy', Same.refl _⟩) fun z hz => by
      rw [List.mem_singleton] at hz; subst hz
      exact .inr ⟨e₀.guarded, rfl, active_lt hpre.active, hpre.active, fun l hl => hl⟩
    exact ⟨hsk, pskel_refl _⟩
  | @unlock s reg ar c i st₁ h =>
    obtain ⟨-, e₀, g₀, -, -, -, hpre, -, rfl⟩ := h
    obtain ⟨x, hx, -⟩ := hpre.active
    have hx' : (s.view c).A[g₀]? = some x := hx
    refine ⟨release_skel' (c := c) (show s.A[g₀]? = some x from hx), ?_⟩
    show PSkel s.P (releaseEff (s.view c) g₀).P
    rw [releaseEff_eq hx']; exact pskel_refl _
  | resetLock h =>
    obtain ⟨-, -, -, -, -, -, rfl⟩ := h
    exact ⟨skel_refl _, pskel_refl _⟩
  | @spawnVal s s' reg ar c ps ls vs h =>
    obtain ⟨-, h'⟩ := h; obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h'
    have hf := spawnEff_facts (reg := reg) (c := c) (ps := []) (s := s) (fun _ h => by cases h)
      hpre.localsOK
    obtain ⟨h1, l1, o1⟩ := transfers_skel c (spawnCreate s c ls) vs
    have hp : ∀ a ∈ ps, ∀ y, (transfersEff c (spawnCreate s c ls) vs).A[a]? = some y →
        ∃ g, y.holder = .frame g := by
      intro a ha y hy
      have := hpre.paramsAtYield a ha
      have hy' : ((transfersEff c (spawnCreate s c ls) vs).view c).A[a]? = some y := hy
      rw [hy'] at this
      exact ⟨_, this.2.1⟩
    obtain ⟨h2, l2, o2⟩ := yield_skel' (f := s.nF) hp
    exact ⟨Skel.comp (Skel.comp hf.skel h1 l1 o1) h2 l2 o2,
      PSkel.comp (PSkel.comp hf.pskel (pskel_transfers c _ vs)) (pskel_refl _)⟩
  | newArena h =>
    obtain ⟨-, -, rfl⟩ := newArenaStepC_ok h
    exact ⟨skel_refl _, pskel_refl _⟩
  | @issue s reg ar c i region dst st₁ h =>
    obtain ⟨E, s₁, hE, -, -, hsp, hsto, -⟩ := issueStepC_ok h
    have hsep' : Encap L (s, reg) (.kernel c (.split E.internal [region])) :=
      fun e hm hl heq => hsep e hm E (List.mem_of_getElem? hE) hl
        (by show s.flat.Active E.internal; rw [heq]; exact hl) heq.symm
    have hf := opStep_facts (reg := reg) hsp hsep' (fun _ _ h => by cases h) hw
    obtain ⟨-, h'⟩ := hsto; obtain ⟨hpre, he₂⟩ := Guarded.ok_iff.1 h'
    rw [he₂]
    obtain ⟨l2, o2⟩ := store_org s₁ c s.A.length dst
    refine ⟨Skel.comp hf.skel (store_skel' hpre.derivedHeld) l2 o2, PSkel.comp hf.pskel ?_⟩
    show PSkel s₁.P (storeEff (s₁.view c) s.A.length dst).P
    unfold storeEff; split <;> exact pskel_refl _
  | @reset s reg ar c i st₁ h =>
    obtain ⟨E, s₁, hE, hd, hrl, -, -⟩ := resetStepC_ok (k := k) h
    have hl₀ : s.flat.Active E.internal := by
      obtain ⟨-, o, hR, ho⟩ := hd
      cases hR with
      | ok hp => exact hp.active
      | reject => cases ho
    have hsep' :
        Encap L (s, reg) (.kernel c (.derive E.internal (footprint s.P E.storage) .modify)) :=
      fun e hm hl heq => hsep e hm E (List.mem_of_getElem? hE) hl
        (by show s.flat.Active E.internal; exact hl₀) heq.symm
    have hf := opStep_facts (reg := reg) hd hsep' (fun _ _ h => by cases h) hw
    obtain ⟨-, o, hR, ho⟩ := hrl
    cases hR with
    | ok hp =>
      have he₂ : st₁.1 = s₁.set (releaseEff (s₁.view c) s.A.length) := Outcome3.ok.inj ho
      rw [he₂]
      obtain ⟨x, hx, -⟩ := hp.active
      have hx' : (s₁.view c).A[s.A.length]? = some x := hx
      obtain ⟨l2, o2⟩ := release_org s₁ c s.A.length
      refine ⟨Skel.comp hf.skel (release_skel' (c := c) hx) l2 o2, PSkel.comp hf.pskel ?_⟩
      show PSkel s₁.P (releaseEff (s₁.view c) s.A.length).P
      rw [releaseEff_eq hx']; exact pskel_refl _
    | reject => cases ho

/-! ## Protected leaves do not die -/

/-- Brief of the complement, task 3, first fact, step form: when the `guarded` of an entry is
active after a step (WC5.2 C12) and `NoDangling` holds after it (Spec 1 §54), no leaf of
`footprint(guarded)` read before the step dies in it. -/
theorem protected_not_dying {s s' : SC} {g l : Nat} (hsk : Skel s s') (hP : PSkel s.P s'.P)
    (hnd : NoDangling s'.flat) (ha : s'.flat.Active g) (hg : g < s.A.length)
    (hl : l ∈ s.flat.afp g) : ¬ Dying s s' l := by
  rintro ⟨hleaf, hu, hu'⟩
  obtain ⟨y', hy', ya'⟩ := ha
  have hlt := hu.lt
  have hleaf' : isLeaf s'.P l := (hP.isLeaf hlt).2 hleaf
  have hmem : l ∈ footprint s'.flat.P l :=
    (Arena.mem_footprint_leaf hleaf' (Nat.lt_of_lt_of_le hlt hP.1)).2 rfl
  have hfp : l ∈ y'.footprint := by
    rw [← hsk.afp hg, afp_of hy'] at hl; exact hl
  exact hnd g y' hy' ya' l hu' l hmem hfp

/-- Brief of the complement, task 3, first fact: on a `RunFull` from the initial state, under
`DDSound`, no leaf of `footprint(e.guarded)` dies in a step that leaves `e` live before and after
it. -/
theorem protected_not_dying_run {k : K} {L : MutexLayout} {statics : Statics}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} (hdd : DDSound k)
    (hstat : StaticsOK statics) (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], []))
    (h : RunFull k L σ lbls) {i : Nat} (hi : i < lbls.length) {e : SyncEntry}
    (hl : e.Live (σ i).1) (hl' : e.Live (σ (i + 1)).1) {l : Nat}
    (hfp : l ∈ (σ i).1.flat.afp e.guarded) : ¬ Dying (σ i).1 (σ (i + 1)).1 l := by
  obtain ⟨hk, hlib⟩ := runFull_inv hdd hstat h0 h (Nat.le_of_lt hi)
  obtain ⟨hk', -⟩ := runFull_inv hdd hstat h0 h hi
  obtain ⟨hsk, hP⟩ := shape_step hk hlib.2.1 (h i hi).1.1.1.1.1 (h i hi).2
  exact protected_not_dying hsk hP hk'.1.2.1.2.2 hl' (active_lt hl) hfp

/-! ## No other context has a capacity on a dying leaf -/

/-- The second fact of the brief of the complement, task 3, for one step from `st` to `st'`: in the
state before the step, no context other than the acting one has a `cap5` (WC5.2 C43) on a leaf
that dies in the step. -/
def OtherCapFree (st : SC × SyncReg × ArenaReg) (lbl : Label) (st' : SC × SyncReg × ArenaReg) :
    Prop :=
  ∀ c' ∈ List.range st.1.C.length, c' ≠ lbl.ctx → ∀ l ∈ List.range st.1.P.length,
    Dying st.1 st'.1 l → cap5 st.1 st.2.1 c' l = none

/-- Decidability of `OtherCapFree`. -/
instance (st : SC × SyncReg × ArenaReg) (lbl : Label) (st' : SC × SyncReg × ArenaReg) :
    Decidable (OtherCapFree st lbl st') := by
  unfold OtherCapFree; infer_instance

open CapacityWitness in
/-- Brief of the complement, task 3, the two facts on the four witnesses of the exceptions of
slice 3: in each, the protected leaf that dies belongs to an entry that dies with the step (the
first fact does not apply), and no context other than the acting one has a `cap5` on a leaf that
dies (`endUse(M)`, `free(R)`, `exitFrame`, `terminate`). -/
theorem exc_dying_facts :
    ¬ (⟨3, none⟩ : SyncEntry).Live ClassifyWitness.ce1 ∧
    OtherCapFree (ClassifyWitness.ceσ 3) (.kernel 0 (.endUse 0)) (ClassifyWitness.ceσ 4) ∧
    ¬ (⟨4, none⟩ : SyncEntry).Live fr6 ∧ OtherCapFree (frσ 6) (.kernel 0 (.free 2 0)) (frσ 7) ∧
    ¬ (⟨3, none⟩ : SyncEntry).Live ex5 ∧ OtherCapFree (exσ 5) (.kernel 0 .exit) (exσ 6) ∧
    ¬ (⟨3, none⟩ : SyncEntry).Live tm5 ∧ OtherCapFree (tmσ 5) (.terminate 1) (tmσ 6) ∧
    cap5 tm4 exReg 0 4 = none := by
  decide

end Ern.Concurrency.FullEncap
