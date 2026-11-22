import Ern.ConcurrencyModel.SyncInit

/-!
# The arena registry of the concurrent machine: `ArenaInv` and the §56 separation

Library invariants of the arena registry beside the synchronization registry (C2, C19;
`specs/ERN_Memory_Model_Specification_v0.1.md` §46, §55, §56):

* every labelled step keeps the authorities (`Arena.AKeep`: none is removed, reactivated, or
  given another mode, footprint or non-place holder) and the footprints of the existing places
  (`lstep_keep`);
* `ArenaInvC`: `ArenaInv` (Spec 1 §55) of every live entry of the arena registry, with the
  auxiliaries of `Arena.LInv`, on the kernel components with the globally live frames (C2);
  every labelled step preserves it (`lstep_arenaInv`), as part of theorem 2;
* `AdminSep` (Spec 1 §56; C13.7, OB-C16) is preserved by every labelled step
  (`lstep_adminSep`).
-/

namespace Ern.ConcurrencyModel

open Ern.MemoryModel Ern.MemoryModel.Access SyncPreserveAux SyncInitAux

/-- `ArenaInv` (Spec 1 §55) on the arena registry of the concurrent machine (C2, C19): the
library invariant `Arena.LInv` of the registry `ar` over the kernel components with the globally
live frames, i.e. every registered `internal` exists and every live entry satisfies `ArenaInv`
with the auxiliary `IssuedShape`. -/
def ArenaInvC (s : SC) (ar : ArenaReg) : Prop := Arena.LInv ⟨s.flat, ar⟩

namespace ArenaAux

/-! ## Authorities and footprints kept by every labelled step (Spec 1 §42, §58) -/

/-- The parameters of `enterFrame` keep a frame holder and the locals are appended (Spec 1 §72
effect): the proof of the `enter` case of `Arena.kstep_akeep`, which reads only §72.1. -/
theorem akeep_enter {t : S3} {ps : List Nat} {ls : LocalShape}
    (hpar : ∀ a ∈ ps, OptP (t.A[a]?) (fun y => y.active = true ∧ y.holder = .frame t.top ∧
      y.origin ≠ none) False) :
    Arena.AKeep t (enterEff t ps ls) := by
  intro j y hy
  have hj := lt_of_getElem? hy
  refine ⟨if j ∈ ps then { y with holder := .frame t.nF } else y, ?_, ?_⟩
  · simp only [enterEff]
    rw [List.getElem?_append_left (by rw [length_mapI]; exact hj), getElem?_mapI, hy]
    simp
  · by_cases hjp : j ∈ ps
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hjp)]
      refine ⟨rfl, rfl, id, fun _ => ?_, fun o h _ _ => h⟩
      have := hpar j hjp; rw [hy] at this
      rw [this.2.1]; rfl
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hjp)]; exact ⟨rfl, rfl, id, id, fun o h _ _ => h⟩

/-- `transfer` executed by `c` keeps the authorities (Spec 1 §63 effect): the proof of the
`transfer` case of `Arena.kstep_akeep`, which reads no precondition. -/
theorem akeep_transfer (s : SC) (c src dst : Nat) :
    Arena.AKeep s.flat (transferEffC s c src dst).flat := by
  refine Arena.akeep_map (f := fun y => if heldIn (s.view c).P src y.holder then
    { y with holder := mvTo (s.view c).P src dst y.holder } else y) rfl fun y => ?_
  cases e : y.holder with
  | frame f => simp [heldIn, e, Holder.isPlace]
  | place r =>
    by_cases hc : partOf (s.view c).P r src <;> simp [heldIn, hc, mvTo, Holder.isPlace, e]

/-- The yield of C5.3 keeps the authorities when the yielded parameters are frame-held. -/
theorem akeep_yield {t : SC} {ps : List Nat} {f : Nat}
    (hpar : ∀ a ∈ ps, ∀ y, t.A[a]? = some y → y.holder.isPlace = false) :
    Arena.AKeep t.flat (yieldEff t ps f).flat := by
  intro j y hy
  refine ⟨if j ∈ ps then { y with holder := .frame f } else y, ?_, ?_⟩
  · have hy' : t.A[j]? = some y := hy
    show (mapI _ 0 t.A)[j]? = _
    rw [getElem?_mapI, hy']; simp
  · by_cases hjp : j ∈ ps
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hjp)]
      exact ⟨rfl, rfl, id, fun _ => hpar j hjp y hy, fun o h _ _ => h⟩
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hjp)]; exact ⟨rfl, rfl, id, id, fun o h _ _ => h⟩

/-- `AKeep` reads the authorities only (Spec 1 §42). -/
theorem akeep_of_A {s t s' t' : S3} (h1 : t.A = s.A) (h2 : t'.A = s'.A)
    (h : Arena.AKeep s s') : Arena.AKeep t t' := by
  unfold Arena.AKeep S3.Active at *; rw [h1, h2]; exact h

/-- Authorities kept and footprints of the existing places kept. -/
def Keep (s s' : SC) : Prop :=
  Arena.AKeep s.flat s'.flat ∧ ∀ q, q < s.P.length → ∀ l, l ∈ footprint s'.P q ↔ l ∈ footprint s.P q

/-- `Keep` composes when no place is removed. -/
theorem Keep.trans {s s' s'' : SC} (h : Keep s s') (h' : Keep s' s'')
    (hlen : s.P.length ≤ s'.P.length) : Keep s s'' :=
  ⟨h.1.trans h'.1, fun q hq l => (h'.2 q (Nat.lt_of_lt_of_le hq hlen) l).trans (h.2 q hq l)⟩

/-- An unchanged kernel state. -/
theorem keep_same {s s' : SC} (hA : s'.A = s.A) (hP : s'.P = s.P) : Keep s s' :=
  ⟨Arena.akeep_of_eq hA, fun _ _ _ => by rw [hP]⟩

/-- A kernel step run on the view of `c` and written back (C2): `Arena.kstep_akeep` and
`Arena.kstep_fp`. -/
theorem keep_view {k : K} {op : KernelOp} {c : Nat} {s : SC} {t : S3}
    (hR : op.Step k (s.view c) (.ok t)) : Keep s (s.set t) := by
  have hk : KStep k (s.view c) t := kstep_iff.2 ⟨op, hR⟩
  exact ⟨akeep_of_A (s := s.view c) (s' := t) rfl rfl (Arena.kstep_akeep hk),
    fun q hq l => view_fp hR hq l⟩

/-- Every inherited operation executed by `c` keeps the authorities and the footprints of the
existing places (Spec 1 §60–§75 effects re-indexed, C2, C6). -/
theorem opStepC_keep {k : K} {op : KernelOp} {c : Nat} {s s' : SC}
    (h : opStepC k op c s (.ok s')) : Keep s s' := by
  cases op
  case transfer src dst =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
    refine ⟨akeep_transfer s c src dst, fun q _ l => ?_⟩
    show l ∈ footprint (transferEff (s.view c) src dst).P q ↔ _
    rw [transfer_footprint]; exact Iff.rfl
  case depend q x =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; exact keep_same rfl rfl
  case store a p =>
    obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
    have hd := hpre.derivedHeld
    unfold OptP at hd; split at hd
    · rename_i y hy
      have hy' : (s.view c).A[a]? = some y := hy
      have he := Arena.storeEff_eq (p := p) hy'
      refine ⟨Arena.akeep_set (x' := { y with holder := .place p }) hy' ?_ rfl rfl id
        (fun h => by simp [Holder.isPlace] at h) rfl, fun q _ l => ?_⟩
      · show (storeEff (s.view c) a p).A = _; rw [he]; rfl
      · show l ∈ footprint (storeEff (s.view c) a p).P q ↔ _; rw [he]; exact Iff.rfl
    · exact hd.elim
  case enter ps ls =>
    obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
    exact ⟨akeep_of_A rfl rfl (akeep_enter (t := s.view c) (ls := ls) hpre.params),
      fun q hq l => Arena.footprint_shapeP hpre.localsOK hq l⟩
  case exit =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
    exact ⟨akeep_of_A rfl rfl (Arena.exit_akeep (s.view c)), fun _ _ _ => Iff.rfl⟩
  all_goals (obtain ⟨t, hR, rfl⟩ := viewStep_ok h; exact keep_view hR)

/-- The places of `enterFrame` and `spawn` are appended (Spec 1 §72 effect). -/
theorem enter_len (t : S3) (ps : List Nat) (ls : LocalShape) :
    t.P.length ≤ (enterEff t ps ls).P.length := by
  simp [enterEff, enterP, shapeP]

/-- The transfer phases of the by-value composite keep the authorities and the footprints
(Spec 1 §63 effect; C5.2). -/
theorem keep_transfers (c : Nat) :
    ∀ (t : SC) (vs : List (Nat × Nat)), Keep t (transfersEff c t vs) ∧
      t.P.length ≤ (transfersEff c t vs).P.length
  | t, [] => ⟨keep_same rfl rfl, Nat.le_refl _⟩
  | t, v :: vs => by
    have h₁ : Keep t (transferEffC t c v.1 v.2) := by
      refine ⟨akeep_transfer t c v.1 v.2, fun q _ l => ?_⟩
      show l ∈ footprint (transferEff (t.view c) v.1 v.2).P q ↔ _
      rw [transfer_footprint]; exact Iff.rfl
    have hl₁ : t.P.length ≤ (transferEffC t c v.1 v.2).P.length := by
      show _ ≤ (transferEff (t.view c) v.1 v.2).P.length
      rw [transfer_len]; exact Nat.le_refl _
    obtain ⟨h₂, hl₂⟩ := keep_transfers c (transferEffC t c v.1 v.2) vs
    exact ⟨h₁.trans h₂ hl₁, Nat.le_trans hl₁ hl₂⟩

/-- The by-value composite keeps the authorities and the footprints (C5 effects). -/
theorem keep_spawnVal {k : K} {s s' : SC} {c : Nat} {ps : List Nat} {ls : LocalShape}
    {vs : List (Nat × Nat)} (h : SpawnValStep k s c ps ls vs (.ok s')) : Keep s s' := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  have h₁ : Keep s (spawnCreate s c ls) :=
    ⟨akeep_of_A rfl rfl (akeep_enter (t := s.view c) (ps := []) (ls := ls)
      (fun _ h => by cases h)), fun q hq l => Arena.footprint_shapeP hpre.localsOK hq l⟩
  have hl₁ : s.P.length ≤ (spawnCreate s c ls).P.length := enter_len (s.view c) [] ls
  obtain ⟨h₂, hl₂⟩ := keep_transfers c (spawnCreate s c ls) vs
  have h₃ : Keep (transfersEff c (spawnCreate s c ls) vs) (spawnValEff s c ps ls vs) := by
    refine ⟨akeep_yield fun a ha y hy => ?_, fun _ _ _ => Iff.rfl⟩
    have := hpre.paramsAtYield a ha
    have hy' : ((transfersEff c (spawnCreate s c ls) vs).view c).A[a]? = some y := hy
    rw [hy'] at this; rw [this.2.1]; rfl
  exact (h₁.trans h₂ hl₁).trans h₃ (Nat.le_trans hl₁ hl₂)

/-- Every labelled step keeps the authorities and the footprints of the existing places (Spec 1
§42, §58, §60–§78 effects; C4–C8, C13–C18). -/
theorem lstep_keep {ks : KShared} {L : MutexLayout} {lbl : Label} {st st' : SC × SyncReg × ArenaReg}
    (h : LStep ks L lbl st st') : Keep st.1 st'.1 := by
  cases h with
  | kernel h => exact opStepC_keep h
  | @spawn s s' reg ar c ps ls h =>
    obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
    exact ⟨akeep_of_A (s := s.view c) (s' := enterEff (s.view c) ps ls) rfl rfl
      (akeep_enter hpre.params), fun q hq l => Arena.footprint_shapeP hpre.localsOK hq l⟩
  | @terminate s s' reg ar c h =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
    exact ⟨akeep_of_A (s := s.view c) (s' := exitEff (s.view c)) rfl rfl (Arena.exit_akeep _),
      fun _ _ _ => Iff.rfl⟩
  | join h => cases h; exact keep_same rfl rfl
  | deriveSync h =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
    exact ⟨Arena.akeep_append rfl, fun _ _ _ => Iff.rfl⟩
  | newMutex h => obtain ⟨-, rfl⟩ := h; exact keep_same rfl rfl
  | acquire h =>
    obtain ⟨e, -, -, -, rfl⟩ := h
    exact ⟨Arena.akeep_append rfl, fun _ _ _ => Iff.rfl⟩
  | unlock h =>
    obtain ⟨e, g, -, -, -, hrel, -, -, rfl⟩ := h
    exact opStepC_keep (k := ks.toK) (op := .release g) ⟨_, .ok hrel, rfl⟩
  | resetLock h => obtain ⟨-, -, -, -, -, -, rfl⟩ := h; exact keep_same rfl rfl
  | spawnVal h => exact keep_spawnVal h
  | newArena h => obtain ⟨-, -, rfl⟩ := newArenaStepC_ok h; exact keep_same rfl rfl
  | issue h =>
    obtain ⟨E, s₁, -, -, -, hsp, hsto, -⟩ := issueStepC_ok h
    obtain ⟨t, hR, rfl⟩ := viewStep_ok hsp
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hR
    exact (keep_view hR).trans (opStepC_keep hsto) (Nat.le_refl _)
  | reset h =>
    obtain ⟨E, s₁, -, hd, hrl, -, -⟩ := resetStepC_ok (k := ks.toK) h
    obtain ⟨t, hR, rfl⟩ := viewStep_ok hd
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hR
    exact (keep_view hR).trans (opStepC_keep hrl) (Nat.le_refl _)
  | readShared h => exact keep_same rfl rfl
  | writeShared h => exact opStepC_keep (writeSharedC_ok_kernel h)
  | cas h =>
    rcases cas_ok_cases h with hk' | rfl
    · exact opStepC_keep hk'
    · exact keep_same rfl rfl

end ArenaAux

open ArenaAux

/-! ## `ArenaInv` on the arena registry (Spec 1 §55; C19) -/

namespace ArenaAux

open Ern.MemoryModel.Arena in
/-- A step keeping the authorities and the footprints of the existing places preserves the library
invariant of an unchanged registry, when the state before satisfies `WF3` and the state after
`NoDangling` (Spec 1 §55, §57): the proof of `Arena.lInv_kernel`, which reads of the kernel step
only `Arena.AKeep` and the footprints. -/
theorem lInv_keep {t t' : S3} {ar : ArenaReg} (hA : AKeep t t')
    (hfp : ∀ q, q < t.P.length → ∀ l, l ∈ footprint t'.P q ↔ l ∈ footprint t.P q)
    (hw : WF3 t) (hnd : NoDangling t') (hi : LInv ⟨t, ar⟩) : LInv ⟨t', ar⟩ := by
  intro E hE
  obtain ⟨hlt, hinv⟩ := hi E hE
  refine ⟨hA.lt hlt, fun hlive => ?_⟩
  have hEI := hinv (hA.active_back hlive hlt)
  have hfp' := hfp E.storage hEI.1.storageUsable.lt
  refine entryInv_transport hEI hA hfp' ?_ hlive
  obtain ⟨l, hl⟩ := exists_mem_footprint hw (t.P.length - E.storage + 1) E.storage (by omega)
    hEI.1.storageUsable.lt
  obtain ⟨yi, hyi, -⟩ := hEI.1.active
  obtain ⟨y', hy', -, hf', -⟩ := hA _ yi hyi
  obtain ⟨y'', hy'', ya''⟩ := hlive
  rw [hy'] at hy''; cases hy''
  have hli : l ∈ yi.footprint := by
    have := (hEI.1.fpEq l).2 hl; simpa [S3.afp, hyi] using this
  exact usable_of_covered hnd hy' ya'' (hf' ▸ hli) ((hfp' l).2 hl)

open Ern.MemoryModel.Arena in
/-- The library invariant after `issue` of entry `i` (Spec 1 §55, §77): the proof of
`Arena.lInv_issue`, which reads of the step only §77.1 (the entry is live), §77.2 (the region
belongs to the storage), the effective right of `internal` on the region (§77.5, §61) and the
arrival state `issueKEff` (`Arena.issueKEff_eq`). -/
theorem lInv_issue_core {L : LState} {i : Nat} {E : ArenaEntry} {region : List Nat} {dst : Nat}
    (hE : L.arenas[i]? = some E) (hlive : L.kern.Active E.internal)
    (hreg : ∀ l ∈ region, l ∈ footprint L.kern.P E.storage)
    (hright : IssueRight L.kern E region) (hi : LInv L) :
    LInv ⟨issueKEff L.kern E region dst, L.arenas.set i (issueMeta L.kern E region)⟩ := by
  have hEm : E ∈ L.arenas := List.mem_of_getElem? hE
  have hil := (hi E hEm).1
  have hAe : (issueKEff L.kern E region dst).A =
      L.kern.A ++ [⟨.modify, some E.internal, region, .place dst, true⟩] := rfl
  have hold : ∀ F ∈ L.arenas, F.internal < (issueKEff L.kern E region dst).A.length ∧
      (Live (issueKEff L.kern E region dst) F → EntryInv (issueKEff L.kern E region dst) F) := by
    intro F hF
    obtain ⟨hlt, hinv⟩ := hi F hF
    refine ⟨by rw [hAe, List.length_append]; omega, fun hl => ?_⟩
    exact entryInv_append (hinv ((akeep_append hAe).active_back hl hlt)) hAe rfl rfl rfl hl
  intro F hF
  rcases List.mem_or_eq_of_mem_set hF with hF | rfl
  · exact hold F hF
  · obtain ⟨hlt, hinv'⟩ := hold E hEm
    refine ⟨hlt, fun hl => ?_⟩
    obtain ⟨hai, hsh⟩ := hinv' hl
    obtain ⟨hai0, hsh0⟩ := (hi E hEm).2 hlive
    have hnew : (issueKEff L.kern E region dst).A[L.kern.A.length]? =
        some ⟨.modify, some E.internal, region, .place dst, true⟩ := by simp [hAe]
    have hold' : ∀ e ∈ E.issued, e.2 < L.kern.A.length := fun e he => by
      obtain ⟨y, hy, -⟩ := hsh0 e he; exact lt_of_getElem? hy
    have hact : ∀ e ∈ E.issued, (issueKEff L.kern E region dst).Active e.2 → L.kern.Active e.2 :=
      fun e he ha => (akeep_append hAe).active_back ha (hold' e he)
    have hdis : ∀ e ∈ E.issued, L.kern.Active e.2 → ∀ l ∈ region, l ∉ e.1 := by
      intro e he ha l hl hle
      obtain ⟨y, hy, -, -, hf, hm⟩ := hsh0 e he
      obtain ⟨y', hy', ya⟩ := ha
      rw [hy] at hy'; cases hy'
      exact effective_ne_modify_of_desc hy ya (hf ▸ hle) (hai0.derived e he ⟨y, hy, ya⟩) hm
        (allows_modify_iff.1 (hright l hl))
    refine ⟨⟨hai.storageUsable, hai.fpEq, hai.active, hai.shape,
      fun l hl => hai.availableIn l (List.mem_filter.1 hl).1, fun e he l hl => ?_,
      fun e he e' he' hne ha ha' l hl hl' => ?_, fun e he ha l hl hla => ?_,
      fun e he ha => ?_⟩, fun e he => ?_⟩
    · rcases List.mem_cons.1 he with rfl | he
      · exact hreg l hl
      · exact hai.issuedIn e he l hl
    · rcases List.mem_cons.1 he with rfl | he <;> rcases List.mem_cons.1 he' with rfl | he'
      · exact hne rfl
      · exact hdis e' he' (hact e' he' ha') l hl hl'
      · exact hdis e he (hact e he ha) l hl' hl
      · exact hai.disjoint e he e' he' hne ha ha' l hl hl'
    · have hla' := List.mem_filter.1 hla
      rcases List.mem_cons.1 he with rfl | he
      · simp at hla'; exact hla'.2 hl
      · exact hai.notAvailable e he ha l hl hla'.1
    · rcases List.mem_cons.1 he with rfl | he
      · show E.internal ∈ (L.kern.addAuth ⟨.modify, some E.internal, region, .place dst, true⟩).ancs
          L.kern.A.length
        rw [ancs_addAuth_self rfl hil]; exact List.mem_cons_self ..
      · exact hai.derived e he ha
    · rcases List.mem_cons.1 he with rfl | he
      · exact ⟨_, hnew, rfl, hil, rfl, rfl⟩
      · exact hsh e he

/-- The library invariant depends on the stack only through membership (Spec 1 §40, §55). -/
theorem lInv_congrF {t : S3} {F' : List Nat} {ar : ArenaReg} (hF : ∀ f, f ∈ F' ↔ f ∈ t.F) :
    Arena.LInv ⟨{ t with F := F' }, ar⟩ ↔ Arena.LInv ⟨t, ar⟩ := by
  have hu : ∀ q, ({ t with F := F' } : S3).Usable q ↔ t.Usable q := fun q => usable_mem_congr hF
  constructor
  · intro h E hE
    obtain ⟨hlt, hinv⟩ := h E hE
    exact ⟨hlt, fun hl => by
      obtain ⟨ha, hs⟩ := hinv hl
      exact ⟨{ ha with storageUsable := (hu _).1 ha.storageUsable }, hs⟩⟩
  · intro h E hE
    obtain ⟨hlt, hinv⟩ := h E hE
    exact ⟨hlt, fun hl => by
      obtain ⟨ha, hs⟩ := hinv hl
      exact ⟨{ ha with storageUsable := (hu _).2 ha.storageUsable }, hs⟩⟩

end ArenaAux

/-- Theorem 2, arena part (Spec 1 §55; C19, C23): every labelled step, the arena operations included,
preserves `ArenaInvC` (`ArenaInv` of every live entry of the arena registry, with the auxiliaries
of `Arena.LInv`), when the state before satisfies `WF3` and the state after `NoDangling` (both
supplied by theorem 2). Fragment: every labelled step, interleaved at the grain of abstract
steps. -/
theorem lstep_arenaInv {ks : KShared} {L : MutexLayout} {lbl : Label} {st st' : SC × SyncReg × ArenaReg}
    (h : LStep ks L lbl st st') (hw : WF3 st.1.flat) (hnd : NoDangling st'.1.flat)
    (hi : ArenaInvC st.1 st.2.2) : ArenaInvC st'.1 st'.2.2 := by
  have hkp := lstep_keep h
  have keep : st'.2.2 = st.2.2 → ArenaInvC st'.1 st'.2.2 := fun e => by
    unfold ArenaInvC; rw [e]; exact lInv_keep hkp.1 hkp.2 hw hnd hi
  cases h
  case newArena s reg ar c st i st' h =>
    obtain ⟨-, hpre, rfl⟩ := newArenaStepC_ok h
    intro F hF
    rcases List.mem_append.1 hF with hF | hF
    · exact hi F hF
    · rw [List.mem_singleton.1 hF]
      have hia := hpre.internalAuth
      cases hy : s.A[i]? with
      | none => rw [hy] at hia; exact hia.elim
      | some y => exact ⟨lt_of_getElem? hy, fun _ => ⟨hpre.arenaInv, fun _ he => by cases he⟩⟩
  case issue s reg ar c i region dst st' h =>
    rcases st' with ⟨s', ar'⟩
    obtain ⟨E, s₁, hE, hst, -, hsp, hsto, he2⟩ := issueStepC_ok h
    dsimp only at hsto he2
    subst he2
    obtain ⟨t, hR, rfl⟩ := viewStep_ok hsp
    have hR' : SplitStep ks.toK E.internal [region] (s.view c) (.ok t) := hR
    obtain ⟨hp, rfl⟩ := Guarded.ok_iff.1 hR'
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hsto
    have hv : (s.set (splitEff (s.view c) E.internal [region])).view c =
        splitEff (s.view c) E.internal [region] := SC.view_set (opStepC_live hsp) rfl
    have hflat : (storeEffC (s.set (splitEff (s.view c) E.internal [region])) c s.A.length
        dst).flat = Arena.issueKEff s.flat E region dst := by
      unfold storeEffC; rw [hv]
      show (s.set (storeEff (splitEff (s.view c) E.internal [region]) (s.view c).A.length
        dst)).flat = _
      rw [← Arena.issueKEff_eq]; rfl
    unfold ArenaInvC; rw [hflat]
    exact lInv_issue_core (L := ⟨s.flat, ar⟩) hE hst.live hst.regionIn (fun l hl => by
      have := hp.modifyOn _ (List.mem_singleton_self _) l hl
      show Allows (effective (s.view c) E.internal l) .modify
      rw [this]; exact Arena.allows_some_modify _) hi
  case reset s reg ar c i st' h =>
    rcases st' with ⟨s', ar'⟩
    obtain ⟨o₃, hr, ho⟩ := h
    cases hr with
    | noEntry => cases ho
    | derive => cases ho
    | release => cases ho
    | contract => cases ho
    | @ok E t₁ t₂ hE hd hrl hnd' =>
      cases ho
      have hl : s.Live c := SC.live_of_exercisable (Guarded.ok_iff.1 hd).1.exercisable
      have h0 : Arena.LInv ⟨s.view c, ar⟩ :=
        (lInv_congrF (t := s.flat) (F' := (s.view c).F) fun _ => SC.mem_view_F hl).2 hi
      have hL := Arena.lInv_reset (.ok hE hd hrl hnd') h0
      have hF : t₂.F = (s.view c).F := by
        obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hd
        obtain ⟨hp2, rfl⟩ := Guarded.ok_iff.1 hrl
        obtain ⟨x, hx, -⟩ := hp2.active
        rw [releaseEff_eq hx]; rfl
      exact (lInv_congrF (t := t₂) (F' := s.frames) fun f => by
        rw [hF]; exact (SC.mem_view_F hl).symm).2 hL
  all_goals exact keep rfl

/-! ## The separation of the registries (Spec 1 §56; C13.7, OB-C16) -/

/-- The `guarded` of a live entry belongs to the registry of live administrations of the
synchronization registry (Spec 1 §56). -/
theorem mem_liveGuardeds {s : SC} {reg : SyncReg} {e : SyncEntry} (he : e ∈ reg)
    (hl : e.Live s) : e.guarded ∈ liveGuardeds s reg :=
  List.mem_map.2 ⟨e, List.mem_filter.2 ⟨he, decide_eq_true hl⟩, rfl⟩

/-- The `internal` of a live arena belongs to the registry of live administrations of the arena
registry (Spec 1 §46, §56). -/
theorem mem_liveInternals {t : S3} {ar : ArenaReg} {E : Arena.ArenaEntry} (hE : E ∈ ar)
    (hl : Arena.Live t E) : E.internal ∈ Arena.liveInternals t ar :=
  List.mem_map.2 ⟨E, List.mem_filter.2 ⟨hE, decide_eq_true hl⟩, rfl⟩

/-- `AdminSep` (Spec 1 §56; C13.7, OB-C16) is preserved by every labelled step: `newMutex`
and `newArena` check the other registry through the unified guard (C13.7, Spec 1 §76.4); no
other step registers an identity, and no step reactivates an authority (Spec 1 §42, §58), the
registered identities existing (`RegBound`, C21.6, and the bound of `ArenaInvC`). -/
theorem lstep_adminSep {ks : KShared} {L : MutexLayout} {lbl : Label} {st st' : SC × SyncReg × ArenaReg}
    (h : LStep ks L lbl st st') (hsep : AdminSep st.1 st.2.1 st.2.2)
    (hb : ∀ e ∈ st.2.1, e.guarded < st.1.A.length)
    (hb' : ∀ E ∈ st.2.2, E.internal < st.1.A.length) : AdminSep st'.1 st'.2.1 st'.2.2 := by
  have hA := (lstep_keep h).1
  have back : ∀ x, x < st.1.A.length → st'.1.flat.Active x → st.1.flat.Active x :=
    fun x hx ha => hA.active_back ha hx
  have same : st'.2.1 = st.2.1 → st'.2.2 = st.2.2 → AdminSep st'.1 st'.2.1 st'.2.2 :=
    fun e1 e2 e he E hE hl hL => by
      rw [e1] at he; rw [e2] at hE
      exact hsep e he E hE (back _ (hb e he) hl) (back _ (hb' E hE) hL)
  cases h
  case newMutex s reg ar c g st' h =>
    obtain ⟨hpre, rfl⟩ := h
    intro e he E hE hl hL
    rcases List.mem_append.1 he with he | he
    · exact hsep e he E hE hl hL
    · rw [List.mem_singleton.1 he]
      intro heq
      have heq' : g = E.internal := heq
      exact hpre.otherAdmin (heq' ▸ mem_liveInternals hE hL)
  case acquire s reg ar c i st' h =>
    obtain ⟨e₀, hi, -, -, rfl⟩ := h
    intro e he E hE hl hL
    rcases mem_set_cases he with rfl | ⟨j, hj, -⟩
    · exact hsep e₀ (List.mem_of_getElem? hi) E hE (back _ (hb _ (List.mem_of_getElem? hi)) hl)
        (back _ (hb' E hE) hL)
    · exact hsep e (List.mem_of_getElem? hj) E hE (back _ (hb _ (List.mem_of_getElem? hj)) hl)
        (back _ (hb' E hE) hL)
  case unlock s reg ar c i st' h =>
    obtain ⟨e₀, g, hi, -, -, -, -, -, rfl⟩ := h
    intro e he E hE hl hL
    rcases mem_set_cases he with rfl | ⟨j, hj, -⟩
    · exact hsep e₀ (List.mem_of_getElem? hi) E hE (back _ (hb _ (List.mem_of_getElem? hi)) hl)
        (back _ (hb' E hE) hL)
    · exact hsep e (List.mem_of_getElem? hj) E hE (back _ (hb _ (List.mem_of_getElem? hj)) hl)
        (back _ (hb' E hE) hL)
  case resetLock s reg ar c i st' h =>
    obtain ⟨e₀, hi, -, -, -, -, rfl⟩ := h
    intro e he E hE hl hL
    rcases mem_set_cases he with rfl | ⟨j, hj, -⟩
    · exact hsep e₀ (List.mem_of_getElem? hi) E hE hl hL
    · exact hsep e (List.mem_of_getElem? hj) E hE hl hL
  case newArena s reg ar c st i st' h =>
    obtain ⟨-, hpre, rfl⟩ := newArenaStepC_ok h
    intro e he E hE hl hL
    rcases List.mem_append.1 hE with hE | hE
    · exact hsep e he E hE hl hL
    · rw [List.mem_singleton.1 hE]
      intro heq
      have heq' : e.guarded = i := heq
      exact hpre.guard _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
        (heq' ▸ mem_liveGuardeds he hl)
  case issue s reg ar c i region dst st' h =>
    obtain ⟨E₀, s₁, hi, -, -, -, -, he2⟩ := issueStepC_ok h
    intro e he E hE hl hL
    rw [he2] at hE
    rcases List.mem_or_eq_of_mem_set hE with hE | rfl
    · exact hsep e he E hE (back _ (hb e he) hl) (back _ (hb' E hE) hL)
    · exact hsep e he E₀ (List.mem_of_getElem? hi) (back _ (hb e he) hl)
        (back _ (hb' _ (List.mem_of_getElem? hi)) hL)
  case reset s reg ar c i st' h =>
    obtain ⟨E₀, s₁, hi, -, -, -, he2⟩ := resetStepC_ok (k := ks.toK) h
    intro e he E hE hl hL
    rw [he2] at hE
    rcases List.mem_or_eq_of_mem_set hE with hE | rfl
    · exact hsep e he E hE (back _ (hb e he) hl) (back _ (hb' E hE) hL)
    · exact hsep e he E₀ (List.mem_of_getElem? hi) (back _ (hb e he) hl)
        (back _ (hb' _ (List.mem_of_getElem? hi)) hL)
  all_goals exact same rfl rfl

/-! ## Uniqueness of the live `internal` identities inside the arena registry (Spec 1 §56) -/

/-- `ArenaReg.unique` (Spec 1 §56, first sentence: "An authority identity may serve as `internal`
for at most one live administrative abstraction"), inside the arena registry: two live entries,
by position, do not share their `internal` identity. -/
def ArenaReg.unique (ar : ArenaReg) (s : SC) : Prop :=
  ∀ (i j : Nat) (E E' : Arena.ArenaEntry), ar[i]? = some E → ar[j]? = some E' →
    Arena.Live s.flat E → Arena.Live s.flat E' → E.internal = E'.internal → i = j

namespace ArenaAux

/-- The entries of a registry extended by one entry (Spec 1 §76 effect). -/
theorem append_one_cases {ar : ArenaReg} {E₀ E : Arena.ArenaEntry} {j : Nat}
    (h : (ar ++ [E₀])[j]? = some E) : ar[j]? = some E ∨ (j = ar.length ∧ E = E₀) := by
  by_cases hj : j < ar.length
  · rw [List.getElem?_append_left hj] at h; exact .inl h
  · rw [List.getElem?_append_right (Nat.le_of_not_lt hj)] at h
    cases e : j - ar.length with
    | zero =>
      rw [e] at h; simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      exact .inr ⟨by omega, h.symm⟩
    | succ n => rw [e] at h; simp at h

/-- An update of entry `i` that keeps its `internal` (Spec 1 §77, §78 metadata effects) keeps
the `internal` at every position. -/
theorem set_internal {ar : ArenaReg} {i j : Nat} {E₀ X E : Arena.ArenaEntry}
    (hi : ar[i]? = some E₀) (hX : X.internal = E₀.internal) (h : (ar.set i X)[j]? = some E) :
    ∃ F, ar[j]? = some F ∧ F.internal = E.internal := by
  rcases Arena.get_set_internal h with ⟨rfl, E₁, hE₁, rfl⟩ | h
  · rw [hi] at hE₁; cases hE₁; exact ⟨E₀, hi, hX.symm⟩
  · exact ⟨E, h, rfl⟩

end ArenaAux

/-- `ArenaReg.unique` (Spec 1 §56) is preserved by every labelled step: `newArena` checks the
arena registry through its guard (Spec 1 §76.4); `issue` and `reset` keep the `internal` of the
updated entry (Spec 1 §77, §78 effects); no other step changes the arena registry, and no step
reactivates an authority (Spec 1 §42, §58), the registered identities existing (bound of
`ArenaInvC`). -/
theorem lstep_arenaUnique {ks : KShared} {L : MutexLayout} {lbl : Label}
    {st st' : SC × SyncReg × ArenaReg} (h : LStep ks L lbl st st')
    (hu : ArenaReg.unique st.2.2 st.1) (hb : ∀ E ∈ st.2.2, E.internal < st.1.A.length) :
    ArenaReg.unique st'.2.2 st'.1 := by
  have hA := (lstep_keep h).1
  have mapped : (∀ (j : Nat) (E : Arena.ArenaEntry), st'.2.2[j]? = some E →
      ∃ F : Arena.ArenaEntry, st.2.2[j]? = some F ∧ F.internal = E.internal) →
      ArenaReg.unique st'.2.2 st'.1 := by
    intro hmap i j E E' hi hj hl hl' he
    obtain ⟨F, hF, hFi⟩ := hmap i E hi
    obtain ⟨F', hF', hFi'⟩ := hmap j E' hj
    have hbF := hb F (List.mem_of_getElem? hF)
    have hbF' := hb F' (List.mem_of_getElem? hF')
    refine hu i j F F' hF hF' ?_ ?_ (by rw [hFi, hFi', he])
    · show st.1.flat.Active F.internal
      rw [hFi] at hbF ⊢; exact hA.active_back hl hbF
    · show st.1.flat.Active F'.internal
      rw [hFi'] at hbF' ⊢; exact hA.active_back hl' hbF'
  cases h
  case newArena s reg ar c st0 i₀ st'' h =>
    obtain ⟨-, hpre, rfl⟩ := newArenaStepC_ok h
    intro i j E E' hi hj hl hl' he
    have notLive : ∀ F ∈ ar, Arena.Live s.flat F → F.internal ≠ i₀ := fun F hF hlF heq =>
      hpre.guard _ (List.mem_cons_self ..) (heq ▸ mem_liveInternals hF hlF)
    rcases ArenaAux.append_one_cases hi with hi | ⟨rfl, rfl⟩ <;>
      rcases ArenaAux.append_one_cases hj with hj | ⟨rfl, rfl⟩
    · exact hu i j E E' hi hj hl hl' he
    · exact absurd he (notLive E (List.mem_of_getElem? hi) hl)
    · exact absurd he.symm (notLive E' (List.mem_of_getElem? hj) hl')
    · rfl
  case issue s reg ar c i₀ region dst st'' h =>
    obtain ⟨E₀, s₁, hE, -, -, -, -, he2⟩ := issueStepC_ok h
    exact mapped fun j E hj => ArenaAux.set_internal (X := Arena.issueMeta s.flat E₀ region) hE rfl
      (by rw [← he2]; exact hj)
  case reset s reg ar c i₀ st'' h =>
    obtain ⟨E₀, s₁, hE, -, -, -, he2⟩ := resetStepC_ok (k := ks.toK) h
    exact mapped fun j E hj => ArenaAux.set_internal (X := Arena.resetMeta s.flat E₀) hE rfl
      (by rw [← he2]; exact hj)
  all_goals exact mapped fun j E hj => ⟨E, hj, rfl⟩

end Ern.ConcurrencyModel
