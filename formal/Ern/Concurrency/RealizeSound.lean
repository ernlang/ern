import Ern.Concurrency.ArenaConservativity

/-!
# Pointer soundness and pinned addresses under `ReprC` (Spec 1 §82.3, §82.6; WC4 C25)

Extension of R1 (`Ern.Concurrency.Realize`) at the grain of abstract steps: contexts interleave
at the grain of abstract steps, and every statement below is about that fragment only.

* `pointer_sound_storeC` (`Refinement.pointer_sound_store` transported to `ReprC`, §82.2, §82.3):
  the realization of `store` executed by a context writes into the target leaf a reference that
  decodes to the address of the stored authority, with the provenance of the allocation of its
  effective anchor; `issue_pointer_soundC`: the same for the block stored by `issue` (Spec 1 §77,
  Part XIV).
* `pinned_address_stableC` (`Refinement.pinned_address_stable` transported to `ReprC`, §82.6): for
  every labelled step, a pinned leaf whose allocation is live before the step keeps a live
  allocation and the same address after the raw operations of the step.

The proofs of `Refinement` read the preconditions of `store` (§65.1, §65.2) and of `exitFrame`
(§73.1, §73.3) only; the copies below read the same clauses of their re-indexed forms
(`StorePreC`, `ExitPreC`, `TermPre`).
-/

namespace Ern.Concurrency

open Ern.MemoryModel Ern.MemoryModel.Access Ern.MemoryModel.Refinement
open PreservationAux

/-! ## §82.3: pointer soundness of `store` -/

/-- Pointer soundness of `store` executed by `c` (Spec 1 §82.2 pointer validity and its last
sentence, §82.3; WC4 C2, C25), at the grain of abstract steps: under `ReprC`, `FramesC`, `WF3` and
`NoDangling` of the globally live frames, an `ok` step of `store(authority, target)` executed by
`c` whose reference has the address `ad` (`ptrAddr` on the view of `c`), a target of pointer size
and the obligation of the encoding for that reference: the conclusions of
`Refinement.pointer_sound_store` on the view of `c`. The proof is that of
`Refinement.pointer_sound_store`, which reads §65.1 (the authority is active) and §65.2 (the
target is a usable leaf) only. -/
theorem pointer_sound_storeC {Ty : Type} {k : K} {ty : Nat → Ty} {pe : PtrEnc} {L : Layout}
    {rtok : Nat → Nat} {s s' : SC} {m : Machine.State} {c a p ad : Nat}
    (hR : ReprC L rtok s m) (hfr : FramesC s) (hw : WF3 s.flat) (hnd : NoDangling s.flat)
    (h : opStepC k (.store a p) c s (.ok s')) (had : ptrAddr m L (s.view c) a = ad)
    (hsz : (L p).len = pe.size) (henc : PtrEncAt pe ad (some (anchorAlloc L (s.view c) a))) :
    pe.decode (bytesOf (run m (storeOps (Ty := Ty) pe m L ty (s.view c) a p)) L p) = ad ∧
      (∀ i, i < (L p).len →
        (bytesOf (run m (storeOps (Ty := Ty) pe m L ty (s.view c) a p)) L p i).2 =
          some (anchorAlloc L (s.view c) a)) ∧
      (∀ l ∈ (s.view c).afp a, (L l).alloc = anchorAlloc L (s.view c) a ∧
        AllocP m (L l).alloc fun al => al.live = true ∧ (L l).off + (L l).len ≤ al.size) ∧
      ((∀ l ∈ (s.view c).afp a, (L l).len = 0) → ad = baseOf m (anchorAlloc L (s.view c) a)) ∧
      ((∃ l ∈ (s.view c).afp a, 0 < (L l).len) → ∃ l ∈ (s.view c).afp a, 0 < (L l).len ∧
        ad = leafAddr m L l ∧ ∀ l' ∈ (s.view c).afp a, 0 < (L l').len → ad ≤ leafAddr m L l') := by
  obtain ⟨-, h⟩ := h; obtain ⟨hpre, -⟩ := Guarded.ok_iff.1 h
  have hRv := (reprC_view c).1 hR
  have hwv : WF3 (s.view c) := SC.wf3_view hfr hw
  have hndv : NoDangling (s.view c) := noDangling_mem_congr hnd fun _ => SC.mem_view_F
  have htgt : LeafOfUsable (s.view c) p := ⟨p, List.mem_range.2 hpre.usable.lt, hpre.usable,
    mem_footprint.2 ⟨hpre.usable.lt, hpre.leaf, hpre.usable.lt, .inl rfl⟩⟩
  obtain ⟨hpP, hpf, hpu⟩ := leaf_of_leafOfUsable hwv htgt
  obtain ⟨pa, hpa, -⟩ := hRv.leaf_live hwv hpP hpf hpu
  have hrun : run m (storeOps (Ty := Ty) pe m L ty (s.view c) a p) =
      m.write (leafAcc m L .write p) (pe.enc ad (some (anchorAlloc L (s.view c) a))) := by
    simp only [storeOps, had, writeOps, List.map_cons, List.map_nil, run, opEff]
  have hbytes : ∀ i, i < (L p).len →
      bytesOf (run m (storeOps (Ty := Ty) pe m L ty (s.view c) a p)) L p i =
      pe.enc ad (some (anchorAlloc L (s.view c) a)) i := fun i hi => by
    rw [hrun]; exact bytesOf_write ⟨pa, hpa, trivial⟩ hi
  have hy : ∃ y, (s.view c).A[a]? = some y ∧ y.active = true := by
    have h := hpre.derivedHeld
    unfold OptP at h
    split at h
    · exact ⟨_, ‹_›, h.1⟩
    · exact h.elim
  obtain ⟨y, hy, ya⟩ := hy
  have hafp : (s.view c).afp a = y.footprint := by simp [S3.afp, hy]
  refine ⟨?_, fun i hi => by rw [hbytes i hi]; exact henc.2 i, fun l hl => ?_, fun hz => ?_,
    fun hne => ?_⟩
  · rw [pe.reads _ _ fun i hi => hbytes i (hsz ▸ hi)]; exact henc.1
  · rw [hafp] at hl
    refine ⟨(anchorAlloc_eq hRv.layout hwv hy hl).symm, ?_⟩
    obtain ⟨hlP, hlf⟩ := hwv.footprints a y hy l hl
    obtain ⟨r, hr, hlr⟩ := exists_rootPlace hwv (l + 1) l (Nat.lt_succ_self l) hlP
    have hur : (s.view c).Usable r := Decidable.of_not_not fun hn =>
      hndv a y hy ya r hn l (mem_footprint.2 ⟨hlP, hlf, hlr⟩) hl
    exact hRv.leaf_live hwv hlP hlf
      (usable_of_partOf hwv (l + 1) l r (Nat.lt_succ_self l) hlr hur)
  · rw [← had]; unfold ptrAddr
    split
    · rename_i l0 ls hf
      have : l0 ∈ ((s.view c).afp a).filter (fun l => decide (0 < (L l).len)) := by
        rw [hf]; exact List.mem_cons_self ..
      have hpos := of_decide_eq_true (List.mem_filter.1 this).2
      rw [hz l0 (List.mem_filter.1 this).1] at hpos
      exact absurd hpos (Nat.lt_irrefl 0)
    · rfl
  · unfold ptrAddr at had
    split at had
    · rename_i l0 ls hf
      have hmem : ∀ x, x ∈ l0 :: ls → x ∈ (s.view c).afp a ∧ 0 < (L x).len := fun x hx => by
        rw [← hf] at hx; simpa using List.mem_filter.1 hx
      obtain ⟨hle0, hle⟩ := minOver_le (leafAddr m L) ls (leafAddr m L l0)
      have hlow : ∀ l' ∈ (s.view c).afp a, 0 < (L l').len → ad ≤ leafAddr m L l' := by
        intro l' hl' hpos
        have : l' ∈ l0 :: ls := by rw [← hf]; exact List.mem_filter.2 ⟨hl', by simpa using hpos⟩
        rw [← had]
        rcases List.mem_cons.1 this with rfl | h'
        · exact hle0
        · exact hle l' h'
      rcases minOver_mem (leafAddr m L) ls (leafAddr m L l0) with e | ⟨l', hl', e⟩
      · obtain ⟨h1, h2⟩ := hmem l0 (List.mem_cons_self ..)
        exact ⟨l0, h1, h2, by rw [← had, e], hlow⟩
      · obtain ⟨h1, h2⟩ := hmem l' (List.mem_cons_of_mem _ hl')
        exact ⟨l', h1, h2, by rw [← had, e], hlow⟩
    · rename_i hf
      obtain ⟨l, hl, hpos⟩ := hne
      have : l ∈ ((s.view c).afp a).filter (fun l => decide (0 < (L l).len)) :=
        List.mem_filter.2 ⟨hl, by simpa using hpos⟩
      rw [hf] at this; cases this

/-- Pointer soundness of the block stored by `issue` executed by `c` (Spec 1 §77, Part XIV,
§82.2, §82.3, §82.7; WC4 C2, C25), at the grain of abstract steps: the realization of an `ok`
`issue` of a registered entry is the `store` of the block, of identity `|A|`, into the
destination on the state `t` after `split` of `internal` on the region (`realize_issue`), and the
conclusions of `pointer_sound_storeC` hold on `t`. -/
theorem issue_pointer_soundC {Ty : Type} {k : K} {ty : Nat → Ty} {pe : PtrEnc} {L : Layout}
    {rtok : Nat → Nat} {s : SC} {ar : ArenaReg} {st' : SC × ArenaReg} {m : Machine.State}
    {c i dst ad : Nat} {region : List Nat} {E : Arena.ArenaEntry}
    (hR : ReprC L rtok s m) (hfr : FramesC s) (hw : WF3 s.flat) (hnd : NoDangling s.flat)
    (h : IssueStepC k s ar c i region dst (.ok st')) (hE : ar[i]? = some E)
    (had : ptrAddr m L (splitEff (s.view c) E.internal [region]) s.A.length = ad)
    (hsz : (L dst).len = pe.size)
    (henc : PtrEncAt pe ad
      (some (anchorAlloc L (splitEff (s.view c) E.internal [region]) s.A.length))) :
    let t := splitEff (s.view c) E.internal [region]
    pe.decode (bytesOf (run m (storeOps (Ty := Ty) pe m L ty t s.A.length dst)) L dst) = ad ∧
      (∀ i, i < (L dst).len →
        (bytesOf (run m (storeOps (Ty := Ty) pe m L ty t s.A.length dst)) L dst i).2 =
          some (anchorAlloc L t s.A.length)) ∧
      (∀ l ∈ t.afp s.A.length, (L l).alloc = anchorAlloc L t s.A.length ∧
        AllocP m (L l).alloc fun al => al.live = true ∧ (L l).off + (L l).len ≤ al.size) ∧
      ((∀ l ∈ t.afp s.A.length, (L l).len = 0) → ad = baseOf m (anchorAlloc L t s.A.length)) ∧
      ((∃ l ∈ t.afp s.A.length, 0 < (L l).len) → ∃ l ∈ t.afp s.A.length, 0 < (L l).len ∧
        ad = leafAddr m L l ∧ ∀ l' ∈ t.afp s.A.length, 0 < (L l').len → ad ≤ leafAddr m L l') := by
  intro t
  obtain ⟨E', s₁, hE', -, -, hsp, hsto, -⟩ := issueStepC_ok h
  rw [hE] at hE'; cases hE'
  obtain ⟨t₁, hR₁, rfl⟩ := viewStep_ok hsp
  have hR₁' : SplitStep k E.internal [region] (s.view c) (.ok t₁) := hR₁
  have hwt := split_preserves_wf3 (SC.wf3_view hfr hw) hR₁'
  have hndt := split_preserves_noDangling
    (noDangling_mem_congr (F' := (s.view c).F) hnd fun _ => SC.mem_view_F) hR₁'
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hR₁'
  have hv : (s.set t).view c = t := SC.view_set rfl
  have hfr₁ : FramesC (s.set t) := framesC_set rfl hfr
  have hw₁ : WF3 (s.set t).flat := SC.wf3_flat_of_view (c := c) (by rw [hv]; exact hwt) hfr.nodup
  have hnd₁ : NoDangling (s.set t).flat :=
    noDangling_mem_congr (t := (s.set t).view c) (F' := s.frames) (by rw [hv]; exact hndt)
      fun _ => SC.mem_view_F.symm
  have := pointer_sound_storeC (ty := ty) (ad := ad) (hR := reprC_set_same rfl rfl rfl hR) hfr₁ hw₁
    hnd₁ hsto (by rw [hv]; exact had) hsz (by rw [hv]; exact henc)
  rw [hv] at this
  exact this

/-! ## §82.6: pinned addresses -/

/-- The transfer phases of the by-value composite deallocate nothing (Spec 1 §63, §82.2). -/
theorem valOps_noDealloc {Ty : Type} (π : Refinement.Params Ty) (c : Nat) :
    ∀ (t : SC) (vs : List (Nat × Nat)) (m : Machine.State), ∀ o ∈ valOps π c t vs m, NoDealloc o
  | _, [], _ => fun _ h => nomatch h
  | t, v :: vs, m => fun o ho => by
    simp only [valOps] at ho
    rcases List.mem_append.1 ho with ho | ho
    · exact copyOps_noDealloc _ _ _ _ o ho
    · exact valOps_noDealloc π c _ vs _ o ho

/-- The deallocations of the exit of the current frame of `t` (Spec 1 §73, §82.5) keep the
allocation of a leaf that is pinned, when no leaf of a place dying with the frame is pinned
(Spec 1 §73.3): the `exit` case of `Refinement.pinned_address_stable`, which reads §73.1 (a
current frame) and §73.3 only. -/
theorem exit_keeps_pinned {Ty : Type} {k : K} {π : Refinement.Params Ty} {t : S3}
    {m : Machine.State} (hR : Refinement.Repr π.L π.rtok t m) (hw : WF3 t) (hF : t.F ≠ [])
    {l : Nat} (hl : l < t.P.length) (hlf : isLeaf t.P l)
    (hpinned : ¬ (t.pin l = false ∧ ¬ k.Pinned l))
    (hnp : ∀ q ∈ List.range t.P.length, t.Usable q → ¬ ({ t with F := t.F.tail } : S3).Usable q →
      ∀ l ∈ footprint t.P q, t.pin l = false ∧ ¬ k.Pinned l)
    (hlive : LiveAlloc m (π.L l).alloc) :
    LiveAlloc (run m (exitOps (Ty := Ty) π.L π.rtok t)) (π.L l).alloc := by
  have hpw : (exitRoots t).Pairwise (fun r r' => (π.L r).alloc ≠ (π.L r').alloc) :=
    ((range_pairwise _).filter _).imp_of_mem fun {r r'} hr hr' hlt =>
      hR.inj r r' (mem_exitRoots.1 hr).1 (mem_exitRoots.1 hr').1 (Nat.ne_of_lt hlt)
  have hlv : ∀ r ∈ exitRoots t, AllocP m (π.L r).alloc
      fun a => a.live = true ∧ a.freeAuth = some (π.rtok r) := fun r hr =>
    (hR.live r (mem_exitRoots.1 hr).1 (exitRoots_dies hw hF hr).1).and
      (hR.tokens r (mem_exitRoots.1 hr).1)
  obtain ⟨-, hkeep, -⟩ := deallocOps_run (Ty := Ty) (C := fun _ _ => True)
    (ObR := ⟨fun _ _ _ => True, fun _ _ _ => True⟩)
    (ObW := ⟨fun _ _ _ _ => True, fun _ _ _ _ => True⟩) (fun _ => trivial) _ m hpw hlv
  obtain ⟨a, ha, hla⟩ := hlive
  refine ⟨a, ?_, hla⟩
  change (run m (deallocOps (Ty := Ty) π.L π.rtok (exitRoots t))).allocs _ = _
  rw [hkeep _ fun r hr e => hpinned ?_, ha]
  obtain ⟨hdu, hdn⟩ := exitRoots_dies hw hF hr
  have hfp := hR.leaf_of_alloc hw hl hlf (mem_exitRoots.1 hr).1 e.symm
  exact hnp r (List.mem_range.2 (mem_exitRoots.1 hr).1.1) hdu hdn l hfp

/-- **`pinned_address_stable` under `ReprC`** (Spec 1 §82.6, §74, §75; §63.5, §69.4, §70.4,
§73.3; WC4 C2, C7, C25), extension of R1 at the grain of abstract steps: for every labelled step
from a state satisfying `KInvCA`, a leaf covered by an active dynamic pinning obligation or pinned
by `K.Pinned`, whose allocation is live before the step, keeps a live allocation and the same
address after the raw operations realizing the step. -/
theorem pinned_address_stableC {Ty : Type} {k : K} {L : MutexLayout} {π : Refinement.Params Ty}
    {w : Nat → Nat → UInt8 × Option Nat} {lbl : Label} {st st' : SC × SyncReg × ArenaReg}
    {m : Machine.State} (hR : ReprC π.L π.rtok st.1 m) (hk : KInvCA st.1)
    (h : LStep k L lbl st st') {l : Nat} (hl : l < st.1.P.length) (hlf : isLeaf st.1.P l)
    (hpin : (∃ (o : Nat) (ob : PinOb), st.1.pins[o]? = some ob ∧ ob.active = true ∧
      l ∈ ob.leaves) ∨ k.Pinned l)
    (hlive : LiveAlloc m (π.L l).alloc) :
    LiveAlloc (run m (realize π w lbl st.1 st.2.2 m)) (π.L l).alloc ∧
      leafAddr (run m (realize π w lbl st.1 st.2.2 m)) π.L l = leafAddr m π.L l := by
  have hwf := hR.adm.wf
  refine ⟨?_, by simp only [leafAddr]; rw [baseOf_run hwf _ (hlive.mono fun _ _ => trivial)]⟩
  have hnod : ∀ ops : List (Machine.Op Ty), (∀ o ∈ ops, NoDealloc o) →
      LiveAlloc (run m ops) (π.L l).alloc := fun ops hn => live_run _ _ hwf hn hlive
  have hpinned : ∀ c, ¬ ((st.1.view c).pin l = false ∧ ¬ k.Pinned l) := fun c ⟨h1, h2⟩ => by
    rcases hpin with h | h
    · rw [S3.pin_iff.2 h] at h1; cases h1
    · exact h2 h
  cases h with
  | @kernel s s' reg ar c op h =>
    have hpv := view_facts hk c
    cases op
    case transfer => exact hnod _ (copyOps_noDealloc _ _ _ _)
    case store => exact hnod _ (writeOps_noDealloc _ _ _ _ _)
    case enter => exact hnod _ (allocOps_noDealloc _ _ _ _ _ _)
    case depend => exact hnod _ fun _ h => nomatch h
    case exit =>
      obtain ⟨-, h⟩ := h; obtain ⟨hpre, -⟩ := Guarded.ok_iff.1 h
      have hFv : (s.view c).F ≠ [] := by
        intro he
        have hc : s.stk c ≠ [] := fun e => hpre.hasCaller (by rw [e]; rfl)
        obtain ⟨f, hf⟩ := List.exists_mem_of_ne_nil _ hc
        have := (SC.mem_view_F (c := c)).2 (SC.mem_frames_of hf)
        rw [he] at this; cases this
      exact exit_keeps_pinned ((reprC_view c).1 hR) hpv.1 hFv hl hlf (hpinned c) hpre.notPinned
        hlive
    all_goals
      obtain ⟨t, hRt, -⟩ := viewStep_ok h
      exact (pinned_address_stable ((reprC_view c).1 hR) hpv.1 hpv.2.2.1
        ((opStep_kopOf (w := w)).2 hRt) hl hlf hpin hlive).1
  | spawn h => exact hnod _ (allocOps_noDealloc _ _ _ _ _ _)
  | spawnVal h =>
    exact hnod _ fun o ho => (List.mem_append.1 ho).elim (allocOps_noDealloc _ _ _ _ _ _ o)
      (valOps_noDealloc π _ _ _ _ o)
  | @terminate s s' reg ar c h =>
    obtain ⟨-, h⟩ := h; obtain ⟨hpre, -⟩ := Guarded.ok_iff.1 h
    have hFv : (s.view c).F ≠ [] := by
      intro he
      have hc : s.stk c ≠ [] := fun e => by have := hpre.initialOnly; rw [e] at this; cases this
      obtain ⟨f, hf⟩ := List.exists_mem_of_ne_nil _ hc
      have := (SC.mem_view_F (c := c)).2 (SC.mem_frames_of hf)
      rw [he] at this; cases this
    exact exit_keeps_pinned ((reprC_view c).1 hR) (view_facts hk c).1 hFv hl hlf (hpinned c)
      hpre.notPinned hlive
  | @issue s reg ar c i region dst st' h =>
    obtain ⟨E, s₁, hE, -⟩ := issueStepC_ok h
    show LiveAlloc (run m (realize π w (.issue c i region dst) s ar m)) _
    rw [realize_issue π w hE]
    exact hnod _ (writeOps_noDealloc _ _ _ _ _)
  | @reset s reg ar c i st' h =>
    show LiveAlloc (run m (realize π w (.reset c i) s ar m)) _
    rw [(realize_arena_nil π w s ar m c 0 i).2]; exact hlive
  | join => exact hlive
  | deriveSync => exact hlive
  | newMutex => exact hlive
  | acquire => exact hlive
  | unlock => exact hlive
  | resetLock => exact hlive
  | newArena => exact hlive

end Ern.Concurrency
