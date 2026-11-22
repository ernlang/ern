import Ern.ConcurrencyModel.RunRefinement

/-!
# Theorem 9f: state results of the refinement on the reached concurrent states (Spec 1 §82)

The state results of `Ern.MemoryModel.Refinement` and `Ern.MemoryModel.RefinementArena`, as
corollaries on every state reached by a translated run (`TransRun`), at the grain of abstract steps
(contexts interleave at the grain of abstract steps):

* exclusive bytes (`exclusive_bytes`, Spec 1 §82.8) and declared disjointness
  (`declaredDisjoint_bytes`, §82.1);
* no active authority designates dead storage; every anchor of a usable place is active and
  covers live storage (`r4_no_dead_cover`, `r4_anchors`, §82.5);
* deallocation (`deallocable_sound`, `freeSound_derived`, §82.4);
* pointers written by `store` and by `issue` (`pointer_sound_store`, `issue_pointer_sound`,
  §82.3);
* pinned addresses: the address of a pinned place is unchanged by the raw operations of every step,
  whatever the context that executes it (`pinned_address_stable`, §82.6).

The proofs of the memory model read the preconditions of `store` (§65.1, §65.2) and of
`exitFrame` (§73.1, §73.3) only; the copies below read the same clauses of their re-indexed forms
(`StorePreC`, `ExitPreC`, `TermPre`). They say nothing of the physical accesses that are not
modelled (`OB-C05`, `OB-C12` concrete part, `OB-C20`).
-/

namespace Ern.ConcurrencyModel

open Ern.MemoryModel Ern.MemoryModel.Access Ern.MemoryModel.Refinement
open PreservationAux

section Reached

variable {Ty : Type} {ks : KShared} {ML : MutexLayout} {C : Nat → Nat → Prop}
  {ObR : Machine.ReadOblSpec Ty} {ObW : Machine.WriteOblSpec Ty} {statics : Statics}
  {π : Params Ty} {tr : List (Label × WriteRepr)} {ops : List (Machine.Op Ty)}
  {st : SC × SyncReg × ArenaReg} {m : Machine.State}

/-- **Theorem 9f**, exclusive bytes (Spec 1 §82.8, §50, §23): on a state reached by a translated
run, under `DDSound(K)` (§80) and `ParamsOK`, if authority `a` has the effective mode `Modify` on
leaf `l`, no other authority has an effective mode on a leaf `l'` whose range overlaps the range
of `l` in the same allocation. -/
theorem reached_exclusive_bytes (hdd : DDSound ks.toK) (hπ : ParamsOK C π)
    (h : TransRun ks ML C ObR ObW statics π tr ops st m) {a b l l' : Nat}
    (hl : l < st.1.P.length) (hlf : isLeaf st.1.P l) (hl' : l' < st.1.P.length)
    (hlf' : isLeaf st.1.P l') (ha : effective st.1.flat a l = some .modify) (hab : a ≠ b)
    (hsame : (π.L l).alloc = (π.L l').alloc)
    (hover : ¬ Machine.RangeDisjoint (π.L l).off (π.L l).len (π.L l').off (π.L l').len) :
    effective st.1.flat b l' = none :=
  exclusive_bytes (refinement_run hdd hπ h).2.1.layout (TransRun.kInvCA hdd hπ h).1.2.1.1.1
    hl hlf hl' hlf' ha hab hsame hover

/-- **Theorem 9f**, declared disjointness (Spec 1 §82.1, §23, §80 `DDSound`): on a state reached
by a translated run, two regions of leaves declared disjoint have disjoint bytes. -/
theorem reached_declaredDisjoint_bytes (hdd : DDSound ks.toK) (hπ : ParamsOK C π)
    (h : TransRun ks ML C ObR ObW statics π tr ops st m) {r r' : List Nat}
    (hdecl : ks.toK.DeclaredDisjoint r r') (hr : ∀ l ∈ r, l < st.1.P.length ∧ isLeaf st.1.P l)
    (hr' : ∀ l ∈ r', l < st.1.P.length ∧ isLeaf st.1.P l) : ByteDisjoint π.L r r' :=
  declaredDisjoint_bytes (s3 := st.1.flat) hdd (refinement_run hdd hπ h).2.1.layout hdecl hr hr'

/-- **Theorem 9f**, lifetimes (Spec 1 §82.5, §54): on a state reached by a translated run, every
leaf covered by an active authority is an existing leaf whose allocation is live and contains its
range: no active authority designates dead storage. -/
theorem reached_no_dead_cover (hdd : DDSound ks.toK) (hπ : ParamsOK C π)
    (h : TransRun ks ML C ObR ObW statics π tr ops st m) {j : Nat} {y : Authority}
    (hy : st.1.A[j]? = some y) (ya : y.active = true) {l : Nat} (hl : l ∈ y.footprint) :
    l < st.1.P.length ∧ isLeaf st.1.P l ∧
      AllocP m (π.L l).alloc fun a => a.live = true ∧ (π.L l).off + (π.L l).len ≤ a.size :=
  have hk := TransRun.kInvCA hdd hπ h
  r4_no_dead_cover (s3 := st.1.flat) (refinement_run hdd hπ h).2.1 hk.1.1.2 hk.1.2.1.2.2 hy ya hl

/-- **Theorem 9f**, dependencies and storage (Spec 1 §82.5, §52, §44): on a state reached by a
translated run, every anchor of a usable place is active, and every leaf it covers has a live
allocation containing its range. -/
theorem reached_anchors (hdd : DDSound ks.toK) (hπ : ParamsOK C π)
    (h : TransRun ks ML C ObR ObW statics π tr ops st m) {q x : Nat} (hq : st.1.flat.Usable q)
    (hx : x ∈ st.1.D q) :
    st.1.flat.Active x ∧ ∀ l ∈ st.1.flat.afp x,
      AllocP m (π.L l).alloc fun a => a.live = true ∧ (π.L l).off + (π.L l).len ≤ a.size :=
  have hk := TransRun.kInvCA hdd hπ h
  r4_anchors (s3 := st.1.flat) (refinement_run hdd hπ h).2.1 hk.1.1.2 hk.1.2.1.1.2.2.1
    hk.1.2.1.2.2 hq hx

/-- **Theorem 9f**, `Deallocable` (Spec 1 §82.4, §80, §70.2, §17.1): on a state reached by a
translated run, the allocation of every root place is registered and records a deallocation
token. -/
theorem reached_deallocable (hdd : DDSound ks.toK) (hπ : ParamsOK C π)
    (h : TransRun ks ML C ObR ObW statics π tr ops st m) {p : Nat} (hp : RootPlace st.1.P p) :
    AllocP m (π.L p).alloc fun a => ∃ d, a.freeAuth = some d :=
  deallocable_sound (s3 := st.1.flat) (refinement_run hdd hπ h).2.1 hp

/-- **Theorem 9f**, `freeSound_derived` (Spec 1 §82.4, §70.2, §17, §80): on a state reached by a
translated run, for an `ok` `free(place, auth)` executed by any context `c`, when `K.FreeCompat`
is instantiated by `FreeCompatInst`, the raw deallocation has the conditions of §17. -/
theorem reached_freeSound (hdd : DDSound ks.toK) (hπ : ParamsOK C π)
    (h : TransRun ks ML C ObR ObW statics π tr ops st m) {c p auth : Nat} {s' : SC}
    (hf : opStepC ks.toK (.free p auth) c st.1 (.ok s'))
    (hinst : ks.toK.FreeCompat p auth → FreeCompatInst C π.rtok p auth) :
    Machine.CanDealloc C m (π.L p).alloc auth := by
  have hk := TransRun.kInvCA hdd hπ h
  have hc : st.1.Live c := opStepC_live hf
  obtain ⟨hw, -, hnd, -⟩ := view_facts hk hc
  obtain ⟨t, hst, -⟩ := viewStep_ok hf
  have hst' : FreeStep ks.toK p auth (st.1.view c) (.ok t) := hst
  exact freeSound_derived ((reprC_view hc).1 (refinement_run hdd hπ h).2.1) hw hnd
    (Guarded.ok_iff.1 hst').1 hinst

end Reached

/-! ## Pointers written by `store` and `issue` (Spec 1 §82.2, §82.3, §77) -/

/-- Pointer soundness of `store` executed by `c` (Spec 1 §82.2 pointer validity and its last
sentence, §82.3; C2), at the grain of abstract steps: under `ReprC`, `FramesC`, `WF3` and
`NoDangling` of the globally live frames, an `ok` step of
`store(authority, target)` executed by `c` whose reference has the address `ad` (`ptrAddr` on the
view of `c`), with a target of pointer size and the obligation of the encoding for that reference:
the conclusions of `Refinement.pointer_sound_store` on the view of `c`. The proof is that of
`Refinement.pointer_sound_store`, which reads §65.1 (the authority is active) and §65.2 (the target
is a usable leaf) only. -/
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
  obtain ⟨hpre, -⟩ := Guarded.ok_iff.1 h
  have hc : s.Live c := opStepC_live h
  have hRv := (reprC_view hc).1 hR
  have hwv : WF3 (s.view c) := SC.wf3_view hfr hw hc
  have hndv : NoDangling (s.view c) := noDangling_mem_congr hnd fun _ => SC.mem_view_F hc
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

/-- **Theorem 9f**, pointers written by `store` (Spec 1 §82.2, §82.3): on a state reached by a
translated run, under `DDSound(K)` and `ParamsOK`, the conclusions of `pointer_sound_storeC` for
an `ok` `store` executed by any context. -/
theorem reached_pointer_sound_store {Ty : Type} {ks : KShared} {ML : MutexLayout}
    {C : Nat → Nat → Prop} {ObR : Machine.ReadOblSpec Ty} {ObW : Machine.WriteOblSpec Ty}
    {statics : Statics} {π : Params Ty} {tr : List (Label × WriteRepr)}
    {ops : List (Machine.Op Ty)} {st : SC × SyncReg × ArenaReg} {m : Machine.State}
    (hdd : DDSound ks.toK) (hπ : ParamsOK C π) (h : TransRun ks ML C ObR ObW statics π tr ops st m)
    {s' : SC} {c a p ad : Nat} (hs : opStepC ks.toK (.store a p) c st.1 (.ok s'))
    (had : ptrAddr m π.L (st.1.view c) a = ad) (hsz : (π.L p).len = π.pe.size)
    (henc : PtrEncAt π.pe ad (some (anchorAlloc π.L (st.1.view c) a))) :
    π.pe.decode (bytesOf (run m (storeOps π.pe m π.L π.ty (st.1.view c) a p)) π.L p) = ad ∧
      (∀ i, i < (π.L p).len →
        (bytesOf (run m (storeOps π.pe m π.L π.ty (st.1.view c) a p)) π.L p i).2 =
          some (anchorAlloc π.L (st.1.view c) a)) ∧
      (∀ l ∈ (st.1.view c).afp a, (π.L l).alloc = anchorAlloc π.L (st.1.view c) a ∧
        AllocP m (π.L l).alloc fun al => al.live = true ∧ (π.L l).off + (π.L l).len ≤ al.size) ∧
      ((∀ l ∈ (st.1.view c).afp a, (π.L l).len = 0) →
        ad = baseOf m (anchorAlloc π.L (st.1.view c) a)) ∧
      ((∃ l ∈ (st.1.view c).afp a, 0 < (π.L l).len) → ∃ l ∈ (st.1.view c).afp a,
        0 < (π.L l).len ∧ ad = leafAddr m π.L l ∧
          ∀ l' ∈ (st.1.view c).afp a, 0 < (π.L l').len → ad ≤ leafAddr m π.L l') :=
  have hk := TransRun.kInvCA hdd hπ h
  pointer_sound_storeC (ty := π.ty) (refinement_run hdd hπ h).2.1 hk.1.1.1 hk.1.1.2
    hk.1.2.1.2.2 hs had hsz henc

/-- Pointer soundness of the block stored by `issue` executed by `c` (Spec 1 §77, Part XIV, §82.2,
§82.3, §82.7; C2), at the grain of abstract steps: the raw operations of an `ok` `issue` of a
registered entry are the `store` of the block, of identity `|A|`, into the destination on the state
`t` after `split` of `internal` on the region (`rawOps_issue`), and the conclusions of
`pointer_sound_storeC` hold on `t`, the leaves covered by the block being those of the region
(`RefinementArena.issue_pointer_sound`). -/
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
      (∀ l ∈ region, (L l).alloc = anchorAlloc L t s.A.length ∧
        AllocP m (L l).alloc fun al => al.live = true ∧ (L l).off + (L l).len ≤ al.size) ∧
      ((∀ l ∈ region, (L l).len = 0) → ad = baseOf m (anchorAlloc L t s.A.length)) ∧
      ((∃ l ∈ region, 0 < (L l).len) → ∃ l ∈ region, 0 < (L l).len ∧
        ad = leafAddr m L l ∧ ∀ l' ∈ region, 0 < (L l').len → ad ≤ leafAddr m L l') := by
  intro t
  obtain ⟨E', s₁, hE', -, -, hsp, hsto, -⟩ := issueStepC_ok h
  rw [hE] at hE'; cases hE'
  have hc : s.Live c := opStepC_live hsp
  obtain ⟨t₁, hR₁, rfl⟩ := viewStep_ok hsp
  have hR₁' : SplitStep k E.internal [region] (s.view c) (.ok t₁) := hR₁
  have hwt := split_preserves_wf3 (SC.wf3_view hfr hw hc) hR₁'
  have hndt := split_preserves_noDangling
    (noDangling_mem_congr (F' := (s.view c).F) hnd fun _ => SC.mem_view_F hc) hR₁'
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hR₁'
  have hv : (s.set t).view c = t := SC.view_set hc rfl
  have hc₁ : (s.set t).Live c := hc
  have hfr₁ : FramesC (s.set t) := framesC_set hfr rfl
  have hw₁ : WF3 (s.set t).flat := SC.wf3_flat_of_view (c := c) (by rw [hv]; exact hwt) hfr.nodup
  have hnd₁ : NoDangling (s.set t).flat :=
    noDangling_mem_congr (t := (s.set t).view c) (F' := s.frames) (by rw [hv]; exact hndt)
      fun _ => (SC.mem_view_F hc₁).symm
  have := pointer_sound_storeC (ty := ty) (ad := ad) (reprC_set_same rfl rfl rfl hR) hfr₁ hw₁
    hnd₁ hsto (by rw [hv]; exact had) hsz (by rw [hv]; exact henc)
  rw [hv] at this
  have hafp : t.afp s.A.length = region := by
    show (splitEff (s.view c) E.internal [region]).afp (s.view c).A.length = region
    simp [S3.afp, Arena.split_block]
  rw [hafp] at this
  exact this

/-- **Theorem 9f**, pointers written by `issue` (Spec 1 §77, §82.2, §82.3, §82.7): on a state
reached by a translated run, under `DDSound(K)` and `ParamsOK`, the conclusions of
`issue_pointer_soundC` for an `ok` `issue` executed by any context. -/
theorem reached_issue_pointer_sound {Ty : Type} {ks : KShared} {ML : MutexLayout}
    {C : Nat → Nat → Prop} {ObR : Machine.ReadOblSpec Ty} {ObW : Machine.WriteOblSpec Ty}
    {statics : Statics} {π : Params Ty} {tr : List (Label × WriteRepr)}
    {ops : List (Machine.Op Ty)} {st : SC × SyncReg × ArenaReg} {m : Machine.State}
    (hdd : DDSound ks.toK) (hπ : ParamsOK C π) (h : TransRun ks ML C ObR ObW statics π tr ops st m)
    {st' : SC × ArenaReg} {c i dst ad : Nat} {region : List Nat} {E : Arena.ArenaEntry}
    (hi : IssueStepC ks.toK st.1 st.2.2 c i region dst (.ok st')) (hE : st.2.2[i]? = some E)
    (had : ptrAddr m π.L (splitEff (st.1.view c) E.internal [region]) st.1.A.length = ad)
    (hsz : (π.L dst).len = π.pe.size)
    (henc : PtrEncAt π.pe ad
      (some (anchorAlloc π.L (splitEff (st.1.view c) E.internal [region]) st.1.A.length))) :
    let t := splitEff (st.1.view c) E.internal [region]
    π.pe.decode (bytesOf (run m (storeOps π.pe m π.L π.ty t st.1.A.length dst)) π.L dst) = ad ∧
      (∀ i, i < (π.L dst).len →
        (bytesOf (run m (storeOps π.pe m π.L π.ty t st.1.A.length dst)) π.L dst i).2 =
          some (anchorAlloc π.L t st.1.A.length)) ∧
      (∀ l ∈ region, (π.L l).alloc = anchorAlloc π.L t st.1.A.length ∧
        AllocP m (π.L l).alloc fun al => al.live = true ∧ (π.L l).off + (π.L l).len ≤ al.size) ∧
      ((∀ l ∈ region, (π.L l).len = 0) → ad = baseOf m (anchorAlloc π.L t st.1.A.length)) ∧
      ((∃ l ∈ region, 0 < (π.L l).len) → ∃ l ∈ region, 0 < (π.L l).len ∧
        ad = leafAddr m π.L l ∧ ∀ l' ∈ region, 0 < (π.L l').len → ad ≤ leafAddr m π.L l') :=
  have hk := TransRun.kInvCA hdd hπ h
  issue_pointer_soundC (ty := π.ty) (refinement_run hdd hπ h).2.1 hk.1.1.1 hk.1.1.2 hk.1.2.1.2.2
    hi hE had hsz henc

/-! ## Pinned addresses (Spec 1 §82.6, §74, §75; §63.5, §69.4, §70.4, §73.3) -/

/-- The raw reads deallocate nothing (Spec 1 §15, §20.2). -/
theorem readOps_noDealloc {Ty : Type} (s2 : Machine.State) (L : Layout) (ty : Nat → Ty)
    (ls : List Nat) : ∀ o ∈ readOps s2 L ty ls, NoDealloc o := by
  intro o ho
  obtain ⟨l, -, rfl⟩ := List.mem_map.1 ho
  trivial

/-- The transfer phases of the by-value composite deallocate nothing (Spec 1 §63, §82.2). -/
theorem valOps_noDealloc {Ty : Type} (π : Params Ty) (c : Nat) :
    ∀ (t : SC) (vs : List (Nat × Nat)) (m : Machine.State), ∀ o ∈ valOps π c t vs m, NoDealloc o
  | _, [], _ => fun _ h => nomatch h
  | t, v :: vs, m => fun o ho => by
    simp only [valOps] at ho
    rcases List.mem_append.1 ho with ho | ho
    · exact copyOps_noDealloc _ _ _ _ o ho
    · exact valOps_noDealloc π c _ vs _ o ho

/-- The deallocations of the exit of the current frame of `t` (Spec 1 §73, §82.5) keep the
allocation of a pinned leaf, when no leaf of a place dying with the frame is pinned (§73.3): the
`exit` case of `Refinement.pinned_address_stable`, which reads §73.1 (a current frame) and §73.3
only. -/
theorem exit_keeps_pinned {Ty : Type} {k : K} {π : Params Ty} {t : S3}
    {m : Machine.State} (hR : Repr π.L π.rtok t m) (hw : WF3 t) (hF : t.F ≠ [])
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

/-- `pinned_address_stable` for every labelled step (Spec 1 §82.6, §74, §75; §63.5, §69.4, §70.4,
§73.3; C2, C7), at the grain of abstract steps: from a state satisfying `ReprC` and `KInvCA`, a
leaf covered by an active dynamic pinning obligation or pinned by `K.Pinned`, whose allocation is
live before the step, keeps a live allocation and the same address after the raw operations of
the step, whatever the context that executes it. -/
theorem pinned_address_stableC {Ty : Type} {ks : KShared} {ML : MutexLayout} {π : Params Ty}
    {w : WriteRepr} {lbl : Label} {st st' : SC × SyncReg × ArenaReg} {m : Machine.State}
    (hR : ReprC π.L π.rtok st.1 m) (hk : KInvCA st.1) (h : LStep ks ML lbl st st') {l : Nat}
    (hl : l < st.1.P.length) (hlf : isLeaf st.1.P l)
    (hpin : (∃ (o : Nat) (ob : PinOb), st.1.pins[o]? = some ob ∧ ob.active = true ∧
      l ∈ ob.leaves) ∨ ks.toK.Pinned l)
    (hlive : LiveAlloc m (π.L l).alloc) :
    LiveAlloc (run m (rawOps π w lbl st m)) (π.L l).alloc ∧
      leafAddr (run m (rawOps π w lbl st m)) π.L l = leafAddr m π.L l := by
  have hwf := hR.adm.wf
  refine ⟨?_, by simp only [leafAddr]; rw [baseOf_run hwf _ (hlive.mono fun _ _ => trivial)]⟩
  have hnod : ∀ ops : List (Machine.Op Ty), (∀ o ∈ ops, NoDealloc o) →
      LiveAlloc (run m ops) (π.L l).alloc := fun ops hn => live_run _ _ hwf hn hlive
  have hpinned : ∀ c, ¬ ((st.1.view c).pin l = false ∧ ¬ ks.toK.Pinned l) := fun c ⟨h1, h2⟩ => by
    rcases hpin with h | h
    · rw [S3.pin_iff.2 h] at h1; cases h1
    · exact h2 h
  cases h with
  | @kernel s s' reg ar c op h =>
    have hc : s.Live c := opStepC_live h
    have hpv := view_facts hk hc
    cases op
    case transfer => exact hnod _ (copyOps_noDealloc _ _ _ _)
    case store => exact hnod _ (writeOps_noDealloc _ _ _ _ _)
    case enter => exact hnod _ (allocOps_noDealloc _ _ _ _ _ _)
    case depend => exact hnod _ fun _ h => nomatch h
    case exit =>
      obtain ⟨hpre, -⟩ := Guarded.ok_iff.1 h
      have hs : s.stk c ≠ [] := fun e => hpre.hasCaller (by rw [e]; rfl)
      exact exit_keeps_pinned ((reprC_view hc).1 hR) hpv.1 (view_F_ne hs) hl hlf (hpinned c)
        hpre.notPinned hlive
    all_goals
      obtain ⟨t, hRt, -⟩ := viewStep_ok h
      exact (pinned_address_stable ((reprC_view hc).1 hR) hpv.1 hpv.2.2.1
        ((opStep_kopOf (w := w)).2 hRt) hl hlf hpin hlive).1
  | spawn h => exact hnod _ (allocOps_noDealloc _ _ _ _ _ _)
  | spawnVal h =>
    exact hnod _ fun o ho => (List.mem_append.1 ho).elim (allocOps_noDealloc _ _ _ _ _ _ o)
      (valOps_noDealloc π _ _ _ _ o)
  | @terminate s s' reg ar c h =>
    obtain ⟨hpre, -⟩ := Guarded.ok_iff.1 h
    have hs : s.stk c ≠ [] := fun e => by have := hpre.initialOnly; rw [e] at this; cases this
    exact exit_keeps_pinned ((reprC_view (SC.live_of_stk hs)).1 hR)
      (view_facts hk (SC.live_of_stk hs)).1 (view_F_ne hs) hl hlf (hpinned c) hpre.notPinned
      hlive
  | @issue s reg ar c i region dst st' h =>
    obtain ⟨E, s₁, hE, -⟩ := issueStepC_ok h
    rw [rawOps_issue π w (st := (s, reg, ar)) hE]
    exact hnod _ (writeOps_noDealloc _ _ _ _ _)
  | @reset s reg ar c i st' h =>
    rw [(rawOps_arena_nil π w (s, reg, ar) m c 0 0 i).2]; exact hlive
  | @newArena s reg ar c st₀ i st' h =>
    rw [(rawOps_arena_nil π w (s, reg, ar) m c st₀ i 0).1]; exact hlive
  | readShared => exact hnod _ (readOps_noDealloc _ _ _ _)
  | @writeShared s s' reg ar c a region order kind h =>
    cases kind with
    | store => exact hnod _ (writeOps_noDealloc _ _ _ _ _)
    | rmw v =>
      exact hnod _ fun o ho => (List.mem_append.1 ho).elim (readOps_noDealloc _ _ _ _ o)
        (writeOps_noDealloc _ _ _ _ _ o)
  | @cas s s' reg ar c a l' succ fail br h =>
    cases br with
    | success v =>
      exact hnod _ fun o ho => (List.mem_append.1 ho).elim (readOps_noDealloc _ _ _ _ o)
        (writeOps_noDealloc _ _ _ _ _ o)
    | failure v => exact hnod _ (readOps_noDealloc _ _ _ _)
  | join => exact hlive
  | deriveSync => exact hlive
  | newMutex => exact hlive
  | acquire => exact hlive
  | unlock => exact hlive
  | resetLock => exact hlive

/-- **Theorem 9f**, pinned addresses (Spec 1 §82.6, §74, §75): on a state reached by a translated
run, under `DDSound(K)` and `ParamsOK`, for every labelled step from it, whatever the context that
executes it, a pinned leaf whose allocation is live keeps a live allocation and the same address
after the raw operations of the step. -/
theorem reached_pinned_address_stable {Ty : Type} {ks : KShared} {ML : MutexLayout}
    {C : Nat → Nat → Prop} {ObR : Machine.ReadOblSpec Ty} {ObW : Machine.WriteOblSpec Ty}
    {statics : Statics} {π : Params Ty} {tr : List (Label × WriteRepr)}
    {ops : List (Machine.Op Ty)} {st st' : SC × SyncReg × ArenaReg} {m : Machine.State}
    (hdd : DDSound ks.toK) (hπ : ParamsOK C π) (h : TransRun ks ML C ObR ObW statics π tr ops st m)
    {w : WriteRepr} {lbl : Label} (hs : LStep ks ML lbl st st') {l : Nat}
    (hl : l < st.1.P.length) (hlf : isLeaf st.1.P l)
    (hpin : (∃ (o : Nat) (ob : PinOb), st.1.pins[o]? = some ob ∧ ob.active = true ∧
      l ∈ ob.leaves) ∨ ks.toK.Pinned l)
    (hlive : LiveAlloc m (π.L l).alloc) :
    LiveAlloc (run m (rawOps π w lbl st m)) (π.L l).alloc ∧
      leafAddr (run m (rawOps π w lbl st m)) π.L l = leafAddr m π.L l :=
  pinned_address_stableC (refinement_run hdd hπ h).2.1 (TransRun.kInvCA hdd hπ h) hs hl hlf hpin
    hlive

end Ern.ConcurrencyModel
