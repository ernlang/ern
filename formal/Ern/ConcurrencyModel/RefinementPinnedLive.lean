import Ern.ConcurrencyModel.RefinementState
import Ern.ConcurrencyModel.Reachable

/-!
# Theorem 9, pinned leaves on the reached states: liveness without hypothesis (Spec 1 §82.6, §57)

`Refinement.pinned_address_stable_reachable` concludes, with no liveness hypothesis, that a pinned
leaf of a reachable state has a live allocation before the step, keeps it after the raw operations
of the step, and keeps its address. It draws the liveness from `I5` (Spec 1 §57: every pinned leaf
belongs to a usable place). This module transports it, at the grain of abstract steps:

* `I5` on the global state (`SC.flat`: usable places range over the globally live frames, C2) is
  preserved by every labelled step (`lstep_i5`), from a state satisfying `KInvCA`, under
  `DDSound(K)`; it holds on every state reached from the initial state of Spec 1 §47
  (`reached_i5`). C20 requires every transition to preserve the applicable global invariants, and
  `I5` is one of them: Spec 1 §57 requires it on the reachable states. `lstep_i5`, `lrun_i5` and
  `reached_i5` therefore belong to the coverage of theorem 2 (module `Reachable`).
* `reached_pinned_address_live`: the conclusions of `pinned_address_stable_reachable` for every
  labelled step executed by any context, on every reached state.

The step cases read: §63.9 for `transfer` (`TransferPreC.dstUsableAfter`), §72.2 for the new locals
(`enterFrame`, `spawn`), §73.3 for the exit of a frame and for `terminate` (`notPinned`), the fresh
destinations of the by-value composite (C5 item 2), and the per-operation lemmas of the memory model
on the view of the executing context for the other inherited operations.
-/

namespace Ern.ConcurrencyModel

open Ern.MemoryModel Ern.MemoryModel.Access
open PreservationAux TransferPreserveAux

/-! ## `I5` and the components it reads (Spec 1 §57, §40, §74) -/

/-- `I5` (Spec 1 §57) reads the places, the death markers, the pinning obligations and the stack
only through membership (§40: usability). -/
theorem i5_congr {k : K} {t t' : S3} (h5 : I5 k t) (hP : t'.P = t.P) (hd : t'.dead = t.dead)
    (hpins : t'.pins = t.pins) (hF : ∀ f, f ∈ t'.F ↔ f ∈ t.F) : I5 k t' := by
  intro l hlt hleaf hl
  rw [hP] at hlt hleaf
  rw [S3.pin_congr hpins] at hl
  obtain ⟨q, hq, hlq⟩ := h5 l hlt hleaf hl
  exact ⟨q, S3.Usable.mono (s := t') (s' := t) hP.symm (fun f hf => (hF f).2 hf)
    (fun q h => by rw [hd]; exact h) hq, by rw [hP]; exact hlq⟩

/-- `I5` on the global state gives `I5` on the view of a live context (C2). -/
theorem i5_view {k : K} {s : SC} {c : Nat} (hc : s.Live c) (h5 : I5 k s.flat) :
    I5 k (s.view c) :=
  i5_congr h5 rfl rfl rfl fun _ => SC.mem_view_F hc

/-- `I5` after writing back kernel components `t` that list the globally live frames (C2). -/
theorem i5_set {k : K} {s : SC} {t : S3} (h5 : I5 k t) (hF : ∀ f, f ∈ t.F ↔ f ∈ s.frames) :
    I5 k (s.set t).flat :=
  i5_congr h5 rfl rfl rfl fun f => (hF f).symm

/-- `I5` after writing back kernel components with the same places, death markers and pinning
obligations (C2). -/
theorem i5_set_same {k : K} {s : SC} {t : S3} (h5 : I5 k s.flat) (hP : t.P = s.P)
    (hd : t.dead = s.dead) (hpins : t.pins = s.pins) : I5 k (s.set t).flat :=
  i5_congr h5 hP hd hpins fun _ => Iff.rfl

/-! ## The effects that change the places or the frames (Spec 1 §63, §72, §73) -/

/-- The effect of O4 keeps `I5` (Spec 1 §57; §63 effect, §63.9), from `WF3` (§49) and the usability
of the destination after the step: the proof of `transfer_preserves_i5`, which reads §63.9
only. -/
theorem transferEff_i5 {k : K} {t : S3} {src dst : Nat} (hw : WF3 t)
    (hd' : (transferEff t src dst).Usable dst) (h5 : I5 k t) : I5 k (transferEff t src dst) := by
  intro l hlt hleaf hl
  rw [transfer_len] at hlt
  replace hleaf : isLeaf t.P l := by simpa only [isLeaf, transfer_len, transfer_parentOf] using hleaf
  rw [S3.pin_congr (pins_transferEff t src dst)] at hl
  obtain ⟨q, hq, hlq⟩ := h5 l hlt hleaf hl
  exact ⟨q, transfer_usable_fwd hw hd' hq, by rw [transfer_footprint]; exact hlq⟩

/-- The effect of O6 keeps `I5` (Spec 1 §57; §72 effect), from §72.2 (the locals form a
well-formed shape): the proof of `enter_preserves_i5`, which reads §72.2 only. -/
theorem enterEff_i5 {k : K} {t : S3} {ps : List Nat} {ls : LocalShape}
    (hsh : ShapeOK t.P.length ls.toShape) (h5 : I5 k t) : I5 k (enterEff t ps ls) := by
  intro l hlt hleaf hl
  rw [S3.pin_congr (pins_enterEff t ps ls)] at hl
  by_cases hold : l < t.P.length
  · obtain ⟨q, hq, hlq⟩ := h5 l hold ((Frames.enter_isLeaf_old hsh hold).1 hleaf) hl
    exact ⟨q, Frames.enter_usable_old hq, (Frames.enter_footprint_old hsh hq.lt l).2 hlq⟩
  · have hlt' : l < t.P.length + ls.length := by rw [← Frames.enterP_len t ls]; exact hlt
    obtain ⟨i, rfl⟩ : ∃ i, l = t.P.length + i := ⟨l - t.P.length, by omega⟩
    exact ⟨t.P.length + i, Frames.enter_usable_new (by omega),
      mem_footprint.2 ⟨hlt, hleaf, hlt, .inl rfl⟩⟩

/-- The effect of O7 keeps `I5` (Spec 1 §57; §73.3, §73 effect), from §73.3 (no leaf of a place
dying with the frame is pinned): the proof of `exit_preserves_i5`, which reads §73.3 only. It
applies to the re-indexed exit (C6) and to `terminate` (C7). -/
theorem exitEff_i5 {k : K} {t : S3}
    (hnp : ∀ q ∈ List.range t.P.length, t.Usable q → ¬ ({ t with F := t.F.tail } : S3).Usable q →
      ∀ l ∈ footprint t.P q, t.pin l = false ∧ ¬ k.Pinned l)
    (h5 : I5 k t) : I5 k (exitEff t) := by
  intro l hlt hleaf hl
  rw [S3.pin_congr (pins_exitEff t)] at hl
  obtain ⟨q, hq, hlq⟩ := h5 l hlt hleaf hl
  by_cases hu : ({ t with F := t.F.tail } : S3).Usable q
  · exact ⟨q, Frames.exit_usable_iff.2 hu, hlq⟩
  · have hnp := hnp q (List.mem_range.2 hq.lt) hq hu l hlq
    rcases hl with hk | hp
    · exact absurd hk hnp.2
    · rw [hnp.1] at hp; cases hp

/-! ## Every labelled step keeps `I5` (Spec 1 §57; C2, C4–C8, C13–C19, C37–C39) -/

/-- The inherited operations O1–O16 executed by `c` keep `I5` on the global state (Spec 1 §57;
C2, C6): the re-indexed `transfer`, `depend`, `store`, `enterFrame`, `exitFrameC` from the clauses
they read, the others by the lemmas of the memory model on the view of `c`. -/
theorem opStepC_i5 {k : K} {op : KernelOp} {c : Nat} {s s' : SC} (hk : KInvCA s)
    (h : opStepC k op c s (.ok s')) (h5 : I5 k s.flat) : I5 k s'.flat := by
  have hc : s.Live c := opStepC_live h
  have hfr := hk.1.1.1
  have hwv := (view_facts hk hc).1
  have h5v := i5_view hc h5
  cases op with
  | transfer src dst =>
    obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
    exact i5_set (transferEff_i5 hwv hpre.dstUsableAfter h5v) fun _ => SC.mem_view_F hc
  | depend q x =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
    exact i5_set_same h5 rfl rfl rfl
  | store a p =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
    exact i5_set_same h5 (by unfold storeEff; split <;> rfl) (by unfold storeEff; split <;> rfl)
      (pins_storeEff _ a p)
  | enter ps ls =>
    obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
    have hpush := enter_push (ps := ps) (ls := ls) hfr hpre.callerLive
    refine i5_congr (t := enterEff (s.view c) ps ls) (enterEff_i5 hpre.localsOK h5v) rfl rfl rfl
      fun f => ?_
    show f ∈ (enterEffC s c ps ls).frames ↔ f ∈ (enterEff (s.view c) ps ls).F
    rw [hpush.mem]
    show _ ↔ f ∈ s.nF :: (s.view c).F
    rw [List.mem_cons, SC.mem_view_F hc]
  | exit =>
    obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
    exact i5_congr (exitEff_i5 hpre.notPinned h5v) rfl rfl rfl
      fun _ => ((exitEffC_pop hfr.nodup hpre.hasCaller).view_tail hfr.nodup).symm
  | _ =>
    obtain ⟨t, hst, rfl⟩ := viewStep_ok h
    exact i5_set (op_preserves_i5 hwv h5v hst) fun f => by
      rw [viewOp_F hst (fun _ _ e => by cases e) (fun _ _ e => by cases e)
        (fun _ _ e => by cases e) (fun _ _ e => by cases e) (fun e => by cases e)]
      exact SC.mem_view_F hc

/-- `spawn` (C4 effect, Spec 1 §72) executed by `c` keeps `I5`: the new locals belong to the new
frame, the other places keep their usability. -/
theorem spawn_i5 {k : K} {s : SC} {c : Nat} {ps : List Nat} {ls : LocalShape} (hk : KInvCA s)
    (hcr : s.stk c ≠ []) (hsh : ShapeOK s.P.length ls.toShape) (h5 : I5 k s.flat) :
    I5 k (spawnEff s c ps ls).flat := by
  have hc : s.Live c := SC.live_of_stk hcr
  have hpush := spawn_push (ps := ps) (ls := ls) hk.1.1.1 hcr
  refine i5_congr (t := enterEff (s.view c) ps ls) (enterEff_i5 hsh (i5_view hc h5)) rfl rfl rfl
    fun f => ?_
  show f ∈ (spawnEff s c ps ls).frames ↔ f ∈ (enterEff (s.view c) ps ls).F
  rw [hpush.mem]
  show _ ↔ f ∈ s.nF :: (s.view c).F
  rw [List.mem_cons, SC.mem_view_F hc]

/-- The transfer phases of the by-value composite keep `I5` (C5.2; Spec 1 §57, §63 effect), on the
states where the parameters are already yielded, as `transfers_base` keeps `KBase`: the
destination of each transfer is a usable place owned by a frame, so it is usable after its
transfer (C5 item 2). -/
theorem transfers_i5 {k : K} {fin : S3} {c f : Nat} {ps : List Nat} :
    ∀ (t : SC) (vs : List (Nat × Nat)), ValTransfersPre k fin c t vs →
      KBase (yieldEff t ps f) → (∀ v ∈ vs, FrameOwned t.P v.2) →
      (∀ a ∈ ps, ∀ y, t.A[a]? = some y → ∃ g, y.holder = .frame g) →
      I5 k (yieldEff t ps f).flat → I5 k (yieldEff (transfersEff c t vs) ps f).flat
  | _, [], _, _, _, _, h5 => h5
  | t, v :: vs, ⟨hpre, hrest⟩, hk, hown, hp, h5 => by
    simp only [transfersEff]
    have hcl : t.Live c := SC.live_of_hasRight hpre.srcRight
    have hcl' : (yieldEff t ps f).Live c := hcl
    have hu : ∀ q, ((yieldEff t ps f).view c).Usable q ↔ (t.view c).Usable q := fun q =>
      S3.Usable.congr (s' := (yieldEff t ps f).view c) (s := t.view c) rfl
        (by rw [yield_view hcl]) rfl
    have hdeps : ∀ x ∈ movedDeps ((yieldEff t ps f).view c) v.1,
        ((yieldEff t ps f).view c).Active x := by
      intro x hx
      have hmd : movedDeps ((yieldEff t ps f).view c) v.1 = movedDeps (t.view c) v.1 := by
        rw [yield_view hcl]; rfl
      rw [hmd] at hx
      exact (yield_active (v := t.view c) (ps := ps) (f := f)).2 (hpre.depsValid x hx)
    have hown₀ : FrameOwned ((yieldEff t ps f).view c).P v.2 := hown v (List.mem_cons_self ..)
    have hd' := transfer_usable_frameOwned (src := v.1) (dst := v.2) ((hu _).2 hpre.dstUsable) hown₀
    have hk₁ := transfer_base hk hcl ((hu _).2 hpre.srcUsable) ((hu _).2 hpre.dstUsable) hdeps
      hpre.sameShape hpre.disjoint hd'
    have h5₁ : I5 k (transferEffC (yieldEff t ps f) c v.1 v.2).flat :=
      i5_set (transferEff_i5 (view_facts_base hk hcl).1 hd' (i5_view hcl' h5))
        fun _ => SC.mem_view_F hcl'
    rw [yield_transfer hp] at hk₁ h5₁
    refine transfers_i5 (transferEffC t c v.1 v.2) vs hrest hk₁ (fun w hw => ?_)
      (fun a ha y hy => ?_) h5₁
    · exact transfer_frameOwned (hown w (List.mem_cons_of_mem _ hw))
    · obtain ⟨y₀, hy₀, e⟩ := transfer_frame_held hy
      obtain ⟨g, hg⟩ := hp a ha y₀ hy₀
      exact ⟨g, by rw [e ⟨g, hg⟩, hg]⟩

/-- The by-value composite (C4, C5) executed by `c` keeps `I5`: the creation as `spawn`, the
transfer phases as `transfers_i5`; the yield changes holders only. -/
theorem spawnVal_i5 {k : K} {s s' : SC} {c : Nat} {ps : List Nat} {ls : LocalShape}
    {vs : List (Nat × Nat)} (hk : KInvCA s) (h : SpawnValStep k s c ps ls vs (.ok s'))
    (h5 : I5 k s.flat) : I5 k s'.flat := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  have hlt : ∀ a ∈ ps, a < s.A.length := fun a ha => by
    have := hpre.params a ha
    unfold OptP at this; split at this
    · exact lt_of_getElem? ‹_›
    · exact this.elim
  have hframe : ∀ a ∈ ps, ∀ y, (spawnCreate s c ls).A[a]? = some y →
      ∃ g, y.holder = .frame g := by
    intro a ha y hy
    have hp := hpre.params a ha
    have hy' : (spawnCreate s c ls).A[a]? = s.A[a]? := by
      show (mapI _ 0 s.A ++ _)[a]? = _
      rw [List.getElem?_append_left (by rw [length_mapI]; exact hlt a ha), getElem?_mapI]
      cases s.A[a]? <;> simp
    rw [hy'] at hy
    have hy₂ : (s.view c).A[a]? = some y := hy
    rw [hy₂] at hp
    exact ⟨_, hp.2.1⟩
  have hb₀ : KBase (yieldEff (spawnCreate s c ls) ps s.nF) := by
    rw [create_yield hlt]; exact spawn_base hk hpre.creatorLive hpre.params hpre.localsOK
  have h5₀ : I5 k (yieldEff (spawnCreate s c ls) ps s.nF).flat := by
    rw [create_yield hlt]; exact spawn_i5 hk hpre.creatorLive hpre.localsOK h5
  exact transfers_i5 (spawnCreate s c ls) vs hpre.transfers hb₀
    (fun v hv => spawn_frameOwned (hpre.freshDst v hv)) hframe h5₀

/-- Every labelled step keeps `I5` on the global state (Spec 1 §57; C2, C4–C8, C13–C19, C20,
C37–C39), from a state satisfying `KInvCA`, under `DDSound(K)` (Spec 1 §80, for the internal steps
of `issue` and `reset`). C20 requires every transition to preserve the applicable global
invariants; `I5` is one of them (Spec 1 §57, required on the reachable states), so this result
belongs to the coverage of theorem 2. Fragment: every labelled step, no trace restriction. -/
theorem lstep_i5 {ks : KShared} {ML : MutexLayout} {lbl : Label}
    {st st' : SC × SyncReg × ArenaReg} (hdd : DDSound ks.toK) (hk : KInvCA st.1)
    (h : LStep ks ML lbl st st') (h5 : I5 ks.toK st.1.flat) : I5 ks.toK st'.1.flat := by
  cases h with
  | kernel h => exact opStepC_i5 hk h h5
  | spawn h =>
    obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
    exact spawn_i5 hk hpre.creatorLive hpre.localsOK h5
  | spawnVal h => exact spawnVal_i5 hk h h5
  | @terminate s s' reg ar c h =>
    obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
    have hfr := hk.1.1.1
    have hs : s.stk c ≠ [] := fun e => by have := hpre.initialOnly; rw [e] at this; cases this
    have hpar : s.ctxParent c ≠ none := fun e => by
      have := hpre.hasParent; rw [e] at this; exact this
    exact i5_congr (exitEff_i5 hpre.notPinned (i5_view (SC.live_of_stk hs) h5)) rfl rfl rfl
      fun _ => ((termEffC_pop hfr.nodup hpre.initialOnly hpar).view_tail hfr.nodup).symm
  | join h => cases h; exact h5
  | deriveSync h =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
    exact i5_set_same h5 rfl rfl rfl
  | newMutex h => obtain ⟨-, rfl⟩ := h; exact h5
  | acquire h =>
    obtain ⟨e, -, -, -, rfl⟩ := h
    exact i5_set_same h5 rfl rfl rfl
  | unlock h =>
    obtain ⟨e, g, -, -, -, -, -, -, rfl⟩ := h
    exact i5_set_same h5 (by unfold releaseEff; split <;> rfl)
      (by unfold releaseEff; split <;> rfl) (by unfold releaseEff; split <;> rfl)
  | resetLock h => obtain ⟨-, -, -, -, -, -, rfl⟩ := h; exact h5
  | newArena h => obtain ⟨-, -, rfl⟩ := newArenaStepC_ok h; exact h5
  | issue h =>
    obtain ⟨E, s₁, -, -, -, hsp, hsto, -⟩ := issueStepC_ok h
    exact opStepC_i5 (opStepC_preservesC hdd hk (fun e => by cases e) hsp) hsto
      (opStepC_i5 hk hsp h5)
  | reset h =>
    obtain ⟨E, s₁, -, hd, hrl, -, -⟩ := resetStepC_ok (k := ks.toK) h
    exact opStepC_i5 (opStepC_preservesC hdd hk (fun e => by cases e) hd) hrl
      (opStepC_i5 hk hd h5)
  | readShared h => exact h5
  | writeShared h => exact opStepC_i5 hk (writeSharedC_ok_kernel h) h5
  | cas h =>
    rcases cas_ok_cases h with hc | rfl
    · exact opStepC_i5 hk hc h5
    · exact h5

/-- `I5` on the global state along every run (Spec 1 §57; C20), from a state satisfying `KInvCA`
and `I5`, under `DDSound(K)` (Spec 1 §80). Part of the coverage of theorem 2: C20 requires every
transition to preserve the applicable global invariants, `I5` among them. -/
theorem lrun_i5 {ks : KShared} {ML : MutexLayout} {st st' : SC × SyncReg × ArenaReg}
    {lbls : List Label} (hdd : DDSound ks.toK) (h : LRun ks ML st lbls st') (hk : KInvCA st.1)
    (h5 : I5 ks.toK st.1.flat) : I5 ks.toK st'.1.flat := by
  induction h with
  | nil => exact h5
  | cons hs _ ih => exact ih (lstep_kInvCA hdd hs hk) (lstep_i5 hdd hk hs h5)

/-- `I5` on the global state of every state reached from the initial state of Spec 1 §47 by a run
of labelled steps, no trace restriction (Spec 1 §57; C2, C20), under `DDSound(K)` (Spec 1 §80) and
well-formed statics (§47), as `Access.reachable_i5`. Spec 1 §57 requires `I5` on the reachable
states, and C20 requires every transition to preserve the applicable global invariants: this result
belongs to the coverage of theorem 2. -/
theorem reached_i5 {ks : KShared} {ML : MutexLayout} {statics : Statics}
    {st : SC × SyncReg × ArenaReg} {lbls : List Label} (hdd : DDSound ks.toK)
    (hst : StaticsOK statics) (hL : LRun ks ML (SC.ofS3 (S3.init statics), [], []) lbls st) :
    I5 ks.toK st.1.flat := by
  have hflat : (SC.ofS3 (S3.init statics)).flat = S3.init statics := by
    rw [single_flat (SC.Single.sole ⟨_, rfl⟩), toS3_ofS3]
  refine lrun_i5 hdd hL (init_inv hdd hst ML).1 ?_
  show I5 ks.toK (SC.ofS3 (S3.init statics)).flat
  rw [hflat]
  exact reachable_i5 hdd hst .init

/-! ## Pinned leaves of the reached states (Spec 1 §82.6, §74, §75, §57) -/

/-- **Theorem 9**, pinned addresses on the reached states, with all the conclusions of
`Refinement.pinned_address_stable_reachable` (Spec 1 §82.6, §74, §75, §57; C2), at the grain of
abstract steps: under `DDSound(K)` (Spec 1 §80) and well-formed statics (§47), on every state
reached from the initial state of Spec 1 §47 by a run of labelled steps (no trace restriction),
related to the memory state by `ReprC`, for every labelled step from it, whatever the context that
executes it, a leaf covered by an active dynamic pinning obligation (§74) or pinned by `K.Pinned`
has a live allocation before the step; it stays live, with the same address, after the raw
operations of the step (`rawOps`). No invariant or liveness hypothesis: a pinned leaf belongs to a
usable place (`reached_i5`), whose allocation is live (`ReprC`, §82.5). Fragment: every reached
state, every label, every context. -/
theorem reached_pinned_address_live {Ty : Type} {ks : KShared} {ML : MutexLayout}
    {statics : Statics} {π : Refinement.Params Ty} {w : WriteRepr} {lbls : List Label}
    {lbl : Label} {st st' : SC × SyncReg × ArenaReg} {m : Machine.State}
    (hdd : DDSound ks.toK) (hst : StaticsOK statics)
    (hL : LRun ks ML (SC.ofS3 (S3.init statics), [], []) lbls st)
    (hR : ReprC π.L π.rtok st.1 m) (hs : LStep ks ML lbl st st') {l : Nat}
    (hl : l < st.1.P.length) (hlf : isLeaf st.1.P l)
    (hpin : (∃ (o : Nat) (ob : PinOb), st.1.pins[o]? = some ob ∧ ob.active = true ∧
      l ∈ ob.leaves) ∨ ks.toK.Pinned l) :
    Refinement.LiveAlloc m (π.L l).alloc ∧
      Refinement.LiveAlloc (Refinement.run m (rawOps π w lbl st m)) (π.L l).alloc ∧
      Refinement.leafAddr (Refinement.run m (rawOps π w lbl st m)) π.L l =
        Refinement.leafAddr m π.L l := by
  have hk := lrun_kInvCA hdd hL (init_inv hdd hst ML).1
  have hw : WF3 st.1.flat := hk.1.1.2
  obtain ⟨q, hq, hlq⟩ := reached_i5 hdd hst hL l hl hlf
    (hpin.elim (fun h => .inr (S3.pin_iff.2 h)) .inl)
  obtain ⟨-, -, hlq⟩ := mem_footprint.1 hlq
  have hlive : Refinement.LiveAlloc m (π.L l).alloc :=
    (Refinement.Repr.leaf_live (s3 := st.1.flat) hR hw hl hlf
      (usable_of_partOf hw (l + 1) l q (Nat.lt_succ_self l) hlq hq)).mono fun _ h => h.1
  exact ⟨hlive, pinned_address_stableC hR hk hs hl hlf hpin hlive⟩

end Ern.ConcurrencyModel
