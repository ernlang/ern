import Ern.ConcurrencyModel.RefinementState

/-!
# Theorem 9, lifetimes and creations: all the conclusions of `r6_exit`, `r6_free`, `r6_alloc`

Theorem 9a gives, for every labelled step, the execution of `ok` raw steps and `ReprC` after it.
`Refinement.r6_exit`, `Refinement.r6_free` and `Refinement.r6_alloc` conclude more, and this module
transports those results with all their conclusions, at the grain of abstract steps (contexts
interleave at the grain of abstract steps; the statements are about the raw operations modelled by
`rawOps` only), for a step executed by any context (C2):

* the exit of a frame (C6) and `terminate` (C7): the allocations of the root places directly owned
  by the exiting frame are dead after the raw operations (Spec 1 §82.5, §73, §17):
  `exit_realizedC`, `terminate_realizedC`;
* `free`: the allocation of the freed place is dead after its raw operation (Spec 1 §82.4, §70,
  §17): `free_realizedC`;
* `alloc`: one creation realizes the new storage root (Spec 1 §71, `oneRoot`; §82.4):
  `alloc_realizedC`;
* the same on the states reached from the initial state of Spec 1 §47, without invariant
  hypothesis (`reached_*`), as the `_reachable` corollaries of the memory model.

The hypotheses are those of the memory-model results, with `WF3` read on the globally live frames
(`WF3 s.flat`) and the well-formedness of the local stacks (`FramesC`, C20), from which `WF3` of the
view of the executing context follows.
-/

namespace Ern.ConcurrencyModel

open Ern.MemoryModel Ern.MemoryModel.Access Ern.MemoryModel.Refinement
open PreservationAux

/-- The allocations of the root places directly owned by the current frame of `t` are dead after
the deallocations of its exit (Spec 1 §73, §82.5, §17 ¶3): the second conclusion of
`Refinement.r6_exit`, whose proof reads §73.1 (a current frame) only. -/
theorem exit_dead {Ty : Type} {L : Layout} {rtok : Nat → Nat} {t : S3} {m : Machine.State}
    (hR : Repr L rtok t m) (hw : WF3 t) (hF : t.F ≠ []) :
    ∀ r ∈ exitRoots t, AllocP (run m (exitOps (Ty := Ty) L rtok t)) (L r).alloc
      (·.live = false) := by
  have hpw : (exitRoots t).Pairwise (fun r r' => (L r).alloc ≠ (L r').alloc) :=
    ((range_pairwise _).filter _).imp_of_mem fun {r r'} hr hr' hlt =>
      hR.inj r r' (mem_exitRoots.1 hr).1 (mem_exitRoots.1 hr').1 (Nat.ne_of_lt hlt)
  have hlv : ∀ r ∈ exitRoots t, AllocP m (L r).alloc
      fun a => a.live = true ∧ a.freeAuth = some (rtok r) := fun r hr =>
    (hR.live r (mem_exitRoots.1 hr).1 (exitRoots_dies hw hF hr).1).and
      (hR.tokens r (mem_exitRoots.1 hr).1)
  exact (deallocOps_run (Ty := Ty) (C := fun _ _ => True)
    (ObR := ⟨fun _ _ _ => True, fun _ _ _ => True⟩)
    (ObW := ⟨fun _ _ _ _ => True, fun _ _ _ _ => True⟩) (fun _ => trivial) _ m hpw hlv).2.2

section Step

variable {Ty : Type} {ks : KShared} {ML : MutexLayout} {C : Nat → Nat → Prop}
  {ObR : Machine.ReadOblSpec Ty} {ObW : Machine.WriteOblSpec Ty} {π : Params Ty} {w : WriteRepr}

/-- **Theorem 9**, the exit of a frame with all the conclusions of `Refinement.r6_exit` (Spec 1
§82 preamble, §82.5, §73, §17; C2, C6), for `exitFrame` executed by any context `c`, at the grain
of abstract steps: the deallocations of the allocations of the root places directly owned by the
exiting frame (`exitRoots` of the view of `c`) are `ok` raw steps, those allocations are dead
afterwards, and `ReprC` holds after the step. Hypotheses, as `r6_exit`: `ReprC` (Spec 1 §82),
`WF3` of the globally live frames with `FramesC` (Spec 1 §49; C20), the step, and tokens compatible
with themselves (§17.2). Fragment: every state, every context. -/
theorem exit_realizedC {c : Nat} {st st' : SC × SyncReg × ArenaReg} {m : Machine.State}
    (hR : ReprC π.L π.rtok st.1 m) (hfr : FramesC st.1) (hw : WF3 st.1.flat)
    (h : LStep ks ML (.kernel c .exit) st st') (htc : ∀ r, C (π.rtok r) (π.rtok r)) :
    Machine.Exec C ObR ObW (rawOps π w (.kernel c .exit) st m) m
        (run m (rawOps π w (.kernel c .exit) st m)) ∧
      (∀ r ∈ exitRoots (st.1.view c), AllocP (run m (rawOps π w (.kernel c .exit) st m))
        (π.L r).alloc (·.live = false)) ∧
      ReprC π.L π.rtok st'.1 (run m (rawOps π w (.kernel c .exit) st m)) := by
  cases h with
  | @kernel s s' reg ar _ _ h =>
    obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
    have hs : s.stk c ≠ [] := fun e => hpre.hasCaller (by rw [e]; rfl)
    have hc : s.Live c := SC.live_of_stk hs
    have hwv := SC.wf3_view hfr hw hc
    have hRv := (reprC_view hc).1 hR
    obtain ⟨hex, hR'⟩ := exit_realized (C := C) (ObR := ObR) (ObW := ObW) hRv hwv
      (view_F_ne hs) htc
    exact ⟨hex, exit_dead hRv hwv (view_F_ne hs), reprC_of_flat rfl
      (fun f => (exitEffC_pop hfr.nodup hpre.hasCaller).view_tail hfr.nodup) hR'⟩

/-- **Theorem 9**, `terminate` with all the conclusions of `Refinement.r6_exit` (Spec 1 §82
preamble, §82.5, §73, §17; C2, C7), for `terminate` executed by any context `c`, at the grain of
abstract steps: the deallocations of the allocations of the root places directly owned by the
initial frame of `c` are `ok` raw steps, those allocations are dead afterwards, and `ReprC` holds
after the step. Hypotheses as `exit_realizedC`. Fragment: every state, every context. -/
theorem terminate_realizedC {c : Nat} {st st' : SC × SyncReg × ArenaReg} {m : Machine.State}
    (hR : ReprC π.L π.rtok st.1 m) (hfr : FramesC st.1) (hw : WF3 st.1.flat)
    (h : LStep ks ML (.terminate c) st st') (htc : ∀ r, C (π.rtok r) (π.rtok r)) :
    Machine.Exec C ObR ObW (rawOps π w (.terminate c) st m) m
        (run m (rawOps π w (.terminate c) st m)) ∧
      (∀ r ∈ exitRoots (st.1.view c), AllocP (run m (rawOps π w (.terminate c) st m))
        (π.L r).alloc (·.live = false)) ∧
      ReprC π.L π.rtok st'.1 (run m (rawOps π w (.terminate c) st m)) := by
  cases h with
  | @terminate s s' reg ar _ h =>
    obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
    have hs : s.stk c ≠ [] := fun e => by have := hpre.initialOnly; rw [e] at this; cases this
    have hc : s.Live c := SC.live_of_stk hs
    have hwv := SC.wf3_view hfr hw hc
    have hRv := (reprC_view hc).1 hR
    have hpar : s.ctxParent c ≠ none := fun e => by
      have := hpre.hasParent; rw [e] at this; exact this
    obtain ⟨hex, hR'⟩ := exit_realized (C := C) (ObR := ObR) (ObW := ObW) hRv hwv
      (view_F_ne hs) htc
    exact ⟨hex, exit_dead hRv hwv (view_F_ne hs), reprC_of_flat rfl
      (fun f => (termEffC_pop hfr.nodup hpre.initialOnly hpar).view_tail hfr.nodup) hR'⟩

/-- **Theorem 9**, `free` with all the conclusions of `Refinement.r6_free` (Spec 1 §82 preamble,
§82.4, §70, §17; C2), for `free(place, auth)` executed by any context `c`, at the grain of abstract
steps: the deallocation of the allocation of the place is an `ok` raw step, the allocation is dead
afterwards, and `ReprC` holds after the step. Hypotheses, as `r6_free`: `ReprC` (Spec 1 §82), `WF3`
and `NoDangling` of the globally live frames with `FramesC` (Spec 1 §49, §54; C20), the step, and
the instantiation of `K.FreeCompat` (§80). Fragment: every state, every context. -/
theorem free_realizedC {c p auth : Nat} {st st' : SC × SyncReg × ArenaReg} {m : Machine.State}
    (hR : ReprC π.L π.rtok st.1 m) (hfr : FramesC st.1) (hw : WF3 st.1.flat)
    (hnd : NoDangling st.1.flat) (h : LStep ks ML (.kernel c (.free p auth)) st st')
    (hinst : ks.toK.FreeCompat p auth → FreeCompatInst C π.rtok p auth) :
    Machine.Exec C ObR ObW (rawOps π w (.kernel c (.free p auth)) st m) m
        (run m (rawOps π w (.kernel c (.free p auth)) st m)) ∧
      AllocP (run m (rawOps π w (.kernel c (.free p auth)) st m)) (π.L p).alloc
        (·.live = false) ∧
      ReprC π.L π.rtok st'.1 (run m (rawOps π w (.kernel c (.free p auth)) st m)) := by
  cases h with
  | @kernel s s' reg ar _ _ h =>
    have hc : s.Live c := opStepC_live h
    obtain ⟨t, hst, rfl⟩ := viewStep_ok h
    have hst' : FreeStep ks.toK p auth (s.view c) (.ok t) := hst
    have hwv := SC.wf3_view hfr hw hc
    have hndv : NoDangling (s.view c) := noDangling_mem_congr hnd fun _ => SC.mem_view_F hc
    obtain ⟨hex, hdead, hR'⟩ := r6_free (ObR := ObR) (ObW := ObW) ((reprC_view hc).1 hR) hwv hndv
      hst' hinst
    have hF : t.F = (s.view c).F := viewOp_F hst (fun _ _ e => by cases e)
      (fun _ _ e => by cases e) (fun _ _ e => by cases e) (fun _ _ e => by cases e)
      (fun e => by cases e)
    exact ⟨hex, hdead, (reprC_set fun f => by rw [hF]; exact SC.mem_view_F hc).2 hR'⟩

/-- **Theorem 9**, `alloc` with all the conclusions of `Refinement.r6_alloc` (Spec 1 §82 preamble,
§82.4, §71, §9 ¶11; C2), for `alloc(provider, owner, shape)` executed by any context `c`, at the
grain of abstract steps: one creation realizes the new storage root (`oneRoot`, §71), it is an `ok`
raw step, and `ReprC` holds after the step. Hypotheses, as `r6_alloc`: `ReprC` (Spec 1 §82), `WF3`
of the globally live frames with `FramesC` (Spec 1 §49; C20), the step, a valid placement and
geometries (§9 ¶11), and the layout obligations of the new places (§82.1, §23). Fragment: every
state, every context. -/
theorem alloc_realizedC {c pr ow : Nat} {ls : LocalShape} {st st' : SC × SyncReg × ArenaReg}
    {m : Machine.State} (hR : ReprC π.L π.rtok st.1 m) (hfr : FramesC st.1) (hw : WF3 st.1.flat)
    (h : LStep ks ML (.kernel c (.alloc pr ow ls)) st st') (hpl : PlacementOK π.pl)
    (hg : GeomOK π.geom)
    (hlay : NewLayout π.L (allocP (st.1.view c) ow ls) (st.1.view c).P.length m.next π.geom
      (rootIdx ls.toShape)) :
    (rawOps π w (.kernel c (.alloc pr ow ls)) st m).length = 1 ∧
      Machine.Exec C ObR ObW (rawOps π w (.kernel c (.alloc pr ow ls)) st m) m
        (run m (rawOps π w (.kernel c (.alloc pr ow ls)) st m)) ∧
      ReprC π.L π.rtok st'.1 (run m (rawOps π w (.kernel c (.alloc pr ow ls)) st m)) := by
  cases h with
  | @kernel s s' reg ar _ _ h =>
    have hc : s.Live c := opStepC_live h
    obtain ⟨t, hst, rfl⟩ := viewStep_ok h
    have hst' : AllocStep ks.toK pr ow ls (s.view c) (.ok t) := hst
    obtain ⟨hlen, hex, hR'⟩ := r6_alloc (C := C) (ObR := ObR) (ObW := ObW)
      ((reprC_view hc).1 hR) (SC.wf3_view hfr hw hc) hst' hpl hg hlay
    have hF : t.F = (s.view c).F := viewOp_F hst (fun _ _ e => by cases e)
      (fun _ _ e => by cases e) (fun _ _ e => by cases e) (fun _ _ e => by cases e)
      (fun e => by cases e)
    exact ⟨hlen, hex, (reprC_set fun f => by rw [hF]; exact SC.mem_view_F hc).2 hR'⟩

end Step

/-! ## On the reached states (Spec 1 §57; C20, C23) -/

section Reached

variable {Ty : Type} {ks : KShared} {ML : MutexLayout} {C : Nat → Nat → Prop}
  {ObR : Machine.ReadOblSpec Ty} {ObW : Machine.WriteOblSpec Ty} {π : Params Ty} {w : WriteRepr}
  {statics : Statics} {lbls : List Label} {st st' : SC × SyncReg × ArenaReg} {m : Machine.State}

/-- **Theorem 9**, `exit_realizedC` on the reached states (Spec 1 §82.5, §73, §57; C6, C20, C23), as
`Refinement.r6_exit_reachable`: under `DDSound(K)` (Spec 1 §80) and well-formed statics (§47), on
every state reached from the initial state of Spec 1 §47 by a run of labelled steps (no trace
restriction), with no invariant hypothesis, its conclusions in full. Fragment: every reached state,
every context. -/
theorem reached_exit_realized {c : Nat} (hdd : DDSound ks.toK) (hst : StaticsOK statics)
    (hL : LRun ks ML (SC.ofS3 (S3.init statics), [], []) lbls st)
    (hR : ReprC π.L π.rtok st.1 m) (h : LStep ks ML (.kernel c .exit) st st')
    (htc : ∀ r, C (π.rtok r) (π.rtok r)) :
    Machine.Exec C ObR ObW (rawOps π w (.kernel c .exit) st m) m
        (run m (rawOps π w (.kernel c .exit) st m)) ∧
      (∀ r ∈ exitRoots (st.1.view c), AllocP (run m (rawOps π w (.kernel c .exit) st m))
        (π.L r).alloc (·.live = false)) ∧
      ReprC π.L π.rtok st'.1 (run m (rawOps π w (.kernel c .exit) st m)) :=
  have hk := lrun_kInvCA hdd hL (init_inv hdd hst ML).1
  exit_realizedC hR hk.1.1.1 hk.1.1.2 h htc

/-- **Theorem 9**, `terminate_realizedC` on the reached states (Spec 1 §82.5, §73, §57; C7, C20,
C23), as `Refinement.r6_exit_reachable`: under `DDSound(K)` and well-formed statics, on every
reached state, with no invariant hypothesis, its conclusions in full. Fragment: every reached state,
every context. -/
theorem reached_terminate_realized {c : Nat} (hdd : DDSound ks.toK) (hst : StaticsOK statics)
    (hL : LRun ks ML (SC.ofS3 (S3.init statics), [], []) lbls st)
    (hR : ReprC π.L π.rtok st.1 m) (h : LStep ks ML (.terminate c) st st')
    (htc : ∀ r, C (π.rtok r) (π.rtok r)) :
    Machine.Exec C ObR ObW (rawOps π w (.terminate c) st m) m
        (run m (rawOps π w (.terminate c) st m)) ∧
      (∀ r ∈ exitRoots (st.1.view c), AllocP (run m (rawOps π w (.terminate c) st m))
        (π.L r).alloc (·.live = false)) ∧
      ReprC π.L π.rtok st'.1 (run m (rawOps π w (.terminate c) st m)) :=
  have hk := lrun_kInvCA hdd hL (init_inv hdd hst ML).1
  terminate_realizedC hR hk.1.1.1 hk.1.1.2 h htc

/-- **Theorem 9**, `free_realizedC` on the reached states (Spec 1 §82.4, §70, §57; C20, C23), as
`Refinement.r6_free_reachable`: under `DDSound(K)` and well-formed statics, on every reached state,
with no invariant hypothesis, its conclusions in full. Fragment: every reached state, every
context. -/
theorem reached_free_realized {c p auth : Nat} (hdd : DDSound ks.toK) (hst : StaticsOK statics)
    (hL : LRun ks ML (SC.ofS3 (S3.init statics), [], []) lbls st)
    (hR : ReprC π.L π.rtok st.1 m) (h : LStep ks ML (.kernel c (.free p auth)) st st')
    (hinst : ks.toK.FreeCompat p auth → FreeCompatInst C π.rtok p auth) :
    Machine.Exec C ObR ObW (rawOps π w (.kernel c (.free p auth)) st m) m
        (run m (rawOps π w (.kernel c (.free p auth)) st m)) ∧
      AllocP (run m (rawOps π w (.kernel c (.free p auth)) st m)) (π.L p).alloc
        (·.live = false) ∧
      ReprC π.L π.rtok st'.1 (run m (rawOps π w (.kernel c (.free p auth)) st m)) :=
  have hk := lrun_kInvCA hdd hL (init_inv hdd hst ML).1
  free_realizedC hR hk.1.1.1 hk.1.1.2 hk.1.2.1.2.2 h hinst

/-- **Theorem 9**, `alloc_realizedC` on the reached states (Spec 1 §82.4, §71, §57; C20, C23), as
`Refinement.r6_alloc_reachable`: under `DDSound(K)` and well-formed statics, on every reached state,
with no invariant hypothesis, its conclusions in full. Fragment: every reached state, every
context. -/
theorem reached_alloc_realized {c pr ow : Nat} {ls : LocalShape} (hdd : DDSound ks.toK)
    (hst : StaticsOK statics) (hL : LRun ks ML (SC.ofS3 (S3.init statics), [], []) lbls st)
    (hR : ReprC π.L π.rtok st.1 m) (h : LStep ks ML (.kernel c (.alloc pr ow ls)) st st')
    (hpl : PlacementOK π.pl) (hg : GeomOK π.geom)
    (hlay : NewLayout π.L (allocP (st.1.view c) ow ls) (st.1.view c).P.length m.next π.geom
      (rootIdx ls.toShape)) :
    (rawOps π w (.kernel c (.alloc pr ow ls)) st m).length = 1 ∧
      Machine.Exec C ObR ObW (rawOps π w (.kernel c (.alloc pr ow ls)) st m) m
        (run m (rawOps π w (.kernel c (.alloc pr ow ls)) st m)) ∧
      ReprC π.L π.rtok st'.1 (run m (rawOps π w (.kernel c (.alloc pr ow ls)) st m)) :=
  have hk := lrun_kInvCA hdd hL (init_inv hdd hst ML).1
  alloc_realizedC hR hk.1.1.1 hk.1.1.2 h hpl hg hlay

end Reached

end Ern.ConcurrencyModel
