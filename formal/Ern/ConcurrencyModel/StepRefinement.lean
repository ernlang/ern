import Ern.MemoryModel.RefinementArena
import Ern.ConcurrencyModel.SequentialConservativity
import Ern.ConcurrencyModel.Outcomes

/-!
# Theorem 9: refinement at the grain of abstract steps (C2, C25, C50; `OB-C12`, abstract part)

Theorem 9 of `formal/DESIGN.md`, Milestone 4, target theorems: the memory model refinement
(`Ern.MemoryModel.Refinement`, `Ern.MemoryModel.RefinementArena`, Spec 1 §82) extended to the
concurrent machine. Contexts interleave at the grain of abstract steps: the raw operations of one
labelled step run in the memory machine of Spec 1 Parts II–III without interference from the other
contexts. Every statement below is about this fragment only.

* `ReprC`: the representation relation `Repr` of the memory model applied to the global authority
  state `SC.flat` (Spec 1 §82; C2), with the parameters of the run; the library registries are not
  represented (C2, C12). It depends on the stack only through membership (`repr_frames_congr`),
  hence not on the executing context (`reprC_view`; Spec 1 §39: frames have no runtime
  representation).
* `rawOps`: the raw operations of each label, computed from the parameters and the two states,
  nothing chosen per step, as `Refinement.opsOf` and `RefinementArena.lopsOf`. They are of two
  sorts (`rawSort`): a **realization**, the raw operations the memory model gives to the operation
  (Spec 1 §82); or the **abstract effect only**, raw operations that render the effect of the step
  on the represented memory and nothing more, the physical accesses that Spec 2 requires for the
  step being not modelled.
* `StepOblC`: the obligations of one step, explicit, never replaced by `True` (Spec 1 §20.3, §82).
* `refinement_step` (9a): for every labelled step, the raw operations form an execution of `ok`
  raw steps and `ReprC` holds after them.

Not proven here, by any statement of this module:

* the physical realization of the concurrent operations; the physical accesses to the controller
  of the mutex are not modelled: the non-atomic initialization write of C13 and the atomic
  operations of C48 for `acquire`, `unlock` and `resetLock` (`OB-C05`);
* the indivisibility of atomic units and the compilation of memory orders (C38, C39, C50;
  `OB-C12`, concrete part; `OB-C27`); a raw read followed by a raw write does not show it;
* the consistency of an observed value with the bytes read (C31–C34);
* the correspondence of physical events, the internal order of compound steps, `rf`, `mo`, `hb`
  (C26–C34, `OB-C20`);
* that an admitted abstract execution is realizable for given parameters: the obligations of each
  step stay hypotheses;
* any absence of race.
-/

namespace Ern.ConcurrencyModel

open Ern.MemoryModel Ern.MemoryModel.Access Ern.MemoryModel.Refinement
open PreservationAux TransferPreserveAux ReparentAux

/-! ## The representation relation (C2, C12; Spec 1 §82, §39) -/

/-- The representation relation of `S_C` (C2; Spec 1 §82.1, §82.3–§82.5): `Repr` of the memory
model between the global authority state `SC.flat` (the kernel components with the globally live
frames) and a state of the memory machine, for the layout `L` and the deallocation tokens `rtok`
of the parameters of the run (Spec 1 §20.3, §82). The registries of the libraries are outside
`S_C` (C2, C12) and are not represented, as the memory model does for the arena entries
(`RefinementArena.arena_realized`). -/
def ReprC (L : Layout) (rtok : Nat → Nat) (s : SC) (m : Machine.State) : Prop :=
  Repr L rtok s.flat m

/-- `Repr` (Spec 1 §82.1, §82.3–§82.5) reads the places, the initialization states, the death
markers, and the stack only through membership (Spec 1 §40: usability). -/
theorem repr_congr {L : Layout} {rtok : Nat → Nat} {t t' : S3} {m : Machine.State}
    (hR : Repr L rtok t m) (hP : t'.P = t.P) (hI : t'.I = t.I) (hd : t'.dead = t.dead)
    (hF : ∀ f, f ∈ t'.F ↔ f ∈ t.F) : Repr L rtok t' m :=
  hR.transport hR.adm (Dom.refl _) (by rw [hP]) (by rw [hP])
    (fun r hr hu => hR.live r hr
      (S3.Usable.mono (s := t) (s' := t') hP (fun f hf => (hF f).1 hf) (fun q h => hd ▸ h) hu))
    fun _ _ _ h => .inl (hI ▸ h)

/-- `Repr` depends on the stack only through membership (Spec 1 §39: frames have no runtime
representation; §9: the machine is flat): it holds for the same kernel components with any stack
listing the same frames, in any order. -/
theorem repr_frames_congr {L : Layout} {rtok : Nat → Nat} {t : S3} {F' : Frames}
    {m : Machine.State} (hF : ∀ f, f ∈ F' ↔ f ∈ t.F) :
    Repr L rtok { t with F := F' } m ↔ Repr L rtok t m :=
  ⟨fun h => repr_congr (t' := t) h rfl rfl rfl fun f => (hF f).symm,
   fun h => repr_congr (t' := { t with F := F' }) h rfl rfl rfl hF⟩

/-- `ReprC` does not depend on the executing context (C2; Spec 1 §39, §9): for every live context,
it is `Repr` on the view of that context. -/
theorem reprC_view {L : Layout} {rtok : Nat → Nat} {s : SC} {m : Machine.State} {c : Nat}
    (hc : s.Live c) : ReprC L rtok s m ↔ Repr L rtok (s.view c) m :=
  (repr_frames_congr (t := s.flat) (F' := (s.view c).F) fun _ => SC.mem_view_F hc).symm

/-- `ReprC` after writing back kernel components `t` that list the globally live frames (C2). -/
theorem reprC_set {L : Layout} {rtok : Nat → Nat} {s : SC} {t : S3} {m : Machine.State}
    (hF : ∀ f, f ∈ t.F ↔ f ∈ s.frames) : ReprC L rtok (s.set t) m ↔ Repr L rtok t m :=
  repr_frames_congr (t := t) (F' := s.frames) fun f => (hF f).symm

/-- `ReprC` of a state whose kernel components are those of `t` with its globally live frames,
when `t` lists the same frames (C2). -/
theorem reprC_of_flat {L : Layout} {rtok : Nat → Nat} {s' : SC} {t : S3} {m : Machine.State}
    (hflat : s'.flat = { t with F := s'.frames }) (hF : ∀ f, f ∈ t.F ↔ f ∈ s'.frames)
    (h : Repr L rtok t m) : ReprC L rtok s' m := by
  unfold ReprC; rw [hflat]
  exact (repr_frames_congr fun f => (hF f).symm).2 h

/-- `ReprC` after a write-back that changes no place, initialization state or death marker
(Spec 1 §82.1, §82.3, §82.5). -/
theorem reprC_set_same {L : Layout} {rtok : Nat → Nat} {s : SC} {t : S3} {m : Machine.State}
    (hP : t.P = s.P) (hI : t.I = s.I) (hd : t.dead = s.dead) (h : ReprC L rtok s m) :
    ReprC L rtok (s.set t) m :=
  repr_congr (t := s.flat) (t' := (s.set t).flat) h hP hI hd fun _ => Iff.rfl

/-- `ReprC` is kept by the yield of C5.3, which changes holders only. -/
theorem reprC_yield {L : Layout} {rtok : Nat → Nat} {t : SC} {ps : List Nat} {f : Nat}
    {m : Machine.State} (h : ReprC L rtok t m) : ReprC L rtok (yieldEff t ps f) m :=
  repr_congr (t := t.flat) (t' := (yieldEff t ps f).flat) h rfl rfl rfl fun _ => Iff.rfl

/-- `ReprC` of the single-context state of an `S3` is `Repr` of that `S3` (C24). -/
theorem reprC_ofS3 {L : Layout} {rtok : Nat → Nat} {t : S3} {m : Machine.State} :
    ReprC L rtok (SC.ofS3 t) m ↔ Repr L rtok t m := by
  have hF : (SC.ofS3 t).flat = { t with F := (SC.ofS3 t).frames } := rfl
  unfold ReprC
  rw [hF]
  exact repr_frames_congr fun f => by simp [SC.frames, SC.ofS3, SC.stk]

/-! ## Realizations from the clauses they read (Spec 1 §63, §65, §72, §73, §82) -/

section Realized

variable {Ty : Type} {C : Nat → Nat → Prop} {ObR : Machine.ReadOblSpec Ty}
  {ObW : Machine.WriteOblSpec Ty}

/-- Realization of the effect of O4 (Spec 1 §63 effect, §82.2, §82.3), from §63.1 (usable source
and destination), §63.2 (same shape) and §63.3 (source leaves `Init`): the proof of
`Refinement.r6_transfer`, which reads no other clause. It applies to the re-indexed `transfer` and
to the transfer phases of C5. -/
theorem transfer_realized {ty : Nat → Ty} {L : Layout} {rtok : Nat → Nat} {t : S3}
    {m : Machine.State} {src dst : Nat} (hR : Repr L rtok t m) (hw : WF3 t)
    (hsu : t.Usable src) (hdu : t.Usable dst) (hsh : SameShape t.P src dst)
    (hsi : ∀ l ∈ footprint t.P src, t.I l = .init)
    (hob : OblAlong ObR ObW m (transferOps L ty m t src dst)) :
    Machine.Exec C ObR ObW (transferOps L ty m t src dst) m (run m (transferOps L ty m t src dst)) ∧
      Repr L rtok (transferEff t src dst) (run m (transferOps L ty m t src dst)) := by
  have hdl := hdu.lt
  have hsrc : ∀ q ∈ transferPairs t.P src dst, AllocP m (L q.1).alloc fun a => a.live = true ∧
      (L q.1).off + (L q.1).len ≤ a.size ∧ a.InitRange (L q.1).off (L q.1).len := by
    rintro ⟨l, l'⟩ hq
    obtain ⟨hl, -⟩ := mem_transferPairs.1 hq
    obtain ⟨hlP, hlf, hls⟩ := mem_footprint.1 hl
    have hu := usable_of_partOf hw (l + 1) l src (Nat.lt_succ_self l) hls hsu
    obtain ⟨a, ha, h1, h2⟩ := hR.leaf_live hw hlP hlf hu
    obtain ⟨a', ha', h3⟩ := hR.init l hlP hlf (hsi l hl)
    rw [ha] at ha'; cases ha'
    exact ⟨a, ha, h1, h2, h3⟩
  have hdst : ∀ q ∈ transferPairs t.P src dst, AllocP m (L q.2).alloc fun a => a.live = true ∧
      (L q.2).off + (L q.2).len ≤ a.size := by
    rintro ⟨l, l'⟩ hq
    obtain ⟨hl, hc⟩ := mem_transferPairs.1 hq
    obtain ⟨hlP, hlf, hld⟩ := mem_footprint.1 (corr_leaf hw hdl hsh hl hc)
    exact hR.leaf_live hw hlP hlf
      (usable_of_partOf hw (l' + 1) l' dst (Nat.lt_succ_self l') hld hdu)
  obtain ⟨hok, hinit⟩ := copyOps_run (C := C) _ m hR.adm.wf hsrc hdst hob
  have hex := exec_of_along _ _ hok
  refine ⟨hex, hR.transport (hex.admissible hR.adm) (dom_run _ _ hR.adm.wf)
    (transfer_len t src dst) (transfer_parentOf t src dst) (fun r hr hu => ?_)
    fun l _ _ hi => ?_⟩
  · exact live_run _ _ hR.adm.wf (copyOps_noDealloc L ty m _) (hR.live r hr
      (transfer_usable_back hw hsu hu))
  · simp only [transferEff] at hi
    split at hi
    · obtain ⟨l0, hq⟩ := corr_leaf_back hsh ‹_›
      exact .inr (hinit (l0, l) hq)
    · split at hi
      · cases hi
      · exact .inl hi

/-- Realization of the effect of O8 (Spec 1 §65 effect, §82.2, §82.3), from §65.2 (the target is a
usable leaf): the proof of `Refinement.r6_store`, which reads no other clause. -/
theorem store_realized {ty : Nat → Ty} {pe : PtrEnc} {L : Layout} {rtok : Nat → Nat} {t : S3}
    {m : Machine.State} {a p : Nat} (hR : Repr L rtok t m) (hw : WF3 t)
    (hu : t.Usable p) (hleaf : isLeaf t.P p)
    (hob : OblAlong ObR ObW m (storeOps pe m L ty t a p)) :
    Machine.Exec C ObR ObW (storeOps pe m L ty t a p) m (run m (storeOps pe m L ty t a p)) ∧
      Repr L rtok (storeEff t a p) (run m (storeOps pe m L ty t a p)) := by
  have htgt : LeafOfUsable t p :=
    ⟨p, List.mem_range.2 hu.lt, hu, mem_footprint.2 ⟨hu.lt, hleaf, hu.lt, .inl rfl⟩⟩
  simp only [storeOps] at hob ⊢
  refine writes_repr hR hw (fun l hl => by rw [List.mem_singleton.1 hl]; exact htgt)
    hob ?_ ?_ ?_ ?_ <;> unfold storeEff <;> split
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · intro l hl
    dsimp only at hl
    split at hl
    · exact .inr (List.mem_singleton.2 ‹_›)
    · exact .inl hl
  · exact fun l hl => .inl hl

/-- Realization of the effect of O6 (Spec 1 §72 effect, §82.4, §82.5), from §72.2 (the locals form
a well-formed shape): the proof of `Refinement.r6_enter`, which reads no other clause. The creations
are those of the root locals. -/
theorem enter_realized {L : Layout} {rtok : Nat → Nat} {t : S3} {m : Machine.State}
    {ps : List Nat} {ls : LocalShape} {pl : Placement} {g : Nat → Geom}
    (hR : Repr L rtok t m) (hw : WF3 t) (hsh : ShapeOK t.P.length ls.toShape)
    (hpl : PlacementOK pl) (hg : GeomOK g)
    (hlay : NewLayout L (enterP t ls) t.P.length m.next g (rootIdx ls.toShape)) :
    Machine.Exec C ObR ObW (allocOps pl g rtok t.P.length m (rootIdx ls.toShape)) m
        (run m (allocOps (Ty := Ty) pl g rtok t.P.length m (rootIdx ls.toShape))) ∧
      Repr L rtok (enterEff t ps ls)
        (run m (allocOps (Ty := Ty) pl g rtok t.P.length m (rootIdx ls.toShape))) := by
  refine repr_extend hR hpl hg rfl hsh
    (usable_old hw (fun q hq => shapeP_get_lt hq) (fun q hq => ?_) (fun f hf h => ?_))
    (fun l hl => ?_) (fun l hl => ?_) hlay
  · simp only [enterEff, Nat.not_le.2 hq, ↓reduceIte]
  · rcases List.mem_cons.1 h with rfl | h
    · exact absurd hf (Nat.lt_irrefl _)
    · exact h
  · simp only [enterEff, Nat.not_le.2 hl, ↓reduceIte]
  · simp only [enterEff, hl, ↓reduceIte]; exact fun h => by cases h

/-- Realization of the effect of O7 (Spec 1 §73 effect, §82.5, §17), from a nonempty stack (§73.1:
a current frame): the proof of `Refinement.r6_exit`, which reads no other clause of §73. The
deallocations are those of the root places directly owned by the current frame. It applies to the
re-indexed exit (C6) and to `terminate` (C7). -/
theorem exit_realized {L : Layout} {rtok : Nat → Nat} {t : S3} {m : Machine.State}
    (hR : Repr L rtok t m) (hw : WF3 t) (hF : t.F ≠ [])
    (htc : ∀ r, C (rtok r) (rtok r)) :
    Machine.Exec C ObR ObW (exitOps L rtok t) m (run m (exitOps (Ty := Ty) L rtok t)) ∧
      Repr L rtok (exitEff t) (run m (exitOps (Ty := Ty) L rtok t)) := by
  have hpw : (exitRoots t).Pairwise (fun r r' => (L r).alloc ≠ (L r').alloc) :=
    ((range_pairwise _).filter _).imp_of_mem fun {r r'} hr hr' hlt =>
      hR.inj r r' (mem_exitRoots.1 hr).1 (mem_exitRoots.1 hr').1 (Nat.ne_of_lt hlt)
  have hlive : ∀ r ∈ exitRoots t, AllocP m (L r).alloc
      fun a => a.live = true ∧ a.freeAuth = some (rtok r) := fun r hr => by
    obtain ⟨hrt, ho, hd⟩ := mem_exitRoots.1 hr
    cases hpl : t.P[r]? with
    | none => rw [hpl] at ho; exact ho.elim
    | some pl =>
      rw [hpl] at ho
      exact (hR.live r hrt (.frame hpl hd ho (top_mem hF))).and (hR.tokens r hrt)
  obtain ⟨hok, hkeep, -⟩ := deallocOps_run (C := C) (ObR := ObR) (ObW := ObW) htc _ m hpw hlive
  have hex := exec_of_along _ _ hok
  refine ⟨hex, hR.transport (hex.admissible hR.adm) (dom_run _ _ hR.adm.wf) rfl rfl
    (fun r hr hu => ?_) fun l _ _ hi => .inl hi⟩
  have hu0 : t.Usable r := S3.Usable.mono (s := t) (s' := exitEff t) rfl
    (fun f h => List.mem_of_mem_tail h) (fun _ h => h) hu
  have hnot : r ∉ exitRoots t := fun hm => by
    obtain ⟨-, ho, -⟩ := mem_exitRoots.1 hm
    have hnd := hw.frames.2.1
    cases hu with
    | frame hpl _ ho' hf =>
      change t.P[r]? = some _ at hpl
      rw [hpl] at ho; simp only [OptP] at ho; rw [ho] at ho'; cases ho'
      have ht : t.top ∈ t.F.tail := hf
      unfold S3.top at ht
      cases hFe : t.F with
      | nil => exact hF hFe
      | cons f F =>
        rw [hFe] at ht hnd
        exact (List.nodup_cons.1 hnd).1 ht
    | place hpl _ ho' _ =>
      change t.P[r]? = some _ at hpl
      rw [hpl] at ho; simp only [OptP] at ho; rw [ho] at ho'; cases ho'
  obtain ⟨a, ha, hla⟩ := hR.live r hr hu0
  refine ⟨a, ?_, hla⟩
  change (run m (deallocOps (Ty := Ty) L rtok (exitRoots t))).allocs _ = _
  rw [hkeep _ fun r' hr' e => hR.inj r' r (mem_exitRoots.1 hr').1 hr
    (fun e' => hnot (e' ▸ hr')) e, ha]

end Realized

/-! ## Raw operations of each label (C2, C4–C8, C13–C19, C37–C39; Spec 1 §82) -/

/-- The written representation of a step: for each leaf and byte offset, a byte and its
provenance (Spec 1 §10 ¶4, §16 ¶2). It is data of the program carried by the step, as
`Refinement.KOp` carries it for `write` and `writeShared`; the kernel does not read it, and a step
that writes nothing does not read it either. -/
abbrev WriteRepr := Nat → Nat → UInt8 × Option Nat

/-- The kernel operation of the memory model (Spec 1 §60–§75) for an operation O1–O16, with the
representation `w` written by `write` and `writeShared`. -/
def kopOf : KernelOp → WriteRepr → KOp
  | .derive src region m, _ => .derive src region m
  | .split src rs, _ => .split src rs
  | .release a, _ => .release a
  | .transfer src dst, _ => .transfer src dst
  | .depend q x, _ => .depend q x
  | .enter ps ls, _ => .enter ps ls
  | .exit, _ => .exit
  | .read a ls, _ => .read a ls
  | .write a ls, w => .write a ls w
  | .writeShared a ls, w => .writeShared a ls w
  | .pin p, _ => .pin p
  | .unpin o, _ => .unpin o
  | .endUse p, _ => .endUse p
  | .free p auth, _ => .free p auth
  | .alloc pr ow ls, _ => .alloc pr ow ls
  | .store a p, _ => .store a p

/-- The `ok` step of `kopOf op w` is the `ok` outcome of `op` (Spec 1 §58, §60–§75). -/
theorem opStep_kopOf {k : K} {op : KernelOp} {w : WriteRepr} {t t' : S3} :
    OpStep k (kopOf op w) t t' ↔ op.Step k t (.ok t') := by
  cases op <;> exact Iff.rfl

/-- The raw operations of the transfer phases of the by-value composite (C5.2): for each by-value
argument in its declared order, the raw operations of O4 (Spec 1 §63, §82.2, §82.3, `transferOps`)
executed by `c` on the state produced by the earlier transfers, in the memory state produced by the
earlier raw operations. -/
def valOps {Ty : Type} (π : Params Ty) (c : Nat) :
    SC → List (Nat × Nat) → Machine.State → List (Machine.Op Ty)
  | _, [], _ => []
  | t, v :: vs, m => transferOps π.L π.ty m (t.view c) v.1 v.2 ++
      valOps π c (transferEffC t c v.1 v.2) vs (run m (transferOps π.L π.ty m (t.view c) v.1 v.2))

/-- The two sorts of raw operations of a label. -/
inductive RawSort where
  /-- The raw operations the memory model gives to the operation (Spec 1 §82). -/
  | realization
  /-- Raw operations that render the effect of the step on the represented memory, and nothing
  more: the physical accesses that Spec 2 requires for the step are not modelled. -/
  | abstractOnly
deriving DecidableEq

/-- The sort of the raw operations of each label (`rawOps`):

* realization: an inherited operation O1–O16 executed by `c` (C2; Spec 1 §82), the exit of a frame
  (C6; §82.5), `spawn` (C4; §82.4), the by-value composite (C5), `terminate` (C7; §82.5),
  `deriveSync` (C15: no memory effect), the arena operations (C19; Spec 1 §76–§78, §82.7), and a
  concurrent `writeShared` store whose region has no `Atomic` leaf (C36, C39: the O11 writes);
* abstract effect only: `join` (C8, C28, C47: the physical observation of completion is not
  modelled); `newMutex`, `acquire`, `unlock`, `resetLock` (C13, C16–C18, C25, C48: the
  initialization write of the controller and its atomic operations are not modelled, `OB-C05`);
  `readShared` and a failed CAS (C37, C39: neither the memory order nor the observed value is
  modelled); a concurrent `writeShared` store with an `Atomic` leaf (C36, C39: indivisibility and
  memory order not modelled); an RMW and a successful CAS (C38, C39: the indivisibility of the read
  and the write is not shown). -/
def rawSort (ks : KShared) : Label → RawSort
  | .kernel .. | .spawn .. | .spawnVal .. | .terminate .. | .deriveSync .. | .newArena ..
  | .issue .. | .reset .. => .realization
  | .join .. | .newMutex .. | .acquire .. | .unlock .. | .resetLock .. | .readShared ..
  | .cas .. => .abstractOnly
  | .writeShared _ _ region _ kind => match kind with
    | .store => if region.any (fun l => decide (AtomicLeaf ks l)) then .abstractOnly
      else .realization
    | .rmw _ => .abstractOnly

/-- The raw operations of a labelled step from `st`, the memory state being `m` (Spec 1 §82
preamble, §82.2–§82.5, §82.7), computed from the parameters `π`, the written representation `w`
carried by the step and the two states, nothing chosen per step. The sort of each case is given by
`rawSort`.

* An inherited operation O1–O16 executed by `c` (C2), the exit of a frame (C6) included: the raw
  operations `Refinement.opsOf` of the same operation on the view of `c`. Reparenting has no
  memory effect.
* `spawn` (C4): the creations of the root locals of the initial frame, as O6 (Spec 1 §72, §82.4).
* The by-value composite (C5): the creations, then the raw operations of O4 for each transfer in
  the declared order, each from the state left by the previous ones (`valOps`); the yield has none.
* `terminate` (C7): those of O7 on the initial frame of the context (Spec 1 §73, §82.5).
* `deriveSync` (C15): none, the step has no memory effect.
* `join` (C8): none, the abstract state is unchanged; the physical observation of completion is not
  modelled (C28, C47).
* `newMutex`, `acquire`, `unlock`, `resetLock` (C13, C16–C18): none, these steps change only the
  registry and the authority state; the initialization write of the controller (C13) and its
  atomic operations (C48) are not modelled (`OB-C05`).
* `newArena`, `issue`, `reset` (C19; Spec 1 §76–§78): those of the memory model,
  `RefinementArena.lopsOf` of the derived operation on the view of `c` with the arena registry
  (§82.7).
* `readShared` and a failed CAS (C37, C39): the raw read of the leaf, as O9; neither the memory
  order nor the observed value is modelled. The observed value carried by the label is bound to no
  byte here (C31–C34).
* A successful concurrent `writeShared` of kind store (C36, C39): those of O11.
* An RMW and a successful CAS (C38, C39): the raw reads of the leaves of the region, as O9, then
  those of O11; the indivisibility of the read and the write is not shown. The observed value
  carried by the label is bound to no byte here (C31–C34). The region of an admitted RMW is a single
  `Atomic` leaf (C39; `rmw_discipline_cases`), as is that of a CAS: this is the read of that
  leaf. -/
def rawOps {Ty : Type} (π : Params Ty) (w : WriteRepr) :
    Label → SC × SyncReg × ArenaReg → Machine.State → List (Machine.Op Ty)
  | .kernel c op, st, m => opsOf π (kopOf op w) (st.1.view c) m
  | .spawn c _ ls, st, m =>
    allocOps π.pl π.geom π.rtok (st.1.view c).P.length m (rootIdx ls.toShape)
  | .spawnVal c _ ls vs, st, m =>
    allocOps π.pl π.geom π.rtok (st.1.view c).P.length m (rootIdx ls.toShape) ++
      valOps π c (spawnCreate st.1 c ls) vs
        (run m (allocOps (Ty := Ty) π.pl π.geom π.rtok (st.1.view c).P.length m
          (rootIdx ls.toShape)))
  | .terminate c, st, _ => exitOps π.L π.rtok (st.1.view c)
  | .join .., _, _ => []
  | .deriveSync .., _, _ => []
  | .newMutex .., _, _ => []
  | .acquire .., _, _ => []
  | .unlock .., _, _ => []
  | .resetLock .., _, _ => []
  | .newArena c storage internal, st, m =>
    RefinementArena.lopsOf π (.newArena [] storage internal) ⟨st.1.view c, st.2.2⟩ m
  | .issue c i region dst, st, m =>
    RefinementArena.lopsOf π (.issue i region dst) ⟨st.1.view c, st.2.2⟩ m
  | .reset c i, st, m => RefinementArena.lopsOf π (.reset i) ⟨st.1.view c, st.2.2⟩ m
  | .readShared _ _ l _ _, _, m => readOps m π.L π.ty [l]
  | .writeShared _ _ region _ kind, _, m => match kind with
    | .store => writeOps m π.L π.ty w region
    | .rmw _ => readOps m π.L π.ty region ++ writeOps m π.L π.ty w region
  | .cas _ _ l _ _ br, _, m => match br with
    | .success _ => readOps m π.L π.ty [l] ++ writeOps m π.L π.ty w [l]
    | .failure _ => readOps m π.L π.ty [l]

/-- The raw operations of `newArena` and `reset` are empty (Spec 1 §76: registration only; §78:
`derive` and `release` have none, §60, §62). -/
theorem rawOps_arena_nil {Ty : Type} (π : Params Ty) (w : WriteRepr)
    (st : SC × SyncReg × ArenaReg) (m : Machine.State) (c storage internal i : Nat) :
    rawOps π w (.newArena c storage internal) st m = [] ∧ rawOps π w (.reset c i) st m = [] := by
  refine ⟨rfl, ?_⟩
  simp only [rawOps, RefinementArena.lopsOf, RefinementArena.kexp]
  split <;> rfl

/-- The raw operations of `issue` of a registered entry are those of the `store` of the block, of
identity `|A|`, into the destination, on the view after `split` of `internal` (Spec 1 §77, §82.3;
Part XIV): `split` has none (Spec 1 §61). -/
theorem rawOps_issue {Ty : Type} (π : Params Ty) (w : WriteRepr) {st : SC × SyncReg × ArenaReg}
    {m : Machine.State} {c i dst : Nat} {region : List Nat} {E : Arena.ArenaEntry}
    (hE : st.2.2[i]? = some E) :
    rawOps π w (.issue c i region dst) st m =
      storeOps π.pe m π.L π.ty (splitEff (st.1.view c) E.internal [region]) st.1.A.length dst := by
  simp only [rawOps, RefinementArena.lopsOf, RefinementArena.kexp, hE]
  rfl

/-- The obligations of one labelled step (Spec 1 §20.3, §82; C2), explicit and never replaced by
`True`: for an inherited operation executed by `c`, those of `Refinement.StepObl` on the view of `c`
(the parametric obligations of its reads and writes, §15, §16, §20.3; the layout of new places,
§82.1, §23; the instantiation of `K.FreeCompat`, §80, §70.2, §82.4); for `spawn` and the by-value
composite, the parametric obligations of their raw operations and the layout of the new locals
(§82.1, §23); for the other labels, the parametric obligations of their raw operations. Exported
obligation `OB-C12` (C25, C50; Spec 1 §82), stated part (`ExportedObligations`); the obligation is
exported and remains open. -/
def StepOblC {Ty : Type} (k : K) (C : Nat → Nat → Prop) (ObR : Machine.ReadOblSpec Ty)
    (ObW : Machine.WriteOblSpec Ty) (π : Params Ty) (w : WriteRepr) :
    Label → SC × SyncReg × ArenaReg → Machine.State → Prop
  | .kernel c op, st, m => StepObl k C ObR ObW π (kopOf op w) (st.1.view c) m
  | .spawn c ps ls, st, m => OblAlong ObR ObW m (rawOps π w (.spawn c ps ls) st m) ∧
      NewLayout π.L (enterP (st.1.view c) ls) (st.1.view c).P.length m.next π.geom
        (rootIdx ls.toShape)
  | .spawnVal c ps ls vs, st, m => OblAlong ObR ObW m (rawOps π w (.spawnVal c ps ls vs) st m) ∧
      NewLayout π.L (enterP (st.1.view c) ls) (st.1.view c).P.length m.next π.geom
        (rootIdx ls.toShape)
  | lbl, st, m => OblAlong ObR ObW m (rawOps π w lbl st m)

/-! ## Theorem 9a: correspondence step by step -/

section Step

variable {Ty : Type} {k : K} {C : Nat → Nat → Prop} {ObR : Machine.ReadOblSpec Ty}
  {ObW : Machine.WriteOblSpec Ty} {π : Params Ty} {w : WriteRepr}

/-- An `ok` outcome of an operation run on the view of `c` is the written-back `ok` outcome on the
view (C2). -/
theorem viewStep_ok {R : S3 → Outcome3 S3 → Prop} {c : Nat} {s s' : SC}
    (h : ViewStep R c s (.ok s')) : ∃ t', R (s.view c) (.ok t') ∧ s' = s.set t' := by
  obtain ⟨o₃, hR, ho⟩ := h
  cases o₃ with
  | ok t' => injection ho with e; exact ⟨t', hR, e⟩
  | reject => cases ho
  | fail => cases ho

/-- The inherited operations that run on the view of `c` and keep its stack (Spec 1 §60–§62,
§66–§71, §74, §75; C2): `Refinement.r6` on the view, transported to `ReprC`. -/
theorem viewStep_realized {op : KernelOp} {c : Nat} {s s' : SC} {m : Machine.State}
    (hπ : ParamsOK C π) (hR : ReprC π.L π.rtok s m) (hk : KInvCA s) (hc : s.Live c)
    (h : ViewStep (op.Step k) c s (.ok s'))
    (hF : ∀ t', op.Step k (s.view c) (.ok t') → t'.F = (s.view c).F)
    (hob : StepObl k C ObR ObW π (kopOf op w) (s.view c) m) :
    Machine.Exec C ObR ObW (opsOf π (kopOf op w) (s.view c) m) m
        (run m (opsOf π (kopOf op w) (s.view c) m)) ∧
      ReprC π.L π.rtok s' (run m (opsOf π (kopOf op w) (s.view c) m)) := by
  obtain ⟨t', hst, rfl⟩ := viewStep_ok h
  obtain ⟨hw, -, hnd, -, -⟩ := view_facts hk hc
  obtain ⟨hex, hR'⟩ := r6 hπ ((reprC_view hc).1 hR) hw hnd (opStep_kopOf.2 hst) hob
  refine ⟨hex, (reprC_set fun f => ?_).2 hR'⟩
  rw [hF t' hst]; exact SC.mem_view_F hc

/-- The stack of the view of a context with a nonempty local stack is nonempty (C2). -/
theorem view_F_ne {s : SC} {c : Nat} (hs : s.stk c ≠ []) : (s.view c).F ≠ [] := by
  intro he
  obtain ⟨f, hf⟩ := List.exists_mem_of_ne_nil _ hs
  have := (SC.mem_view_F (SC.live_of_stk hs)).2 (SC.mem_frames_of hf)
  rw [he] at this; cases this

/-- The inherited operations O1–O16 executed by `c` (C2, C6; Spec 1 §60–§75, §82): the raw
operations on the view of `c` are an execution of `ok` raw steps and `ReprC` holds after the step.
For `transfer`, `depend`, `store`, `enterFrame` and `exitFrameC`, whose preconditions are
re-indexed on `ancestorC`, the realization is proved from the clauses it reads
(`transfer_realized`, `store_realized`, `enter_realized`, `exit_realized`). -/
theorem kernel_realized {op : KernelOp} {c : Nat} {s s' : SC} {m : Machine.State}
    (hπ : ParamsOK C π) (hR : ReprC π.L π.rtok s m) (hk : KInvCA s)
    (h : opStepC k op c s (.ok s')) (hob : StepObl k C ObR ObW π (kopOf op w) (s.view c) m) :
    Machine.Exec C ObR ObW (opsOf π (kopOf op w) (s.view c) m) m
        (run m (opsOf π (kopOf op w) (s.view c) m)) ∧
      ReprC π.L π.rtok s' (run m (opsOf π (kopOf op w) (s.view c) m)) := by
  have hc : s.Live c := opStepC_live h
  obtain ⟨hw, -, -, -, -⟩ := view_facts hk hc
  have hRv := (reprC_view hc).1 hR
  have hfr := hk.1.1.1
  cases op with
  | transfer src dst =>
    obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
    obtain ⟨hex, hR'⟩ := transfer_realized (C := C) (ty := π.ty) hRv hw hpre.srcUsable
      hpre.dstUsable hpre.sameShape hpre.srcInit hob.1
    exact ⟨hex, (reprC_set (s := s) (t := transferEff (s.view c) src dst)
      fun _ => SC.mem_view_F hc).2 hR'⟩
  | depend q x =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
    exact ⟨.nil _, reprC_set_same rfl rfl rfl hR⟩
  | store a p =>
    obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
    obtain ⟨hex, hR'⟩ := store_realized (C := C) (ty := π.ty) (pe := π.pe) (a := a) hRv hw
      hpre.usable hpre.leaf hob.1
    refine ⟨hex, (reprC_set fun f => ?_).2 hR'⟩
    have : (storeEff (s.view c) a p).F = (s.view c).F := by unfold storeEff; split <;> rfl
    rw [this]; exact SC.mem_view_F hc
  | enter ps ls =>
    obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
    obtain ⟨hex, hR'⟩ := enter_realized (C := C) (ObR := ObR) (ObW := ObW) (ps := ps) hRv hw
      hpre.localsOK hπ.1 hπ.2.1 hob.2
    have hpush := enter_push (ps := ps) (ls := ls) hfr hpre.callerLive
    refine ⟨hex, reprC_of_flat rfl (fun f => ?_) hR'⟩
    rw [hpush.mem]
    show f ∈ s.nF :: (s.view c).F ↔ _
    rw [List.mem_cons, SC.mem_view_F hc]
  | exit =>
    obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
    have hs : s.stk c ≠ [] := fun e => hpre.hasCaller (by rw [e]; rfl)
    obtain ⟨hex, hR'⟩ := exit_realized (C := C) (ObR := ObR) (ObW := ObW) hRv hw (view_F_ne hs)
      hπ.2.2
    exact ⟨hex, reprC_of_flat rfl
      (fun f => (exitEffC_pop hfr.nodup hpre.hasCaller).view_tail hfr.nodup) hR'⟩
  | derive => exact viewStep_realized hπ hR hk hc h (fun _ h => viewOp_F h (fun _ _ e => by cases e)
      (fun _ _ e => by cases e) (fun _ _ e => by cases e) (fun _ _ e => by cases e)
      (fun e => by cases e)) hob
  | split => exact viewStep_realized hπ hR hk hc h (fun _ h => viewOp_F h (fun _ _ e => by cases e)
      (fun _ _ e => by cases e) (fun _ _ e => by cases e) (fun _ _ e => by cases e)
      (fun e => by cases e)) hob
  | release => exact viewStep_realized hπ hR hk hc h (fun _ h => viewOp_F h
      (fun _ _ e => by cases e) (fun _ _ e => by cases e) (fun _ _ e => by cases e)
      (fun _ _ e => by cases e) (fun e => by cases e)) hob
  | read => exact viewStep_realized hπ hR hk hc h (fun _ h => viewOp_F h (fun _ _ e => by cases e)
      (fun _ _ e => by cases e) (fun _ _ e => by cases e) (fun _ _ e => by cases e)
      (fun e => by cases e)) hob
  | write => exact viewStep_realized hπ hR hk hc h (fun _ h => viewOp_F h (fun _ _ e => by cases e)
      (fun _ _ e => by cases e) (fun _ _ e => by cases e) (fun _ _ e => by cases e)
      (fun e => by cases e)) hob
  | writeShared => exact viewStep_realized hπ hR hk hc h (fun _ h => viewOp_F h
      (fun _ _ e => by cases e) (fun _ _ e => by cases e) (fun _ _ e => by cases e)
      (fun _ _ e => by cases e) (fun e => by cases e)) hob
  | pin => exact viewStep_realized hπ hR hk hc h (fun _ h => viewOp_F h (fun _ _ e => by cases e)
      (fun _ _ e => by cases e) (fun _ _ e => by cases e) (fun _ _ e => by cases e)
      (fun e => by cases e)) hob
  | unpin => exact viewStep_realized hπ hR hk hc h (fun _ h => viewOp_F h (fun _ _ e => by cases e)
      (fun _ _ e => by cases e) (fun _ _ e => by cases e) (fun _ _ e => by cases e)
      (fun e => by cases e)) hob
  | endUse => exact viewStep_realized hπ hR hk hc h (fun _ h => viewOp_F h
      (fun _ _ e => by cases e) (fun _ _ e => by cases e) (fun _ _ e => by cases e)
      (fun _ _ e => by cases e) (fun e => by cases e)) hob
  | free => exact viewStep_realized hπ hR hk hc h (fun _ h => viewOp_F h (fun _ _ e => by cases e)
      (fun _ _ e => by cases e) (fun _ _ e => by cases e) (fun _ _ e => by cases e)
      (fun e => by cases e)) hob
  | alloc => exact viewStep_realized hπ hR hk hc h (fun _ h => viewOp_F h (fun _ _ e => by cases e)
      (fun _ _ e => by cases e) (fun _ _ e => by cases e) (fun _ _ e => by cases e)
      (fun e => by cases e)) hob

/-- The transfer phases of the by-value composite (C5.2; Spec 1 §63, §82.2, §82.3): from a state
whose yielded form satisfies the kernel invariant without the anchor orders (`KBase`, the invariant
carried phase by phase in `SpawnValuePreserve`), each phase is realized by `transferOps` on the
view of the creating context, and `ReprC` is kept. -/
theorem vals_realized {fin : S3} {c f : Nat} {ps : List Nat} :
    ∀ (t : SC) (vs : List (Nat × Nat)) (m : Machine.State), ValTransfersPre k fin c t vs →
      KBase (yieldEff t ps f) → (∀ v ∈ vs, FrameOwned t.P v.2) →
      (∀ a ∈ ps, ∀ y, t.A[a]? = some y → ∃ g, y.holder = .frame g) →
      ReprC π.L π.rtok t m → OblAlong ObR ObW m (valOps π c t vs m) →
      Machine.Exec C ObR ObW (valOps π c t vs m) m (run m (valOps π c t vs m)) ∧
        ReprC π.L π.rtok (transfersEff c t vs) (run m (valOps π c t vs m))
  | _, [], _, _, _, _, _, hR, _ => ⟨.nil _, hR⟩
  | t, v :: vs, m, ⟨hpre, hrest⟩, hk, hown, hp, hR, hob => by
    simp only [valOps] at hob ⊢
    obtain ⟨hob₁, hob₂⟩ := (along_append (p := Obl ObR ObW)).1 hob
    have hcl : t.Live c := SC.live_of_hasRight hpre.srcRight
    have hyw := (view_facts_base hk hcl).1
    have hcl' : (yieldEff t ps f).Live c := hcl
    have hRy : Repr π.L π.rtok ((yieldEff t ps f).view c) m :=
      repr_congr ((reprC_view hcl).1 hR) rfl rfl rfl fun _ => by
        rw [SC.mem_view_F hcl', SC.mem_view_F hcl]; exact Iff.rfl
    have hmem : ∀ g, g ∈ ((yieldEff t ps f).view c).F ↔ g ∈ (t.view c).F := fun g => by
      rw [SC.mem_view_F hcl', SC.mem_view_F hcl]; exact Iff.rfl
    have hu : ∀ q, ((yieldEff t ps f).view c).Usable q ↔ (t.view c).Usable q := fun q =>
      ⟨S3.Usable.mono (s := t.view c) (s' := (yieldEff t ps f).view c) rfl
        (fun g hg => (hmem g).1 hg) (fun _ h => h),
       S3.Usable.mono (s := (yieldEff t ps f).view c) (s' := t.view c) rfl
        (fun g hg => (hmem g).2 hg) (fun _ h => h)⟩
    obtain ⟨hex₁, hR₁⟩ := transfer_realized (C := C) (ty := π.ty) hRy hyw
      ((hu _).2 hpre.srcUsable) ((hu _).2 hpre.dstUsable) hpre.sameShape hpre.srcInit hob₁
    have hR₁' : ReprC π.L π.rtok (transferEffC t c v.1 v.2)
        (run m (transferOps π.L π.ty m (t.view c) v.1 v.2)) :=
      (reprC_set (s := t) (t := transferEff (t.view c) v.1 v.2) fun _ => SC.mem_view_F hcl).2
        (repr_congr hR₁ rfl rfl rfl fun g => (hmem g).symm)
    have hk₁ : KBase (yieldEff (transferEffC t c v.1 v.2) ps f) :=
      transfers_base t [v] ⟨hpre, trivial⟩ hk
        (fun w hw => hown w (by rw [List.mem_singleton.1 hw]; exact List.mem_cons_self ..)) hp
    obtain ⟨hex₂, hR₂⟩ := vals_realized (transferEffC t c v.1 v.2) vs _ hrest hk₁
      (fun w hw => transfer_frameOwned (hown w (List.mem_cons_of_mem _ hw)))
      (fun a ha y hy => by
        obtain ⟨y₀, hy₀, e⟩ := transfer_frame_held hy
        obtain ⟨g, hg⟩ := hp a ha y₀ hy₀
        exact ⟨g, by rw [e ⟨g, hg⟩, hg]⟩) hR₁' hob₂
    rw [run_append]
    exact ⟨exec_append hex₁ hex₂, hR₂⟩

/-- `readShared` (C37) and the failed CAS (C39), abstract effect only (`rawSort`): the raw read of
the leaf is an `ok` raw step that leaves the memory state unchanged, and `ReprC` holds; neither the
memory order nor the observed value is modelled, the observed value being bound to no byte here
(C31–C34). -/
theorem readShared_rawOps {ks : KShared} {s : SC} {c a l : Nat} {order : MemOrder}
    {m : Machine.State} (hR : ReprC π.L π.rtok s m) (hk : KInvCA s)
    (hp : ReadSharedPre ks s c a l order)
    (hob : OblAlong ObR ObW m (readOps m π.L π.ty [l])) :
    Machine.Exec C ObR ObW (readOps m π.L π.ty [l]) m (run m (readOps m π.L π.ty [l])) ∧
      ReprC π.L π.rtok s (run m (readOps m π.L π.ty [l])) := by
  have hc : s.Live c := SC.live_of_exercisable hp.read.exercisable
  obtain ⟨hw, -⟩ := view_facts hk hc
  have hrd : Read3Step a [l] (s.view c) (.ok (s.view c)) := .ok hp.read
  obtain ⟨hex, hrun, -⟩ := r6_read (C := C) (rtok := π.rtok) ((reprC_view hc).1 hR) hw hrd hob
  exact ⟨hex, by rw [hrun]; exact hR⟩

/-- The concurrent `writeShared` of kind store (C36, C39): the raw operations of O11 (Spec 1 §68,
§82.2) on the view of `c`, from its O11 preconditions. They are a realization when the region has
no `Atomic` leaf, and the abstract effect only otherwise (`rawSort`: indivisibility and memory
order not modelled). -/
theorem writeSharedStore_rawOps {ks : KShared} {s : SC} {c a : Nat} {region : List Nat}
    {ord : Option MemOrder} {m : Machine.State} (hR : ReprC π.L π.rtok s m) (hk : KInvCA s)
    (hpre : WriteSharedCPre ks s c a region ord .store)
    (hob : OblAlong ObR ObW m (writeOps m π.L π.ty w region)) :
    Machine.Exec C ObR ObW (writeOps m π.L π.ty w region) m
        (run m (writeOps m π.L π.ty w region)) ∧
      ReprC π.L π.rtok (writeSharedCEff s c region) (run m (writeOps m π.L π.ty w region)) := by
  have hc : s.Live c := SC.live_of_exercisable hpre.o11.exercisable
  obtain ⟨hw, -⟩ := view_facts hk hc
  have hst : WriteSharedStep ks.toK a region (s.view c) (.ok (write3Eff (s.view c) region)) :=
    .ok hpre.o11
  obtain ⟨hex, hR'⟩ := r2_writeShared (C := C) (rtok := π.rtok) ((reprC_view hc).1 hR) hw hst hob
  exact ⟨hex, (reprC_set (s := s) (t := write3Eff (s.view c) region)
    fun _ => SC.mem_view_F hc).2 hR'⟩

/-- An RMW and a successful CAS (C38, C39), abstract effect only (`rawSort`): the raw reads of the
leaves of the region, as O9, then the raw operations of O11, from the O11 preconditions and the
initialized leaves of the RMW (`WriteSharedCPre.rmwInit`). The indivisibility of the read and the
write is not shown; the observed value is bound to no byte here (C31–C34). The region of an
admitted RMW is a single `Atomic` leaf (C39; `rmw_discipline_cases`): the raw read is that of the
leaf the step modifies. -/
theorem rmw_rawOps {ks : KShared} {s : SC} {c a : Nat} {region : List Nat}
    {ord : Option MemOrder} {v : Nat} {m : Machine.State} (hR : ReprC π.L π.rtok s m)
    (hk : KInvCA s) (hpre : WriteSharedCPre ks s c a region ord (.rmw v))
    (hob : OblAlong ObR ObW m (readOps m π.L π.ty region ++ writeOps m π.L π.ty w region)) :
    Machine.Exec C ObR ObW (readOps m π.L π.ty region ++ writeOps m π.L π.ty w region) m
        (run m (readOps m π.L π.ty region ++ writeOps m π.L π.ty w region)) ∧
      ReprC π.L π.rtok (writeSharedCEff s c region)
        (run m (readOps m π.L π.ty region ++ writeOps m π.L π.ty w region)) := by
  have hc : s.Live c := SC.live_of_exercisable hpre.o11.exercisable
  obtain ⟨hw, -⟩ := view_facts hk hc
  have hRv := (reprC_view hc).1 hR
  obtain ⟨hob₁, hob₂⟩ := (along_append (p := Obl ObR ObW)).1 hob
  have hrd : Read3Pre (s.view c) a region :=
    ⟨hpre.o11.usable, hpre.rmwInit (fun e => by cases e), hpre.o11.exercisable,
      hpre.o11.effectivePresent, hpre.o11.depsValid⟩
  obtain ⟨hex₁, hrun, -⟩ := r6_read (C := C) (ty := π.ty) (rtok := π.rtok)
    (s3' := s.view c) hRv hw (.ok hrd) hob₁
  rw [hrun] at hob₂ hex₁
  have hst : WriteSharedStep ks.toK a region (s.view c) (.ok (write3Eff (s.view c) region)) :=
    .ok hpre.o11
  obtain ⟨hex₂, hR'⟩ := r2_writeShared (C := C) (rtok := π.rtok) hRv hw hst hob₂
  rw [run_append, hrun]
  exact ⟨exec_append hex₁ hex₂, (reprC_set (s := s) (t := write3Eff (s.view c) region)
    fun _ => SC.mem_view_F hc).2 hR'⟩

/-- **Theorem 9a**, correspondence step by step (C2, C4–C8, C13–C19, C25, C37–C39, C50; Spec 1 §82
preamble, §82.2–§82.5, §82.7, §20.3; `OB-C12`, abstract part), at the grain of abstract steps:
contexts interleave at the grain of abstract steps, and the raw operations of one step run without
interference from the other contexts. For every labelled step `LStep ks ML lbl st st'`, every
label included, every written representation `w` carried by the step and every memory state `m`
related to `st.1` by `ReprC`, the raw operations `rawOps π w lbl st m` form an execution of `ok`
raw steps from `m`, and `ReprC` holds between `st'.1` and the memory state reached.

Hypotheses, with the clause that grants each: the obligations of the parameters (`ParamsOK`,
Spec 1 §9 ¶11, §17.2, §73, §82.5); the kernel invariant re-indexed (`KInvCA`, Spec 1 §57; C20,
C23), which holds on every reached state (`lrun_kInvCA`); the obligations of the step (`StepOblC`:
the parametric obligations of reads and writes, Spec 1 §15, §16, §20.3; the layout of new places,
§82.1, §23; the instantiation of `K.FreeCompat`, §82.4). `DDSound` (Spec 1 §80) is not needed.
Fragment: every reached state satisfying `KInvCA`, every label, at the grain of abstract steps.

Not proven by this statement:

* the physical realization of the concurrent operations; the physical accesses to the controller
  of the mutex are not modelled: the non-atomic initialization write of C13 and the atomic
  operations of C48 for `acquire`, `unlock` and `resetLock` (`OB-C05`);
* the indivisibility of atomic units and the compilation of memory orders (C38, C39, C50;
  `OB-C12`, concrete part; `OB-C27`); a raw read followed by a raw write does not show it;
* the consistency of an observed value with the bytes read (C31–C34);
* the correspondence of physical events, the internal order of compound steps, `rf`, `mo`, `hb`
  (C26–C34, `OB-C20`);
* that an admitted abstract execution is realizable for given parameters: the obligations of each
  step stay hypotheses;
* any absence of race. -/
theorem refinement_step {ks : KShared} {ML : MutexLayout} {lbl : Label}
    {st st' : SC × SyncReg × ArenaReg} {m : Machine.State} (hπ : ParamsOK C π)
    (hR : ReprC π.L π.rtok st.1 m) (hk : KInvCA st.1) (h : LStep ks ML lbl st st')
    (hob : StepOblC ks.toK C ObR ObW π w lbl st m) :
    Machine.Exec C ObR ObW (rawOps π w lbl st m) m (run m (rawOps π w lbl st m)) ∧
      ReprC π.L π.rtok st'.1 (run m (rawOps π w lbl st m)) := by
  cases h with
  | kernel h => exact kernel_realized hπ hR hk h hob
  | @spawn s s' reg ar c ps ls h =>
    obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
    have hc : s.Live c := SC.live_of_stk hpre.creatorLive
    obtain ⟨hw, -⟩ := view_facts hk hc
    obtain ⟨hex, hR'⟩ := enter_realized (C := C) (ObR := ObR) (ObW := ObW) (ps := ps)
      ((reprC_view hc).1 hR) hw hpre.localsOK hπ.1 hπ.2.1 hob.2
    have hpush := spawn_push (ps := ps) (ls := ls) hk.1.1.1 hpre.creatorLive
    refine ⟨hex, reprC_of_flat rfl (fun f => ?_) hR'⟩
    rw [hpush.mem]
    show f ∈ s.nF :: (s.view c).F ↔ _
    rw [List.mem_cons, SC.mem_view_F hc]
  | @spawnVal s s' reg ar c ps ls vs h =>
    obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
    obtain ⟨hob, hlay⟩ := hob
    simp only [rawOps] at hob ⊢
    obtain ⟨hob₁, hob₂⟩ := (along_append (p := Obl ObR ObW)).1 hob
    have hc : s.Live c := SC.live_of_stk hpre.creatorLive
    obtain ⟨hw, -⟩ := view_facts hk hc
    obtain ⟨hex₁, hR₁⟩ := enter_realized (C := C) (ObR := ObR) (ObW := ObW) (ps := [])
      ((reprC_view hc).1 hR) hw hpre.localsOK hπ.1 hπ.2.1 hlay
    have hpush := spawn_push (ps := []) (ls := ls) hk.1.1.1 hpre.creatorLive
    have hR₁' : ReprC π.L π.rtok (spawnCreate s c ls) _ := reprC_of_flat rfl (fun f => by
      show f ∈ (enterEff (s.view c) [] ls).F ↔ f ∈ (spawnEff s c [] ls).frames
      rw [hpush.mem]
      show f ∈ s.nF :: (s.view c).F ↔ _
      rw [List.mem_cons, SC.mem_view_F hc]) hR₁
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
    obtain ⟨hex₂, hR₂⟩ := vals_realized (π := π) (spawnCreate s c ls) vs _ hpre.transfers hb₀
      (fun v hv => spawn_frameOwned (hpre.freshDst v hv)) hframe hR₁' hob₂
    rw [run_append]
    exact ⟨exec_append hex₁ hex₂, reprC_yield hR₂⟩
  | @terminate s s' reg ar c h =>
    obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
    have hs : s.stk c ≠ [] := fun e => by have := hpre.initialOnly; rw [e] at this; cases this
    have hc : s.Live c := SC.live_of_stk hs
    obtain ⟨hw, -⟩ := view_facts hk hc
    have hfr := hk.1.1.1
    have hpar : s.ctxParent c ≠ none := fun e => by
      have := hpre.hasParent; rw [e] at this; exact this
    obtain ⟨hex, hR'⟩ := exit_realized (C := C) (ObR := ObR) (ObW := ObW)
      ((reprC_view hc).1 hR) hw (view_F_ne hs) hπ.2.2
    exact ⟨hex, reprC_of_flat rfl
      (fun f => (termEffC_pop hfr.nodup hpre.initialOnly hpar).view_tail hfr.nodup) hR'⟩
  | join h => cases h; exact ⟨.nil _, hR⟩
  | deriveSync h =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
    exact ⟨.nil _, reprC_set_same rfl rfl rfl hR⟩
  | newMutex h => obtain ⟨-, rfl⟩ := h; exact ⟨.nil _, hR⟩
  | acquire h =>
    obtain ⟨e, -, -, -, rfl⟩ := h
    exact ⟨.nil _, reprC_set_same rfl rfl rfl hR⟩
  | unlock h =>
    obtain ⟨e, g, -, -, -, -, -, -, rfl⟩ := h
    refine ⟨.nil _, reprC_set_same ?_ ?_ ?_ hR⟩ <;> unfold releaseEff <;> split <;> rfl
  | resetLock h => obtain ⟨-, -, -, -, -, -, rfl⟩ := h; exact ⟨.nil _, hR⟩
  | @newArena s reg ar c st i st' h =>
    obtain ⟨-, -, rfl⟩ := newArenaStepC_ok h
    rw [(rawOps_arena_nil π w (s, reg, ar) m c st i 0).1]
    exact ⟨.nil _, hR⟩
  | @issue s reg ar c i region dst st' h =>
    rcases st' with ⟨s', ar'⟩
    obtain ⟨E, s₁, hE, -, -, hsp, hsto, -⟩ := issueStepC_ok h
    dsimp only at hsto ⊢
    have hc : s.Live c := opStepC_live hsp
    obtain ⟨t, hRt, rfl⟩ := viewStep_ok hsp
    have hRt' : SplitStep ks.toK E.internal [region] (s.view c) (.ok t) := hRt
    have hwt : WF3 t := split_preserves_wf3 (view_facts hk hc).1 hRt'
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hRt'
    have hv : (s.set (splitEff (s.view c) E.internal [region])).view c =
        splitEff (s.view c) E.internal [region] := SC.view_set hc rfl
    obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 hsto
    have hob' : OblAlong ObR ObW m (storeOps π.pe m π.L π.ty
        (splitEff (s.view c) E.internal [region]) s.A.length dst) := by
      have := hob; simp only [StepOblC, rawOps_issue π w (st := (s, reg, ar)) hE] at this
      exact this
    rw [rawOps_issue π w (st := (s, reg, ar)) hE]
    have hR₁ : ReprC π.L π.rtok (s.set (splitEff (s.view c) E.internal [region])) m :=
      reprC_set_same rfl rfl rfl hR
    have hc₁ : (s.set (splitEff (s.view c) E.internal [region])).Live c := hc
    obtain ⟨hex, hR'⟩ := store_realized (C := C) (ty := π.ty) (pe := π.pe) (a := s.A.length)
      (by rw [← hv]; exact (reprC_view hc₁).1 hR₁) hwt
      (by rw [← hv]; exact hpre.usable) (by rw [← hv]; exact hpre.leaf) hob'
    refine ⟨hex, ?_⟩
    unfold storeEffC
    rw [hv]
    refine (reprC_set fun f => ?_).2 hR'
    have : (storeEff (splitEff (s.view c) E.internal [region]) s.A.length dst).F =
        (s.view c).F := by unfold storeEff; split <;> rfl
    rw [this, SC.mem_view_F hc]; exact Iff.rfl
  | @reset s reg ar c i st' h =>
    rcases st' with ⟨s', ar'⟩
    obtain ⟨E, s₁, hE, hd, hrl, -, -⟩ := resetStepC_ok (k := ks.toK) h
    dsimp only at hrl ⊢
    rw [(rawOps_arena_nil π w (s, reg, ar) m c 0 0 i).2]
    obtain ⟨t₁, hR₁, rfl⟩ := viewStep_ok hd
    obtain ⟨t₂, hR₂, rfl⟩ := viewStep_ok hrl
    have hR₁' : DeriveStep E.internal (footprint s.P E.storage) .modify (s.view c) (.ok t₁) := hR₁
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hR₁'
    have hR₂' : ReleaseStep s.A.length
        ((s.set (deriveEff (s.view c) E.internal (footprint s.P E.storage) .modify)).view c)
        (.ok t₂) := hR₂
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hR₂'
    refine ⟨.nil _, ?_⟩
    rw [SC.set_set]
    refine reprC_set_same ?_ ?_ ?_ hR <;> unfold releaseEff <;> split <;> rfl
  | readShared h =>
    obtain ⟨hp, -⟩ := Guarded.ok_iff.1 h
    exact readShared_rawOps hR hk hp hob
  | @writeShared s s' reg ar c a region order kind h =>
    obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
    cases kind with
    | store => exact writeSharedStore_rawOps hR hk hpre hob
    | rmw v => exact rmw_rawOps hR hk hpre hob
  | @cas s s' reg ar c a l succ fail br h =>
    rcases h with ⟨-, h⟩ | ⟨-, h⟩
    · cases h
    · cases br with
      | success v =>
        obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
        exact rmw_rawOps hR hk hpre hob
      | failure v =>
        obtain ⟨hp, rfl⟩ := Guarded.ok_iff.1 h
        exact readShared_rawOps hR hk hp hob

end Step

end Ern.ConcurrencyModel
