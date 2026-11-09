import Ern.Concurrency.Repr
import Ern.Concurrency.Reachable
import Ern.Concurrency.TransferPreserve

/-!
# Realization of the labelled concurrent steps in the memory machine (WC4 C2, C24, C25; Spec 1 §82)

Contexts interleave at the grain of abstract steps: the realization of one labelled step of a
context is a sequence of raw steps of the memory machine of Spec 1 Parts II–III, run without
interference from the other contexts. Every statement below is about this fragment only. Concurrent
byte accesses, physical atomicity, memory orders and `happens-before` (WC4 OB-C01–OB-C06) are outside
it, and so is the realization of the controller word (WC4 OB-C05). No unsafe region is modelled.

* `realize`: the raw operations of each label of `LStep`. An inherited operation O1–O16 executed by
  `c` is realized as in `Ern.MemoryModel.Refinement` (`opsOf`) on the view of `c` (WC4 C2), the
  representations written by `write` and `writeShared` being data of the program; `spawn` by the
  creations of the locals of O6 (Spec 1 §72, §82.4); `terminate` as O7 (Spec 1 §73, §82.5);
  reparenting has no memory effect; the by-value composite (WC4 C5) by its phases in order: the
  creations, then the realizations of O4 (Spec 1 §63) by transfer in the declared order, the yield
  having none; `join`, `deriveSync`, `newMutex`, `acquire`, `unlock`, `resetLock` by none.
* `StepOblC`: the obligations of one step, those of `Refinement.StepObl` (Spec 1 §20.3, §15, §16,
  §82.1, §82.4) on the view of the executing context, explicit and never replaced by `True`.
* R1 (`r1_lstep`): for every labelled step, the realization is an execution of `ok` raw steps that
  keeps `ReprC`.
* R5 (`r5_realize`): on a single-context state, the realization of an inherited operation is the
  realization of `Ern.MemoryModel.Refinement` on the projection (WC4 C24).
* R2 (`simulationC`) and R3 (`concrete_safety`): every run of encapsulated labelled steps from the
  initial state of Spec 1 §47, with parameters fixed once per run, is realized by an execution of
  `ok` raw steps from the empty memory state, related by `ReprC`, none of whose raw steps is `ub`.
-/

namespace Ern.Concurrency

open Ern.MemoryModel Ern.MemoryModel.Access Ern.MemoryModel.Refinement
open PreservationAux TransferPreserveAux ReparentAux

/-! ## Realizations transferred from `Ern.MemoryModel.Refinement` -/

namespace RealizeAux

variable {Ty : Type} {C : Nat → Nat → Prop} {ObR : Machine.ReadOblSpec Ty}
  {ObW : Machine.WriteOblSpec Ty}

/-- Realization of the effect of O4 (Spec 1 §63 effect, §82.2, §82.3), from the clauses §63.1
(usability of source and destination), §63.2 and §63.3 (source leaves `Init`) only: the proof of
`Refinement.r6_transfer`, which reads no other clause. -/
theorem realize_transfer {ty : Nat → Ty} {L : Layout} {rtok : Nat → Nat} {t : S3}
    {m : Machine.State} {src dst : Nat} (hR : Refinement.Repr L rtok t m) (hw : WF3 t)
    (hsu : t.Usable src) (hdu : t.Usable dst) (hsh : SameShape t.P src dst)
    (hsi : ∀ l ∈ footprint t.P src, t.I l = .init)
    (hob : OblAlong ObR ObW m (transferOps L ty m t src dst)) :
    Machine.Exec C ObR ObW (transferOps L ty m t src dst) m (run m (transferOps L ty m t src dst)) ∧
      Refinement.Repr L rtok (transferEff t src dst) (run m (transferOps L ty m t src dst)) := by
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

/-- Realization of the effect of O8 (Spec 1 §65 effect, §82.2, §82.3), from the clause §65.2
(`target` is a usable leaf) only: the proof of `Refinement.r6_store`, which reads no other
clause. -/
theorem realize_store {ty : Nat → Ty} {pe : PtrEnc} {L : Layout} {rtok : Nat → Nat} {t : S3}
    {m : Machine.State} {a p : Nat} (hR : Refinement.Repr L rtok t m) (hw : WF3 t)
    (hu : t.Usable p) (hleaf : isLeaf t.P p)
    (hob : OblAlong ObR ObW m (storeOps pe m L ty t a p)) :
    Machine.Exec C ObR ObW (storeOps pe m L ty t a p) m (run m (storeOps pe m L ty t a p)) ∧
      Refinement.Repr L rtok (storeEff t a p) (run m (storeOps pe m L ty t a p)) := by
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

/-- Realization of the effect of O6 (Spec 1 §72 effect, §82.4, §82.5), from the clause §72.2 (the
locals form a well-formed shape) only: the proof of `Refinement.r6_enter`, which reads no other
clause. The creations are those of the root locals. -/
theorem realize_enter {L : Layout} {rtok : Nat → Nat} {t : S3} {m : Machine.State}
    {ps : List Nat} {ls : LocalShape} {pl : Placement} {g : Nat → Geom}
    (hR : Refinement.Repr L rtok t m) (hw : WF3 t) (hsh : ShapeOK t.P.length ls.toShape)
    (hpl : PlacementOK pl) (hg : GeomOK g)
    (hlay : NewLayout L (enterP t ls) t.P.length m.next g (rootIdx ls.toShape)) :
    Machine.Exec C ObR ObW (allocOps pl g rtok t.P.length m (rootIdx ls.toShape)) m
        (run m (allocOps (Ty := Ty) pl g rtok t.P.length m (rootIdx ls.toShape))) ∧
      Refinement.Repr L rtok (enterEff t ps ls)
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

/-- Realization of the effect of O7 (Spec 1 §73 effect, §82.5, §17), from a nonempty stack
only: the proof of `Refinement.r6_exit`, which reads no clause of §73 but the existence of a
current frame. The deallocations are those of the root places directly owned by the current
frame. -/
theorem realize_exit {L : Layout} {rtok : Nat → Nat} {t : S3} {m : Machine.State}
    (hR : Refinement.Repr L rtok t m) (hw : WF3 t) (hF : t.F ≠ [])
    (htc : ∀ r, C (rtok r) (rtok r)) :
    Machine.Exec C ObR ObW (exitOps L rtok t) m (run m (exitOps (Ty := Ty) L rtok t)) ∧
      Refinement.Repr L rtok (exitEff t) (run m (exitOps (Ty := Ty) L rtok t)) := by
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

end RealizeAux

open RealizeAux

/-! ## Transport of `ReprC` to the written-back state (WC4 C2) -/

/-- `ReprC` of a state whose kernel components are those of `t` with the globally live frames,
when `t` lists the same frames (WC4 C2; `repr_frames_congr`). -/
theorem reprC_of_flat {L : Layout} {rtok : Nat → Nat} {s' : SC} {t : S3} {m : Machine.State}
    (hflat : s'.flat = { t with F := s'.frames }) (hF : ∀ f, f ∈ t.F ↔ f ∈ s'.frames)
    (h : Refinement.Repr L rtok t m) : ReprC L rtok s' m := by
  unfold ReprC; rw [hflat]
  exact (repr_frames_congr fun f => (hF f).symm).2 h

/-- `ReprC` after a step that changes no place, initialization state or death marker, and no
context (WC4 C2; Spec 1 §82.1, §82.3, §82.5). -/
theorem reprC_set_same {L : Layout} {rtok : Nat → Nat} {s : SC} {t : S3} {m : Machine.State}
    (hP : t.P = s.P) (hI : t.I = s.I) (hd : t.dead = s.dead) (h : ReprC L rtok s m) :
    ReprC L rtok (s.set t) m :=
  repr_congr (t := s.flat) (t' := (s.set t).flat) h hP hI hd fun _ => Iff.rfl

/-- `ReprC` is kept by the yield of WC4 C5.3, which changes holders only. -/
theorem reprC_yield {L : Layout} {rtok : Nat → Nat} {t : SC} {ps : List Nat} {f : Nat}
    {m : Machine.State} (h : ReprC L rtok t m) : ReprC L rtok (yieldEff t ps f) m :=
  repr_congr (t := t.flat) (t' := (yieldEff t ps f).flat) h rfl rfl rfl fun _ => Iff.rfl

/-! ## Realization of the labels (WC4 C2, C4–C8, C13–C18; Spec 1 §82.2–§82.5) -/

/-- The kernel operation of `Ern.MemoryModel.Refinement` (Spec 1 §60–§75) for an operation
O1–O16, with the representations `w` written by `write` and `writeShared` (Spec 1 §10 ¶4, §16 ¶2),
data of the program that the kernel does not read. -/
def kopOf : KernelOp → (Nat → Nat → UInt8 × Option Nat) → KOp
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
theorem opStep_kopOf {k : K} {op : KernelOp} {w : Nat → Nat → UInt8 × Option Nat} {t t' : S3} :
    OpStep k (kopOf op w) t t' ↔ op.Step k t (.ok t') := by
  cases op <;> exact Iff.rfl

/-- The raw operations of the transfer phases of the by-value composite (WC4 C5.2): for each
by-value argument in its declared order, the realization of O4 (Spec 1 §63, §82.2, §82.3,
`transferOps`) executed by `c` on the state produced by the earlier transfers, in the memory state
produced by the earlier copies. -/
def valOps {Ty : Type} (π : Refinement.Params Ty) (c : Nat) :
    SC → List (Nat × Nat) → Machine.State → List (Machine.Op Ty)
  | _, [], _ => []
  | t, v :: vs, m => transferOps π.L π.ty m (t.view c) v.1 v.2 ++
      valOps π c (transferEffC t c v.1 v.2) vs (run m (transferOps π.L π.ty m (t.view c) v.1 v.2))

/-- The raw operations realizing a labelled step from `s`, the memory state being `m` (WC4 C2,
C4–C8, C13–C18; Spec 1 §82 preamble, §82.2–§82.5), at the grain of abstract steps:
- an inherited operation O1–O16 executed by `c`: the realization `opsOf` of
  `Ern.MemoryModel.Refinement` on the view of `c` (WC4 C2), with the written representations `w`;
- `spawn` (WC4 C4): the creations of the root locals of O6 (Spec 1 §72, §82.4); the yield of the
  parameters has no memory effect;
- the by-value composite (WC4 C5): its phases in order, the creations of the root locals (C5.1),
  then the realizations of O4 by transfer in the declared order (C5.2), the yield (C5.3) having
  none;
- `terminate` (WC4 C7): the realization of O7 on the view of `c` (Spec 1 §73, §82.5);
  reparenting (WC4 C6) has no memory effect;
- `join` (WC4 C8) and `deriveSync` (WC4 C15, O1 has no storage effect, Spec 1 §60): none;
- `newMutex`, `acquire`, `unlock`, `resetLock` (WC4 C13, C16–C18): none, the registry only; the
  physical controller and its correspondence with the registry are the realization obligation
  WC4 OB-C05, not modelled. -/
def realize {Ty : Type} (π : Refinement.Params Ty) (w : Nat → Nat → UInt8 × Option Nat) :
    Label → SC → Machine.State → List (Machine.Op Ty)
  | .kernel c op, s, m => opsOf π (kopOf op w) (s.view c) m
  | .spawn c _ ls, s, m => allocOps π.pl π.geom π.rtok (s.view c).P.length m (rootIdx ls.toShape)
  | .spawnVal c _ ls vs, s, m =>
    allocOps π.pl π.geom π.rtok (s.view c).P.length m (rootIdx ls.toShape) ++
      valOps π c (spawnCreate s c ls) vs
        (run m (allocOps (Ty := Ty) π.pl π.geom π.rtok (s.view c).P.length m (rootIdx ls.toShape)))
  | .terminate c, s, _ => exitOps π.L π.rtok (s.view c)
  | .join .., _, _ => []
  | .deriveSync .., _, _ => []
  | .newMutex .., _, _ => []
  | .acquire .., _, _ => []
  | .unlock .., _, _ => []
  | .resetLock .., _, _ => []

/-- WC4 OB-C05: `newMutex`, `acquire`, `unlock` and `resetLock` have no raw operation in this
realization; their physical controller update is not modelled. -/
theorem realize_sync {Ty : Type} (π : Refinement.Params Ty) (w : Nat → Nat → UInt8 × Option Nat)
    (s : SC) (m : Machine.State) (c g i : Nat) (adm : List Nat) :
    realize π w (.newMutex c g adm) s m = [] ∧ realize π w (.acquire c i) s m = [] ∧
      realize π w (.unlock c i) s m = [] ∧ realize π w (.resetLock c i) s m = [] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The obligations of one labelled step (Spec 1 §20.3, §82; WC4 C2): for an inherited operation
executed by `c`, those of `Refinement.StepObl` on the view of `c` (the parametric obligations of
its reads and writes, §15, §16; the layout of new places, §82.1, §23; the instantiation of
`K.FreeCompat`, §80, §70.2, §82.4); for `spawn` and the by-value composite, the parametric
obligations of its raw operations and the layout of the new locals (§82.1, §23); for the other
labels, the parametric obligations of their raw operations. -/
def StepOblC {Ty : Type} (k : K) (C : Nat → Nat → Prop) (ObR : Machine.ReadOblSpec Ty)
    (ObW : Machine.WriteOblSpec Ty) (π : Refinement.Params Ty)
    (w : Nat → Nat → UInt8 × Option Nat) : Label → SC → Machine.State → Prop
  | .kernel c op, s, m => StepObl k C ObR ObW π (kopOf op w) (s.view c) m
  | .spawn c ps ls, s, m => OblAlong ObR ObW m (realize π w (.spawn c ps ls) s m) ∧
      NewLayout π.L (enterP (s.view c) ls) (s.view c).P.length m.next π.geom (rootIdx ls.toShape)
  | .spawnVal c ps ls vs, s, m => OblAlong ObR ObW m (realize π w (.spawnVal c ps ls vs) s m) ∧
      NewLayout π.L (enterP (s.view c) ls) (s.view c).P.length m.next π.geom (rootIdx ls.toShape)
  | lbl, s, m => OblAlong ObR ObW m (realize π w lbl s m)

/-! ## R1, step by step -/

section R1

variable {Ty : Type} {k : K} {C : Nat → Nat → Prop} {ObR : Machine.ReadOblSpec Ty}
  {ObW : Machine.WriteOblSpec Ty} {π : Refinement.Params Ty}
  {w : Nat → Nat → UInt8 × Option Nat}

/-- An `ok` outcome of an operation run on the view of `c` is the written-back `ok` outcome on the
view (WC4 C2). -/
theorem viewStep_ok {R : S3 → Outcome3 S3 → Prop} {c : Nat} {s s' : SC}
    (h : ViewStep R c s (.ok s')) : ∃ t', R (s.view c) (.ok t') ∧ s' = s.set t' := by
  obtain ⟨-, o₃, hR, ho⟩ := h
  cases o₃ with
  | ok t' => injection ho with e; exact ⟨t', hR, e⟩
  | reject => cases ho
  | fail => cases ho

/-- R1 for the inherited operations that run on the view of `c` and keep the stack (Spec 1
§60–§62, §66–§71, §74, §75; WC4 C2): `Refinement.r6` on the view, transported to `S_C`. -/
theorem r1_viewStep {op : KernelOp} {c : Nat} {s s' : SC} {m : Machine.State}
    (hπ : Refinement.ParamsOK C π) (hR : ReprC π.L π.rtok s m) (hk : KInvCA s)
    (h : ViewStep (op.Step k) c s (.ok s'))
    (hF : ∀ t', op.Step k (s.view c) (.ok t') → t'.F = (s.view c).F)
    (hob : StepObl k C ObR ObW π (kopOf op w) (s.view c) m) :
    Machine.Exec C ObR ObW (opsOf π (kopOf op w) (s.view c) m) m
        (run m (opsOf π (kopOf op w) (s.view c) m)) ∧
      ReprC π.L π.rtok s' (run m (opsOf π (kopOf op w) (s.view c) m)) := by
  obtain ⟨t', hst, rfl⟩ := viewStep_ok h
  obtain ⟨hw, -, hnd, -, -⟩ := view_facts hk c
  obtain ⟨hex, hR'⟩ := r6 hπ ((reprC_view c).1 hR) hw hnd (opStep_kopOf.2 hst) hob
  refine ⟨hex, (reprC_set fun f => ?_).2 hR'⟩
  rw [hF t' hst]; exact SC.mem_view_F

/-- R1 for the inherited operations O1–O16 executed by `c` (WC4 C2, C6; Spec 1 §60–§75, §82):
the realization on the view of `c` is an execution of `ok` raw steps and `ReprC` holds after the
step. For `transfer`, `depend`, `store`, `enterFrame` and `exitFrameC`, whose preconditions are
re-indexed on `ancestorC`, the realization is proved from the clauses it reads
(`realize_transfer`, `realize_store`, `realize_enter`, `realize_exit`). -/
theorem r1_kernel {op : KernelOp} {c : Nat} {s s' : SC} {m : Machine.State}
    (hπ : Refinement.ParamsOK C π) (hR : ReprC π.L π.rtok s m) (hk : KInvCA s)
    (h : opStepC k op c s (.ok s')) (hob : StepObl k C ObR ObW π (kopOf op w) (s.view c) m) :
    Machine.Exec C ObR ObW (opsOf π (kopOf op w) (s.view c) m) m
        (run m (opsOf π (kopOf op w) (s.view c) m)) ∧
      ReprC π.L π.rtok s' (run m (opsOf π (kopOf op w) (s.view c) m)) := by
  obtain ⟨hw, -, -, -, -⟩ := view_facts hk c
  have hRv := (reprC_view c).1 hR
  have hfr := hk.1.1.1
  cases op with
  | transfer src dst =>
    obtain ⟨-, h⟩ := h; obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
    obtain ⟨hex, hR'⟩ := realize_transfer (C := C) (ty := π.ty) hRv hw hpre.srcUsable
      hpre.dstUsable hpre.sameShape hpre.srcInit hob.1
    exact ⟨hex, (reprC_set (s := s) (t := transferEff (s.view c) src dst)
      fun _ => SC.mem_view_F).2 hR'⟩
  | depend q x =>
    obtain ⟨-, h⟩ := h; obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
    exact ⟨.nil _, reprC_set_same rfl rfl rfl hR⟩
  | store a p =>
    obtain ⟨-, h⟩ := h; obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
    obtain ⟨hex, hR'⟩ := realize_store (C := C) (ty := π.ty) (pe := π.pe) (a := a) hRv hw
      hpre.usable hpre.leaf hob.1
    refine ⟨hex, (reprC_set fun f => ?_).2 hR'⟩
    have : (storeEff (s.view c) a p).F = (s.view c).F := by unfold storeEff; split <;> rfl
    rw [this]; exact SC.mem_view_F
  | enter ps ls =>
    obtain ⟨-, h⟩ := h; obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
    obtain ⟨hex, hR'⟩ := realize_enter (C := C) (ObR := ObR) (ObW := ObW) (ps := ps) hRv hw
      hpre.localsOK hπ.1 hπ.2.1 hob.2
    have hpush := enter_push (ps := ps) (ls := ls) hfr hpre.callerLive
    refine ⟨hex, reprC_of_flat rfl (fun f => ?_) hR'⟩
    rw [hpush.mem]
    show f ∈ s.nF :: (s.view c).F ↔ _
    rw [List.mem_cons, SC.mem_view_F]
  | exit =>
    obtain ⟨-, h⟩ := h; obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
    have hFv : (s.view c).F ≠ [] := by
      intro he
      have hc : s.stk c ≠ [] := fun e => hpre.hasCaller (by rw [e]; rfl)
      obtain ⟨f, hf⟩ := List.exists_mem_of_ne_nil _ hc
      have := (SC.mem_view_F (c := c)).2 (SC.mem_frames_of hf)
      rw [he] at this; cases this
    obtain ⟨hex, hR'⟩ := realize_exit (C := C) (ObR := ObR) (ObW := ObW) hRv hw hFv hπ.2.2
    exact ⟨hex, reprC_of_flat rfl
      (fun f => (exitEffC_pop hfr.nodup hpre.hasCaller).view_tail hfr.nodup) hR'⟩
  | derive => exact r1_viewStep hπ hR hk h (fun _ h => viewOp_F h (fun _ _ e => by cases e)
      (fun _ _ e => by cases e) (fun _ _ e => by cases e) (fun _ _ e => by cases e)
      (fun e => by cases e)) hob
  | split => exact r1_viewStep hπ hR hk h (fun _ h => viewOp_F h (fun _ _ e => by cases e)
      (fun _ _ e => by cases e) (fun _ _ e => by cases e) (fun _ _ e => by cases e)
      (fun e => by cases e)) hob
  | release => exact r1_viewStep hπ hR hk h (fun _ h => viewOp_F h (fun _ _ e => by cases e)
      (fun _ _ e => by cases e) (fun _ _ e => by cases e) (fun _ _ e => by cases e)
      (fun e => by cases e)) hob
  | read => exact r1_viewStep hπ hR hk h (fun _ h => viewOp_F h (fun _ _ e => by cases e)
      (fun _ _ e => by cases e) (fun _ _ e => by cases e) (fun _ _ e => by cases e)
      (fun e => by cases e)) hob
  | write => exact r1_viewStep hπ hR hk h (fun _ h => viewOp_F h (fun _ _ e => by cases e)
      (fun _ _ e => by cases e) (fun _ _ e => by cases e) (fun _ _ e => by cases e)
      (fun e => by cases e)) hob
  | writeShared => exact r1_viewStep hπ hR hk h (fun _ h => viewOp_F h (fun _ _ e => by cases e)
      (fun _ _ e => by cases e) (fun _ _ e => by cases e) (fun _ _ e => by cases e)
      (fun e => by cases e)) hob
  | pin => exact r1_viewStep hπ hR hk h (fun _ h => viewOp_F h (fun _ _ e => by cases e)
      (fun _ _ e => by cases e) (fun _ _ e => by cases e) (fun _ _ e => by cases e)
      (fun e => by cases e)) hob
  | unpin => exact r1_viewStep hπ hR hk h (fun _ h => viewOp_F h (fun _ _ e => by cases e)
      (fun _ _ e => by cases e) (fun _ _ e => by cases e) (fun _ _ e => by cases e)
      (fun e => by cases e)) hob
  | endUse => exact r1_viewStep hπ hR hk h (fun _ h => viewOp_F h (fun _ _ e => by cases e)
      (fun _ _ e => by cases e) (fun _ _ e => by cases e) (fun _ _ e => by cases e)
      (fun e => by cases e)) hob
  | free => exact r1_viewStep hπ hR hk h (fun _ h => viewOp_F h (fun _ _ e => by cases e)
      (fun _ _ e => by cases e) (fun _ _ e => by cases e) (fun _ _ e => by cases e)
      (fun e => by cases e)) hob
  | alloc => exact r1_viewStep hπ hR hk h (fun _ h => viewOp_F h (fun _ _ e => by cases e)
      (fun _ _ e => by cases e) (fun _ _ e => by cases e) (fun _ _ e => by cases e)
      (fun e => by cases e)) hob

/-- R1 for the transfer phases of the by-value composite (WC4 C5.2; Spec 1 §63, §82.2, §82.3):
from a state whose yielded form satisfies the kernel invariant without the anchor orders
(`KBase`, the invariant carried phase by phase in `Ern.Concurrency.TransferPreserve`), each phase
is realized by `transferOps` on the view of the creating context, and `ReprC` is kept. -/
theorem realize_vals {fin : S3} {c f : Nat} {ps : List Nat} :
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
    have hyw := (view_facts_base hk c).1
    have hRy : Refinement.Repr π.L π.rtok ((yieldEff t ps f).view c) m :=
      repr_congr ((reprC_view c).1 hR) rfl rfl rfl fun _ => Iff.rfl
    have hu : ∀ q, ((yieldEff t ps f).view c).Usable q ↔ (t.view c).Usable q := fun q =>
      S3.Usable.congr (s' := (yieldEff t ps f).view c) (s := t.view c) rfl rfl rfl
    obtain ⟨hex₁, hR₁⟩ := realize_transfer (C := C) (ty := π.ty) hRy hyw
      ((hu _).2 hpre.srcUsable) ((hu _).2 hpre.dstUsable) hpre.sameShape hpre.srcInit hob₁
    have hR₁' : ReprC π.L π.rtok (transferEffC t c v.1 v.2)
        (run m (transferOps π.L π.ty m (t.view c) v.1 v.2)) :=
      (reprC_set (s := t) (t := transferEff (t.view c) v.1 v.2) fun _ => SC.mem_view_F).2
        (repr_congr hR₁ rfl rfl rfl fun _ => Iff.rfl)
    have hk₁ : KBase (yieldEff (transferEffC t c v.1 v.2) ps f) :=
      transfers_base t [v] ⟨hpre, trivial⟩ hk
        (fun w hw => hown w (by rw [List.mem_singleton.1 hw]; exact List.mem_cons_self ..)) hp
    obtain ⟨hex₂, hR₂⟩ := realize_vals (transferEffC t c v.1 v.2) vs _ hrest hk₁
      (fun w hw => transfer_frameOwned (hown w (List.mem_cons_of_mem _ hw)))
      (fun a ha y hy => by
        obtain ⟨y₀, hy₀, e⟩ := transfer_frame_held hy
        obtain ⟨g, hg⟩ := hp a ha y₀ hy₀
        exact ⟨g, by rw [e ⟨g, hg⟩, hg]⟩) hR₁' hob₂
    rw [run_append]
    exact ⟨exec_append hex₁ hex₂, hR₂⟩

/-- **R1** (WC4 C2, C4–C8, C13–C18, C25; Spec 1 §82 preamble, §82.2–§82.5, §20.3), at the grain of
abstract steps: the realization of a labelled step of one context is a sequence of raw steps run
without interference from the other contexts. For every labelled step `LStep k L lbl st st'` and
every memory state `m` with `ReprC` of `st.1`, under the obligations of the parameters
(`Refinement.ParamsOK`), the kernel invariant `KInvCA` of `st.1` and the obligations of the step
(`StepOblC`, explicit), the realization of `lbl` is an execution of `ok` raw steps from `m` to a
state related to `st'.1` by `ReprC`. -/
theorem r1_lstep {L : MutexLayout} {lbl : Label} {st st' : SC × SyncReg} {m : Machine.State}
    (hπ : Refinement.ParamsOK C π) (hR : ReprC π.L π.rtok st.1 m) (hk : KInvCA st.1)
    (h : LStep k L lbl st st') (hob : StepOblC k C ObR ObW π w lbl st.1 m) :
    Machine.Exec C ObR ObW (realize π w lbl st.1 m) m (run m (realize π w lbl st.1 m)) ∧
      ReprC π.L π.rtok st'.1 (run m (realize π w lbl st.1 m)) := by
  cases h with
  | kernel h => exact r1_kernel hπ hR hk h hob
  | @spawn s s' reg c ps ls h =>
    obtain ⟨-, h⟩ := h; obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
    obtain ⟨hw, -, -, -, -⟩ := view_facts hk c
    obtain ⟨hex, hR'⟩ := realize_enter (C := C) (ObR := ObR) (ObW := ObW) (ps := ps)
      ((reprC_view c).1 hR) hw hpre.localsOK hπ.1 hπ.2.1 hob.2
    have hpush := spawn_push (ps := ps) (ls := ls) hk.1.1.1 hpre.creatorLive
    refine ⟨hex, reprC_of_flat rfl (fun f => ?_) hR'⟩
    rw [hpush.mem]
    show f ∈ s.nF :: (s.view c).F ↔ _
    rw [List.mem_cons, SC.mem_view_F]
  | @spawnVal s s' reg c ps ls vs h =>
    obtain ⟨-, h⟩ := h; obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
    obtain ⟨hob, hlay⟩ := hob
    simp only [realize] at hob ⊢
    obtain ⟨hob₁, hob₂⟩ := (along_append (p := Obl ObR ObW)).1 hob
    obtain ⟨hw, -, -, -, -⟩ := view_facts hk c
    obtain ⟨hex₁, hR₁⟩ := realize_enter (C := C) (ObR := ObR) (ObW := ObW) (ps := [])
      ((reprC_view c).1 hR) hw hpre.localsOK hπ.1 hπ.2.1 hlay
    have hpush := spawn_push (ps := []) (ls := ls) hk.1.1.1 hpre.creatorLive
    have hR₁' : ReprC π.L π.rtok (spawnCreate s c ls) _ := reprC_of_flat rfl (fun f => by
      show f ∈ (enterEff (s.view c) [] ls).F ↔ f ∈ (spawnEff s c [] ls).frames
      rw [hpush.mem]
      show f ∈ s.nF :: (s.view c).F ↔ _
      rw [List.mem_cons, SC.mem_view_F]) hR₁
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
    obtain ⟨hex₂, hR₂⟩ := realize_vals (π := π) (spawnCreate s c ls) vs _ hpre.transfers hb₀
      (fun v hv => spawn_frameOwned (hpre.freshDst v hv)) hframe hR₁' hob₂
    rw [run_append]
    exact ⟨exec_append hex₁ hex₂, reprC_yield hR₂⟩
  | @terminate s s' reg c h =>
    obtain ⟨-, h⟩ := h; obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
    obtain ⟨hw, -, -, -, -⟩ := view_facts hk c
    have hfr := hk.1.1.1
    have hFv : (s.view c).F ≠ [] := by
      intro he
      have hc : s.stk c ≠ [] := fun e => by have := hpre.initialOnly; rw [e] at this; cases this
      obtain ⟨f, hf⟩ := List.exists_mem_of_ne_nil _ hc
      have := (SC.mem_view_F (c := c)).2 (SC.mem_frames_of hf)
      rw [he] at this; cases this
    have hpar : s.ctxParent c ≠ none := fun e => by
      have := hpre.hasParent; rw [e] at this; exact this
    obtain ⟨hex, hR'⟩ := realize_exit (C := C) (ObR := ObR) (ObW := ObW)
      ((reprC_view c).1 hR) hw hFv hπ.2.2
    exact ⟨hex, reprC_of_flat rfl
      (fun f => (termEffC_pop hfr.nodup hpre.initialOnly hpar).view_tail hfr.nodup) hR'⟩
  | join h => cases h; exact ⟨.nil _, hR⟩
  | deriveSync h =>
    obtain ⟨-, h⟩ := h; obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
    exact ⟨.nil _, reprC_set_same rfl rfl rfl hR⟩
  | newMutex h => obtain ⟨-, -, rfl⟩ := h; exact ⟨.nil _, hR⟩
  | acquire h =>
    obtain ⟨-, -, -, -, -, rfl⟩ := h
    exact ⟨.nil _, reprC_set_same rfl rfl rfl hR⟩
  | unlock h =>
    obtain ⟨-, e, g, -, -, -, -, -, rfl⟩ := h
    refine ⟨.nil _, reprC_set_same ?_ ?_ ?_ hR⟩ <;> unfold releaseEff <;> split <;> rfl
  | resetLock h => obtain ⟨-, -, -, -, -, -, rfl⟩ := h; exact ⟨.nil _, hR⟩

end R1

end Ern.Concurrency
