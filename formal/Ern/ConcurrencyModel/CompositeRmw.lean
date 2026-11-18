import Ern.ConcurrencyModel.RunRefinement
import Ern.ConcurrencyModel.WitnessAtomic

/-!
# The reads of a composite RMW: what the choice of `rawOps` costs (C38, C39)

`rawOps` gives an RMW, a concurrent `writeShared` of kind `rmw`, the raw reads of every leaf of
its region, then the writes of O11. C39 defines an RMW on a single `Atomic` leaf ("conditionally
reads and modifies the same initialized leaf"). For a region admitted under a separately
established composite contract (C38), the clauses do not say what the step reads: C39 leaves the
annotation of such a step to that contract, and nothing else. Reading every leaf is a choice of
formalization that the text does not establish. This module establishes what it costs, without
changing it:

* `rmw_discipline_cases`, `mixed_not_singleton`: an RMW over more than one leaf is admitted only
  under a composite contract, over mixed classes;
* `rmw_stepOblC`, `oblAlong_reads_writes`: the obligations of an RMW step are the parametric read
  obligations `ObR` of every leaf of the region, then the obligations of the O11 writes; reading
  only some leaves asks `ObR` of those leaves only, and reading none asks no `ObR`;
* `rmw_reads_realized`: the conditions of the memory machine on the reads (live allocation, range,
  initialized bytes) follow from `ReprC`, `KInvCA` and the preconditions of the step
  (`WriteSharedCPre`, with `rmwInit`), for every list of leaves of the region read;
* `composite_rmw_restricts`: the parametric obligations `ObR` of the added reads do not follow from
  them, nor from the obligations of the O11 writes: an admitted RMW over an `Atomic` leaf and a
  `Synchronized` leaf, under concrete parameters, has an execution of `ok` raw steps with the read
  of the `Atomic` leaf alone, and is the step of no translated run with the reads of both leaves.

So the results of theorem 9 hold as proved, conditional on these obligations, and the faithful
correspondence of a composite RMW stays open. These reads are an auxiliary construction of the
refinement at the grain of abstract steps: they define neither the reads nor the physical events of
a composite RMW.
-/

namespace Ern.ConcurrencyModel

open Ern.MemoryModel Ern.MemoryModel.Access Ern.MemoryModel.Refinement

/-! ## The RMW steps over more than one leaf (C38, C39) -/

/-- The discipline acceptance of an RMW (C38, C39, C40; `WriteDisciplineOK`): a single `Atomic`
leaf with an order of the RMW row, or a region of mixed classes with at most one `Atomic` leaf
admitted by a composite contract. The consistently `Synchronized` or `Confined` case is a plain
write. -/
theorem rmw_discipline_cases {ks : KShared} {region : List Nat} {ord : Option MemOrder} {v : Nat}
    (h : WriteDisciplineOK ks region ord (.rmw v)) :
    (∃ l sz al o, region = [l] ∧ ks.SharedDiscipline l = some (.atomic sz al) ∧ ord = some o ∧
      WriteOrderOK (.rmw v) o) ∨
    (MixedClasses ks region ∧ (region.filter fun l => decide (AtomicLeaf ks l)).length ≤ 1 ∧
      ks.CompositeContract region ord (.rmw v)) := by
  rcases h with h | ⟨-, e, -⟩ | h
  · exact .inl h
  · cases e
  · exact .inr h

/-- A single leaf does not combine classes (C38). So an RMW over more than one leaf is admitted
only under a composite contract (`rmw_discipline_cases`). -/
theorem mixed_not_singleton {ks : KShared} {l : Nat} : ¬ MixedClasses ks [l] := by
  rintro ⟨hd, hs⟩
  refine hs ⟨hd, fun a ha b hb => ?_⟩
  rw [List.mem_singleton.1 ha, List.mem_singleton.1 hb]

/-! ## The obligations of an RMW step (Spec 1 §15, §16, §20.3) -/

section Obl

variable {Ty : Type} {ObR : Machine.ReadOblSpec Ty} {ObW : Machine.WriteOblSpec Ty}

/-- The parametric obligations of the raw reads of a list of leaves (Spec 1 §15 ¶5, §20.3): those
of `ObR` on the access to each leaf, in the memory state where the reads start, which they leave
unchanged. -/
theorem oblAlong_readOps (m : Machine.State) (L : Layout) (ty : Nat → Ty) :
    ∀ rs : List Nat, OblAlong ObR ObW m (readOps m L ty rs) ↔
      ∀ l ∈ rs, ObR.dec m (leafAcc m L .read l) (ty l) ∧ ObR.stat m (leafAcc m L .read l) (ty l)
  | [] => by simp [readOps, Along]
  | l :: rs => by
    show (ObR.dec m _ _ ∧ ObR.stat m _ _) ∧ OblAlong ObR ObW m (readOps m L ty rs) ↔ _
    rw [oblAlong_readOps m L ty rs]
    simp only [List.mem_cons, forall_eq_or_imp]

/-- The parametric obligations of raw reads of the leaves `rs` followed by the writes of O11 on the
leaves `ws` (Spec 1 §15, §16, §20.3): `ObR` on each leaf read, and the obligations of the writes. -/
theorem oblAlong_reads_writes (m : Machine.State) (L : Layout) (ty : Nat → Ty)
    (w : WriteRepr) (rs ws : List Nat) :
    OblAlong ObR ObW m (readOps m L ty rs ++ writeOps m L ty w ws) ↔
      (∀ l ∈ rs, ObR.dec m (leafAcc m L .read l) (ty l) ∧
        ObR.stat m (leafAcc m L .read l) (ty l)) ∧
      OblAlong ObR ObW m (writeOps m L ty w ws) := by
  show Along (Obl ObR ObW) m (_ ++ _) ↔ _
  rw [along_append, run_readOps]
  exact and_congr (oblAlong_readOps m L ty rs) Iff.rfl

/-- The obligations of an RMW step (`StepOblC`; Spec 1 §15, §16, §20.3): the parametric read
obligations `ObR` of every leaf of the region, in the memory state before the step, then the
obligations of the O11 writes. Reading only the leaves `rs` would ask
`(∀ l ∈ rs, ObR …) ∧ OblAlong … (writeOps …)` (`oblAlong_reads_writes`); reading none, the
obligations of the writes alone. -/
theorem rmw_stepOblC {k : K} {C : Nat → Nat → Prop} {π : Params Ty} {w : WriteRepr}
    {c a v : Nat} {region : List Nat} {ord : Option MemOrder} {st : SC × SyncReg × ArenaReg}
    {m : Machine.State} :
    StepOblC k C ObR ObW π w (.writeShared c a region ord (.rmw v)) st m ↔
      (∀ l ∈ region, ObR.dec m (leafAcc m π.L .read l) (π.ty l) ∧
        ObR.stat m (leafAcc m π.L .read l) (π.ty l)) ∧
      OblAlong ObR ObW m (writeOps m π.L π.ty w region) :=
  oblAlong_reads_writes m π.L π.ty w region region

/-- The parametric obligations of writes whose obligation holds everywhere (Spec 1 §16 ¶4). -/
theorem oblAlong_writes_of {s2 : Machine.State} {L : Layout} {ty : Nat → Ty} {w : WriteRepr}
    (h : ∀ s ac t v, ObW.dec s ac t v ∧ ObW.stat s ac t v) :
    ∀ (ws : List Nat) (s : Machine.State), OblAlong ObR ObW s (writeOps s2 L ty w ws)
  | [], _ => trivial
  | _ :: ws, _ => ⟨h _ _ _ _, oblAlong_writes_of h ws _⟩

end Obl

/-! ## The machine conditions of the reads follow (Spec 1 §15, §66, §82.2) -/

section Realized

variable {Ty : Type} {C : Nat → Nat → Prop} {ObR : Machine.ReadOblSpec Ty}
  {ObW : Machine.WriteOblSpec Ty} {π : Params Ty} {w : WriteRepr}

/-- For an RMW (C38, C39), the raw reads of any list `rs` of leaves of the region, as O9, then the
raw operations of O11, form an execution of `ok` raw steps and `ReprC` holds after them, under the
parametric obligations of those reads and writes: the conditions of the memory machine on the reads
(live allocation, range, initialized bytes; Spec 1 §15) follow from `ReprC`, `KInvCA`, the O11
preconditions and `rmwInit` of `WriteSharedCPre`. `rmw_rawOps` is the case `rs = region`. Only the
parametric obligations differ with the list read. -/
theorem rmw_reads_realized {ks : KShared} {s : SC} {c a : Nat} {region rs : List Nat}
    {ord : Option MemOrder} {v : Nat} {m : Machine.State} (hR : ReprC π.L π.rtok s m)
    (hk : KInvCA s) (hpre : WriteSharedCPre ks s c a region ord (.rmw v))
    (hsub : ∀ l ∈ rs, l ∈ region)
    (hob : OblAlong ObR ObW m (readOps m π.L π.ty rs ++ writeOps m π.L π.ty w region)) :
    Machine.Exec C ObR ObW (readOps m π.L π.ty rs ++ writeOps m π.L π.ty w region) m
        (run m (readOps m π.L π.ty rs ++ writeOps m π.L π.ty w region)) ∧
      ReprC π.L π.rtok (writeSharedCEff s c region)
        (run m (readOps m π.L π.ty rs ++ writeOps m π.L π.ty w region)) := by
  have hc : s.Live c := SC.live_of_exercisable hpre.o11.exercisable
  obtain ⟨hw, -⟩ := PreservationAux.view_facts hk hc
  have hRv := (reprC_view hc).1 hR
  obtain ⟨hob₁, hob₂⟩ := (along_append (p := Obl ObR ObW)).1 hob
  have hrd : Read3Pre (s.view c) a rs :=
    ⟨fun l hl => hpre.o11.usable l (hsub l hl),
      fun l hl => hpre.rmwInit (fun e => by cases e) l (hsub l hl), hpre.o11.exercisable,
      fun l hl => hpre.o11.effectivePresent l (hsub l hl),
      fun l hl => hpre.o11.depsValid l (hsub l hl)⟩
  obtain ⟨hex₁, hrun, -⟩ := r6_read (C := C) (ty := π.ty) (rtok := π.rtok)
    (s3' := s.view c) hRv hw (.ok hrd) hob₁
  rw [hrun] at hob₂ hex₁
  have hst : WriteSharedStep ks.toK a region (s.view c) (.ok (write3Eff (s.view c) region)) :=
    .ok hpre.o11
  obtain ⟨hex₂, hR'⟩ := r2_writeShared (C := C) (rtok := π.rtok) hRv hw hst hob₂
  rw [run_append, hrun]
  exact ⟨exec_append hex₁ hex₂, (reprC_set (s := s) (t := write3Eff (s.view c) region)
    fun _ => SC.mem_view_F hc).2 hR'⟩

end Realized

/-! ## Translated runs of one step (Spec 1 §20.3; `TransRun`) -/

section Single

variable {Ty : Type} {ks : KShared} {ML : MutexLayout} {C : Nat → Nat → Prop}
  {ObR : Machine.ReadOblSpec Ty} {ObW : Machine.WriteOblSpec Ty} {statics : Statics}
  {π : Params Ty}

/-- A translated run with no step is at the initial state (`TransRun.init`). -/
theorem TransRun.nil_init {tr : List (Label × WriteRepr)} {ops : List (Machine.Op Ty)}
    {st : SC × SyncReg × ArenaReg} {m : Machine.State}
    (h : TransRun ks ML C ObR ObW statics π tr ops st m) (htr : tr = []) :
    st = (SC.ofS3 (S3.init statics), [], []) ∧
      m = run Machine.State.empty (initOps π.pl π.geom π.rtok π.L π.ty π.ival statics) := by
  cases h with
  | init => exact ⟨rfl, rfl⟩
  | step => simp at htr

/-- A translated run of one step `(lbl, w)` takes it from the initial state under its obligations
in the initial memory state (`TransRun.step`). -/
theorem TransRun.single_obl {lbl : Label} {w : WriteRepr} {ops : List (Machine.Op Ty)}
    {st : SC × SyncReg × ArenaReg} {m : Machine.State}
    (h : TransRun ks ML C ObR ObW statics π [(lbl, w)] ops st m) :
    StepOblC ks.toK C ObR ObW π w lbl (SC.ofS3 (S3.init statics), [], [])
      (run Machine.State.empty (initOps π.pl π.geom π.rtok π.L π.ty π.ival statics)) := by
  generalize htr : [(lbl, w)] = tr at h
  cases h with
  | init => cases htr
  | @step tr' _ lbl' w' _ _ _ h' _ hob =>
    have e : tr' = [] := by
      cases tr' with
      | nil => rfl
      | cons x xs => simp at htr
    subst e
    simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq, and_true] at htr
    obtain ⟨rfl, rfl⟩ := htr
    obtain ⟨rfl, rfl⟩ := h'.nil_init rfl
    exact hob

end Single

/-! ## The read obligations of a composite RMW restrict the translated runs -/

open Ern.MemoryModel.Refinement.Runs

/-- Test read obligation (Spec 1 §15 ¶5, §20.3 ¶1: an explicit predicate of the execution
context): a raw read is admitted only at the type `true`, the type that `πRmw` gives to the
`Atomic` leaf 1. -/
abbrev obRAtomic : Machine.ReadOblSpec Bool := ⟨fun _ _ t => t = true, fun _ _ _ => True⟩

/-- Test write obligation (Spec 1 §16 ¶4, §20.3 ¶1): every raw write is admitted. -/
abbrev obWAll : Machine.WriteOblSpec Bool := ⟨fun _ _ _ _ => True, fun _ _ _ _ => True⟩

/-- Decidability of the test obligations (Spec 1 §20.3 ¶3). -/
instance : ∀ s o, Decidable (Obl obRAtomic obWAll s o) := fun _ o => by
  cases o <;> unfold Obl <;> infer_instance

/-- Test parameters for the statics of the atomic witnesses (Spec 1 §82): those of `piOf` (layout,
tokens, placement, geometry, reference encoding, initial bytes), with the leaf types `true` for the
`Atomic` leaf 1 and `false` for the others. -/
def πRmw : Params Bool :=
  ⟨autoL v0.P [], fun r => 100 + r, topPlacement, autoG v0.P [], fun l => decide (l = 1), pe8,
    fun l i => ((10 * l + i).toUInt8, none)⟩

/-- The memory state of the initial state of a translated run with `πRmw` (Spec 1 §47,
`repr_init`). -/
def mRmw : Machine.State :=
  run Machine.State.empty (initOps πRmw.pl πRmw.geom πRmw.rtok πRmw.L πRmw.ty πRmw.ival
    atomicStatics)

/-- The RMW of the witness (C38, C39): `writeShared(root_V, {1, 3}, acq_rel)` of kind `rmw` over
the `Atomic` leaf 1 and the `Synchronized` leaf 3, under the composite contract of `kComposite`. -/
def lblRmw : Label := .writeShared 0 0 [1, 3] (some .acqRel) (.rmw 0)

/-- **Composite RMW reads** (C38, C39; `rawOps`, `StepOblC`): the read obligations that `rawOps`
adds for a composite RMW do not follow from the preconditions of the step nor from the obligations
of its writes; they restrict the translated runs. Under the test contract `kComposite`, whose
composite contract admits every region, from the initial state `v0` of the atomic witnesses, with
the parameters `πRmw` (`ParamsOK`), the read obligation `obRAtomic` and the write obligation
`obWAll`:

* the RMW `lblRmw` over the `Atomic` leaf 1 and the `Synchronized` leaf 3 is an admitted step, and
  `v0` is the state of a translated run;
* with the raw read of leaf 1 alone, then the O11 writes, the obligations hold for every written
  representation, the raw operations form an execution of `ok` raw steps and `ReprC` holds after
  them;
* with the raw reads of leaves 1 and 3, as `rawOps` gives them, the obligations of the step fail
  for every written representation (the read of leaf 3), so the step is the step of no translated
  run.

The test contract admitting the step does not establish that such a composite contract is
justified under C38–C40. -/
theorem composite_rmw_restricts :
    LStep kComposite mutexLayout lblRmw (v0, [], []) (writeSharedCEff v0 0 [1, 3], [], []) ∧
    ParamsOK (· = ·) πRmw ∧
    TransRun kComposite mutexLayout (· = ·) obRAtomic obWAll atomicStatics πRmw []
      (initOps πRmw.pl πRmw.geom πRmw.rtok πRmw.L πRmw.ty πRmw.ival atomicStatics) (v0, [], [])
      mRmw ∧
    (∀ w : WriteRepr,
      OblAlong obRAtomic obWAll mRmw
        (readOps mRmw πRmw.L πRmw.ty [1] ++ writeOps mRmw πRmw.L πRmw.ty w [1, 3]) ∧
      Machine.Exec (· = ·) obRAtomic obWAll
        (readOps mRmw πRmw.L πRmw.ty [1] ++ writeOps mRmw πRmw.L πRmw.ty w [1, 3]) mRmw
        (run mRmw (readOps mRmw πRmw.L πRmw.ty [1] ++ writeOps mRmw πRmw.L πRmw.ty w [1, 3])) ∧
      ReprC πRmw.L πRmw.rtok (writeSharedCEff v0 0 [1, 3])
        (run mRmw (readOps mRmw πRmw.L πRmw.ty [1] ++ writeOps mRmw πRmw.L πRmw.ty w [1, 3]))) ∧
    (∀ w : WriteRepr,
      ¬ StepOblC kComposite.toK (· = ·) obRAtomic obWAll πRmw w lblRmw (v0, [], []) mRmw) ∧
    ∀ (w : WriteRepr) (ops : List (Machine.Op Bool)) (st : SC × SyncReg × ArenaReg)
      (m : Machine.State),
      ¬ TransRun kComposite mutexLayout (· = ·) obRAtomic obWAll atomicStatics πRmw
        [(lblRmw, w)] ops st m := by
  have hpre : WriteSharedCPre kComposite v0 0 0 [1, 3] (some .acqRel) (.rmw 0) :=
    ⟨by decide, .inr (.inr ⟨by unfold MixedClasses SingleClass; decide, by decide, rfl⟩),
      fun _ => by decide⟩
  have hπ : ParamsOK (· = ·) πRmw := ⟨topPlacement_ok, autoG_ok _ _, fun _ => rfl⟩
  have hlay : NewLayout πRmw.L (S3.init atomicStatics).P 0 0 πRmw.geom
      (rootIdx (atomicStatics.map (·.1))) := by decide
  have hinit : OblAlong obRAtomic obWAll (run Machine.State.empty (allocOps (Ty := Bool) πRmw.pl
      πRmw.geom πRmw.rtok 0 Machine.State.empty (rootIdx (atomicStatics.map (·.1)))))
      (writeOps (run Machine.State.empty (allocOps (Ty := Bool) πRmw.pl πRmw.geom πRmw.rtok 0
        Machine.State.empty (rootIdx (atomicStatics.map (·.1))))) πRmw.L πRmw.ty πRmw.ival
        (initLeaves atomicStatics)) :=
    oblAlong_writes_of (fun _ _ _ _ => ⟨trivial, trivial⟩) _ _
  have hrun : TransRun kComposite mutexLayout (· = ·) obRAtomic obWAll atomicStatics πRmw []
      (initOps πRmw.pl πRmw.geom πRmw.rtok πRmw.L πRmw.ty πRmw.ival atomicStatics) (v0, [], [])
      mRmw := .init atomicStatics_ok hlay hinit
  have hR : ReprC πRmw.L πRmw.rtok v0 mRmw :=
    reprC_ofS3.2 (repr_init (C := (· = ·)) atomicStatics_ok hπ.1 hπ.2.1 hlay hinit).2
  have hk : KInvCA v0 := (init_inv (k := kComposite.toK) (fun _ _ h => h.elim) atomicStatics_ok
    mutexLayout).1
  have hnot : ∀ w : WriteRepr,
      ¬ StepOblC kComposite.toK (· = ·) obRAtomic obWAll πRmw w lblRmw (v0, [], []) mRmw :=
    fun w h => absurd ((rmw_stepOblC.1 h).1 3 (by decide)).1 (by decide)
  refine ⟨.writeShared (.ok hpre), hπ, hrun, fun w => ?_, hnot, fun w ops st m h => ?_⟩
  · have hob : OblAlong obRAtomic obWAll mRmw
        (readOps mRmw πRmw.L πRmw.ty [1] ++ writeOps mRmw πRmw.L πRmw.ty w [1, 3]) :=
      (oblAlong_reads_writes mRmw πRmw.L πRmw.ty w [1] [1, 3]).2
        ⟨fun l hl => by rw [List.mem_singleton.1 hl]; exact ⟨rfl, trivial⟩,
          oblAlong_writes_of (fun _ _ _ _ => ⟨trivial, trivial⟩) _ _⟩
    exact ⟨hob, rmw_reads_realized hR hk hpre (fun l hl => by
      rw [List.mem_singleton.1 hl]; exact List.mem_cons_self ..) hob⟩
  · exact hnot w h.single_obl

end Ern.ConcurrencyModel
