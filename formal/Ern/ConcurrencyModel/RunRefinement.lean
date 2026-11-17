import Ern.ConcurrencyModel.StepRefinement

/-!
# Theorem 9, translated runs (C2, C24, C25, C50; `OB-C12`, abstract part)

Contexts interleave at the grain of abstract steps: the raw operations of one labelled step run in
the memory machine of Spec 1 Parts II–III without interference from the other contexts. Every
statement below is about this fragment only.

* `TransRun`: the translated runs, on the model of `Refinement.SimRun`: parameters fixed once for
  the run, the initial state with the obligations of the creations and writes of the statics, then
  each labelled step under its obligations (`StepOblC`), followed by its raw operations
  (`rawOps`). No trace restriction, no invariant hypothesis on the states of the run.
* `refinement_run` (9b), `step_no_ub`, `run_no_ub` (9c), `rawOps_sole`, `transRun_simRun` (9d).

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
  step stay hypotheses of the translated run;
* any absence of race.
-/

namespace Ern.ConcurrencyModel

open Ern.MemoryModel Ern.MemoryModel.Access Ern.MemoryModel.Refinement

/-! ## Translated runs (Spec 1 §20.3, §82 preamble) -/

/-- Translated runs from the initial state of Spec 1 §47 (one context, empty registries; C3,
C12), with the contract `ks`, the mutex layout `ML`, the deallocation compatibility `C`, the
obligations `ObR`, `ObW` and the parameters `π` fixed once for the run (Spec 1 §20.3 ¶3, §82; as
`Refinement.SimRun`): the initial state with the creations and writes of the statics, under their
obligations (`Refinement.repr_init`); then each labelled step `LStep` with the written
representation `w` it carries, taken under the obligations of that step (`StepOblC`), followed by
its raw operations (`rawOps`). The index lists the steps with their written representations and
the raw operations performed, in order. No trace restriction and no invariant hypothesis on the
states of the run: they are reached (`lrun_kInvCA`). -/
inductive TransRun {Ty : Type} (ks : KShared) (ML : MutexLayout) (C : Nat → Nat → Prop)
    (ObR : Machine.ReadOblSpec Ty) (ObW : Machine.WriteOblSpec Ty) (statics : Statics)
    (π : Params Ty) :
    List (Label × WriteRepr) → List (Machine.Op Ty) → SC × SyncReg × ArenaReg → Machine.State →
      Prop where
  | init : StaticsOK statics →
      NewLayout π.L (S3.init statics).P 0 0 π.geom (rootIdx (statics.map (·.1))) →
      OblAlong ObR ObW (run Machine.State.empty (allocOps (Ty := Ty) π.pl π.geom π.rtok 0
        Machine.State.empty (rootIdx (statics.map (·.1))))) (writeOps (run Machine.State.empty
          (allocOps (Ty := Ty) π.pl π.geom π.rtok 0 Machine.State.empty
            (rootIdx (statics.map (·.1))))) π.L π.ty π.ival (initLeaves statics)) →
      TransRun ks ML C ObR ObW statics π [] (initOps π.pl π.geom π.rtok π.L π.ty π.ival statics)
        (SC.ofS3 (S3.init statics), [], [])
        (run Machine.State.empty (initOps π.pl π.geom π.rtok π.L π.ty π.ival statics))
  | step {tr : List (Label × WriteRepr)} {ops : List (Machine.Op Ty)} {lbl : Label}
      {w : WriteRepr} {st st' : SC × SyncReg × ArenaReg} {m : Machine.State} :
      TransRun ks ML C ObR ObW statics π tr ops st m → LStep ks ML lbl st st' →
      StepOblC ks.toK C ObR ObW π w lbl st m →
      TransRun ks ML C ObR ObW statics π (tr ++ [(lbl, w)]) (ops ++ rawOps π w lbl st m) st'
        (run m (rawOps π w lbl st m))

/-- The statics of a translated run are well formed (Spec 1 §47; `TransRun.init`). -/
theorem TransRun.staticsOK {Ty : Type} {ks : KShared} {ML : MutexLayout} {C : Nat → Nat → Prop}
    {ObR : Machine.ReadOblSpec Ty} {ObW : Machine.WriteOblSpec Ty} {statics : Statics}
    {π : Params Ty} {tr : List (Label × WriteRepr)} {ops : List (Machine.Op Ty)}
    {st : SC × SyncReg × ArenaReg} {m : Machine.State}
    (h : TransRun ks ML C ObR ObW statics π tr ops st m) : StaticsOK statics := by
  induction h with
  | init hst _ _ => exact hst
  | step _ _ _ ih => exact ih

/-! ## Theorem 9b: simulation of the translated runs -/

/-- The labels without raw operation carry no obligation: their obligation is the parametric
obligation of an empty sequence (Spec 1 §20.3; `rawOps`): `join`, `deriveSync`, `newMutex`,
`acquire`, `unlock`, `resetLock`, `newArena` and `reset` hold `StepOblC` in every state. The other
obligations of `StepOblC` (the parametric obligations `ObR`, `ObW` of reads and writes, Spec 1 §15,
§16, §20.3; the layout `NewLayout` of new places, §82.1, §23; the instantiation `FreeCompatInst` of
`K.FreeCompat`, §82.4) do not follow from `ParamsOK`, the invariants and the transition: `ObR`,
`ObW`, the layout and `K.FreeCompat` are free parameters of the run. -/
theorem stepOblC_without_raw_ops {Ty : Type} (k : K) (C : Nat → Nat → Prop)
    (ObR : Machine.ReadOblSpec Ty) (ObW : Machine.WriteOblSpec Ty) (π : Params Ty)
    (w : WriteRepr) (st : SC × SyncReg × ArenaReg) (m : Machine.State) (c d g i st₀ int : Nat) :
    StepOblC k C ObR ObW π w (.join c d) st m ∧ StepOblC k C ObR ObW π w (.deriveSync c g) st m ∧
      StepOblC k C ObR ObW π w (.newMutex c g) st m ∧
      StepOblC k C ObR ObW π w (.acquire c i) st m ∧ StepOblC k C ObR ObW π w (.unlock c i) st m ∧
      StepOblC k C ObR ObW π w (.resetLock c i) st m ∧
      StepOblC k C ObR ObW π w (.newArena c st₀ int) st m ∧
      StepOblC k C ObR ObW π w (.reset c i) st m := by
  refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, ?_, ?_⟩
  · show OblAlong ObR ObW m (rawOps π w (.newArena c st₀ int) st m)
    rw [(rawOps_arena_nil π w st m c st₀ int i).1]; trivial
  · show OblAlong ObR ObW m (rawOps π w (.reset c i) st m)
    rw [(rawOps_arena_nil π w st m c st₀ int i).2]; trivial

/-- **Theorem 9b**, simulation of the translated runs (C2, C4–C8, C13–C19, C25, C37–C39, C50;
Spec 1 §82 preamble, §9 ¶9, §57; `OB-C12`, abstract part), at the grain of abstract steps:
contexts interleave at the grain of abstract steps, and the raw operations of one step run without
interference from the other contexts. Under `DDSound(K)` (Spec 1 §80) and the obligations of the
parameters (`ParamsOK`, Spec 1 §9 ¶11, §17.2, §82.5), for every translated run, the memory state is
reached from the empty state by the execution of `ok` raw steps listed by the run, it is related to
the concurrent state by `ReprC`, and the concurrent state is reached by an `LRun` from the initial
state of Spec 1 §47 with the labels of the run. Fragment: translated runs, every label, no trace
restriction.

What it does not say: that an arbitrary `LRun` is translatable for given parameters. A legal
abstract transition does not guarantee that fixed parameters allow each raw operation: the
obligations of each step (`StepOblC`) stay hypotheses of the translated run, step by step; only
those of the labels without raw operation are derived (`stepOblC_without_raw_ops`). The existence
of parameters for every admitted run is the layout and ABI obligation that `formal/DESIGN.md`
keeps open ("Layout interface").

Not proven by this statement:

* the physical realization of the concurrent operations; the physical accesses to the controller
  of the mutex are not modelled: the non-atomic initialization write of C13 and the atomic
  operations of C48 for `acquire`, `unlock` and `resetLock` (`OB-C05`);
* the indivisibility of atomic units and the compilation of memory orders (C38, C39, C50;
  `OB-C12`, concrete part; `OB-C27`); a raw read followed by a raw write does not show it;
* the consistency of an observed value with the bytes read (C31–C34);
* the correspondence of physical events, the internal order of compound steps, `rf`, `mo`, `hb`
  (C26–C34, `OB-C20`);
* that an admitted abstract execution is realizable for given parameters;
* any absence of race. -/
theorem refinement_run {Ty : Type} {ks : KShared} {ML : MutexLayout} {C : Nat → Nat → Prop}
    {ObR : Machine.ReadOblSpec Ty} {ObW : Machine.WriteOblSpec Ty} {statics : Statics}
    {π : Params Ty} {tr : List (Label × WriteRepr)} {ops : List (Machine.Op Ty)}
    {st : SC × SyncReg × ArenaReg} {m : Machine.State} (hdd : DDSound ks.toK)
    (hπ : ParamsOK C π) (h : TransRun ks ML C ObR ObW statics π tr ops st m) :
    Machine.Exec C ObR ObW ops Machine.State.empty m ∧ ReprC π.L π.rtok st.1 m ∧
      LRun ks ML (SC.ofS3 (S3.init statics), [], []) (tr.map Prod.fst) st := by
  have key : (Machine.Exec C ObR ObW ops Machine.State.empty m ∧ ReprC π.L π.rtok st.1 m ∧
      LRun ks ML (SC.ofS3 (S3.init statics), [], []) (tr.map Prod.fst) st) ∧ KInvCA st.1 := by
    induction h with
    | init hst hlay hob =>
      obtain ⟨hex, hR⟩ := repr_init (C := C) hst hπ.1 hπ.2.1 hlay hob
      exact ⟨⟨hex, reprC_ofS3.2 hR, .nil⟩, (init_inv hdd hst ML).1⟩
    | step _ hs hob ih =>
      obtain ⟨⟨hex, hR, hrun⟩, hk⟩ := ih
      obtain ⟨hex', hR'⟩ := refinement_step hπ hR hk hs hob
      refine ⟨⟨exec_append hex hex', hR', ?_⟩, lstep_kInvCA hdd hs hk⟩
      rw [List.map_append]
      exact hrun.snoc hs
  exact key.1

/-- The states of a translated run satisfy the re-indexed kernel invariant (Spec 1 §57; C20, C23;
`lrun_kInvCA`), under `DDSound(K)` (Spec 1 §80). -/
theorem TransRun.kInvCA {Ty : Type} {ks : KShared} {ML : MutexLayout} {C : Nat → Nat → Prop}
    {ObR : Machine.ReadOblSpec Ty} {ObW : Machine.WriteOblSpec Ty} {statics : Statics}
    {π : Params Ty} {tr : List (Label × WriteRepr)} {ops : List (Machine.Op Ty)}
    {st : SC × SyncReg × ArenaReg} {m : Machine.State} (hdd : DDSound ks.toK)
    (hπ : ParamsOK C π) (h : TransRun ks ML C ObR ObW statics π tr ops st m) : KInvCA st.1 :=
  (lrun_kInvCA hdd (refinement_run hdd hπ h).2.2 (init_inv hdd h.staticsOK ML).1)

/-! ## Theorem 9c: no `ub` at the grain of abstract steps -/

/-- The raw operation `o` has no `ub` outcome in the state `s` (Spec 1 §20.1 ¶2). -/
def NoUB {Ty : Type} (C : Nat → Nat → Prop) (ObR : Machine.ReadOblSpec Ty)
    (ObW : Machine.WriteOblSpec Ty) (s : Machine.State) : Machine.Op Ty → Prop
  | .read ac t => ¬ Machine.ReadStep ObR ac t s .ub
  | .write ac t w => ¬ Machine.WriteStep ObW ac t w s .ub
  | .dealloc id au => ¬ Machine.DeallocStep C id au s .ub
  | .alloc sp b sz al fa => ¬ Machine.AllocStep sp b sz al fa s .ub

/-- No raw step of an execution has a `ub` outcome where it runs (Spec 1 §20.1 ¶2–¶3: an
execution consists of `ok` steps, and each raw operation has at most one outcome). -/
theorem exec_noUB {Ty : Type} {C : Nat → Nat → Prop} {ObR : Machine.ReadOblSpec Ty}
    {ObW : Machine.WriteOblSpec Ty} {ops : List (Machine.Op Ty)} {s s' : Machine.State}
    (h : Machine.Exec C ObR ObW ops s s') : Along (NoUB C ObR ObW) s ops := by
  induction h with
  | nil => trivial
  | cons hs _ ih =>
    cases hs with
    | read h => exact And.intro (fun hu => nomatch Machine.ReadStep_det h hu) ih
    | write h =>
      obtain ⟨-, rfl⟩ := Machine.WriteStep_ok_iff.1 h
      exact And.intro (fun hu => nomatch Machine.WriteStep_det h hu) ih
    | dealloc h =>
      obtain ⟨-, rfl⟩ := Machine.DeallocStep_ok_iff.1 h
      exact And.intro (fun hu => nomatch Machine.DeallocStep_det h hu) ih
    | alloc h =>
      obtain ⟨-, rfl⟩ := Machine.AllocStep_ok_iff.1 h
      exact And.intro (fun hu => nomatch Machine.AllocStep_det h hu) ih

/-- **Theorem 9c**, one step (Spec 1 §20.1, §82; C25), at the grain of abstract steps (contexts
interleave at the grain of abstract steps): under the hypotheses of `refinement_step`, no raw
operation of `rawOps` for the step has a `ub` outcome in the state where it runs. It is about these
raw operations only and says nothing of the physical accesses that are not modelled
(`StepRefinement`, `rawSort`). -/
theorem step_no_ub {Ty : Type} {C : Nat → Nat → Prop} {ObR : Machine.ReadOblSpec Ty}
    {ObW : Machine.WriteOblSpec Ty} {π : Params Ty} {w : WriteRepr} {ks : KShared}
    {ML : MutexLayout} {lbl : Label} {st st' : SC × SyncReg × ArenaReg} {m : Machine.State}
    (hπ : ParamsOK C π) (hR : ReprC π.L π.rtok st.1 m) (hk : KInvCA st.1)
    (h : LStep ks ML lbl st st') (hob : StepOblC ks.toK C ObR ObW π w lbl st m) :
    Along (NoUB C ObR ObW) m (rawOps π w lbl st m) :=
  exec_noUB (refinement_step hπ hR hk h hob).1

/-- **Theorem 9c** (Spec 1 §20.1, §82; C25; `OB-C12`, abstract part), corollary of 9b, at the grain
of abstract steps: contexts interleave at the grain of abstract steps. Under `DDSound(K)` (Spec 1
§80) and `ParamsOK`, along every translated run, none of the raw operations of the run (the
creations and writes of the statics, then `rawOps` of each step, in order) has a `ub` outcome in the
state where it runs. It is about these raw operations only: it says nothing of the physical accesses
that are not modelled (the controller of the mutex, `OB-C05`; atomicity and memory orders, `OB-C12`
concrete part, `OB-C27`; physical events, `OB-C20`), nor of races. -/
theorem run_no_ub {Ty : Type} {ks : KShared} {ML : MutexLayout} {C : Nat → Nat → Prop}
    {ObR : Machine.ReadOblSpec Ty} {ObW : Machine.WriteOblSpec Ty} {statics : Statics}
    {π : Params Ty} {tr : List (Label × WriteRepr)} {ops : List (Machine.Op Ty)}
    {st : SC × SyncReg × ArenaReg} {m : Machine.State} (hdd : DDSound ks.toK)
    (hπ : ParamsOK C π) (h : TransRun ks ML C ObR ObW statics π tr ops st m) :
    Along (NoUB C ObR ObW) Machine.State.empty ops :=
  exec_noUB (refinement_run hdd hπ h).1

/-! ## Theorem 9d: conservativity of the raw operations (C24) -/

/-- **Theorem 9d**, one step (C24; Spec 1 §82): on a state whose only live context is the initial
one (`SC.Sole`), the raw operations of an inherited operation O1–O16 executed by context 0 are the
raw operations `Refinement.opsOf` of the memory model for the same operation on the projection
`SC.toS3`, its obligations are those of `Refinement.StepObl` on the projection, and `ReprC` is
`Repr` of the projection when the state has one context in all. -/
theorem rawOps_sole {Ty : Type} {k : K} {C : Nat → Nat → Prop} {ObR : Machine.ReadOblSpec Ty}
    {ObW : Machine.WriteOblSpec Ty} {π : Params Ty} {w : WriteRepr}
    {st : SC × SyncReg × ArenaReg} (hs : st.1.Sole) (op : KernelOp) (m : Machine.State) :
    rawOps π w (.kernel 0 op) st m = opsOf π (kopOf op w) st.1.toS3 m ∧
      (StepOblC k C ObR ObW π w (.kernel 0 op) st m ↔
        StepObl k C ObR ObW π (kopOf op w) st.1.toS3 m) ∧
      (ReprC π.L π.rtok st.1 m ↔ Repr π.L π.rtok st.1.toS3 m) := by
  refine ⟨?_, ?_, ?_⟩
  · show opsOf π (kopOf op w) (st.1.view 0) m = _
    rw [single_view hs]
  · show StepObl k C ObR ObW π (kopOf op w) (st.1.view 0) m ↔ _
    rw [single_view hs]
  · unfold ReprC
    rw [single_flat hs]

/-- **Theorem 9d** (C24; Spec 1 §82 preamble): under `DDSound(K)` (Spec 1 §80), a translated run
made of inherited operations of context 0 is a `Refinement.SimRun` of the memory model on the
projections, with the same memory state. Its states have one context in all, so the initial
context is the only live one (`SC.Sole`). -/
theorem transRun_simRun {Ty : Type} {ks : KShared} {ML : MutexLayout} {C : Nat → Nat → Prop}
    {ObR : Machine.ReadOblSpec Ty} {ObW : Machine.WriteOblSpec Ty} {statics : Statics}
    {π : Params Ty} {tr : List (Label × WriteRepr)} {ops : List (Machine.Op Ty)}
    {st : SC × SyncReg × ArenaReg} {m : Machine.State} (hdd : DDSound ks.toK)
    (h : TransRun ks ML C ObR ObW statics π tr ops st m)
    (hl : ∀ x ∈ tr, ∃ op, x.1 = .kernel 0 op) :
    SimRun ks.toK C ObR ObW statics π st.1.toS3 m ∧ st.1.Single := by
  have key : SimRun ks.toK C ObR ObW statics π st.1.toS3 m ∧ st.1.Single ∧ KInvCA st.1 := by
    induction h with
    | init hst hlay hob =>
      refine ⟨?_, ⟨_, rfl⟩, (init_inv hdd hst ML).1⟩
      rw [toS3_ofS3]
      exact .init hst hlay hob
    | @step tr ops lbl w st st' m _ hs hob ih =>
      obtain ⟨op, rfl⟩ := hl (lbl, w) (List.mem_append_right _ (List.mem_singleton_self _))
      obtain ⟨hsim, hsg, hk⟩ := ih fun x hx => hl x (List.mem_append_left _ hx)
      have hk' := lstep_kInvCA hdd hs hk
      cases hs with
      | @kernel s s' reg ar c op hop =>
        obtain ⟨hsg', hst⟩ := conservative_ok hsg hk.1.1.1 hop
        obtain ⟨hops, hobl, -⟩ := rawOps_sole (k := ks.toK) (C := C) (ObR := ObR) (ObW := ObW)
          (π := π) (w := w) (st := (s, reg, ar)) hsg.sole op m
        refine ⟨?_, hsg', hk'⟩
        rw [hops]
        exact .step hsim (opStep_kopOf.2 hst) (hobl.1 hob)
  exact ⟨key.1, key.2.1⟩

end Ern.ConcurrencyModel
