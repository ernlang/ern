import Ern.ConcurrencyModel.RunRefinement

/-!
# The RMW steps (C38, C39)

`rawOps` gives an RMW, a concurrent `writeShared` of kind `rmw`, the raw reads of the leaves of its
region, then the writes of O11. The region of an admitted step of kind RMW is exactly one `Atomic`
leaf, and any other region is `reject` (C39; `rmw_region_rejected` of `Legality`). So the reads of
an RMW are those of its single leaf:

* `rmw_discipline_cases`, `rmw_single_atomic`: an admitted RMW, and every concurrent `ok` step of
  kind RMW, has for region a single `Atomic` leaf, not of zero physical size (C38), with an
  annotation of the RMW row of C40;
* `mixed_not_singleton`: a single leaf does not combine classes (C38);
* `rmw_stepOblC`, `oblAlong_reads_writes`: the obligations of an RMW step are the parametric read
  obligations `ObR` of the leaf, then the obligations of the O11 writes;
* `rmw_reads_realized`: the conditions of the memory machine on the reads (live allocation, range,
  initialized bytes) follow from `ReprC`, `KInvCA` and the preconditions of the step
  (`WriteSharedCPre`, with `rmwInit`).

An RMW over a mixed-class region, which the earlier edition left to a composite contract, is a
`reject` (witness D5).
-/

namespace Ern.ConcurrencyModel

open Ern.MemoryModel Ern.MemoryModel.Access Ern.MemoryModel.Refinement

/-! ## An RMW has a single `Atomic` leaf (C38, C39) -/

/-- The discipline acceptance of an RMW (C39, rules on the kind and the annotation; C38;
`WriteDisciplineOK`): its region is a single `Atomic` leaf, not of zero physical size, with an
annotation of the RMW row of C40. -/
theorem rmw_discipline_cases {ks : KShared} {region : List Nat} {ord : Option MemOrder} {v : Nat}
    (h : WriteDisciplineOK ks region ord (.rmw v)) :
    ∃ l sz al o, region = [l] ∧ ks.SharedDiscipline l = some (.atomic sz al) ∧ sz ≠ 0 ∧
      ord = some o ∧ WriteOrderOK (.rmw v) o := by
  obtain ⟨l, sz, al, e1, e2, hsz, hann⟩ := h
  cases ord with
  | none => exact hann.elim
  | some o => exact ⟨l, sz, al, o, e1, e2, hsz, rfl, hann⟩

/-- **Every concurrent `ok` RMW has a single `Atomic` leaf** (C39; C38): the region of a concurrent
`writeShared` of kind RMW with an `ok` outcome is one leaf, of class `Atomic`, not of zero physical
size. Fragment: every state, every contract `K_C`. -/
theorem rmw_single_atomic {ks : KShared} {s s' : SC} {c a v : Nat} {region : List Nat}
    {ord : Option MemOrder} (h : WriteSharedCStep ks s c a region ord (.rmw v) (.ok s')) :
    ∃ l sz al, region = [l] ∧ ks.SharedDiscipline l = some (.atomic sz al) ∧ sz ≠ 0 := by
  obtain ⟨hpre, -⟩ := Guarded.ok_iff.1 h
  obtain ⟨l, sz, al, -, e1, e2, hsz, -, -⟩ := rmw_discipline_cases hpre.discipline
  exact ⟨l, sz, al, e1, e2, hsz⟩

/-- A single leaf does not combine classes (C38). -/
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
obligations `ObR` of the leaves of the region, in the memory state before the step, then the
obligations of the O11 writes. The region of an admitted RMW is a single leaf
(`rmw_discipline_cases`). -/
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
preconditions and `rmwInit` of `WriteSharedCPre`. `rmw_rawOps` is the case `rs = region`; the
region of an admitted RMW is a single leaf (`rmw_discipline_cases`). -/
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

end Ern.ConcurrencyModel
