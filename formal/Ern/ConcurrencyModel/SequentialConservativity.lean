import Ern.ConcurrencyModel.FrameAncestry

/-!
# Theorem 1: sequential conservativity (C2, C24)

Theorem 1 of `formal/DESIGN.md`, Milestone 4, target theorems:

* C24 is carried by the statements on states whose only live context is the initial one
  (`SC.Sole`): the five state-level requirements (`sole_conservativity`): preconditions and
  outcomes coincide, projected effects coincide, authority exercise retains the Spec 1
  definition, sequential ancestry is recovered, the sequential invariants correspond; and the
  last paragraph of C24, a history involving additional contexts does not return to an invalid
  single-context authority state (`no_invalid_sole_return`, the additional contexts having
  terminated);
* the statements on `SC.Single` (one context in all) are the special case of histories without
  `spawn`: `sequential_conservativity` of `sole_conservativity`, `no_invalid_single_return` of
  `no_invalid_sole_return`;
* the reachable sequential domain under inherited operations corresponds to the sequential domain
  of Spec 1, in both directions (`sequential_domain`, `sequential_domain_converse`);
* the two verification obligations of C2: the registry is an external argument of
  `K_C.SyncAuthorized` (`registry_external`, `registry_none_no_deriveSync`), and `K.Satisfiable`
  of a context-executed allocation is evaluated on the view of the executing context
  (`satisfiable_on_view`); and the projection of `K_C` is `K` (`projection_libKC`).
-/

namespace Ern.ConcurrencyModel

open Ern.MemoryModel.Access

/-- **Theorem 1** (C24, C2) on a single-context state with the frame structure `FramesC`, the
special case of `sole_conservativity` where the state has one context in all: for every inherited
operation O1–O16 executed by the context,

1. preconditions and outcomes coincide with Spec 1 on the projection `SC.toS3`, outcome by
   outcome;
2. an `ok` outcome is a single-context state whose projection is the Spec 1 effect;
3. authority exercise retains the Spec 1 definition: the view on which the operations read
   `ExercisableAt` (C2) is the projection itself;
4. sequential ancestry is recovered: `ancestorC` is `ancestor` of Spec 1 §39 on the stack;
5. the sequential invariants correspond: `KInvC` is `FramesC` with `KInv` of Spec 1 §57 on the
   projection.

Fragment: single-context states (`SC.Single`) satisfying `FramesC`. -/
theorem sequential_conservativity {k : K} {s : SC} (hs : s.Single) (hfr : FramesC s) :
    (∀ op : KernelOp, (∀ o, opStepC k op 0 s o → op.Step k s.toS3 (omap SC.toS3 o)) ∧
      (∀ o₃, op.Step k s.toS3 o₃ → ∃ o, opStepC k op 0 s o ∧ omap SC.toS3 o = o₃)) ∧
    (∀ (op : KernelOp) (s' : SC), opStepC k op 0 s (.ok s') →
      s'.Single ∧ op.Step k s.toS3 (.ok s'.toS3)) ∧
    s.view 0 = s.toS3 ∧
    (∀ g f, s.ancestorC g f ↔ ancestor (s.stk 0) g f) ∧
    (KInvC s ↔ FramesC s ∧ KInv s.toS3) :=
  ⟨fun op => conservative_op hs.sole hfr op, fun _ _ h => conservative_ok hs hfr h,
    single_view hs.sole, single_ancestorC hs.sole (single_decreasing hs.sole hfr),
    single_kInvC hs.sole⟩

/-- **Theorem 1** (C24: "The reachable sequential domain under inherited operations must
correspond to the sequential domain of Spec 1 under the stated state correspondence"; "the
applicable sequential invariants are preserved"): every run of inherited operations executed by
the initial context from the initial state of Spec 1 §47 reaches a single-context state whose
projection is reachable in Spec 1 and which satisfies `KInvC`. The converse is
`sequential_domain_converse`. Under `DDSound` (Spec 1 §80) and well-formed statics (Spec 1 §47). -/
theorem sequential_domain {ks : KShared} {L : MutexLayout} {statics : Statics} {lbls : List Label}
    {st' : SC × SyncReg × ArenaReg} (hdd : DDSound ks.toK) (hst : StaticsOK statics)
    (h : LRun ks L (SC.ofS3 (S3.init statics), [], []) lbls st')
    (hlab : ∀ l ∈ lbls, ∃ op, l = .kernel 0 op) :
    st'.1.Single ∧ Reachable ks.toK statics st'.1.toS3 ∧ KInvC st'.1 := by
  have key : ∀ {st st' : SC × SyncReg × ArenaReg} {lbls : List Label},
      LRun ks L st lbls st' → (∀ l ∈ lbls, ∃ op, l = .kernel 0 op) →
      st.1.Single ∧ Reachable ks.toK statics st.1.toS3 ∧ KInvCA st.1 →
      st'.1.Single ∧ Reachable ks.toK statics st'.1.toS3 ∧ KInvCA st'.1 := by
    intro st st' lbls h hl hp
    induction h with
    | nil => exact hp
    | @cons st st₁ st₂ lbl lbls hs _ ih =>
      obtain ⟨op, rfl⟩ := hl _ (List.mem_cons_self ..)
      refine ih (fun l hm => hl l (List.mem_cons_of_mem _ hm)) ?_
      obtain ⟨hsg, hr, hk⟩ := hp
      have hk' := lstep_kInvCA hdd hs hk
      cases hs with
      | kernel hop =>
        obtain ⟨hsg', hst'⟩ := conservative_ok hsg hk.1.1.1 hop
        exact ⟨hsg', hr.step (kstep_iff.2 ⟨op, hst'⟩), hk'⟩
  obtain ⟨hk0, -⟩ := init_inv hdd hst L
  obtain ⟨hsg, hr, hk⟩ := key h hlab ⟨⟨_, rfl⟩, by rw [toS3_ofS3]; exact .init, hk0⟩
  exact ⟨hsg, hr, hk.1⟩

/-- **Theorem 1**, special case of the histories without `spawn` (C24): along every run of the
labelled step relation from the initial state of Spec 1 §47 (any contexts, libraries and atomic
cases, without trace restriction), a reached single-context state (`SC.Single`, one context in
all) satisfies the frame structure and the kernel
invariant of Spec 1 §57 on its projection, under `DDSound` (Spec 1 §80) and well-formed statics
(Spec 1 §47). The last paragraph of C24 ("A transition history involving additional contexts must
not return to an invalid single-context authority state") is carried by
`no_invalid_sole_return`. -/
theorem no_invalid_single_return {ks : KShared} {L : MutexLayout} {statics : Statics}
    {lbls : List Label} {st' : SC × SyncReg × ArenaReg} (hdd : DDSound ks.toK)
    (hst : StaticsOK statics) (h : LRun ks L (SC.ofS3 (S3.init statics), [], []) lbls st')
    (hs : st'.1.Single) : FramesC st'.1 ∧ KInv st'.1.toS3 := by
  have key : ∀ {st st' : SC × SyncReg × ArenaReg} {lbls : List Label},
      LRun ks L st lbls st' → KInvCA st.1 → KInvCA st'.1 := by
    intro st st' lbls h hk
    induction h with
    | nil => exact hk
    | cons hs _ ih => exact ih (lstep_kInvCA hdd hs hk)
  exact (single_kInvC hs.sole).1 (key h (init_inv hdd hst L).1).1

/-- Appending a labelled step to a run. -/
theorem LRun.snoc {ks : KShared} {L : MutexLayout} {st st₁ st₂ : SC × SyncReg × ArenaReg}
    {lbls : List Label} {lbl : Label} (h : LRun ks L st lbls st₁) (hs : LStep ks L lbl st₁ st₂) :
    LRun ks L st (lbls ++ [lbl]) st₂ := by
  induction h with
  | nil => exact .cons hs .nil
  | cons h₁ _ ih => exact .cons h₁ (ih hs)

/-- `KInvCA` along every run (C23), under `DDSound` (Spec 1 §80). -/
theorem lrun_kInvCA {ks : KShared} {L : MutexLayout} {st st' : SC × SyncReg × ArenaReg}
    {lbls : List Label} (hdd : DDSound ks.toK) (h : LRun ks L st lbls st') (hk : KInvCA st.1) :
    KInvCA st'.1 := by
  induction h with
  | nil => exact hk
  | cons hs _ ih => exact ih (lstep_kInvCA hdd hs hk)

/-- **Theorem 1** (C24: "The reachable sequential domain under inherited operations must
correspond to the sequential domain of Spec 1 under the stated state correspondence"), converse of
`sequential_domain`: every state reachable in Spec 1 (§57) from the initial state of §47 is the
projection of a single-context state reached from the initial state, with empty registries, by a
run of inherited operations executed by the initial context. Under `DDSound` (Spec 1 §80) and
well-formed statics (Spec 1 §47), as `sequential_domain`. -/
theorem sequential_domain_converse {ks : KShared} {L : MutexLayout} {statics : Statics} {t : S3}
    (hdd : DDSound ks.toK) (hst : StaticsOK statics) (h : Reachable ks.toK statics t) :
    ∃ lbls s', LRun ks L (SC.ofS3 (S3.init statics), [], []) lbls (s', [], []) ∧
      (∀ l ∈ lbls, ∃ op, l = .kernel 0 op) ∧ s'.Single ∧ s'.toS3 = t := by
  induction h with
  | init => exact ⟨[], _, .nil, (fun _ h => by cases h), ⟨_, rfl⟩, toS3_ofS3 _⟩
  | @step t t' _ hk ih =>
    obtain ⟨lbls, s, hr, hl, hs, rfl⟩ := ih
    obtain ⟨op, hop⟩ := kstep_iff.1 hk
    have hfr : FramesC s := (lrun_kInvCA hdd hr (init_inv hdd hst L).1).1.1.1
    obtain ⟨o, hoC, ho⟩ := (conservative_op hs.sole hfr op).2 _ hop
    cases o with
    | ok s' =>
      cases ho
      refine ⟨lbls ++ [.kernel 0 op], s', hr.snoc (.kernel hoC), fun l hm => ?_,
        (conservative_ok hs hfr hoC).1, rfl⟩
      rcases List.mem_append.1 hm with hm | hm
      · exact hl l hm
      · exact ⟨op, List.mem_singleton.1 hm⟩
    | reject => cases ho
    | fail => cases ho

/-- A state with the frame structure `FramesC` whose only live context is the initial one
satisfies `SC.Sole` (C3: the initial context is live and its initial frame has no parent). -/
theorem sole_of_framesC {s : SC} (hfr : FramesC s) (hs : ∀ c, s.Live c → c = 0) : s.Sole := by
  have h := hfr.initial
  unfold OptP at h; split at h
  · rename_i x hx
    obtain ⟨stk, life, par⟩ := x
    obtain ⟨hl, hp⟩ := h
    simp only at hl hp; subst hl hp
    exact ⟨⟨stk, hx⟩, hs⟩
  · exact h.elim

/-- **Theorem 1** (C24, the five requirements) on a state whose only live context is the initial
one, with the frame structure `FramesC`; such a state may record terminated additional contexts.
For every inherited operation O1–O16 executed by the initial context:

1. preconditions and outcomes coincide with Spec 1 on the projection `SC.toS3`, outcome by
   outcome;
2. an `ok` outcome keeps the initial context the only live one, and its projection is the Spec 1
   effect;
3. authority exercise retains the Spec 1 definition: the view on which the operations read
   `ExercisableAt` (C2) is the projection itself;
4. sequential ancestry is recovered: `ancestorC` is `ancestor` of Spec 1 §39 on the stack;
5. the sequential invariants correspond: `KInvC` is `FramesC` with `KInv` of Spec 1 §57 on the
   projection.

Fragment: states satisfying `FramesC` whose only live context is the initial one. -/
theorem sole_conservativity {k : K} {s : SC} (hfr : FramesC s) (hl : ∀ c, s.Live c → c = 0) :
    (∀ op : KernelOp, (∀ o, opStepC k op 0 s o → op.Step k s.toS3 (omap SC.toS3 o)) ∧
      (∀ o₃, op.Step k s.toS3 o₃ → ∃ o, opStepC k op 0 s o ∧ omap SC.toS3 o = o₃)) ∧
    (∀ (op : KernelOp) (s' : SC), opStepC k op 0 s (.ok s') →
      (∀ c, s'.Live c → c = 0) ∧ op.Step k s.toS3 (.ok s'.toS3)) ∧
    s.view 0 = s.toS3 ∧
    (∀ g f, s.ancestorC g f ↔ ancestor (s.stk 0) g f) ∧
    (KInvC s ↔ FramesC s ∧ KInv s.toS3) :=
  have hs := sole_of_framesC hfr hl
  ⟨fun op => conservative_op hs hfr op, fun _ _ h =>
    ⟨(conservative_ok_sole hs hfr h).1.2, (conservative_ok_sole hs hfr h).2⟩, single_view hs,
    single_ancestorC hs (single_decreasing hs hfr), single_kInvC hs⟩

/-- **Theorem 1** (C24: "A transition history involving additional contexts must not return to an
invalid single-context authority state"): along every run of the labelled step relation from the
initial state of Spec 1 §47 (any contexts, libraries and atomic cases, without trace restriction),
a reached state whose only live context is the initial one, the additional contexts having
terminated, satisfies the frame structure and the kernel invariant of Spec 1 §57 on its
projection, under `DDSound` (Spec 1 §80) and well-formed statics (Spec 1 §47). -/
theorem no_invalid_sole_return {ks : KShared} {L : MutexLayout} {statics : Statics}
    {lbls : List Label} {st' : SC × SyncReg × ArenaReg} (hdd : DDSound ks.toK)
    (hst : StaticsOK statics) (h : LRun ks L (SC.ofS3 (S3.init statics), [], []) lbls st')
    (hl : ∀ c, st'.1.Live c → c = 0) : FramesC st'.1 ∧ KInv st'.1.toS3 := by
  have hk := (lrun_kInvCA hdd h (init_inv hdd hst L).1).1
  exact (single_kInvC (sole_of_framesC hk.1.1 hl)).1 hk

/-! ## The verification obligations of C2 -/

/-- C2: the projection of the contract `K_C` instantiated by the library is the unchanged Spec 1
contract `K`. -/
theorem projection_libKC (ks : KShared) (L : MutexLayout) : (libKC ks L).toK = ks.toK := rfl

/-- C2 (the registry is an external argument of `K_C.SyncAuthorized`, C14: "It must refer to the
same logical registry state used for the library transition"): the library instantiation holds
only for the `guarded` of a live entry of the registry it is given. Its state-dependent soundness
for `deriveSync` is theorem 4. -/
theorem registry_external (ks : KShared) (L : MutexLayout) (reg : SyncReg) (s : SC) (g f : Nat)
    (h : (libKC ks L).SyncAuthorized reg s g f) : ∃ e ∈ reg, e.guarded = g ∧ e.Live s :=
  libKC_sound ks L reg s g f h

/-- C2, C24: with a registry that has no live entry (no active concurrent mechanism), `deriveSync`
executed under the library instantiation has no `ok` outcome. -/
theorem registry_none_no_deriveSync {ks : KShared} {L : MutexLayout} {reg : SyncReg} {s : SC}
    (hnone : ∀ e ∈ reg, ¬ e.Live s) (c g : Nat) (s' : SC) :
    ¬ DeriveSyncStep (libKC ks L) reg s c g (.ok s') := fun h => by
  obtain ⟨e, he, -, hl⟩ := libKC_sound ks L reg s g _ (Guarded.ok_iff.1 h).1.authorized
  exact hnone e he hl

/-- C2 ("An inherited `K.Satisfiable` obligation for a context-executed allocation is evaluated on
the `S₃` view of the executing context"): an `ok` outcome of `alloc` executed by `c` entails
`K.Satisfiable` on the view of `c`, a `fail` outcome its negation; on a single-context state that
view is the Spec 1 state (C2: "these interpretations ... must coincide with Spec 1"). -/
theorem satisfiable_on_view {k : K} {s : SC} {c pr ow : Nat} {ls : LocalShape} :
    (∀ s', opStepC k (.alloc pr ow ls) c s (.ok s') → k.Satisfiable pr ls (s.view c)) ∧
      (opStepC k (.alloc pr ow ls) c s .fail → ¬ k.Satisfiable pr ls (s.view c)) ∧
      (s.Single → s.view 0 = s.toS3) :=
  ⟨fun _ h => alloc_ok_satisfiable h, alloc_fail_unsatisfiable, fun hs => single_view hs.sole⟩

end Ern.ConcurrencyModel
