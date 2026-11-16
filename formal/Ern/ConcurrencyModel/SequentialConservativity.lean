import Ern.ConcurrencyModel.FrameAncestry

/-!
# Theorem 1: sequential conservativity (C2, C24)

Theorem 1 of `formal/DESIGN.md`, Milestone 4, target theorems:

* the five state-level requirements of C24 on a single-context state (`sequential_conservativity`):
  preconditions and outcomes coincide, projected effects coincide, authority exercise retains the
  Spec 1 definition, sequential ancestry is recovered, the sequential invariants correspond;
* the reachable sequential domain under inherited operations corresponds to the sequential domain
  of Spec 1 (`sequential_domain`, with `reachable_single`);
* a history involving additional contexts does not return to an invalid single-context authority
  state (`no_invalid_single_return`);
* the two verification obligations of C2: the registry is an external argument of
  `K_C.SyncAuthorized` (`registry_external`, `registry_none_no_deriveSync`), and `K.Satisfiable`
  of a context-executed allocation is evaluated on the view of the executing context
  (`satisfiable_on_view`); and the projection of `K_C` is `K` (`projection_libKC`).
-/

namespace Ern.ConcurrencyModel

open Ern.MemoryModel.Access

/-- **Theorem 1** (C24, C2) on a single-context state with the frame structure `FramesC`: for
every inherited operation O1–O16 executed by the context,

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
  ⟨fun op => conservative_op hs hfr op, fun _ _ h => conservative_ok hs hfr h, single_view hs,
    single_ancestorC hs (single_decreasing hs hfr), single_kInvC hs⟩

/-- **Theorem 1** (C24: "The reachable sequential domain under inherited operations must
correspond to the sequential domain of Spec 1 under the stated state correspondence"; "the
applicable sequential invariants are preserved"): every run of inherited operations executed by
the initial context from the initial state of Spec 1 §47 reaches a single-context state whose
projection is reachable in Spec 1 and which satisfies `KInvC`; conversely every state reachable in
Spec 1 is such a projection (`reachable_single`). Under `DDSound` (Spec 1 §80) and well-formed
statics (Spec 1 §47). -/
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

/-- **Theorem 1** (C24: "A transition history involving additional contexts must not return to an
invalid single-context authority state"): along every run of the labelled step relation from the
initial state of Spec 1 §47 (any contexts, libraries and atomic cases, without trace
restriction), a reached single-context state satisfies the frame structure and the kernel
invariant of Spec 1 §57 on its projection, under `DDSound` (Spec 1 §80) and well-formed statics
(Spec 1 §47). -/
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
  exact (single_kInvC hs).1 (key h (init_inv hdd hst L).1).1

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
  ⟨fun _ h => alloc_ok_satisfiable h, alloc_fail_unsatisfiable, single_view⟩

end Ern.ConcurrencyModel
