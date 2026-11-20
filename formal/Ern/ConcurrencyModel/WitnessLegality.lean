import Ern.ConcurrencyModel.WitnessAtomic
import Ern.ConcurrencyModel.Classification

/-!
# Witnesses of theorem 11 (C35–C42)

Witnesses D1–D12 on the initial state `v0` of the atomic witnesses (Spec 1 §47): field `1` is a
nonzero `Atomic` leaf (A), `2` a second one (A′), `3` `Synchronized` (S), `4` `Confined` (C), `5`
`SharedMutable` without class (U), `6` an `Atomic` leaf of zero physical size (Z). The contracts
are those of `WitnessAtomic`: `kAtomic` (no composite contract), `kComposite` (admits `{A, S}` in
the declared order S then A, and `{S, C}` in the order S then C), `kAll` (admits every region).

Each rejection names its single cause and its admitted twin; each statement gives its expected
result and the clause that gives it. Limit: the physical size of a non-atomic leaf is not
represented, so the zero-physical-size `Synchronized` or `Confined` store of C38 has no witness.
-/

namespace Ern.ConcurrencyModel

open Ern.MemoryModel.Access

/-- **Witness D1** (C38, C39, C40, `ok`): under `kComposite`, the store `writeShared(root_V, {A, S},
release)` is admitted: the O11 preconditions hold (Spec 1 §68), the region combines classes with
one `Atomic` leaf (C38), the composite contract gives the declared order S then A, which
enumerates the region (C28, C38; reading 7 of `Atomic`), and `release` is in the store row (C39,
C40). The step is the O11 step with its effect. -/
theorem witness_d1 : kComposite.CompositeContract [1, 3] = some [3, 1] ∧
    CompositeAdmits kComposite [1, 3] ∧
    WriteSharedCPre kComposite v0 0 0 [1, 3] (some .release) .store ∧
    LStep kComposite mutexLayout (.writeShared 0 0 [1, 3] (some .release) .store) (v0, [], [])
      (writeSharedCEff v0 0 [1, 3], [], []) :=
  have hp : WriteSharedCPre kComposite v0 0 0 [1, 3] (some .release) .store :=
    ⟨by decide, by decide, fun h => absurd rfl h⟩
  ⟨rfl, by decide, hp, .writeShared (.ok hp)⟩

/-- **Witness D2** (C39, C40, `reject`): the request of D1 annotated `acquire`. Single cause:
`acquire` is not in the store row of C40; every other condition of D1 holds. Positive twin: D1. -/
theorem witness_d2 : ¬ StoreOrderOK .acquire ∧
    WriteSharedPre kComposite.toK (v0.view 0) 0 [1, 3] ∧ CompositeAdmits kComposite [1, 3] ∧
    WriteSharedCStep kComposite v0 0 0 [1, 3] (some .acquire) .store .reject :=
  ⟨id, by decide, by decide,
    atomic_annotation_rejected (ks := kComposite) (l := 1) (by decide) (by decide) id
      compositeOrder⟩

/-- **Witness D3** (C39, `reject`): the request of D1 without annotation. Single cause: the
annotation required by the `Atomic` leaf of a mixed-class region is missing (C39: "whether it is
the entire region or part of a mixed-class composite"); the composite contract admits the region.
Positive twin: D1. -/
theorem witness_d3 : WriteSharedPre kComposite.toK (v0.view 0) 0 [1, 3] ∧
    CompositeAdmits kComposite [1, 3] ∧
    WriteSharedCStep kComposite v0 0 0 [1, 3] none .store .reject :=
  ⟨by decide, by decide,
    atomic_annotation_rejected (ks := kComposite) (l := 1) (by decide) (by decide) id
      compositeOrder⟩

/-- **Witness D4** (C38, C39): under `kComposite`, the store over `{S, C}` without annotation is
`ok` (a mixed-class region without `Atomic` leaf, admitted in the declared order S then C); the
same store annotated `release` is `reject`, single cause: an annotation where no `Atomic` leaf
applies (C39). -/
theorem witness_d4 : kComposite.CompositeContract [3, 4] = some [3, 4] ∧
    WriteSharedCPre kComposite v0 0 0 [3, 4] none .store ∧
    LStep kComposite mutexLayout (.writeShared 0 0 [3, 4] none .store) (v0, [], [])
      (writeSharedCEff v0 0 [3, 4], [], []) ∧
    StoreOrderOK .release ∧
    WriteSharedCStep kComposite v0 0 0 [3, 4] (some .release) .store .reject :=
  have hp : WriteSharedCPre kComposite v0 0 0 [3, 4] none .store :=
    ⟨by decide, by decide, fun h => absurd rfl h⟩
  ⟨rfl, hp, .writeShared (.ok hp), trivial,
    no_atomic_annotation_rejected (ks := kComposite) (by decide) compositeOrder⟩

/-- **Witness D5** (C39, `reject`): under `kComposite`, the RMW `acq_rel` over `{A, S}`. Single
cause: an RMW region that is not exactly one `Atomic` leaf (C39: "No composite RMW read of other
leaves is implied"), although the composite contract admits the region for a store. Positive twins:
D1 (the store over the same region), and the RMW `acq_rel` over `{A}`, which is `ok` (C39: one
initialized `Atomic` leaf, an order in the RMW row). -/
theorem witness_d5 : CompositeAdmits kComposite [1, 3] ∧ RMWOrderOK .acqRel ∧
    WriteSharedCStep kComposite v0 0 0 [1, 3] (some .acqRel) (.rmw 0) .reject ∧
    WriteSharedCPre kComposite v0 0 0 [1] (some .acqRel) (.rmw 0) ∧
    LStep kComposite mutexLayout (.writeShared 0 0 [1] (some .acqRel) (.rmw 0)) (v0, [], [])
      (writeSharedCEff v0 0 [1], [], []) :=
  have hp : WriteSharedCPre kComposite v0 0 0 [1] (some .acqRel) (.rmw 0) :=
    ⟨by decide, ⟨1, 4, 4, rfl, rfl, by decide, trivial⟩, fun _ l hl => by
      rw [List.mem_singleton.1 hl]; decide⟩
  ⟨by decide, trivial,
    rmw_region_rejected (ks := kComposite) (fun ⟨l, sz, al, e, _⟩ => by cases e) compositeOrder,
    hp, .writeShared (.ok hp)⟩

/-- **Witness D6** (C39, `reject`): the RMW over the `Synchronized` leaf `{S}` without annotation.
Single cause: the kind RMW on a non-`Atomic` single leaf (C39); the request is otherwise the store
of witness 6i, which is `ok`. -/
theorem witness_d6 : WriteSharedCStep kAtomic v0 0 0 [3] none (.rmw 0) .reject ∧
    WriteSharedCPre kAtomic v0 0 0 [3] none .store :=
  ⟨rmw_region_rejected (ks := kAtomic) (fun ⟨l, sz, al, e, hd⟩ => by
      cases e; simp [testKS, atomicDisc] at hd) (fun _ => none),
    witness_6i.1⟩

/-- **Witness D7** (C39, "Empty region"):

1. the store on the empty region without annotation is `ok` with the state unchanged, the O11
   preconditions holding for the access authority;
2. with the annotation `release`, `reject`;
3. of kind RMW, `reject`;
4. through authority `5`, which does not exist and is not exercisable (Spec 1 §68.2), `reject`.

Each rejection has item 1 as twin. -/
theorem witness_d7 : WriteSharedCPre kAtomic v0 0 0 [] none .store ∧
    LStep kAtomic mutexLayout (.writeShared 0 0 [] none .store) (v0, [], []) (v0, [], []) ∧
    WriteSharedCStep kAtomic v0 0 0 [] (some .release) .store .reject ∧
    WriteSharedCStep kAtomic v0 0 0 [] (some .acqRel) (.rmw 0) .reject ∧
    (¬ (v0.view 0).ExercisableAt 5 .observe ∧
      WriteSharedCStep kAtomic v0 0 5 [] none .store .reject) :=
  have hp : WriteSharedCPre kAtomic v0 0 0 [] none .store :=
    ⟨by decide, by decide, fun h => absurd rfl h⟩
  have hx : ¬ (v0.view 0).ExercisableAt 5 .observe := by decide
  ⟨hp, by
    have h := LStep.writeShared (L := mutexLayout) (reg := []) (ar := []) (Guarded.ok hp)
    rwa [writeSharedCEff_nil] at h,
    no_atomic_annotation_rejected (ks := kAtomic) (by simp) (fun _ => none),
    rmw_region_rejected (ks := kAtomic) (fun ⟨_, _, _, e, _⟩ => nomatch e) (fun _ => none),
    hx, .reject fun hp => hx hp.o11.exercisable⟩

/-- **Witness D8** (C35, C51 item 2(e)):

1. under `kAll`, whose composite contract admits every region, the store over `{A, U}` annotated
   `release` is `reject`: U has no class (C35: "even when a composite contract would otherwise
   admit the region"); positive twin: the store over `{A, S}` annotated `release` under `kAll`,
   `ok`;
2. the store over `{U}` without annotation is `reject` under the concurrent evaluation (C35) and
   `ok` as the inherited O11 step (Spec 1 §68): the converse of theorem 11d fails. -/
theorem witness_d8 : CompositeAdmits kAll [1, 5] ∧
    WriteSharedCStep kAll v0 0 0 [1, 5] (some .release) .store .reject ∧
    WriteSharedCPre kAll v0 0 0 [1, 3] (some .release) .store ∧
    WriteSharedCStep kAtomic v0 0 0 [5] none .store .reject ∧
    opStepC kAtomic.toK (.writeShared 0 [5]) 0 v0 (.ok (writeSharedCEff v0 0 [5])) ∧
    LStep kAtomic mutexLayout (.kernel 0 (.writeShared 0 [5])) (v0, [], [])
      (writeSharedCEff v0 0 [5], [], []) :=
  have hk : opStepC kAtomic.toK (.writeShared 0 [5]) 0 v0 (.ok (writeSharedCEff v0 0 [5])) :=
    ⟨_, .ok (by decide), rfl⟩
  ⟨by decide,
    unclassified_rejected (ks := kAll) (l := 5) (by decide) rfl (fun r => some r.eraseDups),
    ⟨by decide, by decide, fun h => absurd rfl h⟩,
    unclassified_rejected (ks := kAtomic) (l := 5) (by decide) rfl (fun _ => none),
    hk, .kernel hk⟩

/-- **Witness D9** (C38, `reject`): under `kAll`, the store over `{A, A′, S}` annotated `release`.
Single cause: two `Atomic` leaves (C38; C39: a composite contract cannot "admit more than one
`Atomic` leaf"), although the composite contract admits the region. Positive twin: the store over
`{A, S}` under `kAll` (witness D8, item 1). -/
theorem witness_d9 : CompositeAdmits kAll [1, 2, 3] ∧
    WriteSharedCStep kAll v0 0 0 [1, 2, 3] (some .release) .store .reject :=
  ⟨by decide, multi_atomic_rejected_any (ks := kAll) (l₁ := 1) (l₂ := 2) (by decide) (by decide)
    (by decide) (by decide) (by decide) (fun r => some r.eraseDups)⟩

/-- **Witness D10** (C38, `reject`; reading 6 of `Atomic`): `readShared(root_V, Z, acquire)` and
the store over `{Z}` annotated `relaxed`. Single cause: Z is an `Atomic` leaf of zero physical
size; every other condition holds. Positive twins: 6a (`readShared` of A) and 6d (the store over
`{A}`). -/
theorem witness_d10 : ZeroAtomic kAtomic 6 ∧ Read3Pre (v0.view 0) 0 [6] ∧
    ReadSharedStep kAtomic v0 0 0 6 .acquire .reject ∧
    WriteSharedPre kAtomic.toK (v0.view 0) 0 [6] ∧
    WriteSharedCStep kAtomic v0 0 0 [6] (some .relaxed) .store .reject :=
  have hz : ZeroAtomic kAtomic 6 := ⟨4, rfl⟩
  ⟨hz, by decide, readShared_outcomes.2.2.2.2.2 hz, by decide,
    zero_atomic_rejected (ks := kAtomic) (l := 6) (by decide) hz (fun _ => none)⟩

/-- **Witness D11** (C38, C28; reading 7 of `Atomic`): the request of D1 under `kAtomic`, whose
composite contract admits no region, is `reject` (witness 6f), and under `kComposite`, which gives
its declared order, `ok` (D1): the single cause is the composite contract. -/
theorem witness_d11 : WriteSharedCStep kAtomic v0 0 0 [1, 3] (some .release) .store .reject ∧
    WriteSharedCStep kComposite v0 0 0 [1, 3] (some .release) .store
      (.ok (writeSharedCEff v0 0 [1, 3])) :=
  ⟨witness_6f.2.2.2.2, .ok witness_d1.2.2.1⟩

/-- Witness 6k with the inherited O11 step (C35, theorem 11d): the concurrent store over the
`Atomic` leaf `{A}` without annotation is `reject` (witness 6k), while the inherited O11 step over
`{A}` is `ok` (Spec 1 §68): the converse of theorem 11d fails. -/
theorem witness_6k_kernel : WriteSharedCStep kAtomic v0 0 0 [1] none .store .reject ∧
    LStep kAtomic mutexLayout (.kernel 0 (.writeShared 0 [1])) (v0, [], [])
      (writeSharedCEff v0 0 [1], [], []) :=
  ⟨witness_6k.2.2.2.1, .kernel ⟨_, .ok (by decide), rfl⟩⟩

/-- `o := derive(root_V, Observe, {A})`, authority 1, held by frame 0 (O1). -/
def v1 : SC := v0.set (deriveEff (v0.view 0) 0 [1] .observe)

/-- **Witness D12** (C42: "This is a rule of the safe concurrent interface, not a new O9/O10
kernel precondition"):

1. after `derive(root_V, Observe, {A})`, the `read3` of the `Atomic` leaf A through the `Observe`
   authority 1 is kernel-`ok` (Spec 1 §66), and the rule of C42 does not hold: authority 1 is not
   exercisable in `Modify`;
2. in the initial state, the `read3` of A through the root authority, exercisable in `Modify` with
   effective `Modify` on A, is kernel-`ok` and the rule holds. -/
theorem witness_d12 : opStepC kAtomic.toK (.derive 0 [1] .observe) 0 v0 (.ok v1) ∧
    effective v1.flat 1 1 = some .observe ∧
    opStepC kAtomic.toK (.read 1 [1]) 0 v1 (.ok v1) ∧
    ¬ AtomicOrdinaryOK kAtomic v1 (.kernel 0 (.read 1 [1])) ∧
    opStepC kAtomic.toK (.read 0 [1]) 0 v0 (.ok v0) ∧
    AtomicOrdinaryOK kAtomic v0 (.kernel 0 (.read 0 [1])) := by
  have hx : ¬ (v1.view 0).ExercisableAt 1 .modify := by decide
  refine ⟨⟨_, .ok (by decide), rfl⟩, by decide, ⟨_, .ok (by decide), rfl⟩,
    fun h => hx (h 1 (List.mem_singleton_self _) (by decide)).1, ⟨_, .ok (by decide), rfl⟩, ?_⟩
  intro l hl _
  rw [List.mem_singleton.1 hl]
  exact ⟨by decide, by decide⟩

end Ern.ConcurrencyModel
