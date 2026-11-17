import Ern.ConcurrencyModel.WitnessBase

/-!
# Witnesses: the atomic step cases (C37–C40)

Each witness states its situation, its expected outcome and the clause that gives it, on the
initial state of Spec 1 §47. A rejection states its single cause: the named condition fails and
every other precondition of the clause holds; its positive twin is cited in its docstring.
-/

namespace Ern.ConcurrencyModel

open Ern.MemoryModel.Access

/-- Statics (Spec 1 §47): `0` a value `V` with four `Init` fields: `1` and `2` (`Atomic`), `3`
(`Synchronized`), `4` (`Confined`). Root authority `0` of `V`, held by frame 0. -/
def atomicStatics : Statics :=
  [((none, none, 0), true), ((some 0, none, 0), true), ((some 0, none, 0), true),
   ((some 0, none, 0), true), ((some 0, none, 0), true)]

/-- The statics are well formed (Spec 1 §47). -/
theorem atomicStatics_ok : StaticsOK atomicStatics := by decide

/-- The disciplines selected by the test contract (C35): `Atomic(4, 4)` for leaves 1 and 2,
`Synchronized` for 3, `Confined` for 4. -/
def atomicDisc (l : Nat) : Option Discipline :=
  if l = 1 ∨ l = 2 then some (.atomic 4 4) else if l = 3 then some .synchronized
  else if l = 4 then some .confined else none

/-- The test contract of the atomic witnesses: the four fields are `SharedMutable` (C35); no
composite contract (C38). -/
abbrev kAtomic : KShared := testKS [1, 2, 3, 4] atomicDisc false
/-- The same contract with a composite contract admitting every region (C38). -/
abbrev kComposite : KShared := testKS [1, 2, 3, 4] atomicDisc true

/-- Initial single-context state (Spec 1 §47). -/
def v0 : SC := SC.ofS3 (S3.init atomicStatics)

/-- A leaf that is not an `Atomic` leaf has no `Atomic` discipline (C35). -/
theorem not_atomic_disc {ks : KShared} {l : Nat} (h : ¬ AtomicLeaf ks l) :
    ¬ ∃ sz al, ks.SharedDiscipline l = some (.atomic sz al) :=
  fun ⟨_, _, e⟩ => h (by unfold AtomicLeaf; rw [e]; rfl)

/-- **Witness 6a** (C37, C40, `ok`, state unchanged): `readShared(root_V, 1, acquire)`: C37.1–C37.2
(the `read3` preconditions on the leaf), C37.3 (`SharedMutable`, `Atomic(4, 4)`), C37.4 and C40
(`acquire` is in the load row). The labelled step keeps the state and both registries for every
observed value. -/
theorem witness_6a : ReadSharedPre kAtomic v0 0 0 1 .acquire ∧
    ∀ v, LStep kAtomic mutexLayout (.readShared 0 0 1 .acquire v) (v0, [], []) (v0, [], []) :=
  have hp : ReadSharedPre kAtomic v0 0 0 1 .acquire := ⟨by decide, by decide, ⟨4, 4, rfl⟩, trivial⟩
  ⟨hp, fun _ => .readShared (.ok hp)⟩

/-- **Witness 6b** (C37, `reject`): `readShared` on the `Synchronized` leaf 3, then on the `Confined`
leaf 4. Single cause: the `Atomic` discipline of C37.3 fails; the `read3` preconditions,
`SharedMutable` and the order hold. Positive twin: `witness_6a`. -/
theorem witness_6b :
    (Read3Pre (v0.view 0) 0 [3] ∧ kAtomic.SharedMutable 3 ∧ LoadOrderOK .acquire ∧
      (¬ ∃ sz al, kAtomic.SharedDiscipline 3 = some (.atomic sz al)) ∧
      ReadSharedStep kAtomic v0 0 0 3 .acquire .reject) ∧
    (Read3Pre (v0.view 0) 0 [4] ∧ kAtomic.SharedMutable 4 ∧ LoadOrderOK .acquire ∧
      (¬ ∃ sz al, kAtomic.SharedDiscipline 4 = some (.atomic sz al)) ∧
      ReadSharedStep kAtomic v0 0 0 4 .acquire .reject) :=
  have h3 := not_atomic_disc (ks := kAtomic) (l := 3) (by decide)
  have h4 := not_atomic_disc (ks := kAtomic) (l := 4) (by decide)
  ⟨⟨by decide, by decide, trivial, h3, .reject fun hp => h3 hp.atomic⟩,
    ⟨by decide, by decide, trivial, h4, .reject fun hp => h4 hp.atomic⟩⟩

/-- **Witness 6c** (C40, `reject`): `readShared(root_V, 1, release)`. Single cause: `release` is not in
the load row of C40; the other preconditions of C37 hold. Positive twin: `witness_6a`. -/
theorem witness_6c : Read3Pre (v0.view 0) 0 [1] ∧ kAtomic.SharedMutable 1 ∧
    (∃ sz al, kAtomic.SharedDiscipline 1 = some (.atomic sz al)) ∧ ¬ LoadOrderOK .release ∧
    ReadSharedStep kAtomic v0 0 0 1 .release .reject :=
  ⟨by decide, by decide, ⟨4, 4, rfl⟩, id, .reject fun hp => hp.order⟩

/-- **Witness 6d** (C39, C40, `ok`): an atomic `writeShared(root_V, {1}, release)` store: the O11
preconditions (Spec 1 §68), a single `Atomic` leaf with `release` in the store row (C38, C40).
The step is the O11 step with its effect (theorem 8). -/
theorem witness_6d : WriteSharedCPre kAtomic v0 0 0 [1] (some .release) .store ∧
    LStep kAtomic mutexLayout (.writeShared 0 0 [1] (some .release) .store) (v0, [], [])
      (writeSharedCEff v0 0 [1], [], []) :=
  have hp : WriteSharedCPre kAtomic v0 0 0 [1] (some .release) .store :=
    ⟨by decide, .inl ⟨1, 4, 4, .release, rfl, rfl, rfl, trivial⟩, fun h => absurd rfl h⟩
  ⟨hp, .writeShared (.ok hp)⟩

/-- **Witness 6e** (C38, `reject`): `writeShared(root_V, {1, 2}, release)` over two `Atomic` leaves.
Single cause: the region has more than one `Atomic` leaf; the O11 preconditions hold and the
store needs no initialized leaf. Positive twin: `witness_6d`. -/
theorem witness_6e : WriteSharedPre kAtomic.toK (v0.view 0) 0 [1, 2] ∧ AtomicLeaf kAtomic 1 ∧
    AtomicLeaf kAtomic 2 ∧ ¬ WriteDisciplineOK kAtomic [1, 2] (some .release) .store ∧
    WriteSharedCStep kAtomic v0 0 0 [1, 2] (some .release) .store .reject :=
  have hr : WriteSharedCRel kAtomic v0 0 0 [1, 2] (some .release) .store .reject :=
    multi_atomic_rejected (l₁ := 1) (l₂ := 2) (by decide) (by decide) (by decide) (by decide)
      (by decide)
  ⟨by decide, by decide, by decide, fun hd => by
    cases hr with
    | reject hn => exact hn ⟨by decide, hd, fun h => absurd rfl h⟩, hr⟩

/-- **Witness 6f** (C38, `reject`): `writeShared(root_V, {1, 3}, release)` over an `Atomic` and a
`Synchronized` leaf, with no composite contract. Single cause: the composite contract of C38 is
missing; the classes are mixed with at most one `Atomic` leaf, and the O11 preconditions hold.
Positive twin: the same request under a contract whose composite contract admits it, `ok`. -/
theorem witness_6f : WriteSharedPre kAtomic.toK (v0.view 0) 0 [1, 3] ∧
    MixedClasses kAtomic [1, 3] ∧
    ([1, 3].filter fun l => decide (AtomicLeaf kAtomic l)).length ≤ 1 ∧
    ¬ kAtomic.CompositeContract [1, 3] (some .release) .store ∧
    WriteSharedCStep kAtomic v0 0 0 [1, 3] (some .release) .store .reject ∧
    LStep kComposite mutexLayout (.writeShared 0 0 [1, 3] (some .release) .store) (v0, [], [])
      (writeSharedCEff v0 0 [1, 3], [], []) :=
  have hm : MixedClasses kAtomic [1, 3] := by unfold MixedClasses SingleClass; decide
  have hc : ¬ kAtomic.CompositeContract [1, 3] (some .release) .store := by decide
  ⟨by decide, hm, by decide, hc, mixed_rejected hm hc,
    .writeShared (.ok ⟨by decide,
      .inr (.inr ⟨by unfold MixedClasses SingleClass; decide, by decide, rfl⟩),
      fun h => absurd rfl h⟩)⟩

/-- **Witness 6g** (C40, `reject`): a compare-and-exchange on leaf 1 with the failure order `release`.
Single cause: `release` is not in the CAS-failure row; the success order `acq_rel` is in the RMW
row. A static `reject` whatever the branch. Positive twin: `witness_6h`. -/
theorem witness_6g : RMWOrderOK .acqRel ∧ ¬ CasFailureOrderOK .release ∧
    ∀ br, CasStep kAtomic v0 0 0 1 .acqRel .release br .reject :=
  ⟨trivial, id, fun _ => .inl ⟨fun h => h.2, rfl⟩⟩

/-- **Witness 6h** (C39, C40, `ok`): a failed compare-and-exchange on leaf 1 with the success order
`acq_rel` and the failure order `acquire`: the `readShared` observation of the leaf with the
failure order (C39), state and registries unchanged, for every observed value. -/
theorem witness_6h : CasOrdersOK .acqRel .acquire ∧
    (∀ v, CasStep kAtomic v0 0 0 1 .acqRel .acquire (.failure v) (.ok v0) ↔
      ReadSharedStep kAtomic v0 0 0 1 .acquire (.ok v0)) ∧
    ∀ v, LStep kAtomic mutexLayout (.cas 0 0 1 .acqRel .acquire (.failure v)) (v0, [], [])
      (v0, [], []) :=
  have ho : CasOrdersOK .acqRel .acquire := ⟨trivial, trivial⟩
  have hp : ReadSharedPre kAtomic v0 0 0 1 .acquire := ⟨by decide, by decide, ⟨4, 4, rfl⟩, trivial⟩
  ⟨ho, fun _ => (cas_failure_case (L := mutexLayout) (reg := []) (ar := [])
      (st' := (v0, [], []))).1 ho,
    fun _ => .cas (.inr ⟨ho, .ok hp⟩)⟩

/-- **Witness 6i, C38 third paragraph, C39** (`ok`): a concurrent `writeShared(root_V, {3})` over
the `Synchronized` leaf 3, then `writeShared(root_V, {4})` over the `Confined` leaf 4, each without
a memory-order annotation: the O11 preconditions hold (Spec 1 §68), the region is of a single class
(C38) and the annotation does not apply (C39, "Applicability of atomic memory-order
annotations"). The step is the O11 step with its effect. -/
theorem witness_6i : WriteSharedCPre kAtomic v0 0 0 [3] none .store ∧
    LStep kAtomic mutexLayout (.writeShared 0 0 [3] none .store) (v0, [], [])
      (writeSharedCEff v0 0 [3], [], []) ∧
    WriteSharedCPre kAtomic v0 0 0 [4] none .store ∧
    LStep kAtomic mutexLayout (.writeShared 0 0 [4] none .store) (v0, [], [])
      (writeSharedCEff v0 0 [4], [], []) :=
  have h3 : WriteSharedCPre kAtomic v0 0 0 [3] none .store :=
    ⟨by decide, .inr (.inl ⟨rfl, rfl, .inl (by decide)⟩), fun h => absurd rfl h⟩
  have h4 : WriteSharedCPre kAtomic v0 0 0 [4] none .store :=
    ⟨by decide, .inr (.inl ⟨rfl, rfl, .inr (by decide)⟩), fun h => absurd rfl h⟩
  ⟨h3, .writeShared (.ok h3), h4, .writeShared (.ok h4)⟩

/-- **Witness 6j, C39** (`reject`): the requests of witness 6i with the memory-order annotation
`release`, which is in the store row of C40. Single cause: an annotation is supplied on
`Synchronized` (then `Confined`) storage (C39, "Applicability of atomic memory-order annotations");
the O11 preconditions hold and the region is of a single class. No labelled step. Positive twin:
witness 6i. -/
theorem witness_6j : StoreOrderOK .release ∧
    (WriteSharedPre kAtomic.toK (v0.view 0) 0 [3] ∧
      kAtomic.SharedDiscipline 3 = some .synchronized ∧
      ¬ WriteDisciplineOK kAtomic [3] (some .release) .store ∧
      WriteSharedCStep kAtomic v0 0 0 [3] (some .release) .store .reject ∧
      ∀ st', ¬ LStep kAtomic mutexLayout (.writeShared 0 0 [3] (some .release) .store)
        (v0, [], []) st') ∧
    (WriteSharedPre kAtomic.toK (v0.view 0) 0 [4] ∧ kAtomic.SharedDiscipline 4 = some .confined ∧
      ¬ WriteDisciplineOK kAtomic [4] (some .release) .store ∧
      WriteSharedCStep kAtomic v0 0 0 [4] (some .release) .store .reject ∧
      ∀ st', ¬ LStep kAtomic mutexLayout (.writeShared 0 0 [4] (some .release) .store)
        (v0, [], []) st') :=
  have k3 := (annotation_rejected (ks := kAtomic) (s := v0) (c := 0) (a := 0) (kind := .store)
    (singleClass_singleton (l := 3) (by decide)) (List.mem_singleton_self 3)).2 (.inl rfl) .release
  have k4 := (annotation_rejected (ks := kAtomic) (s := v0) (c := 0) (a := 0) (kind := .store)
    (singleClass_singleton (l := 4) (by decide)) (List.mem_singleton_self 4)).2 (.inr rfl) .release
  have ho3 : WriteSharedPre kAtomic.toK (v0.view 0) 0 [3] := by decide
  have ho4 : WriteSharedPre kAtomic.toK (v0.view 0) 0 [4] := by decide
  ⟨trivial,
    ⟨ho3, rfl, fun hd => absurd ((k3 _).1 (.ok ⟨ho3, hd, fun h => absurd rfl h⟩)) (by intro e; cases e),
      (k3 _).2 rfl, fun _ h => by
        cases h with | writeShared h => exact absurd ((k3 _).1 h) (by intro e; cases e)⟩,
    ⟨ho4, rfl, fun hd => absurd ((k4 _).1 (.ok ⟨ho4, hd, fun h => absurd rfl h⟩)) (by intro e; cases e),
      (k4 _).2 rfl, fun _ h => by
        cases h with | writeShared h => exact absurd ((k4 _).1 h) (by intro e; cases e)⟩⟩

/-- **Witness 6k, C39** (`reject`): a concurrent `writeShared(root_V, {1})` over the `Atomic` leaf 1
without a memory-order annotation. Single cause: the annotation required on `Atomic` storage is
missing (C39, "Applicability of atomic memory-order annotations"); the O11 preconditions hold and
the region is a single `Atomic` leaf. No labelled step. Positive twin: witness 6d, the same store
annotated `release`. -/
theorem witness_6k : WriteSharedPre kAtomic.toK (v0.view 0) 0 [1] ∧ AtomicLeaf kAtomic 1 ∧
    ¬ WriteDisciplineOK kAtomic [1] none .store ∧
    WriteSharedCStep kAtomic v0 0 0 [1] none .store .reject ∧
    ∀ st', ¬ LStep kAtomic mutexLayout (.writeShared 0 0 [1] none .store) (v0, [], []) st' :=
  have k1 := (annotation_rejected (ks := kAtomic) (s := v0) (c := 0) (a := 0) (kind := .store)
    (singleClass_singleton (l := 1) (by decide)) (List.mem_singleton_self 1)).1 (by decide)
  have ho : WriteSharedPre kAtomic.toK (v0.view 0) 0 [1] := by decide
  ⟨ho, by decide, fun hd => absurd ((k1 _).1 (.ok ⟨ho, hd, fun h => absurd rfl h⟩)) (by intro e; cases e),
    (k1 _).2 rfl, fun _ h => by
      cases h with | writeShared h => exact absurd ((k1 _).1 h) (by intro e; cases e)⟩

end Ern.ConcurrencyModel
