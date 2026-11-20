import Ern.ConcurrencyModel.AtomicCases
import Ern.ConcurrencyModel.EventGraph

/-!
# Theorem 11: legality of the shared-discipline operations and of memory orders (C35–C40)

Theorem 11 of `formal/DESIGN.md`, Milestone 4, target theorems, on the authority machine; no event
is involved. Fragment: every state, every contract `K_C`, unless stated.

* 11a (C35, C38, C39): the outcomes of the concurrent `writeShared`, one rejection statement per
  row of the discipline acceptance `WriteDisciplineOK`, each sufficient whatever the composite
  contract (`unclassified_rejected`, `zero_atomic_rejected`, `multi_atomic_rejected_any`,
  `atomic_annotation_rejected`, `no_atomic_annotation_rejected`, `rmw_region_rejected`,
  `rmw_annotation_rejected`); the mixed-class row is `mixed_rejected`, whose cause is the
  composite contract itself. The rules on the kind and the annotation do not depend on the
  composite contract (`kindAnnotation_independent`).
* 11b (C37, C38): the outcomes of `readShared`.
* 11c (C40): the five order rows, the static rejection of an order outside its row, the
  independence of the two orders of a compare-and-exchange, and the agreement of each row with
  the order legality of the event model (`Events.Graph.OrderOK`).
* 11d (C35, `OB-C21`): directional conservativity of the shared writes, relative to the memory
  model formalization, which does not represent the type and storage contract of Spec 1 §68.3.

The classification of the accesses of a step and the rule of C42 are in `Classification`.
-/

namespace Ern.ConcurrencyModel

open Ern.MemoryModel.Access

/-! ## 11a: outcomes of the concurrent `writeShared` (C35, C38, C39) -/

/-- A request that fails the discipline acceptance is `reject` (C35, C38, C39). -/
theorem reject_of_not_discipline {ks : KShared} {s : SC} {c a : Nat} {region : List Nat}
    {ord : Option MemOrder} {kind : WriteKind} (h : ¬ WriteDisciplineOK ks region ord kind) :
    WriteSharedCStep ks s c a region ord kind .reject :=
  .reject fun hp => h hp.discipline

/-- **Theorem 11a** (C35, C38, C39), outcomes of the concurrent `writeShared` executed by `c`: the
outcome is `ok` exactly when the unchanged O11 preconditions on the view of `c` (Spec 1 §68; C35),
the initialization condition of an RMW (C39) and the discipline acceptance (C35, C38–C40) hold,
and its state is then the O11 effect; it is `reject` exactly when they do not; it is never
`fail`; and one of the two outcomes exists for every request. -/
theorem writeSharedC_outcomes {ks : KShared} {s : SC} {c a : Nat} {region : List Nat}
    {ord : Option MemOrder} {kind : WriteKind} :
    (∀ s', WriteSharedCStep ks s c a region ord kind (.ok s') ↔
      (WriteSharedPre ks.toK (s.view c) a region ∧
        (kind ≠ .store → ∀ l ∈ region, (s.view c).I l = .init) ∧
        WriteDisciplineOK ks region ord kind) ∧ s' = writeSharedCEff s c region) ∧
    (WriteSharedCStep ks s c a region ord kind .reject ↔
      ¬ (WriteSharedPre ks.toK (s.view c) a region ∧
        (kind ≠ .store → ∀ l ∈ region, (s.view c).I l = .init) ∧
        WriteDisciplineOK ks region ord kind)) ∧
    ¬ WriteSharedCStep ks s c a region ord kind .fail ∧
    (WriteSharedCStep ks s c a region ord kind (.ok (writeSharedCEff s c region)) ∨
      WriteSharedCStep ks s c a region ord kind .reject) := by
  have hiff : WriteSharedCPre ks s c a region ord kind ↔
      (WriteSharedPre ks.toK (s.view c) a region ∧
        (kind ≠ .store → ∀ l ∈ region, (s.view c).I l = .init) ∧
        WriteDisciplineOK ks region ord kind) :=
    ⟨fun h => ⟨h.o11, h.rmwInit, h.discipline⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, h3, h2⟩⟩
  refine ⟨fun s' => ?_, ?_, (fun h => by cases h), ?_⟩
  · unfold WriteSharedCStep WriteSharedCRel; rw [Guarded.ok_iff, hiff]
  · unfold WriteSharedCStep WriteSharedCRel; rw [Guarded.reject_iff, hiff]
  · by_cases hp : WriteSharedCPre ks s c a region ord kind
    · exact .inl (.ok hp)
    · exact .inr (.reject hp)

/-- C39, "Empty region": the effect of a concurrent `writeShared` on the empty region is no leaf
effect; the state is unchanged. -/
theorem writeSharedCEff_nil (s : SC) (c : Nat) : writeSharedCEff s c [] = s := by
  cases s
  simp only [writeSharedCEff, write3Eff, SC.set, SC.view, SC.flat, List.not_mem_nil, ite_false]

/-- **Theorem 11a**, row "leaf without a class" (C35: "concurrent evaluation of `writeShared` over
a nonempty region is `reject` if any targeted leaf lacks a selected `K_C.SharedDiscipline` class",
even if a composite contract would otherwise have admitted the region): `reject` whatever the
order, the kind and the composite contract. -/
theorem unclassified_rejected {ks : KShared} {s : SC} {c a : Nat} {region : List Nat}
    {ord : Option MemOrder} {kind : WriteKind} {l : Nat} (hl : l ∈ region)
    (hn : ks.SharedDiscipline l = none) (cc : List Nat → Option (List Nat)) :
    WriteSharedCStep { ks with CompositeContract := cc } s c a region ord kind .reject := by
  refine reject_of_not_discipline fun hd => ?_
  cases kind with
  | store => exact hd.1 l hl hn
  | rmw v =>
    obtain ⟨l', sz, al, e1, e2, -, -⟩ := hd
    subst e1; rw [List.mem_singleton.1 hl] at hn
    exact absurd (hn.symm.trans e2) (by simp)

/-- **Theorem 11a**, row "`Atomic` leaf of zero physical size" (C38: "`readShared` or concurrent
`writeShared` targeting that leaf is `reject`"; reading 6 of `Atomic`): `reject` whatever the
order, the kind and the composite contract. -/
theorem zero_atomic_rejected {ks : KShared} {s : SC} {c a : Nat} {region : List Nat}
    {ord : Option MemOrder} {kind : WriteKind} {l : Nat} (hl : l ∈ region)
    (hz : ZeroAtomic ks l) (cc : List Nat → Option (List Nat)) :
    WriteSharedCStep { ks with CompositeContract := cc } s c a region ord kind .reject := by
  refine reject_of_not_discipline fun hd => ?_
  cases kind with
  | store => exact hd.2.1 l hl hz
  | rmw v =>
    obtain ⟨l', sz, al, e1, e2, hsz, -⟩ := hd
    subst e1; rw [List.mem_singleton.1 hl] at hz
    obtain ⟨al', e⟩ := hz
    have : Discipline.atomic 0 al' = .atomic sz al := Option.some.inj (e.symm.trans e2)
    cases this; exact hsz rfl

/-- **Theorem 11a**, row "more than one `Atomic` leaf" (C38: such a region is `reject`; C39: a
composite contract cannot have more than one `Atomic` leaf admitted): `multi_atomic_rejected`
under every composite contract. -/
theorem multi_atomic_rejected_any {ks : KShared} {s : SC} {c a : Nat} {region : List Nat}
    {ord : Option MemOrder} {kind : WriteKind} {l₁ l₂ : Nat} (h12 : l₁ ≠ l₂)
    (h₁ : l₁ ∈ region) (h₂ : l₂ ∈ region) (ha₁ : AtomicLeaf ks l₁) (ha₂ : AtomicLeaf ks l₂)
    (cc : List Nat → Option (List Nat)) :
    WriteSharedCStep { ks with CompositeContract := cc } s c a region ord kind .reject :=
  multi_atomic_rejected h12 h₁ h₂ ha₁ ha₂

/-- **Theorem 11a**, row "one `Atomic` leaf", kind `store` (C39: "exactly one `Atomic` leaf
requires an atomic memory-order annotation, whether it is the entire region or part of a
mixed-class composite"; it "must be permitted for a `store` by C40"; "A missing required
annotation ... or an order illegal for the event kind is `reject`"): `reject` whatever the
composite contract. -/
theorem atomic_annotation_rejected {ks : KShared} {s : SC} {c a : Nat} {region : List Nat}
    {ord : Option MemOrder} {l : Nat} (hl : l ∈ region) (ha : AtomicLeaf ks l)
    (hn : ¬ AnnotatedOK .store ord) (cc : List Nat → Option (List Nat)) :
    WriteSharedCStep { ks with CompositeContract := cc } s c a region ord .store .reject :=
  reject_of_not_discipline fun hd => hn (hd.2.2.2.1 ⟨l, hl, ha⟩)

/-- **Theorem 11a**, rows "empty region" and "no `Atomic` leaf", kind `store` (C39: "With no
`Atomic` leaf, the annotation must be absent"; "a supplied annotation where none applies ... is
`reject`"; "Empty region": "An annotation ... makes this concurrent step `reject`"): `reject`
whatever the composite contract. -/
theorem no_atomic_annotation_rejected {ks : KShared} {s : SC} {c a : Nat} {region : List Nat}
    {o : MemOrder} (hn : ∀ l ∈ region, ¬ AtomicLeaf ks l) (cc : List Nat → Option (List Nat)) :
    WriteSharedCStep { ks with CompositeContract := cc } s c a region (some o) .store .reject :=
  reject_of_not_discipline fun hd => by cases hd.2.2.2.2.1 hn

/-- **Theorem 11a**, kind RMW on a region other than exactly one `Atomic` leaf (C39: "Any other
region, including an empty region, a multi-leaf region, or a non-`Atomic` single leaf, is `reject`
for `RMW`"; "Empty region": "An annotation or `RMW` kind makes this concurrent step `reject`"):
`reject` whatever the order and the composite contract. -/
theorem rmw_region_rejected {ks : KShared} {s : SC} {c a : Nat} {region : List Nat}
    {ord : Option MemOrder} {v : Nat}
    (hn : ¬ ∃ l sz al, region = [l] ∧ ks.SharedDiscipline l = some (.atomic sz al))
    (cc : List Nat → Option (List Nat)) :
    WriteSharedCStep { ks with CompositeContract := cc } s c a region ord (.rmw v) .reject :=
  reject_of_not_discipline fun ⟨l, sz, al, e1, e2, _, _⟩ => hn ⟨l, sz, al, e1, e2⟩

/-- **Theorem 11a**, kind RMW without annotation (C39: an RMW "carries an explicit memory-order
annotation permitted by the atomic RMW row of C40; absence of that annotation or an illegal order
is `reject`"; every order is in that row, `order_rows`): `reject` whatever the region and the
composite contract. -/
theorem rmw_annotation_rejected {ks : KShared} {s : SC} {c a : Nat} {region : List Nat}
    {v : Nat} (cc : List Nat → Option (List Nat)) :
    WriteSharedCStep { ks with CompositeContract := cc } s c a region none (.rmw v) .reject :=
  reject_of_not_discipline fun ⟨_, _, _, _, _, _, h⟩ => h

/-- The rules on the kind and the annotation of C39 ("Operation kind and atomic memory-order
annotations"), which read the classes of the targeted leaves and nothing else: an RMW region is
exactly one `Atomic` leaf and carries an annotation in the RMW row of C40; a store region with an
`Atomic` leaf carries an annotation in the store row of C40, and one without carries none. -/
def KindAnnotationOK (ks : KShared) (region : List Nat) (ord : Option MemOrder) :
    WriteKind → Prop
  | .rmw v => ∃ l sz al, region = [l] ∧ ks.SharedDiscipline l = some (.atomic sz al) ∧
      AnnotatedOK (.rmw v) ord
  | .store => ((∃ l ∈ region, AtomicLeaf ks l) → AnnotatedOK .store ord) ∧
      ((∀ l ∈ region, ¬ AtomicLeaf ks l) → ord = none)

/-- **Theorem 11a**, independence of the composite contract (C39: "A composite contract (C38)
cannot override these rules"):

1. the discipline acceptance entails the rules on the kind and the annotation;
2. two contracts that select the same disciplines give the same verdict on these rules, whatever
   their composite contracts;
3. a request that breaks them is `reject` under every contract that selects the same
   disciplines, whatever its composite contract. -/
theorem kindAnnotation_independent {ks : KShared} {s : SC} {c a : Nat} {region : List Nat}
    {ord : Option MemOrder} {kind : WriteKind} :
    (WriteDisciplineOK ks region ord kind → KindAnnotationOK ks region ord kind) ∧
    (∀ ks' : KShared, ks'.SharedDiscipline = ks.SharedDiscipline →
      (KindAnnotationOK ks' region ord kind ↔ KindAnnotationOK ks region ord kind)) ∧
    (¬ KindAnnotationOK ks region ord kind → ∀ ks' : KShared,
      ks'.SharedDiscipline = ks.SharedDiscipline →
      WriteSharedCStep ks' s c a region ord kind .reject) := by
  have entail : ∀ ks : KShared, WriteDisciplineOK ks region ord kind →
      KindAnnotationOK ks region ord kind := by
    intro ks hd
    cases kind with
    | store => exact ⟨hd.2.2.2.1, hd.2.2.2.2.1⟩
    | rmw v =>
      obtain ⟨l, sz, al, e1, e2, -, h⟩ := hd
      exact ⟨l, sz, al, e1, e2, h⟩
  have same : ∀ ks' : KShared, ks'.SharedDiscipline = ks.SharedDiscipline →
      (KindAnnotationOK ks' region ord kind ↔ KindAnnotationOK ks region ord kind) := by
    intro ks' he
    have hat : ∀ l, AtomicLeaf ks' l ↔ AtomicLeaf ks l := fun l => by
      unfold AtomicLeaf; rw [he]
    cases kind with
    | store => simp only [KindAnnotationOK, hat]
    | rmw v => simp only [KindAnnotationOK, he]
  refine ⟨entail ks, same, fun hn ks' he => reject_of_not_discipline fun hd => ?_⟩
  exact hn ((same ks' he).1 (entail ks' hd))

/-! ## 11b: outcomes of `readShared` (C37, C38) -/

/-- **Theorem 11b** (C37, C38), outcomes of `readShared(access, leaf, order)` executed by `c`:
`ok` exactly under C37.1–C37.4 with a leaf not of zero physical size (`ReadSharedPre`), with the
state unchanged; `reject` exactly otherwise; never `fail`; one of the two for every request. In
particular `reject` on `Synchronized` or `Confined` storage, by the operation's own rule (C37.3,
not O11.3), and on an `Atomic` leaf of zero physical size (C38; reading 6 of `Atomic`). -/
theorem readShared_outcomes {ks : KShared} {s : SC} {c a l : Nat} {order : MemOrder} :
    (∀ s', ReadSharedStep ks s c a l order (.ok s') ↔ ReadSharedPre ks s c a l order ∧ s' = s) ∧
    (ReadSharedStep ks s c a l order .reject ↔ ¬ ReadSharedPre ks s c a l order) ∧
    ¬ ReadSharedStep ks s c a l order .fail ∧
    (ReadSharedStep ks s c a l order (.ok s) ∨ ReadSharedStep ks s c a l order .reject) ∧
    ((ks.SharedDiscipline l = some .synchronized ∨ ks.SharedDiscipline l = some .confined) →
      ReadSharedStep ks s c a l order .reject) ∧
    (ZeroAtomic ks l → ReadSharedStep ks s c a l order .reject) := by
  refine ⟨fun s' => Guarded.ok_iff, Guarded.reject_iff, (fun h => by cases h), ?_,
    fun hd => .reject fun hp => ?_, fun hz => .reject fun hp => hp.nonzero hz⟩
  · by_cases hp : ReadSharedPre ks s c a l order
    · exact .inl (.ok hp)
    · exact .inr (.reject hp)
  · obtain ⟨sz, al, ha⟩ := hp.atomic
    rcases hd with hd | hd <;> rw [hd] at ha <;> cases ha

/-! ## 11c: memory orders (C40) -/

/-- **Theorem 11c** (C40), the five rows of the per-operation legality table, by enumeration:
`readShared` atomic load; atomic `writeShared` store; atomic RMW; CAS success, which is the atomic
RMW row in `CasOrdersOK`; CAS failure. -/
theorem order_rows :
    (∀ o, LoadOrderOK o ↔ o = .relaxed ∨ o = .acquire ∨ o = .seqCst) ∧
    (∀ o, StoreOrderOK o ↔ o = .relaxed ∨ o = .release ∨ o = .seqCst) ∧
    (∀ o, RMWOrderOK o ↔
      o = .relaxed ∨ o = .acquire ∨ o = .release ∨ o = .acqRel ∨ o = .seqCst) ∧
    (∀ succ fail, CasOrdersOK succ fail → (succ = .relaxed ∨ succ = .acquire ∨
      succ = .release ∨ succ = .acqRel ∨ succ = .seqCst)) ∧
    (∀ o, CasFailureOrderOK o ↔ o = .relaxed ∨ o = .acquire ∨ o = .seqCst) := by
  refine ⟨fun o => ?_, fun o => ?_, fun o => ?_, fun succ _ _ => ?_, fun o => ?_⟩ <;>
    first
    | (cases o <;> simp [LoadOrderOK, StoreOrderOK, RMWOrderOK, CasFailureOrderOK])
    | (cases succ <;> simp)

/-- **Theorem 11c** (C40: "A source-level order outside its row is a static `reject` under the
concurrency contract"): for each step that carries an order, an order outside its row makes the
step `reject`: the load, the store on a region with an `Atomic` leaf (whatever the composite
contract, `atomic_annotation_rejected`), the RMW, and both orders of a compare-and-exchange,
whatever its branch. The atomic RMW and CAS success rows contain every order (`order_rows`), so
their hypotheses are never met. -/
theorem order_out_of_row_rejected {ks : KShared} {s : SC} {c a l : Nat} :
    (∀ order, ¬ LoadOrderOK order → ReadSharedStep ks s c a l order .reject) ∧
    (∀ region o, l ∈ region → AtomicLeaf ks l → ¬ StoreOrderOK o →
      WriteSharedCStep ks s c a region (some o) .store .reject) ∧
    (∀ region o v, ¬ RMWOrderOK o → WriteSharedCStep ks s c a region (some o) (.rmw v) .reject) ∧
    (∀ succ fail br, (¬ RMWOrderOK succ ∨ ¬ CasFailureOrderOK fail) →
      CasStep ks s c a l succ fail br .reject) := by
  refine ⟨fun order hn => .reject fun hp => hn hp.order,
    fun region o hl ha hn => atomic_annotation_rejected (ks := ks) (ord := some o) hl ha hn ks.CompositeContract,
    fun region o v hn => reject_of_not_discipline fun ⟨_, _, _, _, _, _, h⟩ => hn h,
    fun succ fail br hn => .inl ⟨fun ⟨h1, h2⟩ => hn.elim (· h1) (· h2), rfl⟩⟩

/-- **Theorem 11c** (C40: "A CAS may choose its success and failure orders independently: no
strength relation between them is imposed"): the order legality of a compare-and-exchange is the
conjunction of its two rows; a failure order stronger than the success order, and the converse,
are both legal. -/
theorem cas_orders_independent :
    (∀ succ fail, CasOrdersOK succ fail ↔ RMWOrderOK succ ∧ CasFailureOrderOK fail) ∧
    CasOrdersOK .relaxed .seqCst ∧ CasOrdersOK .seqCst .relaxed :=
  ⟨fun _ _ => Iff.rfl, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩

/-- **Theorem 11c** (C40), agreement of each row with the order legality of the event model
(`Events.Graph.OrderOK`, C40 on events) for the kind of its event: the load and the CAS failure
are reads (C37, C39), the store is a write (C39), the RMW and the CAS success are RMWs (C39). -/
theorem rows_agree_orderOK (o : MemOrder) :
    (LoadOrderOK o ↔ Events.Graph.OrderOK .read o) ∧
    (StoreOrderOK o ↔ Events.Graph.OrderOK .write o) ∧
    (RMWOrderOK o ↔ Events.Graph.OrderOK .rmw o) ∧
    (CasFailureOrderOK o ↔ Events.Graph.OrderOK .read o) := by
  cases o <;> simp [LoadOrderOK, StoreOrderOK, RMWOrderOK, CasFailureOrderOK,
    Events.Graph.OrderOK]

/-! ## 11d: directional conservativity (C35, `OB-C21`) -/

/-- **Theorem 11d** (C35: "Each concurrency-`ok` inherited operation must separately satisfy the
unchanged Spec 1 O11 under the corresponding projection of `K_C` to `K`"; `OB-C21`), relative to
the memory model formalization, which does not represent the type and storage contract of Spec 1
§68.3 (`WriteSharedPre`): every `ok` concurrent `writeShared`, RMW included, is an `ok` O11 step
on the projection `ks.toK`, executed by the same context and reaching the same state; as a
labelled step, the inherited O11 label takes the same transition. The converse fails: witnesses
D8 and 6k (`witness_d8`, `witness_6k_kernel`). -/
theorem writeShared_conservative {ks : KShared} {L : MutexLayout} {c a : Nat}
    {region : List Nat} {ord : Option MemOrder} {kind : WriteKind}
    {st st' : SC × SyncReg × ArenaReg}
    (h : LStep ks L (.writeShared c a region ord kind) st st') :
    LStep ks L (.kernel c (.writeShared a region)) st st' := by
  cases h with
  | writeShared h => exact .kernel (writeSharedC_ok_kernel h)

/-- **Theorem 11d** for the compare-and-exchange (C39: "A successful compare-and-exchange (CAS)
on an initialized `Atomic` leaf is a `writeShared` mutation"; C35; `OB-C21`), relative to the
memory model formalization, which does not represent the type and storage contract of Spec 1
§68.3: a successful CAS is an `ok` O11 step on its single leaf, on the projection `ks.toK`, taking
the same labelled transition. -/
theorem cas_success_conservative {ks : KShared} {L : MutexLayout} {c a l v : Nat}
    {succ fail : MemOrder} {st st' : SC × SyncReg × ArenaReg}
    (h : LStep ks L (.cas c a l succ fail (.success v)) st st') :
    LStep ks L (.kernel c (.writeShared a [l])) st st' := by
  cases h with
  | cas h =>
    rcases h with ⟨-, h⟩ | ⟨-, h⟩
    · cases h
    · exact .kernel (writeSharedC_ok_kernel h)

end Ern.ConcurrencyModel
