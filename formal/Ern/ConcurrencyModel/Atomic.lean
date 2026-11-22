import Ern.ConcurrencyModel.Contract

/-!
# Atomic step cases (C35–C40)

The three concurrent step cases of the authority machine named by C39 ("Authority-machine
operation coverage"):

* `readShared` (C37), a new concurrent transition: the state is unchanged and the observed value
  is part of the label, unconstrained by the step relation (C37: the transition's state-local
  preconditions do not require an `rf` source);
* the concurrent evaluation of the inherited `writeShared` under `K_C.SharedDiscipline` (C35,
  C38–C40), whose success is the O11 mutation (C39) and whose failure is the O11 `reject`;
* the compare-and-exchange (C39, C40): its success is a `writeShared` RMW, its failure a
  `readShared` observation; the branch is part of the label, not decided by the state (C39).

The definitions this needs from C35, C38, C39 and C40: the per-operation order table, the
single-leaf atomic unit, the classification of every targeted leaf, the rejection of zero-size
`Atomic` leaves, of regions with more than one `Atomic` leaf and of regions combining classes
without a composite contract, and the rules on the kind and the annotation of C39.

Formalization hypotheses (readings, not rules of the specification):

* reading 6 (C38, "zero physical size"): for a leaf `Atomic(size, align)`, zero physical size is
  `size = 0`; C38 makes the byte range of the leaf a single unit, of size `size` (`ZeroAtomic`);
* reading 7 (C28, C38, declared order of a composite contract): the composite contract reads only
  the region; admitting a mixed-class region is giving its declared order, an enumeration of the
  leaves of the region, each once, the order of the leaf writes in the step; a region for which the
  contract gives no order is not admitted (`CompositeAdmits`). The authority and validity markers that C28 also
  names are not represented, and no consequence on events is proved here.
-/

namespace Ern.ConcurrencyModel

open Ern.MemoryModel.Access

/-! ## Memory-order legality (C40) -/

/-- C40, row "`readShared` atomic load": `relaxed`, `acquire`, `seq_cst`. -/
def LoadOrderOK : MemOrder → Prop
  | .relaxed | .acquire | .seqCst => True
  | _ => False

/-- C40, row "atomic `writeShared` store": `relaxed`, `release`, `seq_cst`. -/
def StoreOrderOK : MemOrder → Prop
  | .relaxed | .release | .seqCst => True
  | _ => False

/-- C40, rows "atomic RMW" and "CAS success (modifying RMW)": `relaxed`, `acquire`, `release`,
`acq_rel`, `seq_cst`. -/
def RMWOrderOK : MemOrder → Prop
  | .relaxed | .acquire | .release | .acqRel | .seqCst => True

/-- C40, row "CAS failure (read-only)": `relaxed`, `acquire`, `seq_cst`. -/
def CasFailureOrderOK : MemOrder → Prop
  | .relaxed | .acquire | .seqCst => True
  | _ => False

instance (o : MemOrder) : Decidable (LoadOrderOK o) := by cases o <;> unfold LoadOrderOK <;> infer_instance
instance (o : MemOrder) : Decidable (StoreOrderOK o) := by cases o <;> unfold StoreOrderOK <;> infer_instance
instance (o : MemOrder) : Decidable (RMWOrderOK o) := by cases o <;> unfold RMWOrderOK <;> infer_instance
instance (o : MemOrder) : Decidable (CasFailureOrderOK o) := by
  cases o <;> unfold CasFailureOrderOK <;> infer_instance

/-- The order permitted for an atomic modification of kind `kind` (C40): the store row for a
plain write, the RMW row for an RMW. -/
def WriteOrderOK : WriteKind → MemOrder → Prop
  | .store, o => StoreOrderOK o
  | .rmw _, o => RMWOrderOK o

instance (kind : WriteKind) (o : MemOrder) : Decidable (WriteOrderOK kind o) := by
  cases kind <;> unfold WriteOrderOK <;> infer_instance

/-! ## Disciplines of a region (C35, C38) -/

/-- The class of a discipline (C38: "incompatible `SharedDiscipline` classes"): `Atomic`,
`Synchronized` or `Confined`, sizes and alignments aside. -/
def Discipline.cls : Discipline → Nat
  | .atomic _ _ => 0
  | .synchronized => 1
  | .confined => 2

/-- Leaf `l` is an `Atomic` leaf (C35, C38). -/
def AtomicLeaf (ks : KShared) (l : Nat) : Prop := (ks.SharedDiscipline l).map Discipline.cls = some 0

/-- Decidability of `AtomicLeaf` (C38). -/
instance (ks : KShared) (l : Nat) : Decidable (AtomicLeaf ks l) := by
  unfold AtomicLeaf; infer_instance

/-- The annotation is present and in the C40 row of the kind (C39, C40). -/
def AnnotatedOK (kind : WriteKind) : Option MemOrder → Prop
  | some o => WriteOrderOK kind o
  | none => False

instance (kind : WriteKind) (ord : Option MemOrder) : Decidable (AnnotatedOK kind ord) := by
  cases ord <;> unfold AnnotatedOK <;> infer_instance

/-- An `Atomic` leaf of zero physical size (C38: "An `Atomic(size, align)` leaf with zero physical
size cannot satisfy the supported atomic-unit requirement"; reading 6: `size = 0`). -/
def ZeroAtomic (ks : KShared) (l : Nat) : Prop := ∃ al, ks.SharedDiscipline l = some (.atomic 0 al)

/-- `ZeroAtomic` on the discipline. -/
def zeroB : Option Discipline → Bool
  | some (.atomic 0 _) => true
  | _ => false

theorem zeroAtomic_iff (ks : KShared) (l : Nat) : ZeroAtomic ks l ↔ zeroB (ks.SharedDiscipline l) = true := by
  unfold ZeroAtomic
  cases ks.SharedDiscipline l with
  | none => simp [zeroB]
  | some d => cases d with
    | atomic sz al => cases sz <;> simp [zeroB]
    | synchronized => simp [zeroB]
    | confined => simp [zeroB]

instance (ks : KShared) (l : Nat) : Decidable (ZeroAtomic ks l) :=
  decidable_of_iff _ (zeroAtomic_iff ks l).symm

/-- The declared order enumerates the leaves of the region, each once (C28, C38; reading 7). -/
def Enumerates (order region : List Nat) : Prop :=
  order.Nodup ∧ (∀ l ∈ order, l ∈ region) ∧ ∀ l ∈ region, l ∈ order

instance (order region : List Nat) : Decidable (Enumerates order region) := by
  unfold Enumerates; infer_instance

/-- The composite contract admits `region`: it gives a declared order that enumerates the leaves of
the region (C38: a region combining classes "requires a separately established composite
contract"; C28: the contract determines the within-step order, and a step whose order it leaves
undetermined is not admitted; reading 7). -/
def CompositeAdmits (ks : KShared) (region : List Nat) : Prop :=
  ∃ order, ks.CompositeContract region = some order ∧ Enumerates order region

/-- `CompositeAdmits` on the contract. -/
def admitsB (o : Option (List Nat)) (region : List Nat) : Bool :=
  match o with
  | some order => decide (Enumerates order region)
  | none => false

theorem compositeAdmits_iff (ks : KShared) (region : List Nat) :
    CompositeAdmits ks region ↔ admitsB (ks.CompositeContract region) region = true := by
  unfold CompositeAdmits
  cases ks.CompositeContract region with
  | none => simp [admitsB]
  | some o => simp [admitsB]

instance (ks : KShared) (region : List Nat) : Decidable (CompositeAdmits ks region) :=
  decidable_of_iff _ (compositeAdmits_iff ks region).symm

/-- Every leaf of `region` has a selected discipline, all of the same class (C38: "classified
consistently"). -/
def SingleClass (ks : KShared) (region : List Nat) : Prop :=
  (∀ l ∈ region, ks.SharedDiscipline l ≠ none) ∧
    ∀ l ∈ region, ∀ l' ∈ region, (ks.SharedDiscipline l).map Discipline.cls =
      (ks.SharedDiscipline l').map Discipline.cls

/-- Every leaf of `region` has a selected discipline and two of them differ in class (C38: "a
region that combines incompatible `SharedDiscipline` classes"). -/
def MixedClasses (ks : KShared) (region : List Nat) : Prop :=
  (∀ l ∈ region, ks.SharedDiscipline l ≠ none) ∧ ¬ SingleClass ks region

instance (ks : KShared) (region : List Nat) : Decidable (SingleClass ks region) := by
  unfold SingleClass; infer_instance

instance (ks : KShared) (region : List Nat) : Decidable (MixedClasses ks region) := by
  unfold MixedClasses; infer_instance

/-- The discipline acceptance of a concurrent `writeShared` over `region`, with order annotation
`ord` and modification kind `kind` (C35, C38–C40):

* kind RMW (C39, "Operation kind and atomic memory-order annotations"): the region consists of
  exactly one `Atomic` leaf, not of zero physical size (C38), with an annotation in the atomic RMW
  row of C40; any other region, the empty one included, is `reject`;
* kind `store`:
  - every targeted leaf has a selected `K_C.SharedDiscipline` class (C35: a nonempty region with a
    leaf lacking one is `reject`, even if a composite contract would otherwise have admitted the
    region);
  - no targeted leaf is an `Atomic` leaf of zero physical size (C38);
  - at most one `Atomic` leaf (C38: more than one is `reject`, unconditionally);
  - with an `Atomic` leaf, an annotation in the store row of C40; with none, no annotation (C39:
    "exactly one `Atomic` leaf requires an atomic memory-order annotation, whether it is the entire
    region or part of a mixed-class composite"; "With no `Atomic` leaf, the annotation must be
    absent");
  - a region that combines classes is admitted by the composite contract (C38, C28; reading 7).

The empty region of kind `store` is admitted exactly without annotation (C39, "Empty region"). The
composite contract plays no part in the rules on the kind and the annotation (C39: "A composite
contract (C38) cannot override these rules"). -/
def WriteDisciplineOK (ks : KShared) (region : List Nat) (ord : Option MemOrder) :
    WriteKind → Prop
  | .rmw v => ∃ l sz al, region = [l] ∧ ks.SharedDiscipline l = some (.atomic sz al) ∧ sz ≠ 0 ∧
      AnnotatedOK (.rmw v) ord
  | .store =>
    (∀ l ∈ region, ks.SharedDiscipline l ≠ none) ∧
    (∀ l ∈ region, ¬ ZeroAtomic ks l) ∧
    (region.filter fun l => decide (AtomicLeaf ks l)).length ≤ 1 ∧
    ((∃ l ∈ region, AtomicLeaf ks l) → AnnotatedOK .store ord) ∧
    ((∀ l ∈ region, ¬ AtomicLeaf ks l) → ord = none) ∧
    (MixedClasses ks region → CompositeAdmits ks region)

instance (ks : KShared) (region : List Nat) (ord : Option MemOrder) :
    Decidable (WriteDisciplineOK ks region ord .store) := by
  unfold WriteDisciplineOK; infer_instance

/-! ## `readShared` (C37) -/

/-- Preconditions of `readShared(access, leaf, order)` executed by `c` (C37), on the view of `c`
(C2):

* C37.1 and C37.2 are the conditions of O9 (Spec 1 §66) on the single leaf: the leaf belongs to a
  usable place and is `Init`; its validity and dependency conditions hold; `access` is
  exercisable in `Observe` and its effective mode on the leaf is present;
* C37.3: the leaf is declared `K.SharedMutable` and its companion discipline is
  `Atomic(size, align)` for this single leaf; it is not of zero physical size (C38: "`readShared`
  ... targeting that leaf is `reject`"; reading 6); the rest of the concrete representation
  required by C38 is a realization obligation, outside the abstract state;
* C37.4: `order` is permitted for an atomic read (C40). -/
structure ReadSharedPre (ks : KShared) (s : SC) (c a l : Nat) (order : MemOrder) : Prop where
  /-- C37.1, C37.2 (Spec 1 §66.1–§66.3 on the single leaf). -/
  read : Read3Pre (s.view c) a [l]
  /-- C37.3: `K.SharedMutable`. -/
  shared : ks.SharedMutable l
  /-- C37.3: the discipline of the leaf is `Atomic(size, align)`. -/
  atomic : ∃ sz al, ks.SharedDiscipline l = some (.atomic sz al)
  /-- C37.3, C38: the `Atomic` leaf is not of zero physical size (reading 6). -/
  nonzero : ¬ ZeroAtomic ks l
  /-- C37.4, C40. -/
  order : LoadOrderOK order

/-- `readShared` without the liveness of the executing context (C37): `ok` with the state
unchanged, or `reject`; never `fail`. The observed value is not an argument: it is carried by the
label and not constrained here (C37). -/
def ReadSharedRel (ks : KShared) (s : SC) (c a l : Nat) (order : MemOrder) (o : Outcome3 SC) :
    Prop :=
  Guarded (ReadSharedPre ks s c a l order) s o

/-- `readShared(access, leaf, order)` executed by `c` (C37). A context that is not live has no
current frame (C2): C37.2 fails, `reject`. -/
def ReadSharedStep (ks : KShared) (s : SC) (c a l : Nat) (order : MemOrder) (o : Outcome3 SC) :
    Prop :=
  ReadSharedRel ks s c a l order o

/-! ## Concurrent `writeShared` (C35, C38, C39) -/

/-- Preconditions of the concurrent evaluation of `writeShared(access, region)` executed by `c`
with annotation `ord` and kind `kind` (C35, C38–C40): the unchanged O11 preconditions on the view
of `c` (Spec 1 §68; C35: "Each concurrency-`ok` inherited operation must separately satisfy the
unchanged Spec 1 O11"), the discipline acceptance, and, for an RMW, an initialized leaf (C39: "the
declared atomic operation conditionally reads and modifies the same initialized leaf"). -/
structure WriteSharedCPre (ks : KShared) (s : SC) (c a : Nat) (region : List Nat)
    (ord : Option MemOrder) (kind : WriteKind) : Prop where
  /-- Spec 1 §68.1–§68.3 (C35, C39). -/
  o11 : WriteSharedPre ks.toK (s.view c) a region
  /-- C35, C38–C40. -/
  discipline : WriteDisciplineOK ks region ord kind
  /-- C39: an RMW reads and modifies an initialized leaf. -/
  rmwInit : kind ≠ .store → ∀ l ∈ region, (s.view c).I l = .init

/-- Effect of a successful concurrent `writeShared` (C39): the O11 effect (Spec 1 §68: the
written leaves become `Init`), on the view of `c`, written back. -/
def writeSharedCEff (s : SC) (c : Nat) (region : List Nat) : SC :=
  s.set (write3Eff (s.view c) region)

/-- The concurrent `writeShared` without the liveness of the executing context (C39): `ok` with the
O11 effect, or the O11 `reject`; never `fail`. -/
def WriteSharedCRel (ks : KShared) (s : SC) (c a : Nat) (region : List Nat)
    (ord : Option MemOrder) (kind : WriteKind) (o : Outcome3 SC) : Prop :=
  Guarded (WriteSharedCPre ks s c a region ord kind) (writeSharedCEff s c region) o

/-- The concurrent evaluation of `writeShared` executed by `c` (C35, C38–C40). A context that is
not live has no current frame (C2): the exercise of Spec 1 §68.2 fails, `reject`. -/
def WriteSharedCStep (ks : KShared) (s : SC) (c a : Nat) (region : List Nat)
    (ord : Option MemOrder) (kind : WriteKind) (o : Outcome3 SC) : Prop :=
  WriteSharedCRel ks s c a region ord kind o

/-! ## Compare-and-exchange (C39, C40) -/

/-- The branch of a compare-and-exchange (C39): success, whose RMW read component observed
`observed`, or failure, a `readShared` observation of `observed`. The step relation does not
decide the branch (C39). -/
inductive CasBranch where
  | success (observed : Nat)
  | failure (observed : Nat)
deriving DecidableEq, Repr

/-- The static order legality of a compare-and-exchange (C40): the success order in its row, and
the failure order in its row; no strength relation between them. -/
def CasOrdersOK (succ fail : MemOrder) : Prop := RMWOrderOK succ ∧ CasFailureOrderOK fail

instance (succ fail : MemOrder) : Decidable (CasOrdersOK succ fail) := by
  unfold CasOrdersOK; infer_instance

/-- A compare-and-exchange on `leaf` executed by `c` with success order `succ`, failure order
`fail` and branch `br` (C39, C40): a static `reject` when an order is outside its row (C40);
otherwise, on success, the concurrent `writeShared` RMW on the single leaf with the success order;
on failure, the `readShared` observation with the failure order, which neither mutates nor creates
a grant (C39). A context that is not live has no current frame (C2): `reject`. -/
def CasStep (ks : KShared) (s : SC) (c a leaf : Nat) (succ fail : MemOrder) (br : CasBranch)
    (o : Outcome3 SC) : Prop :=
  (¬ CasOrdersOK succ fail ∧ o = .reject) ∨
    (CasOrdersOK succ fail ∧ match br with
      | .success v => WriteSharedCRel ks s c a [leaf] (some succ) (.rmw v) o
      | .failure _ => ReadSharedRel ks s c a leaf fail o)

/-! ## The atomic cases are O11 or state-preserving steps (C37, C39) -/

/-- C37 `ok` effect: a successful `readShared` leaves the state unchanged. -/
theorem readShared_ok_eq {ks : KShared} {s s' : SC} {c a l : Nat} {order : MemOrder}
    (h : ReadSharedRel ks s c a l order (.ok s')) : s' = s :=
  (Guarded.ok_iff.1 h).2

/-- C39, C35: a successful concurrent `writeShared` is a successful O11 step executed by the same
context (Spec 1 §68, unchanged), with the same effect. -/
theorem writeSharedC_ok_kernel {ks : KShared} {s s' : SC} {c a : Nat} {region : List Nat}
    {ord : Option MemOrder} {kind : WriteKind}
    (h : WriteSharedCRel ks s c a region ord kind (.ok s')) :
    opStepC ks.toK (.writeShared a region) c s (.ok s') := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  exact ⟨.ok (write3Eff (s.view c) region), .ok hpre.o11, rfl⟩

/-- C39: a successful compare-and-exchange is either a successful O11 step on the single leaf
(success) or leaves the state unchanged (failure, a `readShared` observation). -/
theorem cas_ok_cases {ks : KShared} {s s' : SC} {c a l : Nat} {succ fail : MemOrder}
    {br : CasBranch} (h : CasStep ks s c a l succ fail br (.ok s')) :
    opStepC ks.toK (.writeShared a [l]) c s (.ok s') ∨ s' = s := by
  obtain (⟨-, h⟩ | ⟨-, h⟩) := h
  · cases h
  · cases br with
    | success v => exact .inl (writeSharedC_ok_kernel h)
    | failure v => exact .inr (readShared_ok_eq h)

end Ern.ConcurrencyModel
