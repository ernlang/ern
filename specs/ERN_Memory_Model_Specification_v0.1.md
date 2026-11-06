# ERN — Memory Model Specification v0.1

**Edition v0.1 — corrective candidate, not yet validated**

Modified clauses, relative to v0 (each change is justified by a defect found while formalizing v0):

- §36: `MetaRight` governs authorities over existing storage, not the fresh allocation of `alloc`; §36 and §71.2 contradicted each other.
- §40: `RootHeld` restricted to usable root places, as in §49.7; the two clauses differed on unusable root places.
- §47: the ownership graph of statics is acyclic; a static ownership cycle made §57 false in the initial state.
- §51: a valid origin is an active origin; "valid" was undefined there.
- §57: definition of I5, which v0 named without defining.
- §59: "access operations" are O9–O11; read as all operations, §59 contradicted §69.
- §60.1: a valid origin chain is an active one, read through §44.
- §63.4: the active derived authorities covering the source from outside are named, and the authorities through which the step exercises its `Modify` right are exempt; without this exemption no value could be moved through a derived authority.
- §63.9 (new): the destination is usable in the resulting state; without it an accepted transfer could create an ownership cycle and break §49.8 and §57.
- §69.2 and §70.3: the same exemption as §63.4, and rejection when an authority made inactive by the step keeps an active descendant; without it an accepted step left an active authority with an inactive origin.
- §71.2: the provider is a usable place; v0 did not require it to exist.
- §74 and §75: each `pin` installs an obligation of fresh identity and `unpin` ends one designated obligation; per-leaf pin flags let an `unpin` lift a pin installed by another `pin`.
- §76.6: the reading of the precondition (whole kernel state, `ArenaInv` of the new entry, resulting state); v0 admitted several readings with different verdicts.
- §78.3: restricted to anchors covering a leaf of the administered storage; as written, its second sentence was false.
- §82.2: address and provenance of a pointer to a region whose leaves all have zero physical size; v0 decided no address for that region.
- §86: the last sentence is rewritten; as written, it was false, since `reset` and `issue` leave a recycled leaf `Init` and readable.

**Higher normative authority:** *ERN — Language Charter v0* (October 27, 2026).  
This specification defines the normative rules of ERN's memory model. Technical names (`derive`, `transfer`, `issue`, etc.) designate **abstract semantic operations**; they do not constitute syntax decisions.

## Validation and Revision Procedure

This edition has been validated and acquires normative authority under the ERN Charter v0. Any subsequent semantic change must identify the clauses concerned, justify the change, and preserve the guarantees of the ERN Charter v0. Formal models and proofs are instruments for verifying this specification, not sources of additional rules. Behaviors not determined within its scope are explicitly identified.

## Scope

This specification defines:

- the safe-code contract;
- the abstract machine for allocations, bytes, and accesses;
- the second-class access discipline;
- footprints, authorities, dependencies, frames, and ownership;
- read, write, transfer, release, allocation, and pinning transitions;
- the normative contract of arenas as a reference library abstraction;
- the correspondence obligations between these mechanisms.

It does not define syntax, the complete concurrency model, control-flow conventions, the type system, or compiler lowering. The sequential model's scope does not waive the general guarantees of the Charter.

---

# I. Safe-Behavior Contract

The following contract applies to all safe code and all properly encapsulated abstractions, regardless of their concrete memory representation.

## 1. Definitions of Safe Behavior

**Safe operation:** An operation that imposes no unchecked safety obligation on its user whose violation could compromise the language's guarantees.

**Safe code:** Code that executes only safe operations and does not directly assume obligations specific to unsafe operations.

**Safe interface:** An interface whose every permitted use preserves the language's guarantees when its implementation is correct.

**Safe abstraction:** An abstraction exposing a safe interface; its implementation may use unsafe operations provided it fulfills all their obligations.

**Safety obligation:** A condition necessary to preserve the guarantees, explicitly left to the user of an unsafe operation rather than automatically checked by that operation.

**Undefined behavior (UB):** Behavior on which the specification imposes no semantic requirements. UB is not a category of recoverable error.

## 2. Fundamental Guarantees

Every program composed of safe code and correctly implemented safe abstractions must preserve, for **all its permitted executions**, the guarantees of ERN Charter v0 §4.1:

1. spatial memory safety;
2. temporal memory safety;
3. absence of reads of uninitialized values;
4. absence of type confusion;
5. absence of *data races*.

Responsibility for fulfilling internal unsafe obligations belongs to the authors of the abstractions using them, not to their safe callers. These guarantees do not assume a single memory-management runtime.

## 3. Behavior Categories

- **Defined behavior:** effects and results determined or bounded by the specification, including when it permits multiple results.
- **Defined failure:** a situation rejected at runtime with a specified consequence (for example, an error value or controlled termination).
- **Implementation-defined behavior:** a choice explicitly permitted by the specification that the implementation must document.
- **Undefined behavior (UB):** a situation for which the language imposes no requirements on the behavior of the execution concerned.

**Safe code cannot cause any UB, regardless of which language rule is concerned.** A defined failure is not UB. Unspecified situations do not, by default, authorize UB in safe code: they must be explicitly resolved before normative stabilization.

## 4. Safety Checks and Optimization

Safety conditions may be established statically, checked dynamically **before** the dangerous operation, or guaranteed by the invariants of a correctly implemented safe abstraction.

The **dynamic** route is available only when execution actually has the relevant information and an executable procedure capable of deciding the condition **before** the dangerous operation. The logical decidability of a predicate in a proof assistant does not, by itself, constitute an executable check in ERN.

Failure of a dynamic check in a safe interface must prevent the dangerous operation and result in a defined failure. An implementation may eliminate a semantically required check only if it demonstrates that the condition holds, without changing the permitted observable behaviors.

**Abstract-machine metadata is not mandated at runtime.** Abstract provenance, allocation liveness, per-byte initialization, or a logical authority do not automatically become observable runtime data. A library, instrumented implementation, or specific mechanism may provide the information needed for certain checks; in its absence, guarantees must be established by other means, including static discipline and the contracts of unsafe abstractions.

In particular, the absence of a *data race* is a property of concurrent actions and their synchronization relations, not a condition decidable by simply inspecting one access locally. Its precise semantics belongs to the concurrency specification.

The existence of an efficient path that avoids an expensive dynamic check is an **evaluation criterion** under Charter §§3.2, 3.3, and 12, not a universal obligation of the memory model.

## 5. Contracts of Safe Abstractions

A safe interface must never rely on an unchecked discipline imposed on its caller to preserve memory safety. It may impose **functional** preconditions, but their violation by safe code must remain within the language's defined behaviors.

Every unsafe operation executed by a safe abstraction must satisfy its contract for all states reachable through permitted use of the interface. A safe interface does not turn an unproved unsafe contract into a guarantee.

## 6. Obligations of Unsafe Operations

Unsafety qualifies **operations or abstractions**, not a global program mode.

An unsafe operation must explicitly state each obligation on which its safety depends. **Violating an obligation explicitly defined as a safety condition constitutes UB.** Other errors are subject to the behavior specified by the operation's contract.

Any notation marking an unsafe operation will be determined during syntax design.

## 7. Limits of the Guarantees

Safe code does not automatically guarantee the absence of memory or resource leaks, deadlocks, or stack overflows. These exclusions do not diminish any guarantee in Section 2. Behavior on resource exhaustion, abnormal termination, or cancellation remains to be specified, without thereby making every safe memory-allocation failure or stack exhaustion defined by default.

---

# II. Values, Allocations, and Access Representation

A value, a place, and a means of access are three distinct notions. The abstract machine distinguishes their existence from their permissions and temporal validity.

## 8. Values and Storage Identity

A **value** is semantic content; a **place** is a portion of storage capable of containing that content; a **means of access** allows a place to be designated under certain conditions.

**Values without intrinsic identity (MVS):** A value has no intrinsic identity. Identity belongs to storage or to a resource designated by the value, not to the value itself. Copying a value, transferring an authority, and accessing a place are semantically distinct operations. The access, consumption, and transfer rules within this model are defined in the following sections; copyability and its typing belong to the appropriate specifications.

## 9. Abstract Allocations and Admissible State

An abstract allocation has at least:

- a **unique identity** within the abstract execution;
- an **address space**;
- a **base address**;
- an **extent** expressed in bytes;
- a strictly positive, power-of-two **alignment** satisfied by its base;
- a **live** or **dead** state;
- abstract offset-indexable storage made up of abstract bytes;
- if deallocatable, **deallocation-authority** conditions.

An abstract allocation does not necessarily correspond to a library allocator call. The kernel also represents storage with static or automatic duration, whose particular rules will be defined later.

**Disjointness of live allocations:** Two distinct live abstract allocations in the **same address space** occupy **disjoint** address ranges. Ranges are half-open: `[base, base + size)`. Two disjoint ranges have an empty intersection. Thus, a zero-sized range overlaps no other range.

**Allocation alignment:** Every **registered** abstract allocation, live or dead, has a strictly positive power-of-two alignment; its base is a multiple of that alignment. Valid alignment is a property of admissible states, not merely a creation-time check.

Subplaces returned by an arena or a data stack within an allocation are **not automatically new abstract allocations**: they may share its identity and provenance. The abstract machine is *flat*: it introduces no parent–child hierarchy of allocations.

The base and extent are modeled over natural numbers in this kernel. Constraints on address width, actually available spaces, and possible overflow of hardware representations are reserved for conversion, layout, and ABI rules; they are not implicitly proved by this mathematical abstraction.

**Admissible state and domain:** The abstract state contains registered allocations and a freshness discipline. **Freshness requires that a newly assigned identity has never been assigned before**, even to an allocation that has since died. A monotonically increasing counter is one possible representation, not a language requirement.

Admissible states jointly satisfy:

- **Well-formedness of identities and freshness:** the preceding discipline is consistent with the registered allocations;
- **Disjointness of live allocations:** two distinct live allocations in the same address space do not overlap;
- **Alignment:** every registered allocation, live or dead, has valid alignment and an aligned base.

Normative memory semantics applies to **admissible states**, namely those satisfying these three properties. An empty state is an admissible initial state and allows reachability proofs; it is **not the only admissible initial state**. An initial configuration supplied by the environment or interoperability may be admissible if it satisfies the required invariants. Establishing such conformity belongs to the applicable initialization or interoperability contract.

**Fundamental distinction:** Well-formedness, disjointness, and alignment, as invariants of admissible states, determine the **domain** of the semantics. Their violation in an arbitrary state outside that domain **is not, by itself, a new operational obligation whose violation would be classified as UB**. Relations in a Lean model may nevertheless be mathematically total on such states; their outcomes do not bind the language specification outside the admissible domain.

**Raw creation:** In an admissible state, creation of a live allocation requires a fresh identity, valid alignment, a correctly aligned base, and no overlap with any distinct live allocation in the same space. These conditions are **operation** preconditions; their violation by an unsafe raw operation constitutes UB. They are distinct from domain invariants even when one guarantees some of them. Actual resource reservation may additionally fail in a defined manner according to the allocator contract; that case is not equated with a violation of a raw-operation precondition.

The abstract machine does not mandate a physical allocation table, `next` counter, or liveness flags at runtime; these are semantic and formalization tools.

## 10. Bytes and Initialization

This kernel considers **8-bit bytes**, whose initialized value ranges from 0 to 255.

An abstract byte is either:

- **uninitialized**;
- **initialized**, with a byte value and optional provenance information.

State is tracked **per byte** to permit partially initialized allocations. In this kernel, the provenance component can be represented by an optional allocation identity; this representation may be enriched by the access discipline. This component is **semantic** information: its existence does not imply a provenance tag physically stored in every byte.

Stored provenance comes from the **value and its representation being written**, not automatically from the provenance of the means of access used to perform the write. Rules for propagation of provenance during byte copies and reinterpretations are not yet fixed.

The initial state of a **newly created raw allocation** is wholly uninitialized. Initializing static values or constructing initialized objects are additional operations; it does not follow that all observable static storage starts uninitialized.

“All required bytes are initialized” and “these bytes represent a valid value of type T” are two different properties. Constraints on invalid representations, padding bytes, and type alignment will be specified by the corresponding specifications.

## 11. Abstract Physical Places

A place designates a portion of an allocation's storage. In the minimal kernel, it is defined by that allocation's identity, an offset, and a length. Typed interpretations, subplaces, and fine-grained permissions may extend this representation.

Resolution of a means of access to a place must be explicitly defined. It is **partial**: a means of access produces a place only if provenance identifies a **registered allocation (live or dead)** and the address range is spatially contained within it. Producing a resolved place does not, by itself, prove the right to read or write: liveness, initialization, authority, type, alignment, and concurrency are established separately by the applicable rules.

## 12. Accesses, Addresses, and Provenance

A means of access conceptually contains:

- an **address**;
- **provenance** identifying the designated allocation;
- an **extent** or access length;
- an **access authority**;
- any other information necessary for its validity.

In the elementary memory machine, provenance identifies the allocation; the access discipline in Part IV and following may associate additional constraints with it. **Access authority** (read, write, etc.) is distinct from **deallocation authority**.

Resolution uses provenance, **never simply selecting an allocation at the requested numerical address**. A reused address does not validate an old means of access.

In the abstract memory machine of Parts II and III, elementary read/write authority is ordered `read ≤ write`; this elementary authority does not replace the discipline of `Observe` and `Modify` modes defined below. In this simplified model, the elementary read-authority condition excludes no access carrying either of those two authorities; substantive rules for observation, modification, and revocation belong to the access discipline. An authority may later become state-dependent and be invalidated.

# III. Memory Machine: Accesses and Byte Transitions

The following relations describe effects on allocations and bytes, independently of the higher-level permissions subsequently established by the authority discipline.

## 13. Allocation Identity and Address Reuse

Each creation of an abstract allocation assigns an identity **never reused** during the abstract execution. A dead allocation may remain registered for reasoning purposes without becoming live again.

The same numerical address may be reused after the previous storage has been freed. Such reuse never restores the rights or validity of an access carrying the old allocation's provenance.

Creating a new allocation does not change pre-existing allocations; read/write/deallocation operations do not create fresh identities unless an explicit later rule provides otherwise.

## 14. Restrictive Derivation of Means of Access

A **restrictive derivation** of a means of access:

- preserves the source allocation's provenance;
- designates a **subrange** of the source access;
- confers no authority greater than that permitted by the source.

In the elementary memory machine, provenance has **allocation granularity**, not field or subrange granularity. Finer-grained rights restrictions are determined by the authority discipline defined in Part IV and following.

A valid restrictive derivation is not necessarily the only way to form an address or create a means of access. A safe abstraction may, through mechanisms and invariants yet to be defined, provide new rights to disjoint places; **the creation of rights is not reducible to restrictive derivation**.

Forming an address or a means of access is distinct from **using** it. Merely forming an out-of-bounds address is not automatically classified as UB; precise formation and conversion restrictions remain open in Section 19.

## 15. Typed Reads and Validity Conditions

For an allocation with base `b` and size `s`, an access with address `a` and length `n` is **spatially contained** when `b ≤ a` and `a + n ≤ b + s`. The corresponding ranges are `[a, a+n)` and `[b, b+s)`.

A typed read requires all applicable conditions:

1. provenance resolves to a **live** allocation;
2. the access is **spatially contained** in that allocation;
3. the bytes **required** for the representation being read are initialized;
4. that representation is valid for the read type;
5. read authority is valid;
6. the alignment constraints of the read type are satisfied;
7. concurrency rules are satisfied.

For a zero-length range, the spatial condition permits any address in `[b, b+s]` and requires no initialized bytes. **This does not automatically permit every zero-length typed read**: the operation remains subject to all its other conditions.

Violation of a safety obligation of an **unsafe raw** read constitutes UB. A safe read interface must establish the condition or report a defined failure before the dangerous operation.

Conditions 4, 6, and 7 are not concretely defined by this kernel; they remain explicit, parameterizable obligations. The choice of how to establish them (static proof, genuinely executable dynamic check, abstraction contract) remains open, subject to Section 4. Thus, kernel theorems alone do not prove the complete validity of an ERN typed read.

## 16. Typed Writes and Preservation of the Memory Frame

A typed write requires all applicable conditions:

1. provenance resolves to a **live** allocation;
2. the place is **spatially contained** as specified in Section 15;
3. write authority is valid;
4. the value and its representation are admissible for the type being written;
5. alignment constraints are satisfied;
6. concurrency rules are satisfied.

A valid write replaces the bytes of the written range **byte by byte** with the supplied representation and its provenance information, then marks the affected bytes initialized. It may initialize a previously uninitialized range. Provenance of the written bytes follows from the representation of the value written, not merely from the provenance of the means of access.

Bytes in other allocations and bytes outside the written range in the target allocation remain unchanged; allocation identity and the allocation counter are unaffected. The consequences of replacement for a pre-existing typed value remain to be determined.

Conditions 4, 5, and 6 are not concretely defined by this kernel; they remain explicit, parameterizable obligations. A raw write violating a safety obligation is UB; a safe interface must prevent it or produce a defined failure.

**Read-after-write and non-interference:** A valid write initializes the bytes of the written range. In the absence of an intervening write or invalidation, **every valid raw byte read of a subrange contained in the written range**, including the entire range, returns exactly the corresponding subsequence of the written contents, including abstract provenance information, subject to the other read conditions. A valid write changes neither the result of a valid read of another allocation nor that of a range disjoint from the written range. These properties concern abstract bytes and do not prejudge the reconstruction of a typed value.

## 17. Deallocation and Invalidation of Old Accesses

Successful raw deallocation requires:

1. an abstract allocation that is **live** and deallocatable;
2. **deallocation authority compatible** with that required by the allocation.

Compatibility is a semantic relation; it does not necessarily require the two allocator handles to have numerically identical identities, and it is distinct from access provenance.

Successful deallocation ends the allocation's validity. Accesses carrying its provenance can no longer read or write that old storage. An attempted double deallocation through the raw operation violates a safety obligation and constitutes UB. A safe abstraction that detects an incompatible attempt before performing a dangerous operation may produce a defined failure; this does not require a universal checked-deallocation primitive.

In the elementary memory machine, compatibility is defined between the presented authority and the recorded deallocation token. A library allocator may additionally impose constraints depending on its own state; these do not change the minimal signature of the kernel's compatibility relation.

**Validity of derived rights:** The logical invalidation of an object inside an allocation that is still live—for example, a block following an arena reset—is governed by the authorities, anchors, and end-of-use rules in Parts IV through XIV. It does not change the two elementary deallocation conditions in Section 17.

## 18. Boundary with Concurrency and Data Races

**A *data race* is UB; no execution of safe code can cause one.** This section establishes that guarantee and its interface with the concurrency model, without purporting to define concurrent events and orderings by itself.

A *data race* involves conflicting accesses to overlapping memory ranges from concurrent execution contexts, at least one of which is a write and at least one of which is non-atomic, when the ordering relations required by the concurrency model do not order them sufficiently. This criterion becomes fully operational only with the event and synchronization semantics of Spec 2.

**Normative boundary:** Spec 2 determines, in particular, the exact definitions of events, conflicts, *happens-before*, atomic operations, and memory orders. The elementary memory machine does not claim that a local access check is sufficient to prove the absence of data races.

## 19. Address Conversions and Provenance: Open Boundary

ERN must distinguish:

1. address calculation that preserves valid provenance;
2. extraction of a numerical address representation;
3. reconstruction of a means of access from an integer;
4. external address spaces and accesses, particularly MMIO;
5. representation transformations, particularly tagged pointers and C interoperability.

None of these conversions may allow safe code to fabricate dangerous access authority.

**Undecided:** exposed provenance, strict provenance, or another model; exact rules for integer–pointer conversions, tagged pointers, and propagation through representation copies. These conversions require a separate definition before any guarantee about reconstructing an access from an integer representation; they are not settled by the simplified provenance of Section 12 alone.

---

## 20. Relational Semantics and Outcomes

**State-domain conditions**, **operation-specific obligations**, **the effect of a valid operation**, and **semantic outcome** must be distinguished.

### 20.1 — Normative Transition Relations

Raw memory-model operations are interpreted by **transition relations**. Their role is to determine the semantic outcome without assuming that all their obligations can be computed at runtime. Operation names are semantic designations independent of any particular implementation or formalization.

In an **admissible** state:

- a raw operation satisfying all applicable obligations has a defined `ok` outcome with the specified effect;
- violation of a safety obligation of that operation produces a `ub` outcome (Section 6), **including when the obligation is static**;
- a `ub` transition does not supply a new ordinary state reusable as a valid step.

Memory-machine relations may be deterministic and mathematically total even when certain obligations are not constructively decidable. A classical proof of totality is not a runtime requirement. Modeling a defined failure of resource reservation belongs to the allocator contract: it does not change the classification of violations of safety obligations of raw operations.

### 20.2 — Read Values and Effects of Other Operations

A valid **byte read** does not modify memory state; its `ok` outcome supplies the sequence of abstract bytes actually read, including provenance. A raw typed read must additionally satisfy type, alignment, and concurrency obligations and subsequent value-reconstruction rules. Unlike operations that only transition the state, a read supplies a value together with its successful outcome.

A valid **write** updates its range according to Section 16. A valid **deallocation** ends allocation liveness according to Section 17. A valid **allocation** creates a fresh identity and its storage according to Sections 9, 10, and 13. Non-interference, invalidation, and invariant-preservation properties apply to their `ok` transitions.

### 20.3 — Parametric Obligations and Executions

Read and write obligations not yet concretely defined are **explicit predicates** of the semantic context: they are not tacitly replaced by `True`.

The formalization may distinguish a component with an executable decision procedure from a component whose satisfaction is established by static reasoning or by contract. **This decomposition remains parametric and does not universally prescribe a strategy for each requirement.** It does not permit concurrent safety to be reduced to a simple local test.

A normative relation requires **no decision instance** for these predicates to be stated. A computable function may require a decision instance for conditions it evaluates. Obligations and the deallocation-compatibility relation are fixed as **parameters of an execution's context**; obligation predicates may nevertheless depend on the state and operation. The minimal compatibility relation of Section 17 concerns the presented authority and the deallocation token; additional state-dependent contracts belong to the relevant abstraction.

# IV. Access Discipline and Aliasing Rules

The authority discipline determines which memory operations may be exercised in safe code. A resource may have several identification paths, but only compatible rights may be exercised simultaneously.

## 21. Observation and Compiler-Exploitable Stability

An observation access (`Observe`) permits ordinary reads of the leaves in its footprint, subject to effectively exercisable rights and read conditions. Multiple compatible observations of the same resource may coexist.

**Stability under observation:** While an ordinary observation authority remains active, ordinary data observable through it remains stable. The compiler may exploit this guarantee in its analyses and optimizations, subject to the exceptions declared below.

Stability of **observed contents** is not guaranteed for leaves whose storage is declared `SharedMutable` when permitted shared-mutation operations may execute. This exception removes neither structural exclusivity I1 nor authority-validity obligations. Likewise, a region declared as susceptible to external modification does not benefit from ordinary content stability; its particular guarantees are declared by the storage and its contract. Pinning (`Pinned`) may preserve an address without guaranteeing stability of the data at that address.

## 22. Modification, Footprints, and Indirect Invalidation

A modification access (`Modify`), when effective and exercisable, confers mutation authority over a specified footprint. For ordinary reads and writes, conflicts are measured on the leaves actually covered. For operations that may end a value's use or free its storage, the analysis also includes, according to the value's structure, transitively owned storage whose validity might be affected.

Two independent ordinary accesses are incompatible when they require conflicting authorities on common leaves. Incompatibility may also arise from **validity invalidation without immediate physical overlap**: it is represented by anchors and dependencies (`D`), the effective anchor, anchor-order constraints, and `NoDangling`, rather than by a second aliasing relation independent of the access discipline.

An operation that moves, replaces, ends, frees, or recycles storage must therefore preserve still-active authorities and dependencies on which its validity depends. Ownership of storage and holding an access authority are two distinct relations.

## 23. Disjointness and Splitting

Simultaneous modifications of disjoint regions are permitted when their independence and the validity of their dependencies are established. A safe abstraction may decompose a modification authority into several authorities over independent footprints, without duplicating exclusive rights or creating rights greater than those of the origin.

This capability is modeled by the kernel operation `split` (Section 61, O2). Disjointness may be structurally guaranteed, statically proved, or justified by a prior dynamic check encapsulated in a safe abstraction, including correctly justified internal unsafe operations. For `DeclaredDisjoint`, the normative condition is **leaf disjointness**; under a memory layout satisfying `LayoutWF`, it implies disjointness of the corresponding bytes. Merely asserting disjointness without justification does not authorize splitting.

The existence of the semantic `split` operation does not determine intrinsic language syntax.

## 24. Shared Mutation Declared by Storage

A region may follow a shared-mutation discipline distinct from ordinary accesses. **This property belongs to storage and must be declared by its type**, so the compiler can determine which stability guarantees apply. The mere existence of multiple access paths or a shared address is insufficient to authorize mutation.

`writeShared` (Section 68, O11) is the only kernel operation permitting mutation from an observation, and only for `SharedMutable` leaves satisfying the applicable rights and contracts. Safety conditions may include confinement to an execution context, atomic operations, or appropriate synchronization. Their concurrent semantics and synchronization rules are defined by Spec 2, not by the sequential authority machine (Parts VI through XV). External agents and regions that they may modify must be declared with their specific constraints.

## 25. Duration of Authority Validity

Access restrictions apply **while the corresponding authorities are active**, not necessarily until the end of the lexical block where they were created. Frames and the `release` and `endUse` operations defined below govern their termination. The compiler may place `endUse` at the last permitted use, according to the control-flow rules of Spec 3.

A derived access may depend on resources beyond its immediate physical place: a container, owned storage, a region, an arena, or an abstraction administering validity. A dependent value is subject, in particular, to `AnchorOrder` and `AnchorOrderHeld`. Any operation capable of invalidating an active anchor or storage on which an authority depends must be refused or satisfy a contract establishing preservation of that validity.

## 26. Authority of the Origin

An origin cannot exercise, through another path, authority incompatible with the authority it has derived. During a `Modify` borrow, its effective rights over leaves covered by that borrow are suspended. During one or more derived observations, it retains only capabilities compatible with those observations. These capabilities are determined **leaf by leaf** according to the effective mode in Section 43.

Reborrows, disjoint projections, and returns of authority respect these restrictions. Once incompatible derived authorities become inactive, the origin regains the effective rights permitted by its own origin chain. Thus, a projection does not prohibit all use of the origin: operations on independent leaves remain permitted.

## 27. Consumption, Transfer, and Invalidation

A value cannot be consumed, ended, reset, or transferred in a way that would invalidate an active authority dependent on its validity. By default, transferring the whole value is incompatible with active derived authorities covering its source; exceptions are limited to transitions that actually preserve validity obligations without creating new rights.

The `transfer` operation in Section 63 (O4) is a consuming operation: it marks the source `Moved` and the destination `Init` for the relevant leaves, subject to its preconditions on shape, initialization, rights, holders, anchors, and pinning. It does **not physically move storage owned** by the value. A transfer is prohibited if an in-place leaf being moved is pinned; pinning of owned storage alone does not, by itself, prohibit transferring the value that owns it. The local self-blocking prevention rule also requires that no authority moved into a destination part cover a leaf of its new holder (O4.8).

Dependencies must remain valid after the transition (`NoDangling` and related rules). Conditions required over all control-flow paths, as well as value-passing conventions at calls, belong to Spec 3. No general guarantee of freedom from authority-blocking cycles is added to this contract.

## 28. Global Accesses Without Ambient Authority

Access to global storage, or storage reachable through several paths, cannot bypass ordinary exclusivity or observation stability. In the access discipline, **a global is static storage attached, directly or transitively, to the base frame**. A mutable global is not prohibited in principle; however, it does not confer any ambient authority on a called function.

To exercise authority over a global, the callee must receive a parameter derived and passed by the caller under the rules of `enterFrame` (Section 72, O6), then respect the corresponding effective rights and dependencies. A function's indirect effects create no exception to these rules. The representation and syntactic forms of globals are not fixed here.

## 29. Boundary of the Concurrent Model

The access discipline distinguishes values transferable between execution contexts from values whose access may be shared between such contexts. These properties follow structurally from declared leaves, composition rules, types, authorities, and associated resources; they do not follow merely from a storage address.

Their complete definition, as well as synchronization, confinement, and concurrent-access contracts, belongs to **Spec 2 — Concurrency Model**. The present authority model defines a sequential discipline without imposing a universal synchronization mechanism or a general memory-management runtime.

## 30. General Aliasing Principle

> ERN allows multiple identification paths and multiple compatible accesses to the same resource.
>
> For ordinary accesses, mutation requires exclusive authority over the relevant footprint. Multiple modification authorities may coexist if their footprints and validity dependencies are independent.
>
> Shared-mutation abstractions may define other safe disciplines, notably atomic or synchronized ones, without weakening the rule applicable to ordinary accesses.

# V. Second-Class Derived Accesses

Derived rights are second-class: they are temporary and cannot be duplicated or extended like arbitrary persistent values. The operational machine defines how their holders and origins evolve.

## 31. Nature and Transmission of Derived Accesses

A derived authority is a temporary right tied to an origin. It may be used and passed within the limits of its validity, but does not freely become a persistent value by copying its representation. Its validity depends on its origin, derivation chain, holder, and, where applicable, the anchors of a dependent value.

An authority may be held by the current frame or, in accordance with the kernel's `store` operation and derived operations such as `issue`, by a place. Such controlled placement grants no arbitrary copying, escape, or extension of validity. A value containing a derived authority may be transferred only when its anchors and rights remain valid.

## 32. Reborrowing and Restoration of Rights

While a `Modify` derivative is active, its origin cannot exercise incompatible mutation or observation through another path over the relevant leaves. During derived observations, it retains only its compatible effective rights. Its exercise capabilities are restored when the derivatives blocking them become inactive, subject to its other active descendants and the rights received from its own origin.

The active period may be determined by control flow and local use analysis; it is not automatically fixed to the entire lexical duration of a block. Control-flow analysis itself belongs to Spec 3.

## 33. Footprints and Validity Dependencies

Ordinary read and modification conflicts are evaluated over leaf footprints according to effective modes. Validity dependencies also include resources whose move, replacement, end of use, or release would invalidate an authority, even without immediate physical overlap. Operations ending or releasing a value account for transitively owned storage according to the authority machine.

A global modification of a dynamic container is presumed capable of invalidating accesses to its elements unless its contract explicitly establishes otherwise. Disjoint projections may perform independent modifications under the splitting preconditions.

## 34. Safe Splitting of Authorities

A safe abstraction may split a `Modify` authority into authorities over pairwise disjoint leaf regions. Splitting preserves invariants, prohibits duplicating competing exclusive rights, and maintains restrictions on the origin while derivatives are active.

It may be established structurally, statically, or through a prior dynamic check whose obligations remain the abstraction's responsibility. `split` is defined in Section 61 (O2); this semantic name is not a syntax decision.

## 35. Transfer and Pinning

Value transfer is prohibited when it would invalidate an active derived access. A legal transfer does not turn a second-class authority into a freely copyable persistent reference and must preserve its validity chain and anchor dependencies.

Transferring a value never physically moves storage owned by it. Moving an **in-place** leaf is rejected when that leaf is pinned; pinning only the owned storage does not prohibit transfer of the owning value. Detailed constraints belong to `transfer` (O4), `Pinned`, and pinning invariant I5.

## 36. Shared Mutation and Internal Administration

An abstraction may keep its metadata in `SharedMutable` storage and modify it through `writeShared` to the extent permitted by the applicable rights and contracts. **Shared mutation of metadata does not, however, grant the right to create, recycle, or terminate exclusive authority over the administered storage.** Such operations require `internal` to be exercisable in `Modify` mode from the value administering the storage.

For every administrative abstraction, including arenas, `HandlePool`, and `DataStack`, **`MetaRight` requires `Modify` exercisable on the administering value**. The `writeShared` branch alone is insufficient. `MetaRight` governs the creation or recycling of authorities over existing storage; it does not govern the creation of a fresh allocation by `alloc` (Section 71). Concurrency between calls belongs to Spec 2. Operations issuing, recycling, ending, or invalidating regions must preserve active authorities and dependencies. Allocation through administration shared among simultaneous holders, under an interface not providing such exclusive exercise, cannot be expressed in safe code with only these sequential operations: any synchronized implementation of it belongs to Spec 2. These abstractions remain libraries and add no rights to the kernel.

## 37. Dependent Values and Persistent References

When a value depends on the validity of other storage, that dependency must be carried by an explicit mechanism. In particular, this model retains:

- joint ownership or legal transfer of the resource;
- **non-escaping** dependent values, governed by `depend`, `store`, `AnchorOrder`, and end-of-use operations; they may survive a call if their anchors come from still-valid caller resources;
- library handles checked for identity and generation upon resolution, which are not authorities by themselves;
- validity durations bound to a frame or context, without a universal system of first-class lifetimes;
- safe abstractions encapsulating, when necessary, unsafe operations and proofs of their obligations.

**Not adopted as a universal ERN mechanism:** a first-class persistent reference subject to general lifetime constraints at the type-system level. The above mechanisms are complementary; neither a handle nor a temporary access guarantees the perpetual validity of its target resource on its own.

# VI. Abstract Authority Machine

The components described below constitute the logical state of the sequential discipline. They prescribe neither generalized runtime metadata nor reference syntax.

## 38. Machine State

The access discipline is based on the finite state

\[ S_3=(F,P,I,A,D) \]

where `F` represents the frame stack, `P` the places, `I` their initialization, `A` the authorities, and `D` the validity anchors. Administrative states of arenas and other library abstractions are separate from `S₃`. The external contract `K` is a separate parameter. The internal representation may carry auxiliary information that creates no new rights.

## 39. Execution Frames

`F` is a nonempty stack of identified, non-duplicate frames. Every frame except the initial frame knows its parent. Frames hold temporary authorities and directly local places. The **current frame** is at the top of the stack. `ancestor(f₁, f₂)` means `f₁` is `f₂` or an ancestor of `f₂` in the stack and its call chain.

The base frame, whose identity is 0 in states reachable from the initial state, never exits. An exited frame can neither be the terminal owner of a usable place nor hold an authority that remains active. Frames have semantic existence; no particular runtime representation is required.

## 40. Logical Places, Leaves, and Ownership

A place has an identity, optionally a structural parent, an abstract `kind`, an owner `owner : Frame | Place`, and a logical death marker. Structural parenthood `partOf(p,q)` describes the subplaces of a value; `owner` describes **who keeps the storage** of a root place valid. An owned place may lie outside its owner's direct footprint; ownership and composition are therefore distinct.

A **leaf** is a place with no structural children. `footprint(p)` contains the leaves of `p`, and access rights over a place are evaluated on those leaves. Places transitively owned by a value are not automatically leaves of its `footprint`. A logical unit of the access discipline does not automatically constitute an additional allocation in the elementary memory machine.

A place `p` is **usable** (`Usable(s,p)`) if and only if:

1. `p` exists and is not marked dead;
2. if its owner is a frame, that frame belongs to the stack;
3. if its owner is a place `q`, then `q` is itself usable and the chain terminates at a frame in the stack.

An ownership cycle makes no place usable. `placeFrame(p)` is the terminal frame of this chain when `p` is usable. Structural parts share their parent's owner and death marker. A value may be logically ended by `endUse` without the place that contained it becoming unusable; the substorages it owned may, however, die.

A **root place** has no structural parent. Every **usable** root place has a root authority of own mode `Modify`, with no origin, held exactly by that place's owner (`RootHeld`). This authority cannot be transferred in isolation; root ownership follows a legal transfer of the owning value when necessary.

## 41. Leaf Initialization States

Every tracked leaf has exactly one of the states `Uninit`, `Init`, or `Moved`.

- `Uninit`: no initialized value available in this leaf.
- `Init`: initialized value, subject to type, representation, and storage obligations.
- `Moved`: value consumed by transfer, inaccessible as its former value.

Aggregates may be partially initialized. Both `Uninit` and `Moved` prohibit ordinary reads, while remaining distinct states for diagnostics and end-of-use obligations. An initialization state creates no access permission.

## 42. Authorities, Modes, Holders, and Origins

An authority conceptually has the following fields:

```text
Authority {
    id
    mode: Observe | Modify
    origin?: AuthorityId
    footprint: Set<Leaf>
    holder: Frame | Place
    active: Bool
}
```

`origin` links a derived authority to its current origin. Authorities have fresh identities and well-formed origin chains. A root authority has no origin; a derived authority has one. Creating derived rights does not increase the scope or permitted mode of the origin.

The **holder** (`holder`) is not the **owner** (`owner`). An authority derived by `derive` or `split` is initially held by the current frame; `store` or a permitted transfer may make it held by a place. The derived `issue` operation proceeds through `split` followed by `store`. `release` does not release a root. There is no persistent `Suspended` field: suspension of rights is inferred from active descendants and applies leaf by leaf.

## 43. Effective Rights and Exercise of Authorities

For an authority `a` and a leaf `l`, `effective(s,a,l)` is derived from the active descendants of `a` whose footprint contains `l`:

1. if `a` is inactive or does not cover `l`, its effective mode is absent;
2. if no active descendant covers `l`, the effective mode is the own mode of `a`;
3. if an active descendant with own mode `Modify` covers `l`, the effective mode of `a` is absent;
4. otherwise, when the covering active descendants are `Observe`, the effective mode of `a` on `l` is `Observe`.

The effect is **local to each leaf**: after splitting a region, the origin may retain effective `Modify` over undistributed leaves.

Requested modes are ordered `Observe ≤ Modify`. `ExercisableAt(s,a,m)` means:

- `a` is active and its own mode permits `m`;
- either `a` is held by the current frame;
- or `a` is held by a place `p`, and the current frame has, over **all** leaves of `p`, an authority itself exercisable in mode `m` with sufficient effective mode.

The latter clause is recursive along the holder chain. Thus, being active or covering a leaf does not automatically make an authority exercisable. `HasRight(s,m,p)` means the current frame has exercise in mode `m` and sufficient effective mode **over every leaf in `p`'s footprint**. Every operation requires the modes it actually needs; an authority's own mode alone is insufficient.

## 44. Dependencies and Effective Anchors

`D(p)` is the set of authorities serving as **validity anchors** for place `p`. An anchor is valid as long as the authority it names is active. Dependencies of contained values are accounted for transitively. Relevant dependencies follow the value during transfer; those of its container do not automatically follow a part transferred in isolation.

For an authority `x`, its **effective anchor** is the root reached by traversing its origin chain. It does not necessarily coincide with its current holder. Lifetime constraints are calculated from the frame of that effective anchor and the frames of places that remain usable. A dependency cannot create a right or artificially extend a lifetime.

`AnchorOrder` requires, for every anchor `x ∈ D(q)` of a usable place `q`, that the frame of the effective anchor of `x` be the frame of `q` or one of its ancestors. `AnchorOrderHeld` imposes the same rule on every **active authority held** by `q`. These conditions apply to the resulting states of operations that move or create holder relations.

## 45. Parameters, Returns, and Reanchoring

A call parameter is an **active derived authority held by the caller** before being passed to the callee; its original provenance may go back to an earlier frame. This interpretation does not require that the authority was originally derived in the calling frame; that additional requirement belongs to Spec 3. The caller **yields** the authority to the new frame: it does not simultaneously retain a copy. If the authority remains in that frame upon return, `exitFrame` releases it; **it is not automatically returned to the caller**. To retain its own right, the caller may pass a **fresh derivative** of the authority it wishes to keep: this is ordinary reborrowing. The definition of ergonomic calling conventions is deferred to Spec 3.

A result is returned by a legal `transfer` into the result place provided by the caller as a `Modify` parameter. Surviving authorities and their dependencies are reanchored by `exitFrame` to still-valid origins. There is no standalone correspondence `M` and no implicit escape permission.

## 46. Arenas as Library Administration States

Each entry belongs to the library's abstract state, **separate from kernel state `S₃`**. It has the following fields:

```text
ArenaEntry {
    storage: PlaceId
    internal: AuthorityId
    available: Set<Leaf>
    issued: Set<(Region, AuthorityId)>
}
```

A region is **available if and only if each of its leaves belongs to `available`**; the empty region is always available. Issuance removes the leaves of the issued region from `available`. Reset restores all leaves of the administered storage to that set. The registry and its updates belong to the abstraction contract and create no kernel permissions.

The arena is **live** if `internal` is active. The **arena value** is the place holding `internal`, distinct from the possible owner of `storage`. Administered storage may be local, static, allocated, or issued by another arena, under `newArena` preconditions and applicable invariants. `available` and `issued` remain **in the library's arena entry**.

## 47. Initial State

The kernel's initial state contains only base frame 0 and the declared static storage. Every static leaf has its declared initial state, `Init` or `Uninit`. The roots of static places directly owned by frame 0 have a root `Modify` authority held by that frame; a static may also be owned by another static, in which case its root authority is held by the latter. The ownership graph of statics is acyclic: no static is owned, directly or transitively, by itself. The initial state invents no dynamic allocation, derived authority, or implicit anchor. The initial arena registry belongs to library state and is empty. The initial frame does not exit.

## 48. External Parametric Contract

`K` contains the predicates `DeclaredDisjoint`, `SharedMutable`, `Pinned`, `ExternalDone`, `Deallocable`, `FreeCompat`, and `Satisfiable`. Their obligations are specified in Section 80. `K` can neither fabricate access rights nor remove an obligation of the Charter. The predicate `Invalidates` is not part of this contract.

# VII. Invariants of Reachable States

Machine states are subject to structural, validity, and exclusivity requirements preserved by permitted transitions under their declared external contracts.

## 49. WF3 — Well-Formedness of Frames, Places, and Authorities

`WF3(s)` is a **predicate on state `s`**. It jointly requires:

1. a nonempty, duplicate-free frame stack, every frame having a valid identity and, except for the base frame, a valid parent; frame-parent relations are well-founded;
2. a place structure whose composition links are valid and **acyclic**; every structural part shares its parent's owner and death marker;
3. valid owners of type frame or place, and **well-founded** ownership chains reaching a live frame for every usable place;
4. footprints consisting exclusively of leaves of existing places;
5. authorities with valid identities and modes, whose existing origins form **acyclic** chains ending at a root authority;
6. `RootChain`: every origin chain of an authority covering a leaf ends at the root of the **same structural root place** as that leaf;
7. `RootHeld`: every usable root place has its active root `Modify` authority, with no origin, held exactly by its owner;
8. holder validity: every active authority is held by a frame present in the stack or by a usable place.

Numerical ordering of identifiers, parent precedence over child in a list, and bounds on generated identifiers may be used **to represent or prove** this well-formedness in a formalization; they are not normative restrictions on place or authority identities. Preservation of `WF3` by a transition is a **required property of transitions**, not an additional clause of the state predicate. `WF3` does not impose any particular physical object layout: that belongs to refinement into the elementary memory machine.

## 50. I1 — Structural Exclusivity

For two active authorities **unrelated by derivation** covering the same leaf, their own modes must both be `Observe`. This rule also applies to leaves identified as `SharedMutable`; their particular mutation is governed by the `writeShared` contract and creates no exception to I1.

Exclusivity of **effective** modes (`effective_exclusive`) is a consequence of I1 and the definition of `effective`, not the definition of I1. On a leaf, two incompatible authorities cannot simultaneously possess incompatible effective rights. The only permitted independent ordinary coexistence is `Observe` / `Observe`.

## 51. I2 — Conservation of Rights

A derived authority covers only a subfootprint of what its origin chain permits and does not elevate its mode. Derivation and splitting restrictions do not allow duplication of an exclusive right over a leaf. Every active authority is linked to a valid origin according to state and reanchoring rules: an origin is **valid** if and only if it is active, so the origin of an active derived authority is active. Partial suspension follows from `effective`.

## 52. I3 — Validity of Anchors and Dependencies

Every explicit anchor of a still-usable place is valid. An operation cannot invalidate an anchor retained by a place that remains usable. Transitive propagation of dependencies from contained values does not change this obligation. Dependencies are not permissions and are insufficient to justify an access.

## 53. I4 — Consumption and Movement

A `Moved` leaf cannot be read as if it still contained its previous value. Moving a value does not preserve two copies of an exclusive authority. Initialization state and authority-exercise state are separate checks.

## 54. Anchor Ordering and Absence of Orphan Rights

`AnchorOrder` and `AnchorOrderHeld` are defined in Section 44. `NoDangling` prohibits an **active** authority from covering a leaf belonging to an unusable place; the invariant does not say that a leaf is initialized. `NoOrphan` requires every active authority held by a place to be connected to a frame in the stack through a **finite, non-repeating chain** of authorities: the first link is held by a live frame, and each active link **structurally covers the entirety** of the place holding the next link. The link need not have an effective mode over that place. `NoOrphan` guarantees neither the exercisability of all stored authorities nor freedom from blocking.

## 55. ArenaInv — Invariant of the Arena Abstraction

`ArenaInv` is an invariant of the **library contract**, not an additional predicate of kernel state. For every live arena:

- `storage` designates an existing, usable place; the footprint of `internal` is exactly the footprint of `storage`;
- `internal` is active, with own mode `Modify`, held by the arena value;
- available leaves and issued regions belong to the administered storage;
- two still-active issuances have disjoint regions; no leaf of a still-issued region simultaneously belongs to `available`;
- every still-issued block authority is a derivative of `internal` complying with exclusivity and validity rules;
- anchor and ownership restrictions are respected.

Arena entries do not, by themselves, constitute an additional storage owner. Two live arenas may cover common leaves when their `internal` authorities are distinct and their effective rights are compatible; no **global** disjointness of arena footprints is imposed.

## 56. Uniqueness of Live Administration

**An authority identity may serve as `internal` for at most one live administrative abstraction**, whether an arena, `HandlePool`, `DataStack`, or another library administrative instance. Before registering a new abstraction, its creation operation must jointly check the absence of that identity from **all relevant registries of live administrations**. Uniqueness concerns the identity of the `internal` authority, not merely possible overlap of footprints: abstractions with distinct `internal` identities are not forbidden merely because their footprints overlap. Library contracts must make the information required for this guard available to the creation operation; checking only an abstraction's own registry is insufficient.

**This guard is not a condition for any safety property in Section 57.** The effective right (Section 43, case 3) already prohibits a second issuance over leaves covered by an active block derived from the same authority. Rather, the guard preserves the **abstraction contract**: without it, simultaneous administration of the same `internal` could cause `reject` instead of `fail`, or reissue a previously released block that the first administration still considers unavailable. It creates neither permissions nor allocations and introduces no general detection of authority cycles. Its physical representation and encapsulation of library registries remain outside the kernel.

## 57. Main Invariant

\[
Inv3 = I1 \land I2 \land I3 \land I4 \land AnchorOrder \land NoDangling
\]

On states reachable from `S3.init statics` under `DDSound(K)`, the kernel guarantees:

\[
WF3 \land Inv3 \land AnchorOrderHeld \land NoOrphan
\]

`ArenaInv` (Section 55) belongs to the library abstraction: it is not included in this main kernel invariant.

**I5:** every pinned leaf, statically (`K.Pinned`) or dynamically (an active pinning obligation, Section 74), belongs to a usable place.

I5, associated with pinned storage, remains a **specialized obligation** of `K.Pinned`, not a clause automatically implied by sequential accesses alone. This property is required for reachable states under the declared assumptions. Its correspondence with allocations and bytes requires the refinement defined below.

# VIII. Definition of Transitions and Management of Authorities

The following operations are abstract transition rules. They distinguish rejection by the discipline, defined failure, and a permitted transition.

## 58. Transition Outcomes

Every operation has a conceptual outcome among:

```text
Outcome3 = ok(new_state) | reject | fail
```

`reject` means that the static discipline does not permit the step; it is neither an implicit runtime trap nor `ub` in the elementary memory machine. `fail` is a **defined failure** leaving the state unchanged; **only `alloc` may produce it in the O1–O16 kernel**. Other kernel operations produce `ok` or `reject`. Library-abstraction operations, including `issue` (§77), may define their own `fail` cases. Where such failure is provided, static preconditions are checked before dynamic availability, according to the operation's contract.

An `ok` transition must satisfy its preconditions, apply exactly its prescribed effects, and preserve the relevant invariants. No transition fabricates a permission to make its conclusion true. Holder and anchor changes are evaluated in the **resulting state** when a rule explicitly so provides.

## 59. Implicit Preservation of Modes and Anchors

Changes in effective authority are **derived** from active authorities and their origins; no `Suspended` indicator is mutated. Access operations (O9–O11) do not change an anchor without an explicitly authorized effect of transfer, `depend`, `store`, release, or reanchoring. Leaves becoming `Init` do so through a permitted write (`write3`, `writeShared`, `store`, including during a derived `issue`) or a transfer from a corresponding source leaf already `Init`; leaves initialized in `S3.init` are declared as such.

## 60. O1 — Derivation of an Authority

**Preconditions**

1. `source` is an active derived or root authority, and `ExercisableAt(s,source,mode)` holds; its origin chain and anchors are valid: every authority of its origin chain, its effective anchor included, is active.
2. The leaves of `region` exist and belong to the footprint of `source`; `mode` does not exceed the available effective right on these leaves.
3. The addition preserves exclusivity I1: no unrelated active authority becomes incompatible with the derived right, and already-active descendants are respected.
4. The new holding frame is the live current frame. The admissible state's footprint and anchoring restrictions remain true.

**`ok` effect:** A new active authority with fresh identity, origin `source`, requested mode and footprint, and held by the current frame is added. The source remains active; its effective modes are recomputed per leaf. No storage or place anchor is created. Multiple compatible observations remain permitted. **Other outcome:** `reject`.

## 61. O2 — Splitting Authorities

**Preconditions**

1. `source` is active and exercisable by the current frame with sufficient modification rights over the relevant leaves.
2. Each region lies within the available, effectively modifiable footprint of the source.
3. Regions are pairwise disjoint under structural composition or contract `K.DeclaredDisjoint`, subject to obligation `DDSound(K)`; no exclusive right already distributed is overlapped.
4. Creation of the derivatives respects origins, conservation I1/I2, and validity obligations.

**`ok` effect:** An active derived `Modify` authority held by the current frame is created for each region. `source` remains active; its effective modification capability disappears only over distributed leaves and remains on undistributed leaves. Authorities are split logically: `split` performs no physical allocation. **Other outcome:** `reject`.

An unjustified declaration of disjointness may invalidate the proof: without `DDSound`, an accepted `split` may violate I1. Constructing zero-sized subregions is not identified with an allocation of the elementary memory machine; the case of an empty shape in `alloc` is distinct.

## 62. O3 — End of a Derived Borrow

**Preconditions**

1. `authority` is active **and derived**: an authority with no origin is rejected.
2. It is held by the current frame, or by a place `p` on which the current frame has exercisable `Modify`.
3. No active descendant of the authority prevents its release; no other still-usable value may lose a required anchor.
4. If the authority is stored in its holding place, that place is exempted from the check “this authority still appears among the anchors” **only because the effect removes that anchor at the same time**. An anchor with the same identity attached by `depend` to another usable place continues to block the step.
5. Applicable abstraction contracts remain satisfied.

**`ok` effect:** The authority becomes inactive and can no longer be exercised. It is removed from its holding place's anchors when stored there. Effective modes of its origins are recomputed, allowing unblocked rights to return. There is no implicit deallocation. **Other outcome:** `reject`.

# IX. Transfer, Dependencies, and Storage of Rights

These transitions govern value consumption and the controlled movement of their dependencies. A valid transition can neither create an additional permission nor discard a surviving anchor.

## 63. O4 — Consuming Value Transfer

**Preconditions**

1. `source` and `destination` are usable, and the current frame has exercisable `Modify` over their relevant footprints.
2. Source and destination have the **same shape of ordered subtrees**. The `i`-th child of each source part corresponds to the `i`-th child of the corresponding destination part; all nodes are matched. Structural field identity is positional, not an arbitrary matching of children.
3. **All** source leaves are `Init`, and **no** destination leaf is `Init`. The source and destination footprints are disjoint.
4. No exclusive authority is duplicated; validity of derived authorities and active projections is preserved. No active derived authority held outside `source` covers a source leaf, except the authorities through which the step exercises its `Modify` right over `source`: the exercisable authority on which that right rests and its origin chain. Other active authorities remain subject to this check.
5. **No in-place source leaf is pinned**, either statically (`K.Pinned`) or dynamically (`pin`). Storage merely **owned** by the source, which is not itself moved by the transfer of that value, does not prevent this transfer.
6. Dependencies of all still-usable places following the value remain valid; non-escape constraints and `AnchorOrder` are checked in the **resulting state**, including transferred anchors of owned places that remain usable.
7. All moved held authorities, including those of owned storage, satisfy `AnchorOrderHeld` in the resulting state; no authority may escape a local anchor on the grounds that its containing value was transferred.
8. **Local self-blocking prevention:** For each active authority held before the step by a part `r` of `source` whose holder becomes the corresponding part `corr(r)` of `destination`, that authority's footprint contains **no leaf** of `corr(r)` in the resulting state. Transfer is rejected if this local check fails; no global authority-acyclicity check is imposed.
9. **Destination usability:** `destination` is usable in the resulting state.

**`ok` effect:**

- every source leaf becomes `Moved` and each corresponding destination leaf becomes `Init`;
- every authority held by source part `r` acquires as its new holder the corresponding destination part `corr(r)`, not indiscriminately the destination root;
- places owned by `r` become owned by `corr(r)`; their roots follow this owner according to `RootHeld`;
- value dependencies follow the corresponding places under validity guarantees; no authority is created or duplicated;
- destination places receive the transferred values and rights without automatically moving storage not owned by a source part.

**Other outcome:** `reject`. `transfer` to a call result is subject to these same rules.

A partially initialized structure may be transferred **field by field**, but only for fields individually eligible for transfer. This does not automatically destructure a value that owns storage **at the container level**: that storage stays with the container if the container is not transferred. Conversion between structures with permuted fields must be handled separately, not as a `transfer`.

## 64. O5 — Explicit Attachment of an Anchor

**Preconditions**

1. `result` is a usable place over which the current frame has exercisable `Modify`.
2. `anchor` designates an active, valid authority representing a real dependency of the relevant rights or storage; a declared dependency cannot extend an origin's lifetime.
3. Existing anchors are preserved and the addition respects `AnchorOrder`: the effective anchor's frame is the frame of `result` or an ancestor thereof.
4. Every dependency carried by a contained value remains represented in the transitive obligations of its container.

**`ok` effect:** `anchor` is added to `D(result)`; the container's transitive dependencies account for it. No additional access right is created. **Other outcome:** `reject`.

A safe interface must declare dependencies covering those actually required by its implementation; the annotation itself is not presumed true. An unsafe abstraction bears the obligations of its contract.

## 65. O8 — Controlled Storage of an Authority

**Preconditions**

1. `authority` is active, **derived**, and held by the current frame; a root authority can never be stored by `store`.
2. `target` is a usable **leaf** under exercisable `Modify` by the current frame. It holds no other **active** authority. Its data already being `Init` does not by itself prohibit the operation.
3. The stored authority covers neither a leaf of `target` nor the leaves of storage transitively owned by it.
4. The effective anchor of `authority` respects `AnchorOrder` relative to the frame of `target`; other dependencies are preserved.
5. **In the resulting state**, `target` remains under exercisable `Modify` by the current frame (`store_keeps_target_reachable`), and `AnchorOrderHeld` remains true. This is a genuine additional precondition, not an automatic consequence of the preceding ones.

**`ok` effect:** The holder of `authority` becomes `target`; the authority is added to `D(target)`; **only** leaf `target` becomes `Init`. Other fields of a structure, even adjacent ones, do not change their initialization state. **Other outcome:** `reject`.

Overwriting an active authority already held by the leaf is prohibited; its explicit release may make the target reusable. The resulting-state clause does not by itself prohibit all cycles possible after other operations: general freedom from blocking (`NoLock`) is not adopted here.

# X. Reading, Writing, and Initialization

A leaf's initialization state and the effective right to access it are two distinct conditions.

## 66. O9 — Safe Reading of Regions

**Preconditions**

1. Every leaf being read belongs to a usable place and is `Init`.
2. `access` is an authority exercisable in `Observe` mode over the region; its **effective** mode actually permits observation of each leaf being read.
3. Required anchors are valid, and the type and storage contract permits this read.

**`ok` effect:** The logical read succeeds, without modifying `F`, `P`, `I`, `A`, `D`, or arena entries. **Other outcome:** `reject`.

`Moved` and `Uninit` cannot be read. This definition does not replace concrete representation and pointer checks of the elementary memory machine.

## 67. O10 — Ordinary Write

**Preconditions**

1. Targeted leaves belong to usable places, and `access` is exercisable in `Modify` mode with **effective** `Modify` right over each leaf.
2. No incompatible ordinary authority holds an incompatible effective mode over the written leaves (I1).
3. Anchors and constraints of the relevant types, storage, and abstractions remain valid.

**`ok` effect:** The logical write sets the actually written leaves to `Init` and does not modify authorities or their anchors. An unwritten leaf does not become `Init` by this effect. **Other outcome:** `reject`.

## 68. O11 — Write Under Shared Mutation

**Preconditions**

1. Every leaf in the region is usable and declared `K.SharedMutable`.
2. `access` is exercisable in a mode **at least** `Observe` and has a present effective mode on every leaf, either `Observe` or `Modify`; exercising an authority without an effective mode is insufficient.
3. Dependencies are valid and the particular shared-mutation discipline guaranteed by `K.SharedMutable` applies.

**`ok` effect:** Actually written leaves become `Init`; authorities and their structural exclusivity I1 do not change. **Other outcome:** `reject`.

`writeShared` may update metadata under an `Observe` authority when the contract permits. Stability of observed contents is not automatically guaranteed, and this kernel **does not prove** the absence of data races: that requires the concurrency model's guarantees.

# XI. End of Use, Deallocation, and Allocation

The logical end of a value does not necessarily entail deallocation of its storage. The following operations treat initialization, ownership, and physical release separately.

## 69. O12 — Logical End of a Value's Use

**Preconditions**

1. `place` is usable and the current frame has exercisable `Modify` over it.
2. No active descendant over the leaves of `place` **or storage that dies with it** is held outside the places dying with `place`, in a way that would prevent rights from returning or being invalidated. The authorities through which the step exercises its `Modify` right over `place`, namely the exercisable authority on which that right rests and its origin chain, are exempt from this check. Moreover, no authority that the effect makes inactive (held by `place` or by a place dying with it, transitively owned storage included) has an active descendant, whatever its footprint, that the same step does not make inactive.
3. No place **remaining usable after the effect** depends on an authority held by `place`, its root, or an authority that would become inactive when an owned holder dies.
4. **No leaf whose use ends, including transitively owned storage, is pinned**, either statically (`K.Pinned`) or dynamically (`pin`). A dynamic pinning obligation must be legally removed by `unpin` before this step.

**`ok` effect:** The leaves of value `place` become `Uninit`; `place` **remains usable as a place** and may legally be reinitialized. Authorities held by `place` and dead substorages are released; dependencies of the ended value are removed; transitively owned places that cease to live are marked dead. The operation does not automatically trigger physical deallocation in the elementary memory machine: an unfreed allocation may constitute a leak, which this guarantee does not prohibit. **Other outcome:** `reject`.

## 70. O13 — Release of an Owned Storage Unit

**Preconditions**

1. `place` is a **root of storage owned by a value** (`OwnedRoot`), not an ordinary local directly owned by a frame and not part of an aggregate.
2. `K.Deallocable(place)` is established, and `K.FreeCompat(place,auth)` justifies deallocation authority `auth`; this identifier is opaque to the authority kernel.
3. The current frame has exercisable `Modify`; no active derivative over the footprint being freed is held outside holders that die; no surviving place is anchored to an authority of the released region or of its dead holders. The authorities through which the step exercises its `Modify` right over `place`, namely the exercisable authority on which that right rests and its origin chain, are exempt from the check on active derivatives. Moreover, no authority that the effect makes inactive (an authority of the released region, its root included, or an authority whose holder dies) has an active descendant, whatever its footprint, that the same step does not make inactive.
4. No leaf of the released unit is statically or dynamically pinned. Ending external use does not silently turn a still-pinned leaf into a releasable unit.

**`ok` effect:** `place` and the storage that ceases to live are marked dead; authorities of those regions, including their corresponding roots, become inactive, as do authorities whose holders die. Surviving dependencies must remain valid. Every realization of `free` must satisfy the corresponding deallocation relation of the elementary memory machine (Part III). **Other outcome:** `reject`.

## 71. O14 — Allocation of a New Storage Root

**Static preconditions**

1. `shape` is a **nonempty** abstract shape, represented like the local places of `enterFrame`; an allocation of **zero physical size** may be represented by a logical one-leaf shape.
2. The provider is a usable place, and **all leaves of the provider** are `Init`; updates to its metadata are permitted through exercisable `Modify` or a valid `writeShared` over `SharedMutable` metadata.
3. The current frame has exercisable `Modify` over `owner`; new identities and ownership relations must respect `WF3`, `RootHeld`, and liveness restrictions.

**Outcomes**

- `reject`: a static precondition does not hold;
- `fail`: static preconditions hold, but `K.Satisfiable(provider,shape,s)` is false in the state under consideration; **no state change**;
- `ok(s')`: creation of a **new storage root** with fresh identity, owned by `owner`; its leaves start `Uninit`, its new root `Modify` authority with no origin is held by `owner`; provider metadata is updated only in accordance with its modification rights.

Allocation success depends on the provider's state: it does not constitute a right to invent physical memory. Any realization of this operation must satisfy the `AllocStep` relation defined by the rules of Sections 9 and 13.

# XII. Call Frames and Return of Authorities

Frames are execution units that receive authorities, introduce locals, and have exit rules distinct from Spec 3's value-passing conventions.

## 72. O6 — Entering a Frame

**Preconditions**

1. The calling frame is the current frame and is live. Each parameter passed to the callee is an active, derived authority held by the caller before the step; the caller is **not necessarily** the frame in which the authority was first derived.
2. Modes, footprints, anchoring, and parameter-passing rules permit this change of holder; introduction of locals preserves well-formedness and the validity of their roots.
3. **Origin protection on entry:** for each `Modify` parameter with direct origin `o`, `o` is exercisable in **no mode** (neither `Observe` nor `Modify`) in the **resulting state**, once the new frame's parameters and locals have been created.
4. **G4:** `AnchorOrderHeld` is checked over the complete resulting state.

**`ok` effect:** A new child frame is pushed onto the stack; active parameters **are yielded** to that frame, which becomes their sole holder; local places and their root authorities are created; valid anchors inherited from the caller are preserved. This transfer creates no additional rights. **Other outcome:** `reject`.

This clause establishes **entry protection**. It does not prove the stronger property of protection throughout the **entire** invocation following other releases or reanchorings. While a `Modify` parameter remains active, its direct origin remains subject to effective-mode restrictions. Any additional protection throughout the invocation is deferred to Spec 3.

## 73. O7 — Exiting a Frame

**Preconditions**

1. The current frame is not the initial frame and has a surviving caller.
2. Results that must survive have already been legally transferred to their destinations; no active authority or dependency may remain invalidly attached to locals that are about to die.
3. **No leaf of a place that dies with the frame, including transitively owned storage, is pinned**, either statically (`K.Pinned`) or dynamically (`pin`).
4. Iterated reanchoring of surviving authorities and anchors reaches the **first surviving active origin**, held either by a surviving frame or by a usable place whose terminal owner survives; it is not permitted to skip a surviving origin merely because it is held by a place. The operation is rejected when no suitable surviving origin exists, particularly if the chain reaches a root of the exiting frame.
5. Validity of anchors of surviving values and `AnchorOrderHeld` are checked **in the resulting state**. Other state invariants and resource contracts are respected.

**`ok` effect:**

- the current frame is removed from the stack; its untransferred locals and substorages dying with them become unusable;
- authorities still held by that frame, or by places that have become unusable, are released;
- origins of surviving derived authorities are reanchored to the **first surviving active origin** of their chains, whether held by a frame or a usable place, and the `D` anchors of surviving values are correspondingly reanchored;
- reanchoring changes **neither the footprint nor the own mode** of an authority; parameter identities and relations specific to the frame cease their operational role;
- the calling frame becomes current again.

**Other outcome:** `reject`. Exiting does not entail automatic physical deallocation of all dead places. Deferred cleanup (`defer`) lies outside this kernel. Reanchoring may change the current `origin` relation; protection of a historical borrow lineage during an invocation is a distinct, deferred question.

# XIII. Pinning, Statics, and External Commitments

Pinning forbids certain movements or ends of lifetime. It is not a general guarantee of content immutability.

## 74. O15 — Dynamic Pinning

**Preconditions:** `place` is usable, the current frame has exercisable `Modify` over the relevant leaves, and the operation respects applicable pinning obligations.

**`ok` effect:** A dynamic pinning obligation of fresh identity is installed on the relevant leaves. A leaf is dynamically pinned while at least one active pinning obligation covers it. While an obligation is active, `transfer`, `endUse`, `free`, and `exitFrame` are rejected if they act on leaves it pins; removal of this obligation requires `unpin` under `K.ExternalDone`. Pinning does not make contents immutable. **Other outcome:** `reject`.

## 75. O16 — Removal of Dynamic Pinning

**Preconditions:** `unpin` designates one active dynamic pinning obligation, installed by `pin` on `place`; `place` is usable, the current frame has exercisable `Modify`, and contract `K.ExternalDone`, applied to that obligation, attests that all relevant external use has ended.

**`ok` effect:** The designated dynamic pinning obligation ends, and only that one: a leaf it covered stays pinned while another active obligation covers it. The step does not itself modify values, their initialization, or their access authorities. Static obligations are not removed by this operation. **Other outcome:** `reject`.

**Associated static rule (`StaticPinnedBottom`):** Statics designated by `K.Pinned` must be places **directly** owned by the **base frame**, not merely transitively owned by a static value. This restriction ensures that they do not die when an intermediate frame exits.

# XIV. Arenas and Collective Invalidation — Reference Abstraction

An arena is a **library abstraction**, not a memory-kernel primitive. Operations O17 through O19 are **derived** from operations O1 through O16 and abstraction-specific metadata: `newArena` registers an administration without modifying the kernel; `issue` performs `split` followed by `store` (after checking availability); `reset` performs a `Modify` derivation over all storage—through `derive` or `split`—then `release`, before restoring availability. Their contract below is **normative for the standard-library arena** until Spec 10 takes responsibility for it. It authorizes neither new permissions nor an additional access machine. Arena entries (Section 46) constitute the abstract state of this administration; the guard in Section 56 belongs to its consistency contract. The contracts of `HandlePool` and `DataStack` belong to their library abstractions and are not defined here.

## 76. O17 — Creation of an Administered Arena

**Preconditions**

1. `storage` is an existing, usable place under exercisable `Modify` by the current frame. It may be local, static, allocated, or a block issued by a previous arena.
2. `internal` is explicitly named by the caller, exists, is active, has own mode `Modify`, and `ExercisableAt(s,internal,Modify)` holds.
3. `internal` is **held by a place**: that place is the arena value; `footprint(internal) = footprint(storage)`.
4. **Unified administration guard (Section 56):** no **live** administrative abstraction, whether an arena or a library instance such as a handle pool, already uses this `internal` identity. The relevant registries of library administrations are consulted before registration. Two distinct identities may cover common leaves: this is not in itself grounds for rejection.
5. All leaves of the arena value holding `internal` are already `Init`; construction does not initialize them implicitly.
6. Dependency, holder, storage, and administration relations respect, in the resulting state, `WF3`, I1, `AnchorOrder`, and `AnchorOrderHeld` over the whole kernel state, and the new entry satisfies `ArenaInv` (Section 55).

**`ok` effect:** A live entry `{storage, internal, available, issued}` is added; the initial `available` set represents the administered storage, and `issued` is initially empty. Registering the entry fabricates no place, access right, or `Init` state. **Other outcome:** `reject`.

The identity of `internal`, not the index of `storage`, is the key to preventing duplication of live administrations. No global constraint requires footprints of live arenas to be pairwise disjoint.

## 77. O18 — Issuing an Arena Block

**Static preconditions**

1. The `arena` entry exists and is live; `internal` is active. `MetaRight` requires exercisable `Modify` over the arena value holding `internal` (Section 36). Mutation of metadata through `writeShared` alone does not satisfy this condition.
2. `region` belongs to the administered storage; `destination` is a usable **leaf** holding no active authority; the destination can legally receive the block value in mode `Modify`. The fact that `destination` is already `Init` is not in itself grounds for rejection, in accordance with O8.2.
   **Local self-blocking prevention: leaf `destination` is not in `region`, including when the region is declared available.** This condition is static and is checked before an availability `fail`.
3. Applicable **static** validity and non-escape restrictions for the destination are satisfied. The `AnchorOrder` check depending on the new anchor is performed on the **simulated resulting state**, after the availability check described in point 4; it cannot turn an unavailable issuance (`fail`) into `reject`.

**Availability and exercisability checks**

4. If static conditions hold but **at least one leaf of `region` does not belong to `available`**, the operation produces **`fail` and leaves the entire state unchanged**. The empty region is always available. An unavailable region does not permit a prior static rejection to be bypassed.
5. If the region is available, the effective mode of `internal` on that region must permit `Modify`; otherwise the outcome is `reject`.
6. The simulated result must satisfy `AnchorOrderHeld` **in the resulting state**; moreover, **in that resulting state, `destination` must remain under exercisable `Modify` by the current frame**, in accordance with O8.5. Issuance into a value with a longer lifetime than a local anchor is not made valid merely by storing it in the caller.

**`ok` effect:** A block authority of fresh identity, derived from `internal` and of mode `Modify`, is issued for the region; it is held by `destination`, which receives the corresponding anchor. The leaves of the region leave `available`, and the issuance is added to `issued` with its authority. **Only leaf `destination` becomes `Init`**; no other leaf of the arena value changes initialization. Previous issuances remain intact and valid. Issuance does not automatically install anchors on third-party values: they must use their lawful dependency mechanisms.

**Outcomes:** `ok`, `fail` (region unavailable after static validation), `reject` (static rule, effective right, or anchoring not satisfied). The destination may be a leaf of the arena value itself: its initialization then constitutes **an explicit write to that destination**, not implicit initialization of the entire arena value's metadata.

## 78. O19 — Collective Arena Reset

**Preconditions**

1. The entry exists and is live. **`MetaRight(s,arena)` requires exercisable `Modify` over the arena value**, in accordance with Section 36. `writeShared` over metadata alone, even when legal, does not replace such exercise. `internal` and the arena's other restrictions remain valid.
2. **No active authority derived from `internal` covers a leaf of the administered storage.** A derived authority with an empty footprint does not, by itself, block `reset`.
3. No still-usable place depends, directly or transitively, on an anchor in the **strict origin subtree of `internal`** (`internal` itself is excluded) that covers a leaf of the administered storage. Under precondition 2 and invariant I3, this condition follows from the absence of active descendants covering the storage, and remains explicit in the abstraction contract. Validity obligations of other nested arenas remain satisfied.

**`ok` effect:** All **leaves** of the administered storage become available again, and the issuance list is cleared under the arena contract. No still-active derived authority covering those leaves may remain, by precondition 2; an empty-footprint derivative may remain active without designating any recycled leaf. **No leaf is made `Init` by `reset`**, including in the arena value. **Other outcome:** `reject`.

Safe reuse after `reset` requires that previous issuances **covering recycled leaves**, and the dependencies on which their validity rests, have effectively ceased preventing their reuse. Any active empty-footprint derivatives cover none of those leaves. A historically issued region does not remain permanently unavailable solely for that reason.

# XV. Transitive Dependencies, Returns, and Value Behavior

Dependent values may survive transfers and calls only if the required anchors and rights remain valid. Second-class access does not imply an arbitrary persistent reference.

## 79. Non-Escaping Values and Returns

The second-class nature of access authorities does not prohibit constructing a value carrying a derived authority or returning a result dependent on a caller-owned resource. What is prohibited is artificially extending the validity of a local origin.

A typical scenario is:

```text
arena = create_arena()
buffer = create_buffer(arena)
use(buffer)
endUse(buffer)       // or equivalent release of its dependent rights
arena.reset()
```

The scenario is permitted when:

1. the call receives and exercises valid authorities over the arena;
2. issuance supplies a block disjoint from live issuances;
3. the result value is anchored to the rights actually required;
4. its transfer to the caller respects `SameShape`, holders, `AnchorOrder`, and `AnchorOrderHeld`;
5. `exitFrame` can reanchor surviving authorities without using a dead local root;
6. `reset` is rejected while the dependent result or a block authority remains active, then becomes permitted after those rights have effectively ended.

A “non-escaping” value is therefore not necessarily confined to the frame in which it was created. It may survive a function when it depends on a caller anchor, without extending dead local storage. This result does **not** imply strong protection of all parameter authorities throughout the entire invocation: the historical interpretation of reborrows and this property are deferred to Spec 3.

Properties of transfer between threads and shareability do not follow from this sequential model alone. They depend on external resources, contained authorities, anchors, confinement restrictions, and the concurrency model of Spec 2.

# XVI. External Contracts and Interfaces with Other Specifications

Declarative contracts create no rights. Their satisfaction is an obligation of the language, typing, implementation, or a safe abstraction, according to the nature of each contract.

## 80. Parametric Contracts of the Access Discipline

A contract `K` parameterizes rules of the access discipline without fabricating permissions. A safe abstraction using part of `K` must prove or fulfill the corresponding obligation; an unestablished precondition is not a language guarantee.

| Contract | External obligation |
|---|---|
| `DeclaredDisjoint` | `DDSound(K)`: no falsely declared disjoint region when leaves can overlap |
| `Pinned` | I5, prohibition of incompatible physical moves; `StaticPinnedBottom` for pinned statics |
| `SharedMutable` | Applicable shared-mutation discipline, with correct rights and synchronization |
| `ExternalDone` | External use of storage has ended when `unpin` is permitted |
| `Deallocable` | The place belongs to a unit that can actually be freed |
| `FreeCompat` | Opaque deallocation authority is compatible with the unit being freed |
| `Satisfiable` | The provider can satisfy the requested shape **in the current state** |

Structural conditions of `free`, dependencies, and the derived library `reset` carry the relevant invalidation obligations. Physical justification of `DDSound` must be established by a realization consistent with memory layouts and Section 82.

## 81. Boundaries Remaining to Be Specified

This specification **does not by itself determine**: concurrency and synchronization effects (Spec 2); control-flow analysis, `defer`, and by-value calling conventions (Spec 3); representation criteria and typed formation of accesses (Spec 4); representation of library metadata, address width, encodings, and alignment/ABI obligations (Spec 11); or final translation of `noalias` properties (Spec 13). Leaving a rule open does not authorize a safe interface to cause UB; the implementation must fulfill or reject the obligations before exposing the operation to safe code.

# XVII. Correspondence Between Access Discipline and Memory Machine

A transition of the access discipline must admit a realization compatible with the bytes and allocations of the memory machine. An abstract definition of a right does not suffice to justify its concrete representation.

## 82. Representation Relation and Concrete Obligations

1. **Places and bytes:** relate `P`, `footprint` leaves, their ownership, and their parts to the storage units, offsets, ranges, identities, and alignment constraints of the elementary memory machine; establish actual disjointness for `DeclaredDisjoint` declarations.
2. **Authorities and operations:** connect effective modes and `ExercisableAt` to concrete read, write, and pointer-validity conditions; show that safe access governed by Parts VI through XV satisfies the obligations of Part III, without conflating ownership and binary representation. A pointer to a region whose leaves all have zero physical size is represented like a pointer to the empty region: its address is the base of the allocation of the effective anchor of its authority, and that allocation is its provenance.
3. **Initialization:** relate `Uninit`, `Init`, and `Moved` to concrete values and representations; an authority `store` must correspond to writing an actual reference into **a single logical leaf** with an appropriate representation.
4. **Allocation and deallocation:** relate `alloc` / `free` to `AllocStep` / `DeallocStep`, justify `Satisfiable`, `Deallocable`, and `FreeCompat`, as well as the zero-physical-size case.
5. **Lifetimes:** relate `endUse`, `exitFrame`, `NoDangling`, dependencies, and death markers to the validity effects on actual storage.
6. **Pinning and static storage:** prove compatibility of permitted moves and pinned-address restrictions; specify the physical obligations of statics and external use. Hardware-specific MMIO semantics remain outside the sequential kernel.
7. **Arenas:** show that the library abstraction's derived operations and metadata, distinct from `S₃`, can be realized by operations O1–O16; relate issued regions and local/static/allocated storage to the elementary memory machine without reintroducing access after invalidation.
8. **`noalias`:** infer no pointer-lowering property from abstract invariants alone; memory justification is established here and the translation choices at Spec 13 level.

# XVIII. Examples of Semantic Behavior

The fragments below are **traces of abstract operations**, not language syntax. The judgments illustrate normative rules; they create no exception to the detailed preconditions.

## 83. Address Reuse and Old Provenance

An allocation `a` is created and an access retains its provenance; after deallocation, a new allocation `b` may occupy the same address. `a ≠ b` as abstract identities: reading through the old access is invalid even if the addresses are equal. A new valid access with provenance `b` may be used within its rights.

## 84. Partial Initialization and Reading

A valid write to a subrange initializes its corresponding bytes. Reading another subrange that remains uninitialized is not permitted. The correspondence for logical state `Init` must guarantee a representation valid for the expected type; the mere presence of bits does not authorize type confusion.

## 85. Splitting a Structure or SoA Columns

Starting from a `Modify` authority exercised over a structure, `split` may provide `Modify` authorities over disjoint leaf regions. Modification of each region is permitted as long as the other validity and holder conditions hold; a second independent derivation over the same leaf does not become legal merely by having a distinct name.

## 86. Arena, Active Views, and Reset

Two disjoint issued regions may be used simultaneously with valid derived rights. `reset` is rejected while an issuance or active dependency would make recycling unsafe; after a legal end of use for all the relevant blocks, the region may be reissued. Reissuance modifies neither the bytes nor the initialization state. A read remains subject to the ordinary conditions of the memory model, notably `Init`, access rights, and representation validity for the requested type. Spec 4 will determine the construction and typing obligations of reissued values.

## 87. Pinning an In-Place Value

A pinned in-place leaf cannot be physically moved by `transfer`. If only an allocation owned by a value is pinned, transfer of that value may remain valid when the other conditions hold, because the owned allocation is not physically moved.

## 88. Local Self-Blocking and Indirect Cycles

An authority stored by `transfer` in a place that would then become its new holder cannot cover any leaf of that place. Likewise, `issue` cannot issue into a leaf belonging to the issued region, **or into a destination that would no longer be exercisable in `Modify` in the resulting state** (O8.5). These restrictions do not promise general freedom from authority cycles: indirect blocking compatible with safety may remain.

## 89. Handles and Persistent References

In a generation-based pool library abstraction, a handle may contain a logical pool identity, an entry identifier, and a generation. This handle is not, by itself, an access right. Safe resolution temporarily supplies authority when the pool and entry are valid; a stale identity or generation leads to defined failure. These conditions belong to the safe abstraction's contract and do not modify the authority-discipline kernel.

## 90. Global and Called Frame

Global storage is anchored to the base frame, but a called function does not acquire ambient authority to modify it merely by being invoked. To access a global, it receives a derived authority under `enterFrame` conditions and may exercise only its effective modes.
