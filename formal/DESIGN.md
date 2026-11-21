# Formalization design

Decisions for the Lean formalization. They govern how to formalize, never what ERN means: semantics comes only from `specs/`. Agents follow them. A design question not settled here is proposed in the report, never decided silently.

## Goal

Check that the spec's rules deliver what ERN promises. A rule that cannot be formalized or proven as written is a result: report it with the failing goal, never work around it.

Three results stay distinct: the formal model of the rules, the theorems proven about that model, and later the correctness of the compiler against it. This formalization covers the first two.

## Architecture

The formalization uses two permanent, complementary models linked
by a refinement theorem.

This is an architectural decision about formalization, not a
normative decision about ERN semantics. Both models must faithfully
represent the validated specifications.

If a specification cannot be represented faithfully, the mismatch
must be reported. Any necessary change to the formalization
architecture requires an explicit revision of this document.

1. **Abstract model.** Memory is a set of places: variables and field paths (`p.right`). Gives the semantics of safe code. States what safe code may assume about memory.
2. **Concrete model.** Memory is byte-addressed allocations. Gives the semantics of safe and unsafe code. Parameterized by a layout interface, never by a fixed layout.
3. **Refinement theorem.** Links the two models. It is the formal statement of ERN's safety promise.

## Concrete memory

- Bytes are abstract: each byte carries its initialization state and, when it belongs to a pointer, its provenance. Address and provenance are distinct.
- The concrete model represents every distinction the spec's rules rely on, including storage shared by several places.

## Layout interface

- Size, alignment and position of each component of a type are abstract functions.
- Their guarantees (in bounds, non-overlapping where the spec requires it, aligned) are hypotheses carried as structure fields or typeclass assumptions, never Lean `axiom`s.
- The interface contains only guarantees that some spec rule needs. Each hypothesis cites the rule that requires it.
- Non-vacuity: whenever the interface changes, a layout satisfying it is exhibited and proven. An unsatisfiable interface would make every refinement result empty.
- Realizability for every admissible target and instance is an obligation of the charter's ABI and layout step. It stays recorded as open until that step discharges it.

## Main theorems

- **Observable behaviors** are defined explicitly: termination with its observable result, trap, undefined behavior, divergence. Refinement compares concrete behaviors projected onto abstract observations.
- **Abstract safety.** A program accepted by the static rules has no undefined behavior in the abstract model.
- **Refinement.** For every layout satisfying the interface: if each unsafe region satisfies its contract, every observable behavior of an accepted program in the concrete model projects to a behavior of the abstract model. Concrete safety follows from abstract safety.
- **Unsafe contracts.** A contract is an entry condition and an exit condition relating the two models. From any state satisfying the entry condition, no execution of the region reaches undefined behavior, and every non-trap exit satisfies the exit condition. A trap is terminal: it runs no cleanup and is compared as an observable behavior. The relation between the models implies the entry condition of any region reachable from safe code; a stronger entry condition must be established by the unsafe code that enters the region. Intermediate states may break the relation, since in sequential execution no other code observes them. Under concurrency, other contexts observe shared state during the region, and the form above is not enough. A concurrent contract has five parts:

  - Entry condition. As above, including the authorities the region needs.
  - Rely. The interference the region tolerates from other contexts. It never
    assumes that another context stops running.
  - Guarantee. At every intermediate state, the invariants and the relation
    between the models on which other contexts may rely remain valid for
    every part of the state they can observe. A temporary departure from the
    relation is permitted only for storage for which the region establishes
    exclusive authority and physical non-observability by other contexts
    throughout the departure, under its rely and event conditions. The
    relation and the invariants are restored before that storage is
    published, transferred, made externally accessible, or ceases to be
    exclusively controlled. No temporary departure invalidates a global
    invariant on which another context relies.
  - Event condition. The accesses, memory orders, synchronizations and
    storage-validity events of the region satisfy the event rules of the
    concurrency spec.
  - Exit condition. As above, on every exit the contract announces, defined
    failures included.

  Non-observability is a property of events, not of one state. The departure
  and the restoration are represented by events, or by explicitly mapped cuts
  of the event graph, before their order is stated: every access of another
  context to that storage is ordered by `hb` before the departure or after the
  restoration. An abstract state transition or an exclusive authority alone is
  not evidence of that order.

  A safe abstraction establishes these parts itself, for every interference its
  environment may produce. It never passes them on to its safe callers. The
  contract is a proof method: it adds no rule to any spec. What a trap in one
  context means for the other contexts belongs to the control flow spec; no
  theorem of milestone 4 depends on it.
- **Scope.** Every theorem states the language fragment it covers. A theorem on a fragment supports no claim about the whole language; sequential safety implies nothing about concurrent safety.

## Construction order

1. Control flow infrastructure: abstract syntax and operational semantics of control constructs. No safety theorem yet: the control flow spec's preservation rule depends on the memory and concurrency models.
2. Memory model, safe part, on the abstract model. Abstract safety for the sequential fragment.
3. Concrete model, layout interface and refinement for the sequential fragment. The memory model counts as verified for that fragment only once refinement is proven.
4. Concurrency model: extends both models and the refinement.
5. IR dialect, once its dependencies are formalized.

The semantic style and target theorems of milestone 4 are set out below. The
style and target theorems of milestone 5 must be decided through an explicit
revision of this document before milestone 5 begins.

## Milestone 4: concurrency model

Source: the concurrency model specification in `specs/`. Clause numbers and
obligation labels below are its own.

### Semantic style

- **Three objects stay distinct**: the abstract step relation, the execution
  events with their relations, and the correspondence between the two. None is
  obtained from another by convention.
- **Place in the architecture.** The step relation extends the abstract model.
  Its realization extends the concrete model. The event graph is a third,
  declarative object, added to the architecture by this section.
- **Abstract steps.** A labelled step relation over the concurrent state and
  the library states, interleaved nondeterministically. Library states stay
  outside the concurrent kernel state (C2, C12). Outcomes are those of the
  memory model (§58), unchanged. A legal request that is not enabled has no
  outcome (C8, C16): enabledness is a separate predicate, never an added
  outcome.
- **Events.** An axiomatic graph: events with `po`, `rf`, `mo` and `sw`, and
  `hb` derived from them (C26–C33). The consistency predicate is the
  conjunction defined by C34. Definitions hold for any number of contexts and
  of atomic units.
- **Correspondence.** A successful step corresponds to one or more events. An
  event may correspond to no successful step: an attempt that is rejected or
  not enabled may still perform physical accesses (C8, C16, C26, C39). The
  absence of an `ok` step never implies the absence of events.
- **One event per step** is a proof fragment, never the semantics of C26–C29.
  Every theorem that relies on it carries it as a hypothesis.

### Scope of proofs

- Scope (Main theorems) applies in full. A property proven for one atomic
  unit, for one event per step or for runs from the initial state keeps that
  restriction in its statement.
- Witness traces and witness graphs establish non-vacuity. They never replace
  a general proof.
- Results of external bounded tools are evidence kept in reports, outside the
  formalization.
- The memory model formalization is extended, not modified. It does not
  represent the discipline condition of the shared write (memory model
  §68.3). A theorem relative to that formalization alone does not discharge
  directional conservativity against §68.3. The missing correspondence
  between the two shared-discipline contracts is recorded as an outstanding
  obligation; a statement that needs it carries it as an explicit premise.
  No change to the frozen specification or to its formalization is
  authorized by this milestone.

### Target theorems

Each is proven on its declared fragment.

1. Sequential conservativity (C24).
2. Preservation of concurrent well-formedness and of the synchronization
   invariants by every transition, by-value `spawn` included (C5, C20–C23).
3. Frame ancestry under reparenting (C3, C6, C7).
4. Soundness of the synchronization contract and exclusivity of grants
   (C14, C21, C25).
5. Synchronized administration and the uniqueness guard on administration
   identities (C13, C19).
6. Coverage of the rights read under encapsulation (C22).
7. Outcomes: rejection and enabledness of `join` and `acquire`; rejection of
   `unlock` and of recovery (C8, C16–C18).
8. Atomic operations as step cases, with preservation extended to them
   (C37, C39).
9. Refinement at the grain of abstract steps: the memory model refinement
   extended to the concurrent machine (C50). The correspondence of physical
   events is not part of it.
10. General lemmas of the event model; the pure-authority-marker `po`/`hb`
    erasure property under its explicit premises (C29); non-vacuity of each
    conjunct of the consistency predicate (C30–C34). On the explicitly
    stated common fence-free atomic-event fragment, the inclusion of
    RC11-consistent executions in ERN-admissible executions is proven or
    refuted (C34, `OB-C23`, `OB-C26`). The statement gives the event mapping
    and the alignment of `rf`, `mo`, initial writes, RMW and failed-CAS
    events, and memory orders. No inclusion or equivalence is assumed as an
    axiom.
11. Legality of shared-discipline operations and of memory orders;
    directional conservativity of shared writes (C35–C42).
12. Handoff: L1 and L2 as stated by C45, the position of the loss marker in
    the abstract trace, and exclusion of a race by an ordered handoff
    (C43–C46).
13. Reference protocols: ordering by `spawn`, completion and `join`; lock
    order, with its conditions on intervening acquisitions, on recovery and
    on the stability of the controller leaf stated in the theorem;
    correspondence with the reference controller graph (C47–C49).
14. Lifetime ordering and the conditional composition theorem, proven by
    cases on the conflicting pair: ordinary storage; two atomic accesses;
    atomic storage with an ordinary access; confined storage; synchronized
    storage with an exclusive writer; synchronized storage under shared
    observation, where the order is a premise of the safe trace; distinct
    storage identities reusing bytes (C51, C52).

### Exported obligations

The exported obligations are not discharged by this milestone. Each obligation
remains recorded as open in the formalization, with its clause, label, and
applicable parts, as follows:

- **Stated:** The applicable part is expressed by an identifiable Lean
  predicate or hypothesis. The theorems relying on it carry it as a
  hypothesis, and the corresponding documentation cites the obligation's
  clause and label.
- **Documented:** The relevant object is represented in the model, but no Lean
  predicate or hypothesis states the applicable part as a contract.
- **Out of scope:** The object required to state the applicable part is not
  represented in this milestone.

An obligation may have multiple parts with different statuses. Each part must
be identified by the requirement it covers. A proof of an explicitly
identified abstract property may be recorded as a result, but it does not
discharge the exported obligation or establish its unrepresented
implementation requirements.

All exported obligations remain open regardless of the status or proofs of
their individual parts. Documentation alone is not a formal contract.

- physical realization of the reference mutex: controller accesses, failed
  attempts, recovery publication (`OB-C05`);
- typing of transferable and shareable values, enforcement of the safe
  interfaces, by-value passing conventions, external contexts (`OB-C07` to
  `OB-C10`);
- concrete realization under the memory model's representation obligations,
  beyond the grain of abstract steps (`OB-C12`);
- physical classification of pure-authority markers, projection of
  storage-validity events, and complete physical-access/event
  correspondence; the abstract erasure property itself is an internal proof
  target (C29, `OB-C19`, `OB-C20`);
- target compilation, the no-thin-air requirement included (`OB-C22`,
  `OB-C27`);
- soundness of safe programs (`OB-C24`);
- enforcement by the safe interfaces of the authority premises inventoried
  by theorem 6, and physical coverage of recovery (`OB-C28`);
- layout and ABI.

### Obligation labels

| Theorem | Labels |
|---|---|
| 2 | `OB-C14` |
| 3 | `OB-C13` |
| 4 | `OB-C15` |
| 5 | `OB-C16` |
| 6 | `OB-C28`, abstract part |
| 8 | `OB-C03` |
| 9 | `OB-C12`, abstract part |
| 10 | `OB-C01`, `OB-C02`, `OB-C19` abstract part, `OB-C23`, `OB-C26` |
| 11 | `OB-C03`, `OB-C21` |
| 12 | `OB-C17`, `OB-C18`, `OB-C25` |
| 13 | `OB-C04`, `OB-C05` abstract part, `OB-C11` |
| 14 | `OB-C06` |
| exported | `OB-C05`, `OB-C07` to `OB-C10`, `OB-C12`, `OB-C19`, `OB-C20`, `OB-C22`, `OB-C24`, `OB-C27`, `OB-C28` |

Theorems 1 and 7 carry no label: their statements are clauses of the spec.
Theorem 11 discharges `OB-C21` only relative to the present memory model
formalization; its bridge to §68.3 stays outstanding (Scope of proofs).

### Completion

Milestone 4 is complete when:

- every target theorem is proven on its declared fragment;
- Every exported obligation remains recorded as open in the formalization,
  with its clause, label, and the status of each applicable part. A part is
  classified as stated only when an identifiable Lean predicate or hypothesis
  expresses its contract, the theorems relying on that contract carry it as a
  hypothesis, and its documentation cites the clause and label. Documented and
  out-of-scope parts remain explicitly identified as not formally stated.
  Proofs of abstract properties do not discharge their exported implementation
  obligations.
- every limit is listed in the report;
- the adversarial corpus is replayed against the reconstructed modules.

A rule that cannot be formalized or proven as written stops the work and is
reported (Goal). It is never worked around.

## Representation

- **Abstract syntax** is built incrementally: only the constructs required by the rules being formalized. No concrete syntax.
- **Semantics** is a step function where the spec is deterministic, a step relation where it is not. Interpreters for tests iterate steps with fuel. Running out of fuel is not an outcome, neither termination nor trap. Each interpreter is proven to agree with the unbounded semantics on every result it returns.
- **No Mathlib** unless a milestone requires it. Adding it is a design decision recorded here.
