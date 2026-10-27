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
- **Unsafe contracts.** A contract is an entry condition and an exit condition relating the two models. From any state satisfying the entry condition, no execution of the region reaches undefined behavior, and every non-trap exit satisfies the exit condition. A trap is terminal: it runs no cleanup and is compared as an observable behavior. The relation between the models implies the entry condition of any region reachable from safe code; a stronger entry condition must be established by the unsafe code that enters the region. Intermediate states may break the relation, since in sequential execution no other code observes them. Under concurrency, shared state is observable during the region; the contract form for that case is decided before milestone 4.
- **Scope.** Every theorem states the language fragment it covers. A theorem on a fragment supports no claim about the whole language; sequential safety implies nothing about concurrent safety.

## Construction order

1. Control flow infrastructure: abstract syntax and operational semantics of control constructs. No safety theorem yet: the control flow spec's preservation rule depends on the memory and concurrency models.
2. Memory model, safe part, on the abstract model. Abstract safety for the sequential fragment.
3. Concrete model, layout interface and refinement for the sequential fragment. The memory model counts as verified for that fragment only once refinement is proven.
4. Concurrency model: extends both models and the refinement.
5. IR dialect, once its dependencies are formalized.

The semantic style of milestones 4 and 5 and their target theorems are decided here before they start.

## Representation

- **Abstract syntax** is built incrementally: only the constructs required by the rules being formalized. No concrete syntax.
- **Semantics** is a step function where the spec is deterministic, a step relation where it is not. Interpreters for tests iterate steps with fuel. Running out of fuel is not an outcome, neither termination nor trap. Each interpreter is proven to agree with the unbounded semantics on every result it returns.
- **No Mathlib** unless a milestone requires it. Adding it is a design decision recorded here.
