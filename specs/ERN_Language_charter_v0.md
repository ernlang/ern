# ERN — Language Charter v0

**Status: Frozen — October 27, 2026**

## 1. Identity and Vision

ERN `[e.ʁɛn]` is a general-purpose, low-level, systems-oriented programming language designed to combine high performance, extremely fast compilation, modern ergonomics, and precise control over resources.

ERN targets systems software, game engines, simulations, development tools, native applications, servers, software infrastructure, and compute-intensive workloads.

## 2. Fundamental Objectives

ERN pursues five major objectives:

1. **Runtime Performance** — produce highly performant native code with controllable costs.
2. **Compilation Speed** — minimize development latency and support scalability.
3. **Ergonomics** — provide a coherent, readable, expressive, and practical language for systems programming.
4. **Safety and Predictability** — enable precise reasoning about operations, resources, and program behavior.
5. **Overall Simplicity** — limit unnecessary mechanisms, exceptions, and complexity imposed on users and implementations.

No single objective, by itself, justifies a mechanism whose overall cost would be disproportionate.

## 3. Cross-Cutting Principles

### 3.1 Semantics Before Syntax

Language mechanisms are defined semantically before their concrete syntax is finalized.

Provisional syntax is permitted for examples and experimentation.

### 3.2 Controlled Abstractions

Abstractions must make it possible to reason about their runtime costs and provide the necessary optimization opportunities.

### 3.3 Explicit Control

Significant effects and costs must be understandable and controllable.

This does not imply that every operation must necessarily be explicit in the syntax.

### 3.4 Language and Library

A feature should primarily be implemented in a library when it can be expressed there correctly and efficiently.

Its inclusion in the language must be justified by semantic guarantees, compiler requirements, or measurable benefits.

### 3.5 Mechanism Coherence

Language features must form a coherent system without unjustified proliferation of exceptions or competing mechanisms.

### 3.6 Validation Through Concrete Cases

Architectural proposals must be tested against representative examples, edge cases, and counterexamples.

A feature must not be adopted solely because it is novel or exists in another language.

## 4. Memory Model and Safety

ERN aims to provide a memory model that enables precise low-level control, efficient resource management, and clearly defined safety guarantees.

### 4.1 Safety Contract

Safe ERN code must guarantee:

1. **Spatial memory safety**.
2. **Temporal memory safety**.
3. **Absence of reads of uninitialized values**.
4. **Absence of type confusion**.
5. **Absence of data races**.

These guarantees also depend on the contracts of any unsafe abstractions being respected.

The safety contract does not automatically guarantee the absence of:

- Memory or resource leaks.
- Deadlocks.
- Stack overflows.

These exclusions do not prevent the language or its libraries from providing mechanisms for prevention, detection, or diagnosis.

### 4.2 Memory Model

Rules governing values, storage locations, references, memory accesses, resources, invalidation, and unsafe operations will be established by the memory model specification.

The safety contract must distinguish guarantees applicable to safe code from the obligations associated with unsafe operations.

The charter does not presuppose any particular model of ownership, borrowing, regions, or destruction.

## 5. Concurrency and Asynchrony

ERN aims to support efficient concurrent and parallel programming compatible with its memory safety guarantees.

The design must accommodate different execution and scheduling models without unnecessarily imposing a single runtime.

Guarantees concerning sharing, synchronization, atomicity, suspension, and cancellation will be defined in the relevant specifications.

## 6. Control Flow and Errors

ERN must provide coherent semantics for expressions, functions, branches, loops, scopes, and control transfers.

Error handling, propagation, abnormal termination, and cleanup mechanisms must be compatible with the memory model.

Their precise forms and rules belong to the specifications.

## 7. Types and Data Representation

ERN aims to provide an expressive type system suitable for systems programming.

The language must enable appropriate control over memory representations and efficient data-oriented programming.

The specific mechanisms for typing, layouts, views, and data abstractions will be determined by the corresponding specifications.

## 8. Arithmetic and Vector Computation

ERN aims to provide performant numerical and vector computation capabilities.

The semantics of arithmetic operations, conversions, floating-point operations, and SIMD must be sufficiently precise to enable optimizations while preserving the language's guarantees.

## 9. Generics and Metaprogramming

ERN must support the construction of reusable abstractions and the execution of computations at compile time.

Generics, compile-time evaluation (`comptime`), reflection, and generation must be designed consistently with the type system, memory model, and fast-compilation objectives.

## 10. Modules and Interoperability

ERN must support modularity and efficient interoperability with native environments.

Interoperability with C is a priority objective.

Guarantees concerning external interfaces, calling conventions, binary representation, and linking will be established in the appropriate specifications.

## 11. Compiler and Tooling

ERN aims to eventually provide a self-hosted compiler.

Its objectives include a performant compilation architecture, precise diagnostics, modern tooling, and the ability to leverage different optimization and code generation strategies.

Decisions concerning intermediate representations, backends, bootstrapping, incremental compilation, and hot reload will be based on technical evaluation and experimentation.

The internal compiler architecture must not implicitly alter the normative semantics of the language.

## 12. Validation Criteria

Major decisions must be evaluated according to their impact on:

- Runtime performance.
- Compilation speed.
- Ergonomics.
- Safety and predictability guarantees.
- Overall complexity of the language and its implementation.

Evaluations may rely on stress-test cases, prototypes, benchmarks, and formal models.

Adopted decisions must comply with the principles of this charter.

## 13. Specifications and Formalization

### 13.1 Document Responsibilities

The charter establishes the objectives, principles, and design order.

Specifications establish language mechanisms, their behaviors, and their normative guarantees.

A specification may cover multiple closely related mechanisms.

No subdivision into additional documents is required unless necessary.

### 13.2 Specification Content

Each specification defines, as appropriate to its scope:

- The concepts involved.
- Semantic rules.
- Permitted and forbidden behaviors.
- Invariants.
- Examples and counterexamples.
- Stress-test cases and their expected verdicts.
- Interactions with other specifications.

### 13.3 Formalization

Lean 4 is used progressively as a tool for designing, evaluating, and verifying the semantic properties of the language.

Formal models accompany the design of mechanisms and enable examination of their guarantees before stabilization.

Validated specifications constitute the normative reference; formal models must remain consistent with their rules.

### 13.4 Syntax

Abstract syntax and provisional notations may precede the final grammar.

The normative grammar is established after the corresponding semantic mechanisms have been stabilized.

### 13.5 Sources of Truth

Design documents may contain hypotheses, alternatives, and historical analyses.

These documents are not authoritative for implementation.

The validated charter and validated normative specifications constitute the official references for the language.

Approved technical implementation documents must comply with these references.

## 14. Evolution and Stability

Charter v0 is frozen upon validation and takes precedence over specifications in the normative hierarchy.

Any modification to its principles or commitments requires an explicit, justified revision of the charter.

Specifications may evolve according to their modification procedures without contradicting the charter.

Language compatibility and versioning policies will be refined during its development.

## 15. Long-Term Vision

ERN aims to provide a durable foundation for an ecosystem of libraries, runtimes, tools, and native applications.

Its architecture must accommodate the evolution of language capabilities and hardware platforms without sacrificing its coherence, efficiency, or fundamental principles.

## 16. Work Order

Specifications will be designed in the following order.

Each entry corresponds to one specification document, whose normative content is defined during its design.

| Order | Document |
|---|---|
| 1 | Memory Model |
| 2 | Concurrency Model |
| 3 | Control Flow |
| 4 | Type System |
| 5 | Generics and Compile-Time Evaluation |
| 6 | Effects and Capabilities |
| 7 | Arithmetic and SIMD |
| 8 | Data Representation and Layouts |
| 9 | Modules and Program Structure |
| 10 | Built-in Primitives and Language–Library Contract |
| 11 | Interoperability and ABI |
| 12 | Syntax and Grammar |
| 13 | Compiler Architecture |

The order establishes the design priority of the documents. Necessary interactions with later domains may be considered in earlier specifications.

The first twelve documents concern language contracts. The thirteenth primarily concerns its implementation architecture and remains subordinate to the normative language semantics.

---

**ERN — Language Charter v0 — Frozen.**