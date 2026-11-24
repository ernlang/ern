/-!
# Exported obligations of the concurrency model (`formal/DESIGN.md`, "Exported obligations")

One entry per label of the row "exported" of the table "Obligation labels" of `formal/DESIGN.md`,
and one for layout and ABI. The labels and their clauses are those of the table of external
contracts of `specs/ERN_Concurrency_Model_Specification_v0.md` ("External Contracts and Proof
Boundaries"). Each entry identifies the parts of the obligation by the requirement they cover and
gives the status of each part, with the criteria of `formal/DESIGN.md`:

* **stated**: a Lean predicate or hypothesis expresses the part, the theorems that rely on it carry
  it as a hypothesis, and its documentation cites the clause and the label;
* **documented**: the object is represented in the model, no predicate or hypothesis states the
  part as a contract;
* **out of scope**: the object needed to state the part is not represented.

"Results" are theorems that prove an identified abstract property. They do not discharge the
obligation. **Every exported obligation remains open**, whatever the status of its parts. This
module contains no declaration.

## `OB-C05` (C25, C41, C48, C49): physical realization of the reference mutex

* Event-level realization of the controller steps: the event of `newMutex` and of each successful
  `acquire`, `unlock` and `resetLock`, with its access, order, values and `sync` role, and their
  linearization by `mo` on the controller (C48, C49; C13, C27, C31). **Stated**: `Realizes`, with
  `ctlAcc`, `ctlSync` and the orders `CtlOrders` (legality `CtlOrders.Legal`, C40). Carried by
  `acquire_rf_source`, `acquire_rf_last`, `acquire_readOn`, `acquire_reads_v0`, `acquire_sw`,
  `acquire_sw_ref`, `rf_no_between`, `sw_ctl_iff`, `lock_order`, `recovery_sw`, `lock_edge`,
  `lock_edge_entry`, `mutex_lockEdge`; `CtlOrders.Legal` by `controller_graph`.
* Recovery publication: the controller write of `resetLock` (C48, fifth paragraph; C18; C49).
  **Stated**: the `resetLock` case of `ctlAcc` and `ctlSync` within `Realizes`. Carried by
  `recovery_sw`, `lock_order`, `lock_edge_entry`.
* Failed attempts on the controller (C41; C16 item 2; C48). **Documented**: a request that is not
  enabled is represented (`AcquireNotEnabled`, C16), and an event of the graph may be the event of
  no step; `Realizes` says that failed attempts are not steps and bounds only the modifications of
  the controller (`Realizes.only`); no predicate states their realization.
* Physical realization in the memory machine: the controller accesses as byte operations, their
  indivisibility and linearization (C25, C41). **Out of scope**: the raw operations of `newMutex`,
  `acquire`, `unlock` and `resetLock` are empty (`rawOps`); the memory machine represents no
  controller access.

Results (abstract part, C48, C49): `controller_graph` (13d.1: realization R holds on every
execution of its fragment); `acquire_sw`, `rf_no_between` (13d); `lock_order` (13e);
`recovery_sw` (13f); `lock_edge`, `lock_edge_entry` (14e). The obligation remains open.

## `OB-C07` (C9; Spec 1 §29): transferability and shareability typing

* Static eligibility of values for cross-context transfer and sharing, determined from declared
  types and signatures (C9). **Out of scope**: no type and no signature is represented.
* Interface contract of callables: bodies checked against their signatures; captures of anonymous
  callables. **Out of scope**: no callable is represented.

Results: none. The obligation remains open.

## `OB-C08` (C22): enforcement of the safe interface of the reference mutex

* The property of the traces of the safe reference-mutex abstraction: the six requirements of C22
  on every step (C51 item 1). **Stated**: `EncapStep` and `EncapsulatedTrace` (named-state form
  `EncapRun`), for every datum of the provider metadata (`ProviderMeta`). A property of
  executions, not a proof of its enforcement. Carried by `synchronization_encapsulated`,
  `encapsulated_inv`, `run_inv`, `cap_l2`, `cap_covers`, `cap_of_usesModify`, `cap_of_access`,
  `cap_of_usesModifyAt`, `allows_usedMode`, `local_loss` and its cases `local_loss_*`,
  `loss_marker_of`, `loss_marker_modify`, `loss_marker_confined`, `access_pair_marker`,
  `handoff_no_race`, `spawn_hb`, `join_hb`, `grant_invariant`, `grant_const`, `grant_keep`,
  `ctl_ge`, `acquire_reads_v0`, `lock_order`, `recovery_sw`, `controller_graph`,
  `encapRun_of_trace`, `encapRun_reach`, `trace_of_run`, and, through `SafeConcurrentTrace`, the
  theorems of `OB-C24`.
* Enforcement: the safe interfaces and the library contract expose only steps of such traces (C22,
  last paragraphs). **Out of scope**: no safe interface, library code or program is represented.

Results: `synchronization_encapsulated` (theorem 4, under the stated part). The obligation remains
open.

## `OB-C09` (C5): by-value passing conventions

* By-value passing conventions (C5). **Out of scope**: no calling convention is represented.
* Cancellation, abnormal termination, cleanup. **Out of scope**: not represented; `terminate` is
  the normal end of a context (C7).
* Refinement of the protocol of the language to the reference transition (C5, contract required of
  the protocol, items 1–5). **Out of scope**: the reference transition is represented
  (`SpawnValStep`), the protocol it refines is not.

Results: none for this obligation. The obligation remains open.

## `OB-C10` (C10): external contexts

* Initial parent, frames, authorities and resource contracts of a context entered from an external
  environment, through an interoperability mechanism (C10). **Out of scope**: the contexts of the
  model are the initial context and the contexts created by `spawn` or by-value `spawn` (C3, C4,
  C5); no external context is represented.

Results: none. The obligation remains open.

## `OB-C12` (C25, C50; Spec 1 §82): concrete realization

* Representation obligations of each step at the grain of abstract steps (Spec 1 §82, §20.3): the
  parameters (`Refinement.ParamsOK`: placement, geometry, tokens), the layout of new places
  (`Refinement.NewLayout`), the read and write obligations of the raw operations (`ObR`, `ObW`, of
  types `Machine.ReadOblSpec` and `Machine.WriteOblSpec`, imposed by `Refinement.OblAlong`), the
  obligations of a step (`StepOblC`) and the translated runs that carry them (`TransRun`).
  **Stated**. Carried by `refinement_step` (9a), `refinement_run` (9b), `step_no_ub`, `run_no_ub`
  (9c), `kernel_realized`, `viewStep_realized`, `TransRun.kInvCA`, `transRun_simRun`, the
  theorems `reached_*` (9f), and, for `Refinement.NewLayout` and `Refinement.OblAlong` directly,
  `alloc_realizedC`, `enter_realized`, `safe_read`, `safe_read_spawnVal`, `store_realized`,
  `transfer_realized`, `vals_realized`, `vals_safe`, `rmw_reads_realized`. The declarations of
  `Refinement` and `Machine` belong to the memory model: this entry carries their citation.
* Realization of conflicting access events beyond the grain of steps (C50, C51, C52): the leaf,
  kind and atomicity of each conflicting access event (Q2), the storage identity of each access
  event and the initial writes (reading 9), with the condition of fragment F on initial writes
  (reading 14, field `init_origin`), the order of distinct storage identities that reuse bytes
  (Q3). **Stated**: `CorrQ2`, `AccessData`, `CorrQ3`. Carried by `no_race` (14d); `AccessData` is
  data of `SafeConcurrentTrace` and of the theorems of 14a–14c. The physical provenance of the
  initial contents of a storage is not stated: an initial write of the graph is not proved to be
  those contents.
* Indivisibility of atomic units and interleaving of raw operations below the grain of abstract
  steps (C38, C39, C50). **Out of scope**: contexts interleave at the grain of abstract steps; the
  raw operations of one step run without interference (`refinement_run`).

Results (abstract part, C25, C50): theorem 9, `refinement_step`, `refinement_run`, `step_no_ub`,
`run_no_ub`, and 9d–9f. The obligation remains open.

## `OB-C19` (C29): physical classification of pure authority markers

* Classification of pure authority markers: the erased events are pure authority markers, and no
  erased marker is an endpoint of an `rf` or `mo` edge (C29, C34). **Stated**: the hypothesis
  `X ⊆ Pure` (`hX`) of `Events.Graph.erase_hb_iff`, `Events.Graph.erase_sw_iff` and
  `Events.Graph.erase_race_iff`; `Events.Graph.RfAvoidsPure` and `Events.Graph.MoAvoidsPure`,
  carried by `Events.Graph.erasePure_consistent_iff` and the conjunct statements
  `Events.Graph.erasePure_rfWF_iff`, `Events.Graph.erasePure_moTotal_iff`,
  `Events.Graph.erasePure_coherence_iff`, `Events.Graph.erasePure_rmwAtomic_iff`,
  `Events.Graph.erasePure_noThinAir_iff`, `Events.Graph.erasePure_scConsistent_iff`.
* Projection of storage-validity events by the realization (C27, C29). **Documented**: validity
  events are represented in the graph (`BeginOf`, `EndOf`, `LifetimeOrdered`) and allocation and
  deallocation in the memory machine; no predicate relates them (`SafeTrace`, complement of
  fragment F).

Results (abstract part, C29): `Events.Graph.erase_hb_iff` (10b), `Events.Graph.eraseOne_hb_iff`,
`Events.Graph.erasePure_hb_iff`. The obligation remains open.

## `OB-C20` (C27–C29, C50): correspondence of all physical accesses

* Provenance of access events: every access event is the event of a step or an initial write
  (Q1). **Stated**: `CorrQ1`. Carried by `no_race`. This part is not the coverage of C29, of
  which it is the converse: it says where an access event comes from, not that an access has an
  event.
* Correspondence of the events of steps and of the lifecycle markers, K1–K4, with the provenance
  of lifecycle roles in both directions (C26–C28, C32, C47). **Stated**: `Corresponds`, and its
  lifecycle part `LifecycleOK`, a field of `SafeConcurrentTrace` (C51 item 2(f)). Carried by
  `Corresponds.po_or_eq`, `handoff_compose`, `handoff_no_race`, `spawn_hb`, `join_hb`,
  `lock_order`, `mid_of_same_context`, `hb_of_marker`, `pair_confined`, `pair_exclusive`,
  `pair_ordered`, `pair_covered`, `no_race`, `lock_edge`; concluded by `controller_graph`.
  Outside this part: the order of the events within a step (C28; one event per step in fragment
  F), the validity events and the step that emits them, and whether a step with an access has an
  event (the next part).
* Presence of an event for a step with a classified access (C26). **Stated**: `CorrQ4`, a
  correspondence premise, not a condition of the safe trace (C51). Carried by `pair_covered`
  (14c.6) and `atomic_covered`; it is not a premise of `no_race`. Outside this part: it is not the
  coverage of C29 (the part "Coverage of physical accesses" below): it does not say that the event
  carries an access, nor its byte footprint, and says nothing of the accesses of compound steps or
  of failed attempts.
* Authority and footprint at the grain of leaves: the leaf, kind and atomicity of each conflicting
  access event are those of an access of its step (Q2). **Stated**: `CorrQ2`. Carried by
  `no_race`.
* Kind and memory order of the atomic event of a step (C37, C39, C40; C27): the atomic event of a
  step carries the kind and the memory order of an atomic access of that step. **Stated**:
  `StepOrders`, a field of `SafeConcurrentTrace` (C51 item 2(b)). Carried by `no_race`, through
  `SafeConcurrentTrace`. Outside this part: it relates no leaf to a unit (the next part) and no
  byte range, and says nothing of an event that is the event of no step, of the accesses of
  compound steps or of failed attempts (the parts below).
* Unit of the events of steps (C38, C30, C31, C32 item 1): two events of steps designate one unit
  exactly when their steps access one `Atomic` leaf of nonzero size, and that unit has a nonempty
  byte range. **Stated**: `UnitLeaf`, a field of `SafeConcurrentTrace` (C51 item 2(b)). Carried by
  `atomic_covered`, and by `no_race` through `SafeConcurrentTrace`. Outside this part: the
  placement of the byte range of a unit, the byte ranges of the accesses that designate no unit,
  and the events that are the event of no step.
* Initial writes, a condition of fragment F (C31; readings 9 and 14): an initial write with an
  event of a step `hb`-before it is not atomic. **Stated**: the field `init_origin` of
  `AccessData`, data of `SafeConcurrentTrace` and of the theorems of 14a–14d. Outside this part:
  it does not prove that an initial write is the physical initial contents of its storage; that
  physical provenance of the initial contents of a storage remains open (`OB-C12`). Atomic
  accesses performed during an execution by a phase that is not a step are outside fragment F.
* Coverage of physical accesses (C29). **Documented**: no predicate states it. What the model gives:
  for an access to an `Atomic` leaf of nonzero size, an event that designates a unit of nonempty
  byte range (`atomic_covered`, under Q4 and `UnitLeaf`); for the other leaves, the physical size is
  not represented.
* Byte footprints of physical accesses (C50). **Documented**: the memory machine represents the
  bytes of raw operations and the graph the units of events; no predicate relates them.
* Validity of physical accesses (C27, C50). **Documented**: as the projection of validity events
  under `OB-C19`.
* Ordering of physical accesses (C50). **Documented**: no predicate relates the order of the raw
  operations of a translated run to `po`, `rf` and `mo` of the graph. No predicate relates `rf` to
  the order of the abstract trace either: an `rf` edge may go from the event of a later step to the
  event of an earlier one (C26). The model imposes no memory order from the interleaving.
* Compound steps: the physical accesses of `transfer`, `store`, `issue`, `alloc`, `free`,
  `endUse`, `exitFrame`, `terminate` and of the phases of a by-value `spawn` (C27; C5).
  **Documented**: their raw operations are represented (`rawOps`); `classify` gives them no access
  and fragment F no event; no predicate states their correspondence.
* Failed attempts (C8, C16, C26, C39). **Documented**: requests that are rejected or not enabled
  are represented, and an event may be the event of no step; Q1 excludes from fragment F every
  access event that is neither the event of a step nor an initial write; no predicate states the
  correspondence of their physical accesses.
* The datum of the provider metadata of `alloc` (`ProviderMeta`, `ActualFootprint`) covers the
  actual physical accesses of the provider (C22.4, C50). **Out of scope**: the memory machine
  represents no write of provider metadata; the raw operations of `alloc` allocate the new root
  only (`Refinement.opsOf`).

Results: under Q4, `pair_covered` (14c.6: the two steps of a pair in conflict have events ordered
by `hb`) and `atomic_covered` (an access to an `Atomic` leaf of nonzero size has an event that
designates a unit of nonempty byte range); they state the existence of events, not their fidelity
to the physical accesses. Otherwise none beyond those of `OB-C12`. The obligation remains open.

## `OB-C22` (C34, C50): compilation of `NoThinAir_RC11` and of the finite causal past

* Target feasibility and correct compilation of `NoThinAir_RC11` (C34). **Out of scope**: no
  target and no compiler is represented; `NoThinAir` is a conjunct of `EventConsistent`, a
  condition on graphs.
* Admissibility of the finite causal past for unbounded graphs under compilation, optimizations
  included (C34, C50). **Out of scope**: likewise; `FiniteCausalPast` is a condition on graphs.

Results: none for this obligation. The obligation remains open.

## `OB-C24` (C51, C52): safe-code trace soundness

* The property of the executions against which safe code is sound (C51 item 2). **Stated**:
  `SafeConcurrentTrace`. A property of executions, not a proof that safe code produces only such
  executions. Carried by `SafeConcurrentTrace.encapsulated` (14b), `pair_confined`,
  `pair_exclusive`, `pair_synchronized`, `pair_exhaustive`, `pair_ordered`, `pair_covered` (14c)
  and `no_race` (14d).
* Programs accepted as safe and safe libraries produce only such traces (C51, C52). **Out of
  scope**: no program, type system or library is represented.

Results: `no_race` (14d, `OB-C06`), conditional on the stated parts of `OB-C12`, `OB-C20` and
`OB-C24`. The obligation remains open.

## `OB-C27` (C34, C40, C50): target compilation of atomic operations and memory orders

* Target-specific compilation of atomic operations and memory orders, and its performance
  consequences. **Out of scope**: no target is represented.

Results: none. The obligation remains open.

## `OB-C28` (C17, C22, C23): enforcement of the authority premises

* Enforcement by the safe interfaces of the authority premises inventoried by theorem 6 (C22.6,
  C23, C51 item 1). **Out of scope**: no safe interface is represented. The trace property that requires them
  (`RightsReadFree` within `EncapStep`) is the stated part of `OB-C08`.
* Physical coverage of recovery (C18, C48). **Out of scope**: the memory machine represents no
  access of `resetLock` (`rawOps`); its event-level publication is the stated part of `OB-C05`.

Results (abstract part, C22.6, C39): `rights_inventory`, `atomic_inventory` (theorem 6). The
obligation remains open.

## Layout and ABI (`formal/DESIGN.md`, "Layout interface"; no label, no clause)

* Realizability of the layout interface for every admissible target and instance. **Out of
  scope**: no target is represented.
* Existence of parameters for every admitted run (`refinement_run`). **Documented**: the
  parameters (`Refinement.Params`, `Refinement.ParamsOK`) and the translated runs (`TransRun`) are
  represented; no predicate states that every admitted run has parameters.

Results: `Refinement.Runs.runD_sim` (memory model: a layout and parameters that satisfy the
interface, non-vacuity). The obligation remains open.
-/
