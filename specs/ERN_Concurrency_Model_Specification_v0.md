# ERN — Concurrency Model Specification v0

**Edition v0 — November 16, 2026. Status: validated for reference reconstruction; not frozen.**

**Higher normative authority:** *ERN — Language Charter v0* (frozen).

**Frozen dependency:** *ERN — Memory Model Specification v0.1*.

## Validation and Revision Procedure

This edition has normative authority for reference reconstruction by the language owner’s explicit validation of this exact text. It is not frozen. Formal models, proof reports, and bounded tests are instruments for verifying this specification and do not supply additional language rules. Any change in normative meaning requires explicit identification of the affected clauses and renewed owner authorization.

## Scope

This specification defines the concurrent authority machine, synchronized authority derivation and the reference mutex abstraction, concurrency and event ordering, atomic/shared-mutation disciplines, cross-context handoff, storage validity ordering, and conditional data-race-freedom obligations. It defines semantic operations, not their surface syntax or a mandatory runtime representation. Typing, calling conventions, target compilation, physical event realization, safe-interface enforcement, and interoperability are governed by their named external contracts where indicated.

It does not amend either the ERN Language Charter v0 or the Memory Model Specification v0.1. The external obligations and proof boundaries are stated separately after C53.

---
# I. Concurrent Execution Machine

## C1. Execution Contexts

An **execution context** is a semantic execution unit with an identified current frame and an ordered sequence of operations within that context.

An execution context is not necessarily an operating-system thread, task, or scheduler unit.

Context identity does not confer access authority.

The presence of multiple contexts does not duplicate any allocation, place, authority, or validity dependency.

## C2. Concurrent State and External Contracts

The concurrent authority machine is:

\[ S_C=(C,F_C,P,I,A,D) \]

where:

- `C` identifies execution contexts and their lifecycle states.
- `F_C` contains their local frame stacks and extended frame-parent relation.
- `P`, `I`, `A`, and `D` retain their meanings from Spec 1.

The authority and dependency state is globally coherent. Library administration states, including synchronization registries, remain separate from `S_C`.

The concurrency specification introduces an external contract extension `K_C` with a projection to the unchanged Spec 1 contract `K`. A synchronization registry may be supplied as an **external argument** to `K_C.SyncAuthorized` by the reference abstraction. It does not become a component of `S_C`. The state-dependent soundness of this convention remains a verification obligation.

For an inherited operation executed by context `c`, all occurrences of “the current frame” refer to the top of the live local stack of `c`. References to live frames, usable places, ownership chains, authority holders and orphan conditions range over the globally live frame structure. An inherited `K.Satisfiable` obligation for a context-executed allocation is evaluated on the `S₃` view of the executing context; this must preserve the soundness requirements of Spec 1's unchanged `K`.

For a single context with no active concurrent mechanism, these interpretations and the projection of `K_C` must coincide with Spec 1.

## C3. Frame Ancestry — H1

Each live context has a nonempty local stack.

Frame identities are globally unique.

The initial context contains the base frame of Spec 1, which never exits.

A newly created ERN context receives an initial frame whose parent is the frame that created the context.

The extended `ancestor` relation follows the frame-parent links, including links across contexts.

It is reflexive, acyclic apart from reflexivity, and well-founded through its strict-parent relation.

On corresponding single-context states, it coincides exactly with Spec 1 §39.

Ancestry alone creates neither ownership nor access authority.

## C4. Context Creation — `spawn`

`spawn` is a concurrent transition modeled on O6.

**Preconditions**

1. The creating context and its current frame are live.
2. The new context and frame identities are fresh.
3. Every transmitted access parameter is an active derived authority held by the creating frame.
4. Parameter transmission yields each such authority to the new frame, without duplication.
5. The applicable mode, origin, footprint, local-shape, anchoring and origin-protection conditions of O6 hold under the re-indexed frame interpretation. The origin-protection condition O6.3 is evaluated in the final state from the new context's current frame; O6.4 (`AnchorOrderHeld`) is also checked in the final state.
6. Any transmitted value satisfies the by-value authority contract and reference-transition requirements of C5.

**Effects**

The new context is given an initial frame parented to the creating frame. Its local places and corresponding root authorities are created as in the applicable local-creation effect of O6. Access parameters are yielded to the new frame, which becomes their sole holder. No authority is copied.

For `spawn` without by-value arguments, these actions constitute the reference transition. For `spawn` with by-value arguments, the four-phase reference transition of C5 places parameter yield after value transfer; any alternative Spec 3 protocol must preserve that authority and publication ordering without being required to use those reference phases.

An active `Modify` derivative transferred to the child continues to suppress conflicting effective exercise through its origin in the creator, by Spec 1 §43.

**Preservation obligations, not additional preconditions:** The complete transition must preserve `ConcurrentWF`, the applicable global authority invariants, `AnchorOrder`, `AnchorOrderHeld`, `NoDangling` and `NoOrphan`. Their preservation must be proved from the concrete preconditions and effects, not assumed as a conjunct of the precondition.

**Outcome:** `ok` or `reject`.

## C5. By-Value Authority Contract at `spawn`

A `spawn` may transmit an owned value into a fresh local destination of a new context. From the viewpoint of Spec 2 this is one coherent concurrent transition satisfying the authority preconditions, effects and final-state checks below. It is not an arbitrary sequential application of O6 followed by O4. **For the Spec 2 reference authority machine and its proof obligations**, the four-phase reference transition below defines the intermediate authority states and the exact points at which O4/O6 checks are performed. These phases are a *reference instance of the contract*, not a mandatory implementation calling convention for Spec 3. The complete externally exposed calling convention, physical representation, cancellation/rollback and abnormal termination are governed by the **Spec 3 external contract** (`OB-C09`); alternatives must establish the same final-state and authority/event-order properties.

**Four-phase reference transition:**

1. **Create:** create the new context and initial frame, fresh local places, and their root authorities, **without yet yielding access parameters**. The fresh destination leaves are `Uninit`; the creator remains the executing frame for source-side checks.
2. **Transfer:** transfer each by-value source into its designated fresh destination. Evaluate every applicable non-resulting-state O4 requirement, including source-side `Modify` exercise and O4.4's external-derived-authority restriction, **at the start of the corresponding transfer phase**, after destination creation and before any parameter yield. For multiple by-value arguments, evaluate them in their explicit argument order, each against the state produced by earlier transfers. Source/destination footprints are disjoint and their ordered structural shapes match.
3. **Yield:** in the post-transfer state, check again that every access parameter to be yielded is active, derived and held by the creator under Spec 1 §72.1; yield the declared authorities to the child's initial frame without duplication. Independently required pre-composite conditions remain in force.
4. **Final checks:** evaluate O4's expressly resulting-state conditions (including §§63.6–63.9 as applicable), O6.3/O6.4 and all applicable anchor, origin and parameter-passing conditions on the final state. Preserve the correspondence of effects to O4/O6.

The reference phases describe one indivisible **successful abstract** `spawn` transition; they do not expose intermediate states as successful public operations. Any alternative protocol used by Spec 3 must refine the same Spec 2 single-step relation and must establish the five requirements below, including the effect of argument ordering and all failure-side guarantees. It is not automatically correct merely because its final initialized bytes match.

**Contract required of the Spec 3 protocol** (without duplication or externally observable partial success):

1. **Fresh destination before transfer:** the child's frame, fresh local places and initial root authorities exist when their destination-side authority is checked. Source-side checks still use the creating frame, before the corresponding value is consumed or any access parameter covering it is yielded.
2. **Legal transfer:** every by-value source obeys all applicable O4 requirements and uses the applicable `Modify` exercise at its source-check point. Each source/destination pair has disjoint footprints and matching ordered structural shapes. For multiple arguments, the protocol specifies an evaluation order with effects and checks consistent with earlier transfers.
3. **Legal parameter yield:** no access parameter is yielded before the corresponding source transfer is complete. At its yield point each such parameter is active, derived and held by the creator, meeting Spec 1 §72.1, then yielded without duplication to the child's initial frame.
4. **Final-state checks:** O4's expressly resulting-state conditions (including §§63.6–63.9), O6.3/O6.4 and applicable anchor, origin and parameter-passing conditions hold on the final state. The overall successful transition preserves the O4/O6 correspondence.
5. **Construction publication:** each physical destination construction write is represented and ordered as required by C27–C29, C47, and the safe-execution contract C51; creating a fresh place is not itself the publication of its initialized value to an unrelated context.

**Additional preconditions**

1. The creator has exercisable `Modify` over every source's relevant footprint at its source-check point (the start of the relevant Transfer phase in the reference transition); the source is usable and its required leaves are `Init`. An alternative Spec 3 protocol must justify corresponding source checks.
2. Every destination is a fresh local root of the child, with corresponding `Uninit` leaves, no derived authorities and a `Modify` root authority held by the child frame under `RootHeld`.
3. Only O4.1's **ordinary destination-side exercisability requirement** is replaced by the special fresh-destination construction condition. The source-side exercise condition remains required.
4. Every other applicable precondition of O4 remains required, including pinning, validity, external-derived-authority restrictions, self-blocking prevention, and final destination usability.
5. **No access parameter to be yielded may cover any leaf of any by-value source transferred by the same composite.** The test uses the declared source footprints before consumption, preventing a parameter from remaining associated with leaves becoming `Moved`.
6. No exclusive authority, dependent right or owned resource is duplicated by the composite.

**Effects**

The legal transfer effect marks consumed source leaves `Moved`, corresponding destination leaves `Init`, and relocates the corresponding held authorities, ownership links and dependencies by O4's effects. The legal parameter-yield effect changes holders of the access parameters and creates no rights.

**Preservation obligations, not additional preconditions:** The final transition must preserve `ConcurrentWF`, I1–I4, the applicable anchor ordering properties, `NoDangling` and `NoOrphan`. These must be established by proofs of the composite, not inserted as assumed final-state conjuncts.

**Outcome:** `ok` or `reject`.

The four-phase instance above is sufficient to **define** the Spec 2 reference `spawnVal` step, not to prove its preservation properties. The Spec 3 contract must separately give a realizable construction/transmission protocol, its definite operation order, representation and treatment of cancellation, rollback and abnormal termination; it must prove a refinement to the Spec 2 reference step that preserves every authority and event-order guarantee required by this reference `spawnVal` transition. The Spec 3 contract is the object of `OB-C09`; the preservation properties of the reference step are the object of `OB-C14`.

## C6. Frame Exit and Reparenting

`exitFrameC` applies O7 to the current **non-initial frame of the executing context's local stack**. That frame must have a surviving caller in the same local stack. This explicitly transposes O7.1 without making ordinary frame exit applicable to a context-initial frame.

**Preconditions**

1. The applicable conditions O7.2–O7.5 hold for the global authority and dependency state, under the extended ancestry relation.
2. In particular, no surviving active authority, owned place or required anchor is invalidated by the exit or its reanchoring.

**Effect**

Let `f` be the exiting frame and `p = parent(f)` its surviving immediate caller. Apply the applicable O7 effects. Every surviving context-initial frame whose immediate parent was `f` receives the new parent `p`. All other ancestry links are unchanged. Reparenting creates no right, does not revive storage, and does not independently authorize an otherwise invalid exit.

**Preservation obligations, not additional preconditions:** The resulting frame relation must be well-founded, and the complete transition must preserve the applicable authority and anchor invariants, including `AnchorOrder` and `AnchorOrderHeld`. Proofs must account for the effect of the extended ancestry relation without treating final-state invariants as assumed preconditions.

The transition introduces no implicit wait for the child contexts.

## C7. Context Termination — `terminate`

`terminate` applies the corresponding O7 validity requirements to the initial frame of a terminating non-initial context, after its nested call frames have legally ended.

Its effects include:

- ending the terminating context's initial frame;
- performing applicable releases and legal reanchoring;
- reparenting surviving context-initial frames as specified in C6;
- removing the terminating context from the live-context set;
- establishing its completed lifecycle state.

Completion does not automatically end resources independently and legally owned by surviving contexts.

The initial base context remains subject to its distinct base-frame restrictions.

## C8. Reference Completion Operation — `join`

`join` is a reference operation for observing completion of a previously created context. Its argument is a context identifier; this specification does not introduce an additional completion-capability mechanism.

**Requesting-context validity:** A `join` request requires the requesting execution context to be live. If the requesting context is not live, the operation returns `reject`, regardless of the target identifier or lifecycle state. This check takes precedence over the target-dependent classification below.

- If the identifier is unknown to the execution, the operation returns `reject`.
- If the identified context is live, successful completion observation is not yet enabled. Awaiting completion is not a new `Outcome3` result. A legal `join(c)` whose target is still live is **not activable** as a successful abstract step; this does not itself prescribe whether the caller blocks, retries or yields. Failure of legality (a non-live requesting context or an unknown identity) remains `reject`, and a completed target permits `ok`. A non-activated attempt has no successful state transition, but any physical polling or failed observation must be accounted for under C26–C29.
- If the identified context has a recorded completed lifecycle state, `join` returns `ok`.

**Successful effect:** The abstract state is unchanged, including `C`, `F_C`, `P`, `I`, `A`, and `D`. No consumed or “joined” marker is introduced by this specification.

The complete event-ordering consequences of successful completion observation are deferred to the concurrent event model. `join` is not the only possible completion protocol, and its existence does not impose structured concurrency universally.

## C9. Cross-Context Authorities and Dependencies

Transferability and shareability are distinct properties.

Their applicability depends on values, authorities, contained resources, declared storage properties, dependencies, and external contracts.

An authority cannot be duplicated merely because it is transmitted between contexts.

An active derivative continues to restrict its origin according to effective rights.

A frame exit is rejected when it would invalidate a surviving authority or dependent value.

Conversely, the departure of a creating frame need not terminate a child context whose surviving authorities and resources remain valid after legal reanchoring and reparenting.

The complete typing and composition rules for transferable and shareable values remain an interface obligation for Spec 4.

## C10. External Contexts

The initial parent relationship of a context entered from an external environment remains open.

Such a context must receive valid frames, authorities, and resource contracts through an explicitly justified interoperability mechanism.

No universal attachment to frame 0 is established by this specification.

---

# II. Synchronized Authority Derivation

## C11. Separation of Mechanisms

Synchronization controls when exclusive access may be obtained.

The ordinary authority discipline controls who may exercise an acquired authority and how that authority may be derived, stored, transmitted, or released.

The concurrent memory-ordering model controls whether conflicting accesses are sufficiently ordered.

These are distinct obligations.

The synchronized derivation mechanism does not modify ordinary `ExercisableAt` or inherited O1–O16.

## C12. Synchronization Registry

A reference library abstraction maintains logical entries:

```
SyncEntry {
    guarded: AuthorityId
    grant: Option<AuthorityId>
}
```

An entry is live exactly while `guarded` is active. This registry belongs to library abstraction state, not `S_C`.

A live entry requires an active `guarded` authority of own mode `Modify`, held by a usable place `slot` belonging structurally to a mutex value `M`, and a usable controller leaf `ctl` at its declared field position within `M`.

`ControlOf` is the **per-instance positional relationship**: it identifies `M` as the structural parent of `slot` at `guardedField`, then identifies `ctl` as the child of `M` at `controlField`. `M` and `slot` are structural places; storage owned by `M` is not automatically in `footprint(M)` under Spec 1 §40.

For distinct live mutex entries, both their `guarded` identities and their `ControlOf` controller leaves must be distinct.

A legal transfer of the **whole mutex value `M`**, or a structural ancestor containing `M`, may carry `slot` and its controller together and preserve the association positionally (`slot → slot′`, `ctl → ctl′`). This includes cases in which a grant is active, provided all O4 conditions hold. By contrast, the safe abstraction excludes independent transfers whose source is `slot`, a strict structural subplace of `slot`, or `ctl`, as specified in C22.3. Such restrictions do not redefine O4. A transfer of `M` as a whole, or of an enclosing root, remains eligible under O4's own preconditions; preservation of `SyncInv` is a separate proof obligation.

## C13. Reference Construction — `newMutex`

`newMutex` is a library operation establishing a synchronized authority-administration entry. Let `slot` be the place holding `guarded`, `M` its immediate structural parent and `ctl = ControlOf(M,slot)` its controller leaf.

**Preconditions**

1. `guarded` is active, of own mode `Modify`, and legally held by the usable `slot`.
2. The constructing frame has ordinary exercisable `Modify` over `guarded` under Spec 1 §43.
3. The declared structural positions identify the usable `slot` and a usable controller **leaf** `ctl` in the same `M`.
4. `footprint(guarded) ∩ footprint(M) = ∅`. This is the reference mutex's structural disjointness requirement, allowing the control value `M` to be shared under compatible `Observe` authorities while `guarded` exclusively protects a distinct storage footprint.
5. If `guarded` is stored by O8, the construction respects O8.3. In the reference arrangement, the protected root `T` is owned by `M`, not by `slot`; its leaves are not thereby included in `footprint(M)`.
6. `K.SharedMutable(ctl)` holds for the controller leaf.
7. The `guarded` identity is not registered as a live administrative identity by any other registered administration. This is an unconditional unified consistency guard, following the non-duplication principle of Spec 1 §56.
8. **Controller uniqueness:** no other live synchronization entry is associated with `ctl`. The association is injective among live entries.
9. No active descendant of `guarded` covers a leaf of `footprint(guarded)`.
10. **Initialization:** all structural leaves in `footprint(M)` are `Init` before construction. The operation does not implicitly initialize them. Storage merely owned by `M`, but structurally outside `footprint(M)`, is not included in this requirement solely by ownership.
11. **Controller-initialization authority:** The constructing frame has ordinary exercisable `Modify` authority with effective mode `Modify` over the controller leaf `ctl`, under Spec 1 §43 and the applicable ordinary-write requirements of O10.1 (§67.1). The ordinary-write exclusivity requirement of O10.2 (Spec 1 §67.2) also applies to this non-atomic write; whether it follows from the reachable-state invariants is a verification target, not an assumption. This authority is required to justify the non-atomic physical write establishing the controller's initial available state. A controller-access right sufficient only for an `Observe`-mode shared mutation under Spec 1 §68.2 does not satisfy this requirement.

**Effect**

The library registers an initially available `SyncEntry { guarded, grant = none }`, without creating another access authority over the protected storage or initializing any leaf of `M`. Library administration state remains separate from `S_C`.

**Outcome:** `ok` when all applicable preconditions hold and the registration effect is established; `reject` when any applicable precondition fails. This operation defines no `fail` outcome.

**Controller-initialization clarification:** This is an abstract registration effect: the operation changes no structural leaf's abstract initialization state. C13.10 already requires every structural leaf of `M`, including `ctl`, to be `Init` before construction; `newMutex` does not change an `Uninit` leaf to `Init`. Separately, the physical realization establishes the controller's initial available synchronization value by a **non-atomic write** to `ctl`, justified by C13.11 and subject to the applicable O10.1/O10.2 requirements. The term *controller initialization* in C31 and C48 denotes that physical synchronization-state write, not a transition of abstract structural initialization state. The non-atomic write is represented as an initial modification in `mo` under C31; it does not itself establish `sw`. Its concrete event, the ordering of this write with accesses in other execution contexts, and the correspondence with the initially available registry entry remain obligations under C27–C29, C42, C48 and `OB-C05`. The authority-only kernel state `S_C` does not establish the physical write or its ordering.

**Preservation obligation:** The construction must establish the entire `SyncInv` and `GrantDiscipline` suite for the new and previously live entries. This is not an additional resulting-state precondition.

**Interface and realization obligations:** The safe public interface must prevent falsification of the positional controller association (C13.3); the controller synchronization protocol (C13.6) must be enforced; and the initial physical controller state must correspond to the newly available abstract registry entry. C13.11 supplies a required authority premise for the initial ordinary write, but does not by itself prove its ordering with other contexts or its target realization. These are not claimed to follow from the authority-only state `S_C`. C13.11 does not alter the abstract `newMutex` effect.

A reference representation may place the protected value in a distinct logical owned-storage root. No separate physical allocation is implied.

## C14. Concurrent External Contract — `SyncAuthorized`

`K_C` extends the unchanged Spec 1 contract `K`. The concurrent authorization predicate accepts the **current logical synchronization registry as an explicit external argument**:

```
K_C.SyncAuthorized(state, sync_registry, guarded, requesting_frame)
```

The registry is supplied by the library contract and is not part of the kernel state `S_C`. It must refer to the same logical registry state used for the library transition.

For the reference mutex, the library's **authorization facts**, and only these facts, are:

1. There exists a live registered entry with the requested `guarded` identity.
2. That entry has `grant = none`.
3. The requesting frame has the required effective and exercisable access to `ControlOf(entry)` under the controller-access obligation corresponding to Spec 1 §68.2.

The library must prove, under `ConcurrentWF`, the applicable Spec 1 invariants, `SyncInv`, `GrantDiscipline`, and the abstraction's encapsulation contract, that these facts imply the remaining authority prerequisites for `deriveSync`, including origin-chain validity, sufficient effective mode, absence of blocking descendants and I1 conservation.

The opaque authorization predicate must not be defined by simply conjoining the conclusions the library is required to prove. Its instantiation is state-dependent, and correctness must be reestablished for every enabled acquisition.

`SyncAuthorized` does not create an authority, does not introduce ambient context rights, and cannot be used outside the corresponding valid synchronization contract. The precise synchronized physical realization remains deferred under `OB-C05`.

## C15. New Concurrent Transition — `deriveSync`

`deriveSync` is a new concurrent transition creating an ordinary derived `Modify` authority from `guarded` over `footprint(guarded)`.

**Preconditions**

1. **Own-mode bound, retained from Spec 1 §43 and O1.1:** `guarded` is active and its **own mode permits `Modify`**. In the `Observe | Modify` mode order this requires own mode `Modify`, **even if `footprint(guarded)` is empty**.
2. The complete applicable origin-chain and effective-anchor validity requirements of O1.1 hold.
3. **Exclusive authorization:** `K_C.SyncAuthorized(state, sync_registry, guarded, current_frame)` holds. This predicate is the **only** authorization for `deriveSync`. Neither the current-frame-holder nor the place-holder alternative of ordinary `ExercisableAt` independently enables this new transition. Ordinary O1 retains both alternatives unchanged.
4. O1.2's leaf, subfootprint and effective-mode conditions hold for the full protected footprint and requested mode `Modify`.
5. O1.3's structural exclusivity and I1 preservation conditions hold.
6. O1.4's freshness, legal current-frame holder and resulting-state validity conditions hold.

**Effect**

A fresh, active authority is created with own mode `Modify`, origin `guarded`, full footprint `footprint(guarded)`, and holder equal to the executing context's current frame. No other access right is created.

This grant is ordinary after creation: `ExercisableAt` remains exactly as in Spec 1 §43 for its exercise, reborrowing, storage and legal release. The synchronized exception concerns **only the authorization for creating this derivative**; it does not weaken the source activity, own-mode bound, anchor, effective-mode or structural exclusivity requirements of O1.

**Outcome:** `ok` or `reject` for the abstract safety transition; a busy controller may make the enclosing library acquisition temporarily non-enabled, as specified in C16.

## C16. Reference Acquisition — `acquire`

The library operation `acquire` combines synchronization-controller acquisition and `deriveSync` into one coherent abstract operation.

**Outcome classification**

1. **`reject` — invalid request:** a failure of entry existence/liveness (C14.1), requester-side controller-access authority (C14.3, including Spec 1 §68.2), frame/anchor legality, or any independently violated invariant or Spec 1 safety precondition yields `reject`. In particular, with `grant = none`, an independently invalid protected-authority invariant is `reject`, not ordinary contention. Caller-side illegality is not masked by another context's occupancy.
2. **Temporarily non-enabled — contention:** when the request is legal, the entry's recorded `grant ≠ none` (C14.2), including an inactive recorded grant with surviving derived authorities, or occupation of the controller by another acquisition under its valid protocol, makes `acquire` temporarily non-enabled. The inability to derive `guarded` attributable to such a recorded grant is also non-enablement, not `reject`. In this situation the request has **no outcome**: neither `ok`, `reject`, `fail`, nor any new `Outcome3` value is produced, and there is no successful abstract state transition. A concrete attempt may nevertheless emit physical reads and failed-CAS events, all covered by C26–C29. Non-enablement can persist indefinitely.
3. **`ok` — successful acquisition:** all validity and authority obligations hold, the grant is available and the controller is successfully acquired under its protocol, and the successful effect below is established.

Independently invalid requester-side conditions take precedence over temporary non-enablement **for the same abstract state**; this is a classification of causes and does not assert that a concurrent call has an outcome independent of changing state. Resource `fail` outcomes of `alloc`/`issue` are outside this criterion.

For `acquire`, the authorization facts C14.1 and C14.3 are safety conditions; C14.2 is a contention condition. The combined `SyncAuthorized` predicate of C14 is therefore insufficient by itself to distinguish `reject` from temporary non-enablement. This does not alter the independent transition `deriveSync` or its C15 conditions.

The library must establish all non-dynamic safety preconditions before committing a successful acquisition. Legality and activation are semantic properties; physical observability by the caller is not the defining criterion. The language execution semantics, not this model, may specify blocking/retry policy and progress; the Spec 2 transition relation guarantees no progress.

Its success:

1. acquires the controller under the applicable synchronization protocol;
2. creates the valid grant through `deriveSync`;
3. records the resulting grant identity in `SyncEntry.grant`.

No partially successful abstract operation may expose an invalid ordinary state.

The controller's physical linearization, atomic ordering, and correspondence obligations are specified in C41, C48 and C49 and remain subject to `OB-C05`.

## C17. Reference Unlock — `unlock`

`unlock` is a derived library operation.

**Abstract preconditions**

1. A live entry has `grant = some g`.
2. `g` is active and legally releasable under O3.
3. No active descendant or surviving validity anchor prevents its release.
4. The acting frame has the applicable controller-access right, with effective mode present on `ControlOf(entry)` (Spec 1 §68.2), in the state before `unlock`. Provided that preconditions 1 through 3 hold, it also has that right in the prospective authority state obtained by legally releasing the recorded grant `g` under O3. The prospective state is evaluated solely for checking this precondition of the coherent `unlock` transition. It is neither committed nor externally observable unless that transition succeeds.

**Outcomes**

- **`ok`** if all applicable preconditions hold and the coherent effect below is completed.
- **`reject`** if any required entry, register, authority, dependency, O3-release, or controller-access condition fails, including a recorded `g` that has become inactive. Contention does not convert such a failure into temporary non-enablement.

This specification defines no waiting outcome for `unlock` on a failed C17 precondition. A physical implementation may impose its own internal progress protocol, but it may not report an invalid request as a successful abstract unlock.

**Abstract effect**

The grant is released according to O3, the registry records `grant = none`, and the controller's logical synchronized state is made available as one coherent library transition.

**Realization obligation, not an assumed abstract precondition:** The controller update must satisfy `K.SharedMutable` and the required event, atomicity and ordering discipline. The physical protocol is specified in C41, C48 and C49; its correspondence is an `OB-C05` obligation, not a conclusion from the abstract transition.

## C18. Abandoned Grants and Recovery

A grant may become inactive through an inherited legal release or frame exit without a corresponding `unlock`; the live registry entry may still record `grant = some g`. This can leave the mutex unavailable indefinitely without itself violating memory safety.

`resetLock` is a library recovery operation.

**Abstract preconditions**

1. Ordinary `ExercisableAt(guarded, Modify)` holds under Spec 1 §43, requiring the appropriate exclusive exercise through the mutex's holder.
2. No active descendant of `guarded` covers any protected leaf, as in the relevant no-descendant condition of Spec 1 §78.2.
3. `ControlOf(entry)` resolves to an existing, usable controller **leaf**, as required by C21.3, and recovery does not invalidate surviving dependent authorities. The controller-initialization invariant is established separately for every live entry by C21.7.
4. **Controller-access authority:** The acting frame has the applicable controller-access right, with effective mode present on `ControlOf(entry)`, under the corresponding requirement of Spec 1 §68.2. This condition is independent of, and additional to, `ExercisableAt(guarded, Modify)` in item 1. It authorizes the controller access required by the recovery protocol without granting any new authority.

**Outcomes**

- **`ok`** when the applicable recovery and authority conditions hold and the coherent effect below is completed.
- **`reject`** when any applicable authority, registry, dependent-validity, controller-validity, or Spec 1 precondition fails. Controller occupation does not mask such a failure as temporary non-enablement.

There is no newly introduced `resetLock` waiting outcome and no new prerequisite that the recorded grant first be `none`. This transition is the exceptional recovery protocol described here, not ordinary `unlock`.

**Abstract effect**

The registered grant becomes `none` and the controller's logical state becomes available. Recovery does not revive an inactive grant and does not fabricate authority.

**Realization obligation:** The exclusive recovery discipline and its physical controller update must meet `OB-C05` and the event constraints in C41, C48 and C49; this is not presumed proved by the abstract state transition. The recorded grant may still be `none`.

## C19. Synchronized Administration

A grant protecting an administrative value may permit `MetaRight` only when it provides exercisable `Modify` over every required leaf of that administrative value.

The grant must therefore cover the entire required administrative footprint.

This does not bypass Spec 1 §36.

Issuance, recycling, and reset operations retain their existing authority and dependency restrictions.

The lifetime of a block issued during synchronized administration is determined by its actual origin chain, holders, anchors, and ownership relations, not merely by the lifetime of the synchronization grant.

---

# III. Invariants and Correspondence

## C20. Concurrent Frame and Authority Well-Formedness

`ConcurrentWF` extends frame well-formedness to multiple local stacks and one global parent relationship.

It must preserve the applicable structural, ownership, holder, and authority conditions of Spec 1.

Every inherited transition and every new concurrent transition must preserve the applicable global invariants.

Reparenting must preserve extended ancestry and validity properties.

## C21. Synchronization Invariant — `SyncInv`

For the reference mutex abstraction, the following state properties must be preserved over all **live** entries, except the bound-identity property in item 6, which applies to every entry:

1. **Guarded authority:** `guarded` is active, has own mode `Modify`, and is held by a usable place.
2. **Grant record:** If `grant = some g`, then the recorded authority exists and `origin(g) = guarded` and `footprint(g) = footprint(guarded)`. `g` need not be active; the invariant must handle legal release and reanchoring without silently weakening these equalities.
3. **Controller validity:** `ControlOf(entry)` identifies an existing usable **leaf** associated with the holder `slot` and its structural mutex parent `M`.
4. **Controller uniqueness:** Distinct live entries have distinct `ControlOf` leaves; the guarded-identity uniqueness guard is also respected. The same controller cannot be registered twice under different guarded identities.
5. **`GrantSubtree`:** If `grant = some g` and `g` is active, every active descendant of `guarded` covering a protected leaf is either `g` itself or a descendant of `g`. This is a distinct invariant, necessary to restore grant availability after legal `unlock`.

   **Clarification — inactive recorded grants and surviving derivatives:** The condition above applies when the recorded grant is active. It does not require a recorded inactive grant to remain an ancestor, under the current `origin` relation, of every legally surviving derivative.

   Legal reanchoring under Spec 1 §73.4 may change the direct `origin` of an existing surviving authority, including making it a direct descendant of `guarded`, without creating an authority or introducing an existing authority into the transitive descendant set. Consequently, when the recorded grant is inactive, a covering derivative may remain active under `guarded` even though its current origin chain no longer contains the recorded grant.

   While any such surviving derivative remains active and covers a protected leaf, `resetLock` cannot succeed (C18.2).

   When `grant = none`, `GrantDiscipline` in C22 requires that no active descendant of `guarded` cover a protected leaf.

   These statements clarify consequences for reachable admitted executions. They add no independent state conjunct to `SyncInv`, require no historical-origin field, and do not prohibit otherwise legal surviving derivatives. They establish authority provenance, not the `happens-before` ordering required by C46.
6. **`RegBound`:** Every registered `guarded` identity denotes an existing authority identity, even when its entry is no longer live. This prevents a dormant entry from becoming live merely when a fresh authority is created with its identity.
7. **Structural initialization:** For each live entry, every structural leaf of the place `slot` holding `guarded` is `Init`, and the associated controller leaf `ctl = ControlOf(entry)` is `Init`. This does not impose initialization of storage merely owned by `M` but outside its structural footprint. Preservation by every admitted transition is an obligation to prove, not an assumed precondition.

`SyncInv` is not a claim that every physical controller update is already modeled. Controller-state and event correspondence remain obligations of the library realization in C25 and `OB-C05`.

The live-entry invariants must remain valid when a recorded grant becomes inactive without `unlock`.

## C22. Grant Discipline and Safe Abstraction Encapsulation

The reference abstraction requires **`GrantDiscipline`**:

```
live(entry) ∧ entry.grant = none
⇒ no active descendant of entry.guarded
   covers any leaf of footprint(entry.guarded)
```

It is not implied by structural exclusivity I1 alone. Its proof must use an explicit encapsulation condition on the **allowed traces of the safe abstraction** (`EncapsulatedTrace` in C51). This is an abstraction contract, not a new restriction of the inherited kernel O1–O16.

For each live synchronization entry, that contract has the following **six requirements**:

1. **Ordinary derivation:** the safe abstraction does not expose an inherited `derive` or `split` operation with `source = guarded` while the entry is live.

   No operation exposed by the safe abstraction, including a compound operation that performs an internal `derive` or `split`, creates an ordinary authority whose origin at creation is `guarded` while the entry is live.

   **Clarification:** This restriction concerns the creation of authorities by operations exposed through the safe abstraction. It is not a state invariant forbidding an existing authority from having `origin = guarded` after a legal reanchoring.

   In particular, reanchoring performed under Spec 1 §73.4 during a legal `exitFrame` or `terminate` may change the direct `origin` of an already existing surviving derivative to `guarded`. Such reanchoring does not issue a new derivative, does not constitute an independent `derive` or `split` operation with `source = guarded`, and does not introduce an existing authority from outside the transitive descendant set of `guarded` into that set while the entry remains live.

   Ordinary derivation from an active acquired grant, from its descendants, or from a legally surviving descendant remains eligible under the applicable inherited preconditions and the complete holder-chain restrictions of C22.6. Such derivation is not directly from `guarded` merely because its source is a descendant of `guarded`.

   The creation of a synchronized grant directly from `guarded` remains restricted to the validated `acquire` protocol through C22.2.
2. **Synchronized derivation:** the safe abstraction does not expose an independent, raw `deriveSync` of `guarded`. Such derivation is available only inside the validated `acquire` operation.
3. **Protected structural transfers:** the safe abstraction does not expose an independent `transfer(source, destination)` when `source` is (a) the place `slot` directly holding `guarded`, (b) any **strict structural subplace** of `slot`, or (c) the associated controller leaf `ctl`. For a by-value `spawn` with multiple transfers, this restriction is evaluated for **each** transfer source against the state at the start of its own transfer phase, as defined in C5.2. A transfer of the complete mutex value `M`, or of a structurally enclosing value, remains eligible for O4 under **O4's own unchanged preconditions**. Preservation of `SyncInv`, including positional association, initialization and controller uniqueness, by every eligible transfer is a **proof obligation**, not an additional authorization precondition. This rule restricts the safe interface, not the kernel transition O4.
4. **Controller-access and state-integrity protocol:** For every live synchronization entry, the safe abstraction does not expose ordinary `read3` of `ControlOf(entry)`, even when the acting frame holds an applicable `Observe` right under C14.3. It also does not expose ordinary `write3`, out-of-protocol `writeShared`, or any other operation outside the validated controller protocol whose actual access or effect footprint includes the controller leaf.

   This restriction covers physical reads and writes of the controller, changes to its initialization state, and changes that make the controller leaf itself the holder or owner of an authority or allocated resource.

   In particular, while the entry remains live, the restriction excludes:
   - `store` targeting the controller leaf;
   - `issue` using the controller leaf as its destination;
   - `alloc` using the controller leaf itself as the owner of a newly allocated root;
   - `alloc` whose provider-metadata accesses may write the controller leaf;
   - any other inherited or compound operation producing an equivalent access or effect on that leaf.

   The restriction is evaluated against the leaves actually affected by an operation, including relevant physical metadata accesses. Merely naming a structural place containing the controller does not establish that the controller leaf itself is accessed or modified.

   In particular, `alloc(owner = M)` is not excluded solely because `ControlOf(entry)` is a structural leaf of `M`. Ownership of storage by the mutex value remains eligible under C13.5. Such an allocation must nevertheless satisfy every applicable inherited precondition and must not independently access or alter the controller leaf through its provider, destination, or other effects.

   A change solely to a dependency relation, without a physical controller access or another prohibited controller-state effect, is not excluded by this item merely because it concerns the controller. All applicable inherited dependency and lifetime requirements remain in force.

   An authority whose footprint includes the controller does not, by that fact alone, constitute an access or effect on the controller.

   Valid internal controller operations performed by `acquire`, `unlock`, or authorized `resetLock` remain within their respective validated protocols. Controller initialization through `newMutex` remains governed by C13.

   A legal transfer of the whole mutex value `M`, including by-value `spawn`, or of a structurally enclosing value remains eligible under C22.3 and the unchanged O4 preconditions. Operations that make the entry dead remain eligible under C12, C22.5, and the applicable inherited lifetime rules. These exceptions do not waive the preservation of `SyncInv` or the applicable realization obligations.

   This requirement restricts the safe abstraction, not the inherited kernel transitions or their outcomes. A kernel operation may independently return `ok` without being admitted by the safe mutex interface.

   Enforcement of the safe interface belongs to Specs 4 and 10. Complete physical-access and effect-footprint coverage, controller correspondence, and preservation remain obligations under C23, C25, C29, `OB-C05`, `OB-C20`, and `OB-C28`.
5. **Protected end-of-use:** while the entry is live, the safe abstraction does not expose an inherited `endUse(place)` when `place` is (a) the controller leaf `ctl` or (b) any **strict structural subplace** of `slot`. `endUse(slot)`, `endUse(M)` and operations on structural enclosing values retain their unmodified kernel O12 preconditions and effects; their validity depends on those rules, including the release or invalidation of any required authorities. This restriction does not change O12 or prohibit every legal termination of the mutex value.

6. **Protected holder-chain justification:** for every ordinary exercisability judgment under Spec 1 §43 (`ExercisableAt`) or right over a place (`HasRight`) on which an admitted step depends, there must exist a valid justification whose **entire authority-holder chain excludes the `guarded` authority of every live synchronization entry**. The requirement applies to the actual right relied on by the step, including the source, target, owner, holder, controller and administration rights where relevant, rather than only the authority explicitly passed as an argument. It includes rights checked in intermediate or resulting states of a composite step whenever the inherited precondition checks them there. For `unlock` specifically, the premise inventory includes the controller-access right checked in the state before the operation and the retained controller-access right in the prospective state after releasing the grant under C17.4; each relied-upon justification must be free of a live `guarded` holder chain under this item. A different valid chain that does not pass through a live `guarded` suffices. Ordinary access through a legitimate acquired grant is permitted: the grant's justification is through its rightful frame or holder chain, and the grant itself is not excluded merely because its origin is `guarded`. This is **safe-abstraction trace encapsulation**, not a change to any inherited Spec 1 precondition.

   **`resetLock` exception:** C18.1 deliberately checks `ExercisableAt(entry.guarded, Modify)` for the entry being recovered. Its **subject** `entry.guarded` is exempt from the no-live-`guarded` test for that recovery check alone. The right on the holding `slot` that justifies this exercise must nevertheless have a valid holder chain containing **no other** live entry's `guarded`. This exception neither admits arbitrary access through `entry.guarded` nor relaxes C18.2–C18.3, controller/recovery ordering, or any other ordinary access rule.

Requirements 1–6 all constrain the allowed traces of the safe abstraction. In particular, requirement 4 excludes ordinary `read3(ControlOf(entry))` from `EncapsulatedTrace` as required by C51, while preserving O9 as a kernel operation. Requirement 6 also excludes accesses and other rights justified through a live `guarded` without the relevant grant. Their enforcement must follow from encapsulation and the public interface, rather than hidden runtime constraints or undisclosed hypotheses on the kernel. Preservation of `SyncInv` and `GrantDiscipline` under these explicit restrictions is the proof obligation stated in C23.

Requirement 4 is **also** a physical realization/interface obligation; its enforcement is not falsely claimed to follow merely from the authority-only predicate `GrantDiscipline` or the abstract machine `S_C`.

## C23. Preservation of Ordinary and Concurrent Operations

Formalization must demonstrate preservation of `ConcurrentWF`, the complete `SyncInv` (including controller uniqueness, structural initialization, `GrantSubtree` and `RegBound`) and `GrantDiscipline` for every applicable inherited and new transition, including `transfer` and by-value `spawn`, under the explicit safe-abstraction restrictions C22.1–3 and C22.5. The reference abstract trace relation must include by-value `spawn` and must not silently omit any applicable kernel operation.

For inherited operations, the kernel transition remains governed by the unmodified Spec 1. An operation that is a valid kernel step but not exposed by the safe mutex abstraction may violate the **library's** trace discipline without constituting a memory-safety counterexample against the kernel.

A dead entry or recorded inactive grant is permitted where its contract allows it. A live entry with an invalid positional controller, duplicate controller or unauthorized grant is not a valid safe-abstraction state.

Resulting-state invariants must be **proved**, not included as circular preconditions when their preservation is the proof obligation. Any lemma conditional on encapsulation must expose that condition in its theorem statement or the reachable-trace assumptions.

## C24. Sequential Conservativity

For corresponding single-context states and inherited operations O1–O16:

- preconditions and outcomes coincide;
- projected effects coincide;
- authority exercise retains the Spec 1 definition;
- sequential ancestry is recovered;
- the applicable sequential invariants are preserved.

The reachable sequential domain under inherited operations must correspond to the sequential domain of Spec 1 under the stated state correspondence.

A transition history involving additional contexts must not return to an invalid single-context authority state.

## C25. Abstract-to-Concrete Realization Obligations

The abstract machine imposes no universal runtime authority metadata. The synchronization library may maintain justified implementation metadata; the frozen Spec 1 §4 does not forbid it.

A sound implementation of the reference mutex must prove correspondence between the external registry and physical controller, preserve `ControlOf` under legal whole-value transfers, and enforce safe-interface encapsulation including C22.1–6. In particular, the prohibition of `endUse` on `ctl` or a strict structural subplace of `slot` is an interface property; the unchanged kernel O12 remains available to programs outside that abstraction contract.

Successful controller acquisition must imply the remaining `deriveSync` obligations through proven state invariants and contractual authorization facts. For the reference mutex, authorization is instantiated using **only** the entry's liveness, grant availability and the requesting frame's controller access. Its proof may use the global kernel invariants and the synchronization invariants but may not place its desired conclusion inside the definition of `SyncAuthorized`.

The ambition to check only the physical lock word at runtime is a reference optimization target, not a universal requirement of Spec 1. The exact atomicity, event-ordering and data-race obligations are deferred to `OB-C01`–`OB-C06`, with controller realization specifically under `OB-C05`.

---

# IV. Concurrent Event Model

## C26. Executions, Abstract Steps, and Event Graphs

A **concurrent execution** consists of:

1. a finite or potentially unbounded trace of transitions of the globally coherent concurrent authority machine of C1–C25;
2. the external library-administration states required by those transitions, including `SyncEntry` states and the `K_C.SharedDiscipline` contract;
3. an event graph induced by the abstract steps and their concrete realizations, with identifiable events and relations `po`, `rf`, `mo`, and `sw`;
4. evidence that the event graph satisfies the selected, explicitly named consistency predicate; and
5. where safe execution is asserted, the additional restrictions of C51.

The ordering of transitions in the authority-machine trace is an **abstract interleaving**, used to compute which operation can occur next. This total enumeration is **not** a hardware memory order, and it does not itself imply `happens-before` between events of distinct contexts. In particular, the fact that a permission becomes exercisable in a later state is not evidence that a physical write in an earlier state has been published.

Each successful transition has a defined association with one or more semantic events. A pure abstract operation may produce only a logical event. A compound operation may produce several access, synchronization, and authority-marker events. Failure and temporary non-enablement do not create successful authority-state transitions. A legal but non-enabled request has no successful abstract transition; an illegal request has the specified `reject` outcome. Neither status may be identified with a physical event-free call. The execution semantics of blocking, retries or scheduling belongs to the language/runtime contracts and is not a progress guarantee of Spec 2. Any physical accesses performed while testing, retrying, or rejecting a call must nevertheless be accounted for by its realization; they cannot be silently discarded from the physical event graph.

The event model does not require a runtime record for every logical event. A logical event is a semantic point used to define and prove ordering, not necessarily an executed instruction.

## C27. Event Attributes and Realization Origin

An event is associated with a context, the abstract transition or library phase that generated it, and a position within that transition. Its **attributes are cumulative, not mutually exclusive**:

- `acc`: an actual memory-access component, carrying an access kind `read`, `write`, or `RMW`, a concrete byte range, an atomicity classification, and an applicable memory order for an atomic access;
- `sync`: an event eligible to participate as the source or target of a justified `synchronizes-with` (`sw`) relation;
- `validity`: a semantic begin/end-of-storage-validity event, identifying the storage identity, the applicable byte/provenance realization and whether validity begins or ends; it is not itself an `acc` or `sync` and cannot be erased by the pure-authority rule without a validity-correspondence proof;
- neither `acc`, `sync`, nor `validity`: a **pure authority marker**, recording a logical authority change without claiming a physical access, lifetime effect or synchronization effect.

An event may carry **both** `acc` and `sync`, notably a successful atomic controller operation used by the reference mutex. The event kind and the ordering attributes are separate from a permission's mode (`Observe` or `Modify`).

The access components must come from the **realization** of the step, not just its high-level name. For example, `transfer`, the by-value phases of `spawn`, `store`, `issue`, and `newMutex` may write or copy bytes even when some of their logical authority effects are independent of memory representation. Metadata operations required by a library implementation must also be accounted for. The same abstract step may therefore have both pure authority markers and concrete access events. It may also emit semantic `validity` events. Validity does not follow from mere ownership mode or initialization state: `Moved` and `Uninit` do not, by themselves, end storage validity.

A pure `derive`, `release`, `split`, logical transfer of a holder, or entry/exit of an abstract frame creates no physical memory access **solely because of that abstract effect**. This statement does not authorize erasing physical accesses that a particular implementation of that step actually performs.

**Validity-event coverage by reference operation (semantic events, not necessarily machine instructions):**

| Operation | Validity event | Storage concerned |
|---|---|---|
| `enterFrame` | begin | local storage of the entered frame |
| `spawn` / by-value `spawn` | begin | local storage of the child, including fresh by-value destinations |
| `alloc` | begin | newly allocated root and its storage |
| `exitFrame` | end | local storage whose validity ends with that frame |
| `terminate` | end | storage of the terminating context's frames whose validity ends |
| `free` | end | deallocated storage and the invalidated place as determined by Spec 1 |
| `endUse` | end where applicable | transitively owned storage that ceases to live, **not** the place that remains usable under Spec 1 §69 |

`transfer` does not, by its logical moved/uninitialized effects alone, emit a begin/end validity event. A realization may still emit physical copy accesses. An implementation-specific event map must preserve the exact validity changes required by Spec 1 §§69–70 and §82; the table does not redefine them.

## C28. Program Order, Lifecycle Markers, and Within-Step Order

`po` is the strict order of semantic events within **one execution context**, including the ordered phases of a compound step. It includes pure authority markers so that the loss and acquisition of permissions can be positioned relative to actual physical accesses.

For the reference lifecycle protocol:

- the parent emits a `spawn` synchronization event;
- the new child emits a distinguished `start(c)` synchronization marker, generated by the `spawn` protocol **before the child's first ordinary or authority step**;
- a context that successfully executes `terminate` emits a `complete(c)` synchronization marker after its last event;
- a successful `join(c)` creates a synchronization event in the joining context.

`start(c)` is **not** the child's first arbitrary operation. This avoids attributing synchronization behavior to a `derive` merely because `derive` happens to execute first. Similarly, `complete(c)` is a distinguished termination marker, not a claim that the last ordinary operation was itself a synchronization operation.

For compound synchronization steps, internal event order is significant:

1. a logical **loss** of an incompatible capacity is `po`-before the synchronization event that publishes that loss (for example, the loss marker preceding a release store of `unlock`);
2. a synchronization event that establishes acquisition is `po`-before the corresponding logical **gain** marker (for example, an acquiring RMW preceding exposure of a mutex grant);
3. ordinary accesses protected by the gained authority occur `po`-after that gain marker.

These are **semantic order obligations**. The following additional within-step and cross-context validity obligations also apply: a begin-validity event precedes every construction write to its storage; every physical access occurs while the precise authorization that justifies it is valid, and a composite step places its access before any end-validity event for the accessed storage. Within one context these are `po` requirements (or explicitly represented internal step order). Across contexts the relevant relationships must be established by `hb`, not by abstract trace index alone. For by-value `spawn`, publication to the child must follow construction writes as required by C5 and C47. A `complete(c)` marker follows all end-validity events caused by the terminating context, and the successful `join(c)` may observe that completion only under C32. The position of these semantic events is required even when no machine instruction corresponds one-to-one to a marker.

For a multi-leaf `writeShared` admitted under a composite contract (C38), that contract must determine the within-step `po` order of its actual access events and any applicable validity and authority markers, including which writes precede any atomic release publication. The declared order is a semantic requirement on the step realization, not an order inferred from the abstract interleaving or an implicit cross-context `hb` edge. An implementation must represent the actual accesses in the declared order; a composite contract that leaves their relative order undetermined does not admit the step. The chosen order must also satisfy the authorization, validity, and publication obligations of C27–C29 and C50–C51.

These additional requirements do not by themselves establish the required physical order, which remains subject to `OB-C19`/`OB-C20`. They must be validated against the compositional transition definitions and their possible realizations; they are not assumed consequences of the sequential kernel.

## C29. Pure-Authority Erasure and Concrete-Access Coverage

Two distinct realization obligations are required.

**Pure-authority erasure.** A marker bearing none of `acc`, `sync`, or `validity` is a pure authority marker and is not a source or target of an `sw` edge. Such a marker may be removed from a lower-level graph only when the remaining `po` relation retains the order between its predecessor and successor events in the same context. The required erasure property is that removing all such markers, with the appropriate `po` projection, preserves `hb` between surviving events. This pure-authority erasure rule **never** authorizes removal of required physical memory accesses, controller operations or lifecycle synchronization. Storage-validity events likewise cannot be erased merely as pure-authority markers; their lower-level representation may be abstracted or projected only through a **separate** validity/refinement proof preserving their semantic begin/end boundaries and required ordering. A semantic validity event need not correspond to a distinct machine instruction.

**Concrete-access coverage.** Every actual byte access performed by a step realization must have a corresponding `acc` event with its true byte footprint. This includes unsuccessful acquisitions, rejected calls, retries, CAS failures and metadata accesses that occur before the absence of a successful abstract transition is determined. Every storage-validity change must also have a corresponding semantic validity event, distinct from its possible physical metadata accesses. The proof must relate these footprints to Spec 1 §82, `LayoutWF`, and the actual access-related preconditions. No claim is made that every concrete access requires an ordinary `Modify` authority: `read3` requires `Observe`, `writeShared` may work under `Observe`, and synchronization-library metadata must be justified by its own contract. The obligation is that **each** physical access has the correct kind of authority, atomicity, footprint, and synchronization justification, not that all accesses are ordinary writes.

Neither erasure nor coverage is established by a step-level simulation between the authority machine and the memory machine alone. Their relation to that simulation and to the unresolved physical-access-after-invalidation obligation of Spec 1 §82.7 must be proved separately.

---

# V. Conflicts, Ordering, and Consistency

## C30. Byte-Level Conflicts and Access Pairs

Two `acc` events from different execution contexts **conflict** if their concrete byte ranges intersect and at least one is a write. An RMW counts as both a read and a write for this purpose. Byte-level intersection is the criterion, even when each event corresponds to a larger logical leaf.

An `Atomic(size, align)` event is indivisible over the **entire concrete range of its leaf**; the fact that conflict detection is byte-based does not split that event into independently visible byte writes. The relationship between a leaf, its range of bytes and the concrete layout is governed by C38 and Spec 1 §82.

Two read-only events do not conflict. Conflict is distinct from whether authority preconditions are satisfied, whether the events may overlap in wall-clock time, and whether a sufficient event-order relation exists. This distinction is essential for cross-context handoff (C44–C46).

## C31. Reads-From and Modification Order

The event graph contains:

- `rf` (**reads-from**): a relation from the write event whose value supplies a read component to the corresponding read event. An RMW has a read component and may also be the source of a later `rf` edge. Initial writes or initialized storage must have an explicitly represented source in any concrete litmus or proof requiring a read value.
- `mo` (**modification order**): for each `Atomic` location, a strict total order over **all writes/modifications of that location**, not merely atomic writes. This includes the represented initial/initializing write (including `newMutex` controller initialization) and any exclusive ordinary non-atomic write admitted under C42, as well as subsequent atomic stores and successful RMW modifications. Locations are the indivisible units fixed by C38, not arbitrary overlapping regions. Non-atomic initialization and exclusive writes remain **non-atomic** events; their inclusion in `mo` does not confer atomicity or `sw` on them.

For a successful atomic RMW, its read component obtains the immediately preceding modification of its atomic location in `mo`, under the chosen coherence model; a failed comparison observes a value via a read-only event and contributes no modification to `mo`. The first successful `acquire` must therefore be able to read (`rf`) the initializing `newMutex` write, which is explicitly included in `mo`. An ordinary exclusive write under C42 also occupies its appropriate `mo` position and must be `hb`-ordered as required by the applicable safe-access contract.

A well-formed graph must satisfy explicit typing, source-existence, range-identity, and coherence obligations on `rf` and `mo`. **Specifying `rf` and `mo` alone is insufficient to define a full permitted execution.** The full event model requires the named `EventConsistent` predicate of C34. No unspecified or inconsistent graph may be accepted merely by postulating a convenient `rf` edge.

## C32. Synchronizes-With — `sw`

The following are **reference** sources of synchronization:

1. **Atomic protocol:** a release-capable write/RMW (including a `seq_cst` store or RMW) and an acquire-capable read/RMW (including a `seq_cst` load or RMW) on the same atomic unit may establish `sw` when the acquire reads the release through the applicable `rf` relationship and the relevant memory orders provide release/acquire semantics. **Address identity alone is insufficient.** Release-sequence-mediated synchronization follows the rule of C48.
2. **Context creation:** the parent's `spawn(c)` event `sw`-precedes the child's `start(c)` event, with all prior parent events and subsequent child events related through `po`.
3. **Completion observation:** `complete(c)` of the terminated context `sw`-precedes a successful `join(c)`, with the completing context's preceding events ordered before `complete(c)` and the joining context's subsequent events ordered after `join(c)`.

A pure `release` (O3), `derive`, `endUse`, or other authority marker **does not itself create `sw`**. A bare `spawn` in the abstract interleaving does not order parent operations executed **after** that `spawn` before the child's later operations. A `join(c)` orders only the events of the context whose completion it actually observes, subject to already established transitive edges; it does not implicitly join live descendants or unrelated contexts.

Additional synchronization mechanisms are admissible only under an explicit contract with a proof that their event edges have the claimed semantics.

## C33. Happens-Before and Data Races

Let `hb` denote the strict transitive closure:

\[
  hb=(po\cup sw)^+.
\]

This specification requires the event graph to satisfy the applicable acyclicity and consistency conditions; a cycle of purported `hb` edges cannot be used to justify an otherwise unproved synchronization guarantee.

In the terms of the frozen Spec 1 §18, a **data race** occurs when two events:

1. belong to distinct concurrent execution contexts;
2. conflict on at least one byte;
3. include at least one **non-atomic** event; and
4. are **not ordered by `hb` in either direction**.

The definition applies to physical access events, including accesses emitted by concrete realizations, and is not limited to the abstract operations named `read3`, `write3`, and `writeShared`.

**Spec 1 §18 remains unchanged:** a data race is UB and safe code must not cause one. This specification does not infer data-race freedom solely from a locally enabled authority step, from the sequential interleaving, or from the atomicity of only one member of a mixed access pair.

## C34. Admissible Event Graphs and Reference Memory Models

RC11, including its published `rc11.cat` model, is a **comparative reference**, not an adopted normative definition of ERN.

The **no-thin-air** requirement is:

\[
  NoThinAir_{RC11} := acyclic(po\cup rf).
\]

Admissible ERN event graphs satisfy `acyclic(po ∪ rf)`. This axiom is part of `EventConsistent` on arbitrary finite graph fragments, not merely a bounded test condition. Its compilation cost and correctness on each supported target remain `OB-C22`/`OB-C27` obligations. This axiom is postulated; it is not derived from authority exclusivity. The relationship with RC11 requires explicit comparison; inclusion or equivalence is not presumed.

**Global `seq_cst` consistency, named `SCConsistent` — fence-free adaptation of the RC11 `psc` repair proposed in December 2025.** Let `SC` be the set of `seq_cst` atomic access events (including `seq_cst` RMWs). Let `[SC]` denote the identity relation on this set. In the following definitions, `;` is relational composition, `∪` is relation union, `\` is relation difference, `loc` relates events accessing the same atomic unit, and `id` is event identity. `po`, `rf`, `mo` and `hb` retain their definitions in C31–C33. Define:

- `hb|loc := hb ∩ loc`;
- `rb := (rf⁻¹ ; mo) \ id`, excluding a self-pair on an atomic RMW;
- `scb := po ∪ (po ; hb ; po) ∪ hb|loc ∪ mo ∪ rb`;
- `psc := [SC] ; scb ; [SC]`.

`SCConsistent` holds exactly when `psc` is acyclic. For a finite event graph, this is equivalent to the existence of a strict total order `S` on the `seq_cst` events that extends `psc`. This is a **fence-free adaptation of RC11's `psc` relations using the repair proposed in Ori Lahav's December 2025 corrigendum to *Repairing Sequential Consistency in C/C++11***: that repair replaces `sb|≠loc ; hb ; sb|≠loc` with `(sb \ rmw) ; hb ; (sb \ rmw)`. ERN uses `po` for within-context event order and represents each atomic RMW as one event, unlike the two-event RMW representation of RC11; there is therefore no between-component `rmw` edge to exclude from `po`. ERN v0 does not specify `seq_cst` fence events, so `psc_F` and the fence branches of `psc_base` have no instances. The middle term of ERN `scb` consequently differs from the published `rc11.cat` model. Unlike the C++20/P0668R5 SC wording, this rule does **not** require `S` to extend a transitive coherence-ordered-before relation passing through non-`seq_cst` modifications. LWG 3941 records that such a requirement inadvertently excludes behaviors allowed by standard x86 mappings when `release` and `seq_cst` are mixed.

In particular, an `SC` read directly observing an `SC` modification follows that modification in `S` through `hb|loc`; an `SC` read of a modification `w` precedes every `SC` modification later than `w` in `mo` through `rb`. These are consequences of `psc`, **not additional independent constraints**. `S` is not a runtime instruction order and must not be inferred from the order of abstract transitions. `SCConsistent` is a conjunct of `EventConsistent`, defined below. The ERN release-sequence rule in C48 is the C++20 form and differs from the published `rc11.cat` reference; the middle term of `scb` also differs, as specified above. Inclusion of executions consistent with the **published** `rc11.cat` model is **not** an expected comparison property. On the common fence-free atomic fragment, the comparison hypothesis instead concerns RC11 with the **December 2025 proposed `psc` repair**: inclusion of that amended model's consistent executions among ERN-admissible executions remains to be proved, and no equivalence is assumed (`OB-C23`, `OB-C26`). The feasibility and refinement obligations remain under `OB-C01`, `OB-C22`, `OB-C23`, `OB-C26`, and `OB-C27`.

**Pure-authority erasure invariance (verification target, not an axiom).** For every event graph `G` satisfying the erasure premises below, let `erasePure(G)` remove all pure-authority markers identified in C29, project `po` as required there, and restrict the other event relations to surviving events. Each erased marker carries none of `acc`, `sync`, or `validity` (C27) and is neither a source nor a target of any `rf`, `mo`, or `sw` edge (C29, C31–C32); thus no required physical memory access or validity event is erased. The absence of `rf`/`mo` incidence states the atomic-access typing of those relations, rather than a new event-admissibility axiom. Under these explicit premises, the required property is `EventConsistent(G) ↔ EventConsistent(erasePure(G))`; verification must establish the equivalence separately for each of the seven conjuncts of `EventConsistent`, not merely for `hb` or `SCConsistent`. This property must be **proved**, not postulated as an additional event-graph admissibility condition or an eighth conjunct of `EventConsistent` (`OB-C26`). It complements the separate `hb`-preservation obligation of C29 (`OB-C19`) and does not expand the classes of events erasable under C29.

**`EventConsistent`.** An event graph is `EventConsistent` exactly when all of the following hold:

1. **`rf` well-formedness:** `rf` relates only a modification of an atomic unit to a read component of an access to that same unit; every read component of an access to an atomic unit has exactly one `rf` source, and the value read is the value that source wrote (C31);
2. **`mo` totality:** `mo` relates only two modifications of the same atomic unit; on each atomic unit, it is a strict total order of all the modifications of that unit, the represented initial write included (C31);
3. **RMW atomicity:** the `rf` source of a successful atomic RMW is its immediate `mo`-predecessor (C31);
4. **coherence:** `hb ; eco?` is irreflexive, where `eco := (rf ∪ mo ∪ rb)⁺` and `eco?` is the reflexive closure of `eco`;
5. **`hb` irreflexivity** (C33);
6. **`NoThinAir_RC11`**;
7. **`SCConsistent`**.

Legality of memory-order annotations (C40) is a typing condition on events, separate from these conjuncts.

---

# VI. Shared-Mutation Disciplines and Atomics

## C35. Companion Shared-Mutation Contract — `SharedDiscipline`

`K.SharedMutable` retains **exactly** its frozen Spec 1 meaning: storage must be declared by its type and obey its applicable shared-mutation discipline. The concurrent contract `K_C.SharedDiscipline` is a **companion contract**, not a redefinition of `K.SharedMutable` or an ambient authority source.

For each applicable `SharedMutable` leaf, the companion contract selects one of the following disciplines:

| Discipline | Access behavior and safety contract |
|---|---|
| `Atomic(size, align)` | The leaf is one indivisible atomic unit with a supported size and alignment. Atomic reads/writes/RMW obey its selected memory-order model; ordinary accesses remain non-atomic and require C42 in safe traces. |
| `Synchronized` | Shared mutation may use non-atomic events under an explicit mechanism guaranteeing sufficient `hb` ordering for every conflicting pair that does not fall under exclusive handoff. |
| `Confined` | At most one context has **any attributable capability** on the leaf in a given abstract state. The context may change, but the relevant transfers must satisfy `HandoffOrdered` rather than relying on exclusivity alone. |

The companion contract need not classify every `K.SharedMutable` leaf merely to be well-formed. However, concurrent evaluation of `writeShared` over a nonempty region is `reject` if any targeted leaf lacks a selected `K_C.SharedDiscipline` class, even when a composite contract would otherwise admit the region. Selecting a class is a step-legality condition; establishing the class's cross-context synchronization and confinement obligations is a separate safe-trace obligation under C51, not an additional state-local precondition. These rules restrict the concurrent safe interface and do not change the frozen O11 transition.

A discipline is an obligation of the **safe storage/interface contract**, not an extra way to derive authorities. On a `Confined` leaf, simultaneous `Observe` capabilities in two contexts are forbidden by that safe contract even though compatible observations are permitted in the ordinary kernel.

The safety restriction of a concurrent `writeShared` is evaluated under the additional `K_C.SharedDiscipline` contract defined here; it does **not** interpret the word “applies” in frozen O11.3 as a new or stronger Spec 1 precondition. Each concurrency-`ok` inherited operation must separately satisfy the unchanged Spec 1 O11 under the corresponding projection of `K_C` to `K`. The directional conservativity implication (concurrency-`ok` implies Spec 1 `ok`) is an explicit proof obligation `OB-C21`, not a claimed equivalence of admissible sets.

## C36. Classification of Inherited Accesses

Every `read3` (O9) and `write3` (O10) event is **non-atomic**, including on a leaf classified `Atomic`, `Synchronized`, or `Confined`. This classification **does not modify** the kernel preconditions, `ok` effects, or `reject` outcomes of O9/O10.

The inherited `writeShared` (O11) is **not universally atomic**. Its event classification follows the satisfied `SharedDiscipline` of the targeted storage:

- `Atomic`: one indivisible atomic write of a single compatible leaf, under C38–C40;
- `Synchronized`: non-atomic write event(s), protected by the declared synchronization contract;
- `Confined`: non-atomic write event(s), with context exclusivity and ordered handoff when context ownership changes.

A type's permission to use a shared-mutation operation does not establish that a particular pair of accesses is free from races. Physical access events emitted by other kernel or library operations must be classified by their actual realization and justified by C29 and C50.

## C37. Concurrent Atomic Read — `readShared`

`readShared(access, leaf, order)` is a **new concurrent transition**, not a modification of O9. It reads an atomic leaf via an active authority whose effective and exercisable mode permits at least `Observe` on that leaf.

**Preconditions**

1. The leaf belongs to a usable place, is initialized in the sense required for its typed read, and its required origin, validity, provenance and dependency conditions are satisfied.
2. The authority is active and exercisable in at least `Observe` on the leaf, with a present effective mode; an authority identity alone is insufficient.
3. The storage is declared `K.SharedMutable`, and its companion `SharedDiscipline` is `Atomic(size, align)` for this **single leaf**; its concrete representation meets C38.
4. `order` is permitted for an atomic read by C40.

**`ok` effect:** return an observed value of the initialized atomic leaf without changing the authority, ownership, or initialization structure of the abstract machine. The **transition's state-local preconditions do not require an `rf` source**. Instead, the resulting event graph must satisfy `EventConsistent` (C31–C34), including the existence and validity of the `rf` source for that observation. An unsupported value or inconsistent `rf` makes the **execution graph inadmissible**, not the abstract operation's authority precondition false.

**Other outcome:** `reject` if a precondition or the read's declared storage discipline is not satisfied. In particular, `readShared` on `Synchronized` or `Confined` storage is `reject` under **this operation's own rule**, not by applying O11.3 (which belongs to `writeShared`). It has no resource `fail` outcome. A completed atomic read and a temporary absence of an execution with a consistent observation are not conflated.

For `Synchronized` or `Confined`, the existing ordinary reading primitive is `read3`, subject to its frozen conditions and the corresponding safe-trace discipline.

## C38. Atomic Units, Concrete Layouts, and Multi-Leaf Writes

One `Atomic(size, align)` unit is **one logical leaf** whose entire byte range is a single physically supported atomic unit. The byte range may contain multiple bytes; an atomic 64-bit leaf occupying eight bytes is one event, not eight separately observable writes. The size must be supported for atomic operations on the target, and alignment and representation must satisfy `LayoutWF` and the applicable Spec 1 §82 obligations. Atomic event indivisibility and byte-range conflict testing are different properties.

An inherited `writeShared` whose region contains **more than one `Atomic` leaf** is **`reject` under the concurrent `K_C.SharedDiscipline` safe interface** (without changing any O11 kernel precondition): a multi-leaf region does not satisfy the indivisible-one-leaf `Atomic` discipline. It is not silently lowered into a sequence of independent atomics and is not a multiword transaction.

A region that combines incompatible `SharedDiscipline` classes is not automatically one legal `writeShared` step. It requires a separately established composite contract; absent such a contract, the region is `reject` as not satisfying a single applicable discipline. Such a contract may admit at most one `Atomic` leaf, subject to the unconditional multiple-`Atomic` rejection above. It determines which mixed-class regions are admitted and their required within-step event order (C28), but does not override memory-order legality or create multi-leaf atomicity. Multi-leaf regions classified consistently `Synchronized` or `Confined` remain eligible under O11 and their respective contracts, subject to all existing O11 preconditions. Only the `store` kind is permitted for a multi-leaf region, or for any region not consisting of exactly one `Atomic` leaf (C39).

The empty region is distinct from a nonempty region containing a zero-physical-size leaf. The latter still has a logical leaf, whose initialization and selected discipline apply. An `Atomic(size, align)` leaf with zero physical size cannot satisfy the supported atomic-unit requirement; `readShared` or concurrent `writeShared` targeting that leaf is `reject`. A zero-physical-size `Synchronized` or `Confined` leaf may be targeted by a legal `store` without a byte access, subject to the ordinary authority, dependency and discipline obligations; any actual auxiliary physical accesses must still be represented under C27–C29.

No atomicity guarantee follows from word alignment alone or from merely declaring `K.SharedMutable`. A target that cannot realize the requested indivisible unit must reject the unsupported atomic contract or decline to expose it in a safe interface; it may not silently substitute a racy multi-step emulation.

## C39. Atomic Shared Writes and RMWs

The concurrent evaluation of inherited `writeShared` on an `Atomic` leaf carries a memory-order annotation and produces **one indivisible atomic modification event**: a write, or an RMW when the declared atomic operation conditionally reads and modifies the same initialized leaf. The annotation and event kind refine the **concurrency contract and realization** of `writeShared`; they do not change the frozen O11 signature in `S₃`, its rights, its validity conditions, or its effect on initialization. If the atomic discipline, region, order, or realization requirements fail, the operation retains the existing O11 `reject` outcome.

**Operation kind and atomic memory-order annotations.** For concurrent `writeShared`, the operation kind is `store` (a write without a read component) or `RMW` (an atomic read-modify-write of its target). A step of kind `RMW` is permitted only when its region consists of exactly one `Atomic` leaf and carries an explicit memory-order annotation permitted by the atomic RMW row of C40; absence of that annotation or an illegal order is `reject`. Any other region, including an empty region, a multi-leaf region, or a non-`Atomic` single leaf, is `reject` for `RMW`. No composite RMW read of other leaves is implied. Higher-level read-modify-write behavior involving multiple leaves must be expressed through separately justified operations; the frozen O11 gains neither an implicit read result nor a multi-leaf atomic transaction.

For a nonempty `writeShared` of kind `store`, exactly one `Atomic` leaf requires an atomic memory-order annotation, whether it is the entire region or part of a mixed-class composite. That annotation applies **only** to the atomic event on that leaf and must be permitted for a `store` by C40. With no `Atomic` leaf, the annotation must be absent. A missing required annotation, a supplied annotation where none applies, or an order illegal for the event kind is `reject`. A composite contract (C38) cannot override these rules, impose a global atomic order on the region, or admit more than one `Atomic` leaf.

**Empty region.** A `writeShared` of kind `store` on an empty region without a memory-order annotation has an `ok` outcome with no leaf effect when all still-applicable frozen O11 preconditions hold, including the existence and exercisability of the access authority and the validity of required dependencies. An annotation or `RMW` kind makes this concurrent step `reject`. The successful empty-region step emits no `acc` event and no `mo` modification solely from that logical write; it may emit a pure authority marker. Any actual auxiliary physical accesses of its realization remain subject to C27–C29 and the safe-execution rules. Empty-region behavior does not imply that a nonempty zero-physical-size leaf is absent.

**The kernel mutation underlying a successful atomic RMW is `writeShared` (O11), not a new mutation primitive.** A successful compare-and-exchange (CAS) on an initialized `Atomic` leaf is a `writeShared` mutation realized as one indivisible RMW event whose read component determines the conditional success and whose write component participates in `mo` (C31). **A failed CAS is a `readShared` (C37) observation**, represented by a non-modifying atomic read event: it neither invokes a successful O11 mutation nor creates an acquisition grant. A failed physical CAS attempt must still be recorded as a read in the realization's event graph. The comparison, chosen observed value, success/failure branch, and legal success/failure orders are constrained by `EventConsistent`, not by adding a state-local `rf` precondition to O11 or C37.

No general public CAS/RMW interface is specified by the frozen Spec 1. Specs 3/4 may expose a safe conditional atomic operation **implemented through the `writeShared`-on-success / `readShared`-on-failure contract above**; this does not permit any other kernel mutation under `Observe`. The reference mutex uses this contract internally under `OB-C05`.

**Authority-machine operation coverage.** `readShared`, the success path of an atomic `writeShared` RMW (including CAS) and the failed-CAS `readShared` observation are distinct concurrent step cases of the authority machine. A successful atomic mutation remains an O11 mutation; no extra frozen Spec 1 operation is introduced. Preservation and handoff properties must hold for the case set that includes them (`OB-C03`, `OB-C17`, `OB-C18`, `OB-C20`).

## C40. Memory Orders and Operation Legality

The order set is:

```
{ relaxed, release, acquire, acq_rel, seq_cst }
```

`consume` is not included. **Per-operation legality:**

| Operation | Permitted order annotations |
|---|---|
| `readShared` atomic load | `relaxed`, `acquire`, `seq_cst` |
| atomic `writeShared` store | `relaxed`, `release`, `seq_cst` |
| atomic RMW | `relaxed`, `acquire`, `release`, `acq_rel`, `seq_cst` |
| CAS success (modifying RMW) | `relaxed`, `acquire`, `release`, `acq_rel`, `seq_cst` |
| CAS failure (read-only) | `relaxed`, `acquire`, `seq_cst` |

A source-level order outside its row is a **static `reject`** under the concurrency contract. A CAS may choose its success and failure orders independently: no strength relation between them is imposed. `release` and `acq_rel` are forbidden only as failure orders, since failure does not modify storage. A failed CAS contributes an atomic read event and the `failure` order, not a successful modification in `mo`. This means the invalid operation is not admitted into a safe execution; it does not redefine how the sequential O9–O11 primitives behave absent concurrency.

`relaxed` requires atomicity/coherence but does not, by itself, establish cross-location release/acquire synchronization. `release` and `acquire` contribute to `sw` only when the requisite event relation is established. `acq_rel` combines the two roles on a suitable RMW. **`seq_cst` has release semantics for stores, acquire semantics for loads, and both for RMWs**, as applicable. Its admission also requires the explicit global `SCConsistent` conditions on the total order `S` in C34. These normative conditions give rise to verification and compilation obligations under `OB-C23`/`OB-C27`.

Memory-order annotations alone do not solve out-of-thin-air behavior. C34 requires `acyclic(po ∪ rf)`; target compilation feasibility remains an external obligation.

## C41. Atomic Protocol Obligations and Failure Paths

A sound atomic implementation must demonstrate correspondence between source-level atomic events and target atomic instructions, including atomicity of the entire unit, correct `rf`/`mo` observations and ordering appropriate to the annotated operation. It must not replace an indivisible operation by an unproved bytewise sequence.

A retrying protocol may have physical reads and failed RMW attempts that do not create successful abstract authority grants; they remain represented in the physical event graph. Its implementation must establish a valid **linearization point** for the successful abstract acquisition, and it must not expose a partially completed logical grant or inconsistent controller state if authority derivation fails.

The reference `unlock` and `resetLock` must prove their own controller-update correspondence. Their logical atomicity in C17/C18 does **not** establish physical release semantics. Failure to discharge a realization obligation means the corresponding protocol is not yet justified as safe, not that an additional unchecked primitive is implicitly available.

## C42. Exclusive Ordinary Access to Atomic Storage

For a `SafeConcurrentTrace`, an ordinary `read3` or `write3` on an `Atomic` leaf requires an **effective and exercisable `Modify`** capability for that leaf, even though O9 in the frozen kernel permits an ordinary read with `Observe`.

This is a rule of the **safe concurrent interface**, not a new O9/O10 kernel precondition. The kernel may admit an ordinary read under `Observe`; the safe concurrent trace does not expose such a read to a user while the atomic storage is shared. A compatible `Observe` authority may still be used for the atomic `readShared` that is specifically permitted by C37.

Under the applicable structural authority invariants, `Modify` effective exercise precludes simultaneous incompatible effective exercise by another context on the same leaf. That establishes logical exclusivity **at an abstract state only**. If the exclusive ordinary access is followed or preceded by a conflicting access from another context, the event-order obligation of C46 still applies. This is the general rule of which the controller-specific restriction C22.4 is an instance; O9 and O10 remain unchanged.

---

# VII. Inter-Context Authority Handoff

## C43. Context Capability and Current-Frame Exercise

For the L1/L2 capacity-period definition, for state `s`, execution context `c`, and logical leaf `l`:

```
cap(s, c, l) ∈ { none, Observe, Modify }
```

For the safe-handoff proof, it is the greatest **effective** mode on `l` attributable to `c` through active authorities held by its live frames, **including suspended frames**, or held in a place through a valid holder chain, **provided the attributing chain does not pass through the `guarded` authority of any live synchronization entry**. This guarded-chain-excluding capability permits valid frame-held grants and their legally held descendants but excludes attribution through live `guarded` authorities. It does not change the rights of any authority in the frozen Spec 1.

`cap` is **not** `ExercisableAt`. The latter applies the frozen §43 rules to the executing context's **current frame** and is used to decide **kernel** operation preconditions; C22.6 separately restricts which successful kernel operations the **safe interface** may expose. `cap` summarizes guarded-chain-excluding contextual entitlement across the context's frames and relevant held places, including rights not currently exercisable from the top frame. Derivation, reborrowing and frame changes need not terminate a context's `cap` merely because an individual authority becomes inactive or non-exercisable. Unrestricted contextual capability is distinct from this guarded-chain-excluding `cap` and is not the quantity used by L1/L2.

For two distinct contexts, present `cap` values on a leaf are **incompatible** when at least one is `Modify`; for `Confined`, any two present capabilities are incompatible under the additional safe-storage contract. This is a contextual abstraction for L1/L2, not a new sequential mode or authority identity.

## C44. Scope of Exclusive Handoff Ordering

Let `e1` and `e2` be access events in **different contexts**, associated with the same logical leaf and conflicting byte ranges, where at least one is non-atomic. `HandoffOrdered` applies only if the pair is **exclusive**: its relevant context capabilities are incompatible under C43 and the declared storage discipline. It does not impose `hb` between two genuinely concurrent atomic accesses under compatible observation rights.

Typical cases in scope are:

1. accesses to ordinary non-`SharedMutable` storage, when a conflict necessarily includes an exclusive ordinary `write3`;
2. a mixed atomic/non-atomic pair on `Atomic` storage, because C42 requires exclusive `Modify` for the ordinary member;
3. conflicting accesses under `Confined`, because the safe-storage contract excludes simultaneous cross-context capacities;
4. exclusive ordinary access pairs under `Synchronized`.

Conflicting **non-atomic** `writeShared` operations on `Synchronized` storage performed under shared compatible `Observe` rights are **not** covered by the exclusive-handoff premise. Their ordering is established by the particular `Synchronized` protocol, not by claiming that the shared rights are exclusive.

The scope is deliberately narrower than the class of all conflicts, and wider than just final restitution of a spawn parameter. It includes a capacity becoming available to a child **after** its `spawn`, and multi-context relays.

## C45. Loss Marker, L1 and L2 — Loss-Marker Obligations

**Scope clarification:** the loss-marker rule continues to govern accesses justified by a pre-existing capacity. A semantic begin/end-validity event does not become an `acc` or a loss marker solely by that label. Its order is handled by C27–C29 and C51. This clarification does not weaken the existing requirement to place the physical access before the marker that revokes its justifying capacity.

For a pair in the scope of C44, write `e1` for the earlier access in the abstract trace, issued by `c′`, and `e2` for the subsequent conflicting access by `c ≠ c′`. Let `r(e1,e2,l)` be the **loss marker** that ends the period containing `e1` during which `cap(·,c′,l)` is incompatible with the capability used by `e2`.

This marker may denote a release, a parameter yield, a derivation that reduces the relevant effective mode, frame exit, termination, unlock, or a justified holder/ownership change. It is a **pure logical marker** if its effect is only an authority change; a concrete step can additionally emit physical memory or synchronization events. The required loss threshold depends on the later access: a later exclusive write requires no incompatible surviving capability in `c′`; a later shared `Observe` read may be permitted after `c′` has lost its `Modify` exclusivity while retaining compatible `Observe`.

**L1 — local loss.** On an `EncapsulatedTrace` (C51), a strict reduction of `cap(·,c′,l)` occurs only at a step of `c′` itself. The loss marker `r(e1,e2,l)` is therefore an event of `c′`, and the required order is `po(e1, r(e1,e2,l))`, including when the access and the loss belong to the same compound step (C28).

**L2 — incompatibility and existence of the marker.** On an `EncapsulatedTrace`, no state gives two distinct contexts incompatible `cap` values on the same leaf under the `Modify` criterion of C43; for `Confined` storage, that no state gives two distinct contexts a present capability on the same leaf is a premise of the safe-storage contract (C35; C51, item 2(c)). L2 also requires that, for every pair in the scope of C44, a step of `c′` that reduces `cap(·,c′,l)` below incompatibility with the capability used by `e2` lies at or after the step emitting `e1` and before the step emitting `e2` in the abstract trace; that step carries the loss marker.

L1 and L2 are obligations on the authority machine and on its event mapping, for the guarded-chain-excluding `cap` of C43. They concern the existence of the marker and its `po` position. They do not establish `hb(r,e2)`, which is the separate requirement of C46, and they do not by themselves place the marker among the physical events of a realized compound step (`OB-C19`, `OB-C20`).

## C46. HandoffOrdered

**Scope clarification:** `HandoffOrdered` continues to apply only to its original exclusive access-pair domain; `LifetimeOrdered` is a separate safe-execution obligation. Let `i` and `j` be the positions in the abstract trace of the steps that emit `e1` and `e2`. A step position `r` with `i ≤ r < j` at which the capability of the earlier context is reduced — possibly the step of `e1` itself, or a step that creates authority — is not, by itself, the physical loss-marker order of L1 and L2. The case `r = i` is not exempt from any applicable `hb` requirement.

For a pair within C44's scope, let `r(e1,e2,l)` denote the loss marker identified by the scoped capacity-period definition in C45. The **sole ordering requirement of `HandoffOrdered`** is:

\[
  HandoffOrdered(e1,e2,l) \;:\!\iff\; hb(r(e1,e2,l),e2).
\]

If the authority machine or concrete realization fails to provide a marker for a relevant pair, that is an unfulfilled proof obligation or counterexample, not permission to assume a hidden marker. The existence of **some** unrelated `sw` event is insufficient. When the event-model mapping has also established `po(e1,r)`, the protocol requirement `hb(r,e2)` implies `hb(e1,e2)` by transitivity. The `HandoffOrdered` rule specifies the ordering each admissible handoff protocol must justify, not a claim that an authority-only trace establishes physical `hb`.

The requirement applies to both **transmission** and **restitution** of authority. A bare inherited O3 `release` may restore an origin's effective right in the globally coherent abstract state, but it generates **no** `sw` by itself. The resulting trace can be kernel-`ok` and nevertheless be excluded from `SafeConcurrentTrace` if a later cross-context access lacks the required order.

`join` is one reference protocol, not the only legal completion/handoff mechanism (C8). Other mechanisms may be added if they prove the requisite `hb` relation without introducing a new ambient authority source or weakening inherited invariants. Safe-language constructs that ensure these obligations belong to Specs 3/4.

---

# VIII. Event Realization of Reference Protocols

## C47. Spawn, Completion, and Join Events

For the reference by-reference `spawn` protocol, the creator's authority-yield **loss marker** precedes its `spawn` synchronization event within the parent context; the latter `sw`-precedes the child's `start(c)` marker. The initial child frame and parameter holder changes still obey C4/C5, and neither the event protocol nor `start(c)` duplicates an authority. A parent's operation executed after `spawn` is not ordered before a child's operation merely because the parent was the creator.

For `terminate`, every earlier event of the terminating context is `po`-before `complete(c)`; a successful `join(c)` in another context is the target of `sw` from that `complete(c)` event. The `join` event is placed in the caller's `po` before subsequent operations. By transitivity, a context's accesses preceding its completion are `hb`-before the caller's accesses following its successful join. An unsuccessful or non-enabled `join` contributes no such completed-observation edge.

The reference safe passing discipline may delay a creator's re-use of transferred exclusive capacity until appropriate completion observation, but C8 does **not** impose this restriction on all possible kernel traces or require universal structured concurrency. For a chain of delegated authorities, a successful join of an intermediate context does not imply completion of a surviving descendant. Correct reference reuse may require **transitive** joining or an equivalent ordering protocol.

For by-value `spawn`, access events emitted by the transfers belong to the actual producing context/phase, and their order must preserve the required construction/transfer/yield causal constraints of C5 and the Spec 3 protocol. For each fresh destination populated by a physical construction write `w`, every subsequent access `a` to that destination from another execution context must satisfy `hb(w,a)`. This is stronger than merely ordering `a` after its begin-validity event. The creator-to-child `spawn`/`start(c)` edge may discharge this when `w` precedes publication and `a` is in the child or an `hb`-ordered descendant; for an unrelated context a separate ordering proof is required. For the C5 reference transition, the phase order is fixed by C5. For any alternative protocol, the Spec 3 contract under C5 and `OB-C09` must establish the same authority and construction-publication guarantees. Whether those byte accesses are correctly ordered with all other physical uses is part of the separate realization and safe-execution proofs, not a consequence of the logical transfer alone.

## C48. Reference Mutex: Acquire, Unlock, and Grant Events

The reference `newMutex` initializes a physical controller in a state corresponding to `grant = none` and must establish the positional, identity and initialization requirements of C12–C13, C21 and Spec 1 §56. As clarified in C13, this is a physical non-atomic write of the controller synchronization value to an **already abstractly `Init`** leaf, not the abstract initialization of an `Uninit` structural leaf. C13.11 requires ordinary `Modify` authority, with applicable O10.1/O10.2 conditions. Its concrete metadata operations have events as required by C27/C29.

A successful `acquire` has an atomic controller-acquisition event, for example a successful CAS/RMW with an acquire-capable memory order. This event must observe (`rf`) the appropriate released/available controller state, satisfy atomic coherence, and linearize the reservation of the controller before the new grant is made externally exercisable. A **gain marker** is placed `po`-after the successful acquire event. A failed CAS does not grant authority; a busy controller and an invalid request remain classified under C16, with `reject` taking priority per abstract state.

An `unlock` has a logical **loss marker** for the released grant, followed in `po` by a corresponding atomic release publication of the controller's available state. The abstract library transition remains coherent and does not expose an intermediate invalid grant/controller pairing. When a later acquiring RMW **directly reads** this release modification (`rf`), the protocol yields the requisite `sw` and thus `hb` from the preceding protected critical section to the succeeding one.

The event-level atomicity of this logical transition, the absence of an observable partial state, `SyncInv`/`GrantDiscipline` preservation and the correspondence to the concrete controller are still obligations of `OB-C05` and C25.

A successful `resetLock` must have a linearization point at which **all** applicable C18 preconditions hold, and it must not overwrite a successful acquisition already linearized. The reference successful recovery publishes the controller's available state by an atomic **`release` store**, not a `relaxed` store. A later acquire-capable read/RMW which obtains its value from this release publication (directly or by the chosen release-sequence rule) acquires a justified `sw` edge from recovery. No such edge is inferred merely from mutex identity. Recovery publication does **not** by itself carry accesses of the former abandoned holder: any required earlier-completion observation, `HandoffOrdered` and `LifetimeOrdered` remain independent safe-trace obligations.

The simple reference protocol, which writes the controller without reading, is valid only in an environment proven to preclude every competing action that could invalidate C18 between its authorization check and publication (including already pending physical operations). Two potentially sufficient operating situations are an inactive recorded grant with no live competing controller update, and an available mutex with no other context capable of taking it. Their sufficiency and register/controller coherence must be established in `OB-C05`; these are **implementation-side preconditions, not new C18 abstract preconditions**. An enriched controller protocol with auxiliary state may realize broader attempts and clean failure, if it proves the same linearization and rights conditions. C48 specifies the required event behavior; it does **not** claim these obligations have been discharged.

The **C++20 release-sequence rule** applies: beginning with release modification `h` of a given atomic unit, the release sequence consists of `h` followed by the maximal contiguous `mo` segment of atomic RMW modifications on that unit. Ordinary atomic stores, including same-thread non-RMW stores, do **not** extend the sequence. An acquire-capable read/RMW which reads via `rf` from any member of this sequence synchronizes with the head release `h`. This is an axiom of the event graph.

## C49. LockOrder, Recovery, and Delegation

**`LockOrder`** is the obligation that the protected accesses in an earlier critical section of one mutex are `hb`-before conflicting protected accesses in a later critical section whose lock-acquisition event receives the preceding release. The proof must use the concrete `rf`, `mo`, `sw`, `po`, and grant-lifecycle relations, not merely the total order of abstract `SyncEntry` updates or the fact that controller identities match.

For a successful `resetLock`, the library must prove exclusive recovery authority under C18, a coherent physical controller update, and the event-order consequences of any protected memory that becomes newly accessible. Recovery is **not automatically** a substitute for an acquire/release edge missing from an abandoned grant. A recovery protocol that cannot establish necessary ordering is not justified for safe concurrent access. Under the C48 protocol a successful `resetLock` publishes with `release`; when a subsequent `acquire` actually reads that publication or a member of its release sequence, `rf` and the selected memory orders establish `sw(resetLock, acquire)`, contributing to `LockOrder`. This is not an identity-only edge and does not restore missing `hb` from the abandoned prior holder. A safe recovering context must separately establish any necessary ordering with that holder. C18 imposes no precondition on the recorded grant state when `resetLock(e)` executes: the recorded grant may be `none`. Any `sw` from the `release` recovery publication must be justified by actual `rf` and the chosen memory orders.

When a grant is reborrowed, passed to another frame, or transmitted between contexts, the reference implementation must show how ordinary authority rules, grant constraints, and the relevant handoff protocol preserve `hb` across the whole path. Exiting a frame that released a grant without `unlock` does not imply controller release, and a logically returned capability does not imply a physical publication.

**Any abstraction of the C48 mutex `sw` edge must respect interventions on the controller between the release and the acquisition, in particular an intervening `resetLock` of the entry, and `ControlOf(entry)` becoming undefined or designating another leaf. The definitive physical rule remains the unchanged direct-`rf` condition on the same atomic unit in C32/C48.**

## C50. Realization, Visibility, and Physical Correspondence

The implementation must relate every relevant successful `S_C` operation and its associated event graph to a concrete memory execution under the frozen Spec 1 §82 representation obligations. For `Atomic` storage this includes unit indivisibility, alignment, coherent `rf`/`mo`, and the compilation of its memory orders. For ordinary, `Synchronized`, and `Confined` storage it includes byte-level access coverage, validity, exclusivity and the required event ordering.

This obligation is **stronger** than establishing a sequence of abstract `ok` outcomes. It includes preservation of actual initialized bytes, pointer provenance, invalidation conditions, owners and holders, and physically executable synchronization operations. In particular, no successful abstraction proof may conceal an unmodeled physical access after invalidation (§82.7 / `OB-C12`).

Claims about compilation to x86-TSO, ARM, or POWER, including the potential cost of the no-thin-air axiom, must be supported by a target-specific compilation or refinement argument.

---

# IX. Safe Executions and Data-Race Freedom

## C51. EncapsulatedTrace and SafeConcurrentTrace

Two **distinct** restrictions apply to completed traces:

1. `EncapsulatedTrace`: the safe **reference-mutex** trace contract of C22, including the restriction against ordinary `read3(ControlOf(entry))` and the C22.6 restriction on all right-justification holder chains traversing a live `guarded` (subject to the specific C18.1 `resetLock` exception). This restricts the **public safe interface**, not O9/O10 or any inherited kernel operation. A kernel-`ok` `read3(lock)` or a kernel-`ok` access through live `guarded` without the required grant can be outside this contract without being a counterexample to Spec 1. Safe-interface enforcement remains an external obligation under `OB-C28`.
2. `SafeConcurrentTrace`: a subset of `EncapsulatedTrace` in which (a) all relevant event-graph consistency conditions hold; (b) `Atomic` accesses obey C37–C42; (c) `Confined` has at most one context with a present **guarded-chain-excluding** capability in each state and any later cross-context conflict satisfies C46; (d) every non-atomic conflict under a `Synchronized` contract is either protected by a proven exclusive handoff or ordered by an established synchronization mechanism; (e) every concurrent `writeShared` step, including an inherited O11 step accepted by the sequential kernel, satisfies the applicable concurrent `K_C.SharedDiscipline` region, kind, annotation and composite-contract legality rules of C35–C40; and (f) all applicable `HandoffOrdered`, `LifetimeOrdered`, lifecycle, and `LockOrder` obligations are fulfilled. Its safe-interface premise includes all of C22.6; physical access coverage and enforcement remain distinct realization obligations.

`SafeConcurrentTrace` is a **semantic safe-execution contract**. It is not the set of all kernel-`ok` traces. The safe interface excludes ordinary controller accesses prohibited by C22/C42, while inherited kernel operations remain defined by Spec 1.

The statement “a safe, well-typed ERN program generates only `SafeConcurrentTrace` executions” is a **separate soundness obligation** of Specs 3/4 (and the relevant safe libraries), not a theorem derived merely from a name or by construction of this predicate.

**`LifetimeOrdered`.** Each access `a` to physical storage with logical identity `x` must be ordered after `beginValidity(x)` and before `endValidity(x)` when those events exist. Within one context the required order is `po` or a declared within-step order; across contexts it is `hb`. A construction write of a fresh destination must precede any access to that destination in another context as C47 requires; begin-validity alone does not publish its bytes. If bytes are reused for a distinct logical storage identity, the prior identity's relevant accesses and end-validity must be ordered before new accesses through the required lifetime order and the target's allocator/stack correspondence (C50). These are safe-execution requirements, not new preconditions of the inherited `free`, `endUse`, `exitFrame` or `terminate` transitions. There is no implicit wait in C6; an unsafe unjoined use simply does not satisfy `SafeConcurrentTrace`. A safe language abstraction may enforce these constraints by joining, synchronizing or proving a stronger order, with cross-context descendants and transferred authorities accounted for.

**External soundness boundary:** Specs 3 and 4 and safe libraries must prove that every program accepted as safe generates only executions satisfying the complete `HandoffOrdered` and `LifetimeOrdered` conditions, as well as encapsulation. A scoped join abstraction is an existence example, not a universal soundness proof (`OB-C24`).

## C52. Conditional Data-Race-Freedom Theorem

**Conditional composition theorem.** The theorem is not a claim that every kernel-`ok` or well-typed program is already known to satisfy `SafeConcurrentTrace`; its premises include the relevant physical-byte and validity-event correspondence. Every execution graph satisfying the stated `EventConsistent` obligations and arising from a `SafeConcurrentTrace` is free from data races as defined in C33 and frozen Spec 1 §18.

For conflicting non-atomic accesses on `Synchronized` storage under shared compatible observation, the required `hb` order is a premise of `SafeConcurrentTrace` (C51, item 2(d)), not a consequence of this theorem: each declared synchronization mechanism must establish its actual `sw` and `hb` edges (C32, C44). Assuming `HandoffOrdered` establishes only a conditional composition result; it does not establish that all safe programs satisfy the premise or that physical events are correctly represented.

A reference-mutex theorem may conclude DRF for protected ordinary accesses only after the concrete controller protocol supplies `LockOrder` and the requisite `rf`/`sw` links. A `.cat` model that simply discards racy graphs does not prove that safe ERN programs could not generate such graphs before that filter.

## C53. Proof Boundary and Conservativity

The following verification and realization obligations remain separate:

1. **Inherited-operation conservativity:** the unchanged Spec 1 O1–O16 must retain their projected kernel meaning. For `K_C.SharedDiscipline`, the inherited-write projection must be established: every concurrency-`ok` inherited write projects to a Spec 1 `ok` under its valid `K`, with equality of relevant admissible sets only under explicitly established matching/accept-all discipline assumptions. No equality is asserted without proof.
2. **Authority lemmas:** L1, L2, and any preservation properties required by the chosen definition of `cap` and holder attribution.
3. **Graph and realization lemmas:** pure-authority erasure, coverage of physical accesses, full `EventConsistent` coherence for any number of atomic units, **target** correctness of the direct-`rf` controller protocol, and reconstruction/preservation under Spec 1 §82.
4. **Program/interface soundness:** safe interfaces exclude kernel-admissible operations outside C22/C42; the typing and library rules of Specs 3/4 prove that safe programs yield `SafeConcurrentTrace`.
5. **Memory-model verification and realization:** the no-thin-air, release-sequence and global `seq_cst` rules, their cross-target compilation, and the proven relationship (inclusion or equivalence, if appropriate) of the ERN model to any reference model.

No equivalence to RC11 is implied by similar names or successful litmus tests. No clause of the frozen Charter or Spec 1 v0.1 is amended by this specification.

---

# External Contracts and Proof Boundaries

The following are **requirements on dependent specifications or realizations**, not claims that a compiler or implementation has been proved correct. Their implementation and proof responsibility is outside the internal reference authority/event model unless an abstract component is separately identified.

| Reference | External contract or boundary |
|---|---|
| `OB-C05` | Reference mutex physical realization, controller accesses, successful and failed attempts, recovery publication, and justified `rf`/`sw`/`LockOrder` (C25, C41, C48, C49). |
| `OB-C07` | Cross-context transferability and shareability typing and interface contract — Specs 3/4 (C9; frozen Spec 1 §29). For a separately declared callable interface, the static eligibility of its parameter and result values for cross-context transfer or sharing (the transferability and shareability properties of C9) must be determinable from its declared types, signature, and applicable declared constraints, without inspecting the body of the callable. The body of a declared callable must be checked against its signature and declared contract; it may not provide additional, undeclared eligibility guarantees to callers. An anonymous callable, including a closure or suspended computation created within a body, may have its captures and resulting eligibility determined during local checking of that body; no particular capture-declaration syntax is imposed here. If such a value crosses a separately declared callable interface, the required eligibility must be expressible and verifiable through that interface. This contract applies to applicable constructs introduced by Spec 3 and to the typing and composition rules of Spec 4; it does not relocate the semantic conditions established by Spec 2. Static eligibility does not establish the legality of a particular transfer or shared access, which remains governed by the applicable authority, initialization, dependency, lifetime, and other step preconditions of Specs 1 and 2, together with their separate safe-trace and event-ordering obligations. |
| `OB-C08` | Reference mutex safe-interface and library contract enforcement — Specs 4 and 10 (C22). |
| `OB-C09` | By-value passing conventions, cancellation, abnormal termination, cleanup, and the refinement to the C5 reference transition — Spec 3. |
| `OB-C10` | External contexts and interoperability contract — Spec 11 (C10). |
| `OB-C12` | Concrete realization and refinement under Spec 1 §82; the abstract step-level component remains a separate formalization target (C25, C50). |
| `OB-C19` | Physical classification of pure authority markers and validity-event projections must be justified by the realization; the mathematical `po`/`hb` erasure property in C29 remains an internal proof target. |
| `OB-C20` | Coverage, authority, byte footprints, validity, and ordering for all actual physical accesses, including compound steps and failed attempts (C27–C29, C50). |
| `OB-C22` | Target feasibility and correct compilation of `NoThinAir_RC11`, including optimization preservation (C34, C50). |
| `OB-C24` | Safe-code trace soundness of Specs 3/4 and safe libraries against `SafeConcurrentTrace` (C51, C52). |
| `OB-C27` | Target-specific correct compilation and performance consequences of atomic and memory-order rules, distinct from graph axioms (C34, C40, C50). |
| `OB-C28` | The abstract authority-premise inventory and its extended atomic cases are internal formalization targets; actual safe-interface enforcement and physical recovery coverage are obligations of Specs 4/10 and the relevant realizations (C17, C22, C23). |

## Internal Verification Targets

The following named targets preserve the obligations referenced by C1–C53. They specify properties to prove, not proof status, and do not enlarge the language rules. An obligation appearing in both tables has an internal abstract component and an external realization or enforcement component.

| Reference | Internal verification target |
|---|---|
| `OB-C01` | Event model and definition of the permitted executions (C26–C34). |
| `OB-C02` | Conflict, synchronizes-with and happens-before relations (C30, C32, C33). |
| `OB-C03` | Atomic operations, memory orders and permitted observations (C37–C41). |
| `OB-C04` | `LockOrder` for successive protected critical sections (C48, C49). |
| `OB-C05` | Abstract part: correspondence between the reference mutex authority trace and its controller event graph (C48, C49). |
| `OB-C06` | Conditional data-race-freedom theorem under `SafeConcurrentTrace` and event/physical-correspondence premises (C52). |
| `OB-C11` | Event-order consequences of `spawn`, completion and `join` (C28, C47). |
| `OB-C12` | Abstract part: step-level refinement to the memory machine (C25, C50). |
| `OB-C13` | Preservation of frame ancestry and validity under reparenting (C3, C6, C7). |
| `OB-C14` | Preservation properties of the four-phase reference by-value `spawn` transition (C5). |
| `OB-C15` | Soundness of the `SyncAuthorized` contract with respect to library state (C14, C25). |
| `OB-C16` | Unified guard on live administrative identities (C13.7, Spec 1 §56). |
| `OB-C17` | L1 (C45). |
| `OB-C18` | L2 (C45). |
| `OB-C19` | Abstract part: erasure of pure-authority markers preserves `hb` (C29). |
| `OB-C21` | Directional conservativity of inherited `writeShared` under `K_C.SharedDiscipline` (C35, C53). |
| `OB-C23` | Atomic model: release sequences, global `seq_cst` consistency, coherence, and the relationship with RC11 (C34, C48). |
| `OB-C25` | Handoff ordering on reference executions, including negative and positive cases (C44–C47). |
| `OB-C26` | `EventConsistent` for any number of atomic units, non-vacuity of each conjunct, and invariance of all seven conjuncts and of `EventConsistent` under the C29 erasure of pure-authority markers, subject to the explicit premises that erased markers carry no `acc`, `sync`, or `validity` attribute and are endpoints of no `rf`, `mo`, or `sw` edge (C27, C29, C31–C34). |
| `OB-C28` | Abstract part: inventory of the authority premises read by every step, atomic cases included (C22.6, C39). |

**Internal proof targets are not erased by this external-contract list.** The mathematical erasure property of C29, the conditional composition theorem of C52, and the authority, order and coherence properties of C1–C53 remain formal verification targets. Their exact scope and assumptions are to be established in `formal/DESIGN.md`, without adding semantic axioms to this specification.

The external obligations remain open until separately discharged. Stating an obligation does not discharge it. A physical realization must not turn an unsuccessful authority operation into a successful abstract step, omit an actual memory access, or fabricate a synchronization edge.
