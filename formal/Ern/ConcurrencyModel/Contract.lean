import Ern.ConcurrencyModel.SpawnValue

/-!
# The concurrent external contract `K_C`

* `KC R` (C2, C14, C35, C38): the unchanged Spec 1 contract `K` (§48, §80), reached by the
  projection `KC.toK`, extended with the opaque predicate `SyncAuthorized(state, sync_registry,
  guarded, requesting_frame)` of C14, whose registry argument has the type `R` of the library
  registry (C2: the registry is an external argument, not a component of `S_C`), and with the
  companion shared-mutation contract `SharedDiscipline` of C35;
* the disciplines of C35 and the memory orders of C40.

Obligations of `K_C` are hypotheses of theorems, never fields.
-/

namespace Ern.ConcurrencyModel

open Ern.MemoryModel.Access

/-- The disciplines that the companion contract `K_C.SharedDiscipline` selects for a
`SharedMutable` leaf (C35): `Atomic(size, align)`, one indivisible atomic unit with a supported
size and alignment; `Synchronized`; `Confined`. -/
inductive Discipline where
  | atomic (size align : Nat)
  | synchronized
  | confined
deriving DecidableEq, Repr

/-- The memory orders (C40); `consume` is not included. -/
inductive MemOrder where
  | relaxed
  | release
  | acquire
  | acqRel
  | seqCst
deriving DecidableEq, Repr

/-- The kind of an atomic modification (C39): a plain atomic write, or an RMW whose read
component observed the value `observed`. Values are opaque numbers; the step relation does not
constrain them (C37, C39). -/
inductive WriteKind where
  | store
  | rmw (observed : Nat)
deriving DecidableEq, Repr

/-- The Spec 1 contract `K` with the companion shared-mutation contract of `K_C` (C35, C38).

* `toK`: the projection to the unchanged Spec 1 contract `K` (C2).
* `SharedDiscipline l`: the discipline the companion contract `K_C.SharedDiscipline` selects for
  leaf `l` (C35), `none` when it selects none. `K.SharedMutable` keeps its Spec 1 meaning (C35).
* `CompositeContract region`: a separately established composite contract (C38) for a region that
  combines `SharedDiscipline` classes. It returns the declared within-step order of the region it
  admits (C28: the contract "must determine the within-step `po` order of its actual access
  events"; "a composite contract that leaves their relative order undetermined does not admit the
  step"), `none` when it does not admit the region. It receives neither the memory-order
  annotation nor the kind of the step (C39: "A composite contract (C38) cannot override these
  rules"). That the contract reads only the region and that the declared order is an enumeration
  of the leaves of the region is a formalization hypothesis (reading 7, module `Atomic`). -/
structure KShared extends K where
  SharedDiscipline : Nat → Option Discipline
  CompositeContract : List Nat → Option (List Nat)

/-- External contract `K_C` (C2, C14, C35): `KShared` with the opaque predicate
`SyncAuthorized(state, sync_registry, guarded, requesting_frame)` of C14, the registry being an
external argument of type `R` (C2: it does not become a component of `S_C`). -/
structure KC (R : Type) extends KShared where
  SyncAuthorized : R → SC → Nat → Nat → Prop

end Ern.ConcurrencyModel
