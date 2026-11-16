import Ern.ConcurrencyModel.Inventory
import Ern.ConcurrencyModel.Outcomes
import Ern.ConcurrencyModel.AtomicCases

/-!
# Witnesses: the test contract and the mutex layout

Shared material of the witness modules (`WitnessMutex`, `WitnessAtomic`, `WitnessFrames`): a test
contract `K_C` without `SyncAuthorized` (`KShared`, C2, C35, C38) and the positional layout of the
reference mutex (C12). Witness states are built from the initial state of Spec 1 §47 by `ok`
steps; preconditions are checked by `decide`, which needs the decidability instances below on the
test contract.
-/

namespace Ern.ConcurrencyModel

open Ern.MemoryModel.Access

/-- Test contract (Spec 1 §48): nothing declared disjoint, the leaves of `sm` are
`SharedMutable`, nothing statically pinned, every external use done, every place deallocable,
every deallocation compatible, every allocation satisfiable. -/
def testK (sm : List Nat) : K :=
  ⟨fun _ _ => False, fun l => l ∈ sm, fun _ => False, fun _ => True, fun _ => True,
    fun _ _ => True, fun _ _ _ => True⟩

/-- Test contract `K_C` without `SyncAuthorized` (C2, C35, C38): `testK sm`, the discipline `d`
selected by `K_C.SharedDiscipline` (C35), and a composite contract (C38) admitting every
region when `cc` holds and none otherwise. -/
def testKS (sm : List Nat) (d : Nat → Option Discipline) (cc : Bool) : KShared :=
  { testK sm with SharedDiscipline := d, CompositeContract := fun _ _ _ => cc = true }

instance (sm : List Nat) (d : Nat → Option Discipline) (cc : Bool) :
    ∀ r r', Decidable ((testKS sm d cc).toK.DeclaredDisjoint r r') :=
  fun _ _ => inferInstanceAs (Decidable False)
instance (sm : List Nat) (d : Nat → Option Discipline) (cc : Bool) :
    DecidablePred (testKS sm d cc).toK.SharedMutable :=
  fun l => inferInstanceAs (Decidable (l ∈ sm))
instance (sm : List Nat) (d : Nat → Option Discipline) (cc : Bool) :
    DecidablePred (testKS sm d cc).toK.Pinned :=
  fun _ => inferInstanceAs (Decidable False)
instance (sm : List Nat) (d : Nat → Option Discipline) (cc : Bool) :
    DecidablePred (testKS sm d cc).toK.ExternalDone :=
  fun _ => inferInstanceAs (Decidable True)
instance (sm : List Nat) (d : Nat → Option Discipline) (cc : Bool) :
    DecidablePred (testKS sm d cc).toK.Deallocable :=
  fun _ => inferInstanceAs (Decidable True)
instance (sm : List Nat) (d : Nat → Option Discipline) (cc : Bool) :
    ∀ p a, Decidable ((testKS sm d cc).toK.FreeCompat p a) :=
  fun _ _ => inferInstanceAs (Decidable True)
instance (sm : List Nat) (d : Nat → Option Discipline) (cc : Bool) :
    ∀ p ls s, Decidable ((testKS sm d cc).toK.Satisfiable p ls s) :=
  fun _ _ _ => inferInstanceAs (Decidable True)
instance (sm : List Nat) (d : Nat → Option Discipline) (cc : Bool) :
    ∀ r o w, Decidable ((testKS sm d cc).CompositeContract r o w) :=
  fun _ _ _ => inferInstanceAs (Decidable (cc = true))

/-- `DDSound` of the test contract (Spec 1 §80): nothing is declared disjoint. -/
theorem testKS_dd (sm : List Nat) (d : Nat → Option Discipline) (cc : Bool) :
    DDSound (testKS sm d cc).toK :=
  fun _ _ h => h.elim

/-- The positional layout of the reference mutex (C12): `guarded` is held by the first field of
the mutex value, the controller is its second field. -/
def mutexLayout : MutexLayout := ⟨0, 1⟩

end Ern.ConcurrencyModel
