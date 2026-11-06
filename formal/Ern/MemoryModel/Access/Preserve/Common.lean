import Ern.MemoryModel.Access.Lemmas

/-!
# Access kernel: the preserved invariant

The conjunction that every kernel step must preserve (§57 of
`specs/ERN_Memory_Model_Specification.md`) and the auxiliary invariant carried with it. The per-operation preservation modules state their results with these two predicates.
-/

namespace Ern.MemoryModel.Access

/-- The kernel invariant of §57: `WF3 ∧ Inv3 ∧ AnchorOrderHeld ∧ NoOrphan`. -/
def KInv (s : S3) : Prop := WF3 s ∧ Inv3 s ∧ AnchorOrderHeld s ∧ NoOrphan s

/-- Auxiliary invariant carried with `KInv`, not a clause of §57 (§40, §49.7): the converse
root-holder property `RootHeldConv`, which is not a clause of `WF3`. -/
def KAux (s : S3) : Prop := RootHeldConv s

/-- `NoOrphan` follows from `WF3` (§54, §49.7), so `KInv` reduces to its first three
conjuncts. -/
theorem kInv_of {s : S3} (hw : WF3 s) (hi : Inv3 s) (ha : AnchorOrderHeld s) : KInv s :=
  ⟨hw, hi, ha, noOrphan_of_wf3 hw⟩

end Ern.MemoryModel.Access
