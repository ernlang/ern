import Ern.ConcurrencyModel.Controller
import Ern.ConcurrencyModel.EventDecide

/-!
# Witness: necessity of the role condition of realization R (C27, C32)

Two of the three sources of `sw` are read on the roles of the events (C32.2, C32.3). A relaxed
atomic write of the controller of role `complete(c)` and a relaxed atomic RMW of the same
controller of role `join(c)`, which reads it by `rf`, are related by `sw` through the completion
source, although neither order is release- or acquire-capable. With the role `protocol` that
realization R gives them (`ctlSync`), `sw` does not relate them.

Events: `0` the non-atomic initial write of the controller unit `0` (context 0); `1` the relaxed
atomic write of `v₀ = 0` (context 1); `2` the relaxed atomic RMW `0 → 1` (context 0), reading `1`.
`mo`: `0 < 1 < 2`.
-/

namespace Ern.ConcurrencyModel

open Events

/-- The witness graph with the roles `r₁` on the write and `r₂` on the RMW. -/
def roleGraph (r₁ r₂ : Option (SyncRole Nat)) : ListGraph 3 Nat Nat Nat Unit where
  ev i := match i.val with
    | 0 => ⟨0, ⟨0, 0⟩, .marks (some (.unit 0 (.write 0))) none⟩
    | 1 => ⟨1, ⟨1, 0⟩, .marks (some (.atomic 0 .relaxed (.write 0))) r₁⟩
    | _ => ⟨0, ⟨2, 0⟩, .marks (some (.atomic 0 .relaxed (.rmw 0 1))) r₂⟩
  uRange _ := ⟨0, 8⟩
  rf := [(1, 2)]
  mo := [(0, 1), (1, 2), (0, 2)]

/-- The roles of the completion source of C32.3. -/
abbrev Gcj : Graph (Fin 3) Nat Nat Nat Unit := (roleGraph (some (.complete 1)) (some (.join 1))).toGraph
/-- The roles of realization R (`ctlSync`). -/
abbrev Gpp : Graph (Fin 3) Nat Nat Nat Unit := (roleGraph (some .protocol) (some .protocol)).toGraph

/-- **Witness of the role condition** (C32.3, C27, C40): with the roles `complete(1)` and `join(1)`,
the relaxed write `1` is not release-capable, the relaxed RMW `2` is not acquire-capable, `2` reads
`1` by `rf`, and `sw` relates them (through the completion source); the graph is
`EventConsistent`. Twin: with the role `protocol` on both, `sw` does not relate them, and the graph
is `EventConsistent`. -/
theorem witness_roles :
    (¬ Gcj.RelCap 1 0 ∧ ¬ Gcj.AcqCap 2 0 ∧ Gcj.rf 1 2 ∧ Gcj.SW 1 2 ∧ Gcj.EventConsistent) ∧
    (¬ Gpp.RelCap 1 0 ∧ ¬ Gpp.AcqCap 2 0 ∧ Gpp.rf 1 2 ∧ ¬ Gpp.SW 1 2 ∧ Gpp.EventConsistent) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩⟩ <;> decide +kernel

end Ern.ConcurrencyModel
