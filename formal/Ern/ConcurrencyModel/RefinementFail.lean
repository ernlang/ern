import Ern.ConcurrencyModel.StepRefinement

/-!
# Theorem 9, the `fail` outcomes of `alloc` and `issue` (Spec 1 §58, §71, §77.4)

`LStep` carries the `ok` transitions only. The two `fail` outcomes of the concurrent machine are
those of Spec 1 (§58: "only `alloc` may produce it in the O1–O16 kernel"; library operations such
as `issue` may define their own), executed by any context `c` (C2):

* `alloc`: `opStepC k (.alloc pr ow ls) c s .fail`, the `fail` of `AllocStep` on the view of `c`:
  the static preconditions hold and `K.Satisfiable` fails on that view (Spec 1 §71; C2,
  `alloc_fail_unsatisfiable`);
* `issue`: `IssueStepC.fail`: the static checks (Spec 1 §77.1–§77.3) hold on the view of `c` and a
  leaf of the region is not available (§77.4).

`Outcome3.fail` carries no state: the machine stays in the state of the request (§58: "a defined
failure leaving the state unchanged"; §71, §77.4). A `fail` is not a labelled step, so it is not a
step of a translated run (`TransRun`). The statements below are the counterpart of
`Refinement.r6_alloc_fail`, distinct from theorem 9a.
-/

namespace Ern.ConcurrencyModel

open Ern.MemoryModel Ern.MemoryModel.Access Ern.MemoryModel.Refinement

section Fail

variable {Ty : Type} {C : Nat → Nat → Prop} {ObR : Machine.ReadOblSpec Ty}
  {ObW : Machine.WriteOblSpec Ty}

/-- **Theorem 9**, the `fail` of `alloc` (Spec 1 §58, §71, §82 preamble; C2), for an `alloc`
executed by any context `c`, at the grain of abstract steps, as `Refinement.r6_alloc_fail`: a
request whose outcome is `fail` ("no state change", §71) is realized by no raw operation, and
`ReprC` is kept as is. Fragment: every state related by `ReprC`, every context.

This is a statement about the refinement at the grain of abstract steps. It does not say that a
failed attempt makes no physical access: such accesses belong to the event coverage (C26,
`OB-C20`). -/
theorem alloc_fail_realizedC {L : Layout} {rtok : Nat → Nat} {k : K} {s : SC}
    {m : Machine.State} {c pr ow : Nat} {ls : LocalShape} (hR : ReprC L rtok s m)
    (_h : opStepC k (.alloc pr ow ls) c s .fail) :
    Machine.Exec C ObR ObW ([] : List (Machine.Op Ty)) m m ∧ ReprC L rtok s m :=
  ⟨.nil m, hR⟩

/-- **Theorem 9**, the `fail` of `issue` (Spec 1 §58, §77.4, Part XIV, §82.7; C2, C19), for an
`issue` executed by any context `c`, at the grain of abstract steps, as `Refinement.r6_alloc_fail`
for `alloc`: a request whose outcome is `fail` (the region is unavailable after the static checks;
"leaves the entire state unchanged", §77.4) is realized by no raw operation, and `ReprC` is kept as
is. Fragment: every state related by `ReprC`, every arena registry, every context.

This is a statement about the refinement at the grain of abstract steps. It does not say that a
failed attempt makes no physical access: such accesses belong to the event coverage (C26,
`OB-C20`). -/
theorem issue_fail_realizedC {L : Layout} {rtok : Nat → Nat} {k : K} {s : SC} {ar : ArenaReg}
    {m : Machine.State} {c i dst : Nat} {region : List Nat} (hR : ReprC L rtok s m)
    (_h : IssueStepC k s ar c i region dst .fail) :
    Machine.Exec C ObR ObW ([] : List (Machine.Op Ty)) m m ∧ ReprC L rtok s m :=
  ⟨.nil m, hR⟩

end Fail

end Ern.ConcurrencyModel
