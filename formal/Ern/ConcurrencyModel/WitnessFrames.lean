import Ern.ConcurrencyModel.WitnessBase

/-!
# Witnesses: by-value `spawn` and frame exit with reparenting (C5, C6)

Rows 7a, 7b and 8 of the witness table of the tranche brief. States are built from the initial
state of Spec 1 §47 by `ok` steps. The rejection states its single cause: the named condition
fails and every other precondition of the clause holds; its positive twin is cited in its
docstring.
-/

namespace Ern.ConcurrencyModel

open Ern.MemoryModel.Access

/-- Statics (Spec 1 §47): one `Init` static place (place 0), root authority `0` held by
frame 0. -/
def frameStatics : Statics := [((none, none, 0), true)]

/-- The statics are well formed (Spec 1 §47). -/
theorem frameStatics_ok : StaticsOK frameStatics := by decide

/-- The contract of the frame witnesses: every place is ordinary; no `SharedMutable` leaf. -/
abbrev kFrames : KShared := testKS [] (fun _ => none) false

/-- Initial single-context state (Spec 1 §47). -/
def f0 : SC := SC.ofS3 (S3.init frameStatics)
/-- Context 0 enters frame 1 with two locals, `v` (place 1) and `p` (place 2), of root
authorities 1 and 2 (O6). -/
def f1 : SC := enterEffC f0 0 [] [(none, 0), (none, 0)]
/-- `write3(v)` through its root authority (O10). -/
def f2 : SC := f1.set (write3Eff (f1.view 0) [1])
/-- `write3(p)` through its root authority (O10). -/
def f3 : SC := f2.set (write3Eff (f2.view 0) [2])
/-- `alloc(provider p, owner v, one leaf)` (O14): the root `T` (place 3) owned by `v`, its root
authority 3 held by `v`. -/
def f4 : SC := f3.set (allocEff (f3.view 0) 1 [(none, 0)])

/-- The setup steps are `ok` (O6, O10, O14). -/
theorem frames_steps : opStepC kFrames.toK (.enter [] [(none, 0), (none, 0)]) 0 f0 (.ok f1) ∧
    opStepC kFrames.toK (.write 1 [1]) 0 f1 (.ok f2) ∧
    opStepC kFrames.toK (.write 2 [2]) 0 f2 (.ok f3) ∧
    opStepC kFrames.toK (.alloc 2 1 [(none, 0)]) 0 f3 (.ok f4) :=
  ⟨⟨by decide, .ok (by decide)⟩, ⟨by decide, _, .ok (by decide), rfl⟩,
    ⟨by decide, _, .ok (by decide), rfl⟩, ⟨by decide, _, .ok (by decide) trivial, rfl⟩⟩

/-- `a := derive(root_p, Modify, {p})` by context 0, authority 4 (O1). -/
def f5 : SC := f4.set (deriveEff (f4.view 0) 2 [2] .modify)
/-- `b := derive(root_v, Modify, {v})` by context 0, authority 4 (O1). -/
def f5' : SC := f4.set (deriveEff (f4.view 0) 1 [1] .modify)

/-- **Row 7a** (C5, `ok`): from frame 1, the by-value composite creates context 1 with one local
`d` (place 4), moves `v` (and the root `T` it owns) into `d`, and yields `a`, which covers `p`
only: the preconditions of C4 and C5 (items 1–5, C5.1–C5.4) hold. -/
theorem witness_7a : opStepC kFrames.toK (.derive 2 [2] .modify) 0 f4 (.ok f5) ∧
    SpawnValPre kFrames.toK f5 0 [4] [(none, 0)] [(1, 4)] ∧
    LStep kFrames mutexLayout (.spawnVal 0 [4] [(none, 0)] [(1, 4)]) (f5, [], [])
      (spawnValEff f5 0 [4] [(none, 0)] [(1, 4)], [], []) :=
  have hp : SpawnValPre kFrames.toK f5 0 [4] [(none, 0)] [(1, 4)] := by decide
  ⟨⟨by decide, _, .ok (by decide), rfl⟩, hp, .spawnVal ⟨by decide, .ok hp⟩⟩

/-- **Row 7b** (C5 item 5, `reject`): the same composite yielding `b`, which covers the leaf of
the source `v`. Single cause: C5 item 5 fails; the other preconditions of C4 and C5 hold, the
transfer phase of `v` included (`b` grounds the `Modify` right over `v`, Spec 1 §63.1, §63.4).
Positive twin: row 7a. -/
theorem witness_7b : opStepC kFrames.toK (.derive 1 [1] .modify) 0 f4 (.ok f5') ∧
    ¬ (∀ a ∈ [4], ∀ v ∈ [(1, 4)], ∀ l ∈ (f5'.view 0).afp a, l ∉ footprint f5'.P v.1) ∧
    f5'.stk 0 ≠ [] ∧
    (∀ a ∈ [4], OptP ((f5'.view 0).A[a]?) (fun y => y.active = true ∧
      y.holder = .frame (f5'.view 0).top ∧ y.origin ≠ none) False) ∧
    ShapeOK f5'.P.length (LocalShape.toShape [(none, 0)]) ∧
    (∀ v ∈ [(1, 4)], FreshRootLocal f5' [(none, 0)] v.2) ∧
    ValTransfersPre kFrames.toK (spawnValEff f5' 0 [4] [(none, 0)] [(1, 4)]).flat 0
      (spawnCreate f5' 0 [(none, 0)]) [(1, 4)] ∧
    (∀ a ∈ [4], OptP (((transfersEff 0 (spawnCreate f5' 0 [(none, 0)]) [(1, 4)]).view 0).A[a]?)
      (fun y => y.active = true ∧
        y.holder = .frame ((transfersEff 0 (spawnCreate f5' 0 [(none, 0)]) [(1, 4)]).view 0).top ∧
        y.origin ≠ none) False) ∧
    AnchorOrderC (spawnValEff f5' 0 [4] [(none, 0)] [(1, 4)]) ∧
    (∀ v ∈ [(1, 4)], (spawnValEff f5' 0 [4] [(none, 0)] [(1, 4)]).flat.Usable v.2) ∧
    (∀ p ∈ [4], ParamOriginHidden
      ((spawnValEff f5' 0 [4] [(none, 0)] [(1, 4)]).view f5'.C.length) p) ∧
    AnchorOrderHeldC (spawnValEff f5' 0 [4] [(none, 0)] [(1, 4)]) ∧
    SpawnValStep kFrames.toK f5' 0 [4] [(none, 0)] [(1, 4)] .reject ∧
    ∀ st', ¬ LStep kFrames mutexLayout (.spawnVal 0 [4] [(none, 0)] [(1, 4)]) (f5', [], []) st' :=
  have hn : ¬ SpawnValPre kFrames.toK f5' 0 [4] [(none, 0)] [(1, 4)] := by decide
  ⟨⟨by decide, _, .ok (by decide), rfl⟩, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, ⟨by decide, .reject hn⟩,
    fun st' h => by
      cases h with
      | spawnVal h =>
        obtain ⟨-, h⟩ := h
        cases h with
        | ok hp => exact hn hp⟩

/-- The by-value composite from frame 1 without parameter: context 1, initial frame 2, parent
frame 1 (C4, C5). -/
def f6 : SC := spawnValEff f4 0 [] [(none, 0)] [(1, 4)]
/-- `exitFrameC` of frame 1 by context 0 (C6). -/
def f7 : SC := exitEffC f6 0

/-- **Row 8** (C6, `ok`): context 0 exits frame 1, the parent of the initial frame 2 of context 1:
the frame is the current non-initial frame of context 0 with the surviving caller frame 0, and the
inherited conditions of O7 (O7.2–O7.5, under `ancestorC`) hold. The initial frame 2 takes the
surviving caller frame 0 as parent; the other links are unchanged. -/
theorem witness_8 : SpawnValStep kFrames.toK f4 0 [] [(none, 0)] [(1, 4)] (.ok f6) ∧
    f6.stk 1 = [2] ∧ f6.parC 2 = some 1 ∧ ExitPreC kFrames.toK f6 0 ∧
    LStep kFrames mutexLayout (.kernel 0 .exit) (f6, [], []) (f7, [], []) ∧
    f7.parC 2 = some 0 ∧ f7.stk 0 = [0] ∧ f7.Live 1 :=
  ⟨⟨by decide, .ok (by decide)⟩, by decide, by decide, by decide,
    .kernel ⟨by decide, .ok (by decide)⟩, by decide, by decide, by decide⟩

end Ern.ConcurrencyModel
