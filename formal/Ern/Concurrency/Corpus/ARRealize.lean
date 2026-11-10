import Ern.Concurrency.Corpus.AR
import Ern.Concurrency.RealizeSound

/-!
# Corpus of milestone 3: the arena run of S3 in the memory machine

The trace of block AR and of `corpus-spec2-m3.md` §1 S3 up to step 3 (`c1 : acquire(e2)`, then
`issue(arena, R1, d1)` under `g2`) as a translated run (`SimRunC`), on the pattern of
`Ern.Concurrency.RealizeWitness.s4_realized`: under parameters fixed once from the final places,
every step satisfies its obligations (`StepOblC`), the run is realized by an execution of `ok` raw
steps from the empty memory state, none `ub`, with `ReprC` at each state (Spec 1 §77, §82; WC4
C19). At the state before `issue`, the hypotheses of `issue_pointer_soundC` hold jointly, and the
reference written into `d1` decodes to the address of the issued region (Spec 1 §82.3).

Contexts interleave at the grain of abstract steps, as everywhere in `Ern.Concurrency.Realize`.
-/

namespace Ern.Concurrency.Corpus.ARRealize

open Ern.MemoryModel Ern.MemoryModel.Access Ern.MemoryModel.Refinement
open Ern.MemoryModel.Refinement.Runs Ern.Concurrency Ern.Concurrency.Corpus
open Ern.Concurrency.Traces (L0)

/-- Parameters of the run, fixed once from its final places (Spec 1 §82): the test layout,
geometry and reference encoding of `Refinement.Runs`. -/
def πA : Refinement.Params Unit := piOf a8.P []

/-- The memory state realizing the initial state of block AR (Spec 1 §47, `repr_init`). -/
def mA0 : Machine.State :=
  run Machine.State.empty (initOps πA.pl πA.geom πA.rtok πA.L πA.ty πA.ival arst)
/-- After `derive(root_ST)` (O1). -/
def mA1 : Machine.State := run mA0 (realize πA wv (.kernel 0 (.derive 2 [5, 6] .modify)) a0 [] mA0)
/-- After `store(internal, AV)` (O8). -/
def mA2 : Machine.State := run mA1 (realize πA wv (.kernel 0 (.store 4 3)) a1 [] mA1)
/-- After `newArena` (O17). -/
def mA3 : Machine.State := run mA2 (realize πA wv (.newArena 0 4 4) a2 [] mA2)
/-- After `derive(root_AV)` (O1). -/
def mA4 : Machine.State :=
  run mA3 (realize πA wv (.kernel 0 (.derive 1 [3] .modify)) a2 arA mA3)
/-- After `store(guarded2, slot2)` (O8). -/
def mA5 : Machine.State := run mA4 (realize πA wv (.kernel 0 (.store 5 1)) a3 arA mA4)
/-- After `newMutex(guarded2)` (WC4 C13). -/
def mA6 : Machine.State := run mA5 (realize πA wv (.newMutex 0 5) a4 arA mA5)
/-- After `derive(root_M2, Observe)` (O1). -/
def mA7 : Machine.State :=
  run mA6 (realize πA wv (.kernel 0 (.derive 0 [1, 2] .observe)) a4 arA mA6)
/-- After `spawn c1` with the local `d1` (WC4 C4). -/
def mA8 : Machine.State := run mA7 (realize πA wv (.spawn 0 [6] [(none, 0)]) a5 arA mA7)
/-- After `c1 : acquire(e2)` (WC4 C16). -/
def mA9 : Machine.State := run mA8 (realize πA wv (.acquire 1 0) a6 arA mA8)
/-- After `c1 : issue(arena, R1, d1)` (Spec 1 §77). -/
def mA10 : Machine.State := run mA9 (realize πA wv (.issue 1 0 [5] 8) a7 arA mA9)

/-- Initial state of the translated run (Spec 1 §47). -/
theorem ar_sim0 : SimRunC KA L0 (· = ·) obR obW arst πA (a0, [], []) mA0 :=
  .init arst_ok (by decide) (by decide)

/-- After `derive(root_ST)`. -/
theorem ar_sim1 : SimRunC KA L0 (· = ·) obR obW arst πA (a1, [], []) mA1 :=
  .step (w := wv) (st := (a0, [], []))
    (lbl := .kernel 0 (.derive 2 [5, 6] .modify)) (st' := (a1, [], [])) ar_sim0
    (fun e he => by cases he) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) (by decide)

/-- After `store(internal, AV)`. -/
theorem ar_sim2 : SimRunC KA L0 (· = ·) obR obW arst πA (a2, [], []) mA2 :=
  .step (w := wv) (st := (a1, [], []))
    (lbl := .kernel 0 (.store 4 3)) (st' := (a2, [], [])) ar_sim1 trivial
    (.kernel ⟨by decide, .ok (by decide)⟩) (by decide)

/-- After `newArena(ST, internal)`. -/
theorem ar_sim3 : SimRunC KA L0 (· = ·) obR obW arst πA (a2, [], arA) mA3 :=
  .step (w := wv) (st := (a2, [], []))
    (lbl := .newArena 0 4 4) (st' := (a2, [], arA)) ar_sim2 trivial
    (.newArena (st' := (a2, arA)) ⟨by decide, .ok (by decide)⟩) (by decide)

/-- After `derive(root_AV)`. -/
theorem ar_sim4 : SimRunC KA L0 (· = ·) obR obW arst πA (a3, [], arA) mA4 :=
  .step (w := wv) (st := (a2, [], arA))
    (lbl := .kernel 0 (.derive 1 [3] .modify)) (st' := (a3, [], arA)) ar_sim3
    (fun e he => by cases he) (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) (by decide)

/-- After `store(guarded2, slot2)`. -/
theorem ar_sim5 : SimRunC KA L0 (· = ·) obR obW arst πA (a4, [], arA) mA5 :=
  .step (w := wv) (st := (a3, [], arA))
    (lbl := .kernel 0 (.store 5 1)) (st' := (a4, [], arA)) ar_sim4 trivial
    (.kernel ⟨by decide, .ok (by decide)⟩) (by decide)

/-- After `newMutex(guarded2)`. -/
theorem ar_sim6 : SimRunC KA L0 (· = ·) obR obW arst πA (a4, regA, arA) mA6 :=
  .step (w := wv) (st := (a4, [], arA))
    (lbl := .newMutex 0 5) (st' := (a4, regA, arA)) ar_sim5 trivial
    (.newMutex (st' := (a4, regA)) ⟨by decide, by decide, rfl⟩) (by decide)

/-- After `derive(root_M2, Observe)`. -/
theorem ar_sim7 : SimRunC KA L0 (· = ·) obR obW arst πA (a5, regA, arA) mA7 :=
  .step (w := wv) (st := (a4, regA, arA))
    (lbl := .kernel 0 (.derive 0 [1, 2] .observe)) (st' := (a5, regA, arA)) ar_sim6
    (by decide : ∀ e ∈ regA, e.Live a4 → 0 ≠ e.guarded)
    (.kernel ⟨by decide, _, .ok (by decide), rfl⟩) (by decide)

/-- After `spawn c1`. -/
theorem ar_sim8 : SimRunC KA L0 (· = ·) obR obW arst πA (a6, regA, arA) mA8 :=
  .step (w := wv) (st := (a5, regA, arA))
    (lbl := .spawn 0 [6] [(none, 0)]) (st' := (a6, regA, arA)) ar_sim7 trivial
    (.spawn ⟨by decide, .ok (by decide)⟩) (by decide)

/-- After `c1 : acquire(e2)` (`S3_2_ok`). -/
theorem ar_sim9 : SimRunC KA L0 (· = ·) obR obW arst πA (a7, regA8, arA) mA9 :=
  .step (w := wv) (st := (a6, regA, arA))
    (lbl := .acquire 1 0) (st' := (a7, regA8, arA)) ar_sim8 trivial
    (.acquire (st' := (a7, regA8)) S3_2_ok) (by decide)

/-- After `c1 : issue(arena, R1, d1)` (`S3_3_ok`). -/
theorem ar_sim10 : SimRunC KA L0 (· = ·) obR obW arst πA (a8, regA8, arA1) mA10 :=
  .step (w := wv) (st := (a7, regA8, arA))
    (lbl := .issue 1 0 [5] 8) (st' := (a8, regA8, arA1)) ar_sim9 trivial
    (.issue (st' := (a8, arA1)) S3_3_ok) (by decide)

/-- `corpus-spec2-m3.md` §1 S3 up to step 3, in the memory machine (Spec 1 §77, §82; WC4 C19, C25),
at the grain of abstract steps: the run is realized by an execution of `ok` raw steps from the empty
memory state, none `ub`; it is an `EncapsulatedTrace` from the initial state of Spec 1 §47; `ReprC`
holds at every state of the run. -/
theorem s3_realized :
    ((∃ ops, Machine.Exec (· = ·) obR obW ops Machine.State.empty mA10) ∧
      ReprC πA.L πA.rtok a8 mA10 ∧
      ∃ lbls, EncapsulatedTrace KA L0 (SC.ofS3 (S3.init arst), [], []) lbls (a8, regA8, arA1)) ∧
    (∃ ops, Machine.Exec (· = ·) obR obW ops Machine.State.empty mA10 ∧
      Along (NoUB (· = ·) obR obW) Machine.State.empty ops) ∧
    ReprC πA.L πA.rtok a0 mA0 ∧ ReprC πA.L πA.rtok a1 mA1 ∧ ReprC πA.L πA.rtok a2 mA2 ∧
    ReprC πA.L πA.rtok a2 mA3 ∧ ReprC πA.L πA.rtok a3 mA4 ∧ ReprC πA.L πA.rtok a4 mA5 ∧
    ReprC πA.L πA.rtok a4 mA6 ∧ ReprC πA.L πA.rtok a5 mA7 ∧ ReprC πA.L πA.rtok a6 mA8 ∧
    ReprC πA.L πA.rtok a7 mA9 := by
  have hdd := ddKC [2]
  have hπ := piOf_ok a8.P []
  exact ⟨simulationC hdd hπ ar_sim10, concrete_safety hdd hπ ar_sim10,
    (simulationC hdd hπ ar_sim0).2.1, (simulationC hdd hπ ar_sim1).2.1,
    (simulationC hdd hπ ar_sim2).2.1, (simulationC hdd hπ ar_sim3).2.1,
    (simulationC hdd hπ ar_sim4).2.1, (simulationC hdd hπ ar_sim5).2.1,
    (simulationC hdd hπ ar_sim6).2.1, (simulationC hdd hπ ar_sim7).2.1,
    (simulationC hdd hπ ar_sim8).2.1, (simulationC hdd hπ ar_sim9).2.1⟩

/-- The state after `split` of `internal` on `R1` by context 1 (Spec 1 §61). -/
def tA : S3 := splitEff (a7.view 1) 4 [[5]]

/-- The address of the issued block, read on `tA` (Spec 1 §82.2, `ptrAddr`). -/
def adA : Nat := ptrAddr mA9 πA.L tA a7.A.length

/-- The hypotheses of `issue_pointer_soundC` hold jointly at the state before `issue` (Spec 1
§82.3; WC4 C25): `ReprC` (from the run), `FramesC`, `WF3` and `NoDangling` (from
`encapsulated_inv` on the run's trace), the `ok` issue `S3_3_ok`, the entry of the arena, a
destination leaf of pointer size, and the obligation of the encoding for the reference. -/
theorem s3_issue_hyps : ReprC πA.L πA.rtok a7 mA9 ∧ FramesC a7 ∧ WF3 a7.flat ∧
    NoDangling a7.flat ∧ IssueStepC KA a7 arA 1 0 [5] 8 (.ok (a8, arA1)) ∧
    arA[0]? = some ⟨4, 4, [5, 6], []⟩ ∧ (πA.L 8).len = πA.pe.size ∧
    PtrEncAt πA.pe adA (some (anchorAlloc πA.L tA a7.A.length)) := by
  obtain ⟨-, hR, lbls, htr⟩ := simulationC (ddKC [2]) (piOf_ok a8.P []) ar_sim9
  obtain ⟨hk, -, -⟩ := encapsulated_inv (ddKC [2]) arst_ok htr
  exact ⟨hR, hk.1.1, hk.1.2, hk.2.1.2.2, S3_3_ok, rfl, by decide, by decide, fun _ => rfl⟩

/-- `issue_pointer_soundC` on the run (Spec 1 §82.3, §77): after the realization of
`issue(arena, R1, d1)`, the bytes of `d1` decode to the address `adA` of the issued region, every
byte carries the provenance of the allocation of the effective anchor of the block, and that
address is 48 under the test parameters. -/
theorem s3_issue_pointer : πA.pe.decode (bytesOf mA10 πA.L 8) = adA ∧
    (∀ i, i < (πA.L 8).len → (bytesOf mA10 πA.L 8 i).2 = some (anchorAlloc πA.L tA a7.A.length)) ∧
    adA = 48 := by
  obtain ⟨hR, hfr, hw, hnd, h, hE, hsz, henc⟩ := s3_issue_hyps
  obtain ⟨h1, h2, -⟩ := issue_pointer_soundC (ty := πA.ty) (ad := adA) hR hfr hw hnd h hE rfl hsz
    henc
  have hv : (a7.set tA).view 1 = tA := SC.view_set rfl
  have hm : mA10 = run mA9 (storeOps (Ty := Unit) πA.pe mA9 πA.L πA.ty tA a7.A.length 8) := by
    show run mA9 (realize πA wv (.issue 1 0 [5] 8) a7 arA mA9) = _
    rw [realize_issue πA wv hE]
    exact congrArg (fun t => run mA9 (storeOps (Ty := Unit) πA.pe mA9 πA.L πA.ty t a7.A.length 8))
      hv
  rw [hm]
  exact ⟨h1, h2, by decide⟩

end Ern.Concurrency.Corpus.ARRealize
