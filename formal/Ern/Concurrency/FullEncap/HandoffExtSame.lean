import Ern.Concurrency.FullEncap.HandoffExtSweep

/-!
# The frontier at the first member

Brief of milestone 4, slice 4, task 4 (`formal/reports/spec2-m4-handoff-ext.md`): the couples
(kind, class) of the first member for which the frontier can be the first member itself (`r = i`).

* Class D: impossible (`extPair_first_not_dying`).
* Class E of `read3`, `write3`, `writeShared`: impossible, the access keeps every `cap5`
  (`frontier_gt_access`).
* Class E of `store` and `issue`: impossible, the clause requires `Modify` on the target in the
  resulting state (Spec 1 §65.5, §77.6), which the guard-free forms read (`PremG`), so the
  capacity of the acting context is `Modify` after the step (`frontier_gt_store`,
  `frontier_gt_issue`).
* Class N of `spawn`, class C of the by-value `spawn`: possible (`r_eq_i_witnesses`): the created
  leaves are held by the initial frame of the child, and the creator has no capability on them
  after the step.
* The other couples are left as written limits in the report.

The question of the brief (when `r = i`, does `hb(i, j)` always hold in the strict graph?) is left
open in the report; `hint_store_rejected` records that the suggested counterexample is rejected
at the kernel by Spec 1 §65.4 (`AnchorOrder`) before reaching the mutex.
-/

set_option autoImplicit false

namespace Ern.Concurrency.FullEncap.HandoffExt

open Ern.MemoryModel Ern.MemoryModel.Access Ern.Concurrency Ern.Concurrency.MutexReal
open SyncPreserveAux SyncInitAux TransferPreserveAux PreservationAux

/-! ## Compatibility facts -/

/-- On a leaf where a mode is required, some mode is required (constructively: for the provider of
`alloc`, `Observe` on a `SharedMutable` leaf, `Modify` otherwise, §71.2). -/
theorem hasReq_some {k : K} {st : SC × SyncReg × ArenaReg} {lbl : Label} {l : Nat}
    (h : HasReq st lbl l) (ho : ¬ ReqMode k st lbl l .observe)
    (hm : ¬ ReqMode k st lbl l .modify) : False := by
  cases lbl with
  | kernel c op =>
    cases op with
    | read | writeShared => exact ho rfl
    | write | store | transfer => exact hm rfl
    | endUse p | free p _ => exact hm ⟨h, rfl⟩
    | alloc pr ow ls =>
      by_cases e : l = ow
      · exact hm (.inl ⟨e, rfl⟩)
      · have hl : l ∈ footprint st.1.P pr := h.resolve_right e
        exact hm (.inr ⟨e, hl, .inr ⟨fun hs => ho (.inr ⟨e, hl, .inl ⟨hs, rfl⟩⟩), rfl⟩⟩)
    | _ => exact (h : False).elim
  | issue | newMutex => exact hm rfl
  | acquire | unlock | resetLock => exact ho rfl
  | spawnVal => exact hm ⟨h, rfl⟩
  | _ => exact (h : False).elim

/-- No touch is compatible with a capability `Modify` (WC5.3 C43: a present capability is
incompatible with a `Modify` one). -/
theorem touchCompat_not_modify {k : K} {st st' : SC × SyncReg × ArenaReg} {lbl : Label}
    {l : Nat} : ¬ TouchCompat k st st' lbl l (some .modify) := by
  rintro (⟨-, h⟩ | ⟨hE, ho, hm⟩)
  · cases h
  · exact hasReq_some hE.2.2.2 (fun h => absurd (ho h) (by decide))
      (fun h => absurd (hm h) (by decide))

/-- An exclusive touch of class D or E is compatible only with no capability. -/
theorem touchCompat_excl_none {k : K} {st st' : SC × SyncReg × ArenaReg} {lbl : Label}
    {l : Nat} {o : Option Mode}
    (hx : ClassD st st' l ∨ ClassEm k st st' lbl l .modify)
    (h : TouchCompat k st st' lbl l o) : o = none := by
  rcases hx with hD | hE
  · exact (touchCompat_iff_of_classD hD o).1 h
  · have := (touchCompat_iff_of_classEm hE o).1 h
    rcases o with _ | _ | _
    · rfl
    all_goals exact absurd this (by decide)

/-! ## Accesses -/

/-- Brief, task 4, class E of `read3`, `write3`, `writeShared`: on a `RunFull` from the initial
state, the frontier of an extended exclusive pair whose first member is an access is not the
access: an access keeps every `cap5` (`inert_effect`, `cap5_same`), which stays incompatible with
the touch of `j` (`Modify` against any touch; `Observe` against an exclusive one). -/
theorem frontier_gt_access {k : K} {L : MutexLayout} {statics : Statics}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} (hdd : DDSound k)
    (hstat : StaticsOK statics) (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], []))
    (h : RunFull k L σ lbls) {i j l r : Nat} (hp : ExtPair k L σ lbls i j l)
    (hi : i < lbls.length) {c : Nat} {m : Mode} (ha : lbls[i].Access c l m)
    (hr : IsFrontier k σ lbls i j l r) : i < r := by
  refine Nat.lt_of_le_of_ne hr.1 fun hir => ?_
  subst hir
  have hn := extPair_second_not_created hdd hstat h0 h hp
  obtain ⟨hij, hj, -, -, -, hex⟩ := hp.out
  have hfr := (frontAt_iff hi hj i).1 hr.2.2.1
  rw [(access_ctx_mode ha).1] at hfr
  obtain ⟨-, hEi, hcap⟩ := access_classEm_run (k := k) hdd hstat h0 h hi ha
  have hinert : Label.Inert lbls[i] := by
    revert ha; cases lbls[i] with
    | kernel _ op => cases op <;> simp [Label.Access, Label.Inert]
    | _ => simp [Label.Access]
  have hw : WF3 (σ i).1.flat := (runFull_inv hdd hstat h0 h (Nat.le_of_lt hi)).1.1.1.2
  obtain ⟨hA, hP, hC, hreg⟩ := inert_effect hinert (h i hi).2
  have hfi := cap5_same hw hA hP hC hreg c l
  cases m with
  | modify =>
    rw [Ern.Concurrency.allows_modify hcap] at hfi
    have e : cap5 (σ (i + 1)).1 (σ (i + 1)).2.1 c l = some .modify := by
      revert hfi; rcases cap5 (σ (i + 1)).1 (σ (i + 1)).2.1 c l with _ | _ | _ <;> decide
    rw [e] at hfr
    exact touchCompat_not_modify hfr
  | observe =>
    have hxj : ClassD (σ j) (σ (j + 1)) l ∨ ClassEm k (σ j) (σ (j + 1)) lbls[j] l .modify := by
      rcases hex with ⟨-, hD | hC | hEm⟩ | ⟨-, hD | hC | hEm⟩
      · exact absurd hD hEi.1.2.2.1
      · exact absurd hEi.1.1 (Nat.not_lt.2 hC.1.1)
      · exact absurd (reqMode_unique hEi.2 hEm.2) (by decide)
      · exact .inl hD
      · exact absurd hC.1 hn
      · exact .inr hEm
    have e := touchCompat_excl_none hxj hfr
    rw [e] at hfi
    revert hcap hfi; rcases cap5 (σ i).1 (σ i).2.1 c l with _ | _ | _ <;> decide

/-! ## `store` and `issue` -/

/-- After an `ok` `store(a, p)` by `c` admitted by the guard-free forms, from a state whose live
contexts have nonempty stacks, `c` has `cap5` `Modify` on `p`: `PremG` reads the right of §65.5
in the resulting state. -/
theorem store_cap_after {k : K} {L : MutexLayout} {st st' : SC × SyncReg × ArenaReg}
    {c a p : Nat} (hF : FramesC st.1) (hs : LStep k L (.kernel c (.store a p)) st st')
    (hp : PremG k L st (.kernel c (.store a p))) : Allows (cap5 st'.1 st'.2.1 c p) .modify := by
  cases hs with
  | @kernel s s' reg ar c op h =>
    obtain ⟨hl, h'⟩ := h; obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h'
    have hlt : p < (storeEffC s c a p).P.length := by
      have := hpre.usable.lt
      show p < (storeEff (s.view c) a p).P.length
      unfold storeEff; split <;> exact this
    have hleaf : isLeaf (storeEffC s c a p).P p := by
      have := hpre.leaf
      show isLeaf (storeEff (s.view c) a p).P p
      unfold storeEff; split <;> exact this
    exact cap5_of_hasRight5 (s := storeEffC s c a p) (hF.nonempty c hl) hp.2
      (mem_footprint_self hleaf hlt)

/-- Brief, task 4, class E of `store`: on a `RunFull` from the initial state, the frontier of an
extended exclusive pair whose first member is `store(a, l)` is not that step. -/
theorem frontier_gt_store {k : K} {L : MutexLayout} {statics : Statics}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} (hdd : DDSound k)
    (hstat : StaticsOK statics) (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], []))
    (h : RunFull k L σ lbls) {i j l r : Nat} (hp : ExtPair k L σ lbls i j l)
    (hi : i < lbls.length) {c a : Nat} (hl : lbls[i] = .kernel c (.store a l))
    (hr : IsFrontier k σ lbls i j l r) : i < r := by
  refine Nat.lt_of_le_of_ne hr.1 fun hir => ?_
  subst hir
  obtain ⟨-, hj, -, -, -, -⟩ := hp.out
  have hfr := (frontAt_iff hi hj i).1 hr.2.2.1
  have hs := (h i hi).2
  have hpg := (h i hi).1.2
  rw [hl] at hs hpg hfr
  have hcap := store_cap_after (runFull_inv hdd hstat h0 h (Nat.le_of_lt hi)).1.1.1.1 hs hpg
  rw [show (Label.kernel c (KernelOp.store a l)).ctx = c from rfl,
    Ern.Concurrency.allows_modify hcap] at hfr
  exact touchCompat_not_modify hfr

/-- After an `ok` `issue` by `c` into `dst` admitted by the guard-free forms, from a state whose
live contexts have nonempty stacks, `c` has `cap5` `Modify` on `dst`: `PremG` reads the right of
§77.6 (with §65.5) in the resulting state. -/
theorem issue_cap_after {k : K} {L : MutexLayout} {st st' : SC × SyncReg × ArenaReg}
    {c ai : Nat} {region : List Nat} {dst : Nat} (hF : FramesC st.1)
    (hs : LStep k L (.issue c ai region dst) st st') (hp : PremG k L st (.issue c ai region dst)) :
    Allows (cap5 st'.1 st'.2.1 c dst) .modify := by
  cases hs with
  | @issue s reg ar c ai region dst st₁ h =>
    obtain ⟨E, s₁, hE, -, -, hsp, hsto, -⟩ := issueStepC_ok h
    have hpg := hp
    simp only [PremG] at hpg
    rw [hE] at hpg
    obtain ⟨hl, hsp'⟩ := hsp
    obtain ⟨t, hR, rfl⟩ := viewStep_ok ⟨hl, hsp'⟩
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hR
    obtain ⟨hl₁, hsto'⟩ := hsto
    obtain ⟨hpre, he⟩ := Guarded.ok_iff.1 hsto'
    have e : st₁.1 = storeEffC (issueMid s c E region) c s.A.length dst := he
    show Allows (cap5 st₁.1 reg c dst) .modify
    rw [e]
    have hlt : dst < (storeEffC (issueMid s c E region) c s.A.length dst).P.length := by
      have := hpre.usable.lt
      show dst < (storeEff _ _ dst).P.length
      unfold storeEff; split <;> exact this
    have hleaf : isLeaf (storeEffC (issueMid s c E region) c s.A.length dst).P dst := by
      have := hpre.leaf
      show isLeaf (storeEff _ _ dst).P dst
      unfold storeEff; split <;> exact this
    exact cap5_of_hasRight5 (hF.nonempty c hl) hpg.2.2.2.2 (mem_footprint_self hleaf hlt)

/-- Brief, task 4, class E of `issue`: on a `RunFull` from the initial state, the frontier of an
extended exclusive pair whose first member is an `issue` into `l` is not that step. -/
theorem frontier_gt_issue {k : K} {L : MutexLayout} {statics : Statics}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} (hdd : DDSound k)
    (hstat : StaticsOK statics) (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], []))
    (h : RunFull k L σ lbls) {i j l r : Nat} (hp : ExtPair k L σ lbls i j l)
    (hi : i < lbls.length) {c ai : Nat} {region : List Nat}
    (hl : lbls[i] = .issue c ai region l) (hr : IsFrontier k σ lbls i j l r) : i < r := by
  refine Nat.lt_of_le_of_ne hr.1 fun hir => ?_
  subst hir
  obtain ⟨-, hj, -, -, -, -⟩ := hp.out
  have hfr := (frontAt_iff hi hj i).1 hr.2.2.1
  have hs := (h i hi).2
  have hpg := (h i hi).1.2
  rw [hl] at hs hpg hfr
  have hcap := issue_cap_after (runFull_inv hdd hstat h0 h (Nat.le_of_lt hi)).1.1.1.1 hs hpg
  rw [show (Label.issue c ai region l).ctx = c from rfl,
    Ern.Concurrency.allows_modify hcap] at hfr
  exact touchCompat_not_modify hfr

end Ern.Concurrency.FullEncap.HandoffExt

namespace Ern.Concurrency.FullEncap.HandoffExtSame

open Ern.MemoryModel Ern.MemoryModel.Access Ern.Concurrency Ern.Concurrency.MutexReal
open Ern.Concurrency.FullEncap Ern.Concurrency.FullEncap.HandoffExt Ern.Concurrency.Corpus
open Ern.Concurrency.FullEncap.Witness (instDecidableEncap5R)
open Ern.Concurrency.Traces (L0)
open Ern.MemoryModel.Access.Examples (K0)

/-! ## Witnesses of `r = i` -/

/-- Brief, task 4, couples where `r = i` occurs, on `RunFull` traces from the initial state:
`(spawn, N)`: in the `terminate` witness of slice 3 (`CapacityWitness.tm`), the `spawn` of step 0
creates the locals of the child and the child stores into one of them at step 2; in S3
(`MutexReal.NonRegression.s3`), the `spawn` of step 7 creates the local 8 of the child, which
`issue`s into it at step 9. `(spawnVal, C)`: W-SV (`W_SV_graph`). The frontier is the creating
step; `hb(i, j)` holds by the creation edge. -/
theorem r_eq_i_witnesses :
    ClassN L0 (CapacityWitness.tmσ 0) (CapacityWitness.tmσ 1) (.spawn 0 [] CapacityWitness.eLocals)
      2 ∧
    IsFrontier CapacityWitness.KE3 CapacityWitness.tmσ CapacityWitness.tmLbls 0 2 2 0 ∧
    HBS CapacityWitness.tmσ L0 CapacityWitness.tmLbls (.step 0) (.step 2) ∧
    ClassN L0 (MutexReal.NonRegression.s3σ 7) (MutexReal.NonRegression.s3σ 8)
      (.spawn 0 [6] [(none, 0)]) 8 ∧
    IsFrontier KA MutexReal.NonRegression.s3σ MutexReal.NonRegression.s3Lbls 7 9 8 7 ∧
    HBS MutexReal.NonRegression.s3σ L0 MutexReal.NonRegression.s3Lbls (.step 7) (.step 9) ∧
    ClassC (HandoffExtWitness.svσ 4) (HandoffExtWitness.svσ 5) 4 ∧
    IsFrontier K0 HandoffExtWitness.svσ HandoffExtWitness.svLbls 4 5 4 4 := by
  decide

/-- `(spawnVal, N)`: the by-value `spawn` of S4 with a second local of the child, which is no
destination (WC5.3 C5 phase 1: created `Uninit`). -/
def vn5 : SC := spawnValEff Traces.q4 0 [] [(none, 0), (none, 0)] [(1, 4)]
/-- `c1 : write3(L)` via `root_L` (authority 5), `L` the second local of the child (O10). -/
def vn6 : SC := vn5.set (write3Eff (vn5.view 1) [5])

/-- The labels of the `(spawnVal, N)` witness. -/
def vnLbls : List Label :=
  [.kernel 0 (.enter [] [(none, 0), (none, 0)]), .kernel 0 (.write 1 [1]),
   .kernel 0 (.write 2 [2]), .kernel 0 (.alloc 2 1 [(none, 0)]),
   .spawnVal 0 [] [(none, 0), (none, 0)] [(1, 4)], .kernel 1 (.write 5 [5])]

/-- The named states of the `(spawnVal, N)` witness. -/
def vnσ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(Traces.q0, [], []), (Traces.q1, [], []), (Traces.q2, [], []), (Traces.q3, [], []),
    (Traces.q4, [], []), (vn5, [], []), (vn6, [], [])].getD i (vn6, [], [])

/-- Brief, task 4, `(spawnVal, N)`: the trace is a `RunFull` from the initial state; the local `5`
of the child is created `Uninit` by the by-value `spawn` (class N), the child writes it; the pair
`(4, 5, 5)` is an extended exclusive pair whose frontier is the by-value `spawn` itself, ordered by
the creation edge. -/
theorem spawnVal_N_witness : RunFull K0 L0 vnσ vnLbls ∧
    ClassN L0 (vnσ 4) (vnσ 5) (.spawnVal 0 [] [(none, 0), (none, 0)] [(1, 4)]) 5 ∧
    ExtPair K0 L0 vnσ vnLbls 4 5 5 ∧ IsFrontier K0 vnσ vnLbls 4 5 5 4 ∧
    HBS vnσ L0 vnLbls (.step 4) (.step 5) := by
  obtain ⟨e0, w1, w2, a3, -, -⟩ := Traces.s4_steps
  have sv : SpawnValStep K0 Traces.q4 0 [] [(none, 0), (none, 0)] [(1, 4)] (.ok vn5) :=
    ⟨by decide, .ok (by decide)⟩
  have s2 : opStepC K0 (.write 5 [5]) 1 vn5 (.ok vn6) := ⟨by decide, _, .ok (by decide), rfl⟩
  have h : Steps5R K0 L0 [(Traces.q0, [], []), (Traces.q1, [], []), (Traces.q2, [], []),
      (Traces.q3, [], []), (Traces.q4, [], []), (vn5, [], []), (vn6, [], [])] vnLbls :=
    .cons (by decide) (.kernel e0) <| .cons (by decide) (.kernel w1) <|
    .cons (by decide) (.kernel w2) <| .cons (by decide) (.kernel a3) <|
    .cons (by decide) (.spawnVal sv) <| .cons (by decide) (.kernel s2) .nil
  exact ⟨runFull_of_run7 (run7_of_run5R (h.run _) (by decide)) (by decide), by decide,
    by decide, by decide, by decide⟩

/-! ## The suggested counterexample to `hb(i, j)` when `r = i` -/

/-- From `MX₄`: `c0 : o2 := derive(root_M, Observe, {slot, lock})`, authority 5 (O1). -/
def hq5 : SC := x4.set (deriveEff (x4.view 0) 0 [1, 2] .observe)
/-- `c0 : spawn c2` yielding `o2`, with a local `L` (place 7, root authority 6) in the initial
frame 2 of `c2` (WC5.3 C4): the step `i` creating `l = L`. -/
def hq6 : SC := spawnEff hq5 0 [5] [(none, 0)]
/-- `c2 : z := derive(root_L, Modify, {L})`, authority 7 (O1). -/
def hq7 : SC := hq6.set (deriveEff (hq6.view 2) 6 [7] .modify)
/-- `c2 : acquire(e)` (WC5.3 C16): grant 8, held by frame 2. -/
def hq8 : SC := deriveSyncEff hq7 2 3
/-- The registry with the grant of `c2` recorded. -/
def hqReg : SyncReg := [⟨3, some 8⟩]

/-- The labels of the suggested construction up to the acquisition by `c2`. -/
def hqLbls : List Label :=
  [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 3 1), .newMutex 0 3,
   .kernel 0 (.derive 0 [1, 2] .observe), .spawn 0 [4] [], .kernel 0 (.derive 0 [1, 2] .observe),
   .spawn 0 [5] [(none, 0)], .kernel 2 (.derive 6 [7] .modify), .acquire 2 0]

/-- The named states of the suggested construction. -/
def hqσ (i : Nat) : SC × SyncReg × ArenaReg :=
  [(x0, [], []), (x1, [], []), (x2, [], []), (x2, regX, []), (x3, regX, []), (x4, regX, []),
    (hq5, regX, []), (hq6, regX, []), (hq7, regX, []), (hq8, hqReg, [])].getD i (hq8, hqReg, [])

/-- Brief, task 4, "Piste de contre-exemple": the construction suggested by the brief, in which a
context existing before step `i` would reach a leaf created by step `i` through an authority kept
in data protected by a mutex, does not get past the kernel. From `MX₄`, `c0` spawns `c2` with a
local `L` (step `i`), `c2` derives `z` over `L` and acquires the mutex: these steps form a
`RunFull` from the initial state. Then `c2 : store(z, T)` is `reject`: the effective anchor of `z`
is `root_L`, in the initial frame of `c2`, which is no ancestor of the frame of `T` (Spec 1 §65.4,
`AnchorOrder`). -/
theorem hint_store_rejected : RunFull KM L0 hqσ hqLbls ∧
    opStepC KM (.store 7 3) 2 hq8 .reject ∧ ¬ EffAnchorOKC hq8 7 ((hq8.view 2).pframe 3) := by
  have d5 : opStepC KM (.derive 0 [1, 2] .observe) 0 x4 (.ok hq5) :=
    ⟨by decide, _, .ok (by decide), rfl⟩
  have s6 : SpawnStep hq5 0 [5] [(none, 0)] (.ok hq6) := ⟨by decide, .ok (by decide)⟩
  have d7 : opStepC KM (.derive 6 [7] .modify) 2 hq6 (.ok hq7) :=
    ⟨by decide, _, .ok (by decide), rfl⟩
  have a8 : AcquireOk KM L0 hq7 regX 2 0 (hq8, hqReg) :=
    ⟨by decide, ⟨3, none⟩, rfl, by decide, by decide, rfl⟩
  have h : Steps5R KM L0 [(x2, regX, []), (x3, regX, []), (x4, regX, []), (hq5, regX, []),
      (hq6, regX, []), (hq7, regX, []), (hq8, hqReg, [])]
      [.kernel 0 (.derive 0 [1, 2] .observe), .spawn 0 [4] [],
        .kernel 0 (.derive 0 [1, 2] .observe), .spawn 0 [5] [(none, 0)],
        .kernel 2 (.derive 6 [7] .modify), .acquire 2 0] :=
    .cons (by decide) (.kernel mx_steps.2.2.2.2.1) <| .cons (by decide) (.spawn mx_steps.2.2.2.2.2) <|
    .cons (by decide) (.kernel d5) <| .cons (by decide) (.spawn s6) <|
    .cons (by decide) (.kernel d7) <| .cons (by decide) (.acquire a8) .nil
  exact ⟨runFull_of_run7 (run7_of_run5R ((ClassifyWitness.mx3_steps h).run _) (by decide))
    (by decide), ⟨by decide, .reject (by decide)⟩, by decide⟩

end Ern.Concurrency.FullEncap.HandoffExtSame
