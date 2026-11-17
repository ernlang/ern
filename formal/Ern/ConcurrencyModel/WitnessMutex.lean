import Ern.ConcurrencyModel.WitnessBase

/-!
# Witnesses: `join`, `acquire`, `unlock`, `resetLock`, `newMutex` (C8, C13, C15–C18)

Rows 1a–5d of the witness table of the tranche brief. States are built from the initial state of
Spec 1 §47 by `ok` steps. A rejection states its single cause: the named condition fails and
every other precondition of the clause holds in the same state; its positive twin is cited in its
docstring. Outcome classes are those of `Outcomes` (theorem 7, and `NewMutexOutcome` for C13,
"Outcome").
-/

namespace Ern.ConcurrencyModel

open Ern.MemoryModel Ern.MemoryModel.Access

/-! ## The reference mutex -/

/-- Statics (Spec 1 §47): `0` the mutex value `M`, `1` its field `slot` (`Uninit`), `2` its field
`lock` (`Init`), `3` the protected root `T` (`Init`), owned by `M`. Root authorities: `0` of `M`
(frame 0), `1` of `T` (held by `M`). -/
def mutexStatics : Statics :=
  [((none, none, 0), false), ((some 0, none, 0), false), ((some 0, none, 0), true),
   ((none, some 0, 0), true)]

/-- The statics are well formed (Spec 1 §47). -/
theorem mutexStatics_ok : StaticsOK mutexStatics := by decide

/-- The contract of the mutex witnesses: the controller `lock` (place 2) is the only
`SharedMutable` leaf, of discipline `Atomic(4, 4)` (C35: one discipline for each applicable
`SharedMutable` leaf). -/
abbrev kMutex : KShared := testKS [2] (fun l => if l = 2 then some (.atomic 4 4) else none) false

/-- Initial single-context state (Spec 1 §47). -/
def m0 : SC := SC.ofS3 (S3.init mutexStatics)
/-- `guarded := derive(root_T, Modify, footprint(T))`, authority 2 (O1). -/
def m1 : SC := m0.set (deriveEff (m0.view 0) 1 [3] .modify)
/-- `store(guarded, slot)` (O8); `slot` becomes `Init`. -/
def m2 : SC := storeEffC m1 0 2 1
/-- The registry with the entry of `guarded`, available (C13). -/
def regFree : SyncReg := [⟨2, none⟩]
/-- `o := derive(root_M, Observe, {slot, lock})`, authority 3 (O1). -/
def m3 : SC := m2.set (deriveEff (m2.view 0) 0 [1, 2] .observe)
/-- `spawn` of context 1 yielding `o` (C4): initial frame 1, parent frame 0. -/
def m4 : SC := spawnEff m3 0 [3] []
/-- `acquire(e)` by context 1 (C16): the grant, authority 4, held by frame 1. -/
def m5 : SC := deriveSyncEff m4 1 2
/-- The registry recording the grant 4 (C16 effect). -/
def regTaken : SyncReg := [⟨2, some 4⟩]
/-- The release of the grant 4 by context 1 (O3): the effect of `unlock(e)` (C17), and of an
ordinary `release` of the grant. -/
def m6 : SC := prospectiveUnlock m5 1 4

/-- The construction steps of the reference mutex are `ok` (O1, O8, C13, C4, C16). -/
theorem mutex_steps : opStepC kMutex.toK (.derive 1 [3] .modify) 0 m0 (.ok m1) ∧
    opStepC kMutex.toK (.store 2 1) 0 m1 (.ok m2) ∧
    NewMutexOk kMutex.toK mutexLayout [] m2 [] 0 2 (m2, regFree) ∧
    opStepC kMutex.toK (.derive 0 [1, 2] .observe) 0 m2 (.ok m3) ∧
    SpawnStep m3 0 [3] [] (.ok m4) ∧ AcquireOk kMutex mutexLayout m4 regFree 1 0 (m5, regTaken) ∧
    UnlockOk mutexLayout m5 regTaken 1 0 (m6, regFree) :=
  ⟨⟨_, .ok (by decide), rfl⟩, (.ok (by decide)),
    ⟨by decide, rfl⟩, ⟨_, .ok (by decide), rfl⟩, (.ok (by decide)),
    ⟨⟨2, none⟩, rfl, by decide, by decide, rfl⟩,
    ⟨⟨2, some 4⟩, 4, rfl, by decide, rfl, by decide, by decide, by decide, rfl⟩⟩

/-- Non-vacuity of `EncapStep` (C22, C51.1): the construction of the reference mutex, the
`acquire(e)` of context 1 and its `unlock(e)` form an `EncapsulatedTrace` from the initial state
of Spec 1 §47 (the six requirements of C22 hold at every step). -/
theorem mutex_encapsulated : EncapsulatedTrace kMutex mutexLayout (m0, [], [])
    [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 2 1), .newMutex 0 2,
     .kernel 0 (.derive 0 [1, 2] .observe), .spawn 0 [3] [], .acquire 1 0, .unlock 1 0]
    (m6, regFree, []) :=
  .cons ⟨by unfold RestrictedStep; decide, by decide, by decide⟩ (.kernel mutex_steps.1) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide, by decide⟩ (.kernel mutex_steps.2.1) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide, by decide⟩
    (.newMutex (st' := (m2, regFree)) mutex_steps.2.2.1) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide, by decide⟩ (.kernel mutex_steps.2.2.2.1) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide, by decide⟩
    (.spawn mutex_steps.2.2.2.2.1) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide, by decide⟩
    (.acquire (st' := (m5, regTaken)) mutex_steps.2.2.2.2.2.1) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide, by decide⟩
    (.unlock (st' := (m6, regFree)) mutex_steps.2.2.2.2.2.2) .nil

/-- C22 ("It is not implied by structural exclusivity I1 alone"): from the constructed mutex,
context 1 takes a raw `deriveSync(guarded)`, `ok` under the library instantiation of
`SyncAuthorized` (C15) and excluded by C22.2 (`RestrictedStep`). The resulting state satisfies
`I1` (Spec 1 §50) while the entry records `grant = none` and an active descendant covers `T`:
`GrantDiscipline` fails. -/
theorem grantDiscipline_not_of_i1 :
    DeriveSyncStep (libKC kMutex mutexLayout) regFree m4 1 2 (.ok m5) ∧
    ¬ RestrictedStep mutexLayout (m4, regFree, []) (.deriveSync 1 2) ∧ I1 m5.flat ∧
    ¬ GrantDiscipline m5 regFree :=
  ⟨(.ok (by decide)), by unfold RestrictedStep; decide, by decide,
    by unfold GrantDiscipline; decide⟩

/-! ## `join` (C8) -/

/-- Context 1 terminates (C7). -/
def mJ : SC := termEffC m4 1

/-- Context 0 spawns context 2 after the termination of context 1 (C4): context 1 is
terminated, context 2 is live. -/
def mJ2 : SC := spawnEff mJ 0 [] []

/-- **Witness 1a, C8** (`reject`): `join` of an identifier unknown to the execution (no context
`2`), requested by the live context 0. Single cause: the identifier is unknown; the requester is
live. Positive twin: `witness_1c`. -/
theorem witness_1a : m4.Live 0 ∧ m4.C[2]? = none ∧ JoinReject m4 0 2 ∧ JoinStep m4 0 2 .reject :=
  ⟨by decide, by decide, .inr (by decide), .unknown (by decide)⟩

/-- **Witness 1b, C8** (legal, not enabled, no transition): `join` of the live context 1,
requested by the live context 0: no outcome and no labelled step. -/
theorem witness_1b : JoinNotEnabled m4 0 1 ∧ (∀ o, ¬ JoinStep m4 0 1 o) ∧
    ∀ st', ¬ LStep kMutex mutexLayout (.join 0 1) (m4, regFree, []) st' := by
  have hn : JoinNotEnabled m4 0 1 := by unfold JoinNotEnabled; decide
  have hno := ((join_classes (s := m4) (c := 0) (d := 1)).2.2.2.1 hn)
  refine ⟨hn, hno, fun st' h => ?_⟩
  cases h with
  | join h => exact hno _ h

/-- **Witness 1c, C8** (`ok`, state unchanged): `join` of context 1 after its termination,
requested by the live context 0. -/
theorem witness_1c : TermStep kMutex.toK m4 1 (.ok mJ) ∧ JoinOkClass mJ 0 1 ∧
    LStep kMutex mutexLayout (.join 0 1) (mJ, regFree, []) (mJ, regFree, []) :=
  ⟨(.ok (by decide)), by unfold JoinOkClass; decide, .join (.ok (by decide) (by decide))⟩

/-- **Witness 1d, C8, "Requesting-context validity"** (`reject`): `join` of the terminated context
1, requested by context 1 itself after its termination. Single cause: the requester is not live;
the target has the completed lifecycle state, so a live requester obtains `ok`. No labelled step.
Positive twin: `witness_1c`. -/
theorem witness_1d : ¬ mJ.Live 1 ∧ OptP (mJ.C[1]?) (fun x => x.life = .done) False ∧
    JoinReject mJ 1 1 ∧ JoinStep mJ 1 1 .reject ∧
    ∀ st', ¬ LStep kMutex mutexLayout (.join 1 1) (mJ, regFree, []) st' :=
  have hc : ¬ mJ.Live 1 := by decide
  ⟨hc, by decide, .inl hc, .deadRequester hc, fun _ h => hc (lstep_live h)⟩

/-- **Witness 1e, C8, "Requesting-context validity"** (`reject`): `join` of the live context 2,
requested by the terminated context 1. Single cause: the requester is not live; the target is
live. No labelled step. Positive twin: the same target joined by the live context 0, legal and not
enabled, with no outcome. -/
theorem witness_1e : SpawnStep mJ 0 [] [] (.ok mJ2) ∧ ¬ mJ2.Live 1 ∧
    OptP (mJ2.C[2]?) (fun x => x.life = .live) False ∧ JoinReject mJ2 1 2 ∧
    JoinStep mJ2 1 2 .reject ∧
    (∀ st', ¬ LStep kMutex mutexLayout (.join 1 2) (mJ2, regFree, []) st') ∧
    JoinNotEnabled mJ2 0 2 ∧ ∀ o, ¬ JoinStep mJ2 0 2 o :=
  have hc : ¬ mJ2.Live 1 := by decide
  have hn : JoinNotEnabled mJ2 0 2 := by unfold JoinNotEnabled; decide
  ⟨.ok (by decide), hc, by decide, .inl hc, .deadRequester hc, fun _ h => hc (lstep_live h), hn,
    (join_classes (s := mJ2) (c := 0) (d := 2)).2.2.2.1 hn⟩

/-- **Witness, C4.1** (`reject`): `spawn` with one local, requested by context 1 after its
termination. Single cause: C4.1 fails (context 1 is not live and has no current frame, C2); C4.3
(no parameter), C4.5 (shape of the locals, origin protection, `AnchorOrderHeld` in the final state)
hold. Outcome `reject`, no labelled step. Positive twin: the same request by the live context 0,
`ok`. -/
theorem witness_spawn_terminated : ¬ mJ.Live 1 ∧ mJ.stk 1 = [] ∧
    (∀ a ∈ ([] : List Nat), OptP ((mJ.view 1).A[a]?) (fun y => y.active = true ∧
      y.holder = .frame (mJ.view 1).top ∧ y.origin ≠ none) False) ∧
    ShapeOK mJ.P.length (LocalShape.toShape [(none, 0)]) ∧
    (∀ p ∈ ([] : List Nat), ParamOriginHidden ((spawnEff mJ 1 [] [(none, 0)]).view mJ.C.length) p) ∧
    AnchorOrderHeldC (spawnEff mJ 1 [] [(none, 0)]) ∧
    SpawnStep mJ 1 [] [(none, 0)] .reject ∧
    (∀ st', ¬ LStep kMutex mutexLayout (.spawn 1 [] [(none, 0)]) (mJ, regFree, []) st') ∧
    LStep kMutex mutexLayout (.spawn 0 [] [(none, 0)]) (mJ, regFree, [])
      (spawnEff mJ 0 [] [(none, 0)], regFree, []) :=
  have hc : ¬ mJ.Live 1 := by decide
  ⟨hc, by decide, by decide, by decide, by decide, by decide,
    (dead_requests_reject (ks := kMutex) (L := mutexLayout) (reg := regFree) (ar := []) hc).2.1 _ _,
    fun _ h => by cases h with | spawn h => exact hc (spawnStep_live h),
    .spawn (.ok (by decide))⟩

/-! ## Rows 2a–2e: `acquire` (C15, C16) -/

/-- **Row 2a** (C15, C16.3, `ok`): `acquire(e)` by context 1 from `m4`: the entry is live,
`grant = none` (C14.1, C14.2), the requester has the controller-access right (C14.3, through
`o`), and the preconditions of `deriveSync` hold (C15.1–C15.6). The controller acquisition under
its protocol is a realization obligation not represented in `S_C` (C16: C41, C48, C49, `OB-C05`);
the abstract step is `ProtocolStepOf` the entry (C22.4) and is an `EncapStep`. -/
theorem witness_2a : EntryAuth mutexLayout m4 ⟨2, none⟩ (m4.view 1).top ∧
    DeriveSyncPre (libKC kMutex mutexLayout) regFree m4 1 2 ∧ AcquireOkClass mutexLayout m4 regFree 1 0 ∧
    LStep kMutex mutexLayout (.acquire 1 0) (m4, regFree, []) (m5, regTaken, []) ∧
    EncapStep kMutex mutexLayout (m4, regFree, []) (.acquire 1 0) (m5, regTaken, []) :=
  ⟨by decide, by decide, (acquireOk_iff.1 mutex_steps.2.2.2.2.2.1).1,
    .acquire (st' := (m5, regTaken)) mutex_steps.2.2.2.2.2.1,
    ⟨by unfold RestrictedStep; decide, by decide, by decide⟩⟩

/-- **Row 2b** (C16.2, not enabled): the request of context 0 is legal and the recorded grant 4 is
active: no outcome, no labelled step. -/
theorem witness_2b : m5.flat.Active 4 ∧ AcquireNotEnabled mutexLayout m5 regTaken 0 0 ∧
    (∀ o, ¬ AcquireOutcome kMutex mutexLayout m5 regTaken 0 0 o) ∧
    ∀ st', ¬ LStep kMutex mutexLayout (.acquire 0 0) (m5, regTaken, []) st' := by
  have hn : AcquireNotEnabled mutexLayout m5 regTaken 0 0 := by
    refine ⟨⟨⟨2, some 4⟩, rfl, by decide, by decide, by unfold AcquireIndependent; decide,
      fun h => by cases h⟩, ⟨2, some 4⟩, rfl, by decide⟩
  exact ⟨by decide, hn,
    ((acquire_classes (ks := kMutex) (ar := []) (s := m5) (reg := regTaken) (c := 0) (i := 0)).2.2.1 hn)⟩

/-- `g′ := derive(grant, Modify, footprint(T))` by context 1, authority 5 (O1). -/
def m5d : SC := m5.set (deriveEff (m5.view 1) 4 [3] .modify)
/-- Context 1 enters frame 2 yielding the grant 4 (O6). -/
def m5e : SC := enterEffC m5d 1 [4] []
/-- Context 1 exits frame 2 (O7, C6): the grant 4 dies with it; `g′`, held by frame 1, survives,
re-anchored on `guarded`. -/
def m5x : SC := exitEffC m5e 1

/-- **Row 2c** (C16.2, not enabled): after a frame exit, the recorded grant 4 is inactive while its
derived authority `g′` survives and covers `T`; the request of context 0 is legal: no outcome, no
labelled step. -/
theorem witness_2c : opStepC kMutex.toK (.derive 4 [3] .modify) 1 m5 (.ok m5d) ∧
    opStepC kMutex.toK (.enter [4] []) 1 m5d (.ok m5e) ∧ opStepC kMutex.toK .exit 1 m5e (.ok m5x) ∧
    ¬ m5x.flat.Active 4 ∧ m5x.flat.Active 5 ∧ 3 ∈ m5x.flat.afp 5 ∧
    AcquireNotEnabled mutexLayout m5x regTaken 0 0 ∧
    (∀ o, ¬ AcquireOutcome kMutex mutexLayout m5x regTaken 0 0 o) ∧
    ∀ st', ¬ LStep kMutex mutexLayout (.acquire 0 0) (m5x, regTaken, []) st' := by
  have hn : AcquireNotEnabled mutexLayout m5x regTaken 0 0 := by
    refine ⟨⟨⟨2, some 4⟩, rfl, by decide, by decide, by unfold AcquireIndependent; decide,
      fun h => by cases h⟩, ⟨2, some 4⟩, rfl, by decide⟩
  exact ⟨⟨_, .ok (by decide), rfl⟩, (.ok (by decide)),
    (.ok (by decide)), by decide, by decide, by decide, hn,
    ((acquire_classes (ks := kMutex) (ar := []) (s := m5x) (reg := regTaken) (c := 0) (i := 0)).2.2.1 hn)⟩

/-- Context 0 enters frame 2 without parameter (O6): it holds no authority there. -/
def m5f : SC := enterEffC m5 0 [] []

/-- **Row 2d** (C16.1 and precedence, `reject`): while the grant 4 is taken, context 0 from a
frame without controller-access right requests `acquire(e)`. Single cause: C14.3 fails; the entry
is live and the conditions of `AcquireIndependent` hold. Twin: row 2b, the same request from
frame 0, which has the right: legal, not enabled. -/
theorem witness_2d : opStepC kMutex.toK (.enter [] []) 0 m5 (.ok m5f) ∧
    (⟨2, some 4⟩ : SyncEntry).Live m5f ∧ ¬ CtrlRight mutexLayout m5f ⟨2, some 4⟩ (m5f.view 0).top ∧
    AcquireIndependent m5f 0 2 ∧ AcquireReject mutexLayout m5f regTaken 0 0 ∧
    AcquireOutcome kMutex mutexLayout m5f regTaken 0 0 .reject :=
  have hr : AcquireReject mutexLayout m5f regTaken 0 0 :=
    acquire_reject_precedence (e := ⟨2, some 4⟩) rfl (by decide)
  ⟨(.ok (by decide)), by decide, by decide, by unfold AcquireIndependent; decide, hr,
    .reject hr⟩

/-! ## Rows 3a–3d: `unlock` (C17) -/

/-- **Row 3a** (C17, C17.4, `ok`): `unlock(e)` by context 1, holder of the active grant 4:
C17.1 (live entry, `grant = some 4`), C17.2 and C17.3 (`ReleasePre`, O3), C17.4 (the
controller-access right through `o` before the step and in the prospective state). -/
theorem witness_3a : UnlockPre mutexLayout m5 regTaken 1 0 ∧
    LStep kMutex mutexLayout (.unlock 1 0) (m5, regTaken, []) (m6, regFree, []) :=
  ⟨⟨⟨2, some 4⟩, 4, rfl, by decide, rfl, by decide, by decide, by decide⟩,
    .unlock (st' := (m6, regFree)) mutex_steps.2.2.2.2.2.2⟩

/-- **Row 3b** (C17, `reject`): the recorded grant 4 has become inactive by an ordinary `release`
(O3; C18: "inherited legal release"). Single cause: the activity of C17.2 fails; the entry is live
and records `grant = some 4`, the other conditions of O3 hold (derived, holder right, no active
descendant, no anchor), and C17.4 holds before the step and in the prospective state. Positive
twin: row 3a. -/
theorem witness_3b : opStepC kMutex.toK (.release 4) 1 m5 (.ok m6) ∧
    (⟨2, some 4⟩ : SyncEntry).Live m6 ∧ ¬ (m6.view 1).Active 4 ∧
    OptP ((m6.view 1).A[4]?) (fun y => y.origin ≠ none) False ∧
    OptP ((m6.view 1).A[4]?) (fun y => HolderRight (m6.view 1) y.holder) False ∧
    (∀ j ∈ List.range (m6.view 1).A.length, 4 ∈ (m6.view 1).ancs j → ¬ (m6.view 1).Active j) ∧
    (∀ q ∈ List.range (m6.view 1).P.length, (m6.view 1).Usable q → 4 ∈ (m6.view 1).D q →
      ((m6.view 1).A[4]?).map (·.holder) = some (.place q)) ∧
    CtrlRight mutexLayout m6 ⟨2, some 4⟩ (m6.view 1).top ∧
    CtrlRight mutexLayout (prospectiveUnlock m6 1 4) ⟨2, some 4⟩ (m6.view 1).top ∧
    UnlockOutcome mutexLayout m6 regTaken 1 0 .reject :=
  ⟨⟨_, .ok (by decide), rfl⟩, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, .reject fun ⟨e, g, he, _, hg, hrel, _⟩ => by
      cases he; cases hg; exact (by decide : ¬ ReleasePre (m6.view 1) 4) hrel⟩

/-- `o′ := derive(root_M, Observe, {lock})` by context 0 from the constructed mutex, authority 3
(O1). -/
def n3 : SC := m2.set (deriveEff (m2.view 0) 0 [2] .observe)
/-- `spawn` of context 1 yielding `o′` (C4). -/
def n4 : SC := spawnEff n3 0 [3] []
/-- `acquire(e)` by context 1 (C16): the grant 4, held by frame 1. -/
def n5 : SC := deriveSyncEff n4 1 2
/-- `store(o′, T)` by context 1 (O8, through the grant): `o′` becomes held by the protected leaf. -/
def n6 : SC := storeEffC n5 1 3 3
/-- `o″ := derive(o′, Observe, {lock})` by context 1, authority 5, held by frame 1 (O1). -/
def n7 : SC := n6.set (deriveEff (n6.view 1) 3 [2] .observe)

/-- **Row 3c** (C17.4, `reject`): context 1 reaches the controller only through `o′`, held by the
protected leaf `T` and exercisable through the grant: the right does not survive the release of
the grant. Single cause: the prospective right of C17.4 fails; C17.1–C17.3 and the right before
the step hold. Positive twin: row 3d. -/
theorem witness_3c : opStepC kMutex.toK (.derive 0 [2] .observe) 0 m2 (.ok n3) ∧
    SpawnStep n3 0 [3] [] (.ok n4) ∧ AcquireOk kMutex mutexLayout n4 regFree 1 0 (n5, regTaken) ∧
    opStepC kMutex.toK (.store 3 3) 1 n5 (.ok n6) ∧
    (⟨2, some 4⟩ : SyncEntry).Live n6 ∧ ReleasePre (n6.view 1) 4 ∧
    CtrlRight mutexLayout n6 ⟨2, some 4⟩ (n6.view 1).top ∧
    ¬ CtrlRight mutexLayout (prospectiveUnlock n6 1 4) ⟨2, some 4⟩ (n6.view 1).top ∧
    UnlockOutcome mutexLayout n6 regTaken 1 0 .reject :=
  ⟨⟨_, .ok (by decide), rfl⟩, (.ok (by decide)),
    ⟨⟨2, none⟩, rfl, by decide, by decide, rfl⟩, (.ok (by decide)),
    by decide, by decide, by decide, by decide, .reject fun ⟨e, g, he, _, hg, _, _, hp⟩ => by
      cases he; cases hg
      exact (by decide : ¬ CtrlRight mutexLayout (prospectiveUnlock n6 1 4) ⟨2, some 4⟩
        (n6.view 1).top) hp⟩

/-- **Row 3d** (C17.4, `ok`): as row 3c, after context 1 has obtained `o″ := derive(o′, Observe,
{lock})`, held by its frame, a controller-access right independent of the grant. -/
theorem witness_3d : opStepC kMutex.toK (.derive 3 [2] .observe) 1 n6 (.ok n7) ∧
    UnlockPre mutexLayout n7 regTaken 1 0 ∧
    LStep kMutex mutexLayout (.unlock 1 0) (n7, regTaken, [])
      (prospectiveUnlock n7 1 4, regFree, []) :=
  ⟨⟨_, .ok (by decide), rfl⟩,
    ⟨⟨2, some 4⟩, 4, rfl, by decide, rfl, by decide, by decide, by decide⟩,
    .unlock (st' := (prospectiveUnlock n7 1 4, regFree))
      ⟨⟨2, some 4⟩, 4, rfl, by decide, rfl, by decide, by decide, by decide, rfl⟩⟩

/-! ## Rows 4a–4d: `resetLock` (C18) -/

/-- Context 1 terminates while holding the grant 4, without `unlock` (C7; C18: frame exit): the
grant is abandoned. -/
def mA : SC := termEffC m5 1

/-- **Row 4a** (C18, `ok`): `resetLock(e)` by context 0 on the abandoned grant 4, inactive, with no
active descendant: C18.1 (`ExercisableAt(guarded, Modify)` through `root_M` over `slot`), C18.2
(no covering active descendant), C18.3 (usable controller leaf), C18.4 (controller-access right
through `root_M`). -/
theorem witness_4a : TermStep kMutex.toK m5 1 (.ok mA) ∧ ¬ mA.flat.Active 4 ∧
    ResetLockPre mutexLayout mA regTaken 0 0 ∧
    LStep kMutex mutexLayout (.resetLock 0 0) (mA, regTaken, []) (mA, regFree, []) :=
  ⟨(.ok (by decide)), by decide,
    ⟨⟨2, some 4⟩, rfl, by decide, by decide, by decide, by decide⟩,
    .resetLock (st' := (mA, regFree)) ⟨⟨2, some 4⟩, rfl, by decide, by decide, by decide,
      by decide, rfl⟩⟩

/-- **Row 4b** (C18, `ok`): `resetLock(e)` by context 0 while `grant = none`: C18.1–C18.4 hold as
in row 4a; no prerequisite on the recorded grant (C18). -/
theorem witness_4b : ResetLockPre mutexLayout m2 regFree 0 0 ∧
    LStep kMutex mutexLayout (.resetLock 0 0) (m2, regFree, []) (m2, regFree, []) :=
  ⟨⟨⟨2, none⟩, rfl, by decide, by decide, by decide, by decide⟩,
    .resetLock (st' := (m2, regFree)) ⟨⟨2, none⟩, rfl, by decide, by decide, by decide,
      by decide, rfl⟩⟩

/-- `acquire(e)` by context 0 (C16): the grant 3, held by frame 0. -/
def mG : SC := deriveSyncEff m2 0 2
/-- The registry recording the grant 3. -/
def regG : SyncReg := [⟨2, some 3⟩]

/-- **Row 4c** (C18.2, `reject`): the active grant 3, a descendant of `guarded`, covers `T`. Single
cause: C18.2 fails; C18.1, C18.3 and C18.4 hold. Positive twin: row 4b. -/
theorem witness_4c : AcquireOk kMutex mutexLayout m2 regFree 0 0 (mG, regG) ∧
    ¬ NoCoveringDesc mG 2 ∧ (mG.view 0).ExercisableAt 2 .modify ∧
    OptP (ControlOf mutexLayout mG ⟨2, some 3⟩) (fun ctl => mG.flat.Usable ctl ∧ isLeaf mG.P ctl)
      False ∧
    CtrlRight mutexLayout mG ⟨2, some 3⟩ (mG.view 0).top ∧
    ResetLockOutcome mutexLayout mG regG 0 0 .reject :=
  ⟨⟨⟨2, none⟩, rfl, by decide, by decide, rfl⟩, by decide, by decide, by decide,
    by decide, .reject (by unfold ResetLockPre; decide)⟩

/-- `s := derive(root_M, Modify, {slot})` by context 0, authority 3 (O1). -/
def mR1 : SC := m2.set (deriveEff (m2.view 0) 0 [1] .modify)
/-- Context 0 enters frame 1 yielding `s` (O6). -/
def mR2 : SC := enterEffC mR1 0 [3] []
/-- `s′ := derive(root_M, Modify, {slot, lock})` by context 0, authority 3 (O1). -/
def mT1 : SC := m2.set (deriveEff (m2.view 0) 0 [1, 2] .modify)
/-- Context 0 enters frame 1 yielding `s′` (O6). -/
def mT2 : SC := enterEffC mT1 0 [3] []

/-- **Row 4d** (C18.4, `reject`): from frame 1, which holds `s` over `slot` only, `resetLock(e)`
by context 0. Single cause: C18.4 fails; C18.1 (through `s` over `slot`), C18.2 and C18.3 hold.
Positive twin: the same with `s′` over `slot` and `lock`, `ok`. -/
theorem witness_4d : opStepC kMutex.toK (.derive 0 [1] .modify) 0 m2 (.ok mR1) ∧
    opStepC kMutex.toK (.enter [3] []) 0 mR1 (.ok mR2) ∧
    (mR2.view 0).ExercisableAt 2 .modify ∧ NoCoveringDesc mR2 2 ∧
    OptP (ControlOf mutexLayout mR2 ⟨2, none⟩) (fun ctl => mR2.flat.Usable ctl ∧ isLeaf mR2.P ctl)
      False ∧
    ¬ CtrlRight mutexLayout mR2 ⟨2, none⟩ (mR2.view 0).top ∧
    ResetLockOutcome mutexLayout mR2 regFree 0 0 .reject ∧
    opStepC kMutex.toK (.derive 0 [1, 2] .modify) 0 m2 (.ok mT1) ∧
    opStepC kMutex.toK (.enter [3] []) 0 mT1 (.ok mT2) ∧
    ResetLockPre mutexLayout mT2 regFree 0 0 ∧
    LStep kMutex mutexLayout (.resetLock 0 0) (mT2, regFree, []) (mT2, regFree, []) :=
  ⟨⟨_, .ok (by decide), rfl⟩, (.ok (by decide)), by decide, by decide,
    by decide, by decide, .reject (by unfold ResetLockPre; decide),
    ⟨_, .ok (by decide), rfl⟩, (.ok (by decide)),
    ⟨⟨2, none⟩, rfl, by decide, by decide, by decide, by decide⟩,
    .resetLock (st' := (mT2, regFree)) ⟨⟨2, none⟩, rfl, by decide, by decide, by decide,
      by decide, rfl⟩⟩

/-! ## Row 2e: `acquire` of an absent or dead entry (C16.1)

The dead entry is built from the abandoned grant of row 4a. -/

/-- `release(guarded)` by context 0 after the grant 4 was abandoned (O3): the entry dies, the
registry still recording `grant = some 4`. -/
def mD : SC := mA.set (releaseEff (mA.view 0) 2)

/-- **Row 2e** (C16.1, `reject`): `acquire` of an absent entry (index 1 of a one-entry registry),
then of a dead entry (`guarded` released, `grant = some 4` still recorded). Single cause for the
dead entry: C14.1 fails; the controller-access right (C14.3) and the conditions of
`AcquireIndependent` hold, and the recorded grant puts the grant-sensitive conditions out of
`reject` (C16.1). Positive twin: row 2a. -/
theorem witness_2e : regFree[1]? = none ∧ AcquireReject mutexLayout m4 regFree 1 1 ∧
    AcquireOutcome kMutex mutexLayout m4 regFree 1 1 .reject ∧
    opStepC kMutex.toK (.release 2) 0 mA (.ok mD) ∧ ¬ (⟨2, some 4⟩ : SyncEntry).Live mD ∧
    CtrlRight mutexLayout mD ⟨2, some 4⟩ (mD.view 0).top ∧ AcquireIndependent mD 0 2 ∧
    AcquireReject mutexLayout mD regTaken 0 0 ∧
    AcquireOutcome kMutex mutexLayout mD regTaken 0 0 .reject :=
  have hd : AcquireReject mutexLayout mD regTaken 0 0 :=
    .inr ⟨⟨2, some 4⟩, rfl, .inl (by decide)⟩
  ⟨rfl, (.inl rfl), .reject (.inl rfl), ⟨_, .ok (by decide), rfl⟩,
    by decide, by decide, by unfold AcquireIndependent; decide, hd, .reject hd⟩

/-! ## Rows 5a–5d: `newMutex` (C13)

C13, "Outcome": `reject` when an applicable precondition fails, no `fail`
(`NewMutexOutcome`). Each rejection also shows the absence of an `ok` step, `NewMutexOk` and
`LStep` alike, with exactly the named precondition failing. -/

/-- **Row 5a** (C13, `ok`): `newMutex(guarded)` by context 0 after `store(guarded, slot)`: the
twelve preconditions C13.1–C13.11 hold (C13.11 through `root_M`, of effective mode `Modify` on
`lock`, the only authority with an effective mode there). -/
theorem witness_5a : NewMutexPre kMutex.toK mutexLayout [] m2 [] 0 2 ∧
    LStep kMutex mutexLayout (.newMutex 0 2) (m2, [], []) (m2, regFree, []) :=
  ⟨mutex_steps.2.2.1.1, .newMutex (st' := (m2, regFree)) mutex_steps.2.2.1⟩

/-- No `ok` step of `newMutex` when a precondition fails (C13). -/
theorem newMutex_none {k : KShared} {L : MutexLayout} {ar : ArenaReg} {s : SC} {reg : SyncReg}
    {c g : Nat} (h : ¬ NewMutexPre k.toK L ar s reg c g) :
    (∀ st', ¬ NewMutexOk k.toK L ar s reg c g st') ∧
      ∀ st', ¬ LStep k L (.newMutex c g) (s, reg, ar) st' :=
  ⟨fun _ h' => h h'.1, fun _ h' => by cases h' with | newMutex h' => exact h h'.1⟩

/-- **Row 5b** (C13.11, `reject`): after `o′ := derive(root_M, Observe, {lock})`, the frame of
context 0 has only `Observe` rights on the controller (`root_M` of effective mode `Observe`, `o′`).
Single cause: C13.11 fails; the eleven other preconditions hold. Positive twin: row 5a. -/
theorem witness_5b : opStepC kMutex.toK (.derive 0 [2] .observe) 0 m2 (.ok n3) ∧
    effective (n3.view 0) 0 2 = some .observe ∧ effective (n3.view 0) 3 2 = some .observe ∧
    ¬ OptP (ControlOf mutexLayout n3 ⟨2, none⟩) (fun ctl => ∃ a ∈ List.range n3.A.length,
      (n3.view 0).ExercisableAt a .modify ∧ effective (n3.view 0) a ctl = some .modify ∧
      ∀ b ∈ List.range n3.A.length, b ≠ a → effective (n3.view 0) b ctl = none) False ∧
    OptP (n3.A[2]?) (fun y => y.active = true ∧ y.mode = .modify ∧
      PlaceUsable n3.flat y.holder) False ∧
    (n3.view 0).ExercisableAt 2 .modify ∧
    OptP (ControlOf mutexLayout n3 ⟨2, none⟩) (fun ctl => n3.flat.Usable ctl ∧ isLeaf n3.P ctl)
      False ∧
    OptP (mutexOf n3 2) (fun m => ∀ l ∈ n3.flat.afp 2, l ∉ footprint n3.P m) False ∧
    OptP (mutexOf n3 2) (fun m => ∀ l ∈ footprint n3.P m, n3.I l = .init) False ∧
    OptP (n3.A[2]?) (fun y => y.origin ≠ none → StoredOK n3.P y) False ∧
    OptP (ControlOf mutexLayout n3 ⟨2, none⟩) kMutex.toK.SharedMutable False ∧
    (∀ e ∈ ([] : SyncReg), e.Live n3 → e.guarded ≠ 2) ∧
    2 ∉ Arena.liveInternals n3.flat [] ∧
    OptP (ControlOf mutexLayout n3 ⟨2, none⟩) (fun ctl => ∀ e ∈ ([] : SyncReg), e.Live n3 →
      ControlOf mutexLayout n3 e ≠ some ctl) False ∧
    NoCoveringDesc n3 2 ∧
    NewMutexOutcome kMutex.toK mutexLayout [] n3 [] 0 2 .reject ∧
    (∀ st', ¬ NewMutexOk kMutex.toK mutexLayout [] n3 [] 0 2 st') ∧
    ∀ st', ¬ LStep kMutex mutexLayout (.newMutex 0 2) (n3, [], []) st' :=
  have hn : ¬ NewMutexPre kMutex.toK mutexLayout [] n3 [] 0 2 := by decide
  ⟨⟨_, .ok (by decide), rfl⟩, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, .reject hn, (newMutex_none hn).1, (newMutex_none hn).2⟩

/-- Statics of row 5c (Spec 1 §47): `0` the mutex value `M`, `1` its field `slot` (`Init`), `2`
its field `lock` (`Init`), `3` and `4` two protected roots `T₁`, `T₂` (`Init`), both owned by
`slot`. Root authorities: `0` of `M` (frame 0), `1` of `T₁` and `2` of `T₂`, both held by `slot`.
A `store` cannot give `slot` a second active authority (Spec 1 §65.2), so both are root
authorities of the statics. -/
def mutexStatics2 : Statics :=
  [((none, none, 0), false), ((some 0, none, 0), true), ((some 0, none, 0), true),
   ((none, some 1, 0), true), ((none, some 1, 0), true)]

/-- The statics are well formed (Spec 1 §47). -/
theorem mutexStatics2_ok : StaticsOK mutexStatics2 := by decide

/-- Initial state of row 5c (Spec 1 §47). -/
def u0 : SC := SC.ofS3 (S3.init mutexStatics2)

/-- **Row 5c** (C13.8, `reject`): `root_T₂`, held by the same `slot`, has the controller `lock` of
the live entry of `root_T₁` (positional `ControlOf`, C12). Single cause: C13.8 fails; the eleven
other preconditions hold. Positive twin: the same `newMutex(root_T₂)` with an empty registry,
`ok`. -/
theorem witness_5c : NewMutexOk kMutex.toK mutexLayout [] u0 [] 0 1 (u0, [⟨1, none⟩]) ∧
    ControlOf mutexLayout u0 ⟨1, none⟩ = some 2 ∧ ControlOf mutexLayout u0 ⟨2, none⟩ = some 2 ∧
    ¬ OptP (ControlOf mutexLayout u0 ⟨2, none⟩) (fun ctl => ∀ e ∈ ([⟨1, none⟩] : SyncReg),
      e.Live u0 → ControlOf mutexLayout u0 e ≠ some ctl) False ∧
    OptP (u0.A[2]?) (fun y => y.active = true ∧ y.mode = .modify ∧
      PlaceUsable u0.flat y.holder) False ∧
    (u0.view 0).ExercisableAt 2 .modify ∧
    OptP (ControlOf mutexLayout u0 ⟨2, none⟩) (fun ctl => u0.flat.Usable ctl ∧ isLeaf u0.P ctl)
      False ∧
    OptP (mutexOf u0 2) (fun m => ∀ l ∈ u0.flat.afp 2, l ∉ footprint u0.P m) False ∧
    OptP (mutexOf u0 2) (fun m => ∀ l ∈ footprint u0.P m, u0.I l = .init) False ∧
    OptP (u0.A[2]?) (fun y => y.origin ≠ none → StoredOK u0.P y) False ∧
    OptP (ControlOf mutexLayout u0 ⟨2, none⟩) kMutex.toK.SharedMutable False ∧
    (∀ e ∈ ([⟨1, none⟩] : SyncReg), e.Live u0 → e.guarded ≠ 2) ∧
    2 ∉ Arena.liveInternals u0.flat [] ∧
    NoCoveringDesc u0 2 ∧
    OptP (ControlOf mutexLayout u0 ⟨2, none⟩) (fun ctl => ∃ a ∈ List.range u0.A.length,
      (u0.view 0).ExercisableAt a .modify ∧ effective (u0.view 0) a ctl = some .modify ∧
      ∀ b ∈ List.range u0.A.length, b ≠ a → effective (u0.view 0) b ctl = none) False ∧
    NewMutexOutcome kMutex.toK mutexLayout [] u0 [⟨1, none⟩] 0 2 .reject ∧
    (∀ st', ¬ NewMutexOk kMutex.toK mutexLayout [] u0 [⟨1, none⟩] 0 2 st') ∧
    (∀ st', ¬ LStep kMutex mutexLayout (.newMutex 0 2) (u0, [⟨1, none⟩], []) st') ∧
    NewMutexOk kMutex.toK mutexLayout [] u0 [] 0 2 (u0, [⟨2, none⟩]) :=
  have hn : ¬ NewMutexPre kMutex.toK mutexLayout [] u0 [⟨1, none⟩] 0 2 := by decide
  ⟨⟨by decide, rfl⟩, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    .reject hn, (newMutex_none hn).1, (newMutex_none hn).2, ⟨by decide, rfl⟩⟩

/-- The arena registry after `newArena(T, guarded)` by context 0 (Spec 1 §76). -/
def arT : ArenaReg := [⟨3, 2, footprint m2.P 3, []⟩]

/-- **Row 5d** (C13.7, `reject`): `guarded` is the `internal` identity of a live arena registered
by `newArena(T, guarded)` (Spec 1 §56, §76). Single cause: C13.7 fails on the arena registry; the
eleven other preconditions hold, among them the uniqueness among synchronization entries.
Positive twin: row 5a, the same request with an empty arena registry. -/
theorem witness_5d : NewArenaStepC m2 [] [] 0 3 2 (.ok (m2, arT)) ∧
    2 ∈ Arena.liveInternals m2.flat arT ∧
    OptP (m2.A[2]?) (fun y => y.active = true ∧ y.mode = .modify ∧
      PlaceUsable m2.flat y.holder) False ∧
    (m2.view 0).ExercisableAt 2 .modify ∧
    OptP (ControlOf mutexLayout m2 ⟨2, none⟩) (fun ctl => m2.flat.Usable ctl ∧ isLeaf m2.P ctl)
      False ∧
    OptP (mutexOf m2 2) (fun m => ∀ l ∈ m2.flat.afp 2, l ∉ footprint m2.P m) False ∧
    OptP (mutexOf m2 2) (fun m => ∀ l ∈ footprint m2.P m, m2.I l = .init) False ∧
    OptP (m2.A[2]?) (fun y => y.origin ≠ none → StoredOK m2.P y) False ∧
    OptP (ControlOf mutexLayout m2 ⟨2, none⟩) kMutex.toK.SharedMutable False ∧
    (∀ e ∈ ([] : SyncReg), e.Live m2 → e.guarded ≠ 2) ∧
    OptP (ControlOf mutexLayout m2 ⟨2, none⟩) (fun ctl => ∀ e ∈ ([] : SyncReg), e.Live m2 →
      ControlOf mutexLayout m2 e ≠ some ctl) False ∧
    NoCoveringDesc m2 2 ∧
    OptP (ControlOf mutexLayout m2 ⟨2, none⟩) (fun ctl => ∃ a ∈ List.range m2.A.length,
      (m2.view 0).ExercisableAt a .modify ∧ effective (m2.view 0) a ctl = some .modify ∧
      ∀ b ∈ List.range m2.A.length, b ≠ a → effective (m2.view 0) b ctl = none) False ∧
    NewMutexOutcome kMutex.toK mutexLayout arT m2 [] 0 2 .reject ∧
    (∀ st', ¬ NewMutexOk kMutex.toK mutexLayout arT m2 [] 0 2 st') ∧
    ∀ st', ¬ LStep kMutex mutexLayout (.newMutex 0 2) (m2, [], arT) st' :=
  have hn : ¬ NewMutexPre kMutex.toK mutexLayout arT m2 [] 0 2 := by decide
  ⟨(.ok (by decide)), by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, .reject hn,
    (newMutex_none hn).1, (newMutex_none hn).2⟩

end Ern.ConcurrencyModel
