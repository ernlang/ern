import Ern.ConcurrencyModel.WitnessMutex

/-!
# Corpus of the concurrency model: outcomes of the mutex protocol (test module)

Cases `R13`–`R24` of the concurrency model
(`specs/ERN_Concurrency_Model_Specification_v0.md`),
replayed on the concurrent authority machine (`LStep`). Each state is reached from the initial
state of Spec 1 §47 by `ok` steps (`LRun`); a step stated admitted is taken from a state reached by
an `EncapsulatedTrace` and satisfies `EncapStep` (C22, C51.1). Each theorem states the obtained
verdict of every step of its case: an outcome of the relation of the step (`opStepC`,
`AcquireOutcome`, `UnlockOutcome`, `ResetLockOutcome`, `NewMutexOutcome`, `IssueStepC`,
`ResetStepC`, `TermStep`, `JoinStep`); for a legal request that is not enabled, no outcome and no
labelled step (C8, C16.2). Its docstring gives the situation, the expected verdict with its clause,
the obtained verdict and the twin. This is a test module: no model module imports it.

The reference mutex is that of `WitnessMutex` (C12, C13): in frame 0, the value `M = {slot,
lock}` (places 0, 1, 2), `lock` initialized and `SharedMutable` of discipline `Atomic(4, 4)`,
`slot` `Uninit`, the protected root `T` (place 3) owned by `M`, initialized; `guarded :=
derive(root_T, Modify, footprint(T))` (authority 2), stored in `slot`, then `newMutex(guarded)`
(`m2`, entry `⟨2, none⟩`). The shared mutex adds `o1 := derive(root_M, Observe, {slot, lock})`
(authority 3) and the `spawn` of context 1 yielding `o1` (`m4`).
-/

namespace Ern.Corpus.Concurrency

open Ern.MemoryModel Ern.MemoryModel.Access Ern.ConcurrencyModel

variable {pm : ProviderMeta}

/-! ## The constructions of the reference mutex -/

/-- The construction of the reference mutex in frame 0, not shared (O1, O8, C13). -/
def refMutexL : List Label := [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 2 1), .newMutex 0 2]

/-- The construction of the reference mutex, then its sharing with context 1 (O1, C4). -/
def sharedMutexL : List Label := refMutexL ++ [.kernel 0 (.derive 0 [1, 2] .observe), .spawn 0 [3] []]

/-- The construction of the reference mutex is an `EncapsulatedTrace` from the initial state of
Spec 1 §47 (C22, C51.1). -/
theorem refMutex_encap : EncapsulatedTrace pm kMutex mutexLayout (m0, [], []) refMutexL (m2, regFree, []) :=
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩ (.kernel mutex_steps.1) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩ (.kernel mutex_steps.2.1) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩
    (.newMutex (st' := (m2, regFree)) mutex_steps.2.2.1) .nil

/-- The construction and sharing of the reference mutex is an `EncapsulatedTrace` from the initial
state of Spec 1 §47 (C22, C51.1). -/
theorem sharedMutex_encap : EncapsulatedTrace pm kMutex mutexLayout (m0, [], []) sharedMutexL (m4, regFree, []) :=
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩ (.kernel mutex_steps.1) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩ (.kernel mutex_steps.2.1) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩
    (.newMutex (st' := (m2, regFree)) mutex_steps.2.2.1) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩ (.kernel mutex_steps.2.2.2.1) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩
    (.spawn mutex_steps.2.2.2.2.1) .nil

/-- The shared reference mutex is reached by `ok` steps. -/
theorem sharedMutex_run : LRun kMutex mutexLayout (m0, [], []) sharedMutexL (m4, regFree, []) :=
  .cons (.kernel mutex_steps.1) <| .cons (.kernel mutex_steps.2.1) <|
  .cons (.newMutex (st' := (m2, regFree)) mutex_steps.2.2.1) <|
  .cons (.kernel mutex_steps.2.2.2.1) <| .cons (.spawn mutex_steps.2.2.2.2.1) .nil

/-! ## R13: a grant not yielded to the entered frame -/

/-- Context 1 enters frame 2 without parameter, holding the grant 4 in frame 1 (O6). -/
def r13s1 : SC := enterEffC m5 1 [] []
/-- `g′ := derive(g, Modify, footprint(T))` by context 1, authority 5 (O1). -/
def r13t1 : SC := m5.set (deriveEff (m5.view 1) 4 [3] .modify)
/-- Context 1 enters frame 2 yielding `g′` (O6). -/
def r13t2 : SC := enterEffC r13t1 1 [5] []

/-- **R13** (`reject`). The shared reference mutex; context 1 acquires the entry, its grant `g`
held by its frame 1; it enters frame 2 without yielding `g`; in frame 2 it writes `T` through
`g`. Expected: `reject` by O10.1 (Spec 1 §43): `g` is held by the initial frame of context 1,
neither the current frame nor a place. Obtained: the `acquire` and the `enterFrame` `ok`; the write
`reject`. Twin: `R13_twin`. -/
theorem R13 : LRun kMutex mutexLayout (m0, [], []) sharedMutexL (m4, regFree, []) ∧
    AcquireOk kMutex mutexLayout m4 regFree 1 0 (m5, regTaken) ∧
    opStepC kMutex.toK (.enter [] []) 1 m5 (.ok r13s1) ∧
    opStepC kMutex.toK (.write 4 [3]) 1 r13s1 .reject :=
  ⟨sharedMutex_run, mutex_steps.2.2.2.2.2.1, .ok (by decide), ⟨_, .reject (by decide), rfl⟩⟩

/-- **R13, twin** (`ok`). From the acquisition of `R13`: context 1 derives `g′ := derive(g,
Modify, footprint(T))`, enters frame 2 yielding `g′`, and writes `T` through `g′`. Expected: `ok`.
Obtained: each step `ok`. -/
theorem R13_twin : opStepC kMutex.toK (.derive 4 [3] .modify) 1 m5 (.ok r13t1) ∧
    opStepC kMutex.toK (.enter [5] []) 1 r13t1 (.ok r13t2) ∧
    opStepC kMutex.toK (.write 5 [3]) 1 r13t2 (.ok (r13t2.set (write3Eff (r13t2.view 1) [3]))) :=
  ⟨⟨_, .ok (by decide), rfl⟩, .ok (by decide), ⟨_, .ok (by decide), rfl⟩⟩

/-! ## R16: an abandoned grant -/

/-- `o1′ := derive(o1, Observe, {slot, lock})` by context 1, authority 4 (O1). -/
def r16s1 : SC := m4.set (deriveEff (m4.view 1) 3 [1, 2] .observe)
/-- Context 1 enters frame 2 yielding `o1′` (O6). -/
def r16s2 : SC := enterEffC r16s1 1 [4] []
/-- `acquire(e)` by context 1 from frame 2: the grant 5, held by frame 2 (C16). -/
def r16s3 : SC := deriveSyncEff r16s2 1 2
/-- The registry recording the grant 5. -/
def r16reg : SyncReg := [⟨2, some 5⟩]
/-- Step 1: context 1 exits frame 2 without `unlock` (O7): the grant 5 and `o1′` are released. -/
def r16s4 : SC := exitEffC r16s3 1
/-- `terminate` of context 1 (C7). -/
def r16t1 : SC := termEffC r16s4 1
/-- `acquire(e)` by context 0 after the recovery: the grant 6, held by frame 0 (C16). -/
def r16t2 : SC := deriveSyncEff r16t1 0 2

/-- **R16** (`ok`; not enabled; `reject`). The shared reference mutex; context 1 derives `o1′ :=
derive(o1, Observe)`, enters frame 2 yielding `o1′` and acquires the entry, its grant `g` held by
frame 2. 1. context 1 exits frame 2 without `unlock`; 2. context 0 requests `acquire(e)`; 3.
context 0 requests `resetLock(e)`. Expected: 1 `ok` by O7, releasing `g` and `o1′`; 2 not enabled
by C16.2: the recorded grant is inactive, the request legal; 3 `reject` by C18.1: `root_M` has
only an effective `Observe` on `slot` while `o1` is active. Obtained: 1 `ok`, `g` inactive and
the entry recording it; 2 legal and not enabled: no outcome and no labelled step; 3 `reject`.
Twin: `R16_twin`. -/
theorem R16 : LRun kMutex mutexLayout (m0, [], []) sharedMutexL (m4, regFree, []) ∧
    opStepC kMutex.toK (.derive 3 [1, 2] .observe) 1 m4 (.ok r16s1) ∧
    opStepC kMutex.toK (.enter [4] []) 1 r16s1 (.ok r16s2) ∧
    AcquireOk kMutex mutexLayout r16s2 regFree 1 0 (r16s3, r16reg) ∧
    opStepC kMutex.toK .exit 1 r16s3 (.ok r16s4) ∧ ¬ r16s4.flat.Active 5 ∧
    AcquireNotEnabled mutexLayout r16s4 r16reg 0 0 ∧
    (∀ o, ¬ AcquireOutcome kMutex mutexLayout r16s4 r16reg 0 0 o) ∧
    (∀ st', ¬ LStep kMutex mutexLayout (.acquire 0 0) (r16s4, r16reg, []) st') ∧
    ResetLockOutcome mutexLayout r16s4 r16reg 0 0 .reject := by
  have hn : AcquireNotEnabled mutexLayout r16s4 r16reg 0 0 :=
    ⟨⟨⟨2, some 5⟩, rfl, by decide, by decide, by unfold AcquireIndependent; decide,
      fun h => by cases h⟩, ⟨2, some 5⟩, rfl, by decide⟩
  have hc := (acquire_classes (ks := kMutex) (ar := []) (s := r16s4) (reg := r16reg) (c := 0)
    (i := 0)).2.2.1 hn
  exact ⟨sharedMutex_run, ⟨_, .ok (by decide), rfl⟩, .ok (by decide),
    ⟨⟨2, none⟩, rfl, by decide, by decide, rfl⟩, .ok (by decide), by decide, hn, hc.1, hc.2,
    .reject (by unfold ResetLockPre; decide)⟩

/-- **R16, twin** (`ok`). From step 1 of `R16`: context 1 terminates; context 0 joins it, then
requests `resetLock(e)`, then `acquire(e)`. Expected: each step `ok`. Obtained: each step `ok`. -/
theorem R16_twin : TermStep kMutex.toK r16s4 1 (.ok r16t1) ∧ JoinStep r16t1 0 1 (.ok r16t1) ∧
    ResetLockOk mutexLayout r16t1 r16reg 0 0 (r16t1, regFree) ∧
    AcquireOk kMutex mutexLayout r16t1 regFree 0 0 (r16t2, [⟨2, some 6⟩]) :=
  ⟨.ok (by decide), .ok (by decide) (by decide),
    ⟨⟨2, some 5⟩, rfl, by decide, by decide, by decide, by decide, rfl⟩,
    ⟨⟨2, none⟩, rfl, by decide, by decide, rfl⟩⟩

/-! ## R17: an `unlock` after the grant left with its frame -/

/-- Step 1: context 1 enters frame 2 yielding the grant 4 (O6). -/
def r17s1 : SC := enterEffC m5 1 [4] []
/-- Step 2: `write3(T)` by context 1 in frame 2 through the grant (O10). -/
def r17s2 : SC := r17s1.set (write3Eff (r17s1.view 1) [3])
/-- Step 3: context 1 exits frame 2 (O7): the grant is released. -/
def r17s3 : SC := exitEffC r17s2 1
/-- Twin: context 1 enters frame 2 yielding `g′` (`r13t2`), writes `T` through `g′`. -/
def r17t1 : SC := r13t2.set (write3Eff (r13t2.view 1) [3])
/-- Twin: context 1 exits frame 2 (O7): `g′` is released. -/
def r17t2 : SC := exitEffC r17t1 1

/-- **R17** (`ok`, `ok`, `ok`, `reject`). The shared reference mutex; context 1 acquires the
entry, its grant `g` held by frame 1. 1. context 1 enters frame 2 yielding `g`; 2. in frame 2 it
writes `T` through `g`; 3. it exits frame 2; 4. it requests `unlock(e)`. Expected: 1, 2 `ok`; 3
`ok`, O7 releasing `g` (Spec 1 §45); 4 `reject` by C17.2: `g` is inactive. Obtained: 1, 2, 3 `ok`,
`g` inactive after 3; 4 `reject`. Twin: `R17_twin`. -/
theorem R17 : LRun kMutex mutexLayout (m0, [], []) sharedMutexL (m4, regFree, []) ∧
    AcquireOk kMutex mutexLayout m4 regFree 1 0 (m5, regTaken) ∧
    opStepC kMutex.toK (.enter [4] []) 1 m5 (.ok r17s1) ∧
    opStepC kMutex.toK (.write 4 [3]) 1 r17s1 (.ok r17s2) ∧
    opStepC kMutex.toK .exit 1 r17s2 (.ok r17s3) ∧ ¬ r17s3.flat.Active 4 ∧
    UnlockOutcome mutexLayout r17s3 regTaken 1 0 .reject :=
  ⟨sharedMutex_run, mutex_steps.2.2.2.2.2.1, .ok (by decide), ⟨_, .ok (by decide), rfl⟩, .ok (by decide),
    by decide, .reject fun ⟨e, g, he, _, hg, hrel, _⟩ => by
      cases he; cases hg; exact (by decide : ¬ ReleasePre (r17s3.view 1) 4) hrel⟩

/-- **R17, twin** (`ok`). From the acquisition of `R17`: context 1 enters frame 2 yielding `g′ :=
derive(g, Modify, footprint(T))`, writes `T` through `g′`, exits frame 2, then requests
`unlock(e)`. Expected: `unlock` `ok`. Obtained: each step `ok`. -/
theorem R17_twin : opStepC kMutex.toK (.derive 4 [3] .modify) 1 m5 (.ok r13t1) ∧
    opStepC kMutex.toK (.enter [5] []) 1 r13t1 (.ok r13t2) ∧
    opStepC kMutex.toK (.write 5 [3]) 1 r13t2 (.ok r17t1) ∧
    opStepC kMutex.toK .exit 1 r17t1 (.ok r17t2) ∧
    UnlockOk mutexLayout r17t2 regTaken 1 0 (prospectiveUnlock r17t2 1 4, regFree) :=
  ⟨⟨_, .ok (by decide), rfl⟩, .ok (by decide), ⟨_, .ok (by decide), rfl⟩, .ok (by decide),
    ⟨⟨2, some 4⟩, 4, rfl, by decide, rfl, by decide, by decide, by decide, rfl⟩⟩

/-! ## R20: `newMutex` from a frame without right on the controller -/

/-- The setup of `R20`: steps 1 and 2 of the construction, then `s := derive(root_M, Modify,
{slot})` (authority 3) and the entry of frame 1 yielding `s` (`mR1`, `mR2` of `WitnessMutex`). -/
def r20L : List Label :=
  [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 2 1), .kernel 0 (.derive 0 [1] .modify),
   .kernel 0 (.enter [3] [])]

/-- **R20** (`reject`). Steps 1 and 2 of the construction of the reference mutex (`guarded`
derived and stored in `slot`); `s := derive(root_M, Modify, {slot})`; context 0 enters frame 1
yielding `s`; from frame 1, `newMutex(guarded)`. Expected: `reject` by C13.11: no authority
exercisable from frame 1 has an effective mode on `lock`. Obtained: `reject`. Twin: `R20_twin`. -/
theorem R20 : LRun kMutex mutexLayout (m0, [], []) r20L (mR2, [], []) ∧
    NewMutexOutcome kMutex.toK mutexLayout [] mR2 [] 0 2 .reject :=
  ⟨.cons (.kernel mutex_steps.1) <| .cons (.kernel mutex_steps.2.1) <|
    .cons (.kernel ⟨_, .ok (by decide), rfl⟩) <| .cons (.kernel (.ok (by decide))) .nil,
   .reject (by decide)⟩

/-- **R20, twin** (`ok`). From frame 0, after steps 1 and 2 of the construction,
`newMutex(guarded)`. Expected: `ok`. Obtained: `ok`. -/
theorem R20_twin : NewMutexOk kMutex.toK mutexLayout [] m2 [] 0 2 (m2, regFree) :=
  mutex_steps.2.2.1

/-! ## R24: `acquire` after a raw `deriveSync` -/

/-- **R24** (`reject`). The shared reference mutex; context 1 takes a raw `deriveSync(guarded)`
outside `acquire`, obtaining `w` (authority 4), the entry still recording `grant = none`; then
context 0 requests `acquire(e)`. Expected: `reject` by C16.1: with `grant = none`, an invalid
protected-authority invariant is `reject` (C15.4 and C15.5 fail). Obtained: the raw `deriveSync`
`ok`; the `acquire` `reject`, by the protected-authority conditions (`AcquireGrantSensitive`).
Twin: `R24_twin`. -/
theorem R24 : LRun kMutex mutexLayout (m0, [], []) sharedMutexL (m4, regFree, []) ∧
    DeriveSyncStep (libKC kMutex mutexLayout) regFree m4 1 2 (.ok m5) ∧
    ¬ AcquireGrantSensitive m5 0 2 ∧
    AcquireOutcome kMutex mutexLayout m5 regFree 0 0 .reject :=
  ⟨sharedMutex_run, grantDiscipline_not_of_i1.1, by unfold AcquireGrantSensitive; decide,
    .reject (.inr ⟨⟨2, none⟩, rfl, .inr (.inr (.inr ⟨rfl, by unfold AcquireGrantSensitive; decide⟩))⟩)⟩

/-- **R24, twin** (`ok`). After the raw `deriveSync` of `R24`: context 1 releases `w`; context 0
requests `acquire(e)`. Expected: `ok`. Obtained: both `ok`. -/
theorem R24_twin : opStepC kMutex.toK (.release 4) 1 m5 (.ok m6) ∧
    AcquireOk kMutex mutexLayout m6 regFree 0 0 (deriveSyncEff m6 0 2, [⟨2, some 5⟩]) :=
  ⟨⟨_, .ok (by decide), rfl⟩, ⟨⟨2, none⟩, rfl, by decide, by decide, rfl⟩⟩

/-! ## R14, R18 (2): two mutexes in frame 0 -/

/-- Statics of two reference mutexes (Spec 1 §47): `M1 = {slot1, lock1}` (places 0, 1, 2) with
`T1` (place 3) owned by `M1`; `M2 = {slot2, lock2}` (places 4, 5, 6) with `T2` (place 7) owned by
`M2`; the slots `Uninit`, the controllers and the protected roots `Init`. Root authorities: 0 of
`M1`, 1 of `T1` (held by `M1`), 2 of `M2`, 3 of `T2` (held by `M2`). -/
def twoMutexStatics : Statics :=
  [((none, none, 0), false), ((some 0, none, 0), false), ((some 0, none, 0), true),
   ((none, some 0, 0), true), ((none, none, 0), false), ((some 4, none, 0), false),
   ((some 4, none, 0), true), ((none, some 4, 0), true)]

/-- The contract of the two mutexes: both controllers `SharedMutable`, of discipline
`Atomic(4, 4)`. -/
abbrev kTwo : KShared :=
  testKS [2, 6] (fun l => if l = 2 ∨ l = 6 then some (.atomic 4 4) else none) (fun _ => none)

/-- Initial state (Spec 1 §47). -/
def r14s0 : SC := SC.ofS3 (S3.init twoMutexStatics)
/-- `guarded1 := derive(root_T1, Modify, footprint(T1))`, authority 4 (O1). -/
def r14s1 : SC := r14s0.set (deriveEff (r14s0.view 0) 1 [3] .modify)
/-- `store(guarded1, slot1)` (O8). -/
def r14s2 : SC := storeEffC r14s1 0 4 1
/-- `guarded2 := derive(root_T2, Modify, footprint(T2))`, authority 5 (O1). -/
def r14s3 : SC := r14s2.set (deriveEff (r14s2.view 0) 3 [7] .modify)
/-- `store(guarded2, slot2)` (O8). -/
def r14s4 : SC := storeEffC r14s3 0 5 5
/-- The registry with the two available entries. -/
def r14reg : SyncReg := [⟨4, none⟩, ⟨5, none⟩]
/-- `acquire(e1)` by context 0: the grant 6 (C16). -/
def r14s5 : SC := deriveSyncEff r14s4 0 4
/-- `acquire(e2)` by context 0: the grant 7 (C16). -/
def r14s6 : SC := deriveSyncEff r14s5 0 5

/-- The construction of the two mutexes, each as the reference mutex. -/
def r14L : List Label :=
  [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 4 1), .newMutex 0 4,
   .kernel 0 (.derive 3 [7] .modify), .kernel 0 (.store 5 5), .newMutex 0 5]

/-- The construction of the two mutexes is reached by `ok` steps (O1, O8, C13). -/
theorem r14_run : LRun kTwo mutexLayout (r14s0, [], []) r14L (r14s4, r14reg, []) :=
  .cons (.kernel ⟨_, .ok (by decide), rfl⟩) <| .cons (.kernel (.ok (by decide))) <|
  .cons (.newMutex (st' := (r14s2, [⟨4, none⟩])) ⟨by decide, rfl⟩) <|
  .cons (.kernel ⟨_, .ok (by decide), rfl⟩) <| .cons (.kernel (.ok (by decide))) <|
  .cons (.newMutex (st' := (r14s4, r14reg)) ⟨by decide, rfl⟩) .nil

/-- **R14** (`ok`, `ok`). Two mutexes `M1`, `M2` in frame 0, each built as the reference mutex,
entries `e1`, `e2`; context 0 acquires `e1`, then `e2`. Expected: both `ok` by C16.3; after the
first, `e2.grant = none` and the footprint of the first grant is that of `T1`, with no leaf of `T2`
(C15 effect). Obtained: both `ok`; after the first, `e2` records `grant = none` and the footprint
of the grant is `footprint(T1)`, disjoint from `footprint(T2)`. Twin: the rejection of a second
mutex on one controller (C13.8) is `witness_5c`. -/
theorem R14 : LRun kTwo mutexLayout (r14s0, [], []) r14L (r14s4, r14reg, []) ∧
    AcquireOk kTwo mutexLayout r14s4 r14reg 0 0 (r14s5, [⟨4, some 6⟩, ⟨5, none⟩]) ∧
    r14s5.flat.afp 6 = footprint r14s5.P 3 ∧ (∀ l ∈ r14s5.flat.afp 6, l ∉ footprint r14s5.P 7) ∧
    AcquireOk kTwo mutexLayout r14s5 [⟨4, some 6⟩, ⟨5, none⟩] 0 1
      (r14s6, [⟨4, some 6⟩, ⟨5, some 7⟩]) :=
  ⟨r14_run, ⟨⟨4, none⟩, rfl, by decide, by decide, rfl⟩, by decide, by decide,
    ⟨⟨5, none⟩, rfl, by decide, by decide, rfl⟩⟩

/-! ## R15: a transfer of the whole mutex while its grant is held -/

/-- `acquire(e)` by context 0 from the reference mutex: the grant 3, held by frame 0 (`mG`). -/
def r15s1 : SC := mG
/-- `m := derive(root_M, Modify)`, authority 4 (O1). -/
def r15s2 : SC := r15s1.set (deriveEff (r15s1.view 0) 0 [1, 2] .modify)
/-- Context 0 enters frame 1 yielding `m`, with a local `M′ = {slot′, lock′}` (places 4, 5, 6;
root authority 5) (O6). -/
def r15s3 : SC := enterEffC r15s2 0 [4] [(none, 0), (some 4, 0), (some 4, 0)]
/-- Step 1: `transfer(M, M′)` (O4). -/
def r15s4 : SC := transferEffC r15s3 0 0 4
/-- Step 3: `transfer(M′, M)` (O4). -/
def r15s5 : SC := transferEffC r15s4 0 4 0

/-- The setup of `R15` after the construction of the reference mutex. -/
def r15L : List Label :=
  [.acquire 0 0, .kernel 0 (.derive 0 [1, 2] .modify),
   .kernel 0 (.enter [4] [(none, 0), (some 4, 0), (some 4, 0)])]

/-- The setup of `R15` is an `EncapsulatedTrace` (C22, C51.1). -/
theorem r15_encap :
    EncapsulatedTrace pm kMutex mutexLayout (m0, [], []) (refMutexL ++ r15L) (r15s3, regG, []) :=
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩ (.kernel mutex_steps.1) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩ (.kernel mutex_steps.2.1) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩
    (.newMutex (st' := (m2, regFree)) mutex_steps.2.2.1) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩
    (.acquire (st' := (mG, regG)) ⟨⟨2, none⟩, rfl, by decide, by decide, rfl⟩) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩
    (.kernel ⟨_, .ok (by decide), rfl⟩) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩
    (.kernel (.ok (by decide))) .nil

/-- **R15** (`ok` admitted; `reject`; `ok`; `ok`). The reference mutex, not shared; context 0
acquires it, the grant `g` held by frame 0; `m := derive(root_M, Modify)`; context 0 enters frame 1
yielding `m`, with a local `M′`. 1. `transfer(M, M′)`; 2. context 0 exits frame 1; 3.
`transfer(M′, M)`; 4. context 0 exits frame 1. Expected: 1 `ok`, admitted by O4 and C22.3 (a
transfer of the whole mutex); 2 `reject` by Spec 1 §73.4: no surviving origin for `g`; 3 `ok`:
the leaves of `M` are `Moved` (§63.3); 4 `ok`. Obtained: 1 `ok` and `EncapStep`; 2 `reject`; 3
`ok`; 4 `ok`. Twin: `R15_twin`. -/
theorem R15 :
    EncapsulatedTrace pm kMutex mutexLayout (m0, [], []) (refMutexL ++ r15L) (r15s3, regG, []) ∧
    LStep kMutex mutexLayout (.kernel 0 (.transfer 0 4)) (r15s3, regG, []) (r15s4, regG, []) ∧
    EncapStep pm kMutex mutexLayout (r15s3, regG, []) (.kernel 0 (.transfer 0 4)) (r15s4, regG, []) ∧
    opStepC kMutex.toK .exit 0 r15s4 .reject ∧
    opStepC kMutex.toK (.transfer 4 0) 0 r15s4 (.ok r15s5) ∧
    opStepC kMutex.toK .exit 0 r15s5 (.ok (exitEffC r15s5 0)) :=
  ⟨r15_encap, .kernel (.ok (by decide)),
    ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩, .reject (by decide),
    .ok (by decide), .ok (by decide)⟩

/-- Statics of the reference mutex with a second value `M′ = {slot′, lock′}` in frame 0, without
entry, its leaves `Uninit` (Spec 1 §47): `M` (places 0, 1, 2), `T` (place 3) owned by `M`, `M′`
(places 4, 5, 6). Root authorities: 0 of `M`, 1 of `T` (held by `M`), 2 of `M′`. -/
def mutexPrimeStatics : Statics :=
  [((none, none, 0), false), ((some 0, none, 0), false), ((some 0, none, 0), true),
   ((none, some 0, 0), true), ((none, none, 0), false), ((some 4, none, 0), false),
   ((some 4, none, 0), false)]

/-- Initial state (Spec 1 §47). -/
def p0 : SC := SC.ofS3 (S3.init mutexPrimeStatics)
/-- `guarded := derive(root_T, Modify, footprint(T))`, authority 3 (O1). -/
def p1 : SC := p0.set (deriveEff (p0.view 0) 1 [3] .modify)
/-- `store(guarded, slot)` (O8). -/
def p2 : SC := storeEffC p1 0 3 1
/-- The registry with the entry of `guarded`, available. -/
def pReg : SyncReg := [⟨3, none⟩]

/-- The construction of the reference mutex beside `M′`. -/
def pL : List Label := [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 3 1), .newMutex 0 3]

/-- The construction of the reference mutex beside `M′` is an `EncapsulatedTrace` (C22, C51.1). -/
theorem p_encap : EncapsulatedTrace pm kMutex mutexLayout (p0, [], []) pL (p2, pReg, []) :=
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩
    (.kernel ⟨_, .ok (by decide), rfl⟩) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩ (.kernel (.ok (by decide))) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩
    (.newMutex (st' := (p2, pReg)) ⟨by decide, rfl⟩) .nil

/-- `acquire(e)` by context 0: the grant 4, held by frame 0 (C16). -/
def p3g : SC := deriveSyncEff p2 0 3

/-- **R15, twin** (`ok`). The reference mutex with `M′` a local of frame 0; context 0 acquires the
entry, then `transfer(M, M′)` from frame 0. Expected: `ok`. Obtained: `ok`. -/
theorem R15_twin : AcquireOk kMutex mutexLayout p2 pReg 0 0 (p3g, [⟨3, some 4⟩]) ∧
    opStepC kMutex.toK (.transfer 0 4) 0 p3g (.ok (transferEffC p3g 0 0 4)) :=
  ⟨⟨⟨3, none⟩, rfl, by decide, by decide, rfl⟩, .ok (by decide)⟩

/-! ## R18, R19: `newMutex` on uninitialized leaves; transfers of the whole mutex -/

/-- Statics of `R18` (1) (Spec 1 §47): `M′ = {slot′, lock′}` (places 0, 1, 2), its leaves
`Uninit`, and `T′` (place 3) owned by `slot′`. Root authorities: 0 of `M′`, 1 of `T′` (held by
`slot′`). -/
def uninitMutexStatics : Statics :=
  [((none, none, 0), false), ((some 0, none, 0), false), ((some 0, none, 0), false),
   ((none, some 1, 0), true)]

/-- **R18** (`reject`, `reject`). (1) `M′` with `Uninit` leaves, `guarded′ = root_T′`, `T′` owned
by `slot′`: `newMutex(guarded′)`. (2) `M` and `M′` both built as the reference mutex, entries
live: context 0 requests `transfer(M, M′)`. Expected: (1) `reject` by C13.10; (2) `reject` by
Spec 1 §63.3: the leaves of `M′` are `Init`. Obtained: (1) `reject`, the leaves of `M′` not
`Init`; (2) `reject`. Twin: the transfer of `R19` (a). -/
theorem R18 :
    NewMutexOutcome kMutex.toK mutexLayout [] (SC.ofS3 (S3.init uninitMutexStatics)) [] 0 1
      .reject ∧
    OptP (mutexOf (SC.ofS3 (S3.init uninitMutexStatics)) 1)
      (fun m => ¬ ∀ l ∈ footprint (SC.ofS3 (S3.init uninitMutexStatics)).P m,
        (SC.ofS3 (S3.init uninitMutexStatics)).I l = .init) False ∧
    LRun kTwo mutexLayout (r14s0, [], []) r14L (r14s4, r14reg, []) ∧
    opStepC kTwo.toK (.transfer 0 4) 0 r14s4 .reject :=
  ⟨.reject (by decide), by decide, r14_run, .reject (by decide)⟩

/-- Step (a): `transfer(M, M′)` by context 0 (O4). -/
def p3t : SC := transferEffC p2 0 0 4
/-- (b): `o1 := derive(root_M, Observe, {slot, lock})`, authority 4 (O1). -/
def p3o : SC := p2.set (deriveEff (p2.view 0) 0 [1, 2] .observe)
/-- (b): `spawn` of context 1 yielding `o1` (C4). -/
def p4o : SC := spawnEff p3o 0 [4] []

/-- **R19** (`ok` admitted; `reject`). (a) The reference mutex beside `M′`: context 0 transfers
`M` into `M′`. (b) The shared reference mutex beside `M′`: context 0 transfers `M` into `M′`.
Expected: (a) `ok`, admitted by O4 and C22.3; after the step `guarded` is held by `slot′` and
`ControlOf(e) = lock′` (C12); (b) `reject` by Spec 1 §63.1 and §63.4: `o1`, active and held
outside the source, covers leaves of the source. Obtained: (a) `ok` and `EncapStep`, `guarded`
held by `slot′`, `ControlOf(e) = lock′`; (b) `reject`. Twin: (a) is the twin of (b). -/
theorem R19 : EncapsulatedTrace pm kMutex mutexLayout (p0, [], []) pL (p2, pReg, []) ∧
    LStep kMutex mutexLayout (.kernel 0 (.transfer 0 4)) (p2, pReg, []) (p3t, pReg, []) ∧
    EncapStep pm kMutex mutexLayout (p2, pReg, []) (.kernel 0 (.transfer 0 4)) (p3t, pReg, []) ∧
    (p3t.A[3]?).map (·.holder) = some (.place 5) ∧
    ControlOf mutexLayout p3t ⟨3, none⟩ = some 6 ∧
    opStepC kMutex.toK (.derive 0 [1, 2] .observe) 0 p2 (.ok p3o) ∧
    SpawnStep p3o 0 [4] [] (.ok p4o) ∧
    opStepC kMutex.toK (.transfer 0 4) 0 p4o .reject :=
  ⟨p_encap, .kernel (.ok (by decide)), ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
    by decide, by decide, ⟨_, .ok (by decide), rfl⟩, .ok (by decide), .reject (by decide)⟩

/-! ## R21: an arena administered under a mutex -/

/-- Statics of the arena under a mutex (Spec 1 §47): `M2 = {slot2, lock2}` (places 0, 1, 2), as
the reference mutex; `AV` (place 3), a leaf root owned by `M2`, `Init`; `ST = {r1, r2}` (places
4, 5, 6), a root owned by frame 0; `d0` (place 7), a leaf of frame 0. Root authorities: 0 of
`M2`, 1 of `AV` (held by `M2`), 2 of `ST`, 3 of `d0`. -/
def arenaMutexStatics : Statics :=
  [((none, none, 0), false), ((some 0, none, 0), false), ((some 0, none, 0), true),
   ((none, some 0, 0), true), ((none, none, 0), false), ((some 4, none, 0), false),
   ((some 4, none, 0), false), ((none, none, 0), false)]

/-- Initial state (Spec 1 §47). -/
def r21s0 : SC := SC.ofS3 (S3.init arenaMutexStatics)
/-- `internal := derive(root_ST, Modify, footprint(ST))`, authority 4 (O1). -/
def r21s1 : SC := r21s0.set (deriveEff (r21s0.view 0) 2 [5, 6] .modify)
/-- `store(internal, AV)` (O8). -/
def r21s2 : SC := storeEffC r21s1 0 4 3
/-- The arena registry after `newArena(ST, internal)`: the arena value is `AV` (Spec 1 §76). -/
def r21ar : ArenaReg := [⟨4, 4, footprint r21s2.P 4, []⟩]
/-- `guarded2 := derive(root_AV, Modify, {AV})`, authority 5 (O1). -/
def r21s3 : SC := r21s2.set (deriveEff (r21s2.view 0) 1 [3] .modify)
/-- `store(guarded2, slot2)` (O8). -/
def r21s4 : SC := storeEffC r21s3 0 5 1
/-- The registry with the entry `e2` of `guarded2`, available. -/
def r21reg : SyncReg := [⟨5, none⟩]
/-- `o1 := derive(root_M2, Observe, {slot2, lock2})`, authority 6 (O1). -/
def r21s5 : SC := r21s4.set (deriveEff (r21s4.view 0) 0 [1, 2] .observe)
/-- `spawn` of context 1 yielding `o1`, with a local leaf `d1` (place 8, root authority 7)
(C4). -/
def r21s6 : SC := spawnEff r21s5 0 [6] [(none, 0)]
/-- Step 2: `acquire(e2)` by context 1: the grant 8, held by frame 1 (C16). -/
def r21s7 : SC := deriveSyncEff r21s6 1 5
/-- The registry recording the grant 8. -/
def r21reg8 : SyncReg := [⟨5, some 8⟩]
/-- Step 3, internal `split` of `internal` on `R1 = [r1]` by context 1 (O2): authority 9. -/
def r21s7a : SC := r21s7.set (splitEff (r21s7.view 1) 4 [[5]])
/-- Step 3, internal `store` of the block 9 into `d1` (O8). -/
def r21s8 : SC := storeEffC r21s7a 1 9 8
/-- The arena registry after step 3 (Spec 1 §77 effect). -/
def r21ar3 : ArenaReg := r21ar.set 0 (Arena.issueMeta r21s7.flat ⟨4, 4, footprint r21s2.P 4, []⟩ [5])
/-- Step 5: `unlock(e2)` by context 1 (C17). -/
def r21s9 : SC := prospectiveUnlock r21s8 1 8
/-- Step 6: `acquire(e2)` by context 0: the grant 10, held by frame 0 (C16). -/
def r21s10 : SC := deriveSyncEff r21s9 0 5
/-- Step 8, internal `split` of `internal` on `R2 = [r2]` by context 0 (O2): authority 11. -/
def r21s10a : SC := r21s10.set (splitEff (r21s10.view 0) 4 [[6]])

/-- The arena block: the arena on `ST` with value `AV`; the mutex `M2` guarding `AV`; its sharing
with context 1. -/
def r21L : List Label :=
  [.kernel 0 (.derive 2 [5, 6] .modify), .kernel 0 (.store 4 3), .newArena 0 4 4,
   .kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 5 1), .newMutex 0 5,
   .kernel 0 (.derive 0 [1, 2] .observe), .spawn 0 [6] [(none, 0)]]

/-- The arena block is reached by `ok` steps (O1, O8, O17, C13, C4). -/
theorem r21_run : LRun kMutex mutexLayout (r21s0, [], []) r21L (r21s6, r21reg, r21ar) :=
  .cons (.kernel ⟨_, .ok (by decide), rfl⟩) <| .cons (.kernel (.ok (by decide))) <|
  .cons (.newArena (st' := (r21s2, r21ar)) (.ok (by decide))) <|
  .cons (.kernel ⟨_, .ok (by decide), rfl⟩) <| .cons (.kernel (.ok (by decide))) <|
  .cons (.newMutex (st' := (r21s4, r21reg)) ⟨by decide, rfl⟩) <|
  .cons (.kernel ⟨_, .ok (by decide), rfl⟩) <| .cons (.spawn (.ok (by decide))) .nil

/-- **R21** (`reject`, `ok`, `ok`, not enabled, `ok`, `ok`, `fail`, `ok`). The arena block: the
arena on `ST` with value `AV`, administered under the mutex `M2` whose entry `e2` guards `AV`,
shared with context 1; context 1 has a local leaf `d1`, context 0 a local leaf `d0`. 1. context 1
issues `R1` into `d1` without grant; 2. context 1 acquires `e2`; 3. context 1 issues `R1` into
`d1`; 4. context 0 requests `acquire(e2)`; 5. context 1 unlocks `e2`; 6. context 0 acquires `e2`;
7. context 0 issues `R1` into `d0`; 8. context 0 issues `R2` into `d0`. Expected: 1 `reject` by
Spec 1 §77.1; 2 `ok`; 3 `ok` by C19, §77; 4 not enabled by C16.2; 5, 6 `ok`; 7 `fail` by §77.4
(`R1` unavailable); 8 `ok`. Obtained: as expected. Twin: steps 3 and 8; `R21_twin`. -/
theorem R21 : LRun kMutex mutexLayout (r21s0, [], []) r21L (r21s6, r21reg, r21ar) ∧
    IssueStepC kMutex.toK r21s6 r21ar 1 0 [5] 8 .reject ∧
    AcquireOk kMutex mutexLayout r21s6 r21reg 1 0 (r21s7, r21reg8) ∧
    IssueStepC kMutex.toK r21s7 r21ar 1 0 [5] 8 (.ok (r21s8, r21ar3)) ∧
    AcquireNotEnabled mutexLayout r21s8 r21reg8 0 0 ∧
    (∀ o, ¬ AcquireOutcome kMutex mutexLayout r21s8 r21reg8 0 0 o) ∧
    (∀ st', ¬ LStep kMutex mutexLayout (.acquire 0 0) (r21s8, r21reg8, r21ar3) st') ∧
    UnlockOk mutexLayout r21s8 r21reg8 1 0 (r21s9, r21reg) ∧
    AcquireOk kMutex mutexLayout r21s9 r21reg 0 0 (r21s10, [⟨5, some 10⟩]) ∧
    IssueStepC kMutex.toK r21s10 r21ar3 0 0 [5] 7 .fail ∧
    IssueStepC kMutex.toK r21s10 r21ar3 0 0 [6] 7
      (.ok (storeEffC r21s10a 0 11 7,
        r21ar3.set 0 (Arena.issueMeta r21s10.flat
          (Arena.issueMeta r21s7.flat ⟨4, 4, footprint r21s2.P 4, []⟩ [5]) [6]))) := by
  have hn : AcquireNotEnabled mutexLayout r21s8 r21reg8 0 0 :=
    ⟨⟨⟨5, some 8⟩, rfl, by decide, by decide, by unfold AcquireIndependent; decide,
      fun h => by cases h⟩, ⟨5, some 8⟩, rfl, by decide⟩
  have hc := (acquire_classes (ks := kMutex) (ar := r21ar3) (s := r21s8) (reg := r21reg8) (c := 0)
    (i := 0)).2.2.1 hn
  exact ⟨r21_run, .static rfl (by decide), ⟨⟨5, none⟩, rfl, by decide, by decide, rfl⟩,
    .ok rfl (by decide) (by decide) ⟨_, .ok (by decide), rfl⟩ (.ok (by decide)), hn, hc.1, hc.2,
    ⟨⟨5, some 8⟩, 8, rfl, by decide, rfl, by decide, by decide, by decide, rfl⟩,
    ⟨⟨5, none⟩, rfl, by decide, by decide, rfl⟩, .fail rfl (by decide) (by decide),
    .ok rfl (by decide) (by decide) ⟨_, .ok (by decide), rfl⟩ (.ok (by decide))⟩

/-- **R21, twin** (`reject`). After step 3 of `R21`: context 1 requests `reset(arena)`. Expected:
`reject` at the internal `derive` of `internal` (Spec 1 §60.2, §43.3); §78.2. Obtained: `reject`,
at the internal `derive`. -/
theorem R21_twin : ResetStepC r21s8 r21ar3 1 0 .reject :=
  ⟨.reject, .derive rfl (.reject (by decide)), rfl⟩

/-! ## R22, R23: a grant abandoned by a frame exit, with a surviving derivative -/

/-- Step 2: context 0 enters frame 1 yielding `o := derive(root_M, Observe, {lock})` (authority 3,
`n3`) (O6). -/
def r22s2 : SC := enterEffC n3 0 [3] []
/-- Step 3: `acquire(e)` from frame 1: the grant 4, held by frame 1 (C16). -/
def r22s3 : SC := deriveSyncEff r22s2 0 2
/-- Step 4: `x := derive(g, Modify, footprint(T))`, authority 5, held by frame 1 (O1). -/
def r22s4 : SC := r22s3.set (deriveEff (r22s3.view 0) 4 [3] .modify)
/-- Step 5: `spawn` of context 1 yielding `x` (C4): initial frame 2, parented to frame 1. -/
def r22s5 : SC := spawnEff r22s4 0 [5] []
/-- Step 6: context 0 exits frame 1 without `unlock` (O7, C6). -/
def r22s6 : SC := exitEffC r22s5 0
/-- Step 7: `write3(T)` by context 1 through `x` (O10). -/
def r22s7 : SC := r22s6.set (write3Eff (r22s6.view 1) [3])
/-- Step 8: `release(x)` by context 1 (O3). -/
def r22s8 : SC := r22s7.set (releaseEff (r22s7.view 1) 5)
/-- Step 10: `acquire(e)` by context 0: the grant 6, held by frame 0 (C16). -/
def r22s10 : SC := deriveSyncEff r22s8 0 2
/-- Step 11: `write3(T)` by context 0 through the new grant (O10). -/
def r22s11 : SC := r22s10.set (write3Eff (r22s10.view 0) [3])
/-- The registry recording the grant 6. -/
def r22reg : SyncReg := [⟨2, some 6⟩]

/-- Steps 1–8 of `R22`, after the construction of the reference mutex. -/
def r22L : List Label :=
  [.kernel 0 (.derive 0 [2] .observe), .kernel 0 (.enter [3] []), .acquire 0 0,
   .kernel 0 (.derive 4 [3] .modify), .spawn 0 [5] [], .kernel 0 .exit,
   .kernel 1 (.write 5 [3]), .kernel 1 (.release 5)]

/-- Steps 9–11 of `R22`. -/
def r22L' : List Label := [.resetLock 0 0, .acquire 0 0, .kernel 0 (.write 6 [3])]

/-- The construction of the reference mutex and steps 1–11 of `R22` form an `EncapsulatedTrace`
(C22, C51.1). -/
theorem r22_encap : EncapsulatedTrace pm kMutex mutexLayout (m0, [], []) (refMutexL ++ r22L ++ r22L')
    (r22s11, r22reg, []) :=
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩ (.kernel mutex_steps.1) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩ (.kernel mutex_steps.2.1) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩
    (.newMutex (st' := (m2, regFree)) mutex_steps.2.2.1) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩
    (.kernel ⟨_, .ok (by decide), rfl⟩) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩ (.kernel (.ok (by decide))) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩
    (.acquire (st' := (r22s3, regTaken)) ⟨⟨2, none⟩, rfl, by decide, by decide, rfl⟩) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩
    (.kernel ⟨_, .ok (by decide), rfl⟩) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩ (.spawn (.ok (by decide))) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩ (.kernel (.ok (by decide))) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩
    (.kernel ⟨_, .ok (by decide), rfl⟩) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩
    (.kernel ⟨_, .ok (by decide), rfl⟩) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩
    (.resetLock (st' := (r22s8, regFree))
      ⟨⟨2, some 4⟩, rfl, by decide, by decide, by decide, by decide, rfl⟩) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩
    (.acquire (st' := (r22s10, r22reg)) ⟨⟨2, none⟩, rfl, by decide, by decide, rfl⟩) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩
    (.kernel ⟨_, .ok (by decide), rfl⟩) .nil

/-- **R22** (steps 1–7 `ok`; a. not enabled; b, c, d `reject`). The reference mutex, not shared.
1. `o := derive(root_M, Observe, {lock})`; 2. context 0 enters frame 1 yielding `o`; 3. it
acquires the entry, the grant `g` held by frame 1; 4. `x := derive(g, Modify, footprint(T))`; 5.
it spawns context 1 yielding `x`; 6. context 0 exits frame 1 without `unlock`; 7. context 1
writes `T` through `x`. Then, each from the state after step 7: a. context 0 requests
`acquire(e)`; b. `unlock(e)`; c. `resetLock(e)`; d. `read3(T)` with `guarded` as access
authority. Expected: 1–7 `ok`; at 6 (C6, Spec 1 §73.4) `g` and `o` are released, `x` survives,
re-anchored on `guarded`, the registry keeps `grant = some g` (C18); a. not enabled by C16.2; b.
`reject` by C17.2; c. `reject` by C18.2; d. `reject` by O9.2 (§43.3). Obtained: 1–7 `ok` (steps
of the `EncapsulatedTrace` `r22_encap`); after 6, `g` and `o` inactive, `x` active of origin
`guarded`, the registry unchanged; a. legal and not enabled, no outcome and no labelled step; b,
c, d `reject`. Twin: `R22_twin`. -/
theorem R22 : EncapsulatedTrace pm kMutex mutexLayout (m0, [], []) (refMutexL ++ r22L ++ r22L')
      (r22s11, r22reg, []) ∧
    ¬ r22s6.flat.Active 4 ∧ ¬ r22s6.flat.Active 3 ∧ r22s6.flat.Active 5 ∧
    r22s6.flat.org 5 = some 2 ∧
    AcquireNotEnabled mutexLayout r22s7 regTaken 0 0 ∧
    (∀ o, ¬ AcquireOutcome kMutex mutexLayout r22s7 regTaken 0 0 o) ∧
    (∀ st', ¬ LStep kMutex mutexLayout (.acquire 0 0) (r22s7, regTaken, []) st') ∧
    UnlockOutcome mutexLayout r22s7 regTaken 0 0 .reject ∧
    ResetLockOutcome mutexLayout r22s7 regTaken 0 0 .reject ∧
    opStepC kMutex.toK (.read 2 [3]) 0 r22s7 .reject := by
  have hn : AcquireNotEnabled mutexLayout r22s7 regTaken 0 0 :=
    ⟨⟨⟨2, some 4⟩, rfl, by decide, by decide, by unfold AcquireIndependent; decide,
      fun h => by cases h⟩, ⟨2, some 4⟩, rfl, by decide⟩
  have hc := (acquire_classes (ks := kMutex) (ar := []) (s := r22s7) (reg := regTaken) (c := 0)
    (i := 0)).2.2.1 hn
  exact ⟨r22_encap, by decide, by decide, by decide, by decide, hn, hc.1, hc.2,
    .reject fun ⟨e, g, he, _, hg, hrel, _⟩ => by
      cases he; cases hg; exact (by decide : ¬ ReleasePre (r22s7.view 0) 4) hrel,
    .reject (by unfold ResetLockPre; decide), ⟨_, .reject (by decide), rfl⟩⟩

/-- **R22, twin** (`ok`; step 9 admitted). After step 7 of `R22`: 8. context 1 releases `x`; 9.
context 0 requests `resetLock(e)`; 10. `acquire(e)`; 11. it writes `T` through the new grant.
Expected: each step `ok`; 9 admitted by C18.1–C18.4 and C22.6 (the exception of `resetLock`).
Obtained: each step `ok`; step 9 satisfies `EncapStep`, from the state reached by the
`EncapsulatedTrace` `r22_encap` up to step 8. -/
theorem R22_twin : opStepC kMutex.toK (.release 5) 1 r22s7 (.ok r22s8) ∧
    ResetLockOk mutexLayout r22s8 regTaken 0 0 (r22s8, regFree) ∧
    EncapStep pm kMutex mutexLayout (r22s8, regTaken, []) (.resetLock 0 0) (r22s8, regFree, []) ∧
    AcquireOk kMutex mutexLayout r22s8 regFree 0 0 (r22s10, r22reg) ∧
    opStepC kMutex.toK (.write 6 [3]) 0 r22s10 (.ok r22s11) :=
  ⟨⟨_, .ok (by decide), rfl⟩, ⟨⟨2, some 4⟩, rfl, by decide, by decide, by decide, by decide, rfl⟩,
    ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
    ⟨⟨2, none⟩, rfl, by decide, by decide, rfl⟩, ⟨_, .ok (by decide), rfl⟩⟩

/-- A1: `y := derive(x, Modify, footprint(T))` by context 1, authority 6 (O1). -/
def r23s1 : SC := r22s7.set (deriveEff (r22s7.view 1) 5 [3] .modify)
/-- A2: `spawn` of context 2 by context 1 yielding `y` (C4). -/
def r23s2 : SC := spawnEff r23s1 1 [6] []
/-- A3: `terminate` of context 1 (C7). -/
def r23s3 : SC := termEffC r23s2 1
/-- A4: `write3(T)` by context 2 through `y` (O10). -/
def r23s4 : SC := r23s3.set (write3Eff (r23s3.view 2) [3])

/-- **R23** (A1–A4 `ok`; `reject`). From the state after step 7 of `R22`: A1. context 1 derives
`y := derive(x, Modify, footprint(T))`; A2. it spawns context 2 yielding `y`; A3. it terminates;
A4. context 2 writes `T` through `y`; then context 0 requests `resetLock(e)`. Expected: A1–A4
`ok`; at A3 (C7, Spec 1 §73.4) `x` is released and `y` survives, re-anchored on `guarded`; the
`resetLock` `reject` by C18.2 (`y` active). Obtained: A1–A4 `ok`, after A3 `x` inactive and `y`
active of origin `guarded`; the `resetLock` `reject`. Twin: step 9 of `R22_twin`. -/
theorem R23 : opStepC kMutex.toK (.derive 5 [3] .modify) 1 r22s7 (.ok r23s1) ∧
    SpawnStep r23s1 1 [6] [] (.ok r23s2) ∧ TermStep kMutex.toK r23s2 1 (.ok r23s3) ∧
    ¬ r23s3.flat.Active 5 ∧ r23s3.flat.Active 6 ∧ r23s3.flat.org 6 = some 2 ∧
    opStepC kMutex.toK (.write 6 [3]) 2 r23s3 (.ok r23s4) ∧
    ResetLockOutcome mutexLayout r23s4 regTaken 0 0 .reject :=
  ⟨⟨_, .ok (by decide), rfl⟩, .ok (by decide), .ok (by decide), by decide, by decide, by decide,
    ⟨_, .ok (by decide), rfl⟩, .reject (by unfold ResetLockPre; decide)⟩

end Ern.Corpus.Concurrency
