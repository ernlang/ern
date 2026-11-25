import Ern.Corpus.ConcurrencyMutex
import Ern.ConcurrencyModel.WitnessCapacity

/-!
# Corpus of the concurrency model: steps excluded or admitted by encapsulation (test module)

Cases `R25`–`R45` and `R59` of the concurrency model
(`specs/ERN_Concurrency_Model_Specification_v0.md`),
replayed on the concurrent authority machine (`LStep`) and on the step condition of
`EncapsulatedTrace` (`EncapStep`: `RestrictedStep` for C22.1–C22.3 and C22.5,
`ControllerRestriction` for C22.4, `RightsReadFree` for C22.6; C51.1). A step stated excluded or
admitted is `ok` (`LStep`) from a state reached by an `EncapsulatedTrace` from the initial state
of Spec 1 §47; an excluded step states the negation of the conjunct of `EncapStep` that carries the
requirement of C22 named by its docstring, and hence `¬ EncapStep`; an admitted step states
`EncapStep`. After an excluded step, the following steps of a case have a machine verdict only.
Other verdicts are outcomes of the relation of the step; `R59` also states effective modes,
exercisability and the capability of contexts (C43) in a reached state, on the execution of witness
W13 (`WitnessCapacity`). Each docstring gives the situation, the
expected verdict with its clause, the obtained verdict and the twin. The reference mutex and its
variants are those of `Ern.Corpus.Concurrency` (`ConcurrencyMutex`). This is a test module: no
model module imports it.
-/

namespace Ern.Corpus.Concurrency

open Ern.MemoryModel Ern.MemoryModel.Access Ern.ConcurrencyModel

variable {pm : ProviderMeta}

/-- A step that fails `ControllerRestriction` (C22.4) is not an `EncapStep`. -/
theorem not_encap_cr {ks : KShared} {L : MutexLayout} {st st' : SC × SyncReg × ArenaReg}
    {lbl : Label} (h : ¬ ControllerRestriction pm L st lbl st') : ¬ EncapStep pm ks L st lbl st' :=
  fun he => h he.2.1

/-- A step that fails `RestrictedStep` (C22.1–C22.3, C22.5) is not an `EncapStep`. -/
theorem not_encap_rs {ks : KShared} {L : MutexLayout} {st st' : SC × SyncReg × ArenaReg}
    {lbl : Label} (h : ¬ RestrictedStep L st lbl) : ¬ EncapStep pm ks L st lbl st' :=
  fun he => h he.1

/-- A step that fails `RightsReadFree` (C22.6) is not an `EncapStep`. -/
theorem not_encap_rr {ks : KShared} {L : MutexLayout} {st st' : SC × SyncReg × ArenaReg}
    {lbl : Label} (h : ¬ RightsReadFree ks L st lbl) : ¬ EncapStep pm ks L st lbl st' :=
  fun he => h he.2.2

/-- `ControllerRestriction` (C22.4) at an `alloc` step from a state whose registry is one entry
`x` with controller `ctl`: if `x` is live and the leaves the step actually affects contain `ctl`,
then `x` is dead after the step (an `alloc` is neither a step of the controller protocol nor a
move of the whole mutex value). -/
theorem ctl_alloc_one {L : MutexLayout} {s : SC} {x : SyncEntry} {ar : ArenaReg}
    {c pr ow ctl : Nat} {ls : LocalShape} {st' : SC × SyncReg × ArenaReg}
    (hc : ControlOf L s x = some ctl) :
    ControllerRestriction pm L (s, [x], ar) (.kernel c (.alloc pr ow ls)) st' ↔
      (x.Live s → pm (s, [x], ar) c pr ow ls ctl = true ∨ ctl = ow ∨ s.P.length ≤ ctl →
        ¬ x.Live st'.1) := by
  simp [ControllerRestriction, OptP, hc, ActualFootprint, ProtocolStepOf, WholeValueMove]

/-! ## R25–R28: accesses to the protected root and to the controller -/

/-- **R25** (`reject`). The shared reference mutex; context 1 acquires the entry, its grant `g`
(authority 4); then the inherited `writeShared` of context 1 on `T` through `g`. Expected:
`reject` by O11.1: `T` is not `SharedMutable`. Obtained: `reject`. Twin: `R25_twin`. -/
theorem R25 : LRun kMutex mutexLayout (m0, [], []) sharedMutexL (m4, regFree, []) ∧
    AcquireOk kMutex mutexLayout m4 regFree 1 0 (m5, regTaken) ∧
    opStepC kMutex.toK (.writeShared 4 [3]) 1 m5 .reject :=
  ⟨sharedMutex_run, mutex_steps.2.2.2.2.2.1, ⟨_, .reject (by decide), rfl⟩⟩

/-- **R25, twin** (`ok`). Context 1 writes `T` through `g` (`write3`). Expected: `ok`. Obtained:
`ok`. -/
theorem R25_twin :
    opStepC kMutex.toK (.write 4 [3]) 1 m5 (.ok (m5.set (write3Eff (m5.view 1) [3]))) :=
  ⟨_, .ok (by decide), rfl⟩

/-- **R26** (`ok`, excluded; `ok`, excluded). The shared reference mutex. (a) The inherited
`writeShared` of context 1 on `{lock}` through `o1`; (b) the concurrent `writeShared` of context 1
on `{lock}`, of kind `store` and order `release`. Expected: (a) `ok` by O11, excluded by C22.4;
(b) `ok` by C39, C40, excluded by C22.4. Obtained: (a), (b) `ok`, each failing
`ControllerRestriction`. Twin: `R26_twin`. -/
theorem R26 : EncapsulatedTrace pm kMutex mutexLayout (m0, [], []) sharedMutexL (m4, regFree, []) ∧
    LStep kMutex mutexLayout (.kernel 1 (.writeShared 3 [2])) (m4, regFree, [])
      (m4.set (write3Eff (m4.view 1) [2]), regFree, []) ∧
    ¬ ControllerRestriction pm mutexLayout (m4, regFree, []) (.kernel 1 (.writeShared 3 [2]))
      (m4.set (write3Eff (m4.view 1) [2]), regFree, []) ∧
    LStep kMutex mutexLayout (.writeShared 1 3 [2] (some .release) .store) (m4, regFree, [])
      (writeSharedCEff m4 1 [2], regFree, []) ∧
    ¬ ControllerRestriction pm mutexLayout (m4, regFree, [])
      (.writeShared 1 3 [2] (some .release) .store) (writeSharedCEff m4 1 [2], regFree, []) :=
  ⟨sharedMutex_encap, .kernel ⟨_, .ok (by decide), rfl⟩, by decide_ctl,
    .writeShared (.ok ⟨by decide, by decide, fun h => absurd rfl h⟩), by decide_ctl⟩

/-- **R26, twin** (`ok`, admitted). From the shared reference mutex: the `acquire` of context 1,
then its `unlock`. Expected: admitted. Obtained: both `ok` and `EncapStep`. -/
theorem R26_twin :
    LStep kMutex mutexLayout (.acquire 1 0) (m4, regFree, []) (m5, regTaken, []) ∧
    EncapStep pm kMutex mutexLayout (m4, regFree, []) (.acquire 1 0) (m5, regTaken, []) ∧
    LStep kMutex mutexLayout (.unlock 1 0) (m5, regTaken, []) (m6, regFree, []) ∧
    EncapStep pm kMutex mutexLayout (m5, regTaken, []) (.unlock 1 0) (m6, regFree, []) :=
  ⟨.acquire (st' := (m5, regTaken)) mutex_steps.2.2.2.2.2.1,
    ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
    .unlock (st' := (m6, regFree)) mutex_steps.2.2.2.2.2.2,
    ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩⟩

/-- **R27** (`ok`, excluded). The reference mutex, not shared: context 0 writes `lock` through
`root_M` (`write3`). Expected: `ok` by O10 (C42: effective `Modify`), excluded by C22.4.
Obtained: `ok`, failing `ControllerRestriction`. Twin: `R27_twin`. -/
theorem R27 : EncapsulatedTrace pm kMutex mutexLayout (m0, [], []) refMutexL (m2, regFree, []) ∧
    LStep kMutex mutexLayout (.kernel 0 (.write 0 [2])) (m2, regFree, [])
      (m2.set (write3Eff (m2.view 0) [2]), regFree, []) ∧
    ¬ ControllerRestriction pm mutexLayout (m2, regFree, []) (.kernel 0 (.write 0 [2]))
      (m2.set (write3Eff (m2.view 0) [2]), regFree, []) :=
  ⟨refMutex_encap, .kernel ⟨_, .ok (by decide), rfl⟩, by decide_ctl⟩

/-- **R27, twin** (`ok`, admitted). From the reference mutex, not shared: the `acquire` of context
0, then its `unlock`. Expected: admitted. Obtained: both `ok` and `EncapStep`. -/
theorem R27_twin :
    LStep kMutex mutexLayout (.acquire 0 0) (m2, regFree, []) (mG, regG, []) ∧
    EncapStep pm kMutex mutexLayout (m2, regFree, []) (.acquire 0 0) (mG, regG, []) ∧
    LStep kMutex mutexLayout (.unlock 0 0) (mG, regG, []) (prospectiveUnlock mG 0 3, regFree, []) ∧
    EncapStep pm kMutex mutexLayout (mG, regG, []) (.unlock 0 0)
      (prospectiveUnlock mG 0 3, regFree, []) :=
  ⟨.acquire (st' := (mG, regG)) ⟨⟨2, none⟩, rfl, by decide, by decide, rfl⟩,
    ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
    .unlock (st' := (prospectiveUnlock mG 0 3, regFree))
      ⟨⟨2, some 3⟩, 3, rfl, by decide, rfl, by decide, by decide, by decide, rfl⟩,
    ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩⟩

/-- **R28** (`ok`, excluded). The reference mutex, not shared: context 0 reads `lock` through
`root_M` (`read3`). Expected: `ok` by O9, excluded by C22.4. Obtained: `ok`, failing
`ControllerRestriction`. Twin: `R28_twin`. -/
theorem R28 : EncapsulatedTrace pm kMutex mutexLayout (m0, [], []) refMutexL (m2, regFree, []) ∧
    LStep kMutex mutexLayout (.kernel 0 (.read 0 [2])) (m2, regFree, [])
      (m2.set (m2.view 0), regFree, []) ∧
    ¬ ControllerRestriction pm mutexLayout (m2, regFree, []) (.kernel 0 (.read 0 [2]))
      (m2.set (m2.view 0), regFree, []) :=
  ⟨refMutex_encap, .kernel ⟨_, .ok (by decide), rfl⟩, by decide_ctl⟩

/-- **R28, twin** (`ok`, admitted). The same read after steps 1 and 2 of the construction, before
`newMutex` (no entry). Expected: `ok`, admitted. Obtained: `ok` and `EncapStep`. -/
theorem R28_twin : EncapsulatedTrace pm kMutex mutexLayout (m0, [], [])
      [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 2 1)] (m2, [], []) ∧
    LStep kMutex mutexLayout (.kernel 0 (.read 0 [2])) (m2, [], []) (m2.set (m2.view 0), [], []) ∧
    EncapStep pm kMutex mutexLayout (m2, [], []) (.kernel 0 (.read 0 [2]))
      (m2.set (m2.view 0), [], []) :=
  ⟨.cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩ (.kernel mutex_steps.1) <|
    .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩ (.kernel mutex_steps.2.1) .nil,
   .kernel ⟨_, .ok (by decide), rfl⟩, ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩⟩

/-! ## R29, R30, R31, R32: protected transfers and protected end of use -/

/-- Statics of the reference mutex with two locals `Y`, `Z` of one leaf, `Uninit` (Spec 1 §47):
`M` (places 0, 1, 2), `T` (place 3) owned by `M`, `Y` (place 4), `Z` (place 5). Root authorities:
0 of `M`, 1 of `T` (held by `M`), 2 of `Y`, 3 of `Z`. -/
def mutexYZStatics : Statics :=
  [((none, none, 0), false), ((some 0, none, 0), false), ((some 0, none, 0), true),
   ((none, some 0, 0), true), ((none, none, 0), false), ((none, none, 0), false)]

/-- Initial state (Spec 1 §47). -/
def yz0 : SC := SC.ofS3 (S3.init mutexYZStatics)
/-- `guarded := derive(root_T, Modify, footprint(T))`, authority 4 (O1). -/
def yz1 : SC := yz0.set (deriveEff (yz0.view 0) 1 [3] .modify)
/-- `store(guarded, slot)` (O8). -/
def yz2 : SC := storeEffC yz1 0 4 1
/-- The registry with the entry of `guarded`, available. -/
def yzReg : SyncReg := [⟨4, none⟩]

/-- The construction of the reference mutex beside `Y` and `Z`. -/
def yzL : List Label := [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 4 1), .newMutex 0 4]

/-- The construction of the reference mutex beside `Y` and `Z` is an `EncapsulatedTrace`. -/
theorem yz_encap : EncapsulatedTrace pm kMutex mutexLayout (yz0, [], []) yzL (yz2, yzReg, []) :=
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩
    (.kernel ⟨_, .ok (by decide), rfl⟩) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩ (.kernel (.ok (by decide))) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩
    (.newMutex (st' := (yz2, yzReg)) ⟨by decide, rfl⟩) .nil

/-- **R29** (`ok`, excluded; `ok`, excluded). The reference mutex, not shared, with the locals `Y`,
`Z` of one leaf, `Uninit`. Two independent steps: (a) `transfer(slot, Y)`; (c) `transfer(lock,
Z)`. Expected: (a) `ok`, excluded by C22.3 (a); (c) `ok`, excluded by C22.3 (c). Obtained: (a),
(c) `ok`, each failing `RestrictedStep`. Twin: `R19` (a). -/
theorem R29 : EncapsulatedTrace pm kMutex mutexLayout (yz0, [], []) yzL (yz2, yzReg, []) ∧
    LStep kMutex mutexLayout (.kernel 0 (.transfer 1 4)) (yz2, yzReg, [])
      (transferEffC yz2 0 1 4, yzReg, []) ∧
    ¬ RestrictedStep mutexLayout (yz2, yzReg, []) (.kernel 0 (.transfer 1 4)) ∧
    LStep kMutex mutexLayout (.kernel 0 (.transfer 2 5)) (yz2, yzReg, [])
      (transferEffC yz2 0 2 5, yzReg, []) ∧
    ¬ RestrictedStep mutexLayout (yz2, yzReg, []) (.kernel 0 (.transfer 2 5)) :=
  ⟨yz_encap, .kernel (.ok (by decide)), by unfold RestrictedStep; decide,
    .kernel (.ok (by decide)), by unfold RestrictedStep; decide⟩

/-- Statics of a reference mutex with a composite `slot = {a, b}` (Spec 1 §47): `M` (place 0),
`slot` (place 1) with the leaves `a`, `b` (places 2, 3), `lock` (place 4), all `Init`; the
protected root `T` (place 5) owned by `slot`; a local `Z` (place 6), `Uninit`. Root authorities:
0 of `M`, 1 of `T` (held by `slot`), 2 of `Z`. -/
def compositeSlotStatics : Statics :=
  [((none, none, 0), false), ((some 0, none, 0), false), ((some 1, none, 0), true),
   ((some 1, none, 0), true), ((some 0, none, 0), true), ((none, some 1, 0), true),
   ((none, none, 0), false)]

/-- The contract of the composite-slot mutex: its controller `lock` (place 4) is the only
`SharedMutable` leaf, of discipline `Atomic(4, 4)`. -/
abbrev kComp : KShared :=
  testKS [4] (fun l => if l = 4 then some (.atomic 4 4) else none) (fun _ => none)

/-- Initial state (Spec 1 §47). -/
def cs0 : SC := SC.ofS3 (S3.init compositeSlotStatics)
/-- The registry with the entry of `guarded = root_T` (authority 1), available. -/
def csReg : SyncReg := [⟨1, none⟩]

/-- `newMutex(root_T)` from the initial state is an `EncapsulatedTrace` (C13). -/
theorem cs_encap : EncapsulatedTrace pm kComp mutexLayout (cs0, [], []) [.newMutex 0 1]
    (cs0, csReg, []) :=
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩
    (.newMutex (st' := (cs0, csReg)) ⟨by decide, rfl⟩) .nil

/-- **R30** (`ok`, excluded). A reference mutex whose `slot = {a, b}` is composite, `guarded =
root_T`, `T` owned by `slot`, not shared; a local `Z`: `transfer(a, Z)`. Expected: `ok`, excluded
by C22.3 (b). Obtained: `ok`, failing `RestrictedStep`. Twin: `R19` (a). -/
theorem R30 : EncapsulatedTrace pm kComp mutexLayout (cs0, [], []) [.newMutex 0 1] (cs0, csReg, []) ∧
    LStep kComp mutexLayout (.kernel 0 (.transfer 2 6)) (cs0, csReg, [])
      (transferEffC cs0 0 2 6, csReg, []) ∧
    ¬ RestrictedStep mutexLayout (cs0, csReg, []) (.kernel 0 (.transfer 2 6)) :=
  ⟨cs_encap, .kernel (.ok (by decide)), by unfold RestrictedStep; decide⟩

/-- **R31** (`ok`, excluded). The reference mutex, not shared: `endUse(lock)`. Expected: `ok`,
excluded by C22.5 (a). Obtained: `ok`, failing `RestrictedStep`. Twin: `R31_twin`. -/
theorem R31 : EncapsulatedTrace pm kMutex mutexLayout (m0, [], []) refMutexL (m2, regFree, []) ∧
    LStep kMutex mutexLayout (.kernel 0 (.endUse 2)) (m2, regFree, [])
      (m2.set (endUseEff (m2.view 0) 2), regFree, []) ∧
    ¬ RestrictedStep mutexLayout (m2, regFree, []) (.kernel 0 (.endUse 2)) :=
  ⟨refMutex_encap, .kernel ⟨_, .ok (by decide), rfl⟩, by unfold RestrictedStep; decide⟩

/-- `endUse(slot)` by context 0 (O12). -/
def r31t1 : SC := m2.set (endUseEff (m2.view 0) 1)

/-- **R31, twin** (`ok`, admitted). From the reference mutex, not shared: `endUse(slot)`, then
`endUse(lock)`. Expected: both `ok`, admitted; after the first the entry is dead (C12). Obtained:
both `ok` and `EncapStep`; the entry is dead after the first. -/
theorem R31_twin :
    LStep kMutex mutexLayout (.kernel 0 (.endUse 1)) (m2, regFree, []) (r31t1, regFree, []) ∧
    EncapStep pm kMutex mutexLayout (m2, regFree, []) (.kernel 0 (.endUse 1)) (r31t1, regFree, []) ∧
    ¬ (⟨2, none⟩ : SyncEntry).Live r31t1 ∧
    LStep kMutex mutexLayout (.kernel 0 (.endUse 2)) (r31t1, regFree, [])
      (r31t1.set (endUseEff (r31t1.view 0) 2), regFree, []) ∧
    EncapStep pm kMutex mutexLayout (r31t1, regFree, []) (.kernel 0 (.endUse 2))
      (r31t1.set (endUseEff (r31t1.view 0) 2), regFree, []) :=
  ⟨.kernel ⟨_, .ok (by decide), rfl⟩, ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
    by decide, .kernel ⟨_, .ok (by decide), rfl⟩,
    ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩⟩

/-- **R32** (`ok`, excluded). The composite-slot mutex of `R30`: `endUse(a)`. Expected: `ok`,
excluded by C22.5 (b). Obtained: `ok`, failing `RestrictedStep`. Twin: `R32_twin`. -/
theorem R32 : EncapsulatedTrace pm kComp mutexLayout (cs0, [], []) [.newMutex 0 1] (cs0, csReg, []) ∧
    LStep kComp mutexLayout (.kernel 0 (.endUse 2)) (cs0, csReg, [])
      (cs0.set (endUseEff (cs0.view 0) 2), csReg, []) ∧
    ¬ RestrictedStep mutexLayout (cs0, csReg, []) (.kernel 0 (.endUse 2)) :=
  ⟨cs_encap, .kernel ⟨_, .ok (by decide), rfl⟩, by unfold RestrictedStep; decide⟩

/-- **R32, twin** (`ok`, admitted). The composite-slot mutex: `endUse(slot)`. Expected: `ok`,
admitted. Obtained: `ok` and `EncapStep`. -/
theorem R32_twin :
    LStep kComp mutexLayout (.kernel 0 (.endUse 1)) (cs0, csReg, [])
      (cs0.set (endUseEff (cs0.view 0) 1), csReg, []) ∧
    EncapStep pm kComp mutexLayout (cs0, csReg, []) (.kernel 0 (.endUse 1))
      (cs0.set (endUseEff (cs0.view 0) 1), csReg, []) :=
  ⟨.kernel ⟨_, .ok (by decide), rfl⟩, ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩⟩

/-! ## R33: a raw `deriveSync` -/

/-- **R33** (`ok`, excluded). The shared reference mutex: context 1 takes a raw
`deriveSync(guarded)` outside `acquire`. Expected: `ok`, excluded by C22.2; after the step
`grant = none` and an active descendant of `guarded` covers `T`. Obtained: `ok`, failing
`RestrictedStep`; after the step the entry records `grant = none` and the authority 4, active
descendant of `guarded`, covers `T`. Twin: `R26_twin` (the `acquire` of context 1, admitted). -/
theorem R33 : EncapsulatedTrace pm kMutex mutexLayout (m0, [], []) sharedMutexL (m4, regFree, []) ∧
    LStep kMutex mutexLayout (.deriveSync 1 2) (m4, regFree, []) (m5, regFree, []) ∧
    ¬ RestrictedStep mutexLayout (m4, regFree, []) (.deriveSync 1 2) ∧
    regFree = [⟨2, none⟩] ∧ CoveringDesc m5 2 4 :=
  ⟨sharedMutex_encap, .deriveSync grantDiscipline_not_of_i1.1, grantDiscipline_not_of_i1.2.1, rfl,
    by decide⟩

/-! ## R34–R39: `store`, `issue`, `alloc`, `depend` on the controller -/

/-- `z := derive(root_M′, Observe, {slot′})`, authority 4 (O1), beside the reference mutex. -/
def pz : SC := p2.set (deriveEff (p2.view 0) 2 [5] .observe)

/-- The setup of `R34` and `R39`: the reference mutex beside `M′`, then `derive(root_M′,
Observe, {slot′})`. -/
theorem pz_encap : EncapsulatedTrace pm kMutex mutexLayout (p0, [], [])
    (pL ++ [.kernel 0 (.derive 2 [5] .observe)]) (pz, pReg, []) :=
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩
    (.kernel ⟨_, .ok (by decide), rfl⟩) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩ (.kernel (.ok (by decide))) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩
    (.newMutex (st' := (p2, pReg)) ⟨by decide, rfl⟩) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩
    (.kernel ⟨_, .ok (by decide), rfl⟩) .nil

/-- **R34** (`ok`, excluded). The reference mutex, not shared, beside `M′`; `z := derive(root_M′,
Observe, {slot′})`: `store(z, lock)`. Expected: `ok` by Spec 1 §65, excluded by C22.4. Obtained:
`ok`, failing `ControllerRestriction`. Twin: `R34_twin`. -/
theorem R34 : EncapsulatedTrace pm kMutex mutexLayout (p0, [], [])
      (pL ++ [.kernel 0 (.derive 2 [5] .observe)]) (pz, pReg, []) ∧
    LStep kMutex mutexLayout (.kernel 0 (.store 4 2)) (pz, pReg, []) (storeEffC pz 0 4 2, pReg, []) ∧
    ¬ ControllerRestriction pm mutexLayout (pz, pReg, []) (.kernel 0 (.store 4 2))
      (storeEffC pz 0 4 2, pReg, []) :=
  ⟨pz_encap, .kernel (.ok (by decide)), by decide_ctl⟩

/-- **R34, twin** (`ok`, admitted). `store(z, lock′)`. Expected: `ok`, admitted. Obtained: `ok`
and `EncapStep`. -/
theorem R34_twin :
    LStep kMutex mutexLayout (.kernel 0 (.store 4 6)) (pz, pReg, []) (storeEffC pz 0 4 6, pReg, []) ∧
    EncapStep pm kMutex mutexLayout (pz, pReg, []) (.kernel 0 (.store 4 6))
      (storeEffC pz 0 4 6, pReg, []) :=
  ⟨.kernel (.ok (by decide)), ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩⟩

/-- `acquire(e2)` by context 0 in the arena block, before its sharing: the grant 6 (C16). -/
def r35s : SC := deriveSyncEff r21s4 0 5
/-- The registry recording the grant 6. -/
def r35reg : SyncReg := [⟨5, some 6⟩]
/-- The internal `split` of `internal` on `R1` by context 0 (O2): authority 7. -/
def r35a : SC := r35s.set (splitEff (r35s.view 0) 4 [[5]])
/-- The arena registry after an `issue` of `R1` from `r35s` (Spec 1 §77 effect). -/
def r35ar : ArenaReg := r21ar.set 0 (Arena.issueMeta r35s.flat ⟨4, 4, footprint r21s2.P 4, []⟩ [5])

/-- Steps 1 and 2 of the arena block (the arena, then the mutex `M2` guarding `AV`), then the
`acquire` of `e2` by context 0. -/
def r35L : List Label :=
  [.kernel 0 (.derive 2 [5, 6] .modify), .kernel 0 (.store 4 3), .newArena 0 4 4,
   .kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 5 1), .newMutex 0 5, .acquire 0 0]

/-- The setup of `R35` is an `EncapsulatedTrace` (C22, C51.1). -/
theorem r35_encap : EncapsulatedTrace pm kMutex mutexLayout (r21s0, [], []) r35L (r35s, r35reg, r21ar) :=
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩
    (.kernel ⟨_, .ok (by decide), rfl⟩) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩ (.kernel (.ok (by decide))) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩
    (.newArena (st' := (r21s2, r21ar)) (.ok (by decide))) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩
    (.kernel ⟨_, .ok (by decide), rfl⟩) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩ (.kernel (.ok (by decide))) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩
    (.newMutex (st' := (r21s4, r21reg)) ⟨by decide, rfl⟩) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩
    (.acquire (st' := (r35s, r35reg)) ⟨⟨5, none⟩, rfl, by decide, by decide, rfl⟩) .nil

/-- **R35** (`ok`, excluded). Steps 1 and 2 of the arena block (the arena on `ST` with value `AV`,
the mutex `M2` guarding `AV`, not shared); context 0 acquires `e2`; then it issues `R1` into
`lock2`. Expected: `ok` by Spec 1 §77.2, excluded by C22.4. Obtained: `ok`, failing
`ControllerRestriction`. Twin: `R35_twin`. -/
theorem R35 : EncapsulatedTrace pm kMutex mutexLayout (r21s0, [], []) r35L (r35s, r35reg, r21ar) ∧
    LStep kMutex mutexLayout (.issue 0 0 [5] 2) (r35s, r35reg, r21ar)
      (storeEffC r35a 0 7 2, r35reg, r35ar) ∧
    ¬ ControllerRestriction pm mutexLayout (r35s, r35reg, r21ar) (.issue 0 0 [5] 2)
      (storeEffC r35a 0 7 2, r35reg, r35ar) :=
  ⟨r35_encap,
    .issue (st' := (storeEffC r35a 0 7 2, r35ar))
      (.ok rfl (by decide) (by decide) ⟨_, .ok (by decide), rfl⟩ (.ok (by decide))),
    by decide_ctl⟩

/-- **R35, twin** (`ok`, admitted). Context 0 issues `R1` into its local `d0`. Expected: `ok`,
admitted. Obtained: `ok` and `EncapStep`. -/
theorem R35_twin :
    LStep kMutex mutexLayout (.issue 0 0 [5] 7) (r35s, r35reg, r21ar)
      (storeEffC r35a 0 7 7, r35reg, r35ar) ∧
    EncapStep pm kMutex mutexLayout (r35s, r35reg, r21ar) (.issue 0 0 [5] 7)
      (storeEffC r35a 0 7 7, r35reg, r35ar) :=
  ⟨.issue (st' := (storeEffC r35a 0 7 7, r35ar))
      (.ok rfl (by decide) (by decide) ⟨_, .ok (by decide), rfl⟩ (.ok (by decide))),
    ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩⟩

/-- **R36** (`ok`, excluded). The reference mutex, not shared, beside `M′`: `alloc(provider =
slot, owner = lock)` of one leaf. Datum of the provider metadata: any. Expected: `ok` by Spec 1
§71.3, excluded by C22.4 (`alloc` using the controller leaf itself as the owner). Obtained: `ok`,
failing `ControllerRestriction` for every datum: the owner is the controller. Twin: `R36_twin`. -/
theorem R36 : EncapsulatedTrace pm kMutex mutexLayout (p0, [], []) pL (p2, pReg, []) ∧
    LStep kMutex mutexLayout (.kernel 0 (.alloc 1 2 [(none, 0)])) (p2, pReg, [])
      (p2.set (allocEff (p2.view 0) 2 [(none, 0)]), pReg, []) ∧
    ¬ ControllerRestriction pm mutexLayout (p2, pReg, []) (.kernel 0 (.alloc 1 2 [(none, 0)]))
      (p2.set (allocEff (p2.view 0) 2 [(none, 0)]), pReg, []) :=
  ⟨p_encap, .kernel ⟨_, .ok (by decide) trivial, rfl⟩, fun h =>
    (ctl_alloc_one (ctl := 2) (by decide)).1 h (by decide) (.inr (.inl rfl)) (by decide)⟩

/-- **R36, twin** (`ok`, admitted). `alloc(provider = slot, owner = lock′)`. Datum of the
provider metadata: the accesses of this step to the metadata of the provider cannot write `lock`
(`pm` does not designate leaf 2 at this step). Expected: `ok`, admitted. Obtained: `ok` and
`EncapStep` for every such datum. -/
theorem R36_twin (hpm : pm (p2, pReg, []) 0 1 6 [(none, 0)] 2 = false) :
    LStep kMutex mutexLayout (.kernel 0 (.alloc 1 6 [(none, 0)])) (p2, pReg, [])
      (p2.set (allocEff (p2.view 0) 6 [(none, 0)]), pReg, []) ∧
    EncapStep pm kMutex mutexLayout (p2, pReg, []) (.kernel 0 (.alloc 1 6 [(none, 0)]))
      (p2.set (allocEff (p2.view 0) 6 [(none, 0)]), pReg, []) :=
  ⟨.kernel ⟨_, .ok (by decide) trivial, rfl⟩,
    ⟨by unfold RestrictedStep; decide, (ctl_alloc_one (ctl := 2) (by decide)).2 fun _ h => by
      rcases h with h | h | h
      · exact absurd (h.symm.trans hpm) (by decide)
      · cases h
      · exact absurd h (by decide), by decide⟩⟩

/-- **R37** (`ok`, admitted). The reference mutex, not shared: `alloc(provider = slot, owner =
M)` of one leaf. Datum of the provider metadata: the accesses of this step to the metadata of the
provider cannot write `lock` (`pm` does not designate leaf 2 at this step). Expected: `ok`,
admitted by C22.4 (naming a place that contains the controller is not touching it; C13.5).
Obtained: `ok` and `EncapStep` for every such datum. No twin. -/
theorem R37 (hpm : pm (m2, regFree, []) 0 1 0 [(none, 0)] 2 = false) :
    EncapsulatedTrace pm kMutex mutexLayout (m0, [], []) refMutexL (m2, regFree, []) ∧
    LStep kMutex mutexLayout (.kernel 0 (.alloc 1 0 [(none, 0)])) (m2, regFree, [])
      (m2.set (allocEff (m2.view 0) 0 [(none, 0)]), regFree, []) ∧
    EncapStep pm kMutex mutexLayout (m2, regFree, []) (.kernel 0 (.alloc 1 0 [(none, 0)]))
      (m2.set (allocEff (m2.view 0) 0 [(none, 0)]), regFree, []) :=
  ⟨refMutex_encap, .kernel ⟨_, .ok (by decide) trivial, rfl⟩,
    ⟨by unfold RestrictedStep; decide, (ctl_alloc_one (ctl := 2) (by decide)).2 fun _ h => by
      rcases h with h | h | h
      · exact absurd (h.symm.trans hpm) (by decide)
      · cases h
      · exact absurd h (by decide), by decide⟩⟩

/-- **R38** (`ok`, excluded). The reference mutex, not shared, beside `M′`: `alloc(provider = M,
owner = lock′)` of one leaf. Datum of the provider metadata: the accesses of this step to the
metadata of the provider may write `lock` (`pm` designates leaf 2 at this step). Expected: `ok`,
excluded by C22.4 (`alloc` whose provider-metadata accesses may write the controller leaf).
Obtained: `ok`, failing `ControllerRestriction` for every such datum. Twin: `R38_twin`. -/
theorem R38 (hpm : pm (p2, pReg, []) 0 0 6 [(none, 0)] 2 = true) :
    EncapsulatedTrace pm kMutex mutexLayout (p0, [], []) pL (p2, pReg, []) ∧
    LStep kMutex mutexLayout (.kernel 0 (.alloc 0 6 [(none, 0)])) (p2, pReg, [])
      (p2.set (allocEff (p2.view 0) 6 [(none, 0)]), pReg, []) ∧
    ¬ ControllerRestriction pm mutexLayout (p2, pReg, []) (.kernel 0 (.alloc 0 6 [(none, 0)]))
      (p2.set (allocEff (p2.view 0) 6 [(none, 0)]), pReg, []) :=
  ⟨p_encap, .kernel ⟨_, .ok (by decide) trivial, rfl⟩, fun h =>
    (ctl_alloc_one (ctl := 2) (by decide)).1 h (by decide) (.inl hpm) (by decide)⟩

/-- **R38, twin** (`ok`, admitted). The step of `R38`; datum of the provider metadata: the
accesses of this step to the metadata of the provider cannot write `lock` (`pm` does not designate
leaf 2 at this step). Expected: `ok`, admitted by C22.4 (naming a structural place that contains
the controller does not establish that the controller leaf is accessed or modified). Obtained:
`ok` and `EncapStep` for every such datum. -/
theorem R38_twin (hpm : pm (p2, pReg, []) 0 0 6 [(none, 0)] 2 = false) :
    LStep kMutex mutexLayout (.kernel 0 (.alloc 0 6 [(none, 0)])) (p2, pReg, [])
      (p2.set (allocEff (p2.view 0) 6 [(none, 0)]), pReg, []) ∧
    EncapStep pm kMutex mutexLayout (p2, pReg, []) (.kernel 0 (.alloc 0 6 [(none, 0)]))
      (p2.set (allocEff (p2.view 0) 6 [(none, 0)]), pReg, []) :=
  ⟨.kernel ⟨_, .ok (by decide) trivial, rfl⟩,
    ⟨by unfold RestrictedStep; decide, (ctl_alloc_one (ctl := 2) (by decide)).2 fun _ h => by
      rcases h with h | h | h
      · exact absurd (h.symm.trans hpm) (by decide)
      · cases h
      · exact absurd h (by decide), by decide⟩⟩

/-- **R39** (`ok`, admitted; `ok`, admitted). The reference mutex, not shared, beside `M′`; `a :=
derive(root_M′, Observe, {slot′})`: `depend(lock, a)`, and from the same state `depend(lock′,
a)`. Expected: both `ok` by Spec 1 §64, admitted by C22.4 (a change of dependency alone is not an
access). Obtained: both `ok` and `EncapStep`. -/
theorem R39 : EncapsulatedTrace pm kMutex mutexLayout (p0, [], [])
      (pL ++ [.kernel 0 (.derive 2 [5] .observe)]) (pz, pReg, []) ∧
    LStep kMutex mutexLayout (.kernel 0 (.depend 2 4)) (pz, pReg, [])
      (dependEffC pz 0 2 4, pReg, []) ∧
    EncapStep pm kMutex mutexLayout (pz, pReg, []) (.kernel 0 (.depend 2 4))
      (dependEffC pz 0 2 4, pReg, []) ∧
    LStep kMutex mutexLayout (.kernel 0 (.depend 6 4)) (pz, pReg, [])
      (dependEffC pz 0 6 4, pReg, []) ∧
    EncapStep pm kMutex mutexLayout (pz, pReg, []) (.kernel 0 (.depend 6 4))
      (dependEffC pz 0 6 4, pReg, []) :=
  ⟨pz_encap, .kernel (.ok (by decide)), ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
    .kernel (.ok (by decide)), ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩⟩

/-! ## R40–R44: rights justified through a live `guarded` (C22.6) -/

/-- `acquire(e)` by context 0 from the shared reference mutex: the grant 4, held by frame 0. -/
def r40s2 : SC := deriveSyncEff m4 0 2

/-- **R40** (`ok`, excluded; `ok`, admitted; `ok`, admitted). The shared reference mutex. 1.
context 1 reads `T` with `guarded` as access authority; 2. context 0 acquires the entry; 3.
context 0 writes `T` through the grant. Expected: 1 `ok` by O9.2 through the third clause of
Spec 1 §43, excluded by C22.6; 2 and 3, without step 1, `ok` and admitted. Obtained: 1 `ok`,
failing `RightsReadFree`; 2 and 3 `ok` and `EncapStep`. Twin: `R40_twin`. -/
theorem R40 : EncapsulatedTrace pm kMutex mutexLayout (m0, [], []) sharedMutexL (m4, regFree, []) ∧
    LStep kMutex mutexLayout (.kernel 1 (.read 2 [3])) (m4, regFree, [])
      (m4.set (m4.view 1), regFree, []) ∧
    ¬ RightsReadFree kMutex mutexLayout (m4, regFree, []) (.kernel 1 (.read 2 [3])) ∧
    LStep kMutex mutexLayout (.acquire 0 0) (m4, regFree, []) (r40s2, [⟨2, some 4⟩], []) ∧
    EncapStep pm kMutex mutexLayout (m4, regFree, []) (.acquire 0 0) (r40s2, [⟨2, some 4⟩], []) ∧
    LStep kMutex mutexLayout (.kernel 0 (.write 4 [3])) (r40s2, [⟨2, some 4⟩], [])
      (r40s2.set (write3Eff (r40s2.view 0) [3]), [⟨2, some 4⟩], []) ∧
    EncapStep pm kMutex mutexLayout (r40s2, [⟨2, some 4⟩], []) (.kernel 0 (.write 4 [3]))
      (r40s2.set (write3Eff (r40s2.view 0) [3]), [⟨2, some 4⟩], []) :=
  ⟨sharedMutex_encap, .kernel ⟨_, .ok (by decide), rfl⟩, by decide,
    .acquire (st' := (r40s2, [⟨2, some 4⟩])) ⟨⟨2, none⟩, rfl, by decide, by decide, rfl⟩,
    ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩, .kernel ⟨_, .ok (by decide), rfl⟩,
    ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩⟩

/-- **R40, twin** (`reject`). Step 1 of `R40` while the grant of step 2 is active. Expected:
`reject` by O9.2. Obtained: `reject`. -/
theorem R40_twin : opStepC kMutex.toK (.read 2 [3]) 1 r40s2 .reject :=
  ⟨_, .reject (by decide), rfl⟩

/-- Statics of the reference mutex with a local `Y` of one leaf, `Uninit` (Spec 1 §47): `M`
(places 0, 1, 2), `T` (place 3) of one leaf owned by `M`, `Y` (place 4). Root authorities: 0 of
`M`, 1 of `T` (held by `M`), 2 of `Y`. -/
def mutexYStatics : Statics :=
  [((none, none, 0), false), ((some 0, none, 0), false), ((some 0, none, 0), true),
   ((none, some 0, 0), true), ((none, none, 0), false)]

/-- Initial state (Spec 1 §47). -/
def y0 : SC := SC.ofS3 (S3.init mutexYStatics)
/-- `write3(Y)` through `root_Y` (O10). -/
def r41s1 : SC := y0.set (write3Eff (y0.view 0) [4])
/-- `guarded := derive(root_T, Modify, footprint(T))`, authority 3 (O1). -/
def r41s2 : SC := r41s1.set (deriveEff (r41s1.view 0) 1 [3] .modify)
/-- `store(guarded, slot)` (O8). -/
def r41s3 : SC := storeEffC r41s2 0 3 1
/-- `z := derive(root_Y, Modify)`, authority 4 (O1). -/
def r41s4 : SC := r41s3.set (deriveEff (r41s3.view 0) 2 [4] .modify)
/-- `store(z, T)` (O8): `z` held by the protected leaf `T`. -/
def r41s5 : SC := storeEffC r41s4 0 4 3
/-- `o1 := derive(root_M, Observe, {slot, lock})`, authority 5 (O1), after `newMutex`. -/
def r41s6 : SC := r41s5.set (deriveEff (r41s5.view 0) 0 [1, 2] .observe)
/-- `spawn` of context 1 yielding `o1` (C4). -/
def r41s7 : SC := spawnEff r41s6 0 [5] []
/-- The registry with the entry of `guarded`, available. -/
def yReg : SyncReg := [⟨3, none⟩]
/-- Step 2: `acquire(e)` by context 0: the grant 6 (C16). -/
def r41s8 : SC := deriveSyncEff r41s7 0 3
/-- The registry recording the grant 6. -/
def yReg6 : SyncReg := [⟨3, some 6⟩]
/-- Step 3: `write3(Y)` by context 0 through `z` (O10). -/
def r41s9 : SC := r41s8.set (write3Eff (r41s8.view 0) [4])

/-- The setup of `R41`: `Y` initialized, steps 1 and 2 of the construction, `z := derive(root_Y,
Modify)` stored in `T`, `newMutex(guarded)`, then the sharing with context 1. -/
def r41L : List Label :=
  [.kernel 0 (.write 2 [4]), .kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 3 1),
   .kernel 0 (.derive 2 [4] .modify), .kernel 0 (.store 4 3), .newMutex 0 3,
   .kernel 0 (.derive 0 [1, 2] .observe), .spawn 0 [5] []]

/-- The setup of `R41` is an `EncapsulatedTrace` (C22, C51.1). -/
theorem r41_encap : EncapsulatedTrace pm kMutex mutexLayout (y0, [], []) r41L (r41s7, yReg, []) :=
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩
    (.kernel ⟨_, .ok (by decide), rfl⟩) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩
    (.kernel ⟨_, .ok (by decide), rfl⟩) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩ (.kernel (.ok (by decide))) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩
    (.kernel ⟨_, .ok (by decide), rfl⟩) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩ (.kernel (.ok (by decide))) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩
    (.newMutex (st' := (r41s5, yReg)) ⟨by decide, rfl⟩) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩
    (.kernel ⟨_, .ok (by decide), rfl⟩) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩ (.spawn (.ok (by decide))) .nil

/-- **R41** (`ok`, excluded; three steps `ok`, admitted). The shared reference mutex with `T` of
one leaf and a local `Y`, initialized; before `newMutex`, `z := derive(root_Y, Modify)` stored in
`T`. 1. context 1 reads `Y` with `z` as access authority; 2. context 0 acquires the entry; 3.
context 0 writes `Y` through `z`; 4. context 0 reads `Y` through `z`. Expected: 1 `ok`, excluded
by C22.6 (the justification goes through `guarded`); 2–4, without step 1, `ok` and admitted, the
justification of 3 and 4 going through the grant. Obtained: 1 `ok`, failing `RightsReadFree`;
2–4 `ok` and `EncapStep`. Twin: steps 3 and 4. -/
theorem R41 : EncapsulatedTrace pm kMutex mutexLayout (y0, [], []) r41L (r41s7, yReg, []) ∧
    LStep kMutex mutexLayout (.kernel 1 (.read 4 [4])) (r41s7, yReg, [])
      (r41s7.set (r41s7.view 1), yReg, []) ∧
    ¬ RightsReadFree kMutex mutexLayout (r41s7, yReg, []) (.kernel 1 (.read 4 [4])) ∧
    LStep kMutex mutexLayout (.acquire 0 0) (r41s7, yReg, []) (r41s8, yReg6, []) ∧
    EncapStep pm kMutex mutexLayout (r41s7, yReg, []) (.acquire 0 0) (r41s8, yReg6, []) ∧
    LStep kMutex mutexLayout (.kernel 0 (.write 4 [4])) (r41s8, yReg6, []) (r41s9, yReg6, []) ∧
    EncapStep pm kMutex mutexLayout (r41s8, yReg6, []) (.kernel 0 (.write 4 [4])) (r41s9, yReg6, []) ∧
    LStep kMutex mutexLayout (.kernel 0 (.read 4 [4])) (r41s9, yReg6, [])
      (r41s9.set (r41s9.view 0), yReg6, []) ∧
    EncapStep pm kMutex mutexLayout (r41s9, yReg6, []) (.kernel 0 (.read 4 [4]))
      (r41s9.set (r41s9.view 0), yReg6, []) :=
  ⟨r41_encap, .kernel ⟨_, .ok (by decide), rfl⟩, by decide,
    .acquire (st' := (r41s8, yReg6)) ⟨⟨3, none⟩, rfl, by decide, by decide, rfl⟩,
    ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩, .kernel ⟨_, .ok (by decide), rfl⟩,
    ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩, .kernel ⟨_, .ok (by decide), rfl⟩,
    ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩⟩

/-- `guarded := derive(root_T, Modify, footprint(T))`, authority 3 (O1). -/
def r42s1 : SC := y0.set (deriveEff (y0.view 0) 1 [3] .modify)
/-- `store(guarded, slot)` (O8). -/
def r42s2 : SC := storeEffC r42s1 0 3 1
/-- `write3(Y2)` through `root_Y2` (O10), after `newMutex`. -/
def r42s3 : SC := r42s2.set (write3Eff (r42s2.view 0) [4])
/-- `z2 := derive(root_Y2, Modify)`, authority 4 (O1). -/
def r42s4 : SC := r42s3.set (deriveEff (r42s3.view 0) 2 [4] .modify)
/-- `o := derive(root_M, Observe, {lock})`, authority 5 (O1). -/
def r42s5 : SC := r42s4.set (deriveEff (r42s4.view 0) 0 [2] .observe)
/-- `spawn` of context 1 yielding `o` (C4). -/
def r42s6 : SC := spawnEff r42s5 0 [5] []
/-- Step 1: `store(z2, T)` by context 0 (O8). -/
def r42s7 : SC := storeEffC r42s6 0 4 3
/-- Step 2: `acquire(e)` by context 1: the grant 6, held by frame 1 (C16). -/
def r42s8 : SC := deriveSyncEff r42s7 1 3
/-- Twin: `acquire(e)` by context 0: the grant 6, held by frame 0 (C16). -/
def r42t1 : SC := deriveSyncEff r42s6 0 3

/-- The setup of `R42`: the reference mutex, not shared, with a local `Y2` (place 4); `Y2`
initialized; `z2 := derive(root_Y2, Modify)`; `o := derive(root_M, Observe, {lock})`; the `spawn`
of context 1 yielding `o`. -/
def r42L : List Label :=
  [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 3 1), .newMutex 0 3,
   .kernel 0 (.write 2 [4]), .kernel 0 (.derive 2 [4] .modify), .kernel 0 (.derive 0 [2] .observe),
   .spawn 0 [5] []]

/-- The setup of `R42` is an `EncapsulatedTrace` (C22, C51.1). -/
theorem r42_encap : EncapsulatedTrace pm kMutex mutexLayout (y0, [], []) r42L (r42s6, yReg, []) :=
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩
    (.kernel ⟨_, .ok (by decide), rfl⟩) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩ (.kernel (.ok (by decide))) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩
    (.newMutex (st' := (r42s2, yReg)) ⟨by decide, rfl⟩) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩
    (.kernel ⟨_, .ok (by decide), rfl⟩) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩
    (.kernel ⟨_, .ok (by decide), rfl⟩) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩
    (.kernel ⟨_, .ok (by decide), rfl⟩) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩ (.spawn (.ok (by decide))) .nil

/-- **R42** (`ok`, excluded; `ok`; `ok`). The reference mutex with a local `Y2`, initialized; `z2
:= derive(root_Y2, Modify)`; `o := derive(root_M, Observe, {lock})`; the `spawn` of context 1
yielding `o`. 1. context 0 stores `z2` in `T` without grant; 2. context 1 acquires the entry; 3.
context 1 reads `T` through its grant. Expected: 1 `ok` by O8, excluded by C22.6; 2 `ok`; 3
`ok`. Obtained: 1 `ok`, failing `RightsReadFree`; 2, 3 `ok`. Twin: `R42_twin`. -/
theorem R42 : EncapsulatedTrace pm kMutex mutexLayout (y0, [], []) r42L (r42s6, yReg, []) ∧
    LStep kMutex mutexLayout (.kernel 0 (.store 4 3)) (r42s6, yReg, []) (r42s7, yReg, []) ∧
    ¬ RightsReadFree kMutex mutexLayout (r42s6, yReg, []) (.kernel 0 (.store 4 3)) ∧
    AcquireOk kMutex mutexLayout r42s7 yReg 1 0 (r42s8, yReg6) ∧
    opStepC kMutex.toK (.read 6 [3]) 1 r42s8 (.ok (r42s8.set (r42s8.view 1))) :=
  ⟨r42_encap, .kernel (.ok (by decide)), by decide, ⟨⟨3, none⟩, rfl, by decide, by decide, rfl⟩,
    ⟨_, .ok (by decide), rfl⟩⟩

/-- **R42, twin** (`ok`, admitted). From the setup of `R42`: context 0 acquires the entry, then
stores `z2` in `T`. Expected: `ok`, admitted. Obtained: both `ok` and `EncapStep`. -/
theorem R42_twin :
    LStep kMutex mutexLayout (.acquire 0 0) (r42s6, yReg, []) (r42t1, yReg6, []) ∧
    EncapStep pm kMutex mutexLayout (r42s6, yReg, []) (.acquire 0 0) (r42t1, yReg6, []) ∧
    LStep kMutex mutexLayout (.kernel 0 (.store 4 3)) (r42t1, yReg6, [])
      (storeEffC r42t1 0 4 3, yReg6, []) ∧
    EncapStep pm kMutex mutexLayout (r42t1, yReg6, []) (.kernel 0 (.store 4 3))
      (storeEffC r42t1 0 4 3, yReg6, []) :=
  ⟨.acquire (st' := (r42t1, yReg6)) ⟨⟨3, none⟩, rfl, by decide, by decide, rfl⟩,
    ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩, .kernel (.ok (by decide)),
    ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩⟩

/-- Statics of the reference mutex beside a free arena of frame 0 (Spec 1 §47): `M` (places 0, 1,
2), `T` (place 3, the leaf `t`) owned by `M`; the storage `ST0` (place 4, one leaf: the region
`R1`) and the arena value `AV0` (place 5, `Init`), both of frame 0. Root authorities: 0 of `M`, 1
of `T` (held by `M`), 2 of `ST0`, 3 of `AV0`. -/
def mutexArenaStatics : Statics :=
  [((none, none, 0), false), ((some 0, none, 0), false), ((some 0, none, 0), true),
   ((none, some 0, 0), true), ((none, none, 0), false), ((none, none, 0), true)]

/-- Initial state (Spec 1 §47). -/
def r43s0 : SC := SC.ofS3 (S3.init mutexArenaStatics)
/-- `guarded := derive(root_T, Modify, footprint(T))`, authority 4 (O1). -/
def r43s1 : SC := r43s0.set (deriveEff (r43s0.view 0) 1 [3] .modify)
/-- `store(guarded, slot)` (O8). -/
def r43s2 : SC := storeEffC r43s1 0 4 1
/-- `internal0 := derive(root_ST0, Modify, footprint(ST0))`, authority 5 (O1). -/
def r43s3 : SC := r43s2.set (deriveEff (r43s2.view 0) 2 [4] .modify)
/-- `store(internal0, AV0)` (O8). -/
def r43s4 : SC := storeEffC r43s3 0 5 5
/-- The arena registry after `newArena(ST0, internal0)` (Spec 1 §76). -/
def r43ar : ArenaReg := [⟨4, 5, footprint r43s4.P 4, []⟩]
/-- `o := derive(root_M, Observe, {lock})`, authority 6 (O1). -/
def r43s5 : SC := r43s4.set (deriveEff (r43s4.view 0) 0 [2] .observe)
/-- `spawn` of context 1 yielding `o` (C4). -/
def r43s6 : SC := spawnEff r43s5 0 [6] []
/-- The registry with the entry of `guarded`, available. -/
def r43reg : SyncReg := [⟨4, none⟩]
/-- Step 1, internal `split` of `internal0` on `R1` by context 0 (O2): authority 7. -/
def r43s6a : SC := r43s6.set (splitEff (r43s6.view 0) 5 [[4]])
/-- Step 1: the block 7 stored in `t` (O8). -/
def r43s7 : SC := storeEffC r43s6a 0 7 3
/-- The arena registry after an `issue` of `R1` from `r43s6`. -/
def r43ar1 : ArenaReg := r43ar.set 0 (Arena.issueMeta r43s6.flat ⟨4, 5, footprint r43s4.P 4, []⟩ [4])
/-- Step 2: `acquire(e)` by context 1: the grant 8, held by frame 1 (C16). -/
def r43s8 : SC := deriveSyncEff r43s7 1 4
/-- Twin: `acquire(e)` by context 0: the grant 7, held by frame 0 (C16). -/
def r43t1 : SC := deriveSyncEff r43s6 0 4
/-- Twin: internal `split` of `internal0` on `R1` by context 0 (O2): authority 8. -/
def r43t1a : SC := r43t1.set (splitEff (r43t1.view 0) 5 [[4]])
/-- Twin: the block 8 stored in `t` (O8). -/
def r43t2 : SC := storeEffC r43t1a 0 8 3
/-- Twin: the arena registry after the `issue`. -/
def r43ar2 : ArenaReg := r43ar.set 0 (Arena.issueMeta r43t1.flat ⟨4, 5, footprint r43s4.P 4, []⟩ [4])

/-- The setup of `R43`: the reference mutex, the free arena, then `o := derive(root_M, Observe,
{lock})` and the `spawn` of context 1 yielding `o`. -/
def r43L : List Label :=
  [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 4 1), .newMutex 0 4,
   .kernel 0 (.derive 2 [4] .modify), .kernel 0 (.store 5 5), .newArena 0 4 5,
   .kernel 0 (.derive 0 [2] .observe), .spawn 0 [6] []]

/-- The setup of `R43` is an `EncapsulatedTrace` (C22, C51.1). -/
theorem r43_encap :
    EncapsulatedTrace pm kMutex mutexLayout (r43s0, [], []) r43L (r43s6, r43reg, r43ar) :=
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩
    (.kernel ⟨_, .ok (by decide), rfl⟩) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩ (.kernel (.ok (by decide))) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩
    (.newMutex (st' := (r43s2, r43reg)) ⟨by decide, rfl⟩) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩
    (.kernel ⟨_, .ok (by decide), rfl⟩) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩ (.kernel (.ok (by decide))) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩
    (.newArena (st' := (r43s4, r43ar)) (.ok (by decide))) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩
    (.kernel ⟨_, .ok (by decide), rfl⟩) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩ (.spawn (.ok (by decide))) .nil

/-- **R43** (`ok`, excluded; `ok`; `ok`). The setup of `R42` without `Y2`, with a free arena of
frame 0 with one region `R1`; `t` the leaf of `T`. 1. context 0 issues `R1` into `t` without
grant; 2. context 1 acquires the entry; 3. context 1 reads `t` through its grant. Expected: 1 `ok`
by Spec 1 §77, excluded by C22.6; 2 `ok`; 3 `ok`. Obtained: 1 `ok`, failing `RightsReadFree`; 2, 3
`ok`. Twin: `R43_twin`. -/
theorem R43 : EncapsulatedTrace pm kMutex mutexLayout (r43s0, [], []) r43L (r43s6, r43reg, r43ar) ∧
    LStep kMutex mutexLayout (.issue 0 0 [4] 3) (r43s6, r43reg, r43ar) (r43s7, r43reg, r43ar1) ∧
    ¬ RightsReadFree kMutex mutexLayout (r43s6, r43reg, r43ar) (.issue 0 0 [4] 3) ∧
    AcquireOk kMutex mutexLayout r43s7 r43reg 1 0 (r43s8, [⟨4, some 8⟩]) ∧
    opStepC kMutex.toK (.read 8 [3]) 1 r43s8 (.ok (r43s8.set (r43s8.view 1))) :=
  ⟨r43_encap,
    .issue (st' := (r43s7, r43ar1))
      (.ok rfl (by decide) (by decide) ⟨_, .ok (by decide), rfl⟩ (.ok (by decide))),
    by decide, ⟨⟨4, none⟩, rfl, by decide, by decide, rfl⟩, ⟨_, .ok (by decide), rfl⟩⟩

/-- **R43, twin** (`ok`, admitted). From the setup of `R43`: context 0 acquires the entry, issues
`R1` into `t`, then unlocks the entry. Expected: `ok`, admitted. Obtained: each step `ok` and
`EncapStep`. -/
theorem R43_twin :
    LStep kMutex mutexLayout (.acquire 0 0) (r43s6, r43reg, r43ar) (r43t1, [⟨4, some 7⟩], r43ar) ∧
    EncapStep pm kMutex mutexLayout (r43s6, r43reg, r43ar) (.acquire 0 0)
      (r43t1, [⟨4, some 7⟩], r43ar) ∧
    LStep kMutex mutexLayout (.issue 0 0 [4] 3) (r43t1, [⟨4, some 7⟩], r43ar)
      (r43t2, [⟨4, some 7⟩], r43ar2) ∧
    EncapStep pm kMutex mutexLayout (r43t1, [⟨4, some 7⟩], r43ar) (.issue 0 0 [4] 3)
      (r43t2, [⟨4, some 7⟩], r43ar2) ∧
    LStep kMutex mutexLayout (.unlock 0 0) (r43t2, [⟨4, some 7⟩], r43ar2)
      (prospectiveUnlock r43t2 0 7, r43reg, r43ar2) ∧
    EncapStep pm kMutex mutexLayout (r43t2, [⟨4, some 7⟩], r43ar2) (.unlock 0 0)
      (prospectiveUnlock r43t2 0 7, r43reg, r43ar2) :=
  ⟨.acquire (st' := (r43t1, [⟨4, some 7⟩])) ⟨⟨4, none⟩, rfl, by decide, by decide, rfl⟩,
    ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
    .issue (st' := (r43t2, r43ar2))
      (.ok rfl (by decide) (by decide) ⟨_, .ok (by decide), rfl⟩ (.ok (by decide))),
    ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
    .unlock (st' := (prospectiveUnlock r43t2 0 7, r43reg))
      ⟨⟨4, some 7⟩, 7, rfl, by decide, rfl, by decide, by decide, by decide, rfl⟩,
    ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩⟩

/-- Statics of two nested mutexes in frame 0 (Spec 1 §47): `M = {slot, lock}` (places 0, 1, 2);
its protected root `T` (place 3), owned by `M`, made of `N = {slot_n, lock_n}` (places 4, 5, 6);
the protected root `T_n` (place 7) of `N`, owned by `N`. `slot`, `slot_n` `Uninit`; `lock`,
`lock_n`, `T_n` `Init`. Root authorities: 0 of `M`, 1 of `T` (held by `M`), 2 of `T_n` (held by
`N`). -/
def nestedStatics : Statics :=
  [((none, none, 0), false), ((some 0, none, 0), false), ((some 0, none, 0), true),
   ((none, some 0, 0), false), ((some 3, some 0, 0), false), ((some 4, some 0, 0), false),
   ((some 4, some 0, 0), true), ((none, some 4, 0), true)]

/-- Initial state (Spec 1 §47). -/
def r44s0 : SC := SC.ofS3 (S3.init nestedStatics)
/-- `guarded_n := derive(root_T_n, Modify, footprint(T_n))`, authority 3 (O1). -/
def r44s1 : SC := r44s0.set (deriveEff (r44s0.view 0) 2 [7] .modify)
/-- `store(guarded_n, slot_n)` (O8). -/
def r44s2 : SC := storeEffC r44s1 0 3 5
/-- `guarded := derive(root_T, Modify, footprint(T))`, authority 4 (O1). -/
def r44s3 : SC := r44s2.set (deriveEff (r44s2.view 0) 1 [5, 6] .modify)
/-- `store(guarded, slot)` (O8). -/
def r44s4 : SC := storeEffC r44s3 0 4 1
/-- The registry with `e_n` (entry 0) and `e` (entry 1), available. -/
def r44reg : SyncReg := [⟨3, none⟩, ⟨4, none⟩]
/-- Twin: `acquire(e)` by context 0: the grant 5 (C16). -/
def r44t1 : SC := deriveSyncEff r44s4 0 4
/-- Twin: the registry recording the grant 5 for `e`. -/
def r44reg5 : SyncReg := [⟨3, none⟩, ⟨4, some 5⟩]

/-- The construction of `N`, then of `M`, each as the reference mutex. -/
def r44L : List Label :=
  [.kernel 0 (.derive 2 [7] .modify), .kernel 0 (.store 3 5), .newMutex 0 3,
   .kernel 0 (.derive 1 [5, 6] .modify), .kernel 0 (.store 4 1), .newMutex 0 4]

/-- The setup of `R44` is an `EncapsulatedTrace` (C22, C51.1). -/
theorem r44_encap : EncapsulatedTrace pm kTwo mutexLayout (r44s0, [], []) r44L (r44s4, r44reg, []) :=
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩
    (.kernel ⟨_, .ok (by decide), rfl⟩) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩ (.kernel (.ok (by decide))) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩
    (.newMutex (st' := (r44s2, [⟨3, none⟩])) ⟨by decide, rfl⟩) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩
    (.kernel ⟨_, .ok (by decide), rfl⟩) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩ (.kernel (.ok (by decide))) <|
  .cons ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩
    (.newMutex (st' := (r44s4, r44reg)) ⟨by decide, rfl⟩) .nil

/-- **R44** (`ok`, excluded). Two nested mutexes in frame 0, not shared: `N = {slot_n, lock_n}`,
entry `e_n`, built first; then `M`, entry `e`, whose protected data `T` contains `N`; context 0
requests `resetLock(e_n)` without the grant of `e`. Expected: `ok`, excluded by C22.6: the chain of
the right on `slot_n` contains the `guarded` of another live entry. Obtained: `ok`, failing
`RightsReadFree`. Twin: `R44_twin`. -/
theorem R44 : EncapsulatedTrace pm kTwo mutexLayout (r44s0, [], []) r44L (r44s4, r44reg, []) ∧
    LStep kTwo mutexLayout (.resetLock 0 0) (r44s4, r44reg, []) (r44s4, r44reg, []) ∧
    ¬ RightsReadFree kTwo mutexLayout (r44s4, r44reg, []) (.resetLock 0 0) :=
  ⟨r44_encap,
    .resetLock (st' := (r44s4, r44reg))
      ⟨⟨3, none⟩, rfl, by decide, by decide, by decide, by decide, rfl⟩, by decide⟩

/-- **R44, twin** (`ok`, admitted). Context 0 acquires `e`, then requests `resetLock(e_n)`.
Expected: `ok`, admitted. Obtained: both `ok` and `EncapStep`. -/
theorem R44_twin :
    LStep kTwo mutexLayout (.acquire 0 1) (r44s4, r44reg, []) (r44t1, r44reg5, []) ∧
    EncapStep pm kTwo mutexLayout (r44s4, r44reg, []) (.acquire 0 1) (r44t1, r44reg5, []) ∧
    LStep kTwo mutexLayout (.resetLock 0 0) (r44t1, r44reg5, []) (r44t1, r44reg5, []) ∧
    EncapStep pm kTwo mutexLayout (r44t1, r44reg5, []) (.resetLock 0 0) (r44t1, r44reg5, []) :=
  ⟨.acquire (st' := (r44t1, r44reg5)) ⟨⟨4, none⟩, rfl, by decide, by decide, rfl⟩,
    ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩,
    .resetLock (st' := (r44t1, r44reg5))
      ⟨⟨3, none⟩, rfl, by decide, by decide, by decide, by decide, rfl⟩,
    ⟨by unfold RestrictedStep; decide, by decide_ctl, by decide⟩⟩

/-! ## R45: a conflict through an inherited `writeShared` -/

/-- **R45** (`ok`, excluded; `ok`, excluded). The shared reference mutex; from the same state:
the inherited `writeShared` of context 0 on `{lock}` through `root_M`; the `read3(lock)` of
context 1 through `o1`. Expected: both `ok`, each excluded by C22.4. Obtained: both `ok`, each
failing `ControllerRestriction`. No twin. -/
theorem R45 : EncapsulatedTrace pm kMutex mutexLayout (m0, [], []) sharedMutexL (m4, regFree, []) ∧
    LStep kMutex mutexLayout (.kernel 0 (.writeShared 0 [2])) (m4, regFree, [])
      (m4.set (write3Eff (m4.view 0) [2]), regFree, []) ∧
    ¬ ControllerRestriction pm mutexLayout (m4, regFree, []) (.kernel 0 (.writeShared 0 [2]))
      (m4.set (write3Eff (m4.view 0) [2]), regFree, []) ∧
    LStep kMutex mutexLayout (.kernel 1 (.read 3 [2])) (m4, regFree, [])
      (m4.set (m4.view 1), regFree, []) ∧
    ¬ ControllerRestriction pm mutexLayout (m4, regFree, []) (.kernel 1 (.read 3 [2]))
      (m4.set (m4.view 1), regFree, []) :=
  ⟨sharedMutex_encap, .kernel ⟨_, .ok (by decide), rfl⟩, by decide_ctl, .kernel ⟨_, .ok (by decide), rfl⟩,
    by decide_ctl⟩

/-! ## R59: capability attributed in the requested mode (C43) -/

/-- **R59** (eight steps `ok`, admitted). The execution of witness W13 (`WitnessCapacity`): in
frame 0, `a := derive(root_X, Modify, {X})`, `store(a, p)`, `o1 := derive(root_p, Observe, {p})`,
`o2 := derive(root_p, Observe, {p})`, `spawn c1` yielding `o1`, `spawn c2` yielding `o2`; then
`c1 : read3(a, X)` and `c2 : read3(a, X)`. Expected (Spec 1 §43, O8, O9; C43, third paragraph):
every step `ok`; after the two `spawn`, the effective mode of `a` on `X` is `Modify`, `a` is
exercisable in `Observe` and not in `Modify` from the current frame of `c1` and from that of `c2`,
and `cap(c1, X) = cap(c2, X) = Observe`, not `Modify`; the execution is an `EncapsulatedTrace`.
Obtained: the same. No twin. -/
theorem R59 : EncapsulatedTrace pm kMutex mutexLayout (w13σ 0) w13L (w13σ 8) ∧
    effective (w13σ 6).1.flat 2 0 = some .modify ∧
    ((w13σ 6).1.view 1).ExercisableAt 2 .observe ∧ ¬ ((w13σ 6).1.view 1).ExercisableAt 2 .modify ∧
    ((w13σ 6).1.view 2).ExercisableAt 2 .observe ∧ ¬ ((w13σ 6).1.view 2).ExercisableAt 2 .modify ∧
    cap (w13σ 6).1 (w13σ 6).2.1 1 0 = some .observe ∧
    cap (w13σ 6).1 (w13σ 6).2.1 2 0 = some .observe :=
  ⟨w13_trace, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

end Ern.Corpus.Concurrency
