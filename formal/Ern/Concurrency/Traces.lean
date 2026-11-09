import Ern.Concurrency.SyncLib
import Ern.MemoryModel.Arena
import Ern.Concurrency.Conservativity
import Ern.Concurrency.Transfer

/-!
# Minimal traces (test module)

Concrete states and runs used by the theorems of the concurrent milestone (constructions and
counterexamples), checked by `decide`. The corpus of WC3 §V (S1a–S16) is covered only for S4, S9
(positive halves) and S16 (`Ern.Concurrency.EncapTraces`).

* a mutex value `m = {data, lock}` whose field `data` owns the protected storage `T` (WC3 C13),
  its registration by `newMutex`, `acquire`, `unlock`;
* theorem 4, counterexample without encapsulation (WC3 C22.1): `derive(guarded, Observe, footprint(T))` by the
  exclusive owner makes `acquire` not enabled while `grant = none` (`acquire_blocked_by_derive`);
  the encapsulated twin enables it (`acquire_enabled`);
* theorem 5 needs the kernel invariant: a state with `SyncInv`, `GrantDiscipline` and the library
  instantiation of `SyncAuthorized`, violating `I1`, where `deriveSync` is not enabled
  (`realizability_needs_i1`);
* frame transitions: `enterFrame`, `spawn`, `exitFrameC` with reparenting, `terminate`, `join`
  (`frames_run`); `join` on a live context has no outcome (`join_waits`), on an unknown identifier
  it is rejected (`join_unknown_rejected`);
* a second `newMutex` on a protected root owned by the same field, hence with the same controller,
  is rejected (`shared_controller_rejected`, WC3 C13.8); two mutex values with distinct
  controllers are both accepted (`distinct_controllers_ok`, WC3 S9);
* S4: a child receives a value through the by-value composite and survives the exit of the
  creating frame (`s4_detached_child`).
-/

namespace Ern.Concurrency.Traces

open Ern.MemoryModel.Access Ern.MemoryModel.Access.Examples Ern.Concurrency

/-! ## Mutex value (WC3 C12, C13) -/

/-- Statics (Spec 1 §47): `0` the mutex value `m`, `1` its field `data`, `2` its field `lock`, `3`
the protected value `T`, a root owned by `data`; every leaf `Init`. -/
def mst : Statics :=
  [((none, none, 0), true), ((some 0, none, 0), true), ((some 0, none, 0), true),
   ((none, some 1, 0), true)]

/-- The reference layout (WC3 C12): `guarded` is held by the first field, the controller is the
second. -/
def L0 : MutexLayout := ⟨0, 1⟩

/-- Initial single-context state (Spec 1 §47): root authority `0` of `m` held by frame 0, root
authority `1` of `T` held by `data` (place 1). -/
def c0 : SC := SC.ofS3 (S3.init mst)

/-- The statics are well formed (Spec 1 §47). -/
theorem mst_ok : StaticsOK mst := by decide

/-- After `newMutex(guarded = 1)` (WC3 C13). -/
def reg1 : SyncReg := [⟨1, none⟩]

/-- `newMutex(1)` executed by context 0 is enabled on `c0`; its controller is place 2. -/
theorem newMutex_ok : NewMutexOk K0 L0 [] c0 [] 0 1 (c0, reg1) ∧
    ControlOf L0 c0 ⟨1, none⟩ = some 2 :=
  ⟨⟨by decide, by decide, rfl⟩, by decide⟩

/-! ## Theorem 4: counterexample without encapsulation (WC3 C22) -/

/-- `derive(guarded = 1, footprint(T) = [3], Observe)` by context 0, the exclusive owner. -/
def c1 : SC := c0.set (deriveEff (c0.view 0) 1 [3] .observe)

/-- The derivation is an enabled kernel step (Spec 1 §60) and it is not encapsulated (WC3
C22.1). -/
theorem derive_step : opStepC K0 (.derive 1 [3] .observe) 0 c0 (.ok c1) ∧
    ¬ Encap L0 (c0, reg1) (.kernel 0 (.derive 1 [3] .observe)) :=
  ⟨⟨by decide, _, .ok (by decide), rfl⟩, fun h => h ⟨1, none⟩ (by decide) (by decide) rfl⟩

/-- Theorem 4, second half (WC3 C22): after the non-encapsulated `derive`, the entry is live with
`grant = none`, `GrantDiscipline` fails, and `acquire` is not enabled. -/
theorem acquire_blocked_by_derive : (⟨1, none⟩ : SyncEntry).Live c1 ∧ ¬ GrantDiscipline c1 reg1 ∧
    ∀ st', ¬ AcquireOk K0 L0 c1 reg1 0 0 st' := by
  refine ⟨by decide, fun h => ?_, ?_⟩
  · have := h ⟨1, none⟩ (by decide) (by decide) rfl
    exact (by decide : ¬ NoCoveringDesc c1 1) this
  · rintro st' ⟨-, e, he, -, hd, -⟩
    simp only [reg1, List.getElem?_cons_zero, Option.some.injEq] at he
    subst he
    exact (by decide : ¬ DeriveSyncPre (libKC K0 L0) reg1 c1 0 1) hd

/-- The grant created by `acquire` on `c0` (WC3 C15, C16). -/
def c2 : SC := deriveSyncEff c0 0 1

/-- Registry after `acquire` (WC3 C16): the grant is authority 2. -/
def reg2 : SyncReg := [⟨1, some 2⟩]

/-- Positive twin (WC3 C16): without the derivation, `acquire` is enabled and records the grant. -/
theorem acquire_enabled : AcquireOk K0 L0 c0 reg1 0 0 (c2, reg2) :=
  ⟨by decide, ⟨1, none⟩, rfl, by decide, by decide, rfl⟩

/-- State after `unlock` (WC3 C17). -/
def c3 : SC := c2.set (releaseEff (c2.view 0) 2)

/-- `unlock` is enabled after `acquire` (WC3 C17). -/
theorem unlock_enabled : UnlockOk L0 c2 reg2 0 0 (c3, reg1) :=
  ⟨by decide, ⟨1, some 2⟩, 2, rfl, by decide, rfl, by decide, by decide, rfl⟩

/-- An encapsulated trace `newMutex`, `acquire`, `unlock` from `c0` with an empty registry (WC3
C13, C16, C17, C22). -/
theorem mutex_trace : EncapsulatedTrace K0 L0 (c0, [])
    [.newMutex 0 1 [], .acquire 0 0, .unlock 0 0] (c3, reg1) :=
  .cons trivial (.newMutex newMutex_ok.1) <|
  .cons trivial (.acquire acquire_enabled) <|
  .cons trivial (.unlock unlock_enabled) .nil

/-! ## Theorem 5 needs the kernel invariant (WC3 C25; Spec 1 §50) -/

/-- `c0` with an extra active root `Modify` authority over `T` held by frame 0, unrelated to
`guarded` (violates I1, Spec 1 §50). -/
def bad : SC := { c0 with A := c0.A ++ [⟨.modify, none, [3], .frame 0, true⟩] }

/-- Theorem 5 is false without the kernel invariant: in `bad`, `SyncInv`, `GrantDiscipline` and
the library instantiation of `SyncAuthorized` hold for the current frame of context 0, `I1`
fails, and the preconditions of `deriveSync` fail (Spec 1 §60.3). -/
theorem realizability_needs_i1 : SyncInv L0 bad reg1 ∧ GrantDiscipline bad reg1 ∧
    LibSyncAuthorized L0 reg1 bad 1 (bad.view 0).top ∧ ¬ I1 bad.flat ∧
    ¬ DeriveSyncPre (libKC K0 L0) reg1 bad 0 1 := by
  have hl : ∀ {i : Nat} {e : SyncEntry}, reg1[i]? = some e → i = 0 ∧ e = ⟨1, none⟩ := by
    intro i e h
    cases i with
    | zero => simp [reg1] at h; exact ⟨rfl, h.symm⟩
    | succ i => simp [reg1] at h
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, by decide, fun h => ?_, by decide⟩
  · intro e he _; simp only [reg1, List.mem_singleton] at he; subst he; decide
  · intro e he _ g hg; simp only [reg1, List.mem_singleton] at he; subst he; cases hg
  · intro e he _; simp only [reg1, List.mem_singleton] at he; subst he; decide
  · intro i j e e' _ hi hj _ _ _ _; rw [(hl hi).1, (hl hj).1]
  · intro i j e e' hi hj _ _ _; rw [(hl hi).1, (hl hj).1]
  · intro e he _ g hg; simp only [reg1, List.mem_singleton] at he; subst he; cases hg
  · intro e he; simp only [reg1, List.mem_singleton] at he; subst he; decide
  · intro e he _; simp only [reg1, List.mem_singleton] at he; subst he; decide
  · intro e he _; simp only [reg1, List.mem_singleton] at he; subst he; decide
  · intro e he _ _; simp only [reg1, List.mem_singleton] at he; subst he; decide
  · have := h 1 2 ⟨.modify, none, [3], .place 1, true⟩ ⟨.modify, none, [3], .frame 0, true⟩ 3
      (by decide) (by decide) (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide)
    cases this.1

/-! ## Frame transitions (WC3 C4, C6–C8) -/

/-- Context 0 enters a call frame (frame 1) without parameter nor local (Spec 1 §72). -/
def f1 : SC := enterEffC c0 0 [] []
/-- From frame 1, context 0 spawns context 1 (frame 2, parent 1) with one local (place 4) (WC3
C4). -/
def f2 : SC := spawnEff f1 0 [] [(none, 0)]
/-- Frame 1 exits; context 1 is reparented to frame 0 (WC3 C6). -/
def f3 : SC := exitEffC f2 0
/-- Context 1 terminates (WC3 C7). -/
def f4 : SC := termEffC f3 1

/-- A run of frame transitions (WC3 C4, C6–C8): `enterFrame`, `spawn`, `exitFrameC` (reparenting
context 1 from the exiting frame 1 to its caller 0), `terminate`, `join`. -/
theorem frames_run : opStepC K0 (.enter [] []) 0 c0 (.ok f1) ∧ SpawnStep f1 0 [] [(none, 0)] (.ok f2) ∧
    f2.ctxParent 1 = some 1 ∧ opStepC K0 .exit 0 f2 (.ok f3) ∧ f3.ctxParent 1 = some 0 ∧
    TermStep K0 f3 1 (.ok f4) ∧ JoinStep f4 0 1 (.ok f4) := by
  refine ⟨⟨by decide, .ok (by decide)⟩, ⟨by decide, .ok (by decide)⟩, by decide,
    ⟨by decide, .ok (by decide)⟩, by decide, ⟨by decide, .ok (by decide)⟩, .ok (by decide) ?_⟩
  decide

/-- WC3 C8: while context 1 is live, `join` has no outcome. -/
theorem join_waits : ∀ o, ¬ JoinStep f3 0 1 o := by
  intro o h
  cases h with
  | ok _ hd => exact (by decide : ¬ OptP (f3.C[1]?) (fun x => x.life = .done) False) hd
  | reject _ hd => exact (by decide : f3.C[1]? ≠ none) hd

/-- WC3 C8: `join` on an identifier unknown to the execution (no context 2) is rejected, and has
no `ok` outcome. -/
theorem join_unknown_rejected : JoinStep f4 0 2 .reject ∧ ∀ s', ¬ JoinStep f4 0 2 (.ok s') :=
  ⟨.reject (by decide) (by decide), fun s' h => by
    cases h with
    | ok _ hd => exact (by decide : ¬ OptP (f4.C[2]?) (fun x => x.life = .done) False) hd⟩

/-- `ancestorC` across contexts after `spawn` (WC3 C3): the creating frame 1 and the base frame 0
are ancestors of the initial frame 2 of context 1; after `exitFrameC`, frame 0 still is. -/
theorem ancestry : f2.ancestorC 1 2 ∧ f2.ancestorC 0 2 ∧ ¬ f2.ancestorC 2 1 ∧
    f3.ancestorC 0 2 ∧ ¬ f3.ancestorC 1 2 := by decide

/-! ## Non-vacuity of the re-indexed kernel invariant (WC3 C20) -/

/-- `FramesC` from bounded, decidable clauses (decision procedure for WC3 C3). -/
theorem framesC_of {s : SC} (h0 : OptP (s.C[0]?) (fun x => x.life = .live ∧ x.parent = none) False)
    (hne : ∀ c ∈ List.range s.C.length, s.Live c → s.stk c ≠ []) (hnd : s.frames.Nodup)
    (hb : ∀ f ∈ s.frames, f < s.nF)
    (hr : ∀ c ∈ List.range s.C.length, c ≠ 0 → s.Live c → s.ctxParent c ≠ none)
    (hp : ∀ f ∈ s.frames, OptP (s.parC f) (fun g => g ∈ s.frames ∧ g < f) True) : FramesC s := by
  have hlt : ∀ c, s.Live c → c < s.C.length := fun c hc => by
    unfold SC.Live at hc; unfold OptP at hc; split at hc
    · exact lt_of_getElem? ‹_›
    · exact hc.elim
  refine ⟨h0, fun c hc => hne c (List.mem_range.2 (hlt c hc)) hc, hnd, hb,
    fun c h0 hc => hr c (List.mem_range.2 (hlt c hc)) h0 hc, fun f hf g hg => ?_⟩
  have := hp f hf; rw [hg] at this; exact this

/-- The initial single-context state satisfies the re-indexed kernel invariant (WC3 C20, C24). -/
theorem c0_kInvC : KInvC c0 := by
  refine (single_kInvC ⟨_, rfl⟩).2 ⟨framesC_of (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide), ?_⟩
  exact (init_kinv mst_ok).1

/-- The two-context state `f2` (after `spawn` from a call frame) satisfies the re-indexed kernel
invariant (WC3 C20): `KInvC` is not vacuous on multi-context states. -/
theorem f2_kInvC : KInvC f2 := by
  have hk := (Ern.MemoryModel.Arena.KInvB.sound (s := f2.flat) (by decide)).1
  obtain ⟨hw, ⟨⟨i1, i2, i3, -⟩, -, hnd⟩, -, hno⟩ := hk
  exact ⟨⟨framesC_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hw⟩,
    ⟨⟨i1, i2, i3, fun _ => i4_always _⟩, by decide, hnd⟩, by decide, hno⟩

/-! ## Controller uniqueness at construction (WC3 C13.8, S9) -/

/-- Statics: the mutex value `m = {data, lock}` and two protected roots `T₁`, `T₂` both owned by
`data`. -/
def mst2 : Statics :=
  [((none, none, 0), true), ((some 0, none, 0), true), ((some 0, none, 0), true),
   ((none, some 1, 0), true), ((none, some 1, 0), true)]

/-- Initial state: root authorities 1 (of `T₁`) and 2 (of `T₂`) are both held by `data`. -/
def d0 : SC := SC.ofS3 (S3.init mst2)

/-- WC3 C13.8: after `newMutex(1)`, the entry of `guarded = 2` would have the same positional
controller (place 2) as the live entry of `guarded = 1`; the second `newMutex` is rejected. -/
theorem shared_controller_rejected : NewMutexOk K0 L0 [] d0 [] 0 1 (d0, [⟨1, none⟩]) ∧
    ControlOf L0 d0 ⟨1, none⟩ = some 2 ∧ ControlOf L0 d0 ⟨2, none⟩ = some 2 ∧
    ¬ NewMutexPre K0 L0 [] d0 [⟨1, none⟩] 0 2 :=
  ⟨⟨by decide, by decide, rfl⟩, by decide, by decide, by decide⟩

/-- Statics: two mutex values `m₁ = {data₁, lock₁}` (places 0–2) and `m₂ = {data₂, lock₂}`
(places 3–5), owning the protected roots `T₁` (place 6, owned by `data₁`) and `T₂` (place 7, owned
by `data₂`). Root authorities: 0 (`m₁`), 1 (`m₂`), 2 (`T₁`, held by `data₁`), 3 (`T₂`, held by
`data₂`). -/
def mst3 : Statics :=
  [((none, none, 0), true), ((some 0, none, 0), true), ((some 0, none, 0), true),
   ((none, none, 0), true), ((some 3, none, 0), true), ((some 3, none, 0), true),
   ((none, some 1, 0), true), ((none, some 4, 0), true)]

/-- Initial state of `mst3`. -/
def d1 : SC := SC.ofS3 (S3.init mst3)

/-- Positive twin of `shared_controller_rejected` (WC3 S9, C13.8): `newMutex(2)` then
`newMutex(3)` are accepted, with the distinct controllers `lock₁` (place 2) and `lock₂` (place
5). -/
theorem distinct_controllers_ok : NewMutexOk K0 L0 [] d1 [] 0 2 (d1, [⟨2, none⟩]) ∧
    NewMutexOk K0 L0 [] d1 [⟨2, none⟩] 0 3 (d1, [⟨2, none⟩, ⟨3, none⟩]) ∧
    ControlOf L0 d1 ⟨2, none⟩ = some 2 ∧ ControlOf L0 d1 ⟨3, none⟩ = some 5 :=
  ⟨⟨by decide, by decide, rfl⟩, ⟨by decide, by decide, rfl⟩, by decide, by decide⟩

/-- The two constructions of `distinct_controllers_ok` as an `EncapsulatedTrace` from `d1` with an
empty registry (WC4 C22, C23). -/
theorem distinct_controllers_trace : EncapsulatedTrace K0 L0 (d1, [])
    [.newMutex 0 2 [], .newMutex 0 3 []] (d1, [⟨2, none⟩, ⟨3, none⟩]) :=
  .cons trivial (.newMutex distinct_controllers_ok.1) <|
  .cons trivial (.newMutex distinct_controllers_ok.2.1) .nil

/-! ## S4: a detached child survives its creator (WC3 S4, C5, C6) -/

/-- Statics: one `Init` static place (place 0), owned by frame 0. -/
def s4st : Statics := [((none, none, 0), true)]

/-- Initial single-context state of `s4st` (Spec 1 §47). -/
def q0 : SC := SC.ofS3 (S3.init s4st)
/-- Context 0 enters frame 1 with two locals, `v` (place 1) and `p` (place 2) (Spec 1 §72). -/
def q1 : SC := enterEffC q0 0 [] [(none, 0), (none, 0)]
/-- `write` of `v` through its root authority 1 (Spec 1 §67). -/
def q2 : SC := q1.set (write3Eff (q1.view 0) [1])
/-- `write` of `p` through its root authority 2 (Spec 1 §67). -/
def q3 : SC := q2.set (write3Eff (q2.view 0) [2])
/-- `alloc(provider p, owner v, one leaf)` (Spec 1 §71): the root `T` (place 3) owned by `v`, its
root authority 3 held by `v`. -/
def q4 : SC := q3.set (allocEff (q3.view 0) 1 [(none, 0)])
/-- From frame 1, the by-value composite (WC3 C5) creates context 1 (frame 2) with one local `d`
(place 4) and moves `v` into `d`. -/
def q5 : SC := spawnValEff q4 0 [] [(none, 0)] [(1, 4)]
/-- Frame 1 exits (WC3 C6); context 1 is reparented to frame 0. -/
def q6 : SC := exitEffC q5 0

/-- The steps of S4 are `ok` (Spec 1 §72, §67, §71; WC3 C5, C6). -/
theorem s4_steps : opStepC K0 (.enter [] [(none, 0), (none, 0)]) 0 q0 (.ok q1) ∧
    opStepC K0 (.write 1 [1]) 0 q1 (.ok q2) ∧ opStepC K0 (.write 2 [2]) 0 q2 (.ok q3) ∧
    opStepC K0 (.alloc 2 1 [(none, 0)]) 0 q3 (.ok q4) ∧
    SpawnValStep K0 q4 0 [] [(none, 0)] [(1, 4)] (.ok q5) ∧ opStepC K0 .exit 0 q5 (.ok q6) :=
  ⟨⟨by decide, .ok (by decide)⟩, ⟨by decide, _, .ok (by decide), rfl⟩,
    ⟨by decide, _, .ok (by decide), rfl⟩, ⟨by decide, _, .ok (by decide) trivial, rfl⟩,
    ⟨by decide, .ok (by decide)⟩, ⟨by decide, .ok (by decide)⟩⟩

/-- The steps of S4 as an `EncapsulatedTrace` from `q0` with an empty registry (WC4 C22, C23). -/
theorem s4_trace : EncapsulatedTrace K0 L0 (q0, [])
    [.kernel 0 (.enter [] [(none, 0), (none, 0)]), .kernel 0 (.write 1 [1]),
     .kernel 0 (.write 2 [2]), .kernel 0 (.alloc 2 1 [(none, 0)]),
     .spawnVal 0 [] [(none, 0)] [(1, 4)], .kernel 0 .exit] (q6, []) :=
  .cons trivial (.kernel s4_steps.1) <| .cons trivial (.kernel s4_steps.2.1) <|
  .cons trivial (.kernel s4_steps.2.2.1) <| .cons trivial (.kernel s4_steps.2.2.2.1) <|
  .cons ⟨fun _ h => (by cases h), trivial⟩ (.spawnVal s4_steps.2.2.2.2.1) <|
  .cons trivial (.kernel s4_steps.2.2.2.2.2) .nil

/-- WC3 S4, positive: after the exit of the creating frame 1, the child context 1 is live, its
initial frame is reparented to frame 0, `d` (place 4) and the storage `T` it now owns (place 3)
are usable, the root authority of `T` is held by `d`, and the re-indexed kernel invariant `KInvC`
(hence `ConcurrentWF`) holds. -/
theorem s4_detached_child : q6.Live 1 ∧ q6.ctxParent 1 = some 0 ∧ q6.flat.Usable 4 ∧
    q6.flat.Usable 3 ∧ (q6.A[3]?).map (·.holder) = some (.place 4) ∧ KInvC q6 ∧
    ConcurrentWF q6 := by
  have hk := (Ern.MemoryModel.Arena.KInvB.sound (s := q6.flat) (by decide)).1
  obtain ⟨hw, ⟨⟨i1, i2, i3, -⟩, -, hnd⟩, -, hno⟩ := hk
  have hfr : FramesC q6 :=
    framesC_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hkc : KInvC q6 :=
    ⟨⟨hfr, hw⟩, ⟨⟨i1, i2, i3, fun _ => i4_always _⟩, by decide, hnd⟩, by decide, hno⟩
  exact ⟨by decide, by decide, by decide, by decide, by decide, hkc, hkc.1⟩

end Ern.Concurrency.Traces
