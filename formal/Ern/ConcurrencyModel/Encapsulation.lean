import Ern.ConcurrencyModel.Reachable

/-!
# Safe-abstraction trace encapsulation (C22.4, C22.6, C51.1)

* Guard-free exercise (C22.6): `ExerFree`, the exercise of Spec 1 §43 by a holder chain that
  contains the `guarded` authority of no live entry, and the rights built on it
  (`HasRightFree`, `HolderRightFree`, `CtrlRightFree`, `MetaRightFree`, `ValRightsFree`); each
  implies its ordinary form.
* The controller restriction of C22.4 (`ControllerRestriction`), read on the leaves a step
  actually affects (`ActualFootprint`).
* The inventory of the rights a step reads (C22.6): `RightsRead`, implied by every `ok` step
  (`rightsRead_of_step`), and its guard-free form `RightsReadFree`, with the `resetLock`
  exception of C22.6, which implies it (`rightsRead_of_free`).
* `EncapStep` and `EncapsulatedTrace` (C51.1): C22.1–C22.3 and C22.5 (`RestrictedStep`), C22.4
  (`ControllerRestriction`) and C22.6 (`RightsReadFree`).
-/

namespace Ern.ConcurrencyModel

open Ern.MemoryModel Ern.MemoryModel.Access

/-! ## Guard-free exercise (C22.6) -/

/-- `a` is the `guarded` authority of no live entry of `reg` (C12, C22.6). -/
def NotGuarded (s : SC) (reg : SyncReg) (a : Nat) : Prop := ∀ e ∈ reg, e.Live s → a ≠ e.guarded

/-- Decidability of `NotGuarded` (C22.6). -/
instance (s : SC) (reg : SyncReg) (a : Nat) : Decidable (NotGuarded s reg a) := by
  unfold NotGuarded; infer_instance

/-- `ExercisableAt` (Spec 1 §43) from the current frame of `c`, justified by a holder chain none
of whose authorities is the `guarded` authority of a live entry of `reg` (C22.6: a valid
justification "whose entire authority-holder chain excludes the `guarded` authority of every live
synchronization entry"). The constructors are those of `S3.ExercisableAt` on the view of `c`, each
with `NotGuarded` for the authority it concludes. An acquired grant is tested as itself, not
through its origin (C22.6). -/
inductive ExerFree (s : SC) (reg : SyncReg) (c : Nat) : Nat → Mode → Prop where
  | base {a : Nat} {m : Mode} {y : Authority} : NotGuarded s reg a → s.A[a]? = some y →
      y.active = true → m.le y.mode → y.holder = .frame (s.view c).top → ExerFree s reg c a m
  | held {a p b : Nat} {m : Mode} {y : Authority} : NotGuarded s reg a → s.A[a]? = some y →
      y.active = true → m.le y.mode → y.holder = .place p → ExerFree s reg c b m →
      (∀ l ∈ footprint s.P p, Allows (effective s.flat b l) m) → ExerFree s reg c a m

/-- One step of `ExerFree · m` read on a Boolean premise (decision procedure for C22.6, on the
pattern of `exR`, Spec 1 §43). -/
def exerFreeR (s : SC) (reg : SyncReg) (c : Nat) (m : Mode) (E : Nat → Bool) (a : Nat) : Bool :=
  decide (NotGuarded s reg a) && match s.A[a]? with
  | some y => y.active && decide (m.le y.mode) && match y.holder with
    | .frame f => decide (f = (s.view c).top)
    | .place p => (List.range s.A.length).any fun b =>
        decide (∀ l ∈ footprint s.P p, Allows (effective s.flat b l) m) && E b
  | none => false

/-- `exerFreeR` is a bounded monotone rule (decision procedure for C22.6). -/
theorem exerFreeR_rule (s : SC) (reg : SyncReg) (c : Nat) (m : Mode) :
    KRule s.A.length (exerFreeR s reg c m) where
  mono p q hpq a h := by
    unfold exerFreeR at h ⊢
    simp only [Bool.and_eq_true] at h ⊢
    refine ⟨h.1, ?_⟩
    have h2 := h.2
    split at h2
    · simp only [Bool.and_eq_true] at h2 ⊢
      refine ⟨h2.1, ?_⟩; split at h2
      · simpa using h2.2
      · simp only [Bool.and_eq_true, List.any_eq_true] at h2 ⊢
        obtain ⟨b, hb, hc, he⟩ := h2.2
        exact ⟨b, hb, hc, hpq b he⟩
    · exact h2
  bound p a h := by
    unfold exerFreeR at h
    simp only [Bool.and_eq_true] at h
    have h2 := h.2
    split at h2
    · exact lt_of_getElem? ‹_›
    · cases h2
  loc p q hpq a := by
    unfold exerFreeR; congr 1; split
    · congr 1; split
      · rfl
      · exact any_congr' fun b hb => by rw [hpq b (List.mem_range.1 hb)]
    · rfl

/-- Soundness of the iteration for `ExerFree` (decision procedure for C22.6). -/
theorem exerFree_of_kiter (s : SC) (reg : SyncReg) (c : Nat) (m : Mode) :
    ∀ k a, kiter (exerFreeR s reg c m) k a = true → ExerFree s reg c a m
  | 0, _, h => by simp [kiter] at h
  | k + 1, a, h => by
    simp only [kiter, exerFreeR, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hg, h⟩ := h
    split at h
    · rename_i y hy
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨ha, hm⟩, h⟩ := h
      split at h
      · rename_i f hf; exact .base hg hy ha hm (by simp at h; rw [hf, h])
      · rename_i p hp
        simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨b, -, hc, hb⟩ := h
        exact .held hg hy ha hm hp (exerFree_of_kiter s reg c m k b hb) hc
    · cases h

/-- The frame-held case of `exerFreeR` (decision procedure for C22.6). -/
theorem exerFreeR_base {s : SC} {reg : SyncReg} {c : Nat} {m : Mode} {E : Nat → Bool} {a : Nat}
    {y : Authority} (hg : NotGuarded s reg a) (hy : s.A[a]? = some y) (ha : y.active = true)
    (hm : m.le y.mode) (hf : y.holder = .frame (s.view c).top) :
    exerFreeR s reg c m E a = true := by
  simp only [exerFreeR, hy, ha, hf, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hg, hm, trivial⟩

/-- The place-held case of `exerFreeR` (decision procedure for C22.6). -/
theorem exerFreeR_held {s : SC} {reg : SyncReg} {c : Nat} {m : Mode} {E : Nat → Bool}
    {a p b : Nat} {y : Authority} (hg : NotGuarded s reg a) (hy : s.A[a]? = some y)
    (ha : y.active = true) (hm : m.le y.mode) (hp : y.holder = .place p) (hb : b < s.A.length)
    (hc : ∀ l ∈ footprint s.P p, Allows (effective s.flat b l) m) (hE : E b = true) :
    exerFreeR s reg c m E a = true := by
  simp only [exerFreeR, hy, ha, hp, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq,
    List.any_eq_true, List.mem_range]
  exact ⟨hg, hm, b, hb, hc, hE⟩

/-- `ExerFree` is computed by `|A| + 1` steps of `exerFreeR` (decision procedure for C22.6). -/
theorem exerFree_iff {s : SC} {reg : SyncReg} {c a : Nat} {m : Mode} :
    ExerFree s reg c a m ↔ kiter (exerFreeR s reg c m) (s.A.length + 1) a = true := by
  refine ⟨fun h => ?_, exerFree_of_kiter s reg c m _ a⟩
  induction h with
  | base hg hy ha hm hf => exact exerFreeR_base hg hy ha hm hf
  | held hg hy ha hm hp _ hc ih =>
    rw [← kiter_fix (exerFreeR_rule s reg c _)]
    exact exerFreeR_held hg hy ha hm hp (kiter_bound (exerFreeR_rule s reg c _) _ _ ih) hc ih

/-- Decidability of `ExerFree` (C22.6). -/
instance (s : SC) (reg : SyncReg) (c a : Nat) (m : Mode) : Decidable (ExerFree s reg c a m) :=
  decidable_of_iff _ exerFree_iff.symm

/-- The authority of an `ExerFree` is not the `guarded` authority of a live entry (C22.6). -/
theorem ExerFree.notGuarded {s : SC} {reg : SyncReg} {c a : Nat} {m : Mode}
    (h : ExerFree s reg c a m) : NotGuarded s reg a := by
  cases h with
  | base hg => exact hg
  | held hg => exact hg

/-- A guard-free exercise is an exercise (Spec 1 §43, C22.6): the restricted holder chain is a
holder chain. -/
theorem exercisable_of_free {s : SC} {reg : SyncReg} {c a : Nat} {m : Mode}
    (h : ExerFree s reg c a m) : (s.view c).ExercisableAt a m := by
  induction h with
  | base _ hy ha hm hf => exact .base hy ha hm hf
  | held _ hy ha hm hp _ hc ih => exact .held hy ha hm hp ih hc

/-- Without a live entry in `reg`, every exercise from the current frame of `c` (Spec 1 §43) is
guard-free (C22.6). -/
theorem exerFree_of_exercisable {s : SC} {reg : SyncReg} {c a : Nat} {m : Mode}
    (hng : ∀ e ∈ reg, ¬ e.Live s) (h : (s.view c).ExercisableAt a m) : ExerFree s reg c a m := by
  have hg : ∀ x, NotGuarded s reg x := fun x e he hl => absurd hl (hng e he)
  induction h with
  | base hy ha hm hf => exact .base (hg _) hy ha hm hf
  | held hy ha hm hp _ hc ih => exact .held (hg _) hy ha hm hp ih hc

/-- `ExercisableAt` reads the stack only through the current frame (Spec 1 §43): the frame
`(s.view c).top` exercises from `s.viewAt` as from `s.view c` (C14.3, C17.4, C18.4 read
`CtrlRight` on `s.viewAt`). -/
theorem exercisable_viewAt {s : SC} {c a : Nat} {m : Mode}
    (h : (s.view c).ExercisableAt a m) : (s.viewAt (s.view c).top).ExercisableAt a m := by
  induction h with
  | base hy ha hm hf => exact .base hy ha hm hf
  | held hy ha hm hp _ hc ih => exact .held hy ha hm hp ih hc

/-! ## Guard-free rights (C22.6) -/

/-- `HasRight(s, m, q)` (Spec 1 §43) from the current frame of `c`, with `ExerFree` in place of
`ExercisableAt` (C22.6: a right over a place). -/
def HasRightFree (st : SC × SyncReg) (c : Nat) (m : Mode) (q : Nat) : Prop :=
  ∃ a ∈ List.range st.1.A.length, ExerFree st.1 st.2 c a m ∧
    ∀ l ∈ footprint st.1.P q, Allows (effective st.1.flat a l) m

/-- Decidability of `HasRightFree` (C22.6). -/
instance (st : SC × SyncReg) (c : Nat) (m : Mode) (q : Nat) :
    Decidable (HasRightFree st c m q) := by
  unfold HasRightFree; infer_instance

/-- `HasRightFree` implies `HasRight` from the current frame of `c` (Spec 1 §43, C22.6). -/
theorem hasRight_of_free {st : SC × SyncReg} {c : Nat} {m : Mode} {q : Nat}
    (h : HasRightFree st c m q) : HasRight (st.1.view c) m q := by
  obtain ⟨a, ha, hx, hall⟩ := h
  exact ⟨a, ha, exercisable_of_free hx, hall⟩

/-- `HolderRight` (Spec 1 §62.2) with `HasRightFree` in its place case (C22.6, holder rights);
the frame case is that of `HolderRight`, the current frame of `c`, which has no holder chain. -/
def HolderRightFree (st : SC × SyncReg) (c : Nat) : Holder → Prop
  | .frame f => f = (st.1.view c).top
  | .place p => HasRightFree st c .modify p

/-- Decidability of `HolderRightFree` (C22.6). -/
instance (st : SC × SyncReg) (c : Nat) (h : Holder) : Decidable (HolderRightFree st c h) := by
  cases h <;> unfold HolderRightFree <;> infer_instance

/-- `HolderRightFree` implies `HolderRight` from the current frame of `c` (Spec 1 §62.2,
C22.6). -/
theorem holderRight_of_free {st : SC × SyncReg} {c : Nat} {h : Holder}
    (hr : HolderRightFree st c h) : HolderRight (st.1.view c) h := by
  cases h with
  | frame f => exact hr
  | place p => exact hasRight_of_free hr

/-- The controller-access right of C14.3, C17.4 and C18.4 (`CtrlRight`, the access condition of
Spec 1 §68.2) of the current frame of `c`, with `ExerFree` in place of `ExercisableAt` (C22.6,
controller rights). -/
def CtrlRightFree (L : MutexLayout) (st : SC × SyncReg) (e : SyncEntry) (c : Nat) : Prop :=
  OptP (ControlOf L st.1 e) (fun ctl => ∃ a ∈ List.range st.1.A.length,
    ExerFree st.1 st.2 c a .observe ∧ effective st.1.flat a ctl ≠ none) False

/-- Decidability of `CtrlRightFree` (C22.6). -/
instance (L : MutexLayout) (st : SC × SyncReg) (e : SyncEntry) (c : Nat) :
    Decidable (CtrlRightFree L st e c) := by
  unfold CtrlRightFree; infer_instance

/-- `CtrlRightFree` implies `CtrlRight` of the current frame of `c` (C14.3, C17.4, C18.4,
C22.6). -/
theorem ctrlRight_of_free {L : MutexLayout} {st : SC × SyncReg} {e : SyncEntry} {c : Nat}
    (h : CtrlRightFree L st e c) : CtrlRight L st.1 e (st.1.view c).top := by
  unfold CtrlRightFree at h; unfold CtrlRight
  revert h
  cases ControlOf L st.1 e with
  | none => exact id
  | some ctl =>
    rintro ⟨a, ha, hx, he⟩
    exact ⟨a, ha, exercisable_viewAt (exercisable_of_free hx), he⟩

/-- A guard-free controller right of `c` makes `c` live (C2). -/
theorem ctrlRightFree_live {L : MutexLayout} {st : SC × SyncReg} {e : SyncEntry} {c : Nat}
    (h : CtrlRightFree L st e c) : st.1.Live c := by
  unfold CtrlRightFree at h
  revert h
  cases ControlOf L st.1 e with
  | none => exact False.elim
  | some ctl =>
    rintro ⟨a, -, hx, -⟩
    exact SC.live_of_exercisable (exercisable_of_free hx)

/-- `MetaRight` (Spec 1 §36, §77.1) with `HasRightFree` over the arena value (C22.6,
administration rights); `False` when the arena value does not exist, as `Arena.MetaRight`. -/
def MetaRightFree (st : SC × SyncReg) (c : Nat) (E : Arena.ArenaEntry) : Prop :=
  OptP (Arena.arenaValue st.1.flat E) (fun v => HasRightFree st c .modify v) False

/-- Decidability of `MetaRightFree` (C22.6). -/
instance (st : SC × SyncReg) (c : Nat) (E : Arena.ArenaEntry) :
    Decidable (MetaRightFree st c E) := by
  unfold MetaRightFree; infer_instance

/-- `MetaRightFree` implies `MetaRight` from the current frame of `c` (Spec 1 §36, C22.6). -/
theorem metaRight_of_free {st : SC × SyncReg} {c : Nat} {E : Arena.ArenaEntry}
    (h : MetaRightFree st c E) : Arena.MetaRight (st.1.view c) E := by
  unfold MetaRightFree at h; unfold Arena.MetaRight
  have h0 : Arena.arenaValue (st.1.view c) E = Arena.arenaValue st.1.flat E := rfl
  rw [h0]; revert h
  cases Arena.arenaValue st.1.flat E with
  | none => exact id
  | some v => exact hasRight_of_free

/-- `Grounds` (Spec 1 §43; §63.4, §69.2, §70.3: "the exercisable authority on which that right
rests") with `ExerFree` in place of `ExercisableAt`, from the current frame of `c` (C22.6). -/
def GroundsFree (st : SC × SyncReg) (c : Nat) (m : Mode) (q g : Nat) : Prop :=
  g ∈ List.range st.1.A.length ∧ ExerFree st.1 st.2 c g m ∧
    ∀ l ∈ footprint st.1.P q, Allows (effective st.1.flat g l) m

/-- Decidability of `GroundsFree` (C22.6). -/
instance (st : SC × SyncReg) (c : Nat) (m : Mode) (q g : Nat) :
    Decidable (GroundsFree st c m q g) := by
  unfold GroundsFree; infer_instance

/-- `GroundsFree` implies `Grounds` from the current frame of `c` (C22.6). -/
theorem grounds_of_free {st : SC × SyncReg} {c : Nat} {m : Mode} {q g : Nat}
    (h : GroundsFree st c m q g) : Grounds (st.1.view c) m q g :=
  ⟨h.1, exercisable_of_free h.2.1, h.2.2⟩

/-- The source-access clause of `transfer` (Spec 1 §63.4), executed by `c` in state `s`: some
authority grounding the `Modify` right over the source, and every active derived authority
covering a source leaf from outside the source is on its origin chain (`TransferPreC`,
`ValTransferPre`). -/
def Outside (s : SC) (c src : Nat) : Prop :=
  ∃ g ∈ List.range (s.view c).A.length, Grounds (s.view c) .modify src g ∧
    ∀ j ∈ List.range (s.view c).A.length, ActiveDerivedOutside (s.view c) src j →
      RightChain (s.view c) g j

/-- `Outside` with `GroundsFree` for the grounding authority (Spec 1 §63.4, C22.6: source
rights). -/
def OutsideFree (st : SC × SyncReg) (c src : Nat) : Prop :=
  ∃ g ∈ List.range st.1.A.length, GroundsFree st c .modify src g ∧
    ∀ j ∈ List.range st.1.A.length, ActiveDerivedOutside (st.1.view c) src j →
      RightChain (st.1.view c) g j

/-- Decidability of `OutsideFree` (C22.6). -/
instance (st : SC × SyncReg) (c src : Nat) : Decidable (OutsideFree st c src) := by
  unfold OutsideFree; infer_instance

/-- `OutsideFree` implies `Outside` (Spec 1 §63.4, C22.6). -/
theorem outside_of_free {s : SC} {reg : SyncReg} {c src : Nat} (h : OutsideFree (s, reg) c src) :
    Outside s c src := by
  obtain ⟨g, hg, hgr, hall⟩ := h
  exact ⟨g, hg, grounds_of_free hgr, hall⟩

/-- The right premises of the transfer phases of the by-value `spawn` executed by `c` (C5.2,
C5 items 1 and 4; Spec 1 §63.1, §63.4; `ValTransferPre.srcRight`, `.noOutsideDerived`): for each
phase, in the declared order, on the state produced by the earlier phases, the source right and
the source-access clause. -/
def ValRights (c : Nat) : SC → List (Nat × Nat) → Prop
  | _, [] => True
  | t, v :: vs => (HasRight (t.view c) .modify v.1 ∧ Outside t c v.1) ∧
      ValRights c (transferEffC t c v.1 v.2) vs

/-- `ValRights` with `HasRightFree` and `OutsideFree`, the registry being `reg` in every phase
(C5.2, C22.6: rights read in intermediate states of a composite step). -/
def ValRightsFree (reg : SyncReg) (c : Nat) : SC → List (Nat × Nat) → Prop
  | _, [] => True
  | t, v :: vs => (HasRightFree (t, reg) c .modify v.1 ∧ OutsideFree (t, reg) c v.1) ∧
      ValRightsFree reg c (transferEffC t c v.1 v.2) vs

/-- Decidability of `ValRightsFree` (C22.6). -/
instance instDecidableValRightsFree (reg : SyncReg) (c : Nat) :
    (t : SC) → (vs : List (Nat × Nat)) → Decidable (ValRightsFree reg c t vs)
  | _, [] => isTrue trivial
  | t, v :: vs =>
    haveI := instDecidableValRightsFree reg c (transferEffC t c v.1 v.2) vs
    inferInstanceAs
      (Decidable ((HasRightFree (t, reg) c .modify v.1 ∧ OutsideFree (t, reg) c v.1) ∧ _))

/-- `ValRightsFree` implies `ValRights` (C5.2, C22.6). -/
theorem valRights_of_free {reg : SyncReg} {c : Nat} :
    ∀ (t : SC) (vs : List (Nat × Nat)), ValRightsFree reg c t vs → ValRights c t vs
  | _, [], _ => trivial
  | _, _ :: vs, ⟨⟨hr, ho⟩, h⟩ =>
    ⟨⟨hasRight_of_free hr, outside_of_free ho⟩, valRights_of_free _ vs h⟩

/-- The guard-free form of the access clause of `endUse` (Spec 1 §69.2): its grounding authority
is exercised by `ExerFree` (C22.6). -/
def EndAccessFree (st : SC × SyncReg) (c p : Nat) : Prop :=
  ∃ g ∈ List.range st.1.A.length, GroundsFree st c .modify p g ∧
    ∀ j ∈ List.range st.1.A.length, RightChain (st.1.view c) g j ∨ EndUseAccessOK (st.1.view c) p j

/-- Decidability of `EndAccessFree` (C22.6). -/
instance (st : SC × SyncReg) (c p : Nat) : Decidable (EndAccessFree st c p) := by
  unfold EndAccessFree; infer_instance

/-- The guard-free form of the access clause of `free` (Spec 1 §70.3): its grounding authority is
exercised by `ExerFree` (C22.6). -/
def FreeAccessFree (st : SC × SyncReg) (c p : Nat) : Prop :=
  ∃ g ∈ List.range st.1.A.length, GroundsFree st c .modify p g ∧
    ∀ j ∈ List.range st.1.A.length, RightChain (st.1.view c) g j ∨ FreeAccessOK (st.1.view c) p j

/-- Decidability of `FreeAccessFree` (C22.6). -/
instance (st : SC × SyncReg) (c p : Nat) : Decidable (FreeAccessFree st c p) := by
  unfold FreeAccessFree; infer_instance

/-- The guard-free form of the library authorization `K_C.SyncAuthorized(state, registry, g,
current frame)` (C14.1–C14.3, C15.3; `LibSyncAuthorized`): an entry of the registry with identity
`g`, live, with `grant = none`, on whose controller `c` has `CtrlRightFree` (C22.6). -/
def AuthFree (L : MutexLayout) (st : SC × SyncReg) (c g : Nat) : Prop :=
  ∃ e ∈ st.2, e.guarded = g ∧ e.Live st.1 ∧ e.grant = none ∧ CtrlRightFree L st e c

/-- Decidability of `AuthFree` (C22.6). -/
instance (L : MutexLayout) (st : SC × SyncReg) (c g : Nat) : Decidable (AuthFree L st c g) := by
  unfold AuthFree; infer_instance

/-- `AuthFree` implies the library authorization (C14.1–C14.3, C15.3, C22.6). -/
theorem auth_of_free {L : MutexLayout} {st : SC × SyncReg} {c g : Nat} (h : AuthFree L st c g) :
    LibSyncAuthorized L st.2 st.1 g (st.1.view c).top := by
  obtain ⟨e, he, hg, hl, hn, hc⟩ := h
  exact ⟨e, he, hg, hl, hn, ctrlRight_of_free hc⟩

/-- The controller-initialization authority of C13.11 (`NewMutexPre.ctlRight`: exercisable
`Modify` with effective `Modify` on the controller leaf, and the O10.2 exclusivity of Spec 1
§67.2) with `ExerFree` in place of `ExercisableAt` (C22.6). -/
def NewMutexRightFree (L : MutexLayout) (st : SC × SyncReg) (c g : Nat) : Prop :=
  OptP (ControlOf L st.1 ⟨g, none⟩) (fun ctl => ∃ a ∈ List.range st.1.A.length,
    ExerFree st.1 st.2 c a .modify ∧ effective (st.1.view c) a ctl = some .modify ∧
    ∀ b ∈ List.range st.1.A.length, b ≠ a → effective (st.1.view c) b ctl = none) False

/-- Decidability of `NewMutexRightFree` (C22.6). -/
instance (L : MutexLayout) (st : SC × SyncReg) (c g : Nat) :
    Decidable (NewMutexRightFree L st c g) := by
  unfold NewMutexRightFree; infer_instance

/-- The check of C18.1, `ExercisableAt(entry.guarded, Modify)` for entry `i`, under the
`resetLock` exception of C22.6: "Its **subject** `entry.guarded` is exempt from the
no-live-`guarded` test for that recovery check alone. The right on the holding `slot` that
justifies this exercise must nevertheless have a valid holder chain containing **no other** live
entry's `guarded`." The subject is checked as in Spec 1 §43 (active, own mode permitting
`Modify`) with no `NotGuarded` test; when it is held by a place `slot`, the right over `slot` is
`HasRightFree` over the registry without entry `i`; when it is held by the current frame there is
no holder chain. -/
def ResetExerciseFree (st : SC × SyncReg) (c i : Nat) : Prop :=
  OptP (st.2[i]?) (fun e => OptP (st.1.A[e.guarded]?) (fun y => y.active = true ∧
    Mode.modify.le y.mode ∧ HolderRightFree (st.1, st.2.eraseIdx i) c y.holder) False) False

/-- Decidability of `ResetExerciseFree` (C22.6). -/
instance (st : SC × SyncReg) (c i : Nat) : Decidable (ResetExerciseFree st c i) := by
  unfold ResetExerciseFree; infer_instance

/-- `ResetExerciseFree` implies the check of C18.1 (Spec 1 §43, C22.6). -/
theorem resetExercise_of_free {s : SC} {reg : SyncReg} {c i : Nat} {e : SyncEntry}
    (he : reg[i]? = some e) (h : ResetExerciseFree (s, reg) c i) :
    (s.view c).ExercisableAt e.guarded .modify := by
  unfold ResetExerciseFree at h
  rw [he] at h
  change OptP (s.A[e.guarded]?) _ False at h
  cases hy : s.A[e.guarded]? with
  | none => rw [hy] at h; exact h.elim
  | some y =>
    rw [hy] at h
    change y.active = true ∧ Mode.modify.le y.mode ∧
      HolderRightFree (s, reg.eraseIdx i) c y.holder at h
    obtain ⟨ha, hm, hh⟩ := h
    cases hp : y.holder with
    | frame f =>
      rw [hp] at hh
      exact .base hy ha hm (hp.trans (congrArg Holder.frame hh))
    | place p =>
      rw [hp] at hh
      obtain ⟨b, -, hb, hall⟩ := hh
      exact .held hy ha hm hp (exercisable_of_free hb) hall

/-! ## Controller restriction (C22.4) -/

/-- The leaves usable in `s` and no longer usable in `s'`: the leaves whose storage dies with a
step from `s` to `s'` (Spec 1 §69, §70, §73 effects; C7). -/
def Dying (s s' : SC) (l : Nat) : Prop := isLeaf s.P l ∧ s.flat.Usable l ∧ ¬ s'.flat.Usable l

/-- Decidability of `Dying` (C22.4). -/
instance (s s' : SC) (l : Nat) : Decidable (Dying s s' l) := by unfold Dying; infer_instance

/-- The leaves of the places a step from `st` names as accessed or changed, each named place
counted by its leaves. C22.4 is read on `ActualFootprint`, which differs only for `alloc`: the
provider counted here by its leaves, there by the datum of the provider metadata
(`ProviderMeta`), and the owner counted here by its leaves (C22.4: "Merely naming a structural
place containing the controller does not establish that the controller leaf itself is accessed
or modified"); the other cases are described on `ActualFootprint`. -/
def StepFootprint (L : MutexLayout) (st : SC × SyncReg × ArenaReg) : Label → Nat → Prop
  | .kernel _ (.read _ ls), l | .kernel _ (.write _ ls), l | .kernel _ (.writeShared _ ls), l =>
    l ∈ ls
  | .kernel _ (.store _ p), l => l = p
  | .kernel _ (.transfer src dst), l => l ∈ footprint st.1.P src ∨ l ∈ footprint st.1.P dst
  | .kernel c (.endUse p), l =>
    l ∈ footprint st.1.P p ∨ Dying st.1 (st.1.set (endUseEff (st.1.view c) p)) l
  | .kernel c (.free p _), l => Dying st.1 (st.1.set (freeEff (st.1.view c) p)) l
  | .kernel c .exit, l => Dying st.1 (exitEffC st.1 c) l
  | .terminate c, l => Dying st.1 (termEffC st.1 c) l
  | .kernel _ (.alloc pr ow _), l =>
    l ∈ footprint st.1.P pr ∨ l ∈ footprint st.1.P ow ∨ st.1.P.length ≤ l
  | .kernel _ (.enter _ _), l | .spawn _ _ _, l => st.1.P.length ≤ l
  | .spawnVal _ _ _ vs, l => st.1.P.length ≤ l ∨ ∃ v ∈ vs, l ∈ footprint st.1.P v.1
  | .issue _ _ _ dst, l => l = dst
  | .newMutex _ g, l => ControlOf L st.1 ⟨g, none⟩ = some l
  | .acquire _ i, l | .unlock _ i, l | .resetLock _ i, l =>
    (st.2.1[i]?).bind (ControlOf L st.1) = some l
  | .readShared _ _ leaf _ _, l => l = leaf
  | .writeShared _ _ region _ _, l => l ∈ region
  | .cas _ _ leaf _ _ _, l => l = leaf
  | .kernel _ (.derive _ _ _), _ | .kernel _ (.split _ _), _ | .kernel _ (.release _), _
  | .kernel _ (.depend _ _), _ | .kernel _ (.pin _), _ | .kernel _ (.unpin _), _
  | .join _ _, _ | .deriveSync _ _, _ | .newArena _ _ _, _ | .reset _ _, _ => False

/-- Decidability of `StepFootprint` (C22.4). -/
instance (L : MutexLayout) (st : SC × SyncReg × ArenaReg) (lbl : Label) (l : Nat) :
    Decidable (StepFootprint L st lbl l) := by
  unfold StepFootprint; split <;> infer_instance

/-- The datum of the provider metadata of `alloc` (C22.4: "`alloc` whose provider-metadata accesses
may write the controller leaf"; Spec 1 §71): for a step `alloc(pr, ow, ls)` executed by context
`c` from the state `st`, the leaves `l` with `pm st c pr ow ls l = true` are the leaves that the
accesses of that step to the metadata of the provider may write. It is a parameter of
`ActualFootprint` and of every definition and statement built on it, quantified over; no instance
is fixed. See `ActualFootprint` for what the specification leaves open about it. -/
abbrev ProviderMeta : Type :=
  SC × SyncReg × ArenaReg → (c pr ow : Nat) → LocalShape → Nat → Bool

/-- The leaves a step from `st` actually affects (C22.4: "evaluated against the leaves actually
affected by an operation, including relevant physical metadata accesses"), counting the three
kinds of effect C22.4 names: physical reads and writes, changes to the initialization state, and
changes that make a leaf itself the holder or owner of an authority or allocated resource.

* `read3`, `write3`, kernel `writeShared` (Spec 1 §66–§68): the leaves read or written; the
  ordinary `read3` and `write3` and the out-of-protocol `writeShared` of C22.4.
* `readShared` (C37), concurrent `writeShared` (C39), compare-and-exchange (C39, both branches):
  the atomic leaf read, the leaves of the region written, the leaf read or read and modified.
* `store` (Spec 1 §65): its target leaf, which becomes the holder (C22.4: "`store` targeting the
  controller leaf").
* `issue` (Spec 1 §77): its destination, written and made the holder of the block (C22.4:
  "`issue` using the controller leaf as its destination").
* `alloc` (Spec 1 §71): the leaves that the datum `pm` designates for the step, those its
  accesses to the metadata of the provider may write (C22.4: "`alloc` whose provider-metadata
  accesses may write the controller leaf"; "Merely naming a structural place containing the
  controller does not establish that the controller leaf itself is accessed or modified"); the
  owner as the place itself, the owner of the new root (C22.4: "`alloc` using the controller leaf
  itself as the owner"; "`alloc(owner = M)` is not excluded solely because `ControlOf(entry)` is a
  structural leaf of `M`"); the fresh leaves.
* `transfer` (Spec 1 §63): the leaves of the source (moved) and of the destination (written).
* by-value `spawn` (C5): the fresh locals and the leaves of each transfer source.
* `endUse` (Spec 1 §69): the leaves of the place (made `Uninit`) and the leaves that die with it;
  `free`, `exitFrame`, `terminate` (Spec 1 §70, §73; C6, C7): the leaves that die.
* `enterFrame`, `spawn` (Spec 1 §72; C4): the fresh locals.
* `newMutex`, `acquire`, `unlock`, `resetLock`: the controller of their entry, the access of the
  controller protocol (C13, C16–C18).
* `derive`, `split`, `release`, `pin`, `unpin`: no leaf; they change authorities or pinning
  obligations only (C22.4: "An authority whose footprint includes the controller does not, by
  that fact alone, constitute an access or effect on the controller"). `depend`: no leaf (C22.4:
  "A change solely to a dependency relation ... is not excluded by this item"). `join`,
  `deriveSync`, `newArena`, `reset` (Spec 1 §78: "No leaf is made `Init` by `reset`"): no
  leaf.

The datum `pm` (`ProviderMeta`) represents, for each `alloc` step, the leaves that its accesses to
the metadata of the provider may write. The specification does not fix it: C22.4 evaluates the
restriction against the leaves actually affected, "including relevant physical metadata
accesses", without saying which leaves those accesses write, and Spec 1 §81 leaves the
representation of library metadata open. It may depend on the state before the step, on the
context that executes it and on its arguments, and it is not bounded by the leaves of the
provider (Spec 1 §71.2 requires rights over the provider, not that its metadata lie in its
leaves). That the datum covers the actual physical accesses of the provider is an open part of
`OB-C20` (C27–C29, C50): no write of provider metadata is represented by the concrete machine. -/
def ActualFootprint (pm : ProviderMeta) (L : MutexLayout) (st : SC × SyncReg × ArenaReg) :
    Label → Nat → Prop
  | .kernel c (.alloc pr ow ls), l => pm st c pr ow ls l = true ∨ l = ow ∨ st.1.P.length ≤ l
  | lbl, l => StepFootprint L st lbl l

/-- Decidability of `ActualFootprint` (C22.4). -/
instance (pm : ProviderMeta) (L : MutexLayout) (st : SC × SyncReg × ArenaReg) (lbl : Label)
    (l : Nat) : Decidable (ActualFootprint pm L st lbl l) := by
  unfold ActualFootprint; split <;> infer_instance

/-- Off `alloc`, the leaves a step actually affects do not depend on the datum of the provider
metadata: they are those of `StepFootprint` (C22.4). -/
theorem actualFootprint_of_not_alloc {pm : ProviderMeta} {L : MutexLayout}
    {st : SC × SyncReg × ArenaReg} {lbl : Label}
    (h : ∀ c pr ow ls, lbl ≠ .kernel c (.alloc pr ow ls)) :
    ActualFootprint pm L st lbl = StepFootprint L st lbl := by
  funext l
  cases lbl with
  | kernel c op =>
    cases op with
    | alloc pr ow ls => exact absurd rfl (h c pr ow ls)
    | _ => rfl
  | _ => rfl

/-- The steps of the validated controller protocol of entry `i` (C22.4: "Valid internal controller
operations performed by `acquire`, `unlock`, or authorized `resetLock` remain within their
respective validated protocols"). -/
def ProtocolStepOf (i : Nat) : Label → Prop
  | .acquire _ j | .unlock _ j | .resetLock _ j => j = i
  | _ => False

/-- Decidability of `ProtocolStepOf` (C22.4). -/
instance (i : Nat) (lbl : Label) : Decidable (ProtocolStepOf i lbl) := by
  unfold ProtocolStepOf; split <;> infer_instance

/-- Decidability of `EncapVals` (C22.3 for the by-value composite). -/
instance instDecidableEncapVals (L : MutexLayout) (reg : SyncReg) (c : Nat) :
    (t : SC) → (vs : List (Nat × Nat)) → Decidable (EncapVals L reg c t vs)
  | _, [] => isTrue trivial
  | t, v :: vs =>
    haveI := instDecidableEncapVals L reg c (transferEffC t c v.1 v.2) vs
    inferInstanceAs (Decidable (TransferExcl L (t, reg) v.1 ∧ _))

/-- The move exception of C22.4 for entry `x`: "A legal transfer of the whole mutex value `M`,
including by-value `spawn`, or of a structurally enclosing value remains eligible under C22.3 and
the unchanged O4 preconditions". A `transfer` whose source is `M` (`mutexOf`, C12) or encloses it,
or a by-value `spawn` one of whose sources is `M` or encloses it, in each case satisfying C22.3
(`TransferExcl`, `EncapVals`). Legality (O4, C5) is the step relation's. -/
def WholeValueMove (L : MutexLayout) (st : SC × SyncReg) (x : SyncEntry) : Label → Prop
  | .kernel _ (.transfer src _) => TransferExcl L st src ∧
      OptP (mutexOf st.1 x.guarded) (fun m => partOf st.1.P m src) False
  | .spawnVal c _ ls vs => EncapVals L st.2 c (spawnCreate st.1 c ls) vs ∧
      OptP (mutexOf st.1 x.guarded) (fun m => ∃ v ∈ vs, partOf st.1.P m v.1) False
  | _ => False

/-- Decidability of `WholeValueMove` (C22.4). -/
instance (L : MutexLayout) (st : SC × SyncReg) (x : SyncEntry) (lbl : Label) :
    Decidable (WholeValueMove L st x lbl) := by
  unfold WholeValueMove; split <;> infer_instance

/-- C22.4 for a step from `st` to `st'`: for every entry `i` live before the step, if the leaves
the step actually affects contain `ControlOf(i)`, the step is a step of the controller protocol
of entry `i`, a move of the whole mutex value admissible under C22.3 (`WholeValueMove`), or entry
`i` is dead after it (C22.4: "Operations that make the entry dead remain eligible"). A predicate on
steps of the safe abstraction, not a precondition of a kernel transition (C22.4). -/
def ControllerRestriction (pm : ProviderMeta) (L : MutexLayout) (st : SC × SyncReg × ArenaReg)
    (lbl : Label) (st' : SC × SyncReg × ArenaReg) : Prop :=
  ∀ i ∈ List.range st.2.1.length, OptP (st.2.1[i]?) (fun x => x.Live st.1 →
    OptP (ControlOf L st.1 x) (fun ctl => ActualFootprint pm L st lbl ctl →
      ProtocolStepOf i lbl ∨ WholeValueMove L (st.1, st.2.1) x lbl ∨ ¬ x.Live st'.1) True) True

/-- Decidability of `ControllerRestriction` (C22.4). -/
instance (pm : ProviderMeta) (L : MutexLayout) (st : SC × SyncReg × ArenaReg) (lbl : Label)
    (st' : SC × SyncReg × ArenaReg) : Decidable (ControllerRestriction pm L st lbl st') := by
  unfold ControllerRestriction; infer_instance

/-- Decides `ControllerRestriction` or its negation for a step that is not an `alloc`, once the
datum of the provider metadata is removed by `actualFootprint_of_not_alloc` (C22.4). -/
macro "decide_ctl" : tactic => `(tactic| (
  unfold ControllerRestriction
  rw [actualFootprint_of_not_alloc]
  · decide
  · intro _ _ _ _ h; cases h))

/-! ## The rights a step reads (C22.6) -/

/-- The state after the internal `split` of `issue(arena, region, dst)` executed by `c` (Spec 1
§77, Part XIV; `IssueStepC`), where the internal `store` reads its rights. -/
def issueMid (s : SC) (c : Nat) (E : Arena.ArenaEntry) (region : List Nat) : SC :=
  s.set (splitEff (s.view c) E.internal [region])

/-- The state after the internal `derive` of `reset(arena)` executed by `c` (Spec 1 §78,
Part XIV; `ResetStepC`), where the internal `release` reads its right. -/
def resetMid (s : SC) (c : Nat) (E : Arena.ArenaEntry) : SC :=
  s.set (deriveEff (s.view c) E.internal (footprint s.P E.storage) .modify)

/-- The view of `c` after a `store` executed by `c` is the `store` on the view (C2). -/
theorem view_storeEffC {s : SC} {c : Nat} (a p : Nat) (hc : s.Live c) :
    (storeEffC s c a p).view c = storeEff (s.view c) a p :=
  SC.view_set hc (by unfold storeEff; split <;> rfl)

/-- The inventory of the rights a step from `st` reads (C22.6: "every ordinary exercisability
judgment under Spec 1 §43 (`ExercisableAt`) or right over a place (`HasRight`)" the step depends
on, "including the source, target, owner, holder, controller and administration rights where
relevant", and the rights "checked in intermediate or resulting states of a composite step"),
each in the state where the step relation reads it:

* `derive`, `split`, `read3`, `write3`, kernel `writeShared`: the exercise of the authority
  argument (Spec 1 §60.1, §61.1, §66.2, §67.1, §68.2);
* `release`: `HolderRight` of the holder (§62.2);
* `transfer`: the source and destination rights (§63.1) and the source-access clause (§63.4);
* `depend` (§64.1), `pin` (§74), `unpin` (§75): the place right;
* `endUse` (§69.1, §69.2), `free` (§70.3): the place right and the access clause;
* `alloc`: the provider right or its `writeShared` branch (§71.2), the owner right (§71.3);
* `store`: the target right before (§65.2) and in the resulting state (§65.5);
* raw `deriveSync`: `SyncAuthorized` (C15.3, C14.1–C14.3);
* `newMutex`: C13.2, and C13.11 with its O10.2 exclusivity;
* `acquire`: C14.3 for the entry and `SyncAuthorized` within `deriveSync` (C15.3);
* `unlock`: O3 for the grant (C17.2, Spec 1 §62.2), C17.4 in the state before the step and in
  the prospective state `prospectiveUnlock` (C22.6, "For `unlock` specifically");
* `resetLock`: C18.1 and C18.4;
* by-value `spawn`: the source right and source-access clause of each transfer phase (C5.2);
* `newArena`: §76.1 and §76.2;
* `issue`: `MetaRight` (§77.1), the destination right (§77.2), the exercise of the internal
  `split` (§61.1), the target rights of the internal `store` in its state and resulting state
  (§65.2, §65.5; §77.6);
* `reset`: the exercise of the internal `derive` (§60.1) and `HolderRight` of the internal
  `release` in the intermediate state (§62.2);
* `readShared`: the exercise of `access` in `Observe` (C37.2); concurrent `writeShared`: the
  exercise of `access` in `Observe` (§68.2, C39); compare-and-exchange: success is a
  `writeShared` (§68.2), failure a `readShared` (C37.2), both reading the exercise of `access` in
  `Observe` (C39);
* `enterFrame`, `exitFrame`, `spawn`, `terminate`, `join`: no right. The origin protection of
  Spec 1 §72.3 (`ParamOriginHidden`) is an exercise that must fail, not a right relied on. -/
def RightsRead (ks : KShared) (L : MutexLayout) (st : SC × SyncReg × ArenaReg) : Label → Prop
  | .kernel c (.derive a _ m) => (st.1.view c).ExercisableAt a m
  | .kernel c (.split a _) => (st.1.view c).ExercisableAt a .modify
  | .kernel c (.release a) => OptP (st.1.A[a]?) (fun y => HolderRight (st.1.view c) y.holder) False
  | .kernel c (.transfer src dst) => HasRight (st.1.view c) .modify src ∧
      HasRight (st.1.view c) .modify dst ∧ Outside st.1 c src
  | .kernel c (.depend q _) => HasRight (st.1.view c) .modify q
  | .kernel _ (.enter _ _) => True
  | .kernel _ .exit => True
  | .kernel c (.read a _) => (st.1.view c).ExercisableAt a .observe
  | .kernel c (.write a _) => (st.1.view c).ExercisableAt a .modify
  | .kernel c (.writeShared a _) => (st.1.view c).ExercisableAt a .observe
  | .kernel c (.pin p) => HasRight (st.1.view c) .modify p
  | .kernel c (.unpin o) =>
      OptP (st.1.pins[o]?) (fun ob => HasRight (st.1.view c) .modify ob.place) False
  | .kernel c (.endUse p) => HasRight (st.1.view c) .modify p ∧
      ∃ g ∈ List.range (st.1.view c).A.length, Grounds (st.1.view c) .modify p g ∧
        ∀ j ∈ List.range (st.1.view c).A.length,
          RightChain (st.1.view c) g j ∨ EndUseAccessOK (st.1.view c) p j
  | .kernel c (.free p _) => HasRight (st.1.view c) .modify p ∧
      ∃ g ∈ List.range (st.1.view c).A.length, Grounds (st.1.view c) .modify p g ∧
        ∀ j ∈ List.range (st.1.view c).A.length,
          RightChain (st.1.view c) g j ∨ FreeAccessOK (st.1.view c) p j
  | .kernel c (.alloc pr ow _) => (HasRight (st.1.view c) .modify pr ∨
      ∃ via ∈ List.range (st.1.view c).A.length,
        WriteSharedPre ks.toK (st.1.view c) via (footprint (st.1.view c).P pr)) ∧
      HasRight (st.1.view c) .modify ow
  | .kernel c (.store a p) => HasRight (st.1.view c) .modify p ∧
      HasRight (storeEff (st.1.view c) a p) .modify p
  | .spawn _ _ _ => True
  | .terminate _ => True
  | .join _ _ => True
  | .deriveSync c g => LibSyncAuthorized L st.2.1 st.1 g (st.1.view c).top
  | .newMutex c g => (st.1.view c).ExercisableAt g .modify ∧
      OptP (ControlOf L st.1 ⟨g, none⟩) (fun ctl => ∃ a ∈ List.range st.1.A.length,
        (st.1.view c).ExercisableAt a .modify ∧ effective (st.1.view c) a ctl = some .modify ∧
        ∀ b ∈ List.range st.1.A.length, b ≠ a → effective (st.1.view c) b ctl = none) False
  | .acquire c i => OptP (st.2.1[i]?) (fun e => CtrlRight L st.1 e (st.1.view c).top ∧
      LibSyncAuthorized L st.2.1 st.1 e.guarded (st.1.view c).top) False
  | .unlock c i => OptP (st.2.1[i]?) (fun e => OptP e.grant (fun g =>
      OptP (st.1.A[g]?) (fun y => HolderRight (st.1.view c) y.holder) False ∧
      CtrlRight L st.1 e (st.1.view c).top ∧
      CtrlRight L (prospectiveUnlock st.1 c g) e (st.1.view c).top) False) False
  | .resetLock c i => OptP (st.2.1[i]?) (fun e =>
      (st.1.view c).ExercisableAt e.guarded .modify ∧ CtrlRight L st.1 e (st.1.view c).top) False
  | .spawnVal c _ ls vs => ValRights c (spawnCreate st.1 c ls) vs
  | .newArena c storage internal => HasRight (st.1.view c) .modify storage ∧
      (st.1.view c).ExercisableAt internal .modify
  | .issue c i region dst => OptP (st.2.2[i]?) (fun E => Arena.MetaRight (st.1.view c) E ∧
      HasRight (st.1.view c) .modify dst ∧ (st.1.view c).ExercisableAt E.internal .modify ∧
      HasRight ((issueMid st.1 c E region).view c) .modify dst ∧
      HasRight (storeEff ((issueMid st.1 c E region).view c) st.1.A.length dst) .modify dst) False
  | .reset c i => OptP (st.2.2[i]?) (fun E => (st.1.view c).ExercisableAt E.internal .modify ∧
      OptP ((resetMid st.1 c E).A[st.1.A.length]?)
        (fun y => HolderRight ((resetMid st.1 c E).view c) y.holder) False) False
  | .readShared c a _ _ _ => (st.1.view c).ExercisableAt a .observe
  | .writeShared c a _ _ _ => (st.1.view c).ExercisableAt a .observe
  | .cas c a _ _ _ _ => (st.1.view c).ExercisableAt a .observe

/-- The guard-free form of the inventory (C22.6): each right of `RightsRead` with `ExerFree` in
place of `ExercisableAt`, in the state where the step relation reads it, the registry being that
of the step (for `unlock`, C17.4 in the state before the step and in `prospectiveUnlock`, both
guard-free, C22.6). For `resetLock`, the check of C18.1 is `ResetExerciseFree` (the exception of
C22.6); the controller right of C18.4 is not exempt (C22.6: the exception concerns "that recovery
check alone"). -/
def RightsReadFree (ks : KShared) (L : MutexLayout) (st : SC × SyncReg × ArenaReg) :
    Label → Prop
  | .kernel c (.derive a _ m) => ExerFree st.1 st.2.1 c a m
  | .kernel c (.split a _) => ExerFree st.1 st.2.1 c a .modify
  | .kernel c (.release a) =>
      OptP (st.1.A[a]?) (fun y => HolderRightFree (st.1, st.2.1) c y.holder) False
  | .kernel c (.transfer src dst) => HasRightFree (st.1, st.2.1) c .modify src ∧
      HasRightFree (st.1, st.2.1) c .modify dst ∧ OutsideFree (st.1, st.2.1) c src
  | .kernel c (.depend q _) => HasRightFree (st.1, st.2.1) c .modify q
  | .kernel _ (.enter _ _) => True
  | .kernel _ .exit => True
  | .kernel c (.read a _) => ExerFree st.1 st.2.1 c a .observe
  | .kernel c (.write a _) => ExerFree st.1 st.2.1 c a .modify
  | .kernel c (.writeShared a _) => ExerFree st.1 st.2.1 c a .observe
  | .kernel c (.pin p) => HasRightFree (st.1, st.2.1) c .modify p
  | .kernel c (.unpin o) =>
      OptP (st.1.pins[o]?) (fun ob => HasRightFree (st.1, st.2.1) c .modify ob.place) False
  | .kernel c (.endUse p) =>
      HasRightFree (st.1, st.2.1) c .modify p ∧ EndAccessFree (st.1, st.2.1) c p
  | .kernel c (.free p _) =>
      HasRightFree (st.1, st.2.1) c .modify p ∧ FreeAccessFree (st.1, st.2.1) c p
  | .kernel c (.alloc pr ow _) => (HasRightFree (st.1, st.2.1) c .modify pr ∨
      ∃ via ∈ List.range st.1.A.length,
        WriteSharedPre ks.toK (st.1.view c) via (footprint st.1.P pr) ∧
          ExerFree st.1 st.2.1 c via .observe) ∧ HasRightFree (st.1, st.2.1) c .modify ow
  | .kernel c (.store a p) => HasRightFree (st.1, st.2.1) c .modify p ∧
      HasRightFree (storeEffC st.1 c a p, st.2.1) c .modify p
  | .spawn _ _ _ => True
  | .terminate _ => True
  | .join _ _ => True
  | .deriveSync c g => AuthFree L (st.1, st.2.1) c g
  | .newMutex c g => ExerFree st.1 st.2.1 c g .modify ∧ NewMutexRightFree L (st.1, st.2.1) c g
  | .acquire c i => OptP (st.2.1[i]?) (fun e => CtrlRightFree L (st.1, st.2.1) e c ∧
      AuthFree L (st.1, st.2.1) c e.guarded) False
  | .unlock c i => OptP (st.2.1[i]?) (fun e => OptP e.grant (fun g =>
      OptP (st.1.A[g]?) (fun y => HolderRightFree (st.1, st.2.1) c y.holder) False ∧
      CtrlRightFree L (st.1, st.2.1) e c ∧
      CtrlRightFree L (prospectiveUnlock st.1 c g, st.2.1) e c) False) False
  | .resetLock c i => ResetExerciseFree (st.1, st.2.1) c i ∧
      OptP (st.2.1[i]?) (fun e => CtrlRightFree L (st.1, st.2.1) e c) False
  | .spawnVal c _ ls vs => ValRightsFree st.2.1 c (spawnCreate st.1 c ls) vs
  | .newArena c storage internal => HasRightFree (st.1, st.2.1) c .modify storage ∧
      ExerFree st.1 st.2.1 c internal .modify
  | .issue c i region dst => OptP (st.2.2[i]?) (fun E => MetaRightFree (st.1, st.2.1) c E ∧
      HasRightFree (st.1, st.2.1) c .modify dst ∧ ExerFree st.1 st.2.1 c E.internal .modify ∧
      HasRightFree (issueMid st.1 c E region, st.2.1) c .modify dst ∧
      HasRightFree (storeEffC (issueMid st.1 c E region) c st.1.A.length dst, st.2.1) c .modify
        dst) False
  | .reset c i => OptP (st.2.2[i]?) (fun E => ExerFree st.1 st.2.1 c E.internal .modify ∧
      OptP ((resetMid st.1 c E).A[st.1.A.length]?)
        (fun y => HolderRightFree (resetMid st.1 c E, st.2.1) c y.holder) False) False
  | .readShared c a _ _ _ => ExerFree st.1 st.2.1 c a .observe
  | .writeShared c a _ _ _ => ExerFree st.1 st.2.1 c a .observe
  | .cas c a _ _ _ _ => ExerFree st.1 st.2.1 c a .observe

/-- Decidability of `RightsReadFree` (C22.6). -/
instance (ks : KShared) [DecidablePred ks.SharedMutable] (L : MutexLayout)
    (st : SC × SyncReg × ArenaReg) (lbl : Label) : Decidable (RightsReadFree ks L st lbl) := by
  unfold RightsReadFree; split <;> infer_instance

/-- Every guard-free form implies the right it replaces (Spec 1
§43, C22.6); for `resetLock`, the exception of C22.6 still implies C18.1. -/
theorem rightsRead_of_free {ks : KShared} {L : MutexLayout} {st : SC × SyncReg × ArenaReg}
    {lbl : Label} (h : RightsReadFree ks L st lbl) : RightsRead ks L st lbl := by
  obtain ⟨s, reg, ar⟩ := st
  cases lbl with
  | kernel c op =>
    cases op with
    | derive => exact exercisable_of_free h
    | split => exact exercisable_of_free h
    | release a =>
      simp only [RightsReadFree, RightsRead] at h ⊢
      revert h
      cases s.A[a]? with
      | none => exact id
      | some y => exact holderRight_of_free
    | transfer =>
      exact ⟨hasRight_of_free h.1, hasRight_of_free h.2.1, outside_of_free h.2.2⟩
    | depend => exact hasRight_of_free h
    | enter => trivial
    | exit => trivial
    | read => exact exercisable_of_free h
    | write => exact exercisable_of_free h
    | writeShared => exact exercisable_of_free h
    | pin => exact hasRight_of_free h
    | unpin o =>
      simp only [RightsReadFree, RightsRead] at h ⊢
      revert h
      cases s.pins[o]? with
      | none => exact id
      | some ob => exact hasRight_of_free
    | endUse =>
      obtain ⟨hr, g, hg, hgr, hall⟩ := h
      exact ⟨hasRight_of_free hr, g, hg, grounds_of_free hgr, hall⟩
    | free =>
      obtain ⟨hr, g, hg, hgr, hall⟩ := h
      exact ⟨hasRight_of_free hr, g, hg, grounds_of_free hgr, hall⟩
    | alloc =>
      obtain ⟨hp, ho⟩ := h
      refine ⟨?_, hasRight_of_free ho⟩
      rcases hp with hp | ⟨via, hv, hws, -⟩
      · exact .inl (hasRight_of_free hp)
      · exact .inr ⟨via, hv, hws⟩
    | store a p =>
      refine ⟨hasRight_of_free h.1, ?_⟩
      have h2 := hasRight_of_free h.2
      rw [view_storeEffC a p (SC.live_of_hasRight (hasRight_of_free h.1))] at h2
      exact h2
  | spawn => trivial
  | terminate => trivial
  | join => trivial
  | deriveSync => exact auth_of_free h
  | newMutex c g =>
    refine ⟨exercisable_of_free h.1, ?_⟩
    have h2 := h.2
    unfold NewMutexRightFree at h2
    revert h2
    cases ControlOf L s ⟨g, none⟩ with
    | none => exact id
    | some ctl =>
      rintro ⟨a, ha, hx, he, hb⟩
      exact ⟨a, ha, exercisable_of_free hx, he, hb⟩
  | acquire c i =>
    simp only [RightsReadFree, RightsRead] at h ⊢
    revert h
    cases reg[i]? with
    | none => exact id
    | some e => exact fun ⟨hc, ha⟩ => ⟨ctrlRight_of_free hc, auth_of_free ha⟩
  | unlock c i =>
    simp only [RightsReadFree, RightsRead] at h ⊢
    revert h
    cases reg[i]? with
    | none => exact id
    | some e =>
      show OptP e.grant _ False → OptP e.grant _ False
      cases e.grant with
      | none => exact id
      | some g =>
        rintro ⟨hg, hc, hp⟩
        have ht : ((prospectiveUnlock s c g).view c).top = (s.view c).top := by
          unfold S3.top; rw [SC.view_F_set (ctrlRightFree_live hc)]
        refine ⟨?_, ctrlRight_of_free hc, ht ▸ ctrlRight_of_free hp⟩
        revert hg
        show OptP (s.A[g]?) _ False → OptP (s.A[g]?) _ False
        cases s.A[g]? with
        | none => exact id
        | some y => exact holderRight_of_free
  | resetLock c i =>
    obtain ⟨hx, hc⟩ := h
    show OptP (reg[i]?) _ False
    cases he : reg[i]? with
    | none => rw [ResetExerciseFree, he] at hx; exact hx
    | some e =>
      rw [he] at hc
      exact ⟨resetExercise_of_free he hx, ctrlRight_of_free hc⟩
  | spawnVal c _ ls vs => exact valRights_of_free _ _ h
  | newArena => exact ⟨hasRight_of_free h.1, exercisable_of_free h.2⟩
  | issue c i region dst =>
    simp only [RightsReadFree, RightsRead] at h ⊢
    revert h
    cases ar[i]? with
    | none => exact id
    | some E =>
      rintro ⟨hm, hd, hx, h1, h2⟩
      refine ⟨metaRight_of_free hm, hasRight_of_free hd, exercisable_of_free hx,
        hasRight_of_free h1, ?_⟩
      have h2' := hasRight_of_free h2
      rw [view_storeEffC (s := issueMid s c E region) _ _
        (show (issueMid s c E region).Live c from SC.live_of_hasRight (s := s) (hasRight_of_free hd))] at h2'
      exact h2'
  | reset c i =>
    simp only [RightsReadFree, RightsRead] at h ⊢
    revert h
    cases ar[i]? with
    | none => exact id
    | some E =>
      rintro ⟨hx, hr⟩
      refine ⟨exercisable_of_free hx, ?_⟩
      revert hr
      cases (resetMid s c E).A[s.A.length]? with
      | none => exact id
      | some y => exact holderRight_of_free
  | readShared => exact exercisable_of_free h
  | writeShared => exact exercisable_of_free h
  | cas => exact exercisable_of_free h

/-- The rights of the transfer phases are read by `ValTransfersPre` (C5.2). -/
theorem valRights_of_pre {k : K} {fin : S3} {c : Nat} :
    ∀ (t : SC) (vs : List (Nat × Nat)), ValTransfersPre k fin c t vs → ValRights c t vs
  | _, [], _ => trivial
  | _, _ :: vs, ⟨hp, h⟩ => ⟨⟨hp.srcRight, hp.noOutsideDerived⟩, valRights_of_pre _ vs h⟩

/-- Every right of the inventory is read by the step relation; each listed right holds
for an `ok` step, so no listed right is fictitious (C22.6). -/
theorem rightsRead_of_step {ks : KShared} {L : MutexLayout} {lbl : Label}
    {st st' : SC × SyncReg × ArenaReg} (h : LStep ks L lbl st st') : RightsRead ks L st lbl := by
  cases h with
  | @kernel s s' reg ar c op hk =>
    cases op with
    | derive a region m =>
      obtain ⟨o, hR, ho⟩ := hk
      cases hR with
      | ok hp => exact hp.exercisable
      | reject => cases ho
    | split a rs =>
      obtain ⟨o, hR, ho⟩ := hk
      cases hR with
      | ok hp => exact hp.exercisable
      | reject => cases ho
    | release a =>
      obtain ⟨o, hR, ho⟩ := hk
      cases hR with
      | ok hp => exact hp.holderRight
      | reject => cases ho
    | transfer src dst =>
      have hp := (Guarded.ok_iff.1 hk).1
      exact ⟨hp.srcRight, hp.dstRight, hp.noOutsideDerived⟩
    | depend q x => exact (Guarded.ok_iff.1 hk).1.right
    | enter => trivial
    | exit => trivial
    | read a ls =>
      obtain ⟨o, hR, ho⟩ := hk
      cases hR with
      | ok hp => exact hp.exercisable
      | reject => cases ho
    | write a ls =>
      obtain ⟨o, hR, ho⟩ := hk
      cases hR with
      | ok hp => exact hp.exercisable
      | reject => cases ho
    | writeShared a ls =>
      obtain ⟨o, hR, ho⟩ := hk
      cases hR with
      | ok hp => exact hp.exercisable
      | reject => cases ho
    | pin p =>
      obtain ⟨o, hR, ho⟩ := hk
      cases hR with
      | ok hp => exact hp.right
      | reject => cases ho
    | unpin o =>
      obtain ⟨o₃, hR, ho⟩ := hk
      cases hR with
      | ok hp => exact hp.right
      | reject => cases ho
    | endUse p =>
      obtain ⟨o, hR, ho⟩ := hk
      cases hR with
      | ok hp => exact ⟨hp.right, hp.access⟩
      | reject => cases ho
    | free p au =>
      obtain ⟨o, hR, ho⟩ := hk
      cases hR with
      | ok hp => exact ⟨hp.right, hp.access⟩
      | reject => cases ho
    | alloc pr ow ls =>
      obtain ⟨o, hR, ho⟩ := hk
      cases hR with
      | ok hst => exact ⟨hst.providerRight, hst.ownerRight⟩
      | fail => cases ho
      | reject => cases ho
    | store a p =>
      have hp := (Guarded.ok_iff.1 hk).1
      exact ⟨hp.right, hp.keepsTarget⟩
  | spawn => trivial
  | terminate => trivial
  | join => trivial
  | deriveSync hd => exact (Guarded.ok_iff.1 hd).1.authorized
  | newMutex hn => exact ⟨hn.1.exercisable, hn.1.ctlRight⟩
  | @acquire s reg ar c i st₁ hacq =>
    obtain ⟨e, he, hauth, hd, -⟩ := hacq
    show OptP (reg[i]?) _ False
    rw [he]
    exact ⟨hauth.2.2, hd.authorized⟩
  | @unlock s reg ar c i st₁ hu =>
    obtain ⟨e, g, he, -, hg, hrel, hc, hp, -⟩ := hu
    show OptP (reg[i]?) _ False
    rw [he]
    show OptP e.grant _ False
    rw [hg]
    exact ⟨hrel.holderRight, hc, hp⟩
  | @resetLock s reg ar c i st₁ hr =>
    obtain ⟨e, he, hx, -, -, hc, -⟩ := hr
    show OptP (reg[i]?) _ False
    rw [he]
    exact ⟨hx, hc⟩
  | spawnVal hs => exact valRights_of_pre _ _ (Guarded.ok_iff.1 hs).1.transfers
  | newArena hn =>
    have hp := (newArenaStepC_ok hn).2.1
    exact ⟨hp.storageRight, hp.exercisable⟩
  | @issue s reg ar c i region dst st₁ hs =>
    obtain ⟨E, s₁, hE, hst, -, hsp, hsto, -⟩ := issueStepC_ok hs
    obtain ⟨o, hR, ho⟩ := hsp
    cases hR with
    | reject => cases ho
    | ok hsp' =>
      obtain rfl := Outcome3.ok.inj ho
      have hp := (Guarded.ok_iff.1 hsto).1
      show OptP (ar[i]?) _ False
      rw [hE]
      exact ⟨hst.metaRight, hst.dstRight, hsp'.exercisable, hp.right, hp.keepsTarget⟩
  | @reset s reg ar c i st₁ hs =>
    obtain ⟨E, s₁, hE, hd, hrl, -, -⟩ := resetStepC_ok (k := ks.toK) hs
    obtain ⟨o, hR, ho⟩ := hd
    cases hR with
    | reject => cases ho
    | ok hd' =>
      obtain rfl := Outcome3.ok.inj ho
      obtain ⟨o', hR', ho'⟩ := hrl
      cases hR' with
      | reject => cases ho'
      | ok hp =>
        show OptP (ar[i]?) _ False
        rw [hE]
        exact ⟨hd'.exercisable, hp.holderRight⟩
  | readShared h => exact (Guarded.ok_iff.1 h).1.read.exercisable
  | writeShared h => exact (Guarded.ok_iff.1 h).1.o11.exercisable
  | @cas s s' reg ar c a l succ fail br h =>
    obtain (⟨-, h⟩ | ⟨-, h⟩) := h
    · cases h
    · cases br with
      | success v => exact (Guarded.ok_iff.1 h).1.o11.exercisable
      | failure v => exact (Guarded.ok_iff.1 h).1.read.exercisable

/-! ## Encapsulated traces (C22, C51.1) -/

/-- A step from `st` to `st'` of the safe reference-mutex abstraction (C22, C51.1): C22.1–C22.3
and C22.5 (`RestrictedStep`), C22.4 (`ControllerRestriction`) and C22.6 (`RightsReadFree`). A
predicate on steps of the safe abstraction, not a precondition of a kernel transition (C22,
C51.1). Exported obligation `OB-C08` (C22), stated part (`ExportedObligations`): a property of the
executions of the safe abstraction; it does not establish that the safe interfaces and the
library produce only such executions. The obligation is exported and remains open. -/
def EncapStep (pm : ProviderMeta) (ks : KShared) (L : MutexLayout) (st : SC × SyncReg × ArenaReg)
    (lbl : Label) (st' : SC × SyncReg × ArenaReg) : Prop :=
  RestrictedStep L st lbl ∧ ControllerRestriction pm L st lbl st' ∧ RightsReadFree ks L st lbl

/-- `EncapsulatedTrace` (C51.1: "the safe **reference-mutex** trace contract of C22"): a run every
step of which satisfies `EncapStep`, the six requirements of C22, in the state where it is
taken. Exported obligation `OB-C08` (C22), stated part (`ExportedObligations`): a property of the
executions of the safe abstraction; it does not establish that the safe interfaces and the
library produce only such executions. The obligation is exported and remains open. -/
inductive EncapsulatedTrace (pm : ProviderMeta) (ks : KShared) (L : MutexLayout) :
    SC × SyncReg × ArenaReg → List Label → SC × SyncReg × ArenaReg → Prop where
  | nil {st : SC × SyncReg × ArenaReg} : EncapsulatedTrace pm ks L st [] st
  | cons {st st₁ st₂ : SC × SyncReg × ArenaReg} {lbl : Label} {lbls : List Label} :
      EncapStep pm ks L st lbl st₁ → LStep ks L lbl st st₁ →
      EncapsulatedTrace pm ks L st₁ lbls st₂ → EncapsulatedTrace pm ks L st (lbl :: lbls) st₂

/-- An `EncapsulatedTrace` is a `RestrictedTrace` (C22, C23, C51.1): the results stated along
`RestrictedTrace` apply to it. -/
theorem EncapsulatedTrace.restricted {pm : ProviderMeta} {ks : KShared} {L : MutexLayout}
    {st st' : SC × SyncReg × ArenaReg} {lbls : List Label}
    (h : EncapsulatedTrace pm ks L st lbls st') : RestrictedTrace ks L st lbls st' := by
  induction h with
  | nil => exact .nil
  | cons he hs _ ih => exact .cons he.1 hs ih

end Ern.ConcurrencyModel
