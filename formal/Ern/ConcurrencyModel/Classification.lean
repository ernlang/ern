import Ern.ConcurrencyModel.Legality
import Ern.ConcurrencyModel.Preservation
import Ern.ConcurrencyModel.Ancestry

/-!
# Theorem 11: classification of accesses and exclusive ordinary access to atomic storage
(C13.11, C16–C18, C36–C42)

Theorem 11 of `formal/DESIGN.md`, Milestone 4, target theorems, continued (`Legality`):

* 11e (C36, C38, C39; C13.11, C16–C18, C48 for the controller): the accesses of a step, per leaf,
  with their kind, their atomicity and memory order, and the mode their authority requires
  (`classify`); an admitted step has at most one atomic access, and a step that may carry an
  annotation carries one exactly when it has an atomic access (`classify_atomic_le_one`,
  `writeShared_annotation_iff`).
* 11f (C42): the rule of C42 on a step (`AtomicOrdinaryOK`), which is not a kernel precondition
  (witness D12) and which an `ok` `write3` meets (`write_atomicOrdinaryOK`); the exclusivity of
  `Modify` exercise between contexts on a reached state (`modify_exercise_exclusive`).

Formalization hypothesis (realization R of the reference controller, `OB-C05` not discharged):
the controller access of a successful `acquire` is an atomic RMW, that of `unlock` and of
`resetLock` an atomic write; their memory orders are parameters (`CtlOrders`). The controller
write of `newMutex` is non-atomic (C13, C48).
-/

namespace Ern.ConcurrencyModel

open Ern.MemoryModel.Access

/-! ## 11e: classification of accesses (C36, C38, C39) -/

/-- A classified access of a step (C27, C36): the leaf, the kind of the access (C27), its memory
order if it is atomic (`some o`) or `none` if it is non-atomic (C36, C38–C40), and the mode the
authority it goes through must permit (Spec 1 §66.2, §67.1, §68.2; C37.2; C13.11). -/
structure LeafAccess where
  leaf : Nat
  kind : Events.Kind
  order : Option MemOrder
  mode : Mode
deriving DecidableEq, Repr

/-- The memory orders of the controller operations under realization R (C48, C49; `OB-C05`): the
order of the controller RMW of a successful `acquire`, and those of the controller writes of
`unlock` and `resetLock`. Parameters, not fixed by the step relation. -/
structure CtlOrders where
  acq : MemOrder
  rel : MemOrder
  reset : MemOrder
deriving DecidableEq, Repr

/-- The event kind of a modification kind (C39): a store is a write, an RMW an RMW. -/
def WriteKind.evKind : WriteKind → Events.Kind
  | .store => .write
  | .rmw _ => .rmw

/-- The accesses of a concurrent `writeShared` of kind `kind` with annotation `ord` over `region`
(C36, C39): on an `Atomic` leaf, one atomic modification of that kind whose order is the
annotation; on a `Synchronized` or `Confined` leaf, a non-atomic write; each through an authority
whose mode permits `Observe` (Spec 1 §68.2). On an admitted step an `Atomic` leaf always carries an
annotation (`writeShared_annotation_iff`). -/
def sharedWrites (ks : KShared) (region : List Nat) (ord : Option MemOrder) (kind : WriteKind) :
    List LeafAccess :=
  region.map fun l =>
    if AtomicLeaf ks l then ⟨l, kind.evKind, ord, .observe⟩ else ⟨l, .write, none, .observe⟩

/-- The controller access of the protocol operation on entry `i` (C16–C18, C48; realization R):
one atomic access of kind `k` and order `o` on `ControlOf(entry)`, through an authority whose mode
permits `Observe` (C14.3, C17.4, C18.4: Spec 1 §68.2); none if the entry or its controller does
not exist. -/
def ctlAccess (L : MutexLayout) (st : SC × SyncReg × ArenaReg) (i : Nat) (k : Events.Kind)
    (o : MemOrder) : List LeafAccess :=
  ((st.2.1[i]?).bind (ControlOf L st.1)).toList.map fun ctl => ⟨ctl, k, some o, .observe⟩

/-- The classified accesses of the step labelled `lbl` from `st` (C36, C38, C39; C13.11, C48):

* `read3` (O9): a non-atomic read of each leaf, `Observe` (C36; Spec 1 §66.2);
* `write3` (O10): a non-atomic write of each leaf, `Modify` (C36; Spec 1 §67.1);
* concurrent `writeShared`: `sharedWrites` (C36, C39), `Observe`;
* `readShared` and a failed compare-and-exchange: an atomic read of the leaf with the order of
  the operation, `Observe` (C37, C39);
* a successful compare-and-exchange: an atomic RMW of the leaf with the success order, `Observe`
  (C39);
* `newMutex`: a non-atomic write of the controller, `Modify` (C13.11, C48);
* `acquire`: an atomic RMW of the controller; `unlock`, `resetLock`: an atomic write of the
  controller; `Observe` (C14.3, C17.4, C18.4, C48; realization R, orders `R`);
* the inherited O11 `writeShared` is classified only when it satisfies the discipline acceptance
  of a store without annotation, as the concurrent store (C36, C51 item 2(e)); otherwise it has
  no classification (`none`);
* every other step has no access. -/
def classify (ks : KShared) (L : MutexLayout) (R : CtlOrders) (st : SC × SyncReg × ArenaReg) :
    Label → Option (List LeafAccess)
  | .kernel _ (.read _ ls) => some (ls.map fun l => ⟨l, .read, none, .observe⟩)
  | .kernel _ (.write _ ls) => some (ls.map fun l => ⟨l, .write, none, .modify⟩)
  | .kernel _ (.writeShared _ ls) =>
      if WriteDisciplineOK ks ls none .store then some (sharedWrites ks ls none .store) else none
  | .readShared _ _ l o _ => some [⟨l, .read, some o, .observe⟩]
  | .writeShared _ _ ls ord kind => some (sharedWrites ks ls ord kind)
  | .cas _ _ l succ _ (.success _) => some [⟨l, .rmw, some succ, .observe⟩]
  | .cas _ _ l _ fail (.failure _) => some [⟨l, .read, some fail, .observe⟩]
  | .newMutex _ g =>
      some ((ControlOf L st.1 ⟨g, none⟩).toList.map fun ctl => ⟨ctl, .write, none, .modify⟩)
  | .acquire _ i => some (ctlAccess L st i .rmw R.acq)
  | .unlock _ i => some (ctlAccess L st i .write R.rel)
  | .resetLock _ i => some (ctlAccess L st i .write R.reset)
  | _ => some []

/-- The atomic accesses of a list of classified accesses. -/
def atomics (acc : List LeafAccess) : List LeafAccess := acc.filter fun x => x.order.isSome

/-- The atomic accesses of a concurrent `writeShared` are at most its `Atomic` leaves, and none
without annotation. -/
theorem atomics_sharedWrites (ks : KShared) (region : List Nat) (ord : Option MemOrder)
    (kind : WriteKind) :
    (atomics (sharedWrites ks region ord kind)).length ≤
      (region.filter fun l => decide (AtomicLeaf ks l)).length ∧
    (ord = none → atomics (sharedWrites ks region ord kind) = []) := by
  induction region with
  | nil => exact ⟨Nat.le_refl _, fun _ => rfl⟩
  | cons l t ih =>
    obtain ⟨ih1, ih2⟩ := ih
    by_cases ha : AtomicLeaf ks l
    · refine ⟨?_, fun e => ?_⟩
      · simp only [sharedWrites, atomics, List.map_cons, ha, ite_true, List.filter_cons,
          decide_true] at ih1 ⊢
        split <;> simp only [List.length_cons] <;> omega
      · subst e
        simp only [sharedWrites, atomics, List.map_cons, ha, ite_true, List.filter_cons,
          Option.isSome_none] at ih2 ⊢
        first | exact ih2 rfl | exact ih2 trivial | exact ih2
    · refine ⟨?_, fun e => ?_⟩
      · simp only [sharedWrites, atomics, List.map_cons, ha, ite_false, List.filter_cons,
          decide_false, Option.isSome_none] at ih1 ⊢
        exact ih1
      · simp only [sharedWrites, atomics, List.map_cons, ha, ite_false, List.filter_cons,
          Option.isSome_none] at ih2 ⊢
        exact ih2 e

/-- The controller access has at most one element. -/
theorem ctlAccess_length (L : MutexLayout) (st : SC × SyncReg × ArenaReg) (i : Nat)
    (k : Events.Kind) (o : MemOrder) : (ctlAccess L st i k o).length ≤ 1 := by
  unfold ctlAccess
  cases (st.2.1[i]?).bind (ControlOf L st.1) <;> simp

/-- A sublist by `filter` is no longer than the list. -/
theorem atomics_length_le (acc : List LeafAccess) : (atomics acc).length ≤ acc.length :=
  List.length_filter_le _ _

/-- **Theorem 11e** (C38, C39, C48): every admitted step has at most one atomic access.
Obligation: `OB-C03`. -/
theorem classify_atomic_le_one {ks : KShared} {L : MutexLayout} {R : CtlOrders} {lbl : Label}
    {st st' : SC × SyncReg × ArenaReg} {acc : List LeafAccess} (h : LStep ks L lbl st st')
    (hc : classify ks L R st lbl = some acc) : (atomics acc).length ≤ 1 := by
  have nonatomic : ∀ (acc : List LeafAccess), (∀ x ∈ acc, x.order = none) →
      (atomics acc).length ≤ 1 := fun acc hn => by
    have : atomics acc = [] := List.filter_eq_nil_iff.2 fun x hx => by simp [hn x hx]
    rw [this]; exact Nat.zero_le _
  cases lbl with
  | kernel c op =>
    (cases op with
    | read a ls =>
      simp only [classify, Option.some.injEq] at hc; subst hc
      exact nonatomic _ fun x hx => by
        obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx; rfl
    | write a ls =>
      simp only [classify, Option.some.injEq] at hc; subst hc
      exact nonatomic _ fun x hx => by
        obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx; rfl
    | writeShared a ls =>
      simp only [classify] at hc
      split at hc
      · cases hc
        rw [(atomics_sharedWrites ks ls none .store).2 rfl]; exact Nat.zero_le _
      · cases hc
    | _ => simp only [classify, Option.some.injEq] at hc; subst hc; exact Nat.zero_le _)
  | writeShared c a region ord kind =>
    simp only [classify, Option.some.injEq] at hc; subst hc
    cases h with
    | writeShared hw =>
      have hd := (Guarded.ok_iff.1 hw).1.discipline
      refine Nat.le_trans (atomics_sharedWrites ks region ord kind).1 ?_
      cases kind with
      | store => exact hd.2.2.1
      | rmw v =>
        obtain ⟨l, -, -, rfl, -, -, -⟩ := hd
        exact Nat.le_trans (List.length_filter_le _ _) (Nat.le_refl _)
  | readShared => simp only [classify, Option.some.injEq] at hc; subst hc; simp [atomics]
  | cas c a l succ fail br =>
    cases br <;> (simp only [classify, Option.some.injEq] at hc; subst hc; simp [atomics])
  | newMutex =>
    simp only [classify, Option.some.injEq] at hc; subst hc
    exact nonatomic _ fun x hx => by
      obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx; rfl
  | acquire =>
    simp only [classify, Option.some.injEq] at hc; subst hc
    exact Nat.le_trans (atomics_length_le _) (ctlAccess_length ..)
  | unlock =>
    simp only [classify, Option.some.injEq] at hc; subst hc
    exact Nat.le_trans (atomics_length_le _) (ctlAccess_length ..)
  | resetLock =>
    simp only [classify, Option.some.injEq] at hc; subst hc
    exact Nat.le_trans (atomics_length_le _) (ctlAccess_length ..)
  | _ => simp only [classify, Option.some.injEq] at hc; subst hc; exact Nat.zero_le _

/-- **Theorem 11e** (C39: an `Atomic` leaf "requires an atomic memory-order annotation"; "With no
`Atomic` leaf, the annotation must be absent"): an admitted concurrent `writeShared` carries an
annotation exactly when it has an atomic access. `readShared` and the compare-and-exchange always
carry their orders and always have exactly one atomic access; the protocol operations of the
mutex carry no annotation, their orders being those of the realization (`CtlOrders`).
Obligation: `OB-C03`. -/
theorem writeShared_annotation_iff {ks : KShared} {L : MutexLayout} {R : CtlOrders} {c a : Nat}
    {region : List Nat} {ord : Option MemOrder} {kind : WriteKind}
    {st st' : SC × SyncReg × ArenaReg} (h : LStep ks L (.writeShared c a region ord kind) st st') :
    (ord.isSome ↔ ∃ x ∈ sharedWrites ks region ord kind, x.order.isSome) ∧
    classify ks L R st (.writeShared c a region ord kind) = some (sharedWrites ks region ord kind) := by
  refine ⟨⟨fun hs => ?_, fun ⟨x, hx, hxs⟩ => ?_⟩, rfl⟩
  · cases h with
    | writeShared hw =>
      have hd := (Guarded.ok_iff.1 hw).1.discipline
      have ex : ∃ l ∈ region, AtomicLeaf ks l := by
        cases kind with
        | store =>
          refine Decidable.byContradiction fun hn => ?_
          have := hd.2.2.2.2.1 fun l hl ha => hn ⟨l, hl, ha⟩
          rw [this] at hs; cases hs
        | rmw v =>
          obtain ⟨l, sz, al, rfl, e, -, -⟩ := hd
          exact ⟨l, List.mem_singleton_self _, by unfold AtomicLeaf; rw [e]; rfl⟩
      obtain ⟨l, hl, ha⟩ := ex
      exact ⟨⟨l, kind.evKind, ord, .observe⟩, List.mem_map.2 ⟨l, hl, by simp [ha]⟩, hs⟩
  · obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
    by_cases ha : AtomicLeaf ks l
    · simp only [ha, ite_true] at hxs; exact hxs
    · simp [ha] at hxs

/-! ## 11f: exclusive ordinary access to atomic storage (C42) -/

/-- The rule of C42 on the step labelled `lbl` from `s` ("an ordinary `read3` or `write3` on an
`Atomic` leaf requires an effective and exercisable `Modify` capability for that leaf"): for each
targeted `Atomic` leaf, the authority of the access is exercisable in `Modify` from the current
frame of the executing context (Spec 1 §43) and its effective mode on the leaf is `Modify`. A rule
of the safe concurrent interface, not a kernel precondition (C42; witness D12). Other steps are
not constrained by it. -/
def AtomicOrdinaryOK (ks : KShared) (s : SC) : Label → Prop
  | .kernel c (.read a ls) => ∀ l ∈ ls, AtomicLeaf ks l →
      (s.view c).ExercisableAt a .modify ∧ effective s.flat a l = some .modify
  | .kernel c (.write a ls) => ∀ l ∈ ls, AtomicLeaf ks l →
      (s.view c).ExercisableAt a .modify ∧ effective s.flat a l = some .modify
  | _ => True

/-- **Theorem 11f**, item 2 (C42: "O9 and O10 remain unchanged"): an `ok` `write3` meets the rule
of C42, by its own preconditions (Spec 1 §67.1). For `read3` the rule is not implied (witness
D12). -/
theorem write_atomicOrdinaryOK {ks : KShared} {s s' : SC} {c a : Nat} {ls : List Nat}
    (h : opStepC ks.toK (.write a ls) c s (.ok s')) :
    AtomicOrdinaryOK ks s (.kernel c (.write a ls)) := by
  obtain ⟨o, hR, ho⟩ := h
  have hR' : Guarded (Write3Pre (s.view c) a ls) (write3Eff (s.view c) ls) o := hR
  cases hR' with
  | ok hp => exact fun l hl _ => ⟨hp.exercisable, hp.effectiveModify l hl⟩
  | reject => cases ho

/-- Two exercises of the same authority, one in `Modify` from the current frame of `c`, one in
any mode from the current frame of `c'`, have the same current frame (Spec 1 §43, §49.8, §50):
along the holder chain, each holding place has a leaf (§40) on which the authority exercised in
`Modify` has effective `Modify`, so the authority of the other chain is the same (§50). -/
theorem top_eq_of_exercisable {s : SC} (h1 : I1 s.flat) (hw : WF3 s.flat) {c c' : Nat} :
    ∀ {x : Nat} {m₁ : Mode}, (s.view c).ExercisableAt x m₁ → m₁ = .modify →
      ∀ {m₂ : Mode}, (s.view c').ExercisableAt x m₂ → (s.view c).top = (s.view c').top := by
  have hv : ∀ d, (s.view d).A = s.A := fun _ => rfl
  intro x m₁ hx
  induction hx with
  | base hy _ _ hh =>
    intro _ m₂ hx'
    cases hx' with
    | base hy' _ _ hh' =>
      rw [hv] at hy hy'; rw [hy] at hy'; cases hy'
      rw [hh] at hh'; exact Holder.frame.inj hh'
    | held hy' _ _ hh' =>
      rw [hv] at hy hy'; rw [hy] at hy'; cases hy'; rw [hh] at hh'; cases hh'
  | @held a p b m₁ y hy ya _ hh _ hc ih =>
    intro hm m₂ hx'
    subst hm
    cases hx' with
    | base hy' _ _ hh' =>
      rw [hv] at hy hy'; rw [hy] at hy'; cases hy'; rw [hh] at hh'; cases hh'
    | @held _ p' b' _ y' hy' _ _ hh' hb' hc' =>
      rw [hv] at hy hy'; rw [hy] at hy'; cases hy'
      rw [hh] at hh'; cases hh'
      have hu : s.flat.Usable p := by
        have := hw.holders a y hy ya; rw [hh] at this; exact this
      obtain ⟨l, hl⟩ := exists_mem_footprint hw (s.flat.P.length - p + 1) p (by omega) hu.lt
      have hbl : effective s.flat b l = some .modify := by
        have := hc l hl
        unfold Allows OptP at this
        split at this
        · rename_i e he
          rcases this with h | h
          · cases h
          · rw [← SC.effective_view s c]; rw [he, h]
        · exact this.elim
      have hb'l : effective s.flat b' l ≠ none := by
        have := hc' l hl
        intro e
        rw [SC.effective_view] at this; rw [e] at this
        exact this
      have hbb : b' = b := Decidable.byContradiction fun hne =>
        hb'l (effective_exclusive h1 (Ne.symm hne) hbl)
      subst hbb
      exact ih rfl hb'

/-- **Theorem 11f**, item 3 (C42: "Under the applicable structural authority invariants, `Modify`
effective exercise precludes simultaneous incompatible effective exercise by another context on
the same leaf"), on a state satisfying the invariants of theorem 2 (`KInvCA`): if an authority
exercisable in `Modify` from the current frame of `c` has effective `Modify` on `l`, no authority
exercisable, in any mode, from the current frame of another context has a present effective mode
on `l`. Logical exclusivity at one abstract state only (C42). -/
theorem modify_exercise_exclusive {s : SC} (hk : KInvCA s) {c c' x y l : Nat} {m : Mode}
    (hcc : c ≠ c') (hx : (s.view c).ExercisableAt x .modify)
    (hxl : effective s.flat x l = some .modify) (hy : (s.view c').ExercisableAt y m) :
    effective s.flat y l = none := by
  have hfr : FramesC s := hk.1.1.1
  have hw : WF3 s.flat := hk.1.1.2
  have h1 : I1 s.flat := hk.1.2.1.1.1
  by_cases hxy : x = y
  · subst hxy
    exfalso
    have htop := top_eq_of_exercisable h1 hw hx rfl hy
    obtain ⟨f, r, hfr1⟩ := List.exists_cons_of_ne_nil (hfr.nonempty c (SC.live_of_exercisable hx))
    obtain ⟨f', r', hfr2⟩ :=
      List.exists_cons_of_ne_nil (hfr.nonempty c' (SC.live_of_exercisable hy))
    rw [SC.view_top hfr1, SC.view_top hfr2] at htop
    subst htop
    exact hcc (ReparentAux.stk_unique hfr.nodup (by rw [hfr1]; exact List.mem_cons_self ..)
      (by rw [hfr2]; exact List.mem_cons_self ..))
  · exact effective_exclusive h1 hxy hxl

end Ern.ConcurrencyModel
