import Ern.ConcurrencyModel.Correspondence
import Ern.ConcurrencyModel.EventLemmas

/-!
# Theorem 13: the reference controller (C48, C49)

Theorem 13 of `formal/DESIGN.md`, Milestone 4, target theorems (13c–13f; `OB-C04`, abstract part
of `OB-C05`).

* 13c (C49, first paragraph; C48; C32.1): the direct form of `LockOrder` (`lock_order_direct`).
* The realization R of the reference controller in a graph (`Realizes`), read on the controller
  steps of an entry (`CtlStep`): `newMutex` of the entry and the protocol steps on it whose
  controller is the unit `x`.
* 13d (C48, C49): the invariant on the recorded grant (`grant_invariant`), the bridge from an
  `acquire` to its `rf` source (`acquire_rf_source`), the synchronization (`acquire_sw`), the
  converse (`rf_no_between`); the construction of the controller graph is in `ControllerGraph`.
* 13e (C49; `OB-C04`): the lock order under its conditions (`lock_order`).
* 13f (C48, fifth paragraph; C49, second paragraph): recovery (`recovery_sw`).

**Realization R** (formalization hypothesis; the reference controller, `OB-C05` not discharged):
values `v₀` (available) and `v₁` (taken), `v₀ ≠ v₁`; the controller write of `newMutex` is a
non-atomic write of `v₀` on the controller unit; a successful `acquire` is an atomic RMW reading
`v₀` and writing `v₁`; `unlock` and `resetLock` are atomic writes of `v₀`; the orders are
parameters (`CtlOrders`), `acq` in the RMW row, `rel` and `reset` in the store row of C40, the
reference triple being `(acquire, release, release)`; on the controller unit, `mo` orders these
events as the trace orders their steps and the unit has no other modification; failed attempts are
not steps.

Units of the graph are leaves (C38: an `Atomic` unit is one logical leaf); values are numbers.
-/

namespace Ern.ConcurrencyModel

open Ern.MemoryModel Ern.MemoryModel.Access

/-! ## 13c: `LockOrder`, direct form (C49, C48, C32.1) -/

/-- **Theorem 13c** (C49: "the protected accesses in an earlier critical section of one mutex are
`hb`-before conflicting protected accesses in a later critical section whose lock-acquisition event
receives the preceding release"; C48: "An acquire-capable read/RMW which reads via `rf` from any
member of this sequence synchronizes with the head release `h`"; C32.1; `OB-C04`): in every graph,
if a release-capable publication `p` and an acquire-capable take `q` are on the same unit and `q`
reads by `rf` a member of the release sequence of `p`, then `sw(p, q)`, and every event that is `p`
or `po`-before `p` is `hb`-before every event that is `q` or `po`-after `q`. -/
theorem lock_order_direct {E C U V S : Type} {G : Events.Graph E C U V S} {p q m : E} {u : U}
    (hp : G.RelCap p u) (hq : G.AcqCap q u) (hm : G.RSMember u p m) (hrf : G.rf m q) :
    G.SW p q ∧ ∀ a b, (a = p ∨ G.po a p) → (b = q ∨ G.po q b) → G.HB a b := by
  have hsw : G.SW p q := .inl ⟨u, m, hp, hq, hm, hrf⟩
  refine ⟨hsw, fun a b ha hb => ?_⟩
  have hpq : G.HB p q := .single (.inr hsw)
  have hpb : G.HB p b := by
    rcases hb with rfl | hb
    · exact hpq
    · exact Relation.TransGen.tail hpq (.inl hb)
  rcases ha with rfl | ha
  · exact hpb
  · exact Relation.TransGen.trans (.single (.inl ha)) hpb

/-! ## The registry along a step (C12, C13, C16–C18) -/

/-- The recorded grant of entry `i` of a registry, if the entry exists (C12). -/
def grantOf (reg : SyncReg) (i : Nat) : Option (Option Nat) := (reg[i]?).map SyncEntry.grant

/-- `List.set` read at an index. -/
theorem getElem?_set' {α : Type} (l : List α) (i j : Nat) (a : α) :
    (l.set i a)[j]? = if i = j then (if j < l.length then some a else none) else l[j]? := by
  by_cases h : i = j
  · subst h; simp only [ite_true]; split <;> simp_all
  · simp only [h, ite_false]; exact List.getElem?_set_ne h

/-- The registry along a labelled step (C12, C13, C16–C18): its length does not decrease
(`newMutex` appends an entry); the recorded grant of an existing entry `i` changes only at
`acquire`, `unlock` or `resetLock` of `i`; `acquire` requires it `none` and records a grant;
`unlock` requires a recorded grant and records `none`; `resetLock` records `none`. -/
theorem lstep_reg {ks : KShared} {L : MutexLayout} {lbl : Label}
    {st st' : SC × SyncReg × ArenaReg} (h : LStep ks L lbl st st') (i : Nat) :
    st.2.1.length ≤ st'.2.1.length ∧
    ((∀ c, lbl ≠ .acquire c i ∧ lbl ≠ .unlock c i ∧ lbl ≠ .resetLock c i) →
      i < st.2.1.length → grantOf st'.2.1 i = grantOf st.2.1 i) ∧
    (∀ c, lbl = .acquire c i → grantOf st.2.1 i = some none ∧
      ∃ g, grantOf st'.2.1 i = some (some g)) ∧
    (∀ c, lbl = .unlock c i → (∃ g, grantOf st.2.1 i = some (some g)) ∧
      grantOf st'.2.1 i = some none) ∧
    (∀ c, lbl = .resetLock c i → grantOf st'.2.1 i = some none) := by
  have keep : ∀ (reg : SyncReg), reg.length ≤ reg.length ∧
      ((∀ c, lbl ≠ .acquire c i ∧ lbl ≠ .unlock c i ∧ lbl ≠ .resetLock c i) →
        i < reg.length → grantOf reg i = grantOf reg i) :=
    fun _ => ⟨Nat.le_refl _, fun _ _ => rfl⟩
  cases h with
  | @newMutex s reg ar c g st₁ hn =>
    obtain ⟨-, rfl⟩ := hn
    refine ⟨by simp, fun _ hi => ?_, (fun _ e => by cases e), (fun _ e => by cases e),
      (fun _ e => by cases e)⟩
    simp only [grantOf, List.getElem?_append_left hi]
  | @acquire s reg ar c j st₁ ha =>
    obtain ⟨e, hej, ⟨-, hg, -⟩, -, rfl⟩ := ha
    have hjl : j < reg.length := (List.getElem?_eq_some_iff.1 hej).1
    refine ⟨by simp, fun hne hi => ?_, fun c' e' => ?_, (fun _ e' => by cases e'),
      (fun _ e' => by cases e')⟩
    · have hji : j ≠ i := fun e => (hne c).1 (by rw [e])
      simp only [grantOf, getElem?_set', hji, ite_false]
    · cases e'
      refine ⟨by simp [grantOf, hej, hg], s.A.length, ?_⟩
      simp [grantOf, hjl]
  | @unlock s reg ar c j st₁ hu =>
    obtain ⟨e, g, hej, -, hg, -, -, -, rfl⟩ := hu
    have hjl : j < reg.length := (List.getElem?_eq_some_iff.1 hej).1
    refine ⟨by simp, fun hne hi => ?_, (fun _ e' => by cases e'), fun c' e' => ?_,
      (fun _ e' => by cases e')⟩
    · have hji : j ≠ i := fun e => (hne c).2.1 (by rw [e])
      simp only [grantOf, getElem?_set', hji, ite_false]
    · cases e'
      exact ⟨⟨g, by simp [grantOf, hej, hg]⟩, by simp [grantOf, hjl]⟩
  | @resetLock s reg ar c j st₁ hr =>
    obtain ⟨e, hej, -, -, -, -, rfl⟩ := hr
    have hjl : j < reg.length := (List.getElem?_eq_some_iff.1 hej).1
    refine ⟨by simp, fun hne hi => ?_, (fun _ e' => by cases e'), (fun _ e' => by cases e'),
      fun c' e' => ?_⟩
    · have hji : j ≠ i := fun e => (hne c).2.2 (by rw [e])
      simp only [grantOf, getElem?_set', hji, ite_false]
    · cases e'
      simp [grantOf, hjl]
  | kernel => exact ⟨(keep _).1, (keep _).2, (fun _ e => by cases e), (fun _ e => by cases e),
      (fun _ e => by cases e)⟩
  | spawn => exact ⟨(keep _).1, (keep _).2, (fun _ e => by cases e), (fun _ e => by cases e),
      (fun _ e => by cases e)⟩
  | terminate => exact ⟨(keep _).1, (keep _).2, (fun _ e => by cases e), (fun _ e => by cases e),
      (fun _ e => by cases e)⟩
  | join => exact ⟨(keep _).1, (keep _).2, (fun _ e => by cases e), (fun _ e => by cases e),
      (fun _ e => by cases e)⟩
  | deriveSync => exact ⟨(keep _).1, (keep _).2, (fun _ e => by cases e), (fun _ e => by cases e),
      (fun _ e => by cases e)⟩
  | spawnVal => exact ⟨(keep _).1, (keep _).2, (fun _ e => by cases e), (fun _ e => by cases e),
      (fun _ e => by cases e)⟩
  | newArena => exact ⟨(keep _).1, (keep _).2, (fun _ e => by cases e), (fun _ e => by cases e),
      (fun _ e => by cases e)⟩
  | issue => exact ⟨(keep _).1, (keep _).2, (fun _ e => by cases e), (fun _ e => by cases e),
      (fun _ e => by cases e)⟩
  | reset => exact ⟨(keep _).1, (keep _).2, (fun _ e => by cases e), (fun _ e => by cases e),
      (fun _ e => by cases e)⟩
  | readShared => exact ⟨(keep _).1, (keep _).2, (fun _ e => by cases e), (fun _ e => by cases e),
      (fun _ e => by cases e)⟩
  | writeShared => exact ⟨(keep _).1, (keep _).2, (fun _ e => by cases e), (fun _ e => by cases e),
      (fun _ e => by cases e)⟩
  | cas => exact ⟨(keep _).1, (keep _).2, (fun _ e => by cases e), (fun _ e => by cases e),
      (fun _ e => by cases e)⟩

/-! ## Controller steps and realization R (C12, C13, C16–C18, C48) -/

/-- The orders of the controller operations are legal (C40): the acquiring RMW in the RMW row,
the publications of `unlock` and `resetLock` in the store row. -/
def CtlOrders.Legal (R : CtlOrders) : Prop :=
  RMWOrderOK R.acq ∧ StoreOrderOK R.rel ∧ StoreOrderOK R.reset

/-- The reference triple (C48: "an acquire-capable memory order"; "an atomic release publication";
"The reference successful recovery publishes the controller's available state by an atomic
**`release` store**"): `(acquire, release, release)`. -/
def refOrders : CtlOrders := ⟨.acquire, .release, .release⟩

/-- An order with release semantics for a write (C32.1, C40): `release`, `acq_rel`, `seq_cst`. -/
def ReleaseOrder (o : MemOrder) : Prop := o = .release ∨ o = .acqRel ∨ o = .seqCst

/-- An order with acquire semantics for a read (C32.1, C40): `acquire`, `acq_rel`, `seq_cst`. -/
def AcquireOrder (o : MemOrder) : Prop := o = .acquire ∨ o = .acqRel ∨ o = .seqCst

/-- The controller of entry `i` in `st`, if the entry and its controller exist (C12). -/
def ctlOf (L : MutexLayout) (st : SC × SyncReg × ArenaReg) (i : Nat) : Option Nat :=
  (st.2.1[i]?).bind (ControlOf L st.1)

/-- Step `k` is a protocol step on entry `i` (C16–C18): `acquire`, `unlock` or `resetLock` of
`i`. -/
def ProtoOn (lbls : List Label) (i k : Nat) : Prop :=
  match lbls[k]? with
  | some (.acquire _ j) | some (.unlock _ j) | some (.resetLock _ j) => j = i
  | _ => False

/-- Step `k` is a controller step of entry `i` with controller `x` (C12, C13, C48): the `newMutex`
that creates entry `i` with controller `x`, or a protocol step on `i` taken while its controller
is `x`. -/
def CtlStep (L : MutexLayout) (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label)
    (i x k : Nat) : Prop :=
  match lbls[k]? with
  | some (.acquire _ j) | some (.unlock _ j) | some (.resetLock _ j) =>
      j = i ∧ ctlOf L (σ k) i = some x
  | some (.newMutex _ g) => (σ k).2.1.length = i ∧ ControlOf L (σ k).1 ⟨g, none⟩ = some x
  | _ => False

instance (lbls : List Label) (i k : Nat) : Decidable (ProtoOn lbls i k) := by
  unfold ProtoOn; split <;> infer_instance

instance (L : MutexLayout) (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label)
    (i x k : Nat) : Decidable (CtlStep L σ lbls i x k) := by
  unfold CtlStep; split <;> infer_instance

/-- The access of the event of a controller step under realization R (C13, C31, C48): `newMutex`
writes `v₀` non-atomically; `acquire` is an atomic RMW reading `v₀` and writing `v₁`; `unlock` and
`resetLock` atomically write `v₀`, with the orders of `R`. -/
def ctlAcc (x : Nat) (R : CtlOrders) (v₀ v₁ : Nat) : Label → Events.Acc Nat Nat
  | .acquire _ _ => .atomic x R.acq (.rmw v₀ v₁)
  | .unlock _ _ => .atomic x R.rel (.write v₀)
  | .resetLock _ _ => .atomic x R.reset (.write v₀)
  | _ => .unit x (.write v₀)

/-- Realization R of the reference controller of entry `i` on the unit `x` in the graph `G` under
the correspondence `K`, with the orders `R` and the values `v₀ ≠ v₁` (C13, C31, C48; formalization
hypothesis, `OB-C05`): the event of every controller step has the access `ctlAcc` (kind,
atomicity, order and values); `mo` orders the events of the controller steps as the trace orders
the steps; every modification of `x` is the event of a controller step. -/
structure Realizes {E S : Type} (G : Events.Graph E Nat Nat Nat S) (L : MutexLayout)
    (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) (K : StepEvents E) (i x : Nat)
    (R : CtlOrders) (v₀ v₁ : Nat) : Prop where
  /-- `v₀ ≠ v₁`. -/
  values : v₀ ≠ v₁
  /-- The event of each controller step. -/
  ev : ∀ k lbl, lbls[k]? = some lbl → CtlStep L σ lbls i x k → ∃ e, K.ev k = some e ∧
    G.acc? e = some (ctlAcc x R v₀ v₁ lbl)
  /-- Linearization on `x`: `mo` is the trace order of the controller steps. -/
  mo : ∀ k k' e e', CtlStep L σ lbls i x k → CtlStep L σ lbls i x k' → K.ev k = some e →
    K.ev k' = some e' → (G.mo e e' ↔ k < k')
  /-- `x` has no other modification. -/
  only : ∀ w, G.ModOn w x → ∃ k, CtlStep L σ lbls i x k ∧ K.ev k = some w

/-- Step `w` is the last controller step of entry `i` with controller `x` before step `k`. -/
def LastCtl (L : MutexLayout) (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label)
    (i x k w : Nat) : Prop :=
  CtlStep L σ lbls i x w ∧ w < k ∧ ∀ w', CtlStep L σ lbls i x w' → w' < k → w' ≤ w

/-- The last controller step is unique. -/
theorem LastCtl.unique {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label}
    {i x k w w' : Nat} (h : LastCtl L σ lbls i x k w) (h' : LastCtl L σ lbls i x k w') :
    w = w' :=
  Nat.le_antisymm (h'.2.2 w h.1 h.2.1) (h.2.2 w' h'.1 h'.2.1)

/-! ## 13d.3, 13d.4, 13d.5: the `rf` source of an `acquire` (C31, C34, C48) -/

section Bridge

variable {E S : Type} {G : Events.Graph E Nat Nat Nat S} {L : MutexLayout}
  {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} {K : StepEvents E} {i x : Nat}
  {R : CtlOrders} {v₀ v₁ : Nat}

/-- The event of an `acquire` controller step reads the unit `x` (C31). -/
theorem acquire_readOn (hR : Realizes G L σ lbls K i x R v₀ v₁) {k c j : Nat}
    (hl : lbls[k]? = some (.acquire c j)) (hk : CtlStep L σ lbls i x k) :
    ∃ q, K.ev k = some q ∧ G.ReadOn q x ∧
      G.acc? q = some (.atomic x R.acq (.rmw v₀ v₁)) := by
  obtain ⟨q, hq, hacc⟩ := hR.ev k _ hl hk
  refine ⟨q, hq, ⟨?_, ?_⟩, hacc⟩
  · unfold Events.Graph.unitOf; rw [hacc]; rfl
  · exact ⟨.rmw, by unfold Events.Graph.kind?; rw [hacc]; rfl, trivial⟩

/-- **Theorem 13d.3**, bridge (C31: "For a successful atomic RMW, its read component obtains the
immediately preceding modification of its atomic location in `mo`"; C48): in every graph that
satisfies R for entry `i` and unit `x` and the conjuncts 1 and 3 of `EventConsistent`, the event of
an `acquire` controller step `k` has an `rf` source, and every `rf` source of it is the event of the
last controller step before `k` in the trace. -/
theorem acquire_rf_source (hR : Realizes G L σ lbls K i x R v₀ v₁) (h1 : G.RfWF)
    (h3 : G.RmwAtomic) {k c j : Nat} (hl : lbls[k]? = some (.acquire c j))
    (hk : CtlStep L σ lbls i x k) {q : E} (hq : K.ev k = some q) :
    (∃ w, G.rf w q) ∧ ∀ w, G.rf w q → ∃ k', LastCtl L σ lbls i x k k' ∧ K.ev k' = some w := by
  obtain ⟨q', hq', hro, hacc⟩ := acquire_readOn hR hl hk
  rw [hq] at hq'; cases hq'
  refine ⟨(h1.2.1 q x hro).1, fun w hrf => ?_⟩
  obtain ⟨u, hwu, hqu⟩ := h1.1 w q hrf
  have hux : u = x := Events.Graph.unitOf_inj G hqu.1 hro.1
  subst hux
  obtain ⟨k', hk', hw⟩ := hR.only w hwu
  have hrmw : G.IsRMW q := by unfold Events.Graph.IsRMW Events.Graph.kind?; rw [hacc]; rfl
  have hat : G.Atomic q := ⟨_, _, _, hacc⟩
  obtain ⟨hmo, hnb⟩ := h3 w q hrmw hat hrf
  refine ⟨k', ⟨hk', (hR.mo k' k w q hk' hk hw hq).1 hmo, fun w' hw' hlt => ?_⟩, hw⟩
  refine Decidable.byContradiction fun hn => ?_
  obtain ⟨lw, hlw⟩ : ∃ lw, lbls[w']? = some lw := by
    unfold CtlStep at hw'; split at hw' <;> simp_all
  obtain ⟨e', he', -⟩ := hR.ev w' lw hlw hw'
  exact hnb e' ⟨(hR.mo k' w' w e' hk' hw' hw he').2 (by omega),
    (hR.mo w' k e' q hw' hk he' hq).2 hlt⟩

/-- The `rf` source of the event of an `acquire` controller step is the event of the last
controller step, when that event is given (13d.3). -/
theorem acquire_rf_last (hR : Realizes G L σ lbls K i x R v₀ v₁) (h1 : G.RfWF)
    (h3 : G.RmwAtomic) {k c j k' : Nat} (hl : lbls[k]? = some (.acquire c j))
    (hk : CtlStep L σ lbls i x k) {q w : E} (hq : K.ev k = some q)
    (hlast : LastCtl L σ lbls i x k k') (hw : K.ev k' = some w) : G.rf w q := by
  obtain ⟨⟨w', hrf⟩, hsrc⟩ := acquire_rf_source hR h1 h3 hl hk hq
  obtain ⟨k'', hl'', hw''⟩ := hsrc w' hrf
  have := hlast.unique hl''
  subst this
  rw [hw''] at hw; cases hw; exact hrf

/-- The atomic source of `sw` (C32.1, C48): `w` is release-capable and `q` acquire-capable on the
same unit, and `q` reads by `rf` a member of the release sequence of `w`. It is the first source of
`Events.Graph.SW`; the other two are the lifecycle sources of C32.2 and C32.3. -/
def AtomicSW {E C U V S : Type} (G : Events.Graph E C U V S) (w q : E) : Prop :=
  ∃ u m, G.RelCap w u ∧ G.AcqCap q u ∧ G.RSMember u w m ∧ G.rf m q

/-- The atomic source is a source of `sw` (C32). -/
theorem AtomicSW.sw {E C U V S : Type} {G : Events.Graph E C U V S} {w q : E}
    (h : AtomicSW G w q) : G.SW w q :=
  .inl h

/-- **Theorem 13d.4**, synchronization (C48: "When a later acquiring RMW **directly reads** this
release modification (`rf`), the protocol yields the requisite `sw`"; C49; C31: the initializing
write is non-atomic and "does not itself establish `sw`"), as proved: for an `acquire` controller
step `k` whose last preceding controller step is `k'`, in every graph that satisfies R and the
conjuncts 1 and 3:

* if `k'` is an `unlock` (a `resetLock`), a release-capable publication order and an
  acquire-capable acquisition order give `sw` between their events; and the atomic source of `sw`
  (C32.1) relates them exactly when the orders are so;
* if `k'` is the `newMutex`, the atomic source of `sw` never relates them.

Realization R does not fix the `sync` attribute of the events: that `sw` relates them only through
its atomic source, the converse for the whole of `sw`, is not established. -/
theorem acquire_sw (hR : Realizes G L σ lbls K i x R v₀ v₁) (h1 : G.RfWF) (h3 : G.RmwAtomic)
    {k c j k' : Nat} (hl : lbls[k]? = some (.acquire c j)) (hk : CtlStep L σ lbls i x k) {q : E}
    (hq : K.ev k = some q) (hlast : LastCtl L σ lbls i x k k') {w : E}
    (hw : K.ev k' = some w) :
    (∀ c' j', lbls[k']? = some (.unlock c' j') →
      (ReleaseOrder R.rel ∧ AcquireOrder R.acq → G.SW w q) ∧
      (AtomicSW G w q ↔ ReleaseOrder R.rel ∧ AcquireOrder R.acq)) ∧
    (∀ c' j', lbls[k']? = some (.resetLock c' j') →
      (ReleaseOrder R.reset ∧ AcquireOrder R.acq → G.SW w q) ∧
      (AtomicSW G w q ↔ ReleaseOrder R.reset ∧ AcquireOrder R.acq)) ∧
    (∀ c' g, lbls[k']? = some (.newMutex c' g) → ¬ AtomicSW G w q) := by
  have hrf := acquire_rf_last hR h1 h3 hl hk hq hlast hw
  obtain ⟨q', hq', hqacc⟩ := hR.ev k _ hl hk
  rw [hq] at hq'; cases hq'
  have pub : ∀ (lbl : Label) (o : MemOrder), lbls[k']? = some lbl →
      ctlAcc x R v₀ v₁ lbl = .atomic x o (.write v₀) →
      (ReleaseOrder o ∧ AcquireOrder R.acq → G.SW w q) ∧
      (AtomicSW G w q ↔ ReleaseOrder o ∧ AcquireOrder R.acq) := by
    intro lbl o hl' hacc
    obtain ⟨w', hw', hwacc⟩ := hR.ev k' lbl hl' hlast.1
    rw [hw] at hw'; cases hw'
    rw [hacc] at hwacc
    have hiff : AtomicSW G w q ↔ ReleaseOrder o ∧ AcquireOrder R.acq := by
      constructor
      · rintro ⟨u, m, ⟨o₁, k₁, h₁, -, ho₁⟩, ⟨o₂, k₂, h₂, -, ho₂⟩, -, -⟩
        rw [hwacc] at h₁; cases h₁
        rw [hqacc] at h₂; cases h₂
        exact ⟨ho₁, ho₂⟩
      · rintro ⟨ho, ha⟩
        exact ⟨x, w, ⟨o, _, hwacc, trivial, ho⟩, ⟨R.acq, _, hqacc, trivial, ha⟩, .inl rfl, hrf⟩
    exact ⟨fun h => (hiff.2 h).sw, hiff⟩
  refine ⟨fun c' j' hl' => pub _ R.rel hl' rfl, fun c' j' hl' => pub _ R.reset hl' rfl,
    fun c' g hl' hsw => ?_⟩
  obtain ⟨w', hw', hwacc⟩ := hR.ev k' _ hl' hlast.1
  rw [hw] at hw'; cases hw'
  obtain ⟨u, m, ⟨o₁, k₁, h₁, -, -⟩, -⟩ := hsw
  rw [hwacc] at h₁; cases h₁

/-- **Theorem 13d.5**, converse (C48; C49: "Any abstraction of the C48 mutex `sw` edge must respect
interventions on the controller between the release and the acquisition"): if `rf` relates the
event of a controller step `k'` to that of an `acquire` controller step `k`, then `k' < k` and no
controller step lies strictly between them. -/
theorem rf_no_between (hR : Realizes G L σ lbls K i x R v₀ v₁) (h1 : G.RfWF) (h3 : G.RmwAtomic)
    {k c j k' : Nat} (hl : lbls[k]? = some (.acquire c j)) (hk : CtlStep L σ lbls i x k) {q : E}
    (hq : K.ev k = some q) (hk' : CtlStep L σ lbls i x k') {w : E} (hw : K.ev k' = some w)
    (hrf : G.rf w q) :
    k' < k ∧ ∀ k'', CtlStep L σ lbls i x k'' → ¬ (k' < k'' ∧ k'' < k) := by
  obtain ⟨k₀, hlast, hw₀⟩ := (acquire_rf_source hR h1 h3 hl hk hq).2 w hrf
  have e1 := hR.mo k' k₀ w w hk' hlast.1 hw hw₀
  have e2 := hR.mo k₀ k' w w hlast.1 hk' hw₀ hw
  have hk₀ : k' = k₀ := by
    rcases Nat.lt_trichotomy k' k₀ with h | h | h
    · exact absurd (e2.1 (e1.2 h)) (by omega)
    · exact h
    · exact absurd (e1.1 (e2.2 h)) (by omega)
  subst hk₀
  exact ⟨hlast.2.1, fun k'' hk'' ⟨h₁, h₂⟩ => by have := hlast.2.2 k'' hk'' h₂; omega⟩

end Bridge

/-! ## The recorded grant along an execution (C13, C16–C18) -/

section Trace

variable {ks : KShared} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label}

/-- The registry does not shrink along an execution (C12, C13). -/
theorem encapRun_reg_mono (hr : EncapRun ks L σ lbls) {a b : Nat} (hab : a ≤ b)
    (hb : b ≤ lbls.length) : (σ a).2.1.length ≤ (σ b).2.1.length := by
  induction b with
  | zero => have : a = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ b ih =>
    rcases Nat.lt_or_eq_of_le hab with h | h
    · exact Nat.le_trans (ih (by omega) (by omega)) (lstep_reg (hr b (by omega)).2 0).1
    · subst h; exact Nat.le_refl _

/-- A step that is not a protocol step on `i` keeps the recorded grant of an existing entry `i`
(C12, C16–C18). -/
theorem grant_keep (hr : EncapRun ks L σ lbls) {i k : Nat} (hk : k < lbls.length)
    (hp : ¬ ProtoOn lbls i k) (hi : i < (σ k).2.1.length) :
    grantOf (σ (k + 1)).2.1 i = grantOf (σ k).2.1 i := by
  refine (lstep_reg (hr k hk).2 i).2.1 (fun c => ⟨fun e => hp ?_, fun e => hp ?_, fun e => hp ?_⟩)
    hi <;> simp [ProtoOn, List.getElem?_eq_getElem hk, e]

/-- Across steps that are not protocol steps on `i`, the recorded grant of an existing entry `i`
is kept (C12, C16–C18). -/
theorem grant_const (hr : EncapRun ks L σ lbls) {i a b : Nat} (hab : a ≤ b)
    (hb : b ≤ lbls.length) (hp : ∀ k, a ≤ k → k < b → ¬ ProtoOn lbls i k)
    (hi : i < (σ a).2.1.length) : grantOf (σ b).2.1 i = grantOf (σ a).2.1 i := by
  induction b with
  | zero => have : a = 0 := by omega
            subst this; rfl
  | succ b ih =>
    rcases Nat.lt_or_eq_of_le hab with h | h
    · rw [grant_keep hr (by omega) (hp b (by omega) (by omega))
        (Nat.lt_of_lt_of_le hi (encapRun_reg_mono hr (by omega) (by omega)))]
      exact ih (by omega) (by omega) fun k h1 h2 => hp k h1 (by omega)
    · subst h; rfl

/-- A protocol step on `i` taken while its controller is `x` is a controller step (C48). -/
theorem ctlStep_of_proto {i x k : Nat} (hp : ProtoOn lbls i k) (hc : ctlOf L (σ k) i = some x) :
    CtlStep L σ lbls i x k := by
  unfold ProtoOn at hp; unfold CtlStep
  split at hp <;> simp_all

/-- A controller step taken while entry `i` exists is a protocol step (C13: `newMutex` creates the
entry). -/
theorem proto_of_ctlStep {i x k : Nat} (hc : CtlStep L σ lbls i x k)
    (hi : i < (σ k).2.1.length) : ProtoOn lbls i k := by
  unfold CtlStep at hc; unfold ProtoOn
  split at hc <;> simp_all <;> omega

/-- An `ok` `newMutex` appends an available entry (C13 effect). -/
theorem lstep_newMutex {st st' : SC × SyncReg × ArenaReg} {c g : Nat}
    (h : LStep ks L (.newMutex c g) st st') : st'.2.1 = st.2.1 ++ [⟨g, none⟩] := by
  cases h with
  | newMutex hn => obtain ⟨-, rfl⟩ := hn; rfl

/-- **Theorem 13d.2**, invariant (C13: "The library registers an initially available
`SyncEntry`"; C16–C18; C48): along an execution in which the `newMutex` step `n` creates entry `i`
with controller `x` and every later protocol step on `i` is taken while the controller is `x`, at
every later state `k` the last controller step `w` before `k` exists, and the recorded grant of `i`
is `none` exactly when `w` is not an `acquire`, that is when the event of `w` writes `v₀` under
realization R. -/
theorem grant_invariant (hr : EncapRun ks L σ lbls) {i x n c g : Nat}
    (hn : lbls[n]? = some (.newMutex c g)) (hnc : CtlStep L σ lbls i x n)
    (hstab : ∀ k, n < k → ProtoOn lbls i k → ctlOf L (σ k) i = some x) :
    ∀ k, n < k → k ≤ lbls.length → ∃ w, LastCtl L σ lbls i x k w ∧
      (grantOf (σ k).2.1 i = some none ↔ ∀ c' j, lbls[w]? ≠ some (.acquire c' j)) := by
  have hnl : n < lbls.length := (List.getElem?_eq_some_iff.1 hn).1
  have hlen : (σ n).2.1.length = i := by
    unfold CtlStep at hnc; rw [hn] at hnc; exact hnc.1
  have hreg : (σ (n + 1)).2.1 = (σ n).2.1 ++ [⟨g, none⟩] := by
    have hs := (hr n hnl).2
    have hln : lbls[n] = .newMutex c g := (List.getElem?_eq_some_iff.1 hn).2
    rw [hln] at hs
    exact lstep_newMutex hs
  have hex : ∀ k, n < k → k ≤ lbls.length → i < (σ k).2.1.length := fun k h1 h2 =>
    Nat.lt_of_lt_of_le (by rw [hreg]; simp [hlen]) (encapRun_reg_mono hr h1 h2)
  intro k hk hkl
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hk' | hk'
    · obtain ⟨w, hlast, hiff⟩ := ih hk' (by omega)
      have hkl' : k < lbls.length := by omega
      have hik := hex k hk' (by omega)
      by_cases hck : CtlStep L σ lbls i x k
      · refine ⟨k, ⟨hck, Nat.lt_succ_self _, fun w' _ h => Nat.le_of_lt_succ h⟩, ?_⟩
        have hp := proto_of_ctlStep hck hik
        obtain ⟨lbl, hlbl⟩ : ∃ lbl, lbls[k]? = some lbl := ⟨_, List.getElem?_eq_getElem hkl'⟩
        have hs := (hr k hkl').2
        have hreg' := lstep_reg hs i
        have hlk : lbls[k] = lbl := (List.getElem?_eq_some_iff.1 hlbl).2
        rw [hlk] at hreg'
        unfold ProtoOn at hp; rw [hlbl] at hp
        cases lbl with
        | acquire c' j =>
          cases hp
          obtain ⟨g', hg'⟩ := (hreg'.2.2.1 c' rfl).2
          rw [hg']
          exact ⟨(fun h => by cases h), fun h => absurd hlbl (h c' i)⟩
        | unlock c' j =>
          cases hp
          rw [(hreg'.2.2.2.1 c' rfl).2]
          exact ⟨(fun _ c'' j' h => by rw [hlbl] at h; cases h), fun _ => rfl⟩
        | resetLock c' j =>
          cases hp
          rw [hreg'.2.2.2.2 c' rfl]
          exact ⟨(fun _ c'' j' h => by rw [hlbl] at h; cases h), fun _ => rfl⟩
        | _ => exact hp.elim
      · refine ⟨w, ⟨hlast.1, Nat.lt_succ_of_lt hlast.2.1, fun w' hw' h => ?_⟩, ?_⟩
        · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h) with h' | h'
          · exact hlast.2.2 w' hw' h'
          · subst h'; exact absurd hw' hck
        · rw [grant_keep hr hkl' (fun hp => hck (ctlStep_of_proto hp (hstab k hk' hp))) hik]
          exact hiff
    · subst hk'
      refine ⟨n, ⟨hnc, Nat.lt_succ_self _, fun w' _ h => Nat.le_of_lt_succ h⟩, ?_⟩
      simp only [grantOf, hreg, List.getElem?_append_right (Nat.le_of_eq hlen), hlen,
        Nat.sub_self]
      exact ⟨(fun _ c' j h => by rw [hn] at h; cases h), fun _ => rfl⟩

end Trace

/-! ## 13e, 13f: lock order and recovery (C48, C49) -/

section Order

variable {ks : KShared} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label}
  {E S : Type} {G : Events.Graph E Nat Nat Nat S} {K : StepEvents E} {i x : Nat}
  {R : CtlOrders} {v₀ v₁ : Nat}

/-- A controller step has a label. -/
theorem CtlStep.label {k : Nat} (h : CtlStep L σ lbls i x k) : ∃ lbl, lbls[k]? = some lbl := by
  unfold CtlStep at h; split at h <;> simp_all

/-- The first controller step after `w`, when a controller step `a > w` exists. -/
theorem first_ctl_after {w a : Nat} (hwa : w < a) (ha : CtlStep L σ lbls i x a) :
    ∃ p, w < p ∧ p ≤ a ∧ CtlStep L σ lbls i x p ∧ ∀ k, w < k → k < p → ¬ CtlStep L σ lbls i x k := by
  obtain ⟨r, h1, h2, h3, h4⟩ := exists_first
    (P := fun k => ∃ k' ∈ List.range (k + 1), w < k' ∧ CtlStep L σ lbls i x k') hwa
    (fun ⟨k', hk', hw, _⟩ => by have := List.mem_range.1 hk'; omega)
    ⟨a, List.mem_range.2 (Nat.lt_succ_self _), hwa, ha⟩
  obtain ⟨k', hk', hwk, hck⟩ := h3
  have hk'r : k' = r + 1 := by
    refine Decidable.byContradiction fun hne => h4 r h1 (Nat.le_refl _) ⟨k', ?_, hwk, hck⟩
    have := List.mem_range.1 hk'; exact List.mem_range.2 (by omega)
  subst hk'r
  refine ⟨r + 1, hwk, Nat.succ_le_of_lt h2, hck, fun k hk1 hk2 hc => ?_⟩
  exact h4 k (by omega) (by omega) ⟨k, List.mem_range.2 (Nat.lt_succ_self k), hk1, hc⟩

/-- **Theorem 13d.2**, reads (C31, C48): every `rf` source of an `acquire` event writes `v₀`: under the
hypotheses of `grant_invariant`, in every graph that satisfies R and the conjuncts 1 and 3, the
source of the event of an `acquire` controller step is the event of a `newMutex`, `unlock` or
`resetLock` step, which writes `v₀`. -/
theorem acquire_reads_v0 (hr : EncapRun ks L σ lbls) (hR : Realizes G L σ lbls K i x R v₀ v₁)
    (h1 : G.RfWF) (h3 : G.RmwAtomic) {n c g : Nat} (hn : lbls[n]? = some (.newMutex c g))
    (hnc : CtlStep L σ lbls i x n)
    (hstab : ∀ k, n < k → ProtoOn lbls i k → ctlOf L (σ k) i = some x)
    {k c' j : Nat} (hl : lbls[k]? = some (.acquire c' j)) (hk : CtlStep L σ lbls i x k) {q w : E}
    (hq : K.ev k = some q) (hrf : G.rf w q) : G.valW w = some v₀ := by
  have hkl : k < lbls.length := (List.getElem?_eq_some_iff.1 hl).1
  have hji : j = i := by unfold CtlStep at hk; rw [hl] at hk; exact hk.1
  subst hji
  have hnk : n < k := by
    have hnl : n < lbls.length := (List.getElem?_eq_some_iff.1 hn).1
    have hlen : (σ n).2.1.length = j := by unfold CtlStep at hnc; rw [hn] at hnc; exact hnc.1
    have hex : j < (σ k).2.1.length := by
      unfold CtlStep at hk; rw [hl] at hk
      obtain ⟨-, hc⟩ := hk
      unfold ctlOf at hc
      cases he : (σ k).2.1[j]? with
      | none => rw [he] at hc; cases hc
      | some _ => exact (List.getElem?_eq_some_iff.1 he).1
    refine Decidable.byContradiction fun hn' => ?_
    have := encapRun_reg_mono hr (Nat.le_of_not_lt hn') (Nat.le_of_lt hnl)
    omega
  obtain ⟨k₀, hlast, hw₀⟩ := (acquire_rf_source hR h1 h3 hl hk hq).2 w hrf
  obtain ⟨w', hlast', hiff⟩ := grant_invariant hr hn hnc hstab k hnk (Nat.le_of_lt hkl)
  have := hlast.unique hlast'
  subst this
  have hs := (hr k hkl).2
  have hlk : lbls[k] = .acquire c' j := (List.getElem?_eq_some_iff.1 hl).2
  rw [hlk] at hs
  have hnone := ((lstep_reg hs j).2.2.1 c' rfl).1
  have hnacq := hiff.1 hnone
  obtain ⟨lbl, hlbl⟩ := hlast.1.label
  obtain ⟨w'', hw'', hacc⟩ := hR.ev k₀ lbl hlbl hlast.1
  rw [hw₀] at hw''; cases hw''
  unfold Events.Graph.valW; rw [hacc]
  cases lbl with
  | acquire c'' j'' => exact absurd hlbl (hnacq c'' j'')
  | _ => rfl

/-- **Theorem 13e**, lock order (C49: "`LockOrder` is the obligation that the protected accesses in
an earlier critical section of one mutex are `hb`-before conflicting protected accesses in a later
critical section whose lock-acquisition event receives the preceding release"; C48; `OB-C04`). On
an execution with a correspondence and a graph satisfying R for entry `i` and unit `x`, with
release-capable publication orders and an acquire-capable acquisition order, and the conjuncts 1
and 3 of `EventConsistent`: let `u` be an `unlock` or `resetLock` controller step of `i` and `a > u`
an `acquire` controller step of `i` such that

* the controller of `i` is `x` at every protocol step on `i` from `u` to `a` (stability of the
  leaf);
* no `resetLock` of `i` lies strictly between `u` and `a` (recovery);
* every `acquire` of `i` at `p` strictly between `u` and `a` is followed, before `a`, by an
  `unlock` of `i` at `p'` whose event is `hb`-after that of `p` (intermediate acquisitions).

Then the event of `u` is `hb`-before that of `a`; hence the event of every step `≤ u` of the context
of `u` is `hb`-before that of every step `≥ a` of the context of `a`. -/
theorem lock_order (hr : EncapRun ks L σ lbls) (hK : Corresponds G σ lbls K)
    (hR : Realizes G L σ lbls K i x R v₀ v₁) (hrel : ReleaseOrder R.rel)
    (hreset : ReleaseOrder R.reset) (hacq : AcquireOrder R.acq) (h1 : G.RfWF)
    (h3 : G.RmwAtomic) {u a : Nat} (hua : u < a) (hu : CtlStep L σ lbls i x u)
    (hukind : ∃ c, lbls[u]? = some (.unlock c i) ∨ lbls[u]? = some (.resetLock c i))
    (ha : CtlStep L σ lbls i x a) (hakind : ∃ c, lbls[a]? = some (.acquire c i))
    (hstab : ∀ k, u ≤ k → k ≤ a → ProtoOn lbls i k → ctlOf L (σ k) i = some x)
    (hnoreset : ∀ k, u < k → k < a → ∀ c, lbls[k]? ≠ some (.resetLock c i))
    (hmid : ∀ p, u < p → p < a → (∃ c, lbls[p]? = some (.acquire c i)) →
      ∃ p', p < p' ∧ p' < a ∧ (∃ c, lbls[p']? = some (.unlock c i)) ∧
        ∀ ep ep', K.ev p = some ep → K.ev p' = some ep' → G.HB ep ep') :
    (∀ eu ea, K.ev u = some eu → K.ev a = some ea → G.HB eu ea) ∧
    ∀ p (hp : p < lbls.length) j (hj : j < lbls.length) ep ej, p ≤ u → ∀ (haj : a ≤ j),
      lbls[p].requester = (lbls[u]'(by omega)).requester →
      lbls[j].requester = (lbls[a]'(by omega)).requester →
      K.ev p = some ep → K.ev j = some ej → G.HB ep ej := by
  have hal : a < lbls.length := by
    obtain ⟨c, hc⟩ := hakind; exact (List.getElem?_eq_some_iff.1 hc).1
  have hiu : i < (σ u).2.1.length := by
    unfold CtlStep at hu; obtain ⟨c, hc | hc⟩ := hukind <;> rw [hc] at hu <;>
    · obtain ⟨-, hctl⟩ := hu
      unfold ctlOf at hctl
      cases he : (σ u).2.1[i]? with
      | none => rw [he] at hctl; cases hctl
      | some _ => exact (List.getElem?_eq_some_iff.1 he).1
  have hex : ∀ k, u ≤ k → k ≤ lbls.length → i < (σ k).2.1.length := fun k h1 h2 =>
    Nat.lt_of_lt_of_le hiu (encapRun_reg_mono hr h1 h2)
  have evOf : ∀ k, CtlStep L σ lbls i x k → ∃ e, K.ev k = some e := fun k hk => by
    obtain ⟨lbl, hl⟩ := hk.label
    obtain ⟨e, he, -⟩ := hR.ev k lbl hl hk
    exact ⟨e, he⟩
  -- The claim, by strong induction on the distance to `a`.
  have claim : ∀ n w, a - w = n → u ≤ w → w < a → CtlStep L σ lbls i x w →
      (∃ c, lbls[w]? = some (.unlock c i) ∨ lbls[w]? = some (.resetLock c i)) →
      ∀ eu ew, K.ev u = some eu → K.ev w = some ew → (eu = ew ∨ G.HB eu ew) →
      ∀ ea, K.ev a = some ea → G.HB eu ea := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
    intro w hn huw hwa hw hwkind eu ew heu hew hrel_uw ea hea
    have hwl : w < lbls.length := by omega
    -- the recorded grant is `none` after `w`
    have hg1 : grantOf (σ (w + 1)).2.1 i = some none := by
      have hs := (hr w hwl).2
      obtain ⟨c, hc | hc⟩ := hwkind
      · rw [(List.getElem?_eq_some_iff.1 hc).2] at hs
        exact ((lstep_reg hs i).2.2.2.1 c rfl).2
      · rw [(List.getElem?_eq_some_iff.1 hc).2] at hs
        exact (lstep_reg hs i).2.2.2.2 c rfl
    obtain ⟨p, hwp, hpa, hp, hfirst⟩ := first_ctl_after hwa ha
    have hpl : p < lbls.length := by omega
    have hnoproto : ∀ k, w + 1 ≤ k → k < p → ¬ ProtoOn lbls i k := fun k h1 h2 hpk =>
      hfirst k (by omega) h2 (ctlStep_of_proto hpk (hstab k (by omega) (by omega) hpk))
    have hgp : grantOf (σ p).2.1 i = some none := by
      rw [grant_const hr (by omega) (by omega) hnoproto (hex _ (by omega) (by omega))]
      exact hg1
    -- `p` is an `acquire` of `i`
    have hpacq : ∃ c, lbls[p]? = some (.acquire c i) := by
      obtain ⟨lbl, hlbl⟩ := hp.label
      have hpp := proto_of_ctlStep hp (hex p (by omega) (by omega))
      have hs := (hr p hpl).2
      rw [(List.getElem?_eq_some_iff.1 hlbl).2] at hs
      unfold ProtoOn at hpp; rw [hlbl] at hpp
      cases lbl with
      | acquire c j => cases hpp; exact ⟨c, hlbl⟩
      | unlock c j =>
        cases hpp
        obtain ⟨g, hg⟩ := ((lstep_reg hs i).2.2.2.1 c rfl).1
        rw [hgp] at hg; cases hg
      | resetLock c j =>
        cases hpp
        rcases Nat.lt_or_eq_of_le hpa with hlt | heq
        · exact absurd hlbl (hnoreset p (by omega) hlt c)
        · subst heq
          obtain ⟨c', hc'⟩ := hakind
          rw [hlbl] at hc'; cases hc'
      | _ => exact hpp.elim
    obtain ⟨cp, hpl'⟩ := hpacq
    obtain ⟨ep, hep⟩ := evOf p hp
    have hlast : LastCtl L σ lbls i x p w :=
      ⟨hw, hwp, fun w' hw' h => Decidable.byContradiction fun hn' =>
        hfirst w' (by omega) h hw'⟩
    have hsw : G.SW ew ep := by
      obtain ⟨hsu, hsr, -⟩ := acquire_sw hR h1 h3 hpl' hp hep hlast hew
      obtain ⟨c, hc | hc⟩ := hwkind
      · exact (hsu c i hc).1 ⟨hrel, hacq⟩
      · exact (hsr c i hc).1 ⟨hreset, hacq⟩
    have hup : G.HB eu ep := by
      rcases hrel_uw with rfl | h
      · exact .single (.inr hsw)
      · exact Relation.TransGen.tail h (.inr hsw)
    rcases Nat.lt_or_eq_of_le hpa with hlt | heq
    · obtain ⟨p', hpp', hp'a, ⟨cu, hcu⟩, hhb⟩ := hmid p (by omega) hlt ⟨cp, hpl'⟩
      have hpp'c : CtlStep L σ lbls i x p' := by
        have hpr : ProtoOn lbls i p' := by simp [ProtoOn, hcu]
        exact ctlStep_of_proto hpr (hstab p' (by omega) (by omega) hpr)
      obtain ⟨ep', hep'⟩ := evOf p' hpp'c
      exact ih (a - p') (by omega) p' rfl (by omega) hp'a hpp'c ⟨cu, .inl hcu⟩ eu ep' heu hep'
        (.inr (Relation.TransGen.trans hup (hhb ep ep' hep hep'))) ea hea
    · subst heq; rw [hea] at hep; cases hep; exact hup
  have main : ∀ eu ea, K.ev u = some eu → K.ev a = some ea → G.HB eu ea :=
    fun eu ea heu hea => claim (a - u) u rfl (Nat.le_refl _) hua hu hukind eu eu heu heu (.inl rfl)
      ea hea
  refine ⟨main, fun p hp j hj ep ej hpu haj hpreq hjreq hep hej => ?_⟩
  obtain ⟨eu, heu⟩ := evOf u hu
  obtain ⟨ea, hea⟩ := evOf a ha
  have hua' := main eu ea heu hea
  have h1' : G.HB ep ea := by
    rcases hK.po_or_eq hp (by omega) hpu hpreq hep heu with rfl | h
    · exact hua'
    · exact Relation.TransGen.trans (.single (.inl h)) hua'
  rcases hK.po_or_eq hal hj haj hjreq.symm hea hej with rfl | h
  · exact h1'
  · exact Relation.TransGen.tail h1' (.inl h)

/-- **Theorem 13e**, corollary: the condition on intermediate acquisitions holds by itself when
every intermediate `acquire` is followed, before `a`, by an `unlock` of the entry taken by the
context that took the lock: the `po` order of that context (K2) puts the event of the `unlock`
`hb`-after that of the `acquire` (C28, C33). -/
theorem mid_of_same_context (hK : Corresponds G σ lbls K) {u a : Nat}
    (hsame : ∀ p, u < p → p < a → (∃ c, lbls[p]? = some (.acquire c i)) →
      ∃ p', p < p' ∧ p' < a ∧ (∃ c, lbls[p']? = some (.unlock c i)) ∧
        ∀ (hp : p < lbls.length) (hp' : p' < lbls.length),
          lbls[p].requester = lbls[p'].requester) :
    ∀ p, u < p → p < a → (∃ c, lbls[p]? = some (.acquire c i)) →
      ∃ p', p < p' ∧ p' < a ∧ (∃ c, lbls[p']? = some (.unlock c i)) ∧
        ∀ ep ep', K.ev p = some ep → K.ev p' = some ep' → G.HB ep ep' := by
  intro p hup hpa hacq
  obtain ⟨p', hpp', hp'a, hun, hreq⟩ := hsame p hup hpa hacq
  refine ⟨p', hpp', hp'a, hun, fun ep ep' hep hep' => ?_⟩
  have hp : p < lbls.length := by
    obtain ⟨c, hc⟩ := hacq; exact (List.getElem?_eq_some_iff.1 hc).1
  have hp' : p' < lbls.length := by
    obtain ⟨c, hc⟩ := hun; exact (List.getElem?_eq_some_iff.1 hc).1
  exact .single (.inl (hK.po p p' hp hp' ep ep' hpp' (hreq hp hp') hep hep'))

/-- **Theorem 13f**, recovery (C48: "A later acquire-capable read/RMW which obtains its value from
this release publication ... acquires a justified `sw` edge from recovery"; C49: "Under the C48
protocol a successful `resetLock` publishes with `release`; when a subsequent `acquire` actually
reads that publication ..., `rf` and the selected memory orders establish `sw(resetLock, acquire)`";
"Any `sw` from the `release` recovery publication must be justified by actual `rf` and the chosen
memory orders"): when an `acquire` controller step `p` is the first protocol step on `i` after a
`resetLock` controller step `r`, its event reads the publication of `r`; under the reference
triple, `sw` relates them; with `o_reset = relaxed`, outside the reference, `rf` holds and the
atomic source of `sw` (C32.1) does not relate them. Realization R does not fix the `sync` attribute
of the events: that no `sw` edge at all relates them is not established. -/
theorem recovery_sw (hr : EncapRun ks L σ lbls) (hR : Realizes G L σ lbls K i x R v₀ v₁)
    (h1 : G.RfWF) (h3 : G.RmwAtomic) {r p cr cp : Nat} (hrp : r < p)
    (hrl : lbls[r]? = some (.resetLock cr i)) (hrc : CtlStep L σ lbls i x r)
    (hpl : lbls[p]? = some (.acquire cp i)) (hpc : CtlStep L σ lbls i x p)
    (hfirst : ∀ k, r < k → k < p → ¬ ProtoOn lbls i k) {er ep : E} (her : K.ev r = some er)
    (hep : K.ev p = some ep) :
    G.rf er ep ∧ (R = refOrders → G.SW er ep) ∧ (R.reset = .relaxed → ¬ AtomicSW G er ep) := by
  have hpl' : p < lbls.length := (List.getElem?_eq_some_iff.1 hpl).1
  have hir : i < (σ r).2.1.length := by
    unfold CtlStep at hrc; rw [hrl] at hrc
    obtain ⟨-, hctl⟩ := hrc
    unfold ctlOf at hctl
    cases he : (σ r).2.1[i]? with
    | none => rw [he] at hctl; cases hctl
    | some _ => exact (List.getElem?_eq_some_iff.1 he).1
  have hlast : LastCtl L σ lbls i x p r := by
    refine ⟨hrc, hrp, fun w' hw' h => Decidable.byContradiction fun hn => ?_⟩
    have hiw : i < (σ w').2.1.length :=
      Nat.lt_of_lt_of_le hir (encapRun_reg_mono hr (by omega) (by omega))
    exact hfirst w' (by omega) h (proto_of_ctlStep hw' hiw)
  have hrf := acquire_rf_last hR h1 h3 hpl hpc hep hlast her
  obtain ⟨-, hsr, -⟩ := acquire_sw hR h1 h3 hpl hpc hep hlast her
  refine ⟨hrf, fun e => (hsr cr i hrl).1 ⟨?_, ?_⟩, fun e hsw => ?_⟩
  · rw [e]; exact .inl rfl
  · rw [e]; exact .inl rfl
  · obtain ⟨ho, -⟩ := ((hsr cr i hrl).2).1 hsw
    rw [e] at ho
    rcases ho with h | h | h <;> cases h

end Order

end Ern.ConcurrencyModel
