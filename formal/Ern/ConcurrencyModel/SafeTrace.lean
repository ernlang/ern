import Ern.ConcurrencyModel.EventFinitePast
import Ern.ConcurrencyModel.WitnessExec

/-!
# Theorem 14: safe concurrent traces and the conditional composition theorem (C50–C52)

Theorem 14 of `formal/DESIGN.md`, Milestone 4, target theorems (`OB-C06`): lifetime ordering and
the conditional composition theorem, proven by cases on the conflicting pair.

* Definitions (C44–C47, C49–C52): the data of the access correspondence (`AccessData`), the
  validity events (`BeginOf`, `EndOf`), `LifetimeOrdered` (C51), the conflicting pairs of steps
  (`ConflictPair`) and their exclusivity (`ExclusivePair`), the ordered handoff of a pair under a
  criterion of C43 (`PairHandoff`), the agreement of the atomic event of a step with that step
  (`StepOrders`), the units of the events of steps (`UnitLeaf`), the conditions (a)–(f) of C51
  item 2 and `SafeConcurrentTrace`, the correspondence premises Q1–Q3 (C52) and Q4 (C26,
  `CorrQ4`), and the premise on the controller leaf (`CtlAtomic`).
* Under Q4 and `UnitLeaf` (C26, C29, C38): a step with a classified access to an `Atomic` leaf of
  nonzero size has an event that designates a unit of nonempty byte range (`atomic_covered`).
* 14a (C51): within one context `hb` and `po` coincide (`hb_iff_po`); ordering across distinct
  storage identities (`lifetime_reuse`).
* 14b (C51): a `SafeConcurrentTrace` is an `EncapsulatedTrace` (`SafeConcurrentTrace.encapsulated`);
  the converse fails (witnesses S1, S3–S8, `WitnessSafe`).
* 14c (C44, C52): the cases on a pair (`pair_atomic`, `pair_confined`, `pair_exclusive`,
  `pair_synchronized`, `pair_exhaustive`); under Q4, the two steps of a pair in conflict have
  events ordered by `hb` (14c.6, `pair_covered`).
* 14d (C52; `OB-C06`): no race, on fragment F (`no_race`).
* 14e (C48, C49; `OB-C04`): the edge of `LockOrder` under realization R, for an `acquire` whose
  controller is the unit of R (`lock_edge`, 14e.1) and for the whole entry under the stability of
  its controller leaf (`lock_edge_entry`, 14e.2).

Fragment F: `DDSound` (Spec 1 §80), well-formed statics (§47), an `EncapsulatedTrace` from the
initial state of §47 with named states (`EncapRun`), a graph `G` whose contexts are context
identities, and the partial correspondence K1–K4 (`Corresponds`): a condition on a pair of steps
concerns the pairs whose two steps have an event in `G`. The correspondence stays partial. The
provenance of lifecycle roles holds in both directions (K3, K4: a role is carried only by the event
of the step, or by the marker, that C28 names). The presence of an event for a step with a
classified access is the premise Q4 (`CorrQ4`), which is not the coverage of C29.

Formalization hypotheses (retained readings, not rules of the specification):

* complement of fragment F: the validity events are those of the graph of theorem 10; the
  correspondence does not say which step emits them;
* reading 9: the storage identity of each access event is data of the correspondence; an initial
  write (a write of `G` that is the event of no step) is the construction write of its storage;
* reading 10: the branch of C51 item 2(d) on the order by a synchronization mechanism is read as
  `hb` in one direction or the other (`SyncOrdered`);
* reading 11: the obligation `LockOrder` is its edge: when the event of an `acquire(e)` reads by
  `rf` the publication of an `unlock(e)` or a `resetLock(e)`, that publication is `hb`-before it;
  delegated grants are not covered;
* reading 14: an initial write (reading 9) with an event of a step `hb`-before it is not atomic:
  fragment F represents no atomic access outside the steps. A condition of the fragment, not a
  rule of C31, and not a proof that an initial write is the physical initial contents of its
  storage; an atomic access performed during the execution by a phase that is not a step is
  outside the fragment (`OB-C20`).

Readings 12 and 13 are stated by the specification:

* reading 12 (C48, first paragraph): `CtlAtomic`, which reads the class of the controller leaf at
  each `newMutex`, `acquire`, `unlock` or `resetLock` step, a premise of the statements that use it;
* reading 13 (C44, first paragraph): `ExclusivePair`, which takes the `Modify` criterion of C43
  (`IncompatModify`) and, for the second access of the pair, `usedMode` (C45). In
  `SafeConcurrentTrace`, `ExclusivePair` restricts `HandoffOrdered` (leaves that are not
  `Confined`) and `SyncOrdered` (`Synchronized` leaves); the pairs on a `Confined` leaf are under
  `ConfinedHandoff`, with the `Confined` criterion.
-/

namespace Ern.ConcurrencyModel

open Ern.MemoryModel Ern.MemoryModel.Access Events

variable {pm : ProviderMeta}

/-! ## Validity events (C27) -/

namespace Events.Graph

variable {E C U V S : Type} (G : Graph E C U V S)

/-- `v` is a begin-validity event of the storage identity `x` (C27 `validity`). -/
def BeginOf (v : E) (x : S) : Prop := (G.ev v).attrs = .validity ⟨true, x⟩

/-- `v` is an end-validity event of the storage identity `x` (C27 `validity`). -/
def EndOf (v : E) (x : S) : Prop := (G.ev v).attrs = .validity ⟨false, x⟩

end Events.Graph

/-! ## The data of the access correspondence (reading 9) -/

/-- The data of the access correspondence (reading 9; C27, C29, C31, C50): the storage identity of
each access event (`sid`, read on access events only), and the initial writes (`init`): writes of
`G` that are the event of no step. A represented initial write is the construction write of its
storage (C31; C51). An initial write that an event of a step precedes by `hb` is not atomic, a
condition of fragment F (reading 14, `init_origin`). Exported obligation `OB-C12` (C25, C50), stated
part. The obligation is exported and remains open (`ExportedObligations`). -/
structure AccessData {E U V S : Type} (G : Events.Graph E Nat U V S) (lbls : List Label)
    (K : StepEvents E) where
  sid : E → S
  init : E → Bool
  init_writes : ∀ e, init e = true → G.Writes e
  init_unstepped : ∀ e, init e = true → ∀ i, i < lbls.length → K.ev i ≠ some e
  /-- Provenance of an initial write, as a condition of fragment F (reading 14; C31). Either no
  event of a step is `hb`-before it, which the fragment requires of initial contents of a storage;
  or it is not atomic: fragment F represents no atomic access outside the steps. The condition does
  not prove that an initial write is the physical initial contents of its storage: that provenance
  remains an open obligation (`OB-C12`, `OB-C20`). -/
  init_origin : ∀ w, init w = true → (∀ i d, K.ev i = some d → ¬ G.HB d w) ∨ ¬ G.Atomic w

/-! ## `LifetimeOrdered` (C51) -/

section Lifetime

variable {E U V S : Type} {G : Events.Graph E Nat U V S} {lbls : List Label} {K : StepEvents E}

/-- `LifetimeOrdered` (C51), on the graph and the data of reading 9, with `hb` in both cases (within
one context, `hb` is `po` under conjunct 5: `hb_iff_po`):

* L1: every access to `x` is `hb`-after every begin-validity event of `x`;
* L2: every access to `x` is `hb`-before every end-validity event of `x`;
* L3: an initial write of `x` is `hb`-before every access to `x` of another context. -/
structure LifetimeOrdered (G : Events.Graph E Nat U V S) (D : AccessData G lbls K) : Prop where
  /-- L1. -/
  after_begin : ∀ a v, G.IsAcc a → G.BeginOf v (D.sid a) → G.HB v a
  /-- L2. -/
  before_end : ∀ a v, G.IsAcc a → G.EndOf v (D.sid a) → G.HB a v
  /-- L3. -/
  init_first : ∀ w a, D.init w = true → G.IsAcc a → D.sid a = D.sid w → G.ctx a ≠ G.ctx w →
    G.HB w a

end Lifetime

/-! ## Pairs of steps (C30, C43–C46) -/

/-- The context of step `i` (C26 item 3), `0` past the end of the trace. -/
def ctxAt (lbls : List Label) (i : Nat) : Nat := ((lbls[i]?).map Label.requester).getD 0

/-- The context of a step of the trace is the requester of its label. -/
theorem ctxAt_eq {lbls : List Label} {i : Nat} (h : i < lbls.length) :
    ctxAt lbls i = lbls[i].requester := by
  simp [ctxAt, List.getElem?_eq_getElem h]

/-- Step `i` accesses `x` in the sense of 11e (C36, C38, C39; C13.11, C48): `x` is one of the
classified accesses of the step. -/
def StepAccess (ks : KShared) (L : MutexLayout) (R : CtlOrders) (σ : Nat → SC × SyncReg × ArenaReg)
    (lbls : List Label) (i : Nat) (x : LeafAccess) : Prop :=
  ∃ h : i < lbls.length, ∃ acc, classify ks L R (σ i) lbls[i] = some acc ∧ x ∈ acc

/-- A pair in conflict (C30, C33, C44): steps `i < j` of distinct contexts accessing the same leaf
in the sense of 11e, through the accesses `x` and `y`, at least one of which writes and at least
one of which is non-atomic. -/
structure ConflictPair (ks : KShared) (L : MutexLayout) (R : CtlOrders)
    (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) (i j : Nat) (x y : LeafAccess) :
    Prop where
  lt : i < j
  left : StepAccess ks L R σ lbls i x
  right : StepAccess ks L R σ lbls j y
  leaf : x.leaf = y.leaf
  ctx : ctxAt lbls i ≠ ctxAt lbls j
  writes : x.kind.Writes ∨ y.kind.Writes
  nonatomic : x.order = none ∨ y.order = none

/-- Step `k` uses `Modify` for its access `x` in the sense of 12e (`UsesModify`; C42, C44). -/
def UsesModifyAt (ks : KShared) (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) (k : Nat)
    (x : LeafAccess) : Prop :=
  ∃ h : k < lbls.length, UsesModify ks (σ k) lbls[k] x

/-- The label is a `read3` (O9). -/
def IsRead3 : Label → Bool
  | .kernel _ (.read _ _) => true
  | _ => false

/-- `IsRead3` decides the `read3` labels of `UsesModify`. -/
theorem isRead3_iff (lbl : Label) : (∃ c a ls, lbl = .kernel c (.read a ls)) ↔ IsRead3 lbl = true := by
  constructor
  · rintro ⟨c, a, ls, rfl⟩; rfl
  · intro h
    cases lbl with
    | kernel c op => cases op <;> first | exact ⟨_, _, _, rfl⟩ | cases h
    | _ => cases h

instance (ks : KShared) (s : SC) (lbl : Label) : Decidable (AtomicOrdinaryOK ks s lbl) := by
  cases lbl with
  | kernel c op => cases op <;> unfold AtomicOrdinaryOK <;> infer_instance
  | _ => unfold AtomicOrdinaryOK; infer_instance

instance (ks : KShared) (st : SC × SyncReg × ArenaReg) (lbl : Label) (x : LeafAccess) :
    Decidable (UsesModify ks st lbl x) :=
  decidable_of_iff (x.mode = .modify ∨
      (AtomicLeaf ks x.leaf ∧ IsRead3 lbl = true ∧ AtomicOrdinaryOK ks st.1 lbl))
    (by unfold UsesModify; rw [isRead3_iff])

instance (ks : KShared) (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) (k : Nat)
    (x : LeafAccess) : Decidable (UsesModifyAt ks σ lbls k x) :=
  if h : k < lbls.length then
    decidable_of_iff (UsesModify ks (σ k) lbls[k] x) ⟨fun h' => ⟨h, h'⟩, fun ⟨_, h'⟩ => h'⟩
  else isFalse fun ⟨h', _⟩ => h h'

/-- The mode used by the access `y` of step `j` (C45; 12e): `Modify` when the step uses `Modify` for
it (`UsesModify`, including the `read3` of an `Atomic` leaf under the rule of C42), otherwise the
mode its authority requires. -/
def usedMode (ks : KShared) (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) (j : Nat)
    (y : LeafAccess) : Mode :=
  if UsesModifyAt ks σ lbls j y then .modify else y.mode

/-- The pair of the access `x` of step `i` and the access `y` of step `j` is exclusive (C44; C45;
reading 13): the capability of the context of step `i` on the leaf of `x`, in the state of step `i`,
is incompatible under the `Modify` criterion of C43 (`IncompatModify`) with the mode used by `y`
(`usedMode`). The capability of the context of step `j` is not compared. -/
def ExclusivePair (ks : KShared) (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label)
    (i j : Nat) (x y : LeafAccess) : Prop :=
  IncompatModify (cap (σ i).1 (σ i).2.1 (ctxAt lbls i) x.leaf) (usedMode ks σ lbls j y)

instance {Inc : Option Mode → Mode → Prop} [∀ v m, Decidable (Inc v m)]
    (σ : Nat → SC × SyncReg × ArenaReg) (i c' l : Nat) (m : Mode) (r : Nat) :
    Decidable (FirstCompatible Inc σ i c' l m r) :=
  decidable_of_iff (i ≤ r ∧ ¬ Inc (cap (σ (r + 1)).1 (σ (r + 1)).2.1 c' l) m ∧
      ∀ k, k < r + 1 - i → Inc (cap (σ (i + k)).1 (σ (i + k)).2.1 c' l) m) (by
    unfold FirstCompatible
    refine and_congr_right fun hir => and_congr_right fun _ => ⟨fun h k hk1 hk2 => ?_,
      fun h k hk => h (i + k) (by omega) (by omega)⟩
    have := h (k - i) (by omega)
    rwa [Nat.add_sub_cancel' hk1] at this)

/-- The ordered handoff of the pair `(i, x)`, `(j, y)` under the criterion `Inc` of C43 (`Modify` or
`Confined`) (C45, C46; position of 12d): for the events `a` of step `i` and `d` of step `j`, there
is a first step `r`, `i ≤ r < j`, at the end of which the capability on the leaf of the context of
step `i` is compatible, under `Inc`, with the mode used by step `j`; step `r` has an event `b`; and
`hb(b, d)`. The existence of the marker is part of the obligation (C46). -/
def PairHandoff (Inc : Option Mode → Mode → Prop) {E U V S : Type} (ks : KShared)
    (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) (G : Events.Graph E Nat U V S)
    (K : StepEvents E) (i j : Nat) (x y : LeafAccess) : Prop :=
  ∀ a d, K.ev i = some a → K.ev j = some d →
    ∃ r, r < j ∧ FirstCompatible Inc σ i (ctxAt lbls i) x.leaf (usedMode ks σ lbls j y) r ∧
      ∃ b, K.ev r = some b ∧ G.HB b d

/-! ## `SafeConcurrentTrace` (C51 item 2) -/

/-- The leaf has the class `Confined` (C35). -/
def ConfinedLeaf (ks : KShared) (l : Nat) : Prop := ks.SharedDiscipline l = some .confined

/-- The leaf has the class `Synchronized` (C35). -/
def SyncLeaf (ks : KShared) (l : Nat) : Prop := ks.SharedDiscipline l = some .synchronized

instance (ks : KShared) (l : Nat) : Decidable (ConfinedLeaf ks l) := by
  unfold ConfinedLeaf; infer_instance

instance (ks : KShared) (l : Nat) : Decidable (SyncLeaf ks l) := by
  unfold SyncLeaf; infer_instance

/-- The atomic event of a step carries the kind and the memory order of an atomic access of that
step in the sense of 11e (`StepAccess`) (C37, for `readShared(access, leaf, order)`; C39; C40).
Under 11e the controller accesses of `acquire`, `unlock` and `resetLock` carry the orders of `R`.
Exported obligation `OB-C20` (C27–C29, C50), stated part: the kind and the memory order of the
atomic event of a step. The obligation is exported and remains open (`ExportedObligations`). The
condition relates neither leaves to units, which is the condition `UnitLeaf`, nor byte ranges, and
says nothing of an event that is the event of no step, of the accesses of compound steps or of
failed attempts. -/
def StepOrders {E U V S : Type} (ks : KShared) (L : MutexLayout) (R : CtlOrders)
    (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) (G : Events.Graph E Nat U V S)
    (K : StepEvents E) : Prop :=
  ∀ i e, K.ev i = some e → ∀ u o k, G.acc? e = some (.atomic u o k) →
    ∃ x, StepAccess ks L R σ lbls i x ∧ x.order = some o ∧ x.kind = k.kind

/-- The units of the events of steps (C38, C31, C32 item 1). The units are those of the `Atomic`
leaves of nonzero size (reading 6). No map from units to leaves is given: the conditions relate the
events of two steps. Exported obligation `OB-C20` (C27–C29, C50), stated part: the unit of the
events of steps. The obligation is exported and remains open (`ExportedObligations`). The condition
says nothing of the placement of the byte range of a unit, of the byte ranges of the accesses that
designate no unit, or of an event that is the event of no step. -/
structure UnitLeaf {E U V S : Type} (ks : KShared) (L : MutexLayout) (R : CtlOrders)
    (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) (G : Events.Graph E Nat U V S)
    (K : StepEvents E) : Prop where
  /-- Two events of steps that designate one unit are events of steps that access one `Atomic`
  leaf of nonzero size. -/
  leaf : ∀ i j a d u, K.ev i = some a → K.ev j = some d → G.unitOf a = some u →
    G.unitOf d = some u →
    ∃ x y, StepAccess ks L R σ lbls i x ∧ StepAccess ks L R σ lbls j y ∧ x.leaf = y.leaf ∧
      AtomicLeaf ks x.leaf ∧ ¬ ZeroAtomic ks x.leaf
  /-- Two events of steps that access one `Atomic` leaf of nonzero size designate one unit. -/
  unit : ∀ i j a d x y, K.ev i = some a → K.ev j = some d → StepAccess ks L R σ lbls i x →
    StepAccess ks L R σ lbls j y → x.leaf = y.leaf → AtomicLeaf ks x.leaf →
    ¬ ZeroAtomic ks x.leaf → ∃ u, G.unitOf a = some u ∧ G.unitOf d = some u
  /-- The unit that the event of a step designates has a nonempty byte range. -/
  range : ∀ i a u, K.ev i = some a → G.unitOf a = some u → (G.uRange u).len ≠ 0

/-- C51 item 2(b), with C42: every `read3` and `write3` step satisfies the rule of 11f. -/
def OrdinaryAtomicOK (ks : KShared) (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) :
    Prop :=
  ∀ i (h : i < lbls.length), AtomicOrdinaryOK ks (σ i).1 lbls[i]

/-- C51 item 2(c), first part, with C35: at every state of the execution, at most one context has
a present capability (C43, guarded-chain-excluding) on a `Confined` leaf. -/
def ConfinedExcl (ks : KShared) (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) : Prop :=
  ∀ k, k ≤ lbls.length → ∀ l, ConfinedLeaf ks l → ∀ d d', d ≠ d' →
    cap (σ k).1 (σ k).2.1 d l ≠ none → cap (σ k).1 (σ k).2.1 d' l = none

/-- C51 item 2(c), second part, with C43 and C46: every pair in conflict on a `Confined` leaf has
its handoff ordered under the `Confined` criterion. -/
def ConfinedHandoff {E U V S : Type} (ks : KShared) (L : MutexLayout) (R : CtlOrders)
    (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) (G : Events.Graph E Nat U V S)
    (K : StepEvents E) : Prop :=
  ∀ i j x y, ConflictPair ks L R σ lbls i j x y → ConfinedLeaf ks x.leaf →
    PairHandoff IncompatConfined ks σ lbls G K i j x y

/-- C51 item 2(d), with C44 and C52 (reading 10): for every non-exclusive pair in conflict on a
`Synchronized` leaf, the events of the two steps are ordered by `hb` in one direction or the
other. -/
def SyncOrdered {E U V S : Type} (ks : KShared) (L : MutexLayout) (R : CtlOrders)
    (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) (G : Events.Graph E Nat U V S)
    (K : StepEvents E) : Prop :=
  ∀ i j x y, ConflictPair ks L R σ lbls i j x y → ¬ ExclusivePair ks σ lbls i j x y →
    SyncLeaf ks x.leaf → ∀ a d, K.ev i = some a → K.ev j = some d → G.HB a d ∨ G.HB d a

/-- C51 item 2(e) on one step, with C35–C40: an inherited `writeShared` (label `kernel`) satisfies
the legality table of 11a for the kind `store` without annotation. -/
def InheritedOK (ks : KShared) : Label → Prop
  | .kernel _ (.writeShared _ ls) => WriteDisciplineOK ks ls none .store
  | _ => True

instance (ks : KShared) (lbl : Label) : Decidable (InheritedOK ks lbl) := by
  cases lbl with
  | kernel c op => cases op <;> unfold InheritedOK <;> infer_instance
  | _ => unfold InheritedOK; infer_instance

/-- C51 item 2(e): every inherited `writeShared` step satisfies the table (`InheritedOK`). -/
def InheritedLegal (ks : KShared) (lbls : List Label) : Prop :=
  ∀ i (h : i < lbls.length), InheritedOK ks lbls[i]

/-- `HandoffOrdered` (C44–C46; C51 item 2(f)): every exclusive pair in conflict on a leaf that is
not `Confined` has its handoff ordered under the `Modify` criterion. -/
def HandoffOrdered {E U V S : Type} (ks : KShared) (L : MutexLayout) (R : CtlOrders)
    (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) (G : Events.Graph E Nat U V S)
    (K : StepEvents E) : Prop :=
  ∀ i j x y, ConflictPair ks L R σ lbls i j x y → ExclusivePair ks σ lbls i j x y →
    ¬ ConfinedLeaf ks x.leaf → PairHandoff IncompatModify ks σ lbls G K i j x y

/-- The lifecycle conditions (C47; C51 item 2(f)): K3 and K4 of the correspondence, in both
directions (C28, C32.2, C32.3). Exported obligation `OB-C20` (C27–C29, C50), stated part: the
correspondence of the events of steps and of the lifecycle markers. The obligation is exported and
remains open (`ExportedObligations`). -/
structure LifecycleOK {E U V S : Type} (G : Events.Graph E Nat U V S)
    (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) (K : StepEvents E) : Prop where
  /-- K3. -/
  spawnRole : ∀ s c, Creates σ lbls s c → ∀ e, K.ev s = some e → G.sync? e = some (.spawn c)
  /-- K3. -/
  start : ∀ c x, K.start c = some x → G.ctx x = c ∧ G.sync? x = some (.start c) ∧
    ∀ j (h : j < lbls.length) d, lbls[j].requester = c → K.ev j = some d → G.po x d
  /-- K4. -/
  complete : ∀ c x, K.complete c = some x → G.ctx x = c ∧ G.sync? x = some (.complete c) ∧
    ∀ j (h : j < lbls.length) d, lbls[j].requester = c → K.ev j = some d → G.po d x
  /-- K4. -/
  joinRole : ∀ q (h : q < lbls.length) c d e, lbls[q] = .join c d → K.ev q = some e →
    G.sync? e = some (.join d)
  /-- K3, provenance. -/
  spawnFrom : ∀ e c, G.sync? e = some (.spawn c) → ∃ s, Creates σ lbls s c ∧ K.ev s = some e
  /-- K3, provenance. -/
  startFrom : ∀ e c, G.sync? e = some (.start c) → K.start c = some e ∧ ∃ s, Creates σ lbls s c
  /-- K4, provenance. -/
  completeFrom : ∀ e c, G.sync? e = some (.complete c) →
    K.complete c = some e ∧ ∃ t, ∃ h : t < lbls.length, lbls[t] = .terminate c
  /-- K4, provenance. -/
  joinFrom : ∀ e d, G.sync? e = some (.join d) →
    ∃ q, ∃ h : q < lbls.length, ∃ c, lbls[q] = .join c d ∧ K.ev q = some e

/-- The correspondence gives the lifecycle conditions. -/
theorem Corresponds.lifecycle {E U V S : Type} {G : Events.Graph E Nat U V S}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} {K : StepEvents E}
    (h : Corresponds G σ lbls K) : LifecycleOK G σ lbls K :=
  ⟨h.spawnRole, h.start, h.complete, h.joinRole, h.spawnFrom, h.startFrom, h.completeFrom,
    h.joinFrom⟩

/-- Step `p` is an `unlock(e)` or a `resetLock(e)` (C17, C18). -/
def PubOn (lbls : List Label) (e p : Nat) : Prop :=
  ∃ c, lbls[p]? = some (.unlock c e) ∨ lbls[p]? = some (.resetLock c e)

/-- Step `q` is an `acquire(e)` (C16). -/
def AcqOn (lbls : List Label) (e q : Nat) : Prop := ∃ c, lbls[q]? = some (.acquire c e)

/-- The edge of `LockOrder` (reading 11; C49, C48, C51 item 2(f)): when the event of an
`acquire(e)` reads by `rf` the event of an `unlock(e)` or a `resetLock(e)` (its publication), that
publication is `hb`-before it. -/
def LockEdge {E U V S : Type} (G : Events.Graph E Nat U V S) (lbls : List Label)
    (K : StepEvents E) : Prop :=
  ∀ e p q, PubOn lbls e p → AcqOn lbls e q → ∀ b d, K.ev p = some b → K.ev q = some d →
    G.rf b d → G.HB b d

/-- `SafeConcurrentTrace` (C51 item 2), on the execution `(σ, lbls)`, the graph `G`, the
correspondence `K` and the data `D` of reading 9: the execution is an `EncapsulatedTrace`
(`EncapRun`), and

* (a) (C26.4, C34): `EventConsistent(G)` and a finite causal past;
* (b) (C37–C42; C34, last sentence): `OrdinaryAtomicOK` (C42), the legality of the memory orders
  of the events, `OrderLegal` (C40), the agreement of the atomic event of each step with that
  step, `StepOrders` (C37, C39, C40), and the units of the events of steps, `UnitLeaf` (C38);
* (c) (C35, C43, C46): `ConfinedExcl` and `ConfinedHandoff`;
* (d) (C44, C52): `SyncOrdered`;
* (e) (C35–C40): `InheritedLegal`;
* (f) (C44–C47, C49, C51): `HandoffOrdered`, `LifetimeOrdered`, the lifecycle conditions K3 and K4,
  the edge of `LockOrder`.

Exported obligation `OB-C24` (C51, C52), stated part (`ExportedObligations`): a property of
executions; it does not establish that programs accepted as safe and safe libraries produce only
such executions. The obligation is exported and remains open. -/
structure SafeConcurrentTrace {E U V S : Type} (pm : ProviderMeta) (ks : KShared) (L : MutexLayout)
    (R : CtlOrders) (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label)
    (G : Events.Graph E Nat U V S)
    (K : StepEvents E) (D : AccessData G lbls K) : Prop where
  run : EncapRun pm ks L σ lbls
  /-- (a). -/
  consistent : G.EventConsistent
  /-- (a). -/
  finitePast : G.FiniteCausalPast
  /-- (b). -/
  ordinary : OrdinaryAtomicOK ks σ lbls
  /-- (b) (C40; C34, last sentence). -/
  orderLegal : G.OrderLegal
  /-- (b) (C37, C39, C40). -/
  stepOrders : StepOrders ks L R σ lbls G K
  /-- (b) (C38; C51 item 2(b)). -/
  unitLeaf : UnitLeaf ks L R σ lbls G K
  /-- (c). -/
  confinedExcl : ConfinedExcl ks σ lbls
  /-- (c). -/
  confinedHandoff : ConfinedHandoff ks L R σ lbls G K
  /-- (d). -/
  synchronized : SyncOrdered ks L R σ lbls G K
  /-- (e). -/
  inherited : InheritedLegal ks lbls
  /-- (f). -/
  handoff : HandoffOrdered ks L R σ lbls G K
  /-- (f). -/
  lifetime : LifetimeOrdered G D
  /-- (f). -/
  lifecycle : LifecycleOK G σ lbls K
  /-- (f). -/
  lockOrder : LockEdge G lbls K

/-! ## Correspondence premises (C52) and the controller leaf (reading 12) -/

/-- The event `e` carries the kind and the atomicity that 11e gives to the access `x` (C30, C38,
C50). -/
def AccTyped {E C U V S : Type} (G : Events.Graph E C U V S) (e : E) (x : LeafAccess) : Prop :=
  G.kind? e = some x.kind ∧ (G.Atomic e ↔ x.order.isSome = true)

/-- Q1 (C29, C31; `OB-C20`): every event of `G` that carries an access is the event of a step, or an
initial write. Exported obligation `OB-C20` (C27–C29, C50), stated part. The obligation is exported
and remains open (`ExportedObligations`). -/
def CorrQ1 {E U V S : Type} (G : Events.Graph E Nat U V S) (lbls : List Label) (K : StepEvents E)
    (D : AccessData G lbls K) : Prop :=
  ∀ e, G.IsAcc e → (∃ i, i < lbls.length ∧ K.ev i = some e) ∨ D.init e = true

/-- Q2 (C30, C38, C50; `OB-C12`, `OB-C20`): when the events `a`, `d` of two steps conflict (C30)
and have the same storage identity, there is a leaf that both steps access in the sense of 11e,
and each event carries the kind and atomicity that 11e gives to its step on that leaf. Exported
obligations `OB-C12` (C25, C50) and `OB-C20` (C27–C29, C50), stated parts. Both are exported and
remain open (`ExportedObligations`). -/
def CorrQ2 {E U V S : Type} (ks : KShared) (L : MutexLayout) (R : CtlOrders)
    (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) (G : Events.Graph E Nat U V S)
    (K : StepEvents E) (D : AccessData G lbls K) : Prop :=
  ∀ i j a d, K.ev i = some a → K.ev j = some d → G.Conflict a d → D.sid a = D.sid d →
    ∃ x y, StepAccess ks L R σ lbls i x ∧ StepAccess ks L R σ lbls j y ∧ x.leaf = y.leaf ∧
      AccTyped G a x ∧ AccTyped G d y

/-- Q3 (C51; C50; `OB-C12`): when two conflicting access events have distinct storage identities, an
end-validity event of one is `hb`-before a begin-validity event of the other. Exported obligation
`OB-C12` (C25, C50), stated part. The obligation is exported and remains open
(`ExportedObligations`). -/
def CorrQ3 {E U V S : Type} {G : Events.Graph E Nat U V S} {lbls : List Label}
    {K : StepEvents E} (D : AccessData G lbls K) : Prop :=
  ∀ a d, G.Conflict a d → D.sid a ≠ D.sid d →
    (∃ v w, G.EndOf v (D.sid a) ∧ G.BeginOf w (D.sid d) ∧ G.HB v w) ∨
    (∃ v w, G.EndOf v (D.sid d) ∧ G.BeginOf w (D.sid a) ∧ G.HB v w)

/-- Q4 (C26), at the grain of 11e: a step with a classified access has an event. This is the
presence of an event, not the coverage of C29: Q4 does not say that the event carries an access, and
says nothing of byte footprints, of the accesses of compound steps or of failed attempts. Exported
obligation `OB-C20` (C27–C29, C50), stated part: the presence of an event for a step with a
classified access. The coverage of C29 is another part of `OB-C20`, documented only. The obligation
is exported and remains open (`ExportedObligations`). A correspondence premise, not a condition of
the safe trace (C51 item 2). -/
def CorrQ4 {E : Type} (ks : KShared) (L : MutexLayout) (R : CtlOrders)
    (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) (K : StepEvents E) : Prop :=
  ∀ i x, StepAccess ks L R σ lbls i x → ∃ e, K.ev i = some e

/-- Under Q4 and `UnitLeaf`, a step with a classified access to an `Atomic` leaf of nonzero size has
an event that designates a unit of nonempty byte range: an `acc` event (C29, C38). For these
accesses the model has the information that a byte access exists; for the other leaves the physical
size is not represented (C38). The statement does not say that the event is atomic when the access
is, and is not the coverage of C29. -/
theorem atomic_covered {E U V S : Type} {ks : KShared} {L : MutexLayout} {R : CtlOrders}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} {G : Events.Graph E Nat U V S}
    {K : StepEvents E} (hq4 : CorrQ4 ks L R σ lbls K) (hu : UnitLeaf ks L R σ lbls G K) {i : Nat}
    {x : LeafAccess} (hx : StepAccess ks L R σ lbls i x) (hat : AtomicLeaf ks x.leaf)
    (hnz : ¬ ZeroAtomic ks x.leaf) :
    ∃ e u, K.ev i = some e ∧ G.unitOf e = some u ∧ (G.uRange u).len ≠ 0 := by
  obtain ⟨e, he⟩ := hq4 i x hx
  obtain ⟨u, hu1, -⟩ := hu.unit i i e e x x he he hx hx rfl hat hnz
  exact ⟨e, u, he, hu1, hu.range i e u he hu1⟩

/-- The controller leaf of a `newMutex`, `acquire`, `unlock` or `resetLock` step (C12, C13, C48). -/
def ctlLeafAt (L : MutexLayout) (st : SC × SyncReg × ArenaReg) : Label → Option Nat
  | .newMutex _ g => ControlOf L st.1 ⟨g, none⟩
  | .acquire _ i | .unlock _ i | .resetLock _ i => ctlOf L st i
  | _ => none

/-- Reading 12 (C48, first paragraph; C35, C38): at every `newMutex`, `acquire`, `unlock` or
`resetLock` step, the controller leaf has the class `Atomic(size, align)` with `size ≠ 0`. A premise
of the statements that use it: `NewMutexPre` does not require it. -/
def CtlAtomic (ks : KShared) (L : MutexLayout) (σ : Nat → SC × SyncReg × ArenaReg)
    (lbls : List Label) : Prop :=
  ∀ k (h : k < lbls.length) ctl, ctlLeafAt L (σ k) lbls[k] = some ctl →
    ∃ sz al, ks.SharedDiscipline ctl = some (.atomic sz al) ∧ sz ≠ 0

/-! ## The legality of the atomic steps, (b) and (e) (11a–11c) -/

/-- **Theorem 14**, first fact (C37–C40; 11a–11c): an `ok` atomic step obeys its legality rules: a
`readShared` reads an `Atomic` leaf of nonzero size with an order of the load row; a
compare-and-exchange has its orders in their rows and targets an `Atomic` leaf of nonzero size.
Hence no condition of (b) is needed for the legality of the atomic steps themselves; among the
steps, (b) constrains `read3` and `write3` (`OrdinaryAtomicOK`), and it constrains the events of
the graph by `OrderLegal` and `StepOrders`. Obligation: `OB-C03`. -/
theorem atomic_steps_legal {ks : KShared} {L : MutexLayout} {lbl : Label}
    {st st' : SC × SyncReg × ArenaReg} (h : LStep ks L lbl st st') :
    (∀ c a l o v, lbl = .readShared c a l o v →
      (∃ sz al, ks.SharedDiscipline l = some (.atomic sz al)) ∧ ¬ ZeroAtomic ks l ∧
        LoadOrderOK o) ∧
    (∀ c a l succ fail br, lbl = .cas c a l succ fail br →
      CasOrdersOK succ fail ∧ (∃ sz al, ks.SharedDiscipline l = some (.atomic sz al)) ∧
        ¬ ZeroAtomic ks l) := by
  refine ⟨fun c a l o v e => ?_, fun c a l succ fail br e => ?_⟩
  · subst e
    cases h with
    | readShared hr =>
      have hp := (Guarded.ok_iff.1 hr).1
      exact ⟨hp.atomic, hp.nonzero, hp.order⟩
  · subst e
    cases h with
    | cas hc =>
      obtain (⟨-, h⟩ | ⟨ho, h⟩) := hc
      · cases h
      · refine ⟨ho, ?_⟩
        cases br with
        | success v =>
          obtain ⟨l', sz, al, hl, hd, hsz, -⟩ := (Guarded.ok_iff.1 h).1.discipline
          cases hl
          exact ⟨⟨sz, al, hd⟩, fun ⟨al', h'⟩ => hsz (by rw [hd] at h'; cases h'; rfl)⟩
        | failure v =>
          have hp := (Guarded.ok_iff.1 h).1
          exact ⟨hp.atomic, hp.nonzero⟩

/-- **Theorem 14**, second fact (C35, C38–C40; 11a): every `ok` concurrent `writeShared` satisfies
the legality table of its region, kind and annotation. Hence (e) constrains only the inherited
steps. Obligation: `OB-C03`. -/
theorem writeShared_legal {ks : KShared} {L : MutexLayout} {c a : Nat} {region : List Nat}
    {ord : Option MemOrder} {kind : WriteKind} {st st' : SC × SyncReg × ArenaReg}
    (h : LStep ks L (.writeShared c a region ord kind) st st') :
    WriteDisciplineOK ks region ord kind := by
  cases h with
  | writeShared hw => exact (Guarded.ok_iff.1 hw).1.discipline

/-! ## 14a: lifetime ordering (C51) -/

/-- **Theorem 14a.1** (C51; C33): under conjunct 5 of `EventConsistent`, for two events of the same
context, `hb` and `po` coincide. -/
theorem hb_iff_po {E C U V S : Type} {G : Events.Graph E C U V S} (h5 : G.HbIrrefl) {a b : E}
    (hc : G.ctx a = G.ctx b) : G.HB a b ↔ G.po a b := by
  refine ⟨fun h => ?_, hb_of_po⟩
  have hne : a ≠ b := fun e => by subst e; exact h5 a h
  rcases G.po_total hc hne with hp | hp
  · exact hp
  · exact absurd (Relation.TransGen.tail h (.inl hp)) (h5 a)

/-- **Theorem 14a.2** (C51): under `LifetimeOrdered`, if an end-validity event of `x` is `hb`-before
a begin-validity event of `y`, every access to `x` is `hb`-before every access to `y`. -/
theorem lifetime_reuse {E U V S : Type} {G : Events.Graph E Nat U V S} {lbls : List Label}
    {K : StepEvents E} {D : AccessData G lbls K} (hL : LifetimeOrdered G D) {x y : S} {v w : E}
    (hv : G.EndOf v x) (hw : G.BeginOf w y) (hvw : G.HB v w) {a b : E} (ha : G.IsAcc a)
    (hax : D.sid a = x) (hb : G.IsAcc b) (hby : D.sid b = y) : G.HB a b := by
  subst hax hby
  exact (hL.before_end a v ha hv).trans (hvw.trans (hL.after_begin b w hb hw))

/-! ## 14b: a contract, not the set of `ok` traces (C51) -/

/-- **Theorem 14b** (C51): every `SafeConcurrentTrace` is an `EncapsulatedTrace` from its first
state. The converse is false (C51): witnesses S1 and S3–S8 (`WitnessSafe`). -/
theorem SafeConcurrentTrace.encapsulated {E U V S : Type} {ks : KShared} {L : MutexLayout}
    {R : CtlOrders} {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label}
    {G : Events.Graph E Nat U V S} {K : StepEvents E} {D : AccessData G lbls K}
    (h : SafeConcurrentTrace pm ks L R σ lbls G K D) :
    EncapsulatedTrace pm ks L (σ 0) lbls (σ lbls.length) :=
  trace_of_run h.run

/-! ## 14c: cases on the pair (C44, C52) -/

section Pairs

variable {ks : KShared} {L : MutexLayout} {R : CtlOrders} {statics : Statics}
  {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} {E U V S : Type}
  {G : Events.Graph E Nat U V S} {K : StepEvents E}

/-- The invariants of theorem 2 at every state of the execution. -/
theorem run_inv (hdd : DDSound ks.toK) (hst : StaticsOK statics)
    (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], [])) (hr : EncapRun pm ks L σ lbls) {k : Nat}
    (hk : k ≤ lbls.length) : KInvCA (σ k).1 := by
  obtain ⟨pre, hpre⟩ := encapRun_reach hr k hk
  rw [h0] at hpre
  exact (encapsulated_inv hdd hst hpre).1

/-- The access of a step is covered by the capability of its context (12a, `cap_covers`). -/
theorem cap_of_access (hdd : DDSound ks.toK) (hst : StaticsOK statics)
    (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], [])) (hr : EncapRun pm ks L σ lbls) {i : Nat}
    {x : LeafAccess} (hx : StepAccess ks L R σ lbls i x) :
    Allows (cap (σ i).1 (σ i).2.1 (ctxAt lbls i) x.leaf) x.mode := by
  obtain ⟨hi, acc, hc, hxa⟩ := hx
  obtain ⟨he, hs⟩ := hr i hi
  rw [ctxAt_eq hi]
  exact cap_covers (run_inv hdd hst h0 hr (Nat.le_of_lt hi)).1.1.1 he hs hc x hxa

/-- An access whose step uses `Modify` is covered by a `Modify` capability (`cap_of_usesModify`). -/
theorem cap_of_usesModifyAt (hdd : DDSound ks.toK) (hst : StaticsOK statics)
    (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], [])) (hr : EncapRun pm ks L σ lbls) {i : Nat}
    {x : LeafAccess} (hx : StepAccess ks L R σ lbls i x) (hu : UsesModifyAt ks σ lbls i x) :
    cap (σ i).1 (σ i).2.1 (ctxAt lbls i) x.leaf = some .modify := by
  obtain ⟨hi, acc, hc, hxa⟩ := hx
  obtain ⟨_, hu⟩ := hu
  obtain ⟨he, hs⟩ := hr i hi
  rw [ctxAt_eq hi]
  exact allows_modify
    (cap_of_usesModify (run_inv hdd hst h0 hr (Nat.le_of_lt hi)) he hs hc hxa hu)

/-- The capability of the context of step `j` permits the mode used by its access. -/
theorem allows_usedMode (hdd : DDSound ks.toK) (hst : StaticsOK statics)
    (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], [])) (hr : EncapRun pm ks L σ lbls) {j : Nat}
    {y : LeafAccess} (hy : StepAccess ks L R σ lbls j y) :
    Allows (cap (σ j).1 (σ j).2.1 (ctxAt lbls j) y.leaf) (usedMode ks σ lbls j y) := by
  unfold usedMode
  split
  · rename_i hu
    rw [cap_of_usesModifyAt hdd hst h0 hr hy hu]; exact Or.inr rfl
  · exact cap_of_access hdd hst h0 hr hy

/-- From an ordered handoff whose marker is a step of the context of step `i`, `hb` from the event
of step `i` to that of step `j` (12f, `handoff_compose`). -/
theorem hb_of_marker (hK : Corresponds G σ lbls K) {i r j : Nat} (hir : i ≤ r) (hrj : r < j)
    (hj : j < lbls.length) (hreq : ∃ hr : r < lbls.length, lbls[r].requester = ctxAt lbls i)
    {a b d : E} (ha : K.ev i = some a) (hb : K.ev r = some b) (hbd : G.HB b d) : G.HB a d := by
  obtain ⟨_, hreq⟩ := hreq
  rw [ctxAt_eq (by omega)] at hreq
  exact ((handoff_compose hK hir hrj hj hreq ha hb).2 hbd).1

/-- **Theorem 14c.1** (C33 item 3): two events that carry the atomicity 11e gives to two atomic
accesses (Q2) are not a race. -/
theorem pair_atomic {E C U V S : Type} {G : Events.Graph E C U V S} {a d : E} {x y : LeafAccess}
    (ha : AccTyped G a x) (hd : AccTyped G d y) (hx : x.order.isSome = true)
    (hy : y.order.isSome = true) : ¬ G.Race a d := fun hr =>
  hr.2.2.1.elim (fun h => h (ha.2.2 hx)) (fun h => h (hd.2.2 hy))

/-- **Theorem 14c.2** (C35, C43, C46; C51 item 2(c); 12d, 12f): in a `SafeConcurrentTrace` on
fragment F, for a pair in conflict on a `Confined` leaf with events `a` and `d`: `hb(a, d)`. -/
theorem pair_confined {D : AccessData G lbls K} (hdd : DDSound ks.toK) (hst : StaticsOK statics)
    (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], [])) (hK : Corresponds G σ lbls K)
    (hS : SafeConcurrentTrace pm ks L R σ lbls G K D) {i j : Nat} {x y : LeafAccess}
    (hp : ConflictPair ks L R σ lbls i j x y) (hc : ConfinedLeaf ks x.leaf) {a d : E}
    (ha : K.ev i = some a) (hd : K.ev j = some d) : G.HB a d := by
  obtain ⟨r, hrj, hfc, b, hb, hbd⟩ := hS.confinedHandoff i j x y hp hc a d ha hd
  have hj : j < lbls.length := hp.right.1
  have hm := allows_usedMode hdd hst h0 hS.run hp.right
  rw [← hp.leaf] at hm
  have hinc : IncompatConfined (cap (σ i).1 (σ i).2.1 (ctxAt lbls i) x.leaf)
      (usedMode ks σ lbls j y) := allows_present (cap_of_access hdd hst h0 hS.run hp.left)
  obtain ⟨r', hfc', -, -, hreq⟩ := loss_marker_confined hdd hst h0 hS.run
    (fun k hk d d' => hS.confinedExcl k hk x.leaf hc d d') hp.lt (Nat.le_of_lt hj)
    (fun e => hp.ctx e.symm) hm hinc
  have := hfc'.unique hfc
  subst this
  exact hb_of_marker hK hfc.1 hrj hj hreq ha hb hbd

/-- **Theorem 14c.3** (C44 cases 1, 2, 4; C45; C46; C51 item 2(f); 12d, 12f): in a
`SafeConcurrentTrace` on fragment F, for an exclusive pair in conflict (reading 13: the capability
of the context of the earlier access is incompatible with the mode used by the later access) on a
leaf that is not `Confined` (ordinary storage; `Atomic` storage with an ordinary access;
`Synchronized` storage with an exclusive capability), with events `a` and `d`: `hb(a, d)`. The
loss marker of 12d is the step of the ordered handoff of (f). -/
theorem pair_exclusive {D : AccessData G lbls K} (hdd : DDSound ks.toK) (hst : StaticsOK statics)
    (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], [])) (hK : Corresponds G σ lbls K)
    (hS : SafeConcurrentTrace pm ks L R σ lbls G K D) {i j : Nat} {x y : LeafAccess}
    (hp : ConflictPair ks L R σ lbls i j x y) (hx : ExclusivePair ks σ lbls i j x y)
    (hc : ¬ ConfinedLeaf ks x.leaf) {a d : E} (ha : K.ev i = some a) (hd : K.ev j = some d) :
    G.HB a d := by
  obtain ⟨r, hrj, hfc, b, hb, hbd⟩ := hS.handoff i j x y hp hx hc a d ha hd
  have hj : j < lbls.length := hp.right.1
  have hm := allows_usedMode hdd hst h0 hS.run hp.right
  rw [← hp.leaf] at hm
  have hinc : IncompatModify (cap (σ i).1 (σ i).2.1 (ctxAt lbls i) x.leaf)
      (usedMode ks σ lbls j y) := hx
  obtain ⟨r', hfc', -, -, hreq⟩ := loss_marker_modify hdd hst h0 hS.run hp.lt (Nat.le_of_lt hj)
    (fun e => hp.ctx e.symm) hm hinc
  have := hfc'.unique hfc
  subst this
  exact hb_of_marker hK hfc.1 hrj hj hreq ha hb hbd

/-- **Theorem 14c.4** (C44; C52): for a non-exclusive pair in conflict on a `Synchronized` leaf, the
events are ordered by `hb` in one direction or the other, by premise (d). -/
theorem pair_synchronized {D : AccessData G lbls K} (hS : SafeConcurrentTrace pm ks L R σ lbls G K D)
    {i j : Nat} {x y : LeafAccess} (hp : ConflictPair ks L R σ lbls i j x y)
    (hx : ¬ ExclusivePair ks σ lbls i j x y) (hs : SyncLeaf ks x.leaf) {a d : E}
    (ha : K.ev i = some a) (hd : K.ev j = some d) : G.HB a d ∨ G.HB d a :=
  hS.synchronized i j x y hp hx hs a d ha hd

/-- A leaf with a class that is not `Atomic` is `Synchronized` or `Confined` (C35). -/
theorem class_of_not_atomic {l : Nat} (hn : ks.SharedDiscipline l ≠ none)
    (ha : ¬ AtomicLeaf ks l) : SyncLeaf ks l ∨ ConfinedLeaf ks l := by
  unfold SyncLeaf ConfinedLeaf
  unfold AtomicLeaf at ha
  cases h : ks.SharedDiscipline l with
  | none => exact absurd h hn
  | some d =>
    rw [h] at ha
    cases d with
    | atomic sz al => exact absurd rfl ha
    | synchronized => exact .inl rfl
    | confined => exact .inr rfl

/-- An `Atomic` discipline makes an `Atomic` leaf (C35, C38). -/
theorem atomicLeaf_of {l sz al : Nat} (h : ks.SharedDiscipline l = some (.atomic sz al)) :
    AtomicLeaf ks l := by
  unfold AtomicLeaf; rw [h]; rfl

/-- The classified accesses of an admitted step (11e) that does not use `Modify` for `x`, under
the rule of 11f for the step and the premise of reading 12 for its controller leaf: `x` is an
atomic access of an `Atomic` leaf, a non-atomic read of a leaf that is not `Atomic`, or a
non-atomic access of a `Synchronized` or `Confined` leaf (C35–C39, C42; C48 with reading 12). -/
theorem access_class {lbl : Label} {st st' : SC × SyncReg × ArenaReg} {acc : List LeafAccess}
    {x : LeafAccess} (hs : LStep ks L lbl st st') (hb : AtomicOrdinaryOK ks st.1 lbl)
    (hctl : ∀ ctl, ctlLeafAt L st lbl = some ctl →
      ∃ sz al, ks.SharedDiscipline ctl = some (.atomic sz al) ∧ sz ≠ 0)
    (hc : classify ks L R st lbl = some acc) (hx : x ∈ acc) (hnu : ¬ UsesModify ks st lbl x) :
    (x.order ≠ none ∧ AtomicLeaf ks x.leaf) ∨
      (x.order = none ∧ x.kind = .read ∧ ¬ AtomicLeaf ks x.leaf) ∨
      (x.order = none ∧ (SyncLeaf ks x.leaf ∨ ConfinedLeaf ks x.leaf)) := by
  have ctl : ∀ (i : Nat) (k : Events.Kind) (o : MemOrder),
      ctlLeafAt L st lbl = ctlOf L st i → x ∈ ctlAccess L st i k o →
      (x.order ≠ none ∧ AtomicLeaf ks x.leaf) := by
    intro i k o he hx
    unfold ctlAccess at hx
    cases hco : (st.2.1[i]?).bind (ControlOf L st.1) with
    | none => rw [hco] at hx; simp at hx
    | some c =>
      rw [hco] at hx
      simp only [Option.toList_some, List.map_cons, List.map_nil, List.mem_singleton] at hx
      subst hx
      obtain ⟨sz, al, hd, -⟩ := hctl c (by rw [he]; exact hco)
      exact ⟨by simp, atomicLeaf_of hd⟩
  cases lbl with
  | kernel c op =>
    cases op with
    | read a ls =>
      simp only [classify, Option.some.injEq] at hc; subst hc
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
      refine .inr (.inl ⟨rfl, rfl, fun hat => hnu (.inr ⟨hat, ⟨c, a, ls, rfl⟩, hb⟩)⟩)
    | write a ls =>
      simp only [classify, Option.some.injEq] at hc; subst hc
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
      exact absurd (.inl rfl) hnu
    | writeShared a ls =>
      simp only [classify] at hc
      split at hc
      · rename_i hd
        cases hc
        obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
        have hna : ¬ AtomicLeaf ks l := fun hat => hd.2.2.2.1 ⟨l, hl, hat⟩
        split
        · rename_i hat; exact absurd hat hna
        · exact .inr (.inr ⟨rfl, class_of_not_atomic (hd.1 l hl) hna⟩)
      · cases hc
    | _ => simp only [classify, Option.some.injEq] at hc; subst hc; simp at hx
  | writeShared c a region ord kind =>
    simp only [classify, Option.some.injEq] at hc; subst hc
    have hd := writeShared_legal hs
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
    split
    · rename_i hat
      refine .inl ⟨?_, hat⟩
      show ord ≠ none
      cases kind with
      | store =>
        have := hd.2.2.2.1 ⟨l, hl, hat⟩
        cases ord with
        | none => exact this.elim
        | some o => simp
      | rmw v =>
        obtain ⟨-, -, -, -, -, -, hann⟩ := hd
        cases ord with
        | none => exact hann.elim
        | some o => simp
    · rename_i hat
      cases kind with
      | store => exact .inr (.inr ⟨rfl, class_of_not_atomic (hd.1 l hl) hat⟩)
      | rmw v =>
        obtain ⟨l', sz, al, rfl, hdl, -, -⟩ := hd
        rw [List.mem_singleton] at hl; subst hl
        exact absurd (atomicLeaf_of hdl) hat
  | readShared c a l o v =>
    simp only [classify, Option.some.injEq] at hc; subst hc
    rw [List.mem_singleton] at hx; subst hx
    obtain ⟨⟨sz, al, hd⟩, -, -⟩ := (atomic_steps_legal hs).1 c a l o v rfl
    exact .inl ⟨by simp, atomicLeaf_of hd⟩
  | cas c a l succ fail br =>
    obtain ⟨-, ⟨sz, al, hd⟩, -⟩ := (atomic_steps_legal hs).2 c a l succ fail br rfl
    cases br <;>
    · simp only [classify, Option.some.injEq] at hc; subst hc
      rw [List.mem_singleton] at hx; subst hx
      exact .inl ⟨by simp, atomicLeaf_of hd⟩
  | newMutex c g =>
    simp only [classify, Option.some.injEq] at hc; subst hc
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
    exact absurd (.inl rfl) hnu
  | acquire c i =>
    simp only [classify, Option.some.injEq] at hc; subst hc
    exact .inl (ctl i _ _ rfl hx)
  | unlock c i =>
    simp only [classify, Option.some.injEq] at hc; subst hc
    exact .inl (ctl i _ _ rfl hx)
  | resetLock c i =>
    simp only [classify, Option.some.injEq] at hc; subst hc
    exact .inl (ctl i _ _ rfl hx)
  | _ => simp only [classify, Option.some.injEq] at hc; subst hc; simp at hx

/-- **Theorem 14c.5** (C35, C42, C43, C44; C51 item 2(b); readings 12, 13), exhaustiveness: in a
`SafeConcurrentTrace` from the initial state of Spec 1 §47, under `DDSound` and the premise of
reading 12, a non-exclusive pair in conflict is on a `Synchronized` or `Confined` leaf. A pair that
is not exclusive has no step that uses `Modify` for its access: the access of a step is covered by
the capability of its context (12a; `cap_of_access`, `cap_of_usesModifyAt`). The rest uses the
execution and the condition `OrdinaryAtomicOK` of (b). Reading 12 is used for a pair one of whose
accesses is a protocol access of `acquire`, `unlock` or `resetLock`. -/
theorem pair_exhaustive {D : AccessData G lbls K} (hdd : DDSound ks.toK) (hst : StaticsOK statics)
    (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], []))
    (hS : SafeConcurrentTrace pm ks L R σ lbls G K D)
    (h12 : CtlAtomic ks L σ lbls) {i j : Nat} {x y : LeafAccess}
    (hp : ConflictPair ks L R σ lbls i j x y) (hx : ¬ ExclusivePair ks σ lbls i j x y) :
    SyncLeaf ks x.leaf ∨ ConfinedLeaf ks x.leaf := by
  have hxi : ¬ UsesModifyAt ks σ lbls i x := fun hu => hx (by
    unfold ExclusivePair
    rw [cap_of_usesModifyAt hdd hst h0 hS.run hp.left hu]
    exact Or.inl rfl)
  have hyj : ¬ UsesModifyAt ks σ lbls j y := fun hu => hx (by
    have hpres := allows_present (cap_of_access hdd hst h0 hS.run hp.left)
    have hmod : usedMode ks σ lbls j y = .modify := by simp only [usedMode, hu, ↓reduceIte]
    unfold ExclusivePair
    rw [hmod]
    revert hpres
    cases cap (σ i).1 (σ i).2.1 (ctxAt lbls i) x.leaf with
    | none => exact fun h => absurd rfl h
    | some v => exact fun _ => Or.inr rfl)
  have cls : ∀ k z, StepAccess ks L R σ lbls k z → ¬ UsesModifyAt ks σ lbls k z →
      (z.order ≠ none ∧ AtomicLeaf ks z.leaf) ∨
        (z.order = none ∧ z.kind = .read ∧ ¬ AtomicLeaf ks z.leaf) ∨
        (z.order = none ∧ (SyncLeaf ks z.leaf ∨ ConfinedLeaf ks z.leaf)) := by
    intro k z ⟨hk, acc, hc, hz⟩ hnu
    exact access_class (hS.run k hk).2 (hS.ordinary k hk) (fun ctl h => h12 k hk ctl h) hc hz
      (fun hu => hnu ⟨hk, hu⟩)
  have cx := cls i x hp.left hxi
  have cy := cls j y hp.right hyj
  rw [← hp.leaf] at cy
  rcases cx with ⟨hxo, hxa⟩ | ⟨hxo, hxk, hxa⟩ | ⟨-, hxc⟩
  · rcases cy with ⟨hyo, -⟩ | ⟨-, -, hya⟩ | ⟨-, hyc⟩
    · exact (hp.nonatomic.elim hxo hyo).elim
    · exact absurd hxa hya
    · exact hyc
  · rcases cy with ⟨-, hya⟩ | ⟨-, hyk, -⟩ | ⟨-, hyc⟩
    · exact absurd hya hxa
    · rcases hp.writes with h | h
      · rw [hxk] at h; exact h.elim
      · rw [hyk] at h; exact h.elim
    · exact hyc
  · exact hxc

/-- Two events of distinct contexts at steps `i < j` whose accesses conflict and carry the kind and
atomicity of 11e are ordered by `hb` in one direction or the other (14c.2–14c.5), in a
`SafeConcurrentTrace` on fragment F under reading 12. -/
theorem pair_ordered {D : AccessData G lbls K} (hdd : DDSound ks.toK) (hst : StaticsOK statics)
    (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], [])) (hK : Corresponds G σ lbls K)
    (hS : SafeConcurrentTrace pm ks L R σ lbls G K D) (h12 : CtlAtomic ks L σ lbls) {i j : Nat}
    {x y : LeafAccess} (hp : ConflictPair ks L R σ lbls i j x y) {a d : E}
    (ha : K.ev i = some a) (hd : K.ev j = some d) : G.HB a d ∨ G.HB d a := by
  by_cases hc : ConfinedLeaf ks x.leaf
  · exact .inl (pair_confined hdd hst h0 hK hS hp hc ha hd)
  · by_cases hx : ExclusivePair ks σ lbls i j x y
    · exact .inl (pair_exclusive hdd hst h0 hK hS hp hx hc ha hd)
    · rcases pair_exhaustive hdd hst h0 hS h12 hp hx with hs | hc'
      · exact pair_synchronized hS hp hx hs ha hd
      · exact absurd hc' hc

/-- **Theorem 14c.6** (C26, C52): under Q4, the two steps of a pair in conflict have events, and
these are ordered by `hb` in one direction or the other, in a `SafeConcurrentTrace` on fragment F
under reading 12. The statement is about the existence and the order of the events of the two
steps. It does not say that these events carry the accesses of the steps, with their byte
footprints: that fidelity is the coverage of C29, an open obligation (`OB-C20`). -/
theorem pair_covered {D : AccessData G lbls K} (hdd : DDSound ks.toK) (hst : StaticsOK statics)
    (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], [])) (hK : Corresponds G σ lbls K)
    (hS : SafeConcurrentTrace pm ks L R σ lbls G K D) (h12 : CtlAtomic ks L σ lbls)
    (hq4 : CorrQ4 ks L R σ lbls K) {i j : Nat} {x y : LeafAccess}
    (hp : ConflictPair ks L R σ lbls i j x y) :
    ∃ a d, K.ev i = some a ∧ K.ev j = some d ∧ (G.HB a d ∨ G.HB d a) := by
  obtain ⟨a, ha⟩ := hq4 i x hp.left
  obtain ⟨d, hd⟩ := hq4 j y hp.right
  exact ⟨a, d, ha, hd, pair_ordered hdd hst h0 hK hS h12 hp ha hd⟩

end Pairs

/-! ## 14d: the conditional composition theorem (C52; `OB-C06`) -/

/-- An event with a byte range carries an access. -/
theorem isAcc_of_range {E C U V S : Type} {G : Events.Graph E C U V S} {e : E} {r : Range}
    (h : G.range? e = some r) : G.IsAcc e := by
  unfold Events.Graph.range? at h
  unfold Events.Graph.IsAcc
  intro hn
  rw [hn] at h
  cases h

/-- **Theorem 14d**, conditional composition theorem on fragment F (C52; `OB-C06`). Proven on
fragment F only, not as a universal proof of C52: `DDSound`, well-formed statics, an execution from
the initial state of Spec 1 §47 with its graph and the partial correspondence K1–K4, the data of
reading 9, the correspondence premises Q1–Q3 and the premise of reading 12. Then no pair of
events of `G` is a race (C33).

Pairs of distinct storage identities go through Q3 and 14a.2; pairs of one identity through Q2 and
14c (14c.2, 14c.3, 14c.5 with 14c.4); initial writes through L3. The proof uses neither
`EventConsistent`, nor the finite causal past, nor the conditions `OrderLegal`, `StepOrders` and
`UnitLeaf` of (b), nor (e), nor the edge of `LockOrder`, nor the lifecycle conditions beyond the
correspondence. It uses neither the provenance of lifecycle roles (K3 and K4, converse direction),
nor the field `init_origin` of the data. The conditions that the proof does not use restrict the
graphs that the premises accept.

The conclusion is about the events of `G`. The premises do not include Q4: a graph that gives no
event to a step with an access satisfies them. The presence of the events is Q4, carried by 14c.6
(`pair_covered`); the coverage of C29 remains open (`OB-C20`). -/
theorem no_race {E U V S : Type} {ks : KShared} {L : MutexLayout} {R : CtlOrders}
    {statics : Statics} {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label}
    {G : Events.Graph E Nat U V S} {K : StepEvents E} {D : AccessData G lbls K}
    (hdd : DDSound ks.toK) (hst : StaticsOK statics)
    (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], [])) (hK : Corresponds G σ lbls K)
    (hS : SafeConcurrentTrace pm ks L R σ lbls G K D) (hq1 : CorrQ1 G lbls K D)
    (hq2 : CorrQ2 ks L R σ lbls G K D) (hq3 : CorrQ3 D) (h12 : CtlAtomic ks L σ lbls)
    (a d : E) : ¬ G.Race a d := by
  rintro ⟨hctx, hconf, hna, hab, hba⟩
  obtain ⟨ra, rd, hra, hrd, -, -, hw⟩ := id hconf
  have ha := isAcc_of_range hra
  have hd := isAcc_of_range hrd
  by_cases hs : D.sid a = D.sid d
  · rcases hq1 a ha with ⟨i, hi, hia⟩ | hia
    · rcases hq1 d hd with ⟨j, hj, hjd⟩ | hjd
      · obtain ⟨x, y, hx, hy, hxy, tx, ty⟩ := hq2 i j a d hia hjd hconf hs
        have hci : ctxAt lbls i = G.ctx a := by rw [ctxAt_eq hi, hK.ctx i hi a hia]
        have hcj : ctxAt lbls j = G.ctx d := by rw [ctxAt_eq hj, hK.ctx j hj d hjd]
        have hwr : x.kind.Writes ∨ y.kind.Writes := by
          rcases hw with ⟨k, hk, hkw⟩ | ⟨k, hk, hkw⟩
          · rw [tx.1] at hk; cases hk; exact .inl hkw
          · rw [ty.1] at hk; cases hk; exact .inr hkw
        have hno : x.order = none ∨ y.order = none := by
          rcases hna with h | h
          · exact .inl (Option.not_isSome_iff_eq_none.1 fun hs => h (tx.2.2 hs))
          · exact .inr (Option.not_isSome_iff_eq_none.1 fun hs => h (ty.2.2 hs))
        rcases Nat.lt_trichotomy i j with h | h | h
        · have hp : ConflictPair ks L R σ lbls i j x y :=
            ⟨h, hx, hy, hxy, by rw [hci, hcj]; exact hctx, hwr, hno⟩
          rcases pair_ordered hdd hst h0 hK hS h12 hp hia hjd with h' | h'
          · exact hab h'
          · exact hba h'
        · subst h
          exact hctx (by rw [← hci, ← hcj])
        · have hp : ConflictPair ks L R σ lbls j i y x :=
            ⟨h, hy, hx, hxy.symm, by rw [hci, hcj]; exact fun e => hctx e.symm, hwr.symm,
              hno.symm⟩
          rcases pair_ordered hdd hst h0 hK hS h12 hp hjd hia with h' | h'
          · exact hba h'
          · exact hab h'
      · exact hba (hS.lifetime.init_first d a hjd ha hs hctx)
    · exact hab (hS.lifetime.init_first a d hia hd hs.symm fun e => hctx e.symm)
  · rcases hq3 a d hconf hs with ⟨v, w, hv, hw', hvw⟩ | ⟨v, w, hv, hw', hvw⟩
    · exact hab (lifetime_reuse hS.lifetime hv hw' hvw ha rfl hd rfl)
    · exact hba (lifetime_reuse hS.lifetime hv hw' hvw hd rfl ha rfl)

/-! ## 14e: the edge of `LockOrder` under the reference realization (C48, C49; `OB-C04`) -/

section Lock

variable {E S : Type} {G : Events.Graph E Nat Nat Nat S} {L : MutexLayout}
  {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} {K : StepEvents E} {e x : Nat}
  {R : CtlOrders} {v₀ v₁ : Nat}

/-- **Theorem 14e.1** (C48; C49; `OB-C04`), corollary of 13d.3 and 13d.4: on a graph with the
correspondence K1–K4 and realization R for the entry `e` and the unit `x`, under conjuncts 1 and 3
of `EventConsistent`, with release-capable orders of `unlock` and `resetLock` and an acquire-capable
order of `acquire`, let `q` be an `acquire(e)` step at which the controller of `e` is `x`. If its
event reads by `rf` the event of an `unlock(e)` or `resetLock(e)` step `p`, that event is
`hb`-before it, by `sw`. That `p` is a controller step of `(e, x)` is not assumed: 13d.3 makes the
`rf` source the event of a controller step, and K1 identifies that step with `p`.

The condition on the controller of `e` at `q` is that of C49 (last paragraph): R speaks only of the
steps whose controller is `x`, and an `ok` execution can move the controller of a live entry to
another leaf (`witness_w12`, a `transfer` of the mutex value `M`). Conjunct 2 is not used. -/
theorem lock_edge (hK : Corresponds G σ lbls K) (hR : Realizes G L σ lbls K e x R v₀ v₁)
    (h1 : G.RfWF) (h3 : G.RmwAtomic) (hrel : ReleaseOrder R.rel)
    (hreset : ReleaseOrder R.reset) (hacq : AcquireOrder R.acq) {p q : Nat}
    (hp : PubOn lbls e p) (hq : AcqOn lbls e q) (hx : ctlOf L (σ q) e = some x) {b d : E}
    (hb : K.ev p = some b) (hd : K.ev q = some d) (hrf : G.rf b d) : G.HB b d := by
  obtain ⟨c, hql⟩ := hq
  have hqc : CtlStep L σ lbls e x q := by unfold CtlStep; rw [hql]; exact ⟨rfl, hx⟩
  obtain ⟨k', hlast, hk'⟩ := (acquire_rf_source hR h1 h3 hql hqc hd).2 b hrf
  have := hK.inj p k' b hb hk'
  subst this
  obtain ⟨hu, hr, -⟩ := acquire_sw hR hql hqc hd hlast.1 hb hrf
  obtain ⟨c', hpl | hpl⟩ := hp
  · exact .single (.inr ((hu c' e hpl).2 ⟨hrel, hacq⟩))
  · exact .single (.inr ((hr c' e hpl).2 ⟨hreset, hacq⟩))

/-- **Theorem 14e.2** (C48, C49; `OB-C04`), corollary of 13d.4: under realization R for the entry
`e` and the unit `x`, with release-capable orders of `unlock` and `resetLock` and an
acquire-capable order of `acquire`, if the controller of `e` is `x` at every protocol step on `e`
(the stability of the controller leaf, condition of 13e), the edge of reading 11 holds for `e`.

The stability condition is that of C49 (last paragraph): an `ok` execution can move the controller
of a live entry to another leaf (`witness_w12`, a `transfer` of the mutex value `M`). -/
theorem lock_edge_entry (hR : Realizes G L σ lbls K e x R v₀ v₁) (hrel : ReleaseOrder R.rel)
    (hreset : ReleaseOrder R.reset) (hacq : AcquireOrder R.acq)
    (hstab : ∀ k, ProtoOn lbls e k → ctlOf L (σ k) e = some x) :
    ∀ p q, PubOn lbls e p → AcqOn lbls e q → ∀ b d, K.ev p = some b → K.ev q = some d →
      G.rf b d → G.HB b d := by
  intro p q hp hq b d hb hd hrf
  have proto_p : ProtoOn lbls e p := by
    obtain ⟨c, h | h⟩ := hp <;> (unfold ProtoOn; rw [h])
  have proto_q : ProtoOn lbls e q := by
    obtain ⟨c, h⟩ := hq; unfold ProtoOn; rw [h]
  obtain ⟨c, hql⟩ := hq
  obtain ⟨hu, hr, -⟩ := acquire_sw hR hql (ctlStep_of_proto proto_q (hstab q proto_q)) hd
    (ctlStep_of_proto proto_p (hstab p proto_p)) hb hrf
  obtain ⟨c', hpl | hpl⟩ := hp
  · exact .single (.inr ((hu c' e hpl).2 ⟨hrel, hacq⟩))
  · exact .single (.inr ((hr c' e hpl).2 ⟨hreset, hacq⟩))

end Lock

end Ern.ConcurrencyModel
