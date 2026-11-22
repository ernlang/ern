import Ern.ConcurrencyModel.SafeTrace

/-!
# Witness tooling for theorem 14: bounded forms of the safe-trace conditions

Shared material of the witnesses S1–S8 (`WitnessSafe`): each condition of `SafeConcurrentTrace`
(C51 item 2), each correspondence premise Q1–Q3 (C52) and the hypothesis of reading 12 from a
bounded form that `decide` evaluates on a finite execution with a hand-written graph, proved
sound. The pairs in conflict range over the classified accesses of the steps (`stepAcc`); the
contexts with a capability over the contexts of the state (`cap_nil`). The legality of the memory
orders of the events (`OrderLegal`) is checked event by event (`orderLegal_of_check`), and the
agreement of the atomic event of a step with its accesses (`StepOrders`) step by step
(`stepOrders_of_check`).
-/

namespace Ern.ConcurrencyModel

open Ern.MemoryModel Ern.MemoryModel.Access Events

/-! ## Decidability -/

section Dec

variable {E C U V S : Type} (G : Events.Graph E C U V S)

instance [DecidableEq U] [DecidableEq V] (e : E) : Decidable (G.IsAcc e) := by
  unfold Events.Graph.IsAcc; infer_instance

instance [DecidableEq C] [DecidableEq U] [DecidableEq V] [DecidableEq S] (v : E) (x : S) :
    Decidable (G.BeginOf v x) := by
  unfold Events.Graph.BeginOf; infer_instance

instance [DecidableEq C] [DecidableEq U] [DecidableEq V] [DecidableEq S] (v : E) (x : S) :
    Decidable (G.EndOf v x) := by
  unfold Events.Graph.EndOf; infer_instance

instance [∀ e, Decidable (G.Atomic e)] (e : E) (x : LeafAccess) : Decidable (AccTyped G e x) := by
  unfold AccTyped; infer_instance

end Dec

instance (ks : KShared) (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) (i j : Nat)
    (x y : LeafAccess) : Decidable (ExclusivePair ks σ lbls i j x y) := by
  unfold ExclusivePair; infer_instance

instance {Inc : Option Mode → Mode → Prop} [∀ v m, Decidable (Inc v m)] {E U V S : Type}
    [Events.Enum E] [DecidableEq E] (ks : KShared) (σ : Nat → SC × SyncReg × ArenaReg)
    (lbls : List Label) (G : Events.Graph E Nat U V S) [DecidableRel G.HB] (K : StepEvents E)
    (i j : Nat) (x y : LeafAccess) : Decidable (PairHandoff Inc ks σ lbls G K i j x y) := by
  unfold PairHandoff; infer_instance

instance (ks : KShared) (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) :
    Decidable (OrdinaryAtomicOK ks σ lbls) := by
  unfold OrdinaryAtomicOK; infer_instance

instance (ks : KShared) (lbls : List Label) : Decidable (InheritedLegal ks lbls) := by
  unfold InheritedLegal; infer_instance

/-! ## Classified accesses of a step -/

section Steps

variable {ks : KShared} {L : MutexLayout} {R : CtlOrders} {σ : Nat → SC × SyncReg × ArenaReg}
  {lbls : List Label}

variable (ks L R σ lbls) in
/-- The classified accesses of step `i` (11e); empty when the step has none or is past the end. -/
def stepAcc (i : Nat) : List LeafAccess :=
  match lbls[i]? with
  | some lbl => (classify ks L R (σ i) lbl).getD []
  | none => []

/-- An access of a step is in `stepAcc`. -/
theorem mem_stepAcc {i : Nat} {x : LeafAccess} (h : StepAccess ks L R σ lbls i x) :
    x ∈ stepAcc ks L R σ lbls i := by
  obtain ⟨hi, acc, hc, hx⟩ := h
  unfold stepAcc
  rw [List.getElem?_eq_getElem hi]
  simp only [hc, Option.getD_some]
  exact hx

/-- A member of `stepAcc` is an access of the step. -/
theorem stepAccess_of_mem {i : Nat} {x : LeafAccess} (h : x ∈ stepAcc ks L R σ lbls i) :
    StepAccess ks L R σ lbls i x := by
  unfold stepAcc at h
  cases hl : lbls[i]? with
  | none => simp [hl] at h
  | some lbl =>
    simp only [hl] at h
    obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.1 hl
    cases hc : classify ks L R (σ i) lbl with
    | none => simp [hc] at h
    | some acc =>
      simp only [hc, Option.getD_some] at h
      exact ⟨hi, acc, by rw [he]; exact hc, h⟩

variable (lbls) in
/-- A property of the accesses `x` and `y` of steps `i` and `j` when they are on the same leaf, of
distinct contexts, one of them writes and one of them is non-atomic. -/
def PairCond (P : Nat → Nat → LeafAccess → LeafAccess → Prop) (i j : Nat) (x y : LeafAccess) :
    Prop :=
  x.leaf = y.leaf → ctxAt lbls i ≠ ctxAt lbls j → (x.kind.Writes ∨ y.kind.Writes) →
    (x.order = none ∨ y.order = none) → P i j x y

instance {P : Nat → Nat → LeafAccess → LeafAccess → Prop} [∀ i j x y, Decidable (P i j x y)]
    (i j : Nat) (x y : LeafAccess) : Decidable (PairCond lbls P i j x y) := by
  unfold PairCond; infer_instance

variable (ks L R σ lbls) in
/-- A property of all the candidate pairs in conflict: steps `i < j` of the trace with accesses `x`
and `y` of the same leaf, of distinct contexts, one of which writes and one of which is
non-atomic. -/
def PairCheck (P : Nat → Nat → LeafAccess → LeafAccess → Prop) : Prop :=
  ∀ j, j < lbls.length → ∀ i, i < j → ∀ x ∈ stepAcc ks L R σ lbls i,
    ∀ y ∈ stepAcc ks L R σ lbls j, PairCond lbls P i j x y

instance {P : Nat → Nat → LeafAccess → LeafAccess → Prop} [∀ i j x y, Decidable (P i j x y)] :
    Decidable (PairCheck ks L R σ lbls P) := by
  unfold PairCheck; infer_instance

/-- A property checked on the candidate pairs holds for every pair in conflict. -/
theorem forall_conflictPairs {P : Nat → Nat → LeafAccess → LeafAccess → Prop}
    (h : PairCheck ks L R σ lbls P) :
    ∀ i j x y, ConflictPair ks L R σ lbls i j x y → P i j x y :=
  fun i j x y hp => h j hp.right.1 i hp.lt x (mem_stepAcc hp.left) y (mem_stepAcc hp.right)
    hp.leaf hp.ctx hp.writes hp.nonatomic

/-- A candidate pair whose accesses are in `stepAcc` is a pair in conflict. -/
theorem conflictPair_of {i j : Nat} {x y : LeafAccess} (hij : i < j)
    (hx : x ∈ stepAcc ks L R σ lbls i) (hy : y ∈ stepAcc ks L R σ lbls j) (hl : x.leaf = y.leaf)
    (hc : ctxAt lbls i ≠ ctxAt lbls j) (hw : x.kind.Writes ∨ y.kind.Writes)
    (hn : x.order = none ∨ y.order = none) : ConflictPair ks L R σ lbls i j x y :=
  ⟨hij, stepAccess_of_mem hx, stepAccess_of_mem hy, hl, hc, hw, hn⟩

variable {E U V S : Type} {G : Events.Graph E Nat U V S} {K : StepEvents E}

/-- `ConfinedHandoff` from its check on the candidate pairs. -/
theorem confinedHandoff_of_check
    (h : PairCheck ks L R σ lbls fun i j x y =>
      ConfinedLeaf ks x.leaf → PairHandoff IncompatConfined ks σ lbls G K i j x y) :
    ConfinedHandoff ks L R σ lbls G K :=
  forall_conflictPairs h

/-- `SyncOrdered` from its check on the candidate pairs. -/
theorem syncOrdered_of_check
    (h : PairCheck ks L R σ lbls fun i j x y => ¬ ExclusivePair ks σ lbls i j x y →
      SyncLeaf ks x.leaf → ∀ a d, K.ev i = some a → K.ev j = some d → G.HB a d ∨ G.HB d a) :
    SyncOrdered ks L R σ lbls G K :=
  forall_conflictPairs h

/-- `HandoffOrdered` from its check on the candidate pairs. -/
theorem handoffOrdered_of_check
    (h : PairCheck ks L R σ lbls fun i j x y => ExclusivePair ks σ lbls i j x y →
      ¬ ConfinedLeaf ks x.leaf → PairHandoff IncompatModify ks σ lbls G K i j x y) :
    HandoffOrdered ks L R σ lbls G K :=
  forall_conflictPairs h

/-- Q2 from its check on the steps of the trace, when the correspondence gives no event past the
end. -/
theorem corrQ2_of_check {D : AccessData G lbls K}
    (hK : ∀ i, lbls.length ≤ i → K.ev i = none)
    (h : ∀ i, i < lbls.length → ∀ j, j < lbls.length → ∀ a d, K.ev i = some a →
      K.ev j = some d → G.Conflict a d → D.sid a = D.sid d →
      ∃ x ∈ stepAcc ks L R σ lbls i, ∃ y ∈ stepAcc ks L R σ lbls j, x.leaf = y.leaf ∧
        AccTyped G a x ∧ AccTyped G d y) :
    CorrQ2 ks L R σ lbls G K D := by
  intro i j a d ha hd hc hs
  have hi : i < lbls.length := Decidable.byContradiction fun hn => by
    rw [hK i (by omega)] at ha; cases ha
  have hj : j < lbls.length := Decidable.byContradiction fun hn => by
    rw [hK j (by omega)] at hd; cases hd
  obtain ⟨x, hx, y, hy, hl, ta, td⟩ := h i hi j hj a d ha hd hc hs
  exact ⟨x, y, stepAccess_of_mem hx, stepAccess_of_mem hy, hl, ta, td⟩

end Steps

/-! ## Contexts with a capability -/

/-- A context past the end of the context list has no frames. -/
theorem stk_of_ge {s : SC} {d : Nat} (h : s.C.length ≤ d) : s.stk d = [] := by
  unfold SC.stk; rw [List.getElem?_eq_none h]

/-- A contract without `Confined` leaf satisfies the first part of (c). -/
theorem confinedExcl_none {ks : KShared} {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label}
    (h : ∀ l, ¬ ConfinedLeaf ks l) : ConfinedExcl ks σ lbls :=
  fun _ _ l hl => absurd hl (h l)

/-- The first part of (c) from its check on the `Confined` leaves `ls` and the contexts below `N`,
when every state has at most `N` contexts. -/
theorem confinedExcl_of_check {ks : KShared} {σ : Nat → SC × SyncReg × ArenaReg}
    {lbls : List Label} (ls : List Nat) (N : Nat) (hl : ∀ l, ConfinedLeaf ks l → l ∈ ls)
    (hN : ∀ k, k ≤ lbls.length → (σ k).1.C.length ≤ N)
    (h : ∀ k, k ≤ lbls.length → ∀ l ∈ ls, ∀ d, d < N → ∀ d', d' < N → d ≠ d' →
      cap (σ k).1 (σ k).2.1 d l ≠ none → cap (σ k).1 (σ k).2.1 d' l = none) :
    ConfinedExcl ks σ lbls := by
  intro k hk l hc d d' hne hd
  have hdN : d < N := Decidable.byContradiction fun hn =>
    hd (cap_nil (stk_of_ge (Nat.le_trans (hN k hk) (by omega))))
  by_cases hd' : d' < N
  · exact h k hk l (hl l hc) d hdN d' hd' hne hd
  · exact cap_nil (stk_of_ge (Nat.le_trans (hN k hk) (by omega)))

/-! ## The controller leaf (reading 12) and the edge of `LockOrder` -/

/-- The check of reading 12 on one step. -/
def ctlAtomicB (ks : KShared) (L : MutexLayout) (st : SC × SyncReg × ArenaReg) (lbl : Label) :
    Bool :=
  match ctlLeafAt L st lbl with
  | none => true
  | some ctl =>
    match ks.SharedDiscipline ctl with
    | some (.atomic sz _) => sz != 0
    | _ => false

/-- `CtlAtomic` from its check on every step. -/
theorem ctlAtomic_of_check {ks : KShared} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg}
    {lbls : List Label} (h : ∀ k (hk : k < lbls.length), ctlAtomicB ks L (σ k) lbls[k] = true) :
    CtlAtomic ks L σ lbls := by
  intro k hk ctl hc
  have := h k hk
  unfold ctlAtomicB at this
  rw [hc] at this
  cases hd : ks.SharedDiscipline ctl with
  | none => simp [hd] at this
  | some d =>
    cases d with
    | atomic sz al => simp only [hd] at this; exact ⟨sz, al, rfl, by simpa using this⟩
    | synchronized => simp [hd] at this
    | confined => simp [hd] at this

/-- The label is an `acquire`. -/
def IsAcquire : Label → Bool
  | .acquire _ _ => true
  | _ => false

/-- A trace without `acquire` satisfies the edge of `LockOrder` vacuously. -/
theorem lockEdge_none {E U V S : Type} {G : Events.Graph E Nat U V S} {lbls : List Label}
    {K : StepEvents E} (h : ∀ k (hk : k < lbls.length), IsAcquire lbls[k] = false) :
    LockEdge G lbls K := by
  intro e p q _ ⟨c, hq⟩
  obtain ⟨hk, he⟩ := List.getElem?_eq_some_iff.1 hq
  have := h q hk
  rw [he] at this
  cases this

/-- The entry of an `acquire` is `e₀` (`true` on the other labels). -/
def AcqEntry (e₀ : Nat) : Label → Bool
  | .acquire _ e => e == e₀
  | _ => true

/-- The edge of `LockOrder` for a trace whose `acquire` steps are all on `e₀`, from the edge
for `e₀`. -/
theorem lockEdge_single {E U V S : Type} {G : Events.Graph E Nat U V S} {lbls : List Label}
    {K : StepEvents E} (e₀ : Nat) (h : ∀ k (hk : k < lbls.length), AcqEntry e₀ lbls[k] = true)
    (he : ∀ p q, PubOn lbls e₀ p → AcqOn lbls e₀ q → ∀ b d, K.ev p = some b → K.ev q = some d →
      G.rf b d → G.HB b d) :
    LockEdge G lbls K := by
  intro e p q hp hq
  obtain ⟨c, hql⟩ := hq
  obtain ⟨hk, hlq⟩ := List.getElem?_eq_some_iff.1 hql
  have := h q hk
  rw [hlq] at this
  have hee : e = e₀ := by simpa [AcqEntry] using this
  subst hee
  exact he p q hp ⟨c, hql⟩

/-- The stability of the controller of `e` from its check on the steps of the trace (a protocol
step is a step of the trace). -/
theorem stab_of_check {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label}
    {e x : Nat} (h : ∀ k, k < lbls.length → ProtoOn lbls e k → ctlOf L (σ k) e = some x) :
    ∀ k, ProtoOn lbls e k → ctlOf L (σ k) e = some x := by
  intro k hp
  have hk : k < lbls.length := Decidable.byContradiction fun hn => by
    unfold ProtoOn at hp; rw [List.getElem?_eq_none (by omega)] at hp; exact hp
  exact h k hk hp

/-! ## Graphs given by lists -/

/-- A list correspondence gives no event past the end of its list. -/
theorem listK_none {n : Nat} {evs : List (Fin n)} {starts completes : List (Nat × Fin n)}
    {lbls : List Label} (h : evs.length ≤ lbls.length) :
    ∀ i, lbls.length ≤ i → (listK evs starts completes).ev i = none := by
  intro i hi
  exact List.getElem?_eq_none (by omega)

/-- A graph on `Fin n` has a finite causal past (10f). -/
theorem finitePast_fin {n : Nat} {C U V S : Type} (G : Events.Graph (Fin n) C U V S) :
    G.FiniteCausalPast :=
  G.finiteCausalPast_of_finite ⟨List.finRange n, List.mem_finRange⟩

/-- Data of reading 9 without initial writes. -/
def noInit {E U V S : Type} {G : Events.Graph E Nat U V S} {lbls : List Label} {K : StepEvents E}
    (sid : E → S) : AccessData G lbls K :=
  ⟨sid, fun _ => false, (fun _ h => by cases h), (fun _ h _ _ => by cases h)⟩

/-! ## The memory orders of the events (C40) -/

instance (k : Events.Kind) (o : MemOrder) : Decidable (Events.Graph.OrderOK k o) := by
  cases k <;> unfold Events.Graph.OrderOK <;> infer_instance

/-- The memory order of an atomic access is permitted for its kind (C40), as a Boolean. -/
def accOrderOK {U V : Type} : Option (Events.Acc U V) → Bool
  | some (.atomic _ o k) => decide (Events.Graph.OrderOK k.kind o)
  | _ => true

/-- `OrderLegal` from its check on the events of the graph. -/
theorem orderLegal_of_check {E C U V S : Type} {G : Events.Graph E C U V S}
    (h : ∀ e, accOrderOK (G.acc? e) = true) : G.OrderLegal := by
  intro e u o k he
  have := h e
  rw [he] at this
  exact of_decide_eq_true this

/-- The kind and the memory order of an atomic access are those of an access of the list, as a
Boolean (C37, C39, C40). -/
def accStepOK {U V : Type} (xs : List LeafAccess) : Option (Events.Acc U V) → Bool
  | some (.atomic _ o k) => xs.any fun x => decide (x.order = some o ∧ x.kind = k.kind)
  | _ => true

/-- `StepOrders` from its check on the steps of the trace, when the correspondence gives no event
past the end of the trace. -/
theorem stepOrders_of_check {E U V S : Type} {ks : KShared} {L : MutexLayout} {R : CtlOrders}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} {G : Events.Graph E Nat U V S}
    {K : StepEvents E} (hK : ∀ i, lbls.length ≤ i → K.ev i = none)
    (h : ∀ i, i < lbls.length → ∀ e, K.ev i = some e →
      accStepOK (stepAcc ks L R σ lbls i) (G.acc? e) = true) : StepOrders ks L R σ lbls G K := by
  intro i e he u o k ha
  have hi : i < lbls.length := Decidable.byContradiction fun hn => by
    rw [hK i (Nat.le_of_not_lt hn)] at he; cases he
  have := h i hi e he
  rw [ha] at this
  simp only [accStepOK, List.any_eq_true, decide_eq_true_eq] at this
  obtain ⟨x, hx, ho, hk⟩ := this
  exact ⟨x, stepAccess_of_mem hx, ho, hk⟩

end Ern.ConcurrencyModel
