import Ern.ConcurrencyModel.EventLemmas

/-!
# Theorem 10: deciding the predicates of an enumerated event graph

Decision procedures for the predicates of `EventGraph` on a graph whose events, contexts and units
are enumerated, used by the witness graphs to obtain their verdicts by evaluation. Nothing here is
a rule of the specification: each instance is `decidable_of_iff` from a proved equivalence with the
definition it decides.

The transitive closure of a relation on the positions `0, …, N - 1` is computed by rounds on a
table; within `N + 1` rounds the table is closed and is then the transitive closure. A relation on
an enumerated type is first tabulated by positions, so that each pair is evaluated once.
-/

namespace Ern.ConcurrencyModel.Events

open Relation

/-! ## Transitive closure on `0, …, N - 1` -/

namespace Closure

/-- Entry `v` of a table (`false` outside it). -/
def tget (S : List Bool) (v : Nat) : Bool := (S[v]?).getD false

/-- One round from `src`: `v` is reached if it was, if it is a successor of `src`, or if it is a
successor of a reached node. -/
def round (N : Nat) (R : Nat → Nat → Bool) (src : Nat) (S : List Bool) : List Bool :=
  (List.range N).map fun v =>
    tget S v || R src v || (List.range N).any fun u => tget S u && R u v

/-- The table after `k` rounds. -/
def iter (N : Nat) (R : Nat → Nat → Bool) (src : Nat) : Nat → List Bool
  | 0 => []
  | k + 1 => round N R src (iter N R src k)

/-- Reachability from `src`, computed in `N + 1` rounds. -/
def reach (N : Nat) (R : Nat → Nat → Bool) (src v : Nat) : Bool :=
  tget (iter N R src (N + 1)) v

/-- Entry `v` after one round. -/
theorem tget_round (N : Nat) (R : Nat → Nat → Bool) (src : Nat) (S : List Bool) (v : Nat) :
    tget (round N R src S) v = (decide (v < N) &&
      (tget S v || R src v || (List.range N).any fun u => tget S u && R u v)) := by
  unfold tget round
  rw [List.getElem?_map]
  by_cases h : v < N
  · rw [List.getElem?_range h, decide_eq_true h]; rfl
  · rw [List.getElem?_eq_none_iff.2 (by rw [List.length_range]; exact Nat.le_of_not_lt h),
      decide_eq_false h]
    rfl

section
variable {N : Nat} {R : Nat → Nat → Bool} {src : Nat}

/-- No node outside `0, …, N - 1` is ever reached. -/
theorem tget_iter_ge : ∀ (k : Nat) {v : Nat}, N ≤ v → tget (iter N R src k) v = false
  | 0, _, _ => rfl
  | k + 1, v, h => by
    show tget (round N R src (iter N R src k)) v = false
    rw [tget_round, decide_eq_false (Nat.not_lt_of_le h)]; rfl

/-- A reached node is one of `0, …, N - 1`. -/
theorem lt_of_tget {k v : Nat} (h : tget (iter N R src k) v = true) : v < N :=
  Nat.lt_of_not_le fun hv => by rw [tget_iter_ge k hv] at h; cases h

/-- Every reached node is reachable. -/
theorem sound : ∀ (k : Nat) {v : Nat}, tget (iter N R src k) v = true →
    TransGen (fun a b => R a b = true) src v
  | 0, _, h => by cases h
  | k + 1, v, h => by
    change tget (round N R src (iter N R src k)) v = true at h
    rw [tget_round] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, List.any_eq_true,
      List.mem_range] at h
    obtain ⟨-, (h | h) | ⟨u, -, hu, huv⟩⟩ := h
    · exact sound k h
    · exact .single h
    · exact .tail (sound k hu) huv

/-- The table grows with the rounds. -/
theorem mono {k v : Nat} (h : tget (iter N R src k) v = true) :
    tget (iter N R src (k + 1)) v = true := by
  have hv := lt_of_tget h
  show tget (round N R src (iter N R src k)) v = true
  rw [tget_round, decide_eq_true hv, h]; rfl

/-- The table after `k` rounds is closed: one more round adds nothing. -/
def Closed (N : Nat) (R : Nat → Nat → Bool) (src k : Nat) : Prop :=
  ∀ v, v < N → tget (iter N R src (k + 1)) v = true → tget (iter N R src k) v = true

/-- A closed table contains every node reachable from `src`. -/
theorem complete (hR : ∀ a b, R a b = true → a < N ∧ b < N) {K : Nat} (hK : Closed N R src K)
    {v : Nat} (h : TransGen (fun a b => R a b = true) src v) :
    tget (iter N R src K) v = true := by
  induction h with
  | single h =>
    rename_i b
    have hb := (hR _ _ h).2
    refine hK b hb ?_
    show tget (round N R src (iter N R src K)) b = true
    rw [tget_round, decide_eq_true hb, h]
    simp
  | tail _ h ih =>
    rename_i b c _
    obtain ⟨hb, hc⟩ := hR _ _ h
    refine hK c hc ?_
    show tget (round N R src (iter N R src K)) c = true
    rw [tget_round, decide_eq_true hc]
    simp only [Bool.true_and, Bool.or_eq_true, List.any_eq_true, List.mem_range,
      Bool.and_eq_true]
    exact Or.inr ⟨b, hb, ih, h⟩

/-- A closed table stays the same at the next round. -/
theorem tget_succ_of_closed {k : Nat} (hk : Closed N R src k) (v : Nat) :
    tget (iter N R src (k + 1)) v = tget (iter N R src k) v := by
  by_cases hv : v < N
  · cases h : tget (iter N R src k) v
    · cases h' : tget (iter N R src (k + 1)) v
      · rfl
      · rw [hk v hv h'] at h; cases h
    · exact mono h
  · rw [tget_iter_ge _ (Nat.le_of_not_lt hv), tget_iter_ge _ (Nat.le_of_not_lt hv)]

/-- A closed table stays closed. -/
theorem closed_succ {k : Nat} (hk : Closed N R src k) : Closed N R src (k + 1) := by
  intro v _ h
  have heq := tget_succ_of_closed hk
  have h2 : tget (iter N R src (k + 2)) v = tget (iter N R src (k + 1)) v := by
    show tget (round N R src (iter N R src (k + 1))) v =
      tget (round N R src (iter N R src k)) v
    simp only [tget_round, heq]
  rw [← h2]; exact h

/-- A table closed at round `j` is closed at every later round. -/
theorem closed_le {j k : Nat} (hj : Closed N R src j) (hjk : j ≤ k) : Closed N R src k := by
  induction k with
  | zero => obtain rfl := Nat.le_zero.1 hjk; exact hj
  | succ k ih =>
    rcases Nat.lt_or_ge k j with h | h
    · obtain rfl : j = k + 1 := by omega
      exact hj
    · exact closed_succ (ih h)

/-- A weaker filter keeps at most as many elements. -/
theorem filter_length_le {l : List Nat} {p q : Nat → Bool}
    (h : ∀ x ∈ l, p x = true → q x = true) : (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons a l ih =>
    have ih := ih fun x hx => h x (List.mem_cons_of_mem a hx)
    rw [List.filter_cons, List.filter_cons]
    cases hp : p a
    · cases q a
      · exact ih
      · simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons]; omega
    · rw [h a List.mem_cons_self hp]
      simp only [↓reduceIte, List.length_cons]; omega

/-- A weaker filter keeps fewer elements when it misses one that the other keeps. -/
theorem filter_length_lt {l : List Nat} {p q : Nat → Bool}
    (h : ∀ x ∈ l, p x = true → q x = true) (hn : ¬ ∀ x ∈ l, q x = true → p x = true) :
    (l.filter p).length < (l.filter q).length := by
  induction l with
  | nil => exact absurd (fun x hx => by cases hx) hn
  | cons a l ih =>
    have h' := fun x hx => h x (List.mem_cons_of_mem a hx)
    rw [List.filter_cons, List.filter_cons]
    cases hp : p a <;> cases hq : q a
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine ih h' fun hl => hn fun x hx hqx => ?_
      rcases List.mem_cons.1 hx with rfl | hx
      · rw [hq] at hqx; cases hqx
      · exact hl x hx hqx
    · simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons]
      have := filter_length_le h'; omega
    · rw [h a List.mem_cons_self hp] at hq; cases hq
    · simp only [↓reduceIte, List.length_cons]
      have := ih h' fun hl => hn fun x hx hqx => by
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hp
        · exact hl x hx hqx
      omega

/-- The number of reached nodes after `k` rounds. -/
def cnt (N : Nat) (R : Nat → Nat → Bool) (src k : Nat) : Nat :=
  ((List.range N).filter (tget (iter N R src k))).length

/-- At most `N` nodes are reached. -/
theorem cnt_le (k : Nat) : cnt N R src k ≤ N := by
  unfold cnt
  have := List.length_filter_le (tget (iter N R src k)) (List.range N)
  rwa [List.length_range] at this

/-- A round adds a node while the table is not closed. -/
theorem cnt_succ {k : Nat} (hk : ¬ Closed N R src k) : cnt N R src k < cnt N R src (k + 1) := by
  refine filter_length_lt (fun x _ hx => mono hx) fun hl => hk fun v hv h => ?_
  exact hl v (List.mem_range.2 hv) h

/-- After `k` rounds, the table has been closed or has at least `k` nodes. -/
theorem closed_or_cnt : ∀ k, (∃ j, j ≤ k ∧ Closed N R src j) ∨ k ≤ cnt N R src k
  | 0 => Or.inr (Nat.zero_le _)
  | k + 1 => by
    rcases closed_or_cnt k with ⟨j, hj, hc⟩ | h
    · exact Or.inl ⟨j, Nat.le_succ_of_le hj, hc⟩
    · by_cases hc : Closed N R src k
      · exact Or.inl ⟨k, Nat.le_succ k, hc⟩
      · exact Or.inr (by have := cnt_succ hc; omega)

/-- The table is closed after `N + 1` rounds. -/
theorem closed_final : Closed N R src (N + 1) := by
  rcases closed_or_cnt (N := N) (R := R) (src := src) (N + 1) with ⟨j, hj, hc⟩ | h
  · exact closed_le hc hj
  · exact absurd (Nat.le_trans h (cnt_le _)) (Nat.not_succ_le_self N)

/-- The transitive closure of a relation on `0, …, N - 1` is computed by `reach`. -/
theorem transGen_iff_reach (hR : ∀ a b, R a b = true → a < N ∧ b < N) (v : Nat) :
    TransGen (fun a b => R a b = true) src v ↔ reach N R src v = true :=
  ⟨fun h => complete hR closed_final h, fun h => sound _ h⟩

end

end Closure

/-! ## Enumerated types -/

/-- An enumeration of a type: a list containing every element. -/
class Enum (α : Type) where
  elems : List α
  complete : ∀ a, a ∈ elems

instance (n : Nat) : Enum (Fin n) := ⟨List.finRange n, List.mem_finRange⟩

instance {α : Type} [Enum α] (p : α → Prop) [DecidablePred p] : Enum (Subtype p) where
  elems := Enum.elems.filterMap fun a => if h : p a then some ⟨a, h⟩ else none
  complete := fun ⟨a, h⟩ => List.mem_filterMap.2 ⟨a, Enum.complete a, by simp [h]⟩

namespace Enum

variable {α : Type} [Enum α]

instance (priority := low) decForall (P : α → Prop) [DecidablePred P] : Decidable (∀ a, P a) :=
  decidable_of_iff (∀ a ∈ (elems : List α), P a)
    ⟨fun h a => h a (complete a), fun h a _ => h a⟩

instance (priority := low) decExists (P : α → Prop) [DecidablePred P] : Decidable (∃ a, P a) :=
  decidable_of_iff (∃ a ∈ (elems : List α), P a)
    ⟨fun ⟨a, _, h⟩ => ⟨a, h⟩, fun ⟨a, h⟩ => ⟨a, complete a, h⟩⟩

/-- A relation tabulated by positions: each pair is evaluated once. -/
def relTab (R : α → α → Prop) [DecidableRel R] : List (List Bool) :=
  (elems : List α).map fun x => (elems : List α).map fun y => decide (R x y)

/-- The tabulated relation on positions. -/
def relB (R : α → α → Prop) [DecidableRel R] (i j : Nat) : Bool :=
  Closure.tget (((relTab R)[i]?).getD []) j

theorem relB_iff (R : α → α → Prop) [DecidableRel R] (i j : Nat) :
    relB R i j = true ↔
      ∃ x y, (elems : List α)[i]? = some x ∧ (elems : List α)[j]? = some y ∧ R x y := by
  unfold relB relTab Closure.tget
  rw [List.getElem?_map]
  cases hi : (elems : List α)[i]? with
  | none => simp
  | some x =>
    simp only [Option.map_some, Option.getD_some, List.getElem?_map]
    cases hj : (elems : List α)[j]? with
    | none => simp
    | some y => simp

variable [DecidableEq α]

/-- The position of an element in the enumeration. -/
def idx (a : α) : Nat := (elems : List α).idxOf a

theorem getElem?_idx (a : α) : (elems : List α)[idx a]? = some a := by
  have h := List.idxOf_lt_length_of_mem (complete a)
  unfold idx
  rw [List.getElem?_eq_getElem h, List.getElem_idxOf h]

/-- Reachability in the tabulated relation is the transitive closure of the relation. -/
theorem transGen_iff (R : α → α → Prop) [DecidableRel R] (a b : α) :
    TransGen R a b ↔ Closure.reach (elems : List α).length (relB R) (idx a) (idx b) = true := by
  have hbnd : ∀ i j, relB R i j = true → i < (elems : List α).length ∧ j < (elems : List α).length :=
    fun i j h => by
      obtain ⟨x, y, hx, hy, -⟩ := (relB_iff R i j).1 h
      exact ⟨(List.getElem?_eq_some_iff.1 hx).1, (List.getElem?_eq_some_iff.1 hy).1⟩
  rw [← Closure.transGen_iff_reach hbnd]
  constructor
  · intro h
    induction h with
    | single h => exact .single ((relB_iff R _ _).2 ⟨_, _, getElem?_idx _, getElem?_idx _, h⟩)
    | tail _ h ih => exact .tail ih ((relB_iff R _ _).2 ⟨_, _, getElem?_idx _, getElem?_idx _, h⟩)
  · intro h
    have key : ∀ {i j}, TransGen (fun a b => relB R a b = true) i j → ∀ x y,
        (elems : List α)[i]? = some x → (elems : List α)[j]? = some y → TransGen R x y := by
      intro i j h
      induction h with
      | single h =>
        intro x y hx hy
        obtain ⟨x', y', hx', hy', hr⟩ := (relB_iff R _ _).1 h
        rw [hx] at hx'; rw [hy] at hy'; cases hx'; cases hy'
        exact .single hr
      | tail _ h ih =>
        intro x y hx hy
        obtain ⟨z, y', hz, hy', hr⟩ := (relB_iff R _ _).1 h
        rw [hy] at hy'; cases hy'
        exact .tail (ih x z hx hz) hr
    exact key h a b (getElem?_idx a) (getElem?_idx b)

/-- The transitive closure of a decidable relation on an enumerated type is decidable. -/
instance decTransGen (R : α → α → Prop) [DecidableRel R] : DecidableRel (TransGen R) :=
  fun a b => decidable_of_iff _ (transGen_iff R a b).symm

end Enum

/-! ## Decidability of the predicates of a graph -/

instance : DecidablePred Kind.Reads := fun k => by cases k <;> unfold Kind.Reads <;> infer_instance
instance : DecidablePred Kind.Writes := fun k => by cases k <;> unfold Kind.Writes <;> infer_instance

/-- Two concrete byte ranges intersect exactly when each starts before the other ends and neither
is empty. -/
theorem Range.inter_iff (r r' : Range) : r.Inter r' ↔
    r.base < r'.base + r'.len ∧ r'.base < r.base + r.len ∧ 0 < r.len ∧ 0 < r'.len := by
  constructor
  · rintro ⟨n, ⟨h1, h2⟩, h3, h4⟩; omega
  · intro h
    refine ⟨max r.base r'.base, ⟨Nat.le_max_left _ _, ?_⟩, Nat.le_max_right _ _, ?_⟩ <;>
      simp only [Nat.max_def] <;> split <;> omega

instance (r r' : Range) : Decidable (r.Inter r') := decidable_of_iff _ (Range.inter_iff r r').symm

namespace Graph

variable {E C U V S : Type} (G : Graph E C U V S)

/-- `Reads` on the kind. -/
def readsB : Option Kind → Bool
  | some .read | some .rmw => true
  | _ => false

/-- `Writes` on the kind. -/
def writesB : Option Kind → Bool
  | some .write | some .rmw => true
  | _ => false

theorem reads_iff (e : E) : G.Reads e ↔ readsB (G.kind? e) = true := by
  unfold Reads
  cases G.kind? e with
  | none => simp [readsB]
  | some k => cases k <;> simp [readsB, Kind.Reads]

theorem writes_iff (e : E) : G.Writes e ↔ writesB (G.kind? e) = true := by
  unfold Writes
  cases G.kind? e with
  | none => simp [writesB]
  | some k => cases k <;> simp [writesB, Kind.Writes]

instance (e : E) : Decidable (G.Reads e) := decidable_of_iff _ (G.reads_iff e).symm
instance (e : E) : Decidable (G.Writes e) := decidable_of_iff _ (G.writes_iff e).symm
instance (e : E) : Decidable (G.IsRMW e) := inferInstanceAs (Decidable (_ = _))

/-- `Atomic` on the access. -/
def atomicB : Option (Acc U V) → Bool
  | some (.atomic ..) => true
  | _ => false

theorem atomic_iff (e : E) : G.Atomic e ↔ atomicB (G.acc? e) = true := by
  unfold Atomic
  cases G.acc? e with
  | none => simp [atomicB]
  | some a => cases a <;> simp [atomicB]

instance (e : E) : Decidable (G.Atomic e) := decidable_of_iff _ (G.atomic_iff e).symm

/-- `SC` on the access. -/
def scB : Option (Acc U V) → Bool
  | some (.atomic _ .seqCst _) => true
  | _ => false

theorem sc_iff (e : E) : G.SC e ↔ scB (G.acc? e) = true := by
  unfold SC
  cases G.acc? e with
  | none => simp [scB]
  | some a => cases a with
    | atomic u o k => cases o <;> simp [scB]
    | unit => simp [scB]
    | plain => simp [scB]

instance (e : E) : Decidable (G.SC e) := decidable_of_iff _ (G.sc_iff e).symm

/-- The lifecycle sources of `sw` (C32.2, C32.3) on the `sync` attributes. -/
def lifeB [DecidableEq C] : Option (SyncRole C) → Option (SyncRole C) → Bool
  | some (.spawn c), some (.start c') => decide (c = c')
  | some (.complete c), some (.join c') => decide (c = c')
  | _, _ => false

theorem life_iff [DecidableEq C] (a b : E) :
    ((∃ c, G.sync? a = some (.spawn c) ∧ G.sync? b = some (.start c)) ∨
      (∃ c, G.sync? a = some (.complete c) ∧ G.sync? b = some (.join c))) ↔
      lifeB (G.sync? a) (G.sync? b) = true := by
  cases G.sync? a with
  | none => simp [lifeB]
  | some r => cases r <;> cases G.sync? b <;> try simp [lifeB]
              all_goals (rename_i r'; cases r' <;> simp [eq_comm])

/-- The value read is the value written, both present. -/
def valB [DecidableEq V] : Option V → Option V → Bool
  | some v, some v' => decide (v = v')
  | _, _ => false

theorem val_iff [DecidableEq V] (w r : E) :
    (∃ v, G.valW w = some v ∧ G.valR r = some v) ↔ valB (G.valW w) (G.valR r) = true := by
  cases G.valW w <;> cases G.valR r <;> simp [valB, eq_comm]

/-- `range?` intersection. -/
def interB : Option Range → Option Range → Bool
  | some r, some r' => decide (r.Inter r')
  | _, _ => false

theorem conflict_iff' [DecidableEq C] (a b : E) : G.Conflict a b ↔
    G.ctx a ≠ G.ctx b ∧ interB (G.range? a) (G.range? b) = true ∧ (G.Writes a ∨ G.Writes b) := by
  unfold Conflict
  cases G.range? a <;> cases G.range? b <;> simp [interB]

instance [DecidableEq C] (a b : E) : Decidable (G.Conflict a b) :=
  decidable_of_iff _ (G.conflict_iff' a b).symm

variable [DecidableEq U]

instance (e : E) (u : U) : Decidable (G.ModOn e u) := inferInstanceAs (Decidable (_ ∧ _))
instance (e : E) (u : U) : Decidable (G.ReadOn e u) := inferInstanceAs (Decidable (_ ∧ _))

/-- `AtomicRMWOn` on the access. -/
def rmwOnB (u : U) : Option (Acc U V) → Bool
  | some (.atomic u' _ (.rmw _ _)) => decide (u' = u)
  | _ => false

theorem atomicRMWOn_iff (e : E) (u : U) : G.AtomicRMWOn e u ↔ rmwOnB u (G.acc? e) = true := by
  unfold AtomicRMWOn
  cases G.acc? e with
  | none => simp [rmwOnB]
  | some a => cases a with
    | atomic u' o k => cases k <;> simp [rmwOnB, eq_comm]
    | unit => simp [rmwOnB]
    | plain => simp [rmwOnB]

instance (e : E) (u : U) : Decidable (G.AtomicRMWOn e u) :=
  decidable_of_iff _ (G.atomicRMWOn_iff e u).symm

/-- `RelCap` on the access. -/
def relCapB (u : U) : Option (Acc U V) → Bool
  | some (.atomic u' o k) => decide (u' = u) && writesB (some k.kind) &&
      (decide (o = .release) || decide (o = .acqRel) || decide (o = .seqCst))
  | _ => false

/-- `AcqCap` on the access. -/
def acqCapB (u : U) : Option (Acc U V) → Bool
  | some (.atomic u' o k) => decide (u' = u) && readsB (some k.kind) &&
      (decide (o = .acquire) || decide (o = .acqRel) || decide (o = .seqCst))
  | _ => false

theorem writesB_some (k : Kind) : writesB (some k) = true ↔ k.Writes := by
  cases k <;> simp [writesB, Kind.Writes]

theorem readsB_some (k : Kind) : readsB (some k) = true ↔ k.Reads := by
  cases k <;> simp [readsB, Kind.Reads]

theorem relCapB_atomic (u u' : U) (o : MemOrder) (k : UKind V) :
    relCapB u (some (.atomic u' o k)) = true ↔
      u' = u ∧ k.kind.Writes ∧ (o = .release ∨ o = .acqRel ∨ o = .seqCst) := by
  rw [relCapB, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, writesB_some, and_assoc]
  cases o <;> simp

theorem acqCapB_atomic (u u' : U) (o : MemOrder) (k : UKind V) :
    acqCapB u (some (.atomic u' o k)) = true ↔
      u' = u ∧ k.kind.Reads ∧ (o = .acquire ∨ o = .acqRel ∨ o = .seqCst) := by
  rw [acqCapB, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, readsB_some, and_assoc]
  cases o <;> simp

theorem relCap_iff (e : E) (u : U) : G.RelCap e u ↔ relCapB u (G.acc? e) = true := by
  unfold RelCap
  cases G.acc? e with
  | none => simp [relCapB]
  | some a => cases a with
    | atomic u' o k =>
      rw [relCapB_atomic]
      constructor
      · rintro ⟨o', k', h, hw, ho⟩
        injection h with h; injection h with h1 h2 h3; subst h1 h2 h3; exact ⟨rfl, hw, ho⟩
      · rintro ⟨rfl, hw, ho⟩; exact ⟨o, k, rfl, hw, ho⟩
    | unit => simp [relCapB]
    | plain => simp [relCapB]

theorem acqCap_iff (e : E) (u : U) : G.AcqCap e u ↔ acqCapB u (G.acc? e) = true := by
  unfold AcqCap
  cases G.acc? e with
  | none => simp [acqCapB]
  | some a => cases a with
    | atomic u' o k =>
      rw [acqCapB_atomic]
      constructor
      · rintro ⟨o', k', h, hr, ho⟩
        injection h with h; injection h with h1 h2 h3; subst h1 h2 h3; exact ⟨rfl, hr, ho⟩
      · rintro ⟨rfl, hr, ho⟩; exact ⟨o, k, rfl, hr, ho⟩
    | unit => simp [acqCapB]
    | plain => simp [acqCapB]

instance (e : E) (u : U) : Decidable (G.RelCap e u) := decidable_of_iff _ (G.relCap_iff e u).symm
instance (e : E) (u : U) : Decidable (G.AcqCap e u) := decidable_of_iff _ (G.acqCap_iff e u).symm

instance (a b : E) : Decidable (G.Loc a b) :=
  decidable_of_iff ((G.unitOf a).isSome ∧ G.unitOf a = G.unitOf b) (by
    unfold Loc
    cases ha : G.unitOf a <;> cases hb : G.unitOf b <;> simp [eq_comm])

variable [Enum E] [DecidableEq E] [Enum U] [DecidableEq C] [DecidableEq V]
  [DecidableRel G.po] [DecidableRel G.rf] [DecidableRel G.mo]

instance (u : U) (h m : E) : Decidable (G.RSMember u h m) := by
  unfold RSMember; infer_instance

instance : DecidableRel G.SW := fun a b =>
  decidable_of_iff ((∃ u m, G.RelCap a u ∧ G.AcqCap b u ∧ G.RSMember u a m ∧ G.rf m b) ∨
    lifeB (G.sync? a) (G.sync? b) = true) (by unfold SW; rw [← G.life_iff a b])

instance : DecidableRel G.PoSw := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

instance : DecidableRel G.HB := fun a b => Enum.decTransGen G.PoSw a b

instance (a b : E) : Decidable (G.Race a b) := by unfold Race; infer_instance

instance : DecidableRel G.HBLoc := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

instance : DecidableRel G.RB := fun a b => by unfold RB; infer_instance

instance : DecidableRel G.EcoBase := fun a b => by unfold EcoBase; infer_instance

instance : DecidableRel G.ECO := fun a b => Enum.decTransGen G.EcoBase a b

instance : DecidableRel G.SCB := fun a b => by unfold SCB; infer_instance

instance : DecidableRel G.PSC := fun a b => by unfold PSC; infer_instance

instance : DecidableRel G.PoRf := fun a b => by unfold PoRf; infer_instance

instance : Decidable G.RfWF :=
  decidable_of_iff ((∀ w r, G.rf w r → ∃ u, G.ModOn w u ∧ G.ReadOn r u) ∧
    (∀ r u, G.ReadOn r u → (∃ w, G.rf w r) ∧ ∀ w w', G.rf w r → G.rf w' r → w = w') ∧
    (∀ w r, G.rf w r → valB (G.valW w) (G.valR r) = true)) (by
      unfold RfWF
      exact and_congr Iff.rfl (and_congr Iff.rfl
        (forall_congr' fun w => forall_congr' fun r => imp_congr_right fun _ =>
          (G.val_iff w r).symm)))

instance : Decidable G.MoTotal := by
  unfold MoTotal
  haveI : ∀ u : U, Decidable (∀ a b c : E, G.ModOn a u → G.ModOn b u → G.ModOn c u →
      G.mo a b → G.mo b c → G.mo a c) := fun _ => inferInstance
  haveI : ∀ u : U, Decidable (∀ a b : E, G.ModOn a u → G.ModOn b u → a ≠ b →
      G.mo a b ∨ G.mo b a) := fun _ => inferInstance
  infer_instance
instance : Decidable G.RmwAtomic := by unfold RmwAtomic; infer_instance
instance : Decidable G.Coherence := by unfold Coherence; infer_instance
instance : Decidable G.HbIrrefl := by unfold HbIrrefl; infer_instance
instance : Decidable G.NoThinAir := by unfold NoThinAir Acyclic; infer_instance
instance : Decidable G.SCConsistent := by unfold SCConsistent Acyclic; infer_instance
instance : Decidable G.EventConsistent := by unfold EventConsistent; infer_instance

end Graph

/-! ## Graphs on `Fin n` given by lists -/

/-- An event graph on `Fin n` given by its events and by the lists of its `rf` and `mo` edges;
`po` is the order of the indices within each context (C28). -/
structure ListGraph (n : Nat) (C U V S : Type) where
  ev : Fin n → Event C U V S
  uRange : U → Range
  rf : List (Fin n × Fin n)
  mo : List (Fin n × Fin n)

/-- The event graph of a `ListGraph`: `po` relates two events of the same context by increasing
index; it is a strict order, total on each context (C28). -/
def ListGraph.toGraph {n : Nat} {C U V S : Type} [DecidableEq C] (W : ListGraph n C U V S) :
    Graph (Fin n) C U V S where
  ev := W.ev
  uRange := W.uRange
  po a b := (W.ev a).ctx = (W.ev b).ctx ∧ a < b
  rf a b := (a, b) ∈ W.rf
  mo a b := (a, b) ∈ W.mo
  po_irrefl a h := Nat.lt_irrefl _ h.2
  po_trans h₁ h₂ := ⟨h₁.1.trans h₂.1, Nat.lt_trans h₁.2 h₂.2⟩
  po_ctx h := h.1
  po_total {a b} hc hne := by
    rcases Nat.lt_or_ge a b with h | h
    · exact .inl ⟨hc, h⟩
    · exact .inr ⟨hc.symm, Nat.lt_of_le_of_ne h fun e => hne (Fin.ext e.symm)⟩

instance {n : Nat} {C U V S : Type} [DecidableEq C] (W : ListGraph n C U V S) :
    DecidableRel W.toGraph.po := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

instance {n : Nat} {C U V S : Type} [DecidableEq C] (W : ListGraph n C U V S) :
    DecidableRel W.toGraph.rf := fun _ _ => inferInstanceAs (Decidable (_ ∈ _))

instance {n : Nat} {C U V S : Type} [DecidableEq C] (W : ListGraph n C U V S) :
    DecidableRel W.toGraph.mo := fun _ _ => inferInstanceAs (Decidable (_ ∈ _))

end Ern.ConcurrencyModel.Events
