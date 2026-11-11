/-!
# Decision of a transitive closure on a finite set of nodes

Brief of milestone 4, slice 2 (layer E), task 1 (`formal/reports/spec2-m4-eventmodel.md`): the
decision of `hb` must not assume that edges increase in an enumeration order. For a relation on
the nodes `0, …, N - 1`, the reachable set from a source is computed by rounds on a table; within
`N + 1` rounds the table is closed under the relation, and it is then the transitive closure. The
completeness argument counts the true entries of the table, which grow at every round until the
table is closed.
-/

set_option autoImplicit false

namespace Ern.Concurrency.EventModel

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
    Relation.TransGen (fun a b => R a b = true) src v
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

/-- Decidability of `Closed`. -/
instance (k : Nat) : Decidable (Closed N R src k) := by unfold Closed; infer_instance

/-- A closed table contains every node reachable from `src`. -/
theorem complete (hR : ∀ a b, R a b = true → a < N ∧ b < N) {K : Nat} (hK : Closed N R src K)
    {v : Nat} (h : Relation.TransGen (fun a b => R a b = true) src v) :
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

/-! ## Counting -/

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
    Relation.TransGen (fun a b => R a b = true) src v ↔ reach N R src v = true :=
  ⟨fun h => complete hR closed_final h, fun h => sound _ h⟩

end

end Ern.Concurrency.EventModel
