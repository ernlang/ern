import Ern.ConcurrencyModel.Library

/-!
# Theorem 8: atomic operations as step cases (C37–C40; `OB-C03` for the step cases)

Theorem 8 of `formal/DESIGN.md`, Milestone 4, target theorems: `readShared` (C37), the success of
an atomic `writeShared` (C39), and the failure of a compare-and-exchange (C39), with the
rejections of C38 and C40. Theorem 2 covers these cases (`lstep_kInvCA`, `lstep_inv`).
-/

namespace Ern.ConcurrencyModel

open Ern.MemoryModel.Access

/-! ## `readShared` (C37) -/

/-- **Theorem 8**, `readShared` (C37, C40):

1. `ok` exactly under its preconditions, and with the state unchanged;
2. `reject` otherwise, in particular on `Synchronized` or `Confined` storage, by its own rule;
3. no `fail`;
4. the observed value is not constrained: for every value, the labelled step exists exactly when
   the `ok` step does, and it changes neither the state nor the registries.

Fragment: every state, every registry. -/
theorem readShared_case {ks : KShared} {L : MutexLayout} {s : SC} {reg : SyncReg}
    {ar : ArenaReg} {c a l : Nat} {order : MemOrder} :
    (ReadSharedPre ks s c a l order → ReadSharedRel ks s c a l order (.ok s)) ∧
      (∀ s', ReadSharedRel ks s c a l order (.ok s') → s' = s) ∧
      (¬ ReadSharedPre ks s c a l order → ReadSharedRel ks s c a l order .reject) ∧
      ((ks.SharedDiscipline l = some .synchronized ∨ ks.SharedDiscipline l = some .confined) →
        ReadSharedRel ks s c a l order .reject) ∧
      (∀ o, ReadSharedRel ks s c a l order o → o ≠ .fail) ∧
      (∀ v st', LStep ks L (.readShared c a l order v) (s, reg, ar) st' ↔
        ReadSharedStep ks s c a l order (.ok s) ∧ st' = (s, reg, ar)) := by
  have hrej : ¬ ReadSharedPre ks s c a l order → ReadSharedRel ks s c a l order .reject :=
    fun h => .reject h
  refine ⟨fun h => .ok h, fun _ h => readShared_ok_eq h, hrej, fun hd => hrej fun hp => ?_,
    (fun o h e => by subst e; cases h), fun v st' => ⟨fun h => ?_, fun ⟨h, e⟩ => by subst e; exact .readShared h⟩⟩
  · obtain ⟨sz, al, ha⟩ := hp.atomic
    rcases hd with hd | hd <;> rw [hd] at ha <;> cases ha
  · cases h with
    | readShared h => exact ⟨h, rfl⟩

/-! ## Success of an atomic `writeShared` (C39) and its rejections (C38, C40) -/

/-- A singleton region is classified consistently (C38). -/
theorem singleClass_singleton {ks : KShared} {l : Nat} (h : ks.SharedDiscipline l ≠ none) :
    SingleClass ks [l] :=
  ⟨fun l' hl' => by rw [List.mem_singleton.1 hl']; exact h, fun a ha b hb => by
    rw [List.mem_singleton.1 ha, List.mem_singleton.1 hb]⟩

/-- A region of only `Synchronized` (or only `Confined`) leaves is classified consistently. -/
theorem singleClass_const {ks : KShared} {region : List Nat} {d : Discipline}
    (h : ∀ l ∈ region, ks.SharedDiscipline l = some d) : SingleClass ks region :=
  ⟨fun l hl => by rw [h l hl]; exact Option.some_ne_none _, fun a ha b hb => by
    rw [h a ha, h b hb]⟩

/-- Two distinct members of a list make a sublist of length at least two. -/
theorem two_le_length_filter {p : Nat → Bool} {l : List Nat} {a b : Nat} (hab : a ≠ b)
    (ha : a ∈ l) (hb : b ∈ l) (hpa : p a = true) (hpb : p b = true) :
    2 ≤ (l.filter p).length := by
  have ha' : a ∈ l.filter p := List.mem_filter.2 ⟨ha, hpa⟩
  have hb' : b ∈ l.filter p := List.mem_filter.2 ⟨hb, hpb⟩
  cases hf : l.filter p with
  | nil => rw [hf] at ha'; cases ha'
  | cons x t =>
    cases t with
    | nil =>
      rw [hf, List.mem_singleton] at ha' hb'
      exact absurd (ha'.trans hb'.symm) hab
    | cons y u => simp

/-- **Theorem 8**, success of an atomic `writeShared` (C39, C35): a successful concurrent
`writeShared` is the O11 step of Spec 1 §68 executed by the same context, with the same effect;
no new mutation primitive. Fragment: every state. -/
theorem atomic_success_is_o11 {ks : KShared} {s s' : SC} {c a : Nat} {region : List Nat}
    {ord : Option MemOrder} {kind : WriteKind}
    (h : WriteSharedCStep ks s c a region ord kind (.ok s')) :
    opStepC ks.toK (.writeShared a region) c s (.ok s') ∧ s' = writeSharedCEff s c region :=
  ⟨writeSharedC_ok_kernel h, (Guarded.ok_iff.1 h).2⟩

/-- **Theorem 8** (C40): on a single `Atomic` leaf, an order outside the row of the operation is a
static `reject`. -/
theorem atomic_order_rejected {ks : KShared} {s : SC} {c a l sz al : Nat} {o : MemOrder}
    {kind : WriteKind} (hd : ks.SharedDiscipline l = some (.atomic sz al))
    (ho : ¬ WriteOrderOK kind o) :
    WriteSharedCRel ks s c a [l] (some o) kind .reject := by
  refine .reject fun hp => ?_
  have hd' := hp.discipline
  cases kind with
  | store =>
    obtain ⟨-, -, -, hann, -, -⟩ := hd'
    exact ho (hann ⟨l, List.mem_singleton_self _, by unfold AtomicLeaf; rw [hd]; rfl⟩)
  | rmw v =>
    obtain ⟨-, -, -, -, -, -, hann⟩ := hd'
    exact ho hann

/-- **Theorem 8** (C38): a `writeShared` whose region contains more than one `Atomic` leaf is
`reject`, whatever the order and the kind, a composite contract included. -/
theorem multi_atomic_rejected {ks : KShared} {s : SC} {c a : Nat} {region : List Nat}
    {ord : Option MemOrder} {kind : WriteKind} {l₁ l₂ : Nat} (h12 : l₁ ≠ l₂)
    (h₁ : l₁ ∈ region) (h₂ : l₂ ∈ region) (ha₁ : AtomicLeaf ks l₁) (ha₂ : AtomicLeaf ks l₂) :
    WriteSharedCRel ks s c a region ord kind .reject := by
  refine .reject fun hp => ?_
  have hd' := hp.discipline
  cases kind with
  | store =>
    obtain ⟨-, -, hle, -, -, -⟩ := hd'
    have := two_le_length_filter (p := fun l => decide (AtomicLeaf ks l)) h12 h₁ h₂
      (decide_eq_true ha₁) (decide_eq_true ha₂)
    omega
  | rmw v =>
    obtain ⟨l, -, -, e1, -, -, -⟩ := hd'
    subst e1
    rw [List.mem_singleton] at h₁ h₂; exact h12 (h₁.trans h₂.symm)

/-- **Theorem 8** (C38): a region that combines `SharedDiscipline` classes, which the composite
contract does not admit, is `reject`, whatever the order and the kind. -/
theorem mixed_rejected {ks : KShared} {s : SC} {c a : Nat} {region : List Nat}
    {ord : Option MemOrder} {kind : WriteKind} (hm : MixedClasses ks region)
    (hc : ¬ CompositeAdmits ks region) :
    WriteSharedCRel ks s c a region ord kind .reject := by
  refine .reject fun hp => ?_
  have hd' := hp.discipline
  cases kind with
  | store =>
    obtain ⟨-, -, -, -, -, hcc⟩ := hd'
    exact hc (hcc hm)
  | rmw v =>
    obtain ⟨l, sz, al, e1, e2, -, -⟩ := hd'
    subst e1; exact hm.2 (singleClass_singleton (by rw [e2]; exact Option.some_ne_none _))

/-- **Theorem 8** (C39, "Operation kind and atomic memory-order annotations"): for a concurrent
`writeShared` whose region is of a single `K_C.SharedDiscipline` class, the class of its leaf `l`
(the region is not empty):

1. on `Atomic` storage the annotation is required: without one, the outcome is `reject`;
2. on `Synchronized` or `Confined` storage the annotation does not apply: with one, the outcome is
   `reject`.

Fragment: every state, every contract `K_C`, every kind of modification. -/
theorem annotation_rejected {ks : KShared} {s : SC} {c a : Nat} {region : List Nat}
    {kind : WriteKind} {l : Nat} (hsc : SingleClass ks region) (hl : l ∈ region) :
    (AtomicLeaf ks l → ∀ o, WriteSharedCStep ks s c a region none kind o ↔ o = .reject) ∧
    ((ks.SharedDiscipline l = some .synchronized ∨ ks.SharedDiscipline l = some .confined) →
      ∀ ord o, WriteSharedCStep ks s c a region (some ord) kind o ↔ o = .reject) := by
  have key : ∀ {ord : Option MemOrder}, ¬ WriteDisciplineOK ks region ord kind → ∀ o,
      WriteSharedCStep ks s c a region ord kind o ↔ o = .reject := fun hn o =>
    ⟨fun h => by
      cases h with
      | ok hp => exact absurd hp.discipline hn
      | reject => rfl,
     fun e => by subst e; exact .reject fun hp => hn hp.discipline⟩
  refine ⟨fun hat => key ?_, fun hd ord => key ?_⟩
  · intro hdo
    cases kind with
    | store => exact hdo.2.2.2.1 ⟨l, hl, hat⟩
    | rmw v => exact hdo.choose_spec.choose_spec.choose_spec.2.2.2
  · intro hdo
    have hcls : (ks.SharedDiscipline l).map Discipline.cls ≠ some 0 := by
      rcases hd with hd | hd <;> rw [hd] <;> simp [Discipline.cls]
    cases kind with
    | store =>
      have hnone := hdo.2.2.2.2.1 fun l' hl' hat' => hcls (by rw [hsc.2 l hl l' hl']; exact hat')
      cases hnone
    | rmw v =>
      obtain ⟨l', sz, al, e1, e2, -, -⟩ := hdo
      subst e1; rw [List.mem_singleton.1 hl] at hcls; rw [e2] at hcls; exact hcls rfl

/-- **Theorem 8** (C39): the concurrent `writeShared` has no `fail` outcome. -/
theorem writeSharedC_no_fail {ks : KShared} {s : SC} {c a : Nat} {region : List Nat}
    {ord : Option MemOrder} {kind : WriteKind} (o : Outcome3 SC)
    (h : WriteSharedCRel ks s c a region ord kind o) : o ≠ .fail := by
  intro e; subst e; cases h

/-! ## Failure of a compare-and-exchange (C39) -/

/-- **Theorem 8** (C39, C40): a compare-and-exchange whose branch is a failure and whose orders
are in their rows is the `readShared` observation of the leaf with the failure order: an `ok`
outcome leaves the state unchanged, and the labelled step keeps both registries (no mutation, no
grant). An order outside its row is a static `reject` whatever the branch. -/
theorem cas_failure_case {ks : KShared} {L : MutexLayout} {s s' : SC} {reg : SyncReg}
    {ar : ArenaReg} {st' : SC × SyncReg × ArenaReg} {c a l v : Nat} {succ fail : MemOrder} :
    (CasOrdersOK succ fail →
      (CasStep ks s c a l succ fail (.failure v) (.ok s') ↔ ReadSharedStep ks s c a l fail (.ok s'))) ∧
      (CasStep ks s c a l succ fail (.failure v) (.ok s') → s' = s) ∧
      (LStep ks L (.cas c a l succ fail (.failure v)) (s, reg, ar) st' → st' = (s, reg, ar)) ∧
      (¬ CasOrdersOK succ fail → ∀ br o, CasStep ks s c a l succ fail br o → o = .reject) := by
  refine ⟨fun ho => ⟨fun h => ?_, fun h => .inr ⟨ho, h⟩⟩, fun h => ?_, fun h => ?_,
    fun hn br o h => ?_⟩
  · rcases h with ⟨hn, -⟩ | ⟨-, h⟩
    · exact absurd ho hn
    · exact h
  · rcases h with ⟨-, h⟩ | ⟨-, h⟩
    · cases h
    · exact readShared_ok_eq h
  · cases h with
    | cas h =>
      rcases h with ⟨-, h⟩ | ⟨-, h⟩
      · cases h
      · rw [readShared_ok_eq h]
  · rcases h with ⟨-, e⟩ | ⟨ho, -⟩
    · exact e
    · exact absurd ho hn

end Ern.ConcurrencyModel
