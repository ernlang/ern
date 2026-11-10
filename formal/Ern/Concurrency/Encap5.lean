import Ern.Concurrency.Cap

/-!
# Extended encapsulation and capability without `guarded`

Additive definitions of the brief of milestone 4, task 3, beside `Encap` and
`EncapsulatedTrace`, which are unchanged:

- `GuardedExcl` is a proposition of the brief, absent from WC5 (WC5 C22.1 excludes only `derive`
  and `split` of source `guarded`); it is tested, not decided;
- `CtlExcl` is WC5 C22, requirement 4 (D-C6);
- `Attr5` and `cap5` are `Attr` and `cap` (WC5 C43) in which the `guarded` authority of a live
  entry is attributable to no context.
-/

namespace Ern.Concurrency

open Ern.MemoryModel.Access

/-- The proposition `GuardedExcl` of the brief of milestone 4 (task 3), absent from WC5: for each
live entry, the step is not a kernel operation that exercises `guarded` as the authority argument
of its precondition (Spec 1 §43, `ExercisableAt`). The kernel operations with such an argument are
`derive` (§60.1), `split` (§61.1), `read` (§66.2), `write` (§67.1) and `writeShared` (§68.2);
`release` (§62.2), `store` (§65.1) and `depend` (§64.2) constrain their authority argument
otherwise, and the other operations have none. -/
def GuardedExcl (st : SC × SyncReg) : Label → Prop
  | .kernel _ (.derive a _ _) | .kernel _ (.split a _) | .kernel _ (.read a _)
  | .kernel _ (.write a _) | .kernel _ (.writeShared a _) =>
    ∀ e ∈ st.2, e.Live st.1 → a ≠ e.guarded
  | _ => True

/-- Decidability of `GuardedExcl`. -/
instance (st : SC × SyncReg) (lbl : Label) : Decidable (GuardedExcl st lbl) := by
  unfold GuardedExcl; split <;> infer_instance

/-- WC5 C22, requirement 4 (D-C6): for each live entry, the step is not a raw `read3`, `write3` or
`writeShared` whose leaves contain the controller leaf `ControlOf(entry)`. -/
def CtlExcl (L : MutexLayout) (st : SC × SyncReg) : Label → Prop
  | .kernel _ (.read _ ls) | .kernel _ (.write _ ls) | .kernel _ (.writeShared _ ls) =>
    ∀ e ∈ st.2, e.Live st.1 → OptP (ControlOf L st.1 e) (fun ctl => ctl ∉ ls) True
  | _ => True

/-- Decidability of `CtlExcl` (WC5 C22.4). -/
instance (L : MutexLayout) (st : SC × SyncReg) (lbl : Label) : Decidable (CtlExcl L st lbl) := by
  unfold CtlExcl; split <;> infer_instance

/-- `Encap5` (brief of milestone 4, task 3): `Encap` (WC4 C22.1–C22.3, C22.5), `GuardedExcl` and
`CtlExcl` (WC5 C22.4). -/
def Encap5 (L : MutexLayout) (st : SC × SyncReg) (lbl : Label) : Prop :=
  Encap L st lbl ∧ GuardedExcl st lbl ∧ CtlExcl L st lbl

/-- `EncapsulatedTrace5`: a run every step of which satisfies `Encap5` in the state where it is
taken, of the same form as `EncapsulatedTrace` (WC4 C22, C23). -/
inductive EncapsulatedTrace5 (k : K) (L : MutexLayout) :
    SC × SyncReg × ArenaReg → List Label → SC × SyncReg × ArenaReg → Prop where
  | nil {st : SC × SyncReg × ArenaReg} : EncapsulatedTrace5 k L st [] st
  | cons {st st₁ st₂ : SC × SyncReg × ArenaReg} {lbl : Label} {lbls : List Label} :
      Encap5 L (st.1, st.2.1) lbl → LStep k L lbl st st₁ → EncapsulatedTrace5 k L st₁ lbls st₂ →
      EncapsulatedTrace5 k L st (lbl :: lbls) st₂

/-- Every `EncapsulatedTrace5` is an `EncapsulatedTrace`: the theorems T2 to T7 stated on
`EncapsulatedTrace` apply to it. -/
theorem encapsulatedTrace5_imp {k : K} {L : MutexLayout} {st st' : SC × SyncReg × ArenaReg}
    {lbls : List Label} (h : EncapsulatedTrace5 k L st lbls st') :
    EncapsulatedTrace k L st lbls st' := by
  induction h with
  | nil => exact .nil
  | cons he hs _ ih => exact .cons he.1 hs ih

/-- An `EncapsulatedTrace5` extended by one step satisfying `Encap5`. -/
theorem EncapsulatedTrace5.snoc {k : K} {L : MutexLayout} {st st' st'' : SC × SyncReg × ArenaReg}
    {lbls : List Label} {lbl : Label} (h : EncapsulatedTrace5 k L st lbls st')
    (he : Encap5 L (st'.1, st'.2.1) lbl) (hs : LStep k L lbl st' st'') :
    EncapsulatedTrace5 k L st (lbls ++ [lbl]) st'' := by
  induction h with
  | nil => exact .cons he hs .nil
  | cons he' hs' _ ih => exact .cons he' hs' (ih he hs)

/-! ## Capability without `guarded` -/

/-- `a` is the `guarded` authority of no live entry of `reg` (WC4 C12). -/
def NotGuarded (s : SC) (reg : SyncReg) (a : Nat) : Prop := ∀ e ∈ reg, e.Live s → a ≠ e.guarded

/-- Decidability of `NotGuarded`. -/
instance (s : SC) (reg : SyncReg) (a : Nat) : Decidable (NotGuarded s reg a) := by
  unfold NotGuarded; infer_instance

/-- `Attr5` (brief of milestone 4, task 3): `Attr` (WC5 C43) in which the `guarded` authority of a
live entry is attributable to no context. Grants are ordinary authorities and remain
attributable. -/
inductive Attr5 (s : SC) (reg : SyncReg) (c : Nat) : Nat → Mode → Prop where
  | base {a : Nat} {m : Mode} {y : Authority} {f : Nat} : NotGuarded s reg a → s.A[a]? = some y →
      y.active = true → m.le y.mode → y.holder = .frame f → f ∈ s.stk c → Attr5 s reg c a m
  | held {a p b : Nat} {m : Mode} {y : Authority} : NotGuarded s reg a → s.A[a]? = some y →
      y.active = true → m.le y.mode → y.holder = .place p → Attr5 s reg c b m →
      (∀ l ∈ footprint s.P p, Allows (effective s.flat b l) m) → Attr5 s reg c a m

/-- One step of `Attr5 · m` read on a Boolean premise (decision procedure for `Attr5`, on the
pattern of `exR`, Spec 1 §43). -/
def attr5R (s : SC) (reg : SyncReg) (c : Nat) (m : Mode) (E : Nat → Bool) (a : Nat) : Bool :=
  decide (NotGuarded s reg a) && match s.A[a]? with
  | some y => y.active && decide (m.le y.mode) && match y.holder with
    | .frame f => decide (f ∈ s.stk c)
    | .place p => (List.range s.A.length).any fun b =>
        decide (∀ l ∈ footprint s.P p, Allows (effective s.flat b l) m) && E b
  | none => false

/-- `attr5R` is a bounded monotone rule (decision procedure for `Attr5`). -/
theorem attr5R_rule (s : SC) (reg : SyncReg) (c : Nat) (m : Mode) :
    KRule s.A.length (attr5R s reg c m) where
  mono p q hpq a h := by
    unfold attr5R at h ⊢
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
    unfold attr5R at h
    simp only [Bool.and_eq_true] at h
    have h2 := h.2
    split at h2
    · exact lt_of_getElem? ‹_›
    · cases h2
  loc p q hpq a := by
    unfold attr5R; congr 1; split
    · congr 1; split
      · rfl
      · exact any_congr' fun b hb => by rw [hpq b (List.mem_range.1 hb)]
    · rfl

/-- Soundness of the iteration for `Attr5`. -/
theorem attr5_of_kiter (s : SC) (reg : SyncReg) (c : Nat) (m : Mode) :
    ∀ k a, kiter (attr5R s reg c m) k a = true → Attr5 s reg c a m
  | 0, _, h => by simp [kiter] at h
  | k + 1, a, h => by
    simp only [kiter, attr5R, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hg, h⟩ := h
    split at h
    · rename_i y hy
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨ha, hm⟩, h⟩ := h
      split at h
      · rename_i f hf; exact .base hg hy ha hm hf (by simpa using h)
      · rename_i p hp
        simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨b, -, hc, hb⟩ := h
        exact .held hg hy ha hm hp (attr5_of_kiter s reg c m k b hb) hc
    · cases h

/-- The frame-held case of `attr5R`. -/
theorem attr5R_base {s : SC} {reg : SyncReg} {c : Nat} {m : Mode} {E : Nat → Bool} {a f : Nat}
    {y : Authority} (hg : NotGuarded s reg a) (hy : s.A[a]? = some y) (ha : y.active = true)
    (hm : m.le y.mode) (hf : y.holder = .frame f) (hin : f ∈ s.stk c) :
    attr5R s reg c m E a = true := by
  simp only [attr5R, hy, ha, hf, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hg, hm, hin⟩

/-- The place-held case of `attr5R`. -/
theorem attr5R_held {s : SC} {reg : SyncReg} {c : Nat} {m : Mode} {E : Nat → Bool} {a p b : Nat}
    {y : Authority} (hg : NotGuarded s reg a) (hy : s.A[a]? = some y) (ha : y.active = true)
    (hm : m.le y.mode) (hp : y.holder = .place p) (hb : b < s.A.length)
    (hc : ∀ l ∈ footprint s.P p, Allows (effective s.flat b l) m) (hE : E b = true) :
    attr5R s reg c m E a = true := by
  simp only [attr5R, hy, ha, hp, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq,
    List.any_eq_true, List.mem_range]
  exact ⟨hg, hm, b, hb, hc, hE⟩

/-- `Attr5` is computed by `|A| + 1` steps of `attr5R`. -/
theorem attr5_iff {s : SC} {reg : SyncReg} {c a : Nat} {m : Mode} :
    Attr5 s reg c a m ↔ kiter (attr5R s reg c m) (s.A.length + 1) a = true := by
  refine ⟨fun h => ?_, attr5_of_kiter s reg c m _ a⟩
  induction h with
  | base hg hy ha hm hf hin => exact attr5R_base hg hy ha hm hf hin
  | held hg hy ha hm hp _ hc ih =>
    rw [← kiter_fix (attr5R_rule s reg c _)]
    exact attr5R_held hg hy ha hm hp (kiter_bound (attr5R_rule s reg c _) _ _ ih) hc ih

/-- Decidability of `Attr5`. -/
instance (s : SC) (reg : SyncReg) (c a : Nat) (m : Mode) : Decidable (Attr5 s reg c a m) :=
  decidable_of_iff _ attr5_iff.symm

/-- `CapAt` with `Attr5` (brief of milestone 4, task 3). -/
def CapAt5 (s : SC) (reg : SyncReg) (c l : Nat) (m : Mode) : Prop :=
  ∃ x ∈ List.range s.A.length, Attr5 s reg c x m ∧ Allows (effective s.flat x l) m

/-- Decidability of `CapAt5`. -/
instance (s : SC) (reg : SyncReg) (c l : Nat) (m : Mode) : Decidable (CapAt5 s reg c l m) := by
  unfold CapAt5; infer_instance

/-- `cap5` (brief of milestone 4, task 3): `cap` (WC5 C43) with `Attr5`. -/
def cap5 (s : SC) (reg : SyncReg) (c l : Nat) : Option Mode :=
  if CapAt5 s reg c l .modify then some .modify else if CapAt5 s reg c l .observe then some .observe
  else none

end Ern.Concurrency
