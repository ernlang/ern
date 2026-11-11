import Ern.Concurrency.CapDrop

/-!
# Test of a corrected `GuardedExcl`

`GuardedExcl` (brief of milestone 4, task 3) excludes the steps whose authority argument is a live
`guarded`; the third clause of Spec 1 §43 is recursive along the holder chain, and an authority
stored in the protected storage is exercisable through `guarded` (`Corpus/GuardedChain.lean`).
This module tests the correction proposed in `formal/reports/spec2-m4-handoff.md`: the authority
argument of `derive`, `split`, `read`, `write` and `writeShared` must be exercisable from the
current frame by a holder chain that contains no live `guarded` (`Exer5`). It is a proposition of
the report, absent from WC5 and from the brief, tested here and not decided. Beside it, the
definitions of the brief (`GuardedExcl`, `Encap5`, `EncapsulatedTrace5`) are unchanged.
-/

namespace Ern.Concurrency

open Ern.MemoryModel.Access

/-! ## Exercise without a live `guarded` -/

/-- `ExercisableAt` (Spec 1 §43) read from the current frame of `c`, by a holder chain none of whose
authorities is the `guarded` of a live entry of `reg` (WC4 C12). -/
inductive Exer5 (s : SC) (reg : SyncReg) (c : Nat) : Nat → Mode → Prop where
  | base {a : Nat} {m : Mode} {y : Authority} : NotGuarded s reg a → s.A[a]? = some y →
      y.active = true → m.le y.mode → y.holder = .frame (s.view c).top → Exer5 s reg c a m
  | held {a p b : Nat} {m : Mode} {y : Authority} : NotGuarded s reg a → s.A[a]? = some y →
      y.active = true → m.le y.mode → y.holder = .place p → Exer5 s reg c b m →
      (∀ l ∈ footprint s.P p, Allows (effective s.flat b l) m) → Exer5 s reg c a m

/-- One step of `Exer5 · m` read on a Boolean premise (decision procedure, on the pattern of `exR`,
Spec 1 §43). -/
def exer5R (s : SC) (reg : SyncReg) (c : Nat) (m : Mode) (E : Nat → Bool) (a : Nat) : Bool :=
  decide (NotGuarded s reg a) && match s.A[a]? with
  | some y => y.active && decide (m.le y.mode) && match y.holder with
    | .frame f => decide (f = (s.view c).top)
    | .place p => (List.range s.A.length).any fun b =>
        decide (∀ l ∈ footprint s.P p, Allows (effective s.flat b l) m) && E b
  | none => false

/-- `exer5R` is a bounded monotone rule. -/
theorem exer5R_rule (s : SC) (reg : SyncReg) (c : Nat) (m : Mode) :
    KRule s.A.length (exer5R s reg c m) where
  mono p q hpq a h := by
    unfold exer5R at h ⊢
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
    unfold exer5R at h
    simp only [Bool.and_eq_true] at h
    have h2 := h.2
    split at h2
    · exact lt_of_getElem? ‹_›
    · cases h2
  loc p q hpq a := by
    unfold exer5R; congr 1; split
    · congr 1; split
      · rfl
      · exact any_congr' fun b hb => by rw [hpq b (List.mem_range.1 hb)]
    · rfl

/-- Soundness of the iteration for `Exer5`. -/
theorem exer5_of_kiter (s : SC) (reg : SyncReg) (c : Nat) (m : Mode) :
    ∀ k a, kiter (exer5R s reg c m) k a = true → Exer5 s reg c a m
  | 0, _, h => by simp [kiter] at h
  | k + 1, a, h => by
    simp only [kiter, exer5R, Bool.and_eq_true, decide_eq_true_eq] at h
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
        exact .held hg hy ha hm hp (exer5_of_kiter s reg c m k b hb) hc
    · cases h

/-- The frame-held case of `exer5R`. -/
theorem exer5R_base {s : SC} {reg : SyncReg} {c : Nat} {m : Mode} {E : Nat → Bool} {a : Nat}
    {y : Authority} (hg : NotGuarded s reg a) (hy : s.A[a]? = some y) (ha : y.active = true)
    (hm : m.le y.mode) (hf : y.holder = .frame (s.view c).top) : exer5R s reg c m E a = true := by
  simp only [exer5R, hy, ha, hf, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hg, hm, trivial⟩

/-- The place-held case of `exer5R`. -/
theorem exer5R_held {s : SC} {reg : SyncReg} {c : Nat} {m : Mode} {E : Nat → Bool} {a p b : Nat}
    {y : Authority} (hg : NotGuarded s reg a) (hy : s.A[a]? = some y) (ha : y.active = true)
    (hm : m.le y.mode) (hp : y.holder = .place p) (hb : b < s.A.length)
    (hc : ∀ l ∈ footprint s.P p, Allows (effective s.flat b l) m) (hE : E b = true) :
    exer5R s reg c m E a = true := by
  simp only [exer5R, hy, ha, hp, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq,
    List.any_eq_true, List.mem_range]
  exact ⟨hg, hm, b, hb, hc, hE⟩

/-- `Exer5` is computed by `|A| + 1` steps of `exer5R`. -/
theorem exer5_iff {s : SC} {reg : SyncReg} {c a : Nat} {m : Mode} :
    Exer5 s reg c a m ↔ kiter (exer5R s reg c m) (s.A.length + 1) a = true := by
  refine ⟨fun h => ?_, exer5_of_kiter s reg c m _ a⟩
  induction h with
  | base hg hy ha hm hf => exact exer5R_base hg hy ha hm hf
  | held hg hy ha hm hp _ hc ih =>
    rw [← kiter_fix (exer5R_rule s reg c _)]
    exact exer5R_held hg hy ha hm hp (kiter_bound (exer5R_rule s reg c _) _ _ ih) hc ih

/-- Decidability of `Exer5`. -/
instance (s : SC) (reg : SyncReg) (c a : Nat) (m : Mode) : Decidable (Exer5 s reg c a m) :=
  decidable_of_iff _ exer5_iff.symm

/-- An authority exercisable without a live `guarded` from the current frame of a context with a
nonempty stack is attributable to that context without a live `guarded` (WC5 C43). -/
theorem Exer5.attr5 {s : SC} {reg : SyncReg} {c a : Nat} {m : Mode} (hne : s.stk c ≠ [])
    (h : Exer5 s reg c a m) : Attr5 s reg c a m := by
  induction h with
  | base hg hy ha hm hf => exact .base hg hy ha hm hf (view_top_mem hne)
  | held hg hy ha hm hp _ hc ih => exact .held hg hy ha hm hp ih hc

/-- The argument of an `Exer5` is not a live `guarded`. -/
theorem Exer5.notGuarded {s : SC} {reg : SyncReg} {c a : Nat} {m : Mode} (h : Exer5 s reg c a m) :
    NotGuarded s reg a := by
  cases h with
  | base hg => exact hg
  | held hg => exact hg

/-! ## The corrected exclusion -/

/-- `ChainExcl` (correction proposed in `formal/reports/spec2-m4-handoff.md`, tested here): the
authority argument of `derive` (Spec 1 §60.1), `split` (§61.1), `read` (§66.2), `write` (§67.1) and
`writeShared` (§68.2) is exercisable, in the mode the precondition requires, from the current
frame of the executing context by a holder chain without a live `guarded` (`Exer5`). -/
def ChainExcl (st : SC × SyncReg) : Label → Prop
  | .kernel c (.derive a _ m) => Exer5 st.1 st.2 c a m
  | .kernel c (.split a _) => Exer5 st.1 st.2 c a .modify
  | .kernel c (.read a _) => Exer5 st.1 st.2 c a .observe
  | .kernel c (.write a _) => Exer5 st.1 st.2 c a .modify
  | .kernel c (.writeShared a _) => Exer5 st.1 st.2 c a .observe
  | _ => True

/-- Decidability of `ChainExcl`. -/
instance (st : SC × SyncReg) (lbl : Label) : Decidable (ChainExcl st lbl) := by
  unfold ChainExcl; split <;> infer_instance

/-- `Encap5C`: `Encap5` with `ChainExcl` in place of `GuardedExcl`. -/
def Encap5C (L : MutexLayout) (st : SC × SyncReg) (lbl : Label) : Prop :=
  Encap L st lbl ∧ ChainExcl st lbl ∧ CtlExcl L st lbl

/-- `ChainExcl` implies `GuardedExcl`: the argument of an `Exer5` is not a live `guarded`. -/
theorem chainExcl_guardedExcl {st : SC × SyncReg} {lbl : Label} (h : ChainExcl st lbl) :
    GuardedExcl st lbl := by
  cases lbl with
  | kernel c op =>
    cases op <;> simp only [ChainExcl, GuardedExcl] at h ⊢ <;>
      first | trivial | exact h.notGuarded
  | _ => trivial

/-- `EncapsulatedTrace5C`: a run every step of which satisfies `Encap5C` in the state where it is
taken. -/
inductive EncapsulatedTrace5C (k : K) (L : MutexLayout) :
    SC × SyncReg × ArenaReg → List Label → SC × SyncReg × ArenaReg → Prop where
  | nil {st : SC × SyncReg × ArenaReg} : EncapsulatedTrace5C k L st [] st
  | cons {st st₁ st₂ : SC × SyncReg × ArenaReg} {lbl : Label} {lbls : List Label} :
      Encap5C L (st.1, st.2.1) lbl → LStep k L lbl st st₁ →
      EncapsulatedTrace5C k L st₁ lbls st₂ → EncapsulatedTrace5C k L st (lbl :: lbls) st₂

/-- Every `EncapsulatedTrace5C` is an `EncapsulatedTrace5`: `cap5_compat` and `cap5_drop_own`
apply to it. -/
theorem encapsulatedTrace5C_imp {k : K} {L : MutexLayout} {st st' : SC × SyncReg × ArenaReg}
    {lbls : List Label} (h : EncapsulatedTrace5C k L st lbls st') :
    EncapsulatedTrace5 k L st lbls st' := by
  induction h with
  | nil => exact .nil
  | cons he hs _ ih => exact .cons ⟨he.1, chainExcl_guardedExcl he.2.1, he.2.2⟩ hs ih

/-- An `EncapsulatedTrace5C` extended by one step satisfying `Encap5C`. -/
theorem EncapsulatedTrace5C.snoc {k : K} {L : MutexLayout}
    {st st' st'' : SC × SyncReg × ArenaReg} {lbls : List Label} {lbl : Label}
    (h : EncapsulatedTrace5C k L st lbls st') (he : Encap5C L (st'.1, st'.2.1) lbl)
    (hs : LStep k L lbl st' st'') : EncapsulatedTrace5C k L st (lbls ++ [lbl]) st'' := by
  induction h with
  | nil => exact .cons he hs .nil
  | cons he' hs' _ ih => exact .cons he' hs' (ih he hs)

/-- An `EncapsulatedTrace5C` with named states. -/
def Run5C (k : K) (L : MutexLayout) (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) :
    Prop :=
  ∀ i (h : i < lbls.length),
    Encap5C L ((σ i).1, (σ i).2.1) lbls[i] ∧ LStep k L lbls[i] (σ i) (σ (i + 1))

/-- Every prefix of a `Run5C` is an `EncapsulatedTrace5C`. -/
theorem run5C_prefix {k : K} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg}
    {lbls : List Label} (h : Run5C k L σ lbls) :
    ∀ n, n ≤ lbls.length → ∃ ls, EncapsulatedTrace5C k L (σ 0) ls (σ n)
  | 0, _ => ⟨[], .nil⟩
  | n + 1, hn => by
    obtain ⟨ls, hls⟩ := run5C_prefix h n (by omega)
    obtain ⟨he, hs⟩ := h n (by omega)
    exact ⟨ls ++ [lbls[n]], hls.snoc he hs⟩

/-! ## Statements under the corrected exclusion -/

/-- `cap5_sound` with `Encap5C` and `EncapsulatedTrace5C` in place of `Encap5` and
`EncapsulatedTrace5` (same form as `Cap5Sound`). -/
def Cap5SoundC (k : K) (L : MutexLayout) : Prop :=
  ∀ (statics : Statics) (lbls : List Label) (st : SC × SyncReg × ArenaReg) (c a : Nat)
    (ls : List Nat) (s' : SC), StaticsOK statics →
    EncapsulatedTrace5C k L (SC.ofS3 (S3.init statics), [], []) lbls st →
    (Encap5C L (st.1, st.2.1) (.kernel c (.read a ls)) → opStepC k (.read a ls) c st.1 (.ok s') →
      ∀ l ∈ ls, Allows (cap5 st.1 st.2.1 c l) .observe) ∧
    (Encap5C L (st.1, st.2.1) (.kernel c (.write a ls)) → opStepC k (.write a ls) c st.1 (.ok s') →
      ∀ l ∈ ls, Allows (cap5 st.1 st.2.1 c l) .modify) ∧
    (Encap5C L (st.1, st.2.1) (.kernel c (.writeShared a ls)) →
      opStepC k (.writeShared a ls) c st.1 (.ok s') →
      ∀ l ∈ ls, Allows (cap5 st.1 st.2.1 c l) .observe)

/-- `handoff_loss_exists` with `Run5C` in place of `Run5` (same form as `HandoffLossExists`). -/
def HandoffLossExistsC (k : K) (L : MutexLayout) : Prop :=
  ∀ (statics : Statics) (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label),
    StaticsOK statics → σ 0 = (SC.ofS3 (S3.init statics), [], []) → Run5C k L σ lbls →
    ∀ (i j c c' l : Nat) (m m' : Mode) (hi : i < j) (hj : j < lbls.length), c ≠ c' →
      lbls[i].Access c' l m → lbls[j].Access c l m' → (m = .modify ∨ m' = .modify) →
      ∃ k', ∃ hk : k' < lbls.length, i < k' ∧ k' < j ∧ lbls[k'].ctx = c' ∧
        capRank (cap5 (σ (k' + 1)).1 (σ (k' + 1)).2.1 c' l) <
          capRank (cap5 (σ k').1 (σ k').2.1 c' l)

/-! ## `cap5_sound` under `ChainExcl` -/

/-- An attributable authority with a sufficient effective mode bounds `cap5` from below (WC5
C43). -/
theorem cap5_of {s : SC} {reg : SyncReg} {c l x : Nat} {m : Mode} (hx : Attr5 s reg c x m)
    (he : Allows (effective s.flat x l) m) : Allows (cap5 s reg c l) m := by
  have hb : x ∈ List.range s.A.length := List.mem_range.2 hx.lt
  cases m with
  | modify =>
    have h1 : CapAt5 s reg c l .modify := ⟨x, hb, hx, he⟩
    simp only [cap5, h1, ↓reduceIte]; exact Or.inr rfl
  | observe =>
    by_cases h : CapAt5 s reg c l .modify
    · simp only [cap5, h, ↓reduceIte]; exact Or.inl rfl
    · have h2 : CapAt5 s reg c l .observe := ⟨x, hb, hx, he⟩
      simp only [cap5, h, h2, ↓reduceIte]; exact Or.inl rfl

/-- `cap5_sound` holds under `ChainExcl`, for every state whose live contexts have nonempty stacks
(`FramesC`, WC4 C3): the access authority is attributable without a live `guarded`. -/
theorem cap5_sound_state {k : K} {s s' : SC} {reg : SyncReg} {c a : Nat}
    {ls : List Nat} (hF : FramesC s) :
    (ChainExcl (s, reg) (.kernel c (.read a ls)) → opStepC k (.read a ls) c s (.ok s') →
      ∀ l ∈ ls, Allows (cap5 s reg c l) .observe) ∧
    (ChainExcl (s, reg) (.kernel c (.write a ls)) → opStepC k (.write a ls) c s (.ok s') →
      ∀ l ∈ ls, Allows (cap5 s reg c l) .modify) ∧
    (ChainExcl (s, reg) (.kernel c (.writeShared a ls)) →
      opStepC k (.writeShared a ls) c s (.ok s') →
      ∀ l ∈ ls, Allows (cap5 s reg c l) .observe) := by
  refine ⟨fun hx ⟨hl, o, hR, ho⟩ l hl' => ?_, fun hx ⟨hl, o, hR, ho⟩ l hl' => ?_,
    fun hx ⟨hl, o, hR, ho⟩ l hl' => ?_⟩ <;> have hne := hF.nonempty c hl
  · have hp := pre_of_ok (P := Read3Pre (s.view c) a ls) hR ho
    exact cap5_of (Exer5.attr5 hne hx) (allows_observe (hp.effectivePresent l hl'))
  · have hp := pre_of_ok (P := Write3Pre (s.view c) a ls) hR ho
    have he : effective s.flat a l = some .modify := hp.effectiveModify l hl'
    exact cap5_of (Exer5.attr5 hne hx) (by rw [he]; exact Or.inr rfl)
  · have hp := pre_of_ok (P := WriteSharedPre k (s.view c) a ls) hR ho
    exact cap5_of (Exer5.attr5 hne hx) (allows_observe (hp.effectivePresent l hl'))

/-- `cap5_sound` under the corrected exclusion: under `DDSound` (Spec 1 §80), on the states
reached by an `EncapsulatedTrace5C` from an initial state (Spec 1 §47). -/
theorem cap5_sound_C {k : K} {L : MutexLayout} (hdd : DDSound k) : Cap5SoundC k L := by
  intro statics lbls st c a ls s' hst htr
  obtain ⟨hF, -, -⟩ := (trace5_kInvCA hdd hst (encapsulatedTrace5C_imp htr)).parts
  obtain ⟨h1, h2, h3⟩ := cap5_sound_state (k := k) (s' := s') (reg := st.2.1) (c := c)
    (a := a) (ls := ls) hF
  exact ⟨fun he => h1 he.2.1, fun he => h2 he.2.1, fun he => h3 he.2.1⟩

/-! ## `handoff_loss_exists` under `ChainExcl` -/

/-- An access step (Spec 1 §66–§68) admitted by `Encap5C`, from a state reached by an
`EncapsulatedTrace5C` from an initial state, gives the accessing context a `cap5` at least the
required mode on the accessed leaf. -/
theorem access_cap5 {k : K} {L : MutexLayout} {statics : Statics} {lbls : List Label}
    {st st' : SC × SyncReg × ArenaReg} {lbl : Label} {d l : Nat} {m : Mode} (hdd : DDSound k)
    (hst : StaticsOK statics)
    (htr : EncapsulatedTrace5C k L (SC.ofS3 (S3.init statics), [], []) lbls st)
    (hacc : lbl.Access d l m) (he : Encap5C L (st.1, st.2.1) lbl) (h : LStep k L lbl st st') :
    Allows (cap5 st.1 st.2.1 d l) m := by
  have hsnd := cap5_sound_C (L := L) hdd
  cases lbl with
  | kernel c op =>
    cases op <;> simp only [Label.Access] at hacc
    all_goals
      obtain ⟨rfl, hl, rfl⟩ := hacc
      cases h with
      | kernel hk => first
        | exact (hsnd statics lbls _ _ _ _ _ hst htr).1 he hk l hl
        | exact (hsnd statics lbls _ _ _ _ _ hst htr).2.1 he hk l hl
        | exact (hsnd statics lbls _ _ _ _ _ hst htr).2.2 he hk l hl
  | _ => simp only [Label.Access] at hacc

/-- A function on `Nat` that is smaller at `b` than at `a ≤ b` decreases at some step of
`[a, b)`. -/
theorem exists_drop (f : Nat → Nat) {a : Nat} :
    ∀ b, a ≤ b → f b < f a → ∃ k, a ≤ k ∧ k < b ∧ f (k + 1) < f k
  | 0, hab, h => by
    obtain rfl : a = 0 := by omega
    exact absurd h (Nat.lt_irrefl _)
  | b + 1, hab, h => by
    by_cases hb : f (b + 1) < f b
    · by_cases hab' : a ≤ b
      · exact ⟨b, hab', Nat.lt_succ_self b, hb⟩
      · obtain rfl : a = b + 1 := by omega
        exact absurd h (Nat.lt_irrefl _)
    · have hab' : a ≤ b := by
        rcases Nat.lt_or_ge b a with h' | h'
        · obtain rfl : a = b + 1 := by omega
          exact absurd h (Nat.lt_irrefl _)
        · exact h'
      obtain ⟨k, hk1, hk2, hk3⟩ := exists_drop f b hab' (by omega)
      exact ⟨k, hk1, by omega, hk3⟩

/-- `capRank` is at most 2. -/
theorem capRank_le (o : Option Mode) : capRank o ≤ 2 := by
  rcases o with _ | _ | _ <;> simp [capRank]

/-- `handoff_loss_exists` under the corrected exclusion: under `DDSound` (Spec 1 §80), on every
`EncapsulatedTrace5C` from an initial state, the loss marker exists. From `cap5_sound_C` at the
earlier access, `cap5_compat` at the later one, the invariance of `cap5` under an access step
(`inert_effect`), and `cap5_drop_own` at the first drop between them. -/
theorem handoff_loss_exists_C {k : K} {L : MutexLayout} (hdd : DDSound k) :
    HandoffLossExistsC k L := by
  intro statics σ lbls hst h0 hr i j c c' l m m' hij hj hcc hai haj hmod
  have hil : i < lbls.length := Nat.lt_trans hij hj
  have htr : ∀ n, n ≤ lbls.length → ∃ ls,
      EncapsulatedTrace5C k L (SC.ofS3 (S3.init statics), [], []) ls (σ n) := fun n hn => by
    rw [← h0]; exact run5C_prefix hr n hn
  let f : Nat → Nat := fun n => capRank (cap5 (σ n).1 (σ n).2.1 c' l)
  -- the earlier access
  obtain ⟨lsi, htri⟩ := htr i (Nat.le_of_lt hil)
  obtain ⟨hei, hsi⟩ := hr i hil
  have hci := access_cap5 hdd hst htri hai hei hsi
  have hwi := (trace5_kInvCA hdd hst (encapsulatedTrace5C_imp htri)).parts.2.1
  have hinert : Label.Inert lbls[i] := by
    revert hai; cases lbls[i] with
    | kernel _ op => cases op <;> simp [Label.Access, Label.Inert]
    | _ => simp [Label.Access]
  obtain ⟨hA, hP, hC, hreg⟩ := inert_effect hinert hsi
  have hfi : f i ≤ f (i + 1) := cap5_same hwi hA hP hC hreg c' l
  -- the later access
  obtain ⟨lsj, htrj⟩ := htr j (Nat.le_of_lt hj)
  obtain ⟨hej, hsj⟩ := hr j hj
  have hcj := access_cap5 hdd hst htrj haj hej hsj
  have hcompat := fun {x y : Nat} (hxy : x ≠ y) =>
    cap5_compat (l := l) hdd hst (encapsulatedTrace5C_imp htrj) hxy
  have hdrop : f j < f (i + 1) := by
    rcases hmod with rfl | rfl
    · have h2 : f i = 2 := by
        show capRank (cap5 (σ i).1 (σ i).2.1 c' l) = 2
        rw [allows_modify hci]; rfl
      have hlt : f j < 2 := by
        show capRank (cap5 (σ j).1 (σ j).2.1 c' l) < 2
        cases hcj' : cap5 (σ j).1 (σ j).2.1 c' l with
        | none => simp [capRank]
        | some md =>
          cases md with
          | observe => simp [capRank]
          | modify =>
            have := hcompat (Ne.symm hcc) hcj'
            rw [this] at hcj; exact hcj.elim
      have := capRank_le (cap5 (σ (i + 1)).1 (σ (i + 1)).2.1 c' l)
      omega
    · have h0' : f j = 0 := by
        show capRank (cap5 (σ j).1 (σ j).2.1 c' l) = 0
        rw [hcompat hcc (allows_modify hcj)]; rfl
      have h1 : 1 ≤ f i := by
        show 1 ≤ capRank (cap5 (σ i).1 (σ i).2.1 c' l)
        cases hc : cap5 (σ i).1 (σ i).2.1 c' l with
        | none => rw [hc] at hci; exact hci.elim
        | some md => cases md <;> simp [capRank]
      omega
  obtain ⟨k', hk1, hk2, hk3⟩ := exists_drop f j hij hdrop
  have hk : k' < lbls.length := Nat.lt_trans hk2 hj
  obtain ⟨lsk, htrk⟩ := htr k' (Nat.le_of_lt hk)
  obtain ⟨hek, hsk⟩ := hr k' hk
  refine ⟨k', hk, by omega, hk2, ?_, hk3⟩
  exact cap5_drop_own hdd statics lsk (σ k') (σ (k' + 1)) lbls[k'] c' l hst
    (encapsulatedTrace5C_imp htrk) ⟨hek.1, chainExcl_guardedExcl hek.2.1, hek.2.2⟩ hsk hk3

end Ern.Concurrency
