import Ern.Concurrency.SyncLib

/-!
# Context capability (WC5 C43)

`ERN_Concurrency_Model_WC5.md` C43 defines, provisionally, the capability `cap(s, c, l)` of a
context `c` on a leaf `l`, and leaves "the exact inductive attribution relation" open. This module
fixes it as the brief of milestone 4 states it: `Attr` is `ExercisableAt` of Spec 1 §43 with "held
by the current frame" read as "held by a live frame of `c`, current or suspended"; `cap` is the
greatest mode `m` such that an authority attributable to `c` in mode `m` has an effective mode
permitting `m` on `l`.
-/

namespace Ern.Concurrency

open Ern.MemoryModel.Access

/-- `Attr s c x m` (WC5 C43; Spec 1 §43): `x` is active, its own mode permits `m`, and it is held
by a live frame of context `c`, current or suspended, or by a place `p` such that an authority
itself attributable to `c` in mode `m` has an effective mode permitting `m` on every leaf of `p`.
Inductive along the holder chain, as `S3.ExercisableAt`. -/
inductive Attr (s : SC) (c : Nat) : Nat → Mode → Prop where
  | base {a : Nat} {m : Mode} {y : Authority} {f : Nat} : s.A[a]? = some y → y.active = true →
      m.le y.mode → y.holder = .frame f → f ∈ s.stk c → Attr s c a m
  | held {a p b : Nat} {m : Mode} {y : Authority} : s.A[a]? = some y → y.active = true →
      m.le y.mode → y.holder = .place p → Attr s c b m →
      (∀ l ∈ footprint s.P p, Allows (effective s.flat b l) m) → Attr s c a m

/-- The kernel components of `s` with the single frame `f` as current frame: Spec 1 §43 read from
`f`. -/
def SC.from (s : SC) (f : Nat) : S3 := { s.flat with F := [f] }

/-- `Attr` is `ExercisableAt` (Spec 1 §43) read from one live frame of `c` (WC5 C43): a holder
chain ends at a single frame-held authority. Decision procedure for `Attr`. -/
theorem attr_iff {s : SC} {c a : Nat} {m : Mode} :
    Attr s c a m ↔ ∃ f ∈ s.stk c, (s.from f).ExercisableAt a m := by
  constructor
  · intro h
    induction h with
    | base hy ha hm hf hin => exact ⟨_, hin, .base hy ha hm (by rw [hf]; rfl)⟩
    | held hy ha hm hp _ hc ih =>
      obtain ⟨f, hin, he⟩ := ih
      exact ⟨f, hin, .held hy ha hm hp he hc⟩
  · rintro ⟨f, hin, h⟩
    induction h with
    | base hy ha hm hf => exact .base hy ha hm hf hin
    | held hy ha hm hp _ hc ih => exact .held hy ha hm hp ih hc

/-- Decidability of `Attr` (WC5 C43). -/
instance (s : SC) (c a : Nat) (m : Mode) : Decidable (Attr s c a m) :=
  decidable_of_iff _ attr_iff.symm

/-- Some authority attributable to `c` in mode `m` has an effective mode permitting `m` on `l`
(WC5 C43). -/
def CapAt (s : SC) (c l : Nat) (m : Mode) : Prop :=
  ∃ x ∈ List.range s.A.length, Attr s c x m ∧ Allows (effective s.flat x l) m

/-- Decidability of `CapAt` (WC5 C43). -/
instance (s : SC) (c l : Nat) (m : Mode) : Decidable (CapAt s c l m) := by
  unfold CapAt; infer_instance

/-- `cap(s, c, l)` (WC5 C43): the greatest mode `m` such that an authority attributable to `c` in
mode `m` has an effective mode permitting `m` on the leaf `l`; `none` if there is none. -/
def cap (s : SC) (c l : Nat) : Option Mode :=
  if CapAt s c l .modify then some .modify else if CapAt s c l .observe then some .observe
  else none

/-- The context executing a labelled step (WC4 C2: every step is executed by one context). -/
def Label.ctx : Label → Nat
  | .kernel c _ | .spawn c _ _ | .terminate c | .join c _ | .deriveSync c _ | .newMutex c _
  | .acquire c _ | .unlock c _ | .resetLock c _ | .spawnVal c _ _ _ | .newArena c _ _
  | .issue c _ _ _ | .reset c _ => c

/-- An attributable authority with a sufficient effective mode bounds `cap` from below (WC5
C43). -/
theorem cap_of {s : SC} {c l x : Nat} {m : Mode} (hx : Attr s c x m)
    (he : Allows (effective s.flat x l) m) : Allows (cap s c l) m := by
  have hb : x ∈ List.range s.A.length := by
    cases hx with
    | base hy => exact List.mem_range.2 (lt_of_getElem? hy)
    | held hy => exact List.mem_range.2 (lt_of_getElem? hy)
  cases m with
  | modify =>
    have h1 : CapAt s c l .modify := ⟨x, hb, hx, he⟩
    simp only [cap, h1, ↓reduceIte]; exact Or.inr rfl
  | observe =>
    by_cases h : CapAt s c l .modify
    · simp only [cap, h, ↓reduceIte]; exact Or.inl rfl
    · have h2 : CapAt s c l .observe := ⟨x, hb, hx, he⟩
      simp only [cap, h, h2, ↓reduceIte]; exact Or.inl rfl

/-- What the current frame of a live context with a nonempty stack can exercise (Spec 1 §43 on its
view, WC4 C2) is attributable to that context (WC5 C43). -/
theorem attr_of_exercisable {s : SC} {c a : Nat} {m : Mode} (hne : s.stk c ≠ [])
    (h : (s.view c).ExercisableAt a m) : Attr s c a m := by
  have htop : (s.view c).top ∈ s.stk c := by
    obtain ⟨f, r, hfr⟩ := List.exists_cons_of_ne_nil hne
    show (s.stk c ++ _).headD 0 ∈ s.stk c
    rw [hfr]; exact List.mem_cons_self ..
  induction h with
  | base hy ha hm hf => exact .base hy ha hm hf htop
  | held hy ha hm hp _ hc ih => exact .held hy ha hm hp ih hc

/-- A present effective mode permits `Observe` (Spec 1 §43). -/
theorem allows_observe {e : Option Mode} (h : e ≠ none) : Allows e .observe := by
  cases e with
  | none => exact absurd rfl h
  | some e => exact Or.inl rfl

/-- The precondition of an operation run on a view, from an `ok` outcome written back (Spec 1
§58; WC4 C2). -/
theorem pre_of_ok {P : Prop} {eff : S3} {o : Outcome3 S3} {s s' : SC} (hR : Guarded P eff o)
    (ho : Outcome3.ok s' = omap s.set o) : P := by
  cases hR with
  | ok hp => exact hp
  | reject => cases ho

/-- `cap_sound` (WC5 C43, brief of milestone 4, task 2): for every enabled access step of context
`c`, `cap` of `c` on every accessed leaf is at least the required mode, `Observe` for `read3`
(Spec 1 §66.2) and `writeShared` (§68.2), `Modify` for `write3` (§67.1). Under `FramesC` (WC4 C3:
a live context has a nonempty stack, whose top is its current frame). -/
theorem cap_sound {k : K} {s s' : SC} {c a : Nat} {ls : List Nat} (hF : FramesC s) :
    (opStepC k (.read a ls) c s (.ok s') → ∀ l ∈ ls, Allows (cap s c l) .observe) ∧
    (opStepC k (.write a ls) c s (.ok s') → ∀ l ∈ ls, Allows (cap s c l) .modify) ∧
    (opStepC k (.writeShared a ls) c s (.ok s') → ∀ l ∈ ls, Allows (cap s c l) .observe) := by
  refine ⟨fun ⟨hl, o, hR, ho⟩ l hl' => ?_, fun ⟨hl, o, hR, ho⟩ l hl' => ?_,
    fun ⟨hl, o, hR, ho⟩ l hl' => ?_⟩ <;> have hne := hF.nonempty c hl
  · have hp := pre_of_ok (P := Read3Pre (s.view c) a ls) hR ho
    exact cap_of (attr_of_exercisable hne hp.exercisable)
      (allows_observe (hp.effectivePresent l hl'))
  · have hp := pre_of_ok (P := Write3Pre (s.view c) a ls) hR ho
    have he : effective s.flat a l = some .modify := hp.effectiveModify l hl'
    exact cap_of (attr_of_exercisable hne hp.exercisable) (by rw [he]; exact Or.inr rfl)
  · have hp := pre_of_ok (P := WriteSharedPre k (s.view c) a ls) hR ho
    exact cap_of (attr_of_exercisable hne hp.exercisable)
      (allows_observe (hp.effectivePresent l hl'))

end Ern.Concurrency
