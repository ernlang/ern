import Ern.Concurrency.Repr
import Ern.Concurrency.Reparent
import Ern.Concurrency.Traces

/-!
# Ordinary accesses of distinct contexts do not conflict (Spec 1 §43, §50, §54, §82.8; WC4 C2)

Contexts interleave at the grain of abstract steps. In a state satisfying the re-indexed kernel
invariant `KInvC`, an ordinary write enabled in the view of one context and an ordinary read or
write enabled in the view of another context share no leaf that is not `K.SharedMutable`
(`r4_nonConflict`, R4), so the bytes realizing their non-`SharedMutable` leaves are disjoint under
`LayoutWF` (`r4_bytes`, R4′, Spec 1 §23, §82.8).

This is absence of conflict between enabled abstract steps. It is not a proof of absence of data
races: the ordering of conflicting accesses that the authority machine separates in time (release
of a grant before its re-acquisition, `terminate` before `join`) by a memory-ordering relation is
WC4 OB-C04, OB-C06 and OB-C11.
-/

namespace Ern.Concurrency

open Ern.MemoryModel Ern.MemoryModel.Access Ern.MemoryModel.Refinement

/-- `OrdinaryCrossContextNonConflict` in state `s` (Spec 1 §43, §50, §54, §82.8; WC4 C2): for all
live contexts `c ≠ c′`, all authorities `a`, `b` and all leaf lists `L`, `L′`, if `write` (Spec 1
§67) through `a` on `L` is enabled in the view of `c` and `read` (§66) or `write` through `b` on
`L′` is enabled in the view of `c′`, then every leaf of both `L` and `L′` is `K.SharedMutable`.
`SharedMutable` leaves are excluded from the conclusion, not from the hypotheses. -/
def OrdinaryCrossContextNonConflict (k : K) (s : SC) : Prop :=
  ∀ c c', s.Live c → s.Live c' → c ≠ c' → ∀ (a b : Nat) (L L' : List Nat),
    Write3Pre (s.view c) a L → (Read3Pre (s.view c') b L' ∨ Write3Pre (s.view c') b L') →
    ∀ l ∈ L, l ∈ L' → k.SharedMutable l

namespace NonConflictAux

/-- An effective mode allowing `m` is present (Spec 1 §43). -/
theorem allows_ne_none {e : Option Mode} {m : Mode} (h : Allows e m) : e ≠ none := by
  intro he; rw [he] at h; exact h

/-- An effective mode allowing `Modify` is `Modify` (Spec 1 §43: `Observe ≤ Modify`). -/
theorem allows_modify {e : Option Mode} (h : Allows e .modify) : e = some .modify := by
  cases e with
  | none => exact h.elim
  | some m => cases m with
    | observe => exact absurd h (by simp [Allows, OptP, Mode.le])
    | modify => rfl

/-- An authority exercisable in `Modify` from the current frame of `t₁` is exercisable in no mode
from the current frame of `t₂`, when the two states have the same authorities and places, satisfy
`I1` and have distinct current frames (Spec 1 §43, §50). By induction on the derivation of
`ExercisableAt` (§43, the clause recursive along the holder chain, which the inductive
definition makes finite): a frame-held authority is exercisable only from its holder; a
place-held one only through an authority with effective `Modify` on a leaf of its holder, which
`I1` makes the same authority from both frames, one link down the chain. -/
theorem no_double_exercise {t₁ t₂ : S3} (hA : t₂.A = t₁.A) (hP : t₂.P = t₁.P)
    (heff : ∀ x l, effective t₂ x l = effective t₁ x l) (hw : WF3 t₁) (hI1 : I1 t₁)
    (htop : t₁.top ≠ t₂.top) :
    ∀ {a : Nat} {m : Mode}, t₁.ExercisableAt a m → m = .modify →
      ∀ {m' : Mode}, t₂.ExercisableAt a m' → False := by
  intro a m h
  induction h with
  | @base a m y hy _ _ hh =>
    intro _ m' h₂
    cases h₂ with
    | base hy' _ _ hh' =>
      rw [hA, hy] at hy'; cases hy'
      rw [hh] at hh'; injection hh' with e; exact htop e
    | held hy' _ _ hh' _ _ =>
      rw [hA, hy] at hy'; cases hy'
      rw [hh] at hh'; cases hh'
  | @held a p b m y hy ya _ hh hb hall ih =>
    intro hmm m' h₂
    subst hmm
    cases h₂ with
    | base hy' _ _ hh' =>
      rw [hA, hy] at hy'; cases hy'
      rw [hh] at hh'; cases hh'
    | @held _ p' b' _ y' hy' _ _ hh' hb' hall' =>
      rw [hA, hy] at hy'; cases hy'
      rw [hh] at hh'; cases hh'
      have hpu : t₁.Usable p := by
        have := hw.holders a y hy ya; rw [hh] at this; exact this
      obtain ⟨l, hl⟩ := exists_mem_footprint hw (t₁.P.length - p + 1) p (Nat.lt_succ_self _) hpu.lt
      have h₁ : effective t₁ b l = some .modify := allows_modify (hall l hl)
      have h₂ : effective t₁ b' l ≠ none := by
        rw [← heff]; exact allows_ne_none (hall' l (by rw [hP]; exact hl))
      by_cases hbb : b = b'
      · subst hbb; exact ih rfl hb'
      · exact h₂ (effective_exclusive hI1 hbb h₁)

/-- The current frames of two distinct live contexts are distinct (WC4 C3: frame identities are
globally unique; every live context has a nonempty stack). -/
theorem view_tops_ne {s : SC} (hfr : FramesC s) {c c' : Nat} (hc : s.Live c) (hc' : s.Live c')
    (hne : c ≠ c') : (s.view c).top ≠ (s.view c').top := by
  obtain ⟨f, rest, hf⟩ : ∃ f rest, s.stk c = f :: rest := by
    cases e : s.stk c with
    | nil => exact absurd e (hfr.nonempty c hc)
    | cons f rest => exact ⟨f, rest, rfl⟩
  obtain ⟨f', rest', hf'⟩ : ∃ f rest, s.stk c' = f :: rest := by
    cases e : s.stk c' with
    | nil => exact absurd e (hfr.nonempty c' hc')
    | cons f rest => exact ⟨f, rest, rfl⟩
  rw [SC.view_top hf, SC.view_top hf']
  intro e
  subst e
  exact hne (ReparentAux.stk_unique hfr.nodup (by rw [hf]; exact List.mem_cons_self ..)
    (by rw [hf']; exact List.mem_cons_self ..))

end NonConflictAux

open NonConflictAux

/-- An ordinary write enabled in the view of a live context and an ordinary read or write enabled
in the view of another live context share no leaf, in a state satisfying `KInvC` (Spec 1 §43,
§50; WC4 C2, C3). For `a ≠ b`: `I1` and the effective modes (Spec 1 §43.3–§43.4,
`effective_exclusive`). For `a = b`: `no_double_exercise`. -/
theorem cross_context_disjoint {s : SC} (hk : KInvC s) {c c' : Nat} (hc : s.Live c)
    (hc' : s.Live c') (hne : c ≠ c') {a b : Nat} {L L' : List Nat}
    (h₁ : Write3Pre (s.view c) a L) (h₂ : Read3Pre (s.view c') b L' ∨ Write3Pre (s.view c') b L') :
    ∀ l ∈ L, l ∉ L' := by
  intro l hl hl'
  have hfr := hk.1.1
  have hI1 : I1 (s.view c) := hk.2.1.1.1
  have hw : WF3 (s.view c) := SC.wf3_view hfr hk.1.2
  have hm : effective (s.view c) a l = some .modify := h₁.effectiveModify l hl
  obtain ⟨m', hex₂, heff₂⟩ : ∃ m', (s.view c').ExercisableAt b m' ∧
      effective (s.view c') b l ≠ none := by
    rcases h₂ with h₂ | h₂
    · exact ⟨_, h₂.exercisable, h₂.effectivePresent l hl'⟩
    · exact ⟨_, h₂.exercisable, by rw [h₂.effectiveModify l hl']; nofun⟩
  by_cases hab : a = b
  · subst hab
    exact no_double_exercise (t₁ := s.view c) (t₂ := s.view c') rfl rfl (fun _ _ => rfl) hw hI1
      (view_tops_ne hfr hc hc' hne) h₁.exercisable rfl hex₂
  · exact heff₂ (effective_exclusive hI1 hab hm)

/-- **R4** (Spec 1 §43, §50, §54, §82.8; WC4 C2), at the grain of abstract steps: every state
satisfying the re-indexed kernel invariant `KInvC` (every reachable state, `encapsulated_inv`)
satisfies `OrdinaryCrossContextNonConflict`. This is absence of conflict between enabled abstract
steps, not absence of data races (WC4 OB-C04, OB-C06, OB-C11). -/
theorem r4_nonConflict {k : K} {s : SC} (hk : KInvC s) : OrdinaryCrossContextNonConflict k s :=
  fun _ _ hc hc' hne _ _ _ _ h₁ h₂ l hl hl' =>
    absurd hl' (cross_context_disjoint hk hc hc' hne h₁ h₂ l hl)

/-- **R4′** (Spec 1 §82.8, §23; WC4 C2): under the layout interface `LayoutWF` (part of `ReprC`),
in a state satisfying `KInvC`, for an ordinary write enabled in the view of a live context on `L`
and an ordinary read or write enabled in the view of another live context on `L′`, the bytes
realizing the leaves of `L` that are not `K.SharedMutable` and those realizing the leaves of `L′`
that are not `K.SharedMutable` are disjoint (`ByteDisjoint`). -/
theorem r4_bytes {k : K} [DecidablePred k.SharedMutable] {s : SC} {Lm : Layout}
    {m : Machine.State} (hk : KInvC s) (hlw : LayoutWF Lm s.flat m) {c c' : Nat}
    (hc : s.Live c) (hc' : s.Live c') (hne : c ≠ c') {a b : Nat} {L L' : List Nat}
    (h₁ : Write3Pre (s.view c) a L) (h₂ : Read3Pre (s.view c') b L' ∨ Write3Pre (s.view c') b L') :
    ByteDisjoint Lm (L.filter fun l => !decide (k.SharedMutable l))
      (L'.filter fun l => !decide (k.SharedMutable l)) := by
  have hfr := hk.1.1
  have hw : WF3 (s.view c) := SC.wf3_view hfr hk.1.2
  have hw' : WF3 (s.view c') := SC.wf3_view hfr hk.1.2
  intro l hl l' hl'
  obtain ⟨hl, hsl⟩ := List.mem_filter.1 hl
  obtain ⟨hl', hsl'⟩ := List.mem_filter.1 hl'
  obtain ⟨hlP, hlf, -⟩ := leaf_of_leafOfUsable hw (h₁.usable l hl)
  have hu' : LeafOfUsable (s.view c') l' := by
    rcases h₂ with h₂ | h₂
    · exact h₂.usable l' hl'
    · exact h₂.usable l' hl'
  obtain ⟨hlP', hlf', -⟩ := leaf_of_leafOfUsable hw' hu'
  by_cases e : (Lm l).alloc = (Lm l').alloc
  · refine .inr (hlw.disjoint l l' hlP hlP' hlf hlf' (fun hll => ?_) e)
    subst hll
    have := r4_nonConflict (k := k) hk c c' hc hc' hne a b L L' h₁ h₂ l hl hl'
    simp [this] at hsl
  · exact .inl e

/-! ## Non-vacuity: two contexts after WC4 S4 -/

namespace NonConflictWitness

open Ern.MemoryModel.Access.Examples Ern.Concurrency.Traces

/-- Non-vacuity of R4 and R4′ (WC4 S4): in the final state of the S4 run, which satisfies `KInvC`,
contexts 0 and 1 are live; `write` through the root authority 0 of the static place 0 is enabled
in the view of context 0, and both `read` and `write` through the root authority 4 of the local
`d` (place 4) of context 1 are enabled in the view of context 1. -/
theorem r4_nonvacuous : KInvC q6 ∧ q6.Live 0 ∧ q6.Live 1 ∧ Write3Pre (q6.view 0) 0 [0] ∧
    Read3Pre (q6.view 1) 4 [4] ∧ Write3Pre (q6.view 1) 4 [4] :=
  ⟨s4_detached_child.2.2.2.2.2.1, by decide, by decide, by decide, by decide, by decide⟩

end NonConflictWitness

end Ern.Concurrency
