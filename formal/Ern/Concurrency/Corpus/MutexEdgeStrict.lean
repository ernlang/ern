import Ern.Concurrency.EventsStrict
import Ern.Concurrency.Corpus.MutexEdge
import Ern.Concurrency.Corpus.HandoffEvents

/-!
# Witnesses on the strict graph

Brief of milestone 4, strict mutex edge, task 4: the facts of `corpus-spec2-m3.md` v9 §2 octies on
the strict graph of `Ern.Concurrency.EventsStrict`, and the facts of v9 §2 septies kept on it.
Facts decided by `decide`; the two-access lemmas below reduce the whole-trace statements to the
single pair of each trace.
-/

namespace Ern.Concurrency.Corpus.MutexEdgeStrict

open Ern.MemoryModel.Access Ern.Concurrency Ern.Concurrency.Corpus
open Ern.Concurrency.Corpus.MutexEdge Ern.Concurrency.Corpus.HandoffEvents
open Ern.Concurrency.Corpus.GuardedChainC (lcLbls)
open Ern.Concurrency.Traces (L0)

/-! ## Traces with two accesses -/

/-- On a trace whose only accesses are steps `a < b`, an exclusive pair is `(a, b, l)`. -/
theorem exclPair_of_two {lbls : List Label} {a b i j l : Nat}
    (hkey : ∀ k (h : k < lbls.length), (lbls[k]'h).accMode ≠ none → k = a ∨ k = b) (hab : a < b)
    (hp : ExclPair lbls i j l) : i = a ∧ j = b ∧
      ∃ (h : a < lbls.length) (c : Nat) (m : Mode), (lbls[a]'h).Access c l m := by
  obtain ⟨hij, hj, c, c', m, m', hcc, hai, haj, _⟩ := hp
  have hi := hkey i _ (accMode_of_access _ hai)
  have hj' := hkey j hj (accMode_of_access hj haj)
  have e1 : i = a := by omega
  have e2 : j = b := by omega
  subst e1 e2
  exact ⟨rfl, rfl, _, c', m, hai⟩

/-- On a trace whose only accesses are steps `a < b`, strict `HandoffOrdered` is the pair
`(a, b)`. -/
theorem handoffOrderedS_of_two {σ : Nat → SC × SyncReg × ArenaReg} {L : MutexLayout}
    {lbls : List Label} {a b : Nat}
    (hkey : ∀ k (h : k < lbls.length), (lbls[k]'h).accMode ≠ none → k = a ∨ k = b) (hab : a < b)
    (hord : ∀ l, (∃ (h : a < lbls.length) (c : Nat) (m : Mode), (lbls[a]'h).Access c l m) →
      HandoffOrderedAtS σ L lbls a b l) : HandoffOrderedS σ L lbls := by
  intro i j l hp
  obtain ⟨rfl, rfl, h⟩ := exclPair_of_two hkey hab hp
  exact hord l h

/-- On a trace whose only accesses are steps `a < b`, strict `hb` from `a` to `b` excludes strict
`Race`. -/
theorem not_raceS_of_two {σ : Nat → SC × SyncReg × ArenaReg} {L : MutexLayout}
    {lbls : List Label} {a b : Nat}
    (hkey : ∀ k (h : k < lbls.length), (lbls[k]'h).accMode ≠ none → k = a ∨ k = b) (hab : a < b)
    (hb : HBS σ L lbls (.step a) (.step b)) : ¬ RaceS σ L lbls := by
  rintro ⟨i, j, l, hp, hnb⟩
  obtain ⟨rfl, rfl, -⟩ := exclPair_of_two hkey hab hp
  exact hnb hb

/-! ## `corpus-spec2-m3.md` v9 §2 octies on the strict graph -/

/-- `corpus-spec2-m3.md` v9 §2 octies W-RL, strict graph: the strict mutex edge from `unlock(e)`
(step 7) to `acquire(e)` (step 10) is cut by the `resetLock` (step 9); no strict `hb` path joins
the two writes of `T` (no `sw` edge leaves context 1); the pair violates strict
`HandoffOrderedAt` (WC5.1 C46), so the trace is not strictly `HandoffOrdered` and has a strict
`Race`. -/
theorem W_RL_strict : ¬ SWS rlσ L0 rlLbls (.step 7) (.step 10) ∧
    ¬ HBS rlσ L0 rlLbls (.step 6) (.step 11) ∧ ¬ HandoffOrderedAtS rlσ L0 rlLbls 6 11 3 ∧
    ¬ HandoffOrderedS rlσ L0 rlLbls ∧ RaceS rlσ L0 rlLbls :=
  have hnb : ¬ HBS rlσ L0 rlLbls (.step 6) (.step 11) := by decide
  have hno : ¬ HandoffOrderedAtS rlσ L0 rlLbls 6 11 3 := by decide
  ⟨by decide, hnb, hno, fun h => hno (h 6 11 3 W_RL_excl), ⟨6, 11, 3, W_RL_excl, hnb⟩⟩

/-- `corpus-spec2-m3.md` v9 §2 octies W-TR, strict graph: the strict mutex edge from `unlock(e)`
(step 7) to `acquire(e)` (step 10) is cut, the controller of `e` moving from `lock` to `lock′` at
step 9; no strict `hb` path joins the two writes of `T`; the pair violates strict
`HandoffOrderedAt` (WC5.1 C46). -/
theorem W_TR_strict : ¬ SWS trσ L0 trLbls (.step 7) (.step 10) ∧
    ctlAt trσ L0 0 8 = some 2 ∧ ctlAt trσ L0 0 10 = some 6 ∧
    ¬ HBS trσ L0 trLbls (.step 6) (.step 11) ∧ ¬ HandoffOrderedAtS trσ L0 trLbls 6 11 3 ∧
    ¬ HandoffOrderedS trσ L0 trLbls ∧ RaceS trσ L0 trLbls :=
  have hnb : ¬ HBS trσ L0 trLbls (.step 6) (.step 11) := by decide
  have hno : ¬ HandoffOrderedAtS trσ L0 trLbls 6 11 3 := by decide
  ⟨by decide, by decide, by decide, hnb, hno, fun h => hno (h 6 11 3 W_TR_excl),
    ⟨6, 11, 3, W_TR_excl, hnb⟩⟩

/-- `corpus-spec2-m3.md` v9 §2 octies W-RL₀, strict graph, expected path: write of context 1
(step 6) →`po` `unlock(e)` (step 7) →strict `sw` `acquire(e)` of context 0 (step 9) →`po` write
of context 0 (step 10); nothing intervenes on the controller. The pair satisfies strict
`HandoffOrderedAt` (WC5.1 C46); the trace, whose only accesses are steps 6 and 10, is strictly
`HandoffOrdered` and has no strict `Race`. -/
theorem W_RL0_strict : PO rl0σ rl0Lbls (.step 6) (.step 7) ∧
    SWS rl0σ L0 rl0Lbls (.step 7) (.step 9) ∧
    PO rl0σ rl0Lbls (.step 9) (.step 10) ∧ HBS rl0σ L0 rl0Lbls (.step 6) (.step 10) ∧
    HandoffOrderedS rl0σ L0 rl0Lbls ∧ ¬ RaceS rl0σ L0 rl0Lbls := by
  have hkey : ∀ k (h : k < rl0Lbls.length), (rl0Lbls[k]'h).accMode ≠ none → k = 6 ∨ k = 10 := by
    decide
  have hb : HBS rl0σ L0 rl0Lbls (.step 6) (.step 10) := by decide
  refine ⟨by decide, by decide, by decide, hb, handoffOrderedS_of_two hkey (by decide) ?_,
    not_raceS_of_two hkey (by decide) hb⟩
  rintro l ⟨_, c, m, ⟨-, hl, -⟩⟩
  rw [List.mem_singleton.1 hl]
  decide

/-- `corpus-spec2-m3.md` v9 §2 octies W-RL-J, strict graph, expected path: write of context 1
(step 6) →`po` `terminate(c1)` (step 9) →`sw` `join(c1)` (step 10) →`po` write of context 0
(step 13). The pair satisfies strict `HandoffOrderedAt` (WC5.1 C46); the trace is strictly
`HandoffOrdered` and has no strict `Race`. -/
theorem W_RLJ_strict : PO rljσ rljLbls (.step 6) (.step 9) ∧
    SWS rljσ L0 rljLbls (.step 9) (.step 10) ∧ PO rljσ rljLbls (.step 10) (.step 13) ∧
    HBS rljσ L0 rljLbls (.step 6) (.step 13) ∧ HandoffOrderedS rljσ L0 rljLbls ∧
    ¬ RaceS rljσ L0 rljLbls := by
  have hkey : ∀ k (h : k < rljLbls.length), (rljLbls[k]'h).accMode ≠ none → k = 6 ∨ k = 13 := by
    decide
  have hb : HBS rljσ L0 rljLbls (.step 6) (.step 13) := by decide
  refine ⟨by decide, by decide, by decide, hb, handoffOrderedS_of_two hkey (by decide) ?_,
    not_raceS_of_two hkey (by decide) hb⟩
  rintro l ⟨_, c, m, ⟨-, hl, -⟩⟩
  rw [List.mem_singleton.1 hl]
  decide

/-- `corpus-spec2-m3.md` v9 §2 octies W-TR-J, strict graph, expected path: write of context 1
(step 6) →`po` `terminate(c1)` (step 9) →`sw` `join(c1)` (step 10) →`po` write of context 0
(step 13). The pair satisfies strict `HandoffOrderedAt` (WC5.1 C46); the trace is strictly
`HandoffOrdered` and has no strict `Race`. -/
theorem W_TRJ_strict : PO trjσ trjLbls (.step 6) (.step 9) ∧
    SWS trjσ L0 trjLbls (.step 9) (.step 10) ∧ PO trjσ trjLbls (.step 10) (.step 13) ∧
    HBS trjσ L0 trjLbls (.step 6) (.step 13) ∧ HandoffOrderedS trjσ L0 trjLbls ∧
    ¬ RaceS trjσ L0 trjLbls := by
  have hkey : ∀ k (h : k < trjLbls.length), (trjLbls[k]'h).accMode ≠ none → k = 6 ∨ k = 13 := by
    decide
  have hb : HBS trjσ L0 trjLbls (.step 6) (.step 13) := by decide
  refine ⟨by decide, by decide, by decide, hb, handoffOrderedS_of_two hkey (by decide) ?_,
    not_raceS_of_two hkey (by decide) hb⟩
  rintro l ⟨_, c, m, ⟨-, hl, -⟩⟩
  rw [List.mem_singleton.1 hl]
  decide

/-! ## `corpus-spec2-m3.md` v9 §2 septies on the strict graph -/

/-- `corpus-spec2-m3.md` v9 §2 septies W-HO, W-HO′, W-HO″ on the strict graph (by `hbS_hb` and
`handoffOrderedAtS_imp`): no strict `hb` between the two writes, and the pair violates strict
`HandoffOrderedAt`. -/
theorem W_HO_all_strict : (¬ HBS hoσ L0 hoLbls (.step 2) (.step 4) ∧
      ∀ l ∈ [1, 2], ¬ HandoffOrderedAtS hoσ L0 hoLbls 2 4 l) ∧
    (¬ HBS ho2σ L0 ho2Lbls (.step 3) (.step 5) ∧ ¬ HandoffOrderedAtS ho2σ L0 ho2Lbls 3 5 0) ∧
    (¬ HBS ho3σ L0 ho3Lbls (.step 4) (.step 9) ∧ ¬ HandoffOrderedAtS ho3σ L0 ho3Lbls 4 9 0) :=
  ⟨⟨fun h => W_HO_noHb (hbS_hb h),
    fun l hl h => W_HO_unordered.1 l hl (handoffOrderedAtS_imp h)⟩,
   ⟨fun h => W_HO2_noHb (hbS_hb h), fun h => W_HO2_unordered.1 (handoffOrderedAtS_imp h)⟩,
   ⟨fun h => W_HO3_noHb (hbS_hb h), fun h => W_HO3_unordered.1 (handoffOrderedAtS_imp h)⟩⟩

/-- `corpus-spec2-m3.md` v9 §2 septies W-HO, W-HO′, W-HO″ have a strict `Race` (`race_raceS`) and
are not strictly `HandoffOrdered` (`handoffOrderedS_imp`). -/
theorem W_HO_all_raceS : (RaceS hoσ L0 hoLbls ∧ ¬ HandoffOrderedS hoσ L0 hoLbls) ∧
    (RaceS ho2σ L0 ho2Lbls ∧ ¬ HandoffOrderedS ho2σ L0 ho2Lbls) ∧
    (RaceS ho3σ L0 ho3Lbls ∧ ¬ HandoffOrderedS ho3σ L0 ho3Lbls) :=
  ⟨⟨race_raceS W_HO_unordered.2.2, fun h => W_HO_unordered.2.1 (handoffOrderedS_imp h)⟩,
   ⟨race_raceS W_HO2_unordered.2.2, fun h => W_HO2_unordered.2.1 (handoffOrderedS_imp h)⟩,
   ⟨race_raceS W_HO3_unordered.2.2, fun h => W_HO3_unordered.2.1 (handoffOrderedS_imp h)⟩⟩

/-- `corpus-spec2-m3.md` v9 §2 septies W-HO-J on the strict graph: the path of the corpus, edge by
edge, strict `HandoffOrdered` on the whole trace and no strict `Race`. -/
theorem W_HOJ_strict : PO hojσ hojLbls (.step 2) (.step 4) ∧
    SWS hojσ L0 hojLbls (.step 4) (.step 5) ∧ PO hojσ hojLbls (.step 5) (.step 6) ∧
    HBS hojσ L0 hojLbls (.step 2) (.step 6) ∧ HandoffOrderedS hojσ L0 hojLbls ∧
    ¬ RaceS hojσ L0 hojLbls := by
  have hkey : ∀ k (h : k < hojLbls.length), (hojLbls[k]'h).accMode ≠ none → k = 2 ∨ k = 6 := by
    decide
  have hb : HBS hojσ L0 hojLbls (.step 2) (.step 6) := by decide
  have hpair : ∀ l ∈ [1, 2], HandoffOrderedAtS hojσ L0 hojLbls 2 6 l := by decide
  refine ⟨by decide, by decide, by decide, hb, handoffOrderedS_of_two hkey (by decide) ?_,
    not_raceS_of_two hkey (by decide) hb⟩
  rintro l ⟨_, c, m, ⟨-, hl, -⟩⟩
  exact hpair l hl

/-- `corpus-spec2-m3.md` v9 §2 septies W-HO″-J on the strict graph: the path of the corpus, edge by
edge, strict `HandoffOrdered` on the whole trace and no strict `Race`. -/
theorem W_HO3J_strict : PO ho3jσ ho3jLbls (.step 4) (.step 6) ∧
    SWS ho3jσ L0 ho3jLbls (.step 6) (.step 7) ∧ PO ho3jσ ho3jLbls (.step 7) (.step 9) ∧
    SWS ho3jσ L0 ho3jLbls (.step 9) (.step 10) ∧ PO ho3jσ ho3jLbls (.step 10) (.step 11) ∧
    HBS ho3jσ L0 ho3jLbls (.step 4) (.step 11) ∧ HandoffOrderedS ho3jσ L0 ho3jLbls ∧
    ¬ RaceS ho3jσ L0 ho3jLbls := by
  have hkey : ∀ k (h : k < ho3jLbls.length), (ho3jLbls[k]'h).accMode ≠ none →
      k = 4 ∨ k = 11 := by
    decide
  have hb : HBS ho3jσ L0 ho3jLbls (.step 4) (.step 11) := by decide
  refine ⟨by decide, by decide, by decide, by decide, by decide, hb,
    handoffOrderedS_of_two hkey (by decide) ?_, not_raceS_of_two hkey (by decide) hb⟩
  rintro l ⟨_, c, m, ⟨-, hl, -⟩⟩
  rw [List.mem_singleton.1 hl]
  decide

/-- `corpus-spec2-m3.md` v9 §2 septies, mutex (`lc_trace`), on the strict graph: the path of the
corpus, edge by edge, the mutex edge from `unlock(e)` (step 9) to `acquire(e)` (step 10) being
strict; strict `HandoffOrdered` on the whole trace and no strict `Race`. -/
theorem lc_strict : PO lcσ lcLbls (.step 8) (.step 9) ∧ SWS lcσ L0 lcLbls (.step 9) (.step 10) ∧
    PO lcσ lcLbls (.step 10) (.step 11) ∧ HBS lcσ L0 lcLbls (.step 8) (.step 11) ∧
    HandoffOrderedS lcσ L0 lcLbls ∧ ¬ RaceS lcσ L0 lcLbls := by
  have hkey : ∀ k (h : k < lcLbls.length), (lcLbls[k]'h).accMode ≠ none → k = 8 ∨ k = 11 := by
    decide
  have hb : HBS lcσ L0 lcLbls (.step 8) (.step 11) := by decide
  refine ⟨by decide, by decide, by decide, hb, handoffOrderedS_of_two hkey (by decide) ?_,
    not_raceS_of_two hkey (by decide) hb⟩
  rintro l ⟨_, c, m, ⟨-, hl, -⟩⟩
  rw [List.mem_singleton.1 hl]
  decide

end Ern.Concurrency.Corpus.MutexEdgeStrict
