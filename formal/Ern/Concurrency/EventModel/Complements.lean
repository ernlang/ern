import Ern.Concurrency.EventModel.Lemmas
import Ern.Concurrency.EventModel.Witness

/-!
# Complements of the event fragment

Brief of milestone 4, slice 2, layer R, task 0 (`formal/reports/spec2-m4-mutexreal.md`): four
statements on the fragment of layer E, beside its definitions, which are unchanged.

* G1 with the events of `c1` listed before those of `c0`, so that `rf` and `sw` go from a higher
  index to a lower one (`G1_back`);
* `HB` is transitive (`hb_trans`);
* `HB` from an event other than the initial write is the transitive closure of `po ∪ sw`
  (`hb_closure`): the convention on the initial write never orders two other events;
* under conjuncts 1 to 3 of `EventConsistent`, `eco` is irreflexive (`eco_irrefl`).
-/

set_option autoImplicit false

namespace Ern.Concurrency.EventModel

/-! ## G1 with a backward edge -/

/-- G1 (`mp .rel .acq`) listed from `c1`: `e = readShared(x, acquire)` (1) reading `1` from `b`,
`g = read3(d)` (2); then `c0`: `a = write3(d)` (3), `b = writeShared(x, 1, release)` (4); `mo`:
`init < b`. -/
def g1back : Graph :=
  { init := 0, evs := [⟨1, .rsh .acq 1⟩, ⟨1, .readD⟩, ⟨0, .writeD⟩, ⟨0, .wsh .rel 1⟩],
    rf := [(4, 1)], mo := chain [0, 4] }

/-- Brief, task 0: in `g1back` the `rf` and `sw` edges go from event 4 to event 1. As G1: well
typed, consistent, `sw(b, e)`, `hb(a, g)`, no race. -/
theorem G1_back : RF g1back 4 1 ∧ WellTyped g1back ∧ EventConsistent g1back ∧ SW g1back 4 1 ∧
    HB g1back 3 2 ∧ ¬ Racy g1back := by
  decide

/-! ## `HB` -/

/-- The initial write has no kind. -/
theorem kind?_zero (g : Graph) : g.kind? 0 = none := by
  simp [Graph.kind?, Graph.ev?]

/-- No edge of `po ∪ sw` ends at the initial write: `po` starts after it and the initial write is
not acquire-capable. -/
theorem poSw_ne_zero {g : Graph} {a b : Nat} (h : PoSw g a b) : b ≠ 0 := by
  rcases h with ⟨h1, h2, -⟩ | ⟨-, -, h⟩
  · exact Nat.ne_of_gt (Nat.lt_trans h1 h2)
  · intro hb
    subst hb
    simp [Graph.acqCap, kind?_zero] at h

/-- The last edge of a path of `po ∪ sw` does not end at the initial write. -/
theorem transGen_ne_zero {g : Graph} {a b : Nat} (h : Relation.TransGen (PoSw g) a b) : b ≠ 0 := by
  cases h with
  | single h => exact poSw_ne_zero h
  | tail _ h => exact poSw_ne_zero h

/-- A path of `po ∪ sw` ends at an event of the graph. -/
theorem transGen_lt {g : Graph} {a b : Nat} (h : Relation.TransGen (PoSw g) a b) : b < g.size := by
  cases h with
  | single h => exact (poSw_lt h).2
  | tail _ h => exact (poSw_lt h).2

/-- Brief, task 0: `HB` is transitive. -/
theorem hb_trans {g : Graph} {a b c : Nat} (hab : HB g a b) (hbc : HB g b c) : HB g a c := by
  rcases hab with hab | ⟨rfl, hb, -⟩
  · rcases hbc with hbc | ⟨rfl, -, -⟩
    · exact Or.inl (Relation.TransGen.trans hab hbc)
    · exact absurd rfl (transGen_ne_zero hab)
  · rcases hbc with hbc | ⟨rfl, -, -⟩
    · exact Or.inr ⟨rfl, Nat.pos_of_ne_zero (transGen_ne_zero hbc), transGen_lt hbc⟩
    · exact absurd hb (Nat.lt_irrefl 0)

/-- Brief, task 0: if `HB a b` and `a` is not the initial write, then `a` and `b` are related by the
transitive closure of `po ∪ sw`. -/
theorem hb_closure {g : Graph} {a b : Nat} (h : HB g a b) (ha : a ≠ 0) :
    Relation.TransGen (PoSw g) a b := by
  rcases h with h | ⟨rfl, -, -⟩
  · exact h
  · exact absurd rfl ha

/-! ## `eco` is irreflexive -/

/-- Number of the `mo`-predecessors of `a`. -/
def moRank (g : Graph) (a : Nat) : Nat :=
  ((List.range g.size).filter fun c => decide (MO g c a)).length

/-- The first `rf` source of `r`, `0` if there is none. -/
def rfSrc (g : Graph) (r : Nat) : Nat :=
  ((List.range g.size).find? fun w => decide (RF g w r)).getD 0

/-- Rank of an event along `eco`: twice the `mo` rank of a modification; for another event, one
more than twice the `mo` rank of its `rf` source. -/
def ecoRank (g : Graph) (a : Nat) : Nat :=
  if g.isMod a then 2 * moRank g a else 2 * moRank g (rfSrc g a) + 1

/-- Under conjunct 2, `mo` increases the `mo` rank. -/
theorem moRank_lt {g : Graph} (h : MoTotal g) {a b : Nat} (hab : MO g a b) :
    moRank g a < moRank g b := by
  obtain ⟨-, hirr, htr, -⟩ := h
  have ha : a ∈ List.range g.size := List.mem_range.2 hab.2.1
  have hb : b ∈ List.range g.size := List.mem_range.2 hab.2.2
  refine filter_length_lt (fun x hx hxa => ?_) fun hall => ?_
  · exact decide_eq_true (htr x hx a ha b hb (of_decide_eq_true hxa) hab)
  · exact hirr a ha (of_decide_eq_true (hall a ha (decide_eq_true hab)))

/-- Under conjunct 1, the `rf` source of a read is its unique source. -/
theorem rfSrc_eq {g : Graph} (h : RfWF g) {w r : Nat} (hwr : RF g w r) : rfSrc g r = w := by
  obtain ⟨hk, huniq⟩ := h
  have hr : r ∈ List.range g.size := List.mem_range.2 hwr.2.2
  have hw : w ∈ List.range g.size := List.mem_range.2 hwr.2.1
  obtain ⟨w₀, -, -, hu⟩ := huniq r hr (hk w hw r hr hwr).2.1
  unfold rfSrc
  cases hf : (List.range g.size).find? (fun w => decide (RF g w r)) with
  | none =>
    exact absurd (List.find?_eq_none.1 hf w hw) (by simp [hwr])
  | some w' =>
    have hw' := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    simp only [decide_eq_true_eq] at hp
    rw [Option.getD_some, hu w' hw' hp, hu w hw hwr]

/-- A modification that reads `x` is a successful RMW. -/
theorem isRMW_of_mod_read {g : Graph} {a : Nat} (hm : g.isMod a = true)
    (hr : g.isReadX a = true) : g.isRMW a = true := by
  unfold Graph.isReadX at hr
  unfold Graph.isMod at hm
  unfold Graph.isRMW
  cases hk : g.kind? a with
  | none => rw [hk] at hr; cases hr
  | some k =>
    cases k <;> rw [hk] at hr hm <;> first | rfl | cases hr | skip
    all_goals
      have ha : a = 0 := by simpa using hm
      subst ha
      rw [kind?_zero] at hk; cases hk

/-- Under conjuncts 1 to 3, every edge of `rf ∪ mo ∪ rb` increases `ecoRank`. -/
theorem ecoRank_lt {g : Graph} (h1 : RfWF g) (h2 : MoTotal g) (h3 : RmwAtomic g) {a b : Nat}
    (h : EcoBase g a b) : ecoRank g a < ecoRank g b := by
  rcases h with hrf | hmo | ⟨⟨w, -, hwa, hwb⟩, hne⟩
  · have ha : a ∈ List.range g.size := List.mem_range.2 hrf.2.1
    have hb : b ∈ List.range g.size := List.mem_range.2 hrf.2.2
    obtain ⟨hma, hrb, -⟩ := h1.1 a ha b hb hrf
    unfold ecoRank
    rw [hma]
    cases hmb : g.isMod b
    · simp only [Bool.false_eq_true, ↓reduceIte, rfSrc_eq h1 hrf]; omega
    · have := moRank_lt h2 (h3 b hb (isRMW_of_mod_read hmb hrb) a ha hrf).1
      simp only [↓reduceIte]; omega
  · have ha : a ∈ List.range g.size := List.mem_range.2 hmo.2.1
    have hb : b ∈ List.range g.size := List.mem_range.2 hmo.2.2
    obtain ⟨hma, hmb⟩ := h2.1 a ha b hb hmo
    unfold ecoRank
    rw [hma, hmb]
    have := moRank_lt h2 hmo
    simp only [↓reduceIte]; omega
  · have hw : w ∈ List.range g.size := List.mem_range.2 hwa.2.1
    have ha : a ∈ List.range g.size := List.mem_range.2 hwa.2.2
    have hb : b ∈ List.range g.size := List.mem_range.2 hwb.2.2
    obtain ⟨-, hra, -⟩ := h1.1 w hw a ha hwa
    obtain ⟨-, hmb⟩ := h2.1 w hw b hb hwb
    unfold ecoRank
    rw [hmb]
    cases hma : g.isMod a
    · simp only [Bool.false_eq_true, ↓reduceIte, rfSrc_eq h1 hwa]
      have := moRank_lt h2 hwb
      omega
    · have hab : MO g a b := by
        rcases h2.2.2.2 a ha b hb hma hmb hne with hab | hba
        · exact hab
        · exact absurd ⟨hwb, hba⟩
            ((h3 a ha (isRMW_of_mod_read hma hra) w hw hwa).2 b hb)
      have := moRank_lt h2 hab
      simp only [↓reduceIte]; omega

/-- Brief, task 0: under conjuncts 1 (`RfWF`), 2 (`MoTotal`) and 3 (`RmwAtomic`) of
`EventConsistent`, `eco` is irreflexive (WC5.1 corrigé C31). -/
theorem eco_irrefl {g : Graph} (h1 : RfWF g) (h2 : MoTotal g) (h3 : RmwAtomic g) (a : Nat) :
    ¬ ECO g a a := by
  have key : ∀ {x y : Nat}, ECO g x y → ecoRank g x < ecoRank g y := by
    intro x y hxy
    induction hxy with
    | single h => exact ecoRank_lt h1 h2 h3 h
    | tail _ h ih => exact Nat.lt_trans ih (ecoRank_lt h1 h2 h3 h)
  exact fun h => Nat.lt_irrefl _ (key h)

end Ern.Concurrency.EventModel
