import Ern.Concurrency.EventModel.Graph

/-!
# General lemmas of the event fragment

Brief of milestone 4, slice 2 (layer E), task 2 (`formal/reports/spec2-m4-eventmodel.md`): six
statements for every graph, with no hypothesis on its shape. Each docstring names the conjuncts of
`EventConsistent` that the proof uses.
-/

set_option autoImplicit false

namespace Ern.Concurrency.EventModel

/-- Brief, task 2: conjunct 5 follows from conjunct 4. -/
theorem hbIrrefl_of_coherent {g : Graph} (h : Coherent g) : HbIrrefl g :=
  fun a ha => (h a ha).1

/-- A successful RMW is a modification of `x` (WC5.1 corrigé C31). -/
theorem isMod_of_isRMW {g : Graph} {m : Nat} (h : g.isRMW m = true) : g.isMod m = true := by
  unfold Graph.isRMW at h
  unfold Graph.isMod
  cases hk : g.kind? m with
  | none => rw [hk] at h; cases h
  | some k => cases k <;> rw [hk] at h <;> first | exact Bool.or_true _ | cases h

/-- Brief, task 2: in a consistent graph, the initial write is minimal for `mo`. Uses conjunct 2
(irreflexivity of `mo`) and conjunct 4 (coherence), with the convention that the initial write is
`hb`-before every other event. -/
theorem init_mo_minimal {g : Graph} (h : EventConsistent g) (m : Nat) : ¬ MO g m 0 := by
  intro hm
  obtain ⟨-, ⟨-, hirr, -⟩, -, hcoh, -⟩ := h
  have hlt : m < g.size := hm.2.1
  have h0 : 0 < g.size := hm.2.2
  have hne : m ≠ 0 := fun he => by subst he; exact hirr 0 (List.mem_range.2 h0) hm
  have hhb : HB g 0 m := Or.inr ⟨rfl, Nat.pos_of_ne_zero hne, hlt⟩
  exact (hcoh 0 (List.mem_range.2 h0)).2 m (List.mem_range.2 hlt) hhb
    (.single (Or.inr (Or.inl hm)))

/-- Brief, task 2: in a consistent graph, no read reads a modification that follows it in `hb`.
Uses conjunct 4 (coherence) only. -/
theorem rf_not_hb_later {g : Graph} (h : EventConsistent g) {w r : Nat} (hrf : RF g w r) :
    ¬ HB g r w := by
  intro hhb
  obtain ⟨-, -, -, hcoh, -⟩ := h
  exact (hcoh r (List.mem_range.2 hrf.2.2)).2 w (List.mem_range.2 hrf.2.1) hhb
    (.single (Or.inl hrf))

/-- Brief, task 2: in a consistent graph, two distinct successful RMWs do not read the same
modification, whatever their orders (WC5.1 corrigé C31). Uses conjunct 2 (totality of `mo`) and
conjunct 3 (atomicity of the RMWs). -/
theorem rmw_sources_distinct {g : Graph} (h : EventConsistent g) {w m₁ m₂ : Nat}
    (h₁ : g.isRMW m₁ = true) (h₂ : g.isRMW m₂ = true) (hne : m₁ ≠ m₂) (hr₁ : RF g w m₁)
    (hr₂ : RF g w m₂) : False := by
  obtain ⟨-, ⟨-, -, -, htot⟩, hat, -, -⟩ := h
  have hw : w ∈ List.range g.size := List.mem_range.2 hr₁.2.1
  have hm₁ : m₁ ∈ List.range g.size := List.mem_range.2 hr₁.2.2
  have hm₂ : m₂ ∈ List.range g.size := List.mem_range.2 hr₂.2.2
  obtain ⟨hw₁, himm₁⟩ := hat m₁ hm₁ h₁ w hw hr₁
  obtain ⟨hw₂, himm₂⟩ := hat m₂ hm₂ h₂ w hw hr₂
  rcases htot m₁ hm₁ m₂ hm₂ (isMod_of_isRMW h₁) (isMod_of_isRMW h₂) hne with h12 | h21
  · exact himm₂ m₁ hm₁ ⟨hw₁, h12⟩
  · exact himm₁ m₂ hm₂ ⟨hw₂, h21⟩

/-- Brief, task 2: two atomic events are never in a race (WC5.1 corrigé C33 item 3). -/
theorem atomic_no_race {g : Graph} {a b : Nat} (ha : g.isAtomic a = true)
    (hb : g.isAtomic b = true) : ¬ RaceOn g a b := by
  rintro ⟨-, h | h, -⟩
  · rw [ha] at h; cases h
  · rw [hb] at h; cases h

/-- Brief, task 2: a conflicting pair ordered by `hb` is not in a race (WC5.1 corrigé C33
item 4). -/
theorem hb_no_race {g : Graph} {a b : Nat} (h : HB g a b ∨ HB g b a) : ¬ RaceOn g a b := by
  rintro ⟨-, -, hab, hba⟩
  rcases h with h | h
  · exact hab h
  · exact hba h

end Ern.Concurrency.EventModel
