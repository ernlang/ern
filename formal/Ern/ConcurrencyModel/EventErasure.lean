import Ern.ConcurrencyModel.EventDecide

/-!
# Theorem 10b, 10c: erasure of pure authority markers (C29, C34; `OB-C19` abstract part, `OB-C26`)

`erase G X` removes the events satisfying `X`, projects `po` on the surviving events and restricts
`rf` and `mo` to them (C29, C34); `erasePure G` removes every pure authority marker (C34:
"`erasePure(G)` remove[s] all pure-authority markers identified in C29").

* 10b (C29, `OB-C19` abstract part): for every graph and every set of pure authority markers, `hb`
  between surviving events is the same before and after the erasure (`erase_hb_iff`), with the two
  instances of C29: one marker (`eraseOne_hb_iff`) and all markers (`erasePure_hb_iff`). The premises
  of C29 are: the erased events carry none of `acc`, `sync`, `validity` (they are pure authority
  markers); no `sw` edge touches them (`sw_not_pure`, a lemma, not a hypothesis); the projection of
  `po` keeps the order of the surviving events (`po` is transitive).
* 10c (C34, `OB-C26`): under the premises written by C34, that no erased marker is an endpoint of an
  `rf` or `mo` edge (a hypothesis, as in the clause; the absence of `sw` edges is derived), each of
  the seven conjuncts holds on the graph exactly when it holds on its erasure (seven separate
  statements), and so does `EventConsistent` (`erasePure_consistent_iff`). The property is proved,
  not posed: no eighth conjunct, no axiom. Corollary: conflicts and races between surviving events
  are unchanged (`erase_conflict_iff`, `erase_race_iff`).
* Necessity of the premise: a graph where a marker is an endpoint of an `mo` edge, on which
  conjunct 2 fails, while its erasure satisfies the seven conjuncts (`necessity_mo`).
-/

namespace Ern.ConcurrencyModel.Events

open Relation

/-! ## Transitive closures and removed nodes -/

section Closure

variable {E : Type} (X : E → Prop)

/-- A relation restricted to the elements outside `X`. -/
def restrictRel (R : E → E → Prop) (a b : {e // ¬ X e}) : Prop := R a.1 b.1

variable {X} {R po : E → E → Prop}

/-- A path of the restriction is a path of the relation. -/
theorem tg_of_restrict {a b : {e // ¬ X e}} (h : TransGen (restrictRel X R) a b) :
    TransGen R a.1 b.1 := by
  induction h with
  | single h => exact .single h
  | tail _ h ih => exact .tail ih h

/-- When the relation relates no element of `X`, a path between elements outside `X` is a path of
the restriction. -/
theorem tg_restrict_iff_of_closed (hR : ∀ x y, R x y → ¬ X x ∧ ¬ X y) (a b : {e // ¬ X e}) :
    TransGen (restrictRel X R) a b ↔ TransGen R a.1 b.1 := by
  refine ⟨tg_of_restrict, fun h => ?_⟩
  have key : ∀ {x y}, TransGen R x y → ∀ (hx : ¬ X x) (hy : ¬ X y),
      TransGen (restrictRel X R) ⟨x, hx⟩ ⟨y, hy⟩ := by
    intro x y h
    induction h with
    | single h => exact fun _ _ => .single h
    | tail _ h ih =>
      intro hx hy
      exact .tail (ih hx (hR _ _ h).1) h
  exact key h a.2 b.2

variable (hpoR : ∀ x y, po x y → R x y) (hpo : ∀ x y z, po x y → po y z → po x z)
  (hR : ∀ x y, R x y → X x ∨ X y → po x y)
include hpoR hpo hR

omit hpoR in
/-- A path from an element of `X` starts with a `po` step to an element outside `X`, or is a `po`
step. -/
theorem tg_from_X {x y : E} (h : TransGen R x y) (hx : X x) :
    po x y ∨ ∃ c, ¬ X c ∧ po x c ∧ TransGen R c y := by
  induction h with
  | single h => exact .inl (hR _ _ h (.inl hx))
  | @tail z w _ h ih =>
    rcases ih with hp | ⟨c, hc, hxc, hcz⟩
    · by_cases hz : X z
      · exact .inl (hpo _ _ _ hp (hR _ _ h (.inl hz)))
      · exact .inr ⟨z, hz, hp, .single h⟩
    · exact .inr ⟨c, hc, hxc, .tail hcz h⟩

omit hpoR in
/-- A path to an element of `X` ends with a `po` step from an element outside `X`, or is a `po`
step. -/
theorem tg_to_X {x y : E} (h : TransGen R x y) (hy : X y) :
    po x y ∨ ∃ c, ¬ X c ∧ TransGen R x c ∧ po c y := by
  induction h with
  | @single z h => exact .inl (hR _ _ h (.inr hy))
  | @tail z w hxz h ih =>
    have hzw := hR _ _ h (.inr hy)
    by_cases hz : X z
    · rcases ih hz with hp | ⟨c, hc, hxc, hcz⟩
      · exact .inl (hpo _ _ _ hp hzw)
      · exact .inr ⟨c, hc, hxc, hpo _ _ _ hcz hzw⟩
    · exact .inr ⟨z, hz, hxz, hzw⟩

/-- Between elements outside `X`, a path of the relation is a path of the restriction: the detours
through `X` are `po` steps, which `po` shortens. -/
theorem tg_restrict_iff (a b : {e // ¬ X e}) :
    TransGen (restrictRel X R) a b ↔ TransGen R a.1 b.1 := by
  refine ⟨tg_of_restrict, fun h => ?_⟩
  have key : ∀ {y}, TransGen R a.1 y → (∀ hy : ¬ X y, TransGen (restrictRel X R) a ⟨y, hy⟩) ∧
      (X y → po a.1 y ∨ ∃ c : {e // ¬ X e}, TransGen (restrictRel X R) a c ∧ po c.1 y) := by
    intro y h
    induction h with
    | @single y h =>
      refine ⟨fun hy => .single h, fun hy => .inl (hR _ _ h (.inr hy))⟩
    | @tail z y _ h ih =>
      by_cases hz : X z
      · have hzy := hR _ _ h (.inl hz)
        rcases ih.2 hz with hp | ⟨c, hac, hcz⟩
        · refine ⟨fun hy => .single (hpo _ _ _ hp hzy |> hpoR _ _), fun _ => .inl (hpo _ _ _ hp hzy)⟩
        · refine ⟨fun hy => .tail hac (hpoR _ _ (hpo _ _ _ hcz hzy)),
            fun _ => .inr ⟨c, hac, hpo _ _ _ hcz hzy⟩⟩
      · have haz := ih.1 hz
        refine ⟨fun hy => .tail haz h, fun hy => .inr ⟨⟨z, hz⟩, haz, hR _ _ h (.inr hy)⟩⟩
  exact (key h).1 b.2

/-- A cycle of the relation passes through an element outside `X`, when `po` is irreflexive. -/
theorem tg_cycle (hirr : ∀ x, ¬ po x x) {x : E} (h : TransGen R x x) :
    ∃ c : {e // ¬ X e}, TransGen R c.1 c.1 := by
  by_cases hx : X x
  · rcases tg_from_X hpo hR h hx with hp | ⟨c, hc, hxc, hcx⟩
    · exact (hirr x hp).elim
    · exact ⟨⟨c, hc⟩, .tail hcx (hpoR _ _ hxc)⟩
  · exact ⟨⟨x, hx⟩, h⟩

end Closure

/-! ## The erased graph -/

namespace Graph

variable {E C U V S : Type} (G : Graph E C U V S)

/-- The graph with the events satisfying `X` removed (C29, C34): the surviving events keep their
attributes, `po` is projected on them (it keeps the order of the surviving events of each context,
C29), and `rf` and `mo` are restricted to them. -/
def erase (X : E → Prop) : Graph {e // ¬ X e} C U V S where
  ev e := G.ev e.1
  uRange := G.uRange
  po a b := G.po a.1 b.1
  rf a b := G.rf a.1 b.1
  mo a b := G.mo a.1 b.1
  po_irrefl a := G.po_irrefl a.1
  po_trans := G.po_trans
  po_ctx := G.po_ctx
  po_total hc hne := G.po_total hc fun e => hne (Subtype.ext e)

/-- `erasePure(G)` (C34): every pure authority marker removed. -/
abbrev erasePure : Graph {e // ¬ G.Pure e} C U V S := G.erase G.Pure

instance [DecidableRel G.po] (X : E → Prop) : DecidableRel (G.erase X).po :=
  fun a b => inferInstanceAs (Decidable (G.po a.1 b.1))
instance [DecidableRel G.rf] (X : E → Prop) : DecidableRel (G.erase X).rf :=
  fun a b => inferInstanceAs (Decidable (G.rf a.1 b.1))
instance [DecidableRel G.mo] (X : E → Prop) : DecidableRel (G.erase X).mo :=
  fun a b => inferInstanceAs (Decidable (G.mo a.1 b.1))

instance [DecidableEq C] [DecidableEq U] [DecidableEq V] [DecidableEq S] (e : E) :
    Decidable (G.Pure e) := inferInstanceAs (Decidable (_ = _))

variable {X : E → Prop}

/-- An access, an event with a `sync` attribute or a designated unit is never a pure authority
marker. -/
theorem not_X_of_unit (hX : ∀ e, X e → G.Pure e) {e : E} {u : U} (h : G.unitOf e = some u) :
    ¬ X e := fun hx => G.not_pure_of_unitOf h (hX e hx)

/-- An event with an access kind is not an erased pure authority marker (C27). -/
theorem not_X_of_kind (hX : ∀ e, X e → G.Pure e) {e : E} {k : Kind} (h : G.kind? e = some k) :
    ¬ X e := fun hx => G.not_pure_of_kind h (hX e hx)

/-- A `seq_cst` event is not an erased pure authority marker (C27, C34). -/
theorem not_X_of_sc (hX : ∀ e, X e → G.Pure e) {e : E} (h : G.SC e) : ¬ X e := fun hx => by
  obtain ⟨u, k, h⟩ := h
  exact G.not_pure_of_unitOf (G.unitOf_atomic h) (hX e hx)

/-! ## `sw` and `hb` (10b) -/

/-- On surviving events, `sw` is unchanged by the erasure of pure authority markers (C29, C32): the
members of a release sequence and the events between them are accesses. -/
theorem erase_sw_iff (hX : ∀ e, X e → G.Pure e) (a b : {e // ¬ X e}) :
    (G.erase X).SW a b ↔ G.SW a.1 b.1 := by
  have hmem : ∀ (u : U) (m : {e // ¬ X e}), (G.erase X).RSMember u a m ↔ G.RSMember u a.1 m.1 := by
    intro u m
    constructor
    · rintro (rfl | ⟨hm, hhm, hall⟩)
      · exact .inl rfl
      · exact .inr ⟨hm, hhm, fun x hx h₁ h₂ =>
          hall ⟨x, G.not_X_of_unit hX hx.1⟩ hx h₁ h₂⟩
    · rintro (h | ⟨hm, hhm, hall⟩)
      · exact .inl (Subtype.ext h)
      · exact .inr ⟨hm, hhm, fun x hx h₁ h₂ => hall x.1 hx h₁ h₂⟩
  constructor
  · rintro (⟨u, m, hr, ha, hm, hrf⟩ | h)
    · exact .inl ⟨u, m.1, hr, ha, (hmem u m).1 hm, hrf⟩
    · exact .inr h
  · rintro (⟨u, m, hr, ha, hm, hrf⟩ | h)
    · have hmX : ¬ X m := by
        rcases hm with rfl | ⟨hm', -, -⟩
        · exact a.2
        · exact G.not_X_of_unit hX (G.modOn_of_rmw hm').1
      exact .inl ⟨u, ⟨m, hmX⟩, hr, ha, (hmem u ⟨m, hmX⟩).2 hm, hrf⟩
    · exact .inr h

/-- The edges of `po ∪ sw` that touch a pure authority marker are `po` edges (C29). -/
theorem posw_X_po (hX : ∀ e, X e → G.Pure e) (x y : E) (h : G.PoSw x y) (hxy : X x ∨ X y) :
    G.po x y := by
  rcases h with h | h
  · exact h
  · have := G.sw_not_pure h
    rcases hxy with hx | hy
    · exact (this.1 (hX _ hx)).elim
    · exact (this.2 (hX _ hy)).elim

/-- `po ∪ sw` of the erased graph is the restriction of `po ∪ sw`. -/
theorem erase_posw_eq (hX : ∀ e, X e → G.Pure e) :
    (G.erase X).PoSw = restrictRel X G.PoSw := by
  funext a b
  exact propext (or_congr Iff.rfl (G.erase_sw_iff hX a b))

/-- **Theorem 10b** (C29, `OB-C19` abstract part): for every graph and every set `X` of pure
authority markers, `hb` between surviving events is the same before and after the erasure of `X`.
The premises of C29: the erased events are pure authority markers (`hX`); no `sw` edge touches them
(`sw_not_pure`, derived); the projection of `po` keeps the order of the surviving events (`po` is
transitive). -/
theorem erase_hb_iff (hX : ∀ e, X e → G.Pure e) (a b : {e // ¬ X e}) :
    (G.erase X).HB a b ↔ G.HB a.1 b.1 := by
  unfold HB
  rw [G.erase_posw_eq hX]
  exact tg_restrict_iff (R := G.PoSw) (po := G.po) (fun _ _ h => Or.inl h) (fun _ _ _ => G.po_trans)
    (G.posw_X_po hX) a b

/-- **Theorem 10b, one marker** (C29: "removing … such markers … preserves `hb` between surviving
events"): the erasure of a single pure authority marker `m`. -/
theorem eraseOne_hb_iff {m : E} (hm : G.Pure m) (a b : {e // ¬ e = m}) :
    (G.erase (· = m)).HB a b ↔ G.HB a.1 b.1 :=
  G.erase_hb_iff (X := fun e => e = m) (fun e h => by subst h; exact hm) a b

/-- **Theorem 10b, all markers** (C29: "removing all such markers, with the appropriate `po`
projection, preserves `hb` between surviving events"). -/
theorem erasePure_hb_iff (a b : {e // ¬ G.Pure e}) : G.erasePure.HB a b ↔ G.HB a.1 b.1 :=
  G.erase_hb_iff (fun _ h => h) a b

/-- A path of `hb` from a pure authority marker. -/
theorem hb_from_X (hX : ∀ e, X e → G.Pure e) {x y : E} (h : G.HB x y) (hx : X x) :
    G.po x y ∨ ∃ c, ¬ X c ∧ G.po x c ∧ G.HB c y :=
  tg_from_X (R := G.PoSw) (po := G.po) (fun _ _ _ => G.po_trans) (G.posw_X_po hX) h hx

/-- A path of `hb` to a pure authority marker. -/
theorem hb_to_X (hX : ∀ e, X e → G.Pure e) {x y : E} (h : G.HB x y) (hy : X y) :
    G.po x y ∨ ∃ c, ¬ X c ∧ G.HB x c ∧ G.po c y :=
  tg_to_X (R := G.PoSw) (po := G.po) (fun _ _ _ => G.po_trans) (G.posw_X_po hX) h hy

/-- A cycle of `hb` passes through a surviving event. -/
theorem hb_cycle (hX : ∀ e, X e → G.Pure e) {x : E} (h : G.HB x x) :
    ∃ c : {e // ¬ X e}, G.HB c.1 c.1 :=
  tg_cycle (R := G.PoSw) (po := G.po) (fun _ _ h => Or.inl h) (fun _ _ _ => G.po_trans)
    (G.posw_X_po hX) G.po_irrefl h

/-! ## Conflicts and races (corollary of 10b) -/

/-- Conflicts between surviving events are unchanged by an erasure (C30). -/
theorem erase_conflict_iff (a b : {e // ¬ X e}) :
    (G.erase X).Conflict a b ↔ G.Conflict a.1 b.1 := Iff.rfl

/-- **Corollary of 10b** (C30, C33): races between surviving events are unchanged by the erasure
of pure authority markers. -/
theorem erase_race_iff (hX : ∀ e, X e → G.Pure e) (a b : {e // ¬ X e}) :
    (G.erase X).Race a b ↔ G.Race a.1 b.1 := by
  unfold Race
  rw [G.erase_hb_iff hX, G.erase_hb_iff hX]
  exact Iff.rfl

/-! ## The seven conjuncts (10c) -/

section Conjuncts

variable (hX : ∀ e, X e → G.Pure e) (hrf : ∀ x y, G.rf x y → ¬ X x ∧ ¬ X y)
  (hmo : ∀ x y, G.mo x y → ¬ X x ∧ ¬ X y)

include hX hrf in
/-- Conjunct 1 (C34.1) holds on the graph exactly when it holds after the erasure of a set `X` of
pure authority markers that no `rf` edge touches (C34, erasure premises). -/
theorem erase_rfWF_iff : (G.erase X).RfWF ↔ G.RfWF := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun w r h => h1 ⟨w, (hrf w r h).1⟩ ⟨r, (hrf w r h).2⟩ h, fun r u hr => ?_,
      fun w r h => h3 ⟨w, (hrf w r h).1⟩ ⟨r, (hrf w r h).2⟩ h⟩
    obtain ⟨⟨w, hw⟩, hu⟩ := h2 ⟨r, G.not_X_of_unit hX hr.1⟩ u hr
    refine ⟨⟨w.1, hw⟩, fun w₁ w₂ h₁ h₂ => ?_⟩
    have := hu ⟨w₁, (hrf _ _ h₁).1⟩ ⟨w₂, (hrf _ _ h₂).1⟩ h₁ h₂
    exact congrArg Subtype.val this
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun w r h => h1 w.1 r.1 h, fun r u hr => ?_, fun w r h => h3 w.1 r.1 h⟩
    obtain ⟨⟨w, hw⟩, hu⟩ := h2 r.1 u hr
    exact ⟨⟨⟨w, (hrf _ _ hw).1⟩, hw⟩, fun w₁ w₂ h₁ h₂ => Subtype.ext (hu w₁.1 w₂.1 h₁ h₂)⟩

include hX hmo in
/-- Conjunct 2 (C34.2) holds on the graph exactly when it holds after the erasure of a set `X` of
pure authority markers that no `mo` edge touches (C34, erasure premises). -/
theorem erase_moTotal_iff : (G.erase X).MoTotal ↔ G.MoTotal := by
  have hs : ∀ {e : E} {u : U}, G.ModOn e u → ¬ X e := fun h => G.not_X_of_unit hX h.1
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun a b h => h1 ⟨a, (hmo a b h).1⟩ ⟨b, (hmo a b h).2⟩ h, fun u => ?_⟩
    obtain ⟨hi, ht, hto⟩ := h2 u
    refine ⟨fun a ha => hi ⟨a, hs ha⟩ ha, fun a b c ha hb hc => ht ⟨a, hs ha⟩ ⟨b, hs hb⟩
      ⟨c, hs hc⟩ ha hb hc, fun a b ha hb hab => hto ⟨a, hs ha⟩ ⟨b, hs hb⟩ ha hb ?_⟩
    exact fun e => hab (congrArg Subtype.val e)
  · rintro ⟨h1, h2⟩
    refine ⟨fun a b h => h1 a.1 b.1 h, fun u => ?_⟩
    obtain ⟨hi, ht, hto⟩ := h2 u
    exact ⟨fun a ha => hi a.1 ha, fun a b c ha hb hc => ht a.1 b.1 c.1 ha hb hc,
      fun a b ha hb hab => hto a.1 b.1 ha hb fun e => hab (Subtype.ext e)⟩

include hrf hmo in
/-- Conjunct 3 (C34.3) holds on the graph exactly when it holds after the erasure of a set `X` of
events that no `rf` or `mo` edge touches (C34, erasure premises). -/
theorem erase_rmwAtomic_iff : (G.erase X).RmwAtomic ↔ G.RmwAtomic := by
  constructor
  · intro h w r hr hrfwr
    obtain ⟨hm, himm⟩ := h ⟨w, (hrf w r hrfwr).1⟩ ⟨r, (hrf w r hrfwr).2⟩ hr hrfwr
    exact ⟨hm, fun x ⟨h₁, h₂⟩ => himm ⟨x, (hmo _ _ h₁).2⟩ ⟨h₁, h₂⟩⟩
  · intro h w r hr hrfwr
    obtain ⟨hm, himm⟩ := h w.1 r.1 hr hrfwr
    exact ⟨hm, fun x hx => himm x.1 hx⟩

/-- `rb` of the erased graph is the restriction of `rb`. -/
theorem erase_rb_iff (hrf : ∀ x y, G.rf x y → ¬ X x ∧ ¬ X y) (a b : {e // ¬ X e}) :
    (G.erase X).RB a b ↔ G.RB a.1 b.1 := by
  constructor
  · rintro ⟨⟨w, h₁, h₂⟩, hne⟩
    exact ⟨⟨w.1, h₁, h₂⟩, fun e => hne (Subtype.ext e)⟩
  · rintro ⟨⟨w, h₁, h₂⟩, hne⟩
    exact ⟨⟨⟨w, (hrf _ _ h₁).1⟩, h₁, h₂⟩, fun e => hne (congrArg Subtype.val e)⟩

/-- The edges of `rf ∪ mo ∪ rb` relate surviving events. -/
theorem ecoBase_not_X (hrf : ∀ x y, G.rf x y → ¬ X x ∧ ¬ X y)
    (hmo : ∀ x y, G.mo x y → ¬ X x ∧ ¬ X y) (x y : E) (h : G.EcoBase x y) : ¬ X x ∧ ¬ X y := by
  rcases h with h | h | ⟨⟨w, h₁, h₂⟩, -⟩
  · exact hrf x y h
  · exact hmo x y h
  · exact ⟨(hrf _ _ h₁).2, (hmo _ _ h₂).2⟩

include hrf hmo in
/-- `eco` (C34.4) between surviving events is unchanged by the erasure of a set `X` of events that
no `rf` or `mo` edge touches (C34, erasure premises). -/
theorem erase_eco_iff (a b : {e // ¬ X e}) : (G.erase X).ECO a b ↔ G.ECO a.1 b.1 := by
  have heq : (G.erase X).EcoBase = restrictRel X G.EcoBase := by
    funext a b
    exact propext (or_congr Iff.rfl (or_congr Iff.rfl (G.erase_rb_iff hrf a b)))
  unfold ECO
  rw [heq]
  exact tg_restrict_iff_of_closed (G.ecoBase_not_X hrf hmo) a b

include hX hrf hmo in
/-- Conjunct 4 (C34.4) holds on the graph exactly when it holds after the erasure of a set `X` of
pure authority markers that no `rf` or `mo` edge touches (C29, C34). -/
theorem erase_coherence_iff : (G.erase X).Coherence ↔ G.Coherence := by
  constructor
  · intro h a b hab hba
    rcases hba with rfl | heco
    · obtain ⟨c, hc⟩ := G.hb_cycle hX hab
      exact h c c ((G.erase_hb_iff hX c c).2 hc) (.inl rfl)
    · have hb : ¬ X b := by
        cases heco with
        | single h => exact (G.ecoBase_not_X hrf hmo _ _ h).1
        | tail h _ =>
          have : ∀ {x y}, TransGen G.EcoBase x y → ¬ X x := fun h => by
            induction h with
            | single h => exact (G.ecoBase_not_X hrf hmo _ _ h).1
            | tail _ _ ih => exact ih
          exact this h
      have ha : ¬ X a := by
        cases heco with
        | single h => exact (G.ecoBase_not_X hrf hmo _ _ h).2
        | tail _ h => exact (G.ecoBase_not_X hrf hmo _ _ h).2
      exact h ⟨a, ha⟩ ⟨b, hb⟩ ((G.erase_hb_iff hX ⟨a, ha⟩ ⟨b, hb⟩).2 hab)
        (.inr ((G.erase_eco_iff hrf hmo ⟨b, hb⟩ ⟨a, ha⟩).2 heco))
  · intro h a b hab hba
    refine h a.1 b.1 ((G.erase_hb_iff hX a b).1 hab) ?_
    rcases hba with rfl | heco
    · exact .inl rfl
    · exact .inr ((G.erase_eco_iff hrf hmo b a).1 heco)

include hX in
/-- Conjunct 5 (C34.5) holds on the graph exactly when it holds after the erasure of any set `X` of
pure authority markers (C29, C34). -/
theorem erase_hbIrrefl_iff : (G.erase X).HbIrrefl ↔ G.HbIrrefl := by
  constructor
  · intro h a ha
    obtain ⟨c, hc⟩ := G.hb_cycle hX ha
    exact h c ((G.erase_hb_iff hX c c).2 hc)
  · intro h a ha
    exact h a.1 ((G.erase_hb_iff hX a a).1 ha)

include hrf in
/-- Conjunct 6 (C34.6) holds on the graph exactly when it holds after the erasure of a set `X` of
events that no `rf` edge touches (C29, C34). -/
theorem erase_noThinAir_iff : (G.erase X).NoThinAir ↔ G.NoThinAir := by
  have hR : ∀ x y, G.PoRf x y → X x ∨ X y → G.po x y := by
    rintro x y (h | h) hxy
    · exact h
    · rcases hxy with hx | hy
      · exact ((hrf x y h).1 hx).elim
      · exact ((hrf x y h).2 hy).elim
  have heq : (G.erase X).PoRf = restrictRel X G.PoRf := rfl
  unfold NoThinAir Acyclic
  rw [heq]
  constructor
  · intro h a ha
    obtain ⟨c, hc⟩ := tg_cycle (R := G.PoRf) (po := G.po) (fun _ _ h => Or.inl h)
      (fun _ _ _ => G.po_trans) hR G.po_irrefl ha
    exact h c ((tg_restrict_iff (R := G.PoRf) (po := G.po) (fun _ _ h => Or.inl h)
      (fun _ _ _ => G.po_trans) hR c c).2 hc)
  · intro h a ha
    exact h a.1 ((tg_restrict_iff (R := G.PoRf) (po := G.po) (fun _ _ h => Or.inl h)
      (fun _ _ _ => G.po_trans) hR a a).1 ha)

include hX hrf in
/-- `scb` between surviving events is unchanged: a middle term `po ; hb ; po` whose intermediate
events are markers shortens into `po`, or into a middle term between surviving events. -/
theorem erase_scb_iff (a b : {e // ¬ X e}) : (G.erase X).SCB a b ↔ G.SCB a.1 b.1 := by
  constructor
  · rintro (h | ⟨x, y, h₁, h₂, h₃⟩ | ⟨h, hl⟩ | h | h)
    · exact .inl h
    · exact .inr (.inl ⟨x.1, y.1, h₁, (G.erase_hb_iff hX x y).1 h₂, h₃⟩)
    · exact .inr (.inr (.inl ⟨(G.erase_hb_iff hX a b).1 h, hl⟩))
    · exact .inr (.inr (.inr (.inl h)))
    · exact .inr (.inr (.inr (.inr ((G.erase_rb_iff hrf a b).1 h))))
  · rintro (h | ⟨x, y, h₁, h₂, h₃⟩ | ⟨h, hl⟩ | h | h)
    · exact .inl h
    · -- the middle term
      have mid : ∀ (c d : {e // ¬ X e}), G.po a.1 c.1 → G.HB c.1 d.1 → G.po d.1 b.1 →
          (G.erase X).SCB a b := fun c d h₁ h₂ h₃ =>
        .inr (.inl ⟨c, d, h₁, (G.erase_hb_iff hX c d).2 h₂, h₃⟩)
      have viaPo : G.po a.1 b.1 → (G.erase X).SCB a b := fun h => .inl h
      by_cases hx : X x
      · rcases G.hb_from_X hX h₂ hx with hp | ⟨c, hc, hxc, hcy⟩
        · exact viaPo (G.po_trans h₁ (G.po_trans hp h₃))
        · have hac := G.po_trans h₁ hxc
          by_cases hy : X y
          · rcases G.hb_to_X hX hcy hy with hp | ⟨d, hd, hcd, hdy⟩
            · exact viaPo (G.po_trans hac (G.po_trans hp h₃))
            · exact mid ⟨c, hc⟩ ⟨d, hd⟩ hac hcd (G.po_trans hdy h₃)
          · exact mid ⟨c, hc⟩ ⟨y, hy⟩ hac hcy h₃
      · by_cases hy : X y
        · rcases G.hb_to_X hX h₂ hy with hp | ⟨d, hd, hxd, hdy⟩
          · exact viaPo (G.po_trans h₁ (G.po_trans hp h₃))
          · exact mid ⟨x, hx⟩ ⟨d, hd⟩ h₁ hxd (G.po_trans hdy h₃)
        · exact mid ⟨x, hx⟩ ⟨y, hy⟩ h₁ h₂ h₃
    · exact .inr (.inr (.inl ⟨(G.erase_hb_iff hX a b).2 h, hl⟩))
    · exact .inr (.inr (.inr (.inl h)))
    · exact .inr (.inr (.inr (.inr ((G.erase_rb_iff hrf a b).2 h))))

include hX hrf in
/-- Conjunct 7 (C34.7) holds on the graph exactly when it holds after the erasure of a set `X` of
pure authority markers that no `rf` edge touches (C29, C34). -/
theorem erase_scConsistent_iff : (G.erase X).SCConsistent ↔ G.SCConsistent := by
  have heq : (G.erase X).PSC = restrictRel X G.PSC := by
    funext a b
    exact propext (and_congr Iff.rfl (and_congr (G.erase_scb_iff hX hrf a b) Iff.rfl))
  have hcl : ∀ x y, G.PSC x y → ¬ X x ∧ ¬ X y := fun x y h =>
    ⟨G.not_X_of_sc hX h.1, G.not_X_of_sc hX h.2.2⟩
  unfold SCConsistent Acyclic
  rw [heq]
  constructor
  · intro h a ha
    have hx : ¬ X a := by
      cases ha with
      | single h => exact (hcl _ _ h).1
      | tail _ h => exact (hcl _ _ h).2
    exact h ⟨a, hx⟩ ((tg_restrict_iff_of_closed hcl ⟨a, hx⟩ ⟨a, hx⟩).2 ha)
  · intro h a ha
    exact h a.1 ((tg_restrict_iff_of_closed hcl a a).1 ha)

end Conjuncts

/-! ## The seven conjuncts under `erasePure` (10c) -/

section ErasePure

/-- The premise of C34 on `rf`: no pure authority marker is an endpoint of an `rf` edge. -/
def RfAvoidsPure : Prop := ∀ x y, G.rf x y → ¬ G.Pure x ∧ ¬ G.Pure y

/-- The premise of C34 on `mo`: no pure authority marker is an endpoint of an `mo` edge. -/
def MoAvoidsPure : Prop := ∀ x y, G.mo x y → ¬ G.Pure x ∧ ¬ G.Pure y

variable {G}

/-- **Theorem 10c, conjunct 1** (C34.1, `OB-C26`). -/
theorem erasePure_rfWF_iff (hrf : G.RfAvoidsPure) : G.erasePure.RfWF ↔ G.RfWF := G.erase_rfWF_iff (fun _ h => h) hrf

/-- **Theorem 10c, conjunct 2** (C34.2, `OB-C26`). -/
theorem erasePure_moTotal_iff (hmo : G.MoAvoidsPure) : G.erasePure.MoTotal ↔ G.MoTotal :=
  G.erase_moTotal_iff (fun _ h => h) hmo

/-- **Theorem 10c, conjunct 3** (C34.3, `OB-C26`). -/
theorem erasePure_rmwAtomic_iff (hrf : G.RfAvoidsPure) (hmo : G.MoAvoidsPure) : G.erasePure.RmwAtomic ↔ G.RmwAtomic :=
  G.erase_rmwAtomic_iff hrf hmo

/-- **Theorem 10c, conjunct 4** (C34.4, `OB-C26`). -/
theorem erasePure_coherence_iff (hrf : G.RfAvoidsPure) (hmo : G.MoAvoidsPure) : G.erasePure.Coherence ↔ G.Coherence :=
  G.erase_coherence_iff (fun _ h => h) hrf hmo

/-- **Theorem 10c, conjunct 5** (C34.5, `OB-C26`); it needs neither premise. -/
theorem erasePure_hbIrrefl_iff : G.erasePure.HbIrrefl ↔ G.HbIrrefl :=
  G.erase_hbIrrefl_iff (fun _ h => h)

/-- **Theorem 10c, conjunct 6** (C34.6, `OB-C26`); it needs the premise on `rf` only. -/
theorem erasePure_noThinAir_iff (hrf : G.RfAvoidsPure) : G.erasePure.NoThinAir ↔ G.NoThinAir :=
  G.erase_noThinAir_iff hrf

/-- **Theorem 10c, conjunct 7** (C34.7, `OB-C26`); it needs the premise on `rf` only. -/
theorem erasePure_scConsistent_iff (hrf : G.RfAvoidsPure) : G.erasePure.SCConsistent ↔ G.SCConsistent :=
  G.erase_scConsistent_iff (fun _ h => h) hrf

/-- **Theorem 10c** (C34: "the required property is `EventConsistent(G) ↔
EventConsistent(erasePure(G))`"; `OB-C26`): under the premises of C34, that no erased marker is an
endpoint of an `rf` or `mo` edge, `EventConsistent` holds on the graph exactly when it holds on its
erasure. The absence of `sw` edges on the markers is derived (`sw_not_pure`). Proved, not posed. -/
theorem erasePure_consistent_iff (hrf : G.RfAvoidsPure) (hmo : G.MoAvoidsPure) : G.erasePure.EventConsistent ↔ G.EventConsistent :=
  and_congr (erasePure_rfWF_iff hrf) (and_congr (erasePure_moTotal_iff hmo)
    (and_congr (erasePure_rmwAtomic_iff hrf hmo) (and_congr (erasePure_coherence_iff hrf hmo)
      (and_congr erasePure_hbIrrefl_iff (and_congr (erasePure_noThinAir_iff hrf)
        (erasePure_scConsistent_iff hrf))))))

end ErasePure

end Graph

/-! ## Necessity of the premise -/

namespace NecessityMo

/-- An initial write of the unit `0` and a pure authority marker in context `0`, with an `mo` edge
from the write to the marker. -/
def W : ListGraph 2 (Fin 1) (Fin 1) Nat Unit where
  ev
    | 0 => ⟨0, ⟨0, 0⟩, .marks (some (.unit 0 (.write 0))) none⟩
    | 1 => ⟨0, ⟨0, 1⟩, .marks none none⟩
  uRange _ := ⟨0, 1⟩
  rf := []
  mo := [(0, 1)]

/-- **Necessity of the premise of 10c** (C34, `OB-C26`): when a marker is an endpoint of an `mo`
edge, conjunct 2 fails on the graph while its erasure satisfies the seven conjuncts. -/
theorem necessity_mo :
    ¬ W.toGraph.MoAvoidsPure ∧ ¬ W.toGraph.MoTotal ∧ W.toGraph.erasePure.EventConsistent := by
  refine ⟨fun h => (h 0 1 (List.mem_singleton.2 rfl)).2 rfl, by decide +kernel, by decide +kernel⟩

end NecessityMo

end Ern.ConcurrencyModel.Events
