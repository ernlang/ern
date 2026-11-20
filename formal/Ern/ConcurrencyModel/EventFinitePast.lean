import Ern.ConcurrencyModel.EventErasure

/-!
# Theorem 10, complement: finite causal past (C26, C29, C34, C48; `OB-C23`)

C34: "An admissible event graph, finite or potentially unbounded (C26), must satisfy
`PrefixFinite((po ∪ sw ∪ rf)⁺)`"; it is "an **additional event-graph admissibility condition**,
separate from the seven conjuncts of `EventConsistent`". The verification targets of C34
("Infinite-graph verification targets, not additional axioms"):

* 10f: every graph whose type of events is finite has a finite causal past (`finiteCausalPast_of_finite`);
* 10g: under conjuncts 1 to 3 and a finite causal past, membership in the release sequence (retained
  reading 5, `RSMember`) agrees with the finite `rf` chains of atomic RMWs (`rsMember_iff_chain_fcp`);
  the proof needs only finitely many `rf`-ancestors of the member (`rsMember_iff_chain_of_rfPast`),
  and statement 3 of `EventLemmas` (`rsMember_iff_chain`, on a finite graph) follows;
* 10h: under a finite causal past, every finite set of events has a finite extension closed under
  the predecessors of `po ∪ sw ∪ rf` (`exists_closed_extension`); under `EventConsistent`, the
  graph induced on such a set is `EventConsistent`, and `sw`, `hb` and the races between its events
  are those of the whole graph (`induced_judgments`);
* 10i: erasing the pure authority markers keeps a finite causal past (`erasePure_finiteCausalPast`);
  no converse is claimed (C34).

What is not proved: that the graph of an execution has a finite causal past. It is an admissibility
condition, stated as a predicate (`FiniteCausalPast`), not derived; its feasibility on each target
is `OB-C22`.
-/

namespace Ern.ConcurrencyModel.Events

open Relation

/-- `PrefixFinite(R)` (C34): "for every event `e`, the set `{ d | R(d, e) }` is finite". -/
def PrefixFinite {E : Type} (R : E → E → Prop) : Prop := ∀ e, ∃ l : List E, ∀ d, R d e → d ∈ l

namespace Graph

variable {E C U V S : Type} (G : Graph E C U V S)

/-- `po ∪ sw ∪ rf` (C34), with `sw` the relation of C32 (`SW`). -/
def PoSwRf (a b : E) : Prop := G.po a b ∨ G.SW a b ∨ G.rf a b

/-- Finite causal past (C34): `PrefixFinite((po ∪ sw ∪ rf)⁺)`. An admissibility condition separate
from `EventConsistent`, which it does not change; an admissible graph satisfies both. -/
def FiniteCausalPast : Prop := PrefixFinite (TransGen G.PoSwRf)

/-! ## 10f: finite graphs -/

/-- **Theorem 10f** (C34: "Every finite graph satisfies this condition"; `OB-C23`): a graph whose
type of events is finite has a finite causal past. -/
theorem finiteCausalPast_of_finite (hfin : Finite E) : G.FiniteCausalPast := fun _ =>
  let ⟨l, hl⟩ := hfin
  ⟨l, fun d _ => hl d⟩

/-! ## 10g: release sequences (C48) -/

/-- A weaker Boolean test counts strictly fewer elements of a list when it misses one that the
other counts. -/
theorem countP_lt {α : Type} (l : List α) (p q : α → Bool) (h : ∀ x ∈ l, p x = true → q x = true)
    {a : α} (ha : a ∈ l) (hpa : p a = false) (hqa : q a = true) : l.countP p < l.countP q := by
  induction l with
  | nil => cases ha
  | cons b l ih =>
    have h' := fun x hx => h x (List.mem_cons_of_mem b hx)
    have hle : l.countP p ≤ l.countP q := List.countP_mono_left fun x hx => h' x hx
    simp only [List.countP_cons]
    rcases List.mem_cons.1 ha with rfl | ha
    · simp only [hpa, hqa, Bool.false_eq_true, ite_false, ite_true]; omega
    · have := ih h' ha
      by_cases hp : p b = true
      · simp only [hp, h b List.mem_cons_self hp, ite_true]; omega
      · simp only [hp, Bool.false_eq_true, ite_false]; split <;> omega

/-- The modifications between the head and a member (C31, C48): under conjuncts 1 to 3, let `Q` be
a set of events, contained in a finite list, closed under `rf` predecessors, whose modifications of
`u` strictly between `a` and `m` in `mo` are atomic RMWs. Then every modification of `u` strictly
between `a` and an atomic RMW `y` of `Q` (with `mo(a, y)` and `y` at or before `m`) is in `Q`: going
back along `rf` from `y`, each RMW reads its immediate `mo` predecessor (conjunct 3), and the
finitely many elements of the list bound the descent. -/
theorem between_mem (h1 : G.RfWF) (h2 : G.MoTotal) (h3 : G.RmwAtomic) {u : U} {a m : E}
    (L : List E) {Q : E → Prop} (hQL : ∀ x, Q x → x ∈ L) (hQrf : ∀ w y, Q y → G.rf w y → Q w)
    (hrmw : ∀ x, Q x → G.ModOn x u → G.mo a x → G.mo x m → G.AtomicRMWOn x u) :
    ∀ y, Q y → G.AtomicRMWOn y u → G.mo a y → (y = m ∨ G.mo y m) →
      ∀ x, G.ModOn x u → G.mo a x → G.mo x y → Q x := by
  classical
  have key : ∀ n y, L.countP (fun z => decide (G.mo z y)) = n → Q y → G.AtomicRMWOn y u →
      G.mo a y → (y = m ∨ G.mo y m) → ∀ x, G.ModOn x u → G.mo a x → G.mo x y → Q x := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
    intro y hc hy hyr hay hym x hx hax hxy
    obtain ⟨⟨w, hrf⟩, -⟩ := h1.2.1 y u (G.readOn_of_rmw hyr)
    have hw : Q w := hQrf w y hy hrf
    obtain ⟨hwy, himm⟩ := h3 w y (G.isRMW_of_rmw hyr) (G.atomic_of_rmw hyr) hrf
    by_cases hxw : x = w
    · subst hxw; exact hw
    have hwu : G.ModOn w u := (G.modOn_of_mo h2 hwy (G.modOn_of_rmw hyr)).1
    rcases (h2.2 u).2.2 x w hx hwu hxw with hxw' | hwx
    · have haw : G.mo a w := G.mo_trans h2 hx hax hxw'
      have hwm : G.mo w m := by
        rcases hym with rfl | hym
        · exact hwy
        · exact G.mo_trans h2 (G.modOn_of_rmw hyr) hwy hym
      have hwr := hrmw w hw hwu haw hwm
      have hlt : L.countP (fun z => decide (G.mo z w)) < n := by
        rw [← hc]
        refine countP_lt L _ _ (fun z _ hz => ?_) (hQL w hw) ?_ ?_
        · simp only [decide_eq_true_eq] at hz ⊢; exact G.mo_trans h2 hwu hz hwy
        · simp only [decide_eq_false_iff_not]; exact G.mo_irrefl h2 w
        · simp only [decide_eq_true_eq]; exact hwy
      exact ih _ hlt w rfl hw hwr haw (.inr hwm) x hx hax hxw'
    · exact (himm x ⟨hwx, hxy⟩).elim
  exact fun y => key _ y rfl

/-- A transitive closure carried by a map that carries the relation. -/
theorem tg_map {α β : Type} {R : α → α → Prop} {R' : β → β → Prop} (f : α → β)
    (h : ∀ a b, R a b → R' (f a) (f b)) {a b : α} (hab : TransGen R a b) :
    TransGen R' (f a) (f b) := by
  induction hab with
  | single h' => exact .single (h _ _ h')
  | tail _ h' ih => exact .tail ih (h _ _ h')

/-- **Theorem 10g**, under finitely many `rf`-ancestors of the member (C48, retained reading 5;
`OB-C23`): under conjuncts 1 to 3, for `m ≠ h` whose `rf`-ancestors are finitely many, `m` is a
member of the release sequence of `h` exactly when a chain of atomic RMWs, each reading the previous
one by `rf`, relates `h` to `m`. -/
theorem rsMember_iff_chain_of_rfPast (h1 : G.RfWF) (h2 : G.MoTotal) (h3 : G.RmwAtomic)
    {u : U} {h m : E} (hne : m ≠ h) (hpast : ∃ l : List E, ∀ d, TransGen G.rf d m → d ∈ l) :
    G.RSMember u h m ↔ G.Chain u h m := by
  refine ⟨fun hm => ?_, G.rsMember_of_chain h2 h3⟩
  obtain ⟨l, hl⟩ := hpast
  refine (G.chain_iff h1 h2 h3 hne).2 ⟨hm, m :: l, fun x hx h₁ h₂ => ?_⟩
  rcases hm with rfl | ⟨hmr, hhm, hall⟩
  · exact absurd rfl hne
  have hQ := G.between_mem h1 h2 h3 (m :: l) (Q := fun x => x = m ∨ TransGen G.rf x m)
    (fun x hx => by
      rcases hx with rfl | hx
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (hl x hx))
    (fun w y hy hrf => by
      rcases hy with rfl | hy
      · exact .inr (.single hrf)
      · exact .inr (TransGen.trans (.single hrf) hy))
    (fun x _ hx h₁ h₂ => hall x hx h₁ h₂) m (.inl rfl) hmr hhm (.inl rfl) x hx h₁ h₂
  rcases hQ with rfl | hx'
  · exact List.mem_cons_self ..
  · exact List.mem_cons_of_mem _ (hl x hx')

/-- **Theorem 10g** (C48: "beginning with release modification `h` of a given atomic unit, the
release sequence consists of `h` followed by the maximal contiguous `mo` segment of atomic RMW
modifications on that unit"; C34, "Infinite-graph verification targets": "verify that C48
release-sequence membership agrees with a finite chain of immediate `mo`-predecessor atomic RMWs
leading back to the release head"; `OB-C23`): under conjuncts 1 to 3 and a finite causal past, for
`m ≠ h`, `m` is a member of the release sequence of `h` (`RSMember`, retained reading 5) exactly when
a finite chain of atomic RMWs, each reading the previous one by `rf`, relates `h` to `m`. -/
theorem rsMember_iff_chain_fcp (h1 : G.RfWF) (h2 : G.MoTotal) (h3 : G.RmwAtomic)
    (hf : G.FiniteCausalPast) {u : U} {h m : E} (hne : m ≠ h) :
    G.RSMember u h m ↔ G.Chain u h m :=
  G.rsMember_iff_chain_of_rfPast h1 h2 h3 hne (by
    obtain ⟨l, hl⟩ := hf m
    exact ⟨l, fun d hd => hl d (tg_map id (fun _ _ h => .inr (.inr h)) hd)⟩)

/-- Statement 3 of `EventLemmas` (`rsMember_iff_chain`, on a finite graph) is a corollary of 10f and
10g (C48). -/
theorem rsMember_iff_chain_of_finite (hfin : Finite E) (h1 : G.RfWF) (h2 : G.MoTotal)
    (h3 : G.RmwAtomic) {u : U} {h m : E} (hne : m ≠ h) : G.RSMember u h m ↔ G.Chain u h m :=
  G.rsMember_iff_chain_fcp h1 h2 h3 (G.finiteCausalPast_of_finite hfin) hne

/-! ## 10h: reduction to finite prefixes (C34) -/

/-- The finite lists bounding the causal past of each event of a list (C34). -/
theorem past_bound (hf : G.FiniteCausalPast) :
    ∀ S : List E, ∃ l : List E, ∀ x, (∃ e ∈ S, TransGen G.PoSwRf x e) → x ∈ l
  | [] => ⟨[], fun _ ⟨_, h, _⟩ => by cases h⟩
  | e :: S => by
    obtain ⟨l, hl⟩ := past_bound hf S
    obtain ⟨l', hl'⟩ := hf e
    refine ⟨l' ++ l, fun x ⟨e', he', hx⟩ => ?_⟩
    rcases List.mem_cons.1 he' with rfl | he'
    · exact List.mem_append_left _ (hl' x hx)
    · exact List.mem_append_right _ (hl x ⟨e', he', hx⟩)

/-- **Theorem 10h**, item 1 (C34: "each finite event set has a finite causal-predecessor-closed
extension"; `OB-C23`): under a finite causal past, every finite list of events `S` is contained in
a finite set `P` (bounded by a list) closed under the predecessors of `po ∪ sw ∪ rf`: the events of
`S` and their causal past. -/
theorem exists_closed_extension (hf : G.FiniteCausalPast) (S : List E) :
    ∃ P : E → Prop, (∃ l : List E, ∀ x, P x → x ∈ l) ∧ (∀ e ∈ S, P e) ∧
      ∀ e d, P e → G.PoSwRf d e → P d := by
  obtain ⟨l, hl⟩ := G.past_bound hf S
  refine ⟨fun x => x ∈ S ∨ ∃ e ∈ S, TransGen G.PoSwRf x e, ⟨S ++ l, fun x hx => ?_⟩,
    fun e he => .inl he, fun e d he hd => ?_⟩
  · rcases hx with hx | hx
    · exact List.mem_append_left _ hx
    · exact List.mem_append_right _ (hl x hx)
  · rcases he with he | ⟨e', he', hee'⟩
    · exact .inr ⟨e, he, .single hd⟩
    · exact .inr ⟨e', he', TransGen.trans (.single hd) hee'⟩

/-- The graph induced on a set of events `P` (C34): the events of `P` with their attributes, and
`po`, `rf` and `mo` restricted to them. Its `sw` is the one the definition of C32 (`SW`) gives it,
not a restriction. -/
def induced (P : E → Prop) : Graph {e // P e} C U V S where
  ev e := G.ev e.1
  uRange := G.uRange
  po a b := G.po a.1 b.1
  rf a b := G.rf a.1 b.1
  mo a b := G.mo a.1 b.1
  po_irrefl a := G.po_irrefl a.1
  po_trans := G.po_trans
  po_ctx := G.po_ctx
  po_total hc hne := G.po_total hc fun e => hne (Subtype.ext e)

/-- A transitive closure of `G` ending in a set closed under its predecessors lies in that set. -/
theorem tg_lift {P : E → Prop} {R : E → E → Prop} {R' : {e // P e} → {e // P e} → Prop}
    (hcl : ∀ e d, P e → R d e → P d) (hR : ∀ (a b : {e // P e}), R a.1 b.1 → R' a b) {x : E}
    (hx : P x) {y : E} (h : TransGen R x y) (hy : P y) : TransGen R' ⟨x, hx⟩ ⟨y, hy⟩ := by
  induction h with
  | single h' => exact .single (hR ⟨x, hx⟩ ⟨_, hy⟩ h')
  | @tail z y hxz hzy ih =>
    have hz : P z := hcl y z hy hzy
    exact .tail (ih hz) (hR ⟨z, hz⟩ ⟨y, hy⟩ hzy)

/-- **Theorem 10h**, item 2 (C34: "whose induced graph preserves the relevant `sw`, `hb`, race and
consistency judgments on that set"; `OB-C23`): under `EventConsistent`, for a finite set `P`
(bounded by a list) closed under the predecessors of `po ∪ sw ∪ rf`, the graph induced on `P` is
`EventConsistent`, and between two events of `P`, `sw`, `hb` and the race (C33) are those of the
whole graph. -/
theorem induced_judgments (hc : G.EventConsistent) {P : E → Prop}
    (hfin : ∃ l : List E, ∀ x, P x → x ∈ l) (hcl : ∀ e d, P e → G.PoSwRf d e → P d) :
    (∀ a b, (G.induced P).SW a b ↔ G.SW a.1 b.1) ∧
    (∀ a b, (G.induced P).HB a b ↔ G.HB a.1 b.1) ∧
    (∀ a b, (G.induced P).Race a b ↔ G.Race a.1 b.1) ∧
    (G.induced P).EventConsistent := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hc
  obtain ⟨L, hL⟩ := hfin
  have hrfP : ∀ w y, P y → G.rf w y → P w := fun w y hy hrf => hcl y w hy (.inr (.inr hrf))
  -- release-sequence membership
  have hmem : ∀ (u : U) (a m : {e // P e}),
      (G.induced P).RSMember u a m ↔ G.RSMember u a.1 m.1 := by
    intro u a m
    constructor
    · rintro (rfl | ⟨hmr, ham, hall⟩)
      · exact .inl rfl
      · refine .inr ⟨hmr, ham, fun x hx h₁ h₂ => ?_⟩
        have hPx : P x := G.between_mem h1 h2 h3 L hL hrfP
          (fun y hy hyu h₁ h₂ => hall ⟨y, hy⟩ hyu h₁ h₂) m.1 m.2 hmr ham (.inl rfl) x hx h₁ h₂
        exact hall ⟨x, hPx⟩ hx h₁ h₂
    · rintro (h | ⟨hmr, ham, hall⟩)
      · exact .inl (Subtype.ext h)
      · exact .inr ⟨hmr, ham, fun x hx h₁ h₂ => hall x.1 hx h₁ h₂⟩
  have hsw : ∀ a b, (G.induced P).SW a b ↔ G.SW a.1 b.1 := by
    intro a b
    constructor
    · rintro (⟨u, m, hr, ha, hm, hrf⟩ | h | h)
      · exact .inl ⟨u, m.1, hr, ha, (hmem u a m).1 hm, hrf⟩
      · exact .inr (.inl h)
      · exact .inr (.inr h)
    · rintro (⟨u, m, hr, ha, hm, hrf⟩ | h | h)
      · have hPm : P m := hrfP m b.1 b.2 hrf
        exact .inl ⟨u, ⟨m, hPm⟩, hr, ha, (hmem u a ⟨m, hPm⟩).2 hm, hrf⟩
      · exact .inr (.inl h)
      · exact .inr (.inr h)
  have hposw : ∀ a b, (G.induced P).PoSw a b ↔ G.PoSw a.1 b.1 := fun a b =>
    or_congr Iff.rfl (hsw a b)
  have hhb : ∀ a b, (G.induced P).HB a b ↔ G.HB a.1 b.1 := by
    intro a b
    refine ⟨fun h => tg_map Subtype.val (fun x y h => (hposw x y).1 h) h, fun h => ?_⟩
    have := tg_lift (R' := (G.induced P).PoSw)
      (fun e d he hd => hcl e d he (by rcases hd with hd | hd; exact .inl hd; exact .inr (.inl hd)))
      (fun x y h => (hposw x y).2 h) a.2 h b.2
    exact this
  have hrace : ∀ a b, (G.induced P).Race a b ↔ G.Race a.1 b.1 := by
    intro a b
    show (_ ∧ _ ∧ _ ∧ ¬ (G.induced P).HB a b ∧ ¬ (G.induced P).HB b a) ↔
      (_ ∧ _ ∧ _ ∧ ¬ G.HB a.1 b.1 ∧ ¬ G.HB b.1 a.1)
    rw [hhb a b, hhb b a]
    exact Iff.rfl
  have hrb : ∀ a b, (G.induced P).RB a b → G.RB a.1 b.1 := fun a b ⟨⟨w, hw1, hw2⟩, hne⟩ =>
    ⟨⟨w.1, hw1, hw2⟩, fun e => hne (Subtype.ext e)⟩
  have heco : ∀ a b, (G.induced P).ECO a b → G.ECO a.1 b.1 := fun a b h =>
    tg_map Subtype.val (fun x y h => by
      rcases h with h | h | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr (hrb x y h))) h
  refine ⟨hsw, hhb, hrace, ⟨⟨fun w r h => h1.1 w.1 r.1 h, fun r u hr => ⟨?_, fun w w' h h' =>
    Subtype.ext ((h1.2.1 r.1 u hr).2 w.1 w'.1 h h')⟩, fun w r h => h1.2.2 w.1 r.1 h⟩,
    ⟨fun a b h => h2.1 a.1 b.1 h, fun u => ⟨fun a ha h => (h2.2 u).1 a.1 ha h,
      fun a b c ha hb hc' h₁ h₂ => (h2.2 u).2.1 a.1 b.1 c.1 ha hb hc' h₁ h₂,
      fun a b ha hb hne => (h2.2 u).2.2 a.1 b.1 ha hb fun e => hne (Subtype.ext e)⟩⟩,
    fun w r hr ha hrf => ⟨(h3 w.1 r.1 hr ha hrf).1, fun x hx => (h3 w.1 r.1 hr ha hrf).2 x.1 hx⟩,
    fun a b hab h => h4 a.1 b.1 ((hhb a b).1 hab) (by
      rcases h with h | h
      · exact .inl (congrArg Subtype.val h)
      · exact .inr (heco b a h)),
    fun a h => h5 a.1 ((hhb a a).1 h),
    fun a h => h6 a.1 (tg_map Subtype.val (fun x y h => by
      rcases h with h | h
      · exact .inl h
      · exact .inr h) h),
    fun a h => h7 a.1 (tg_map Subtype.val (fun x y h => by
      obtain ⟨hx, hs, hy⟩ := h
      refine ⟨hx, ?_, hy⟩
      rcases hs with h | ⟨x', y', h₁, h₂, h₃⟩ | ⟨h, hl⟩ | h | h
      · exact .inl h
      · exact .inr (.inl ⟨x'.1, y'.1, h₁, (hhb x' y').1 h₂, h₃⟩)
      · exact .inr (.inr (.inl ⟨(hhb x y).1 h, hl⟩))
      · exact .inr (.inr (.inr (.inl h)))
      · exact .inr (.inr (.inr (.inr (hrb x y h))))) h)⟩⟩
  obtain ⟨w, hw⟩ := (h1.2.1 r.1 u hr).1
  exact ⟨⟨w, hrfP w r.1 r.2 hw⟩, hw⟩

/-! ## 10i: erasure (C29, C34) -/

/-- **Theorem 10i** (C34: "Verify that erasure of pure-authority markers preserves finite causal
past **from the original graph to its erasure**; no converse is claimed"; C29; `OB-C23`): if `G` has
a finite causal past, so has `erasePure(G)`. The erasure premises of C34 (no `rf` or `mo` edge at a
marker) are not needed in this direction: on surviving events `sw` is unchanged (`erase_sw_iff`).
The converse is refuted by witness G4. -/
theorem erasePure_finiteCausalPast (hf : G.FiniteCausalPast) : G.erasePure.FiniteCausalPast := by
  classical
  intro e
  obtain ⟨l, hl⟩ := hf e.1
  refine ⟨l.filterMap fun x => if h : ¬ G.Pure x then some ⟨x, h⟩ else none, fun d hd => ?_⟩
  have hd' : TransGen G.PoSwRf d.1 e.1 := tg_map Subtype.val (fun x y h => by
    rcases h with h | h | h
    · exact .inl h
    · exact .inr (.inl ((G.erase_sw_iff (fun _ h => h) x y).1 h))
    · exact .inr (.inr h)) hd
  exact List.mem_filterMap.2 ⟨d.1, hl _ hd', by simp [d.2]⟩

end Graph

end Ern.ConcurrencyModel.Events
