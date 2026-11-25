import Ern.ConcurrencyModel.EventFinitePast
import Ern.ConcurrencyModel.EventInfinite

/-!
# Witnesses G1–G4: infinite graphs and the finite causal past (C34; `OB-C23`)

G1 and G2 are the two witnesses that the verification targets of C34 call for; the part of C34
that motivates G3 and G4 is given with each. Each witness is an infinite graph.

* G1 (C34, verification targets): the infinite witness of `EventInfinite` (an `rf` chain of RMWs
  with no origin) satisfies the seven conjuncts and has no finite causal past.
* G2 (C34, verification targets): a context writes `x` once; another writes `x` without end; `mo`
  puts the endless writes first. `EventConsistent`, finite causal past, `mo` not prefix-finite, no
  race.
* G3 (C34, paragraph on the finite causal past, which names this case): contexts `c_n`, each
  started by `c_{n+1}`: `EventConsistent`, `(po ∪ rf)⁺` prefix-finite, no finite causal past,
  through `sw` alone.
* G4 (C34, verification targets, erasure target): infinitely many pure authority markers, then an
  atomic write: `G` and `erasePure(G)` are `EventConsistent`; `G` has no finite causal past,
  `erasePure(G)` has one. No witness is called for here: G4 refutes the converse of theorem 10i
  (`erasePure_finiteCausalPast`), a converse that C34 does not claim.
-/

namespace Ern.ConcurrencyModel.Events

open Relation

/-- An event with infinitely many distinct predecessors, enumerated by `g` and counted back by `f`,
has no finite list of predecessors. -/
theorem not_bounded {E : Type} {R : E → E → Prop} {e : E} (g : Nat → E) (f : E → Nat)
    (hf : ∀ k, f (g k) = k) (hR : ∀ k, R (g k) e) : ¬ ∃ l : List E, ∀ d, R d e → d ∈ l := by
  rintro ⟨l, hl⟩
  have hle : ∀ {l : List Nat} {x : Nat}, x ∈ l → x ≤ l.sum := by
    intro l x hx
    induction l with
    | nil => cases hx
    | cons y l ih =>
      rcases List.mem_cons.1 hx with rfl | hx
      · simp
      · have := ih hx; simp only [List.sum_cons]; omega
  have hm := List.mem_map_of_mem (f := f) (hl _ (hR ((l.map f).sum + 1)))
  rw [hf] at hm
  have := hle hm
  omega

/-! ## G1 -/

/-- **Witness G1** (C34): the infinite witness of `EventInfinite` satisfies the seven conjuncts of
`EventConsistent` and has no finite causal past: every `v_{k+2}` is an `rf`-ancestor of `v_1`. -/
theorem witness_g1 : Infinite.G.EventConsistent ∧ ¬ Infinite.G.FiniteCausalPast := by
  refine ⟨Infinite.infinite_consistent, fun hf => ?_⟩
  have hR : ∀ k, TransGen Infinite.G.PoSwRf (.v (k + 1)) (.v 0) := by
    intro k
    induction k with
    | zero => exact .single (.inr (.inr (show Infinite.G.rf (.v 1) (.v 0) from rfl)))
    | succ k ih =>
      exact TransGen.trans (.single (.inr (.inr (show Infinite.G.rf (.v (k + 1 + 1)) (.v (k + 1))
        from rfl)))) ih
  exact not_bounded (fun k => .v (k + 1)) (fun | .v n => n - 1 | _ => 0) (fun k => by simp) hR
    (hf (.v 0))

/-! ## G2 -/

namespace G2

/-- The events: `wa`, the write of context `A` (context 0); `wb n`, the `n`-th write of context `B`
(context 1). -/
inductive Ev where
  | wa
  | wb (n : Nat)

/-- Relaxed atomic writes of the unit `x` (`()`): `A` writes `1`, `B` writes `2`. -/
def ev : Ev → Event Nat Unit Nat Unit
  | .wa => ⟨0, ⟨0, 0⟩, .marks (some (.atomic () .relaxed (.write 1))) none⟩
  | .wb n => ⟨1, ⟨n, 0⟩, .marks (some (.atomic () .relaxed (.write 2))) none⟩

/-- `po`: the writes of `B` in their order. -/
def po : Ev → Ev → Prop
  | .wb n, .wb m => n < m
  | _, _ => False

/-- `mo`: the writes of `B` in their order, then that of `A`. -/
def mo : Ev → Ev → Prop
  | .wb n, .wb m => n < m
  | .wb _, .wa => True
  | _, _ => False

/-- The graph G2: no `rf`. -/
def G : Graph Ev Nat Unit Nat Unit where
  ev := ev
  uRange _ := ⟨0, 1⟩
  po := po
  rf _ _ := False
  mo := mo
  po_irrefl a h := by cases a <;> simp [po] at h
  po_trans {a b c} h₁ h₂ := by
    cases a <;> cases b <;> cases c <;> simp_all [po]; omega
  po_ctx {a b} h := by cases a <;> cases b <;> simp_all [po, ev]
  po_total {a b} hc hne := by
    cases a <;> cases b <;> simp_all [po, ev]
    · rename_i n m
      rcases Nat.lt_trichotomy n m with h | h | h
      · exact .inl h
      · exact absurd h hne
      · exact .inr h

theorem not_reads (e : Ev) : ¬ G.Reads e := fun ⟨k, hk, hr⟩ => by
  cases e <;> cases hk <;> exact hr

theorem modOn (e : Ev) : G.ModOn e () :=
  ⟨by cases e <;> rfl, ⟨.write, by cases e <;> rfl, trivial⟩⟩

theorem not_sw (x y : Ev) : ¬ G.SW x y := by
  rintro (⟨u, m, -, ⟨o, k, hk, -, ho⟩, -, -⟩ | ⟨c, h, -⟩ | ⟨c, h, -⟩)
  · cases y <;> cases hk <;> rcases ho with h | h | h <;> cases h
  · cases x <;> cases h
  · cases x <;> cases h

theorem hb_po {x y : Ev} (h : G.HB x y) : po x y := by
  induction h with
  | single h => rcases h with h | h; exact h; exact absurd h (not_sw _ _)
  | tail _ h ih =>
    rcases h with h | h
    · exact G.po_trans (show G.po _ _ from ih) h
    · exact absurd h (not_sw _ _)

theorem eco_mo {x y : Ev} (h : G.ECO x y) : mo x y := by
  have mtrans : ∀ {a b c : Ev}, mo a b → mo b c → mo a c := by
    intro a b c h₁ h₂; cases a <;> cases b <;> cases c <;> simp_all [mo]; omega
  have base : ∀ a b, G.EcoBase a b → mo a b := by
    rintro a b (h | h | ⟨⟨w, h, -⟩, -⟩)
    · exact h.elim
    · exact h
    · exact h.elim
  induction h with
  | single h => exact base _ _ h
  | tail _ h ih => exact mtrans ih (base _ _ h)

end G2

/-- **Witness G2** (C34): `EventConsistent`; finite causal past; `mo` is not prefix-finite (the
write of `A` has every write of `B` before it in `mo`); no race. -/
theorem witness_g2 : G2.G.EventConsistent ∧ G2.G.FiniteCausalPast ∧ ¬ PrefixFinite G2.G.mo ∧
    ∀ x y, ¬ G2.G.Race x y := by
  have hsc : ∀ e, ¬ G2.G.SC e := fun e ⟨u, k, hk⟩ => by cases e <;> cases hk
  refine ⟨⟨⟨fun _ _ h => h.elim, fun r u hr => absurd hr.2 (G2.not_reads r), fun _ _ h => h.elim⟩,
    ⟨fun x y _ => ⟨(), G2.modOn x, G2.modOn y⟩, fun u => ⟨fun p _ h => ?_, fun p q r _ _ _ h₁ h₂ => ?_,
      fun p q _ _ hne => ?_⟩⟩, fun w r hr => ?_, fun x y hxy h => ?_, fun x h => ?_, fun x h => ?_,
    fun x h => ?_⟩, fun e => ?_, fun hf => ?_, fun x y => ?_⟩
  · cases p <;> simp [G2.G, G2.mo] at h
  · cases p <;> cases q <;> cases r <;> simp_all [G2.G, G2.mo]; omega
  · show G2.mo p q ∨ G2.mo q p
    match p, q, hne with
    | .wa, .wa, hne => exact absurd rfl hne
    | .wa, .wb _, _ => exact .inr trivial
    | .wb _, .wa, _ => exact .inl trivial
    | .wb n, .wb m, hne =>
      rcases Nat.lt_trichotomy n m with h | h | h
      · exact .inl h
      · exact absurd (by rw [h]) hne
      · exact .inr h
  · exfalso; cases r <;> cases hr
  · have hp := G2.hb_po hxy
    rcases h with rfl | h
    · exact G2.G.po_irrefl _ hp
    · have hm := G2.eco_mo h
      cases x <;> cases y <;> simp_all [G2.po, G2.mo]; omega
  · exact G2.G.po_irrefl _ (G2.hb_po h)
  · have : G2.po x x := by
      have key : ∀ a b, TransGen G2.G.PoRf a b → G2.po a b := by
        intro a b h
        induction h with
        | single h => rcases h with h | h; exact h; exact h.elim
        | tail _ h ih => rcases h with h | h; exact G2.G.po_trans ih h; exact h.elim
      exact key x x h
    exact G2.G.po_irrefl _ this
  · have : ∀ a b, TransGen G2.G.PSC a b → False := by
      intro a b h
      induction h with
      | single h => exact hsc _ h.1
      | tail _ h _ => exact hsc _ h.1
    exact this x x h
  · refine ⟨match e with | .wa => [] | .wb n => (List.range n).map .wb, fun d hd => ?_⟩
    have hp : G2.po d e := by
      have key : ∀ a b, TransGen G2.G.PoSwRf a b → G2.po a b := by
        intro a b h
        induction h with
        | single h =>
          rcases h with h | h | h
          · exact h
          · exact absurd h (G2.not_sw _ _)
          · exact h.elim
        | tail _ h ih =>
          rcases h with h | h | h
          · exact G2.G.po_trans ih h
          · exact absurd h (G2.not_sw _ _)
          · exact h.elim
      exact key d e hd
    cases d <;> cases e <;> simp_all [G2.po]
  · exact not_bounded (e := .wa) G2.Ev.wb (fun | .wb n => n | .wa => 0) (fun _ => rfl)
      (fun _ => trivial) (hf .wa)
  · have hat : ∀ e, G2.G.Atomic e := fun e => by cases e <;> exact ⟨_, _, _, rfl⟩
    exact G2.G.not_race_atomic (hat x) (hat y)

/-! ## G3 -/

namespace G3

/-- The events: `st n`, the marker `start(c_n)`, of context `n`; `sp n`, an event of role
`spawn(c_n)`, of context `n + 1`. -/
inductive Ev where
  | st (n : Nat)
  | sp (n : Nat)

/-- The attributes: lifecycle roles only; no access. -/
def ev : Ev → Event Nat Unit Nat Unit
  | .st n => ⟨n, ⟨n, 0⟩, .marks none (some (.start n))⟩
  | .sp n => ⟨n + 1, ⟨n, 1⟩, .marks none (some (.spawn n))⟩

/-- `po`: in context `n + 1`, `start(c_{n+1})` before the event of role `spawn(c_n)`. -/
def po : Ev → Ev → Prop
  | .st n, .sp m => n = m + 1
  | _, _ => False

/-- The graph G3: no `rf`, no `mo`. -/
def G : Graph Ev Nat Unit Nat Unit where
  ev := ev
  uRange _ := ⟨0, 1⟩
  po := po
  rf _ _ := False
  mo _ _ := False
  po_irrefl a h := by cases a <;> simp [po] at h
  po_trans {a b c} h₁ h₂ := by cases a <;> cases b <;> cases c <;> simp_all [po]
  po_ctx {a b} h := by cases a <;> cases b <;> simp_all [po, ev]
  po_total {a b} hc hne := by
    cases a <;> cases b <;> simp_all [po, ev]

/-- The measure of an event, decreasing along `po ∪ sw`. -/
def rank : Ev → Nat
  | .st n => 2 * n
  | .sp n => 2 * n + 1

theorem sw_iff (x y : Ev) : G.SW x y → ∃ n, x = .sp n ∧ y = .st n := by
  rintro (⟨u, m, ⟨o, k, hk, -⟩, -⟩ | ⟨c, h, h'⟩ | ⟨c, h, -⟩)
  · cases x <;> cases hk
  · cases x <;> cases y <;> simp_all [G, ev, Graph.sync?]
  · cases x <;> simp_all [G, ev, Graph.sync?]

theorem rank_posw {x y : Ev} (h : G.PoSw x y) : rank y < rank x := by
  rcases h with h | h
  · cases x <;> cases y <;> simp_all [G, po, rank]; omega
  · obtain ⟨n, rfl, rfl⟩ := sw_iff x y h
    simp [rank]

theorem rank_hb {x y : Ev} (h : G.HB x y) : rank y < rank x := by
  induction h with
  | single h => exact rank_posw h
  | tail _ h ih => exact Nat.lt_trans (rank_posw h) ih

theorem not_reads (e : Ev) : ¬ G.Reads e := fun ⟨k, hk, _⟩ => by cases e <;> cases hk

end G3

/-- **Witness G3** (C34): `EventConsistent`; `(po ∪ rf)⁺` is prefix-finite; the graph has no finite
causal past, through `sw` alone: every `start(c_{k+1})` is a causal predecessor of `start(c_0)`. -/
theorem witness_g3 : G3.G.EventConsistent ∧ PrefixFinite (TransGen G3.G.PoRf) ∧
    ¬ G3.G.FiniteCausalPast := by
  have heco : ∀ a b, ¬ G3.G.ECO a b := fun a b h => by
    cases h with
    | single h => rcases h with h | h | ⟨⟨_, h, _⟩, _⟩ <;> exact h.elim
    | tail _ h => rcases h with h | h | ⟨⟨_, h, _⟩, _⟩ <;> exact h.elim
  have hporf : ∀ a b, TransGen G3.G.PoRf a b → G3.po a b := by
    intro a b h
    induction h with
    | single h => rcases h with h | h; exact h; exact h.elim
    | tail _ h ih => rcases h with h | h; exact G3.G.po_trans ih h; exact h.elim
  have hsc : ∀ e, ¬ G3.G.SC e := fun e ⟨u, k, hk⟩ => by cases e <;> cases hk
  refine ⟨⟨⟨fun _ _ h => h.elim, fun r u hr => absurd hr.2 (G3.not_reads r), fun _ _ h => h.elim⟩,
    ⟨fun _ _ h => h.elim, fun u => ⟨fun _ _ h => h, fun _ _ _ _ _ _ h => h.elim, fun a b ha _ _ => ?_⟩⟩,
    fun w r hr => ?_, fun a b hab h => ?_, fun a h => ?_, fun a h => ?_, fun a h => ?_⟩,
    fun e => ⟨match e with | .st _ => [] | .sp m => [.st (m + 1)], fun d hd => ?_⟩, fun hf => ?_⟩
  · exfalso; obtain ⟨hu, -⟩ := ha; cases a <;> cases hu
  · exfalso; cases r <;> cases hr
  · rcases h with rfl | h
    · exact Nat.lt_irrefl _ (G3.rank_hb hab)
    · exact heco _ _ h
  · exact Nat.lt_irrefl _ (G3.rank_hb h)
  · exact G3.G.po_irrefl _ (hporf a a h)
  · have : ∀ a b, TransGen G3.G.PSC a b → False := by
      intro a b h
      induction h with
      | single h => exact hsc _ h.1
      | tail _ h _ => exact hsc _ h.1
    exact this a a h
  · have := hporf d e hd
    cases d <;> cases e <;> simp_all [G3.po]
  · have hstep : ∀ k, TransGen G3.G.PoSwRf (.st (k + 1)) (.st k) := fun k =>
      TransGen.trans (.single (.inl (show G3.G.po (.st (k + 1)) (.sp k) from rfl)))
        (.single (.inr (.inl (show G3.G.SW (.sp k) (.st k) from .inr (.inl ⟨k, rfl, rfl⟩)))))
    have hR : ∀ k, TransGen G3.G.PoSwRf (.st (k + 1)) (.st 0) := by
      intro k
      induction k with
      | zero => exact hstep 0
      | succ k ih => exact TransGen.trans (hstep (k + 1)) ih
    exact not_bounded (fun k => .st (k + 1)) (fun | .st n => n - 1 | .sp _ => 0) (fun k => by simp)
      hR (hf (.st 0))

/-! ## G4 -/

namespace G4

/-- The events: `mk n`, the `n`-th pure authority marker; `w`, the atomic write that follows them;
one context. -/
inductive Ev where
  | mk (n : Nat)
  | w

/-- The attributes: the markers carry nothing; `w` is a relaxed atomic write of the unit `()`. -/
def ev : Ev → Event Nat Unit Nat Unit
  | .mk n => ⟨0, ⟨n, 0⟩, .marks none none⟩
  | .w => ⟨0, ⟨0, 1⟩, .marks (some (.atomic () .relaxed (.write 1))) none⟩

/-- `po`: the markers in their order, then `w`. -/
def po : Ev → Ev → Prop
  | .mk n, .mk m => n < m
  | .mk _, .w => True
  | _, _ => False

/-- The graph G4: no `rf`, no `mo`. -/
def G : Graph Ev Nat Unit Nat Unit where
  ev := ev
  uRange _ := ⟨0, 1⟩
  po := po
  rf _ _ := False
  mo _ _ := False
  po_irrefl a h := by cases a <;> simp [po] at h
  po_trans {a b c} h₁ h₂ := by cases a <;> cases b <;> cases c <;> simp_all [po]; omega
  po_ctx {a b} _ := by cases a <;> cases b <;> rfl
  po_total {a b} _ hne := by
    show po a b ∨ po b a
    match a, b, hne with
    | .mk n, .mk m, hne =>
      rcases Nat.lt_trichotomy n m with h | h | h
      · exact .inl h
      · exact absurd (by rw [h]) hne
      · exact .inr h
    | .mk _, .w, _ => exact .inl trivial
    | .w, .mk _, _ => exact .inr trivial
    | .w, .w, hne => exact absurd rfl hne

theorem unitOf_mk (n : Nat) : G.unitOf (.mk n) = none := rfl

theorem not_sw (x y : Ev) : ¬ G.SW x y := by
  rintro (⟨u, m, -, ⟨o, k, hk, -, ho⟩, -, -⟩ | ⟨c, h, -⟩ | ⟨c, h, -⟩)
  · cases y <;> cases hk <;> rcases ho with h | h | h <;> cases h
  · cases x <;> cases h
  · cases x <;> cases h

theorem hb_po {x y : Ev} (h : G.HB x y) : po x y := by
  induction h with
  | single h => rcases h with h | h; exact h; exact absurd h (not_sw _ _)
  | tail _ h ih =>
    rcases h with h | h
    · exact G.po_trans (show G.po _ _ from ih) h
    · exact absurd h (not_sw _ _)

theorem not_reads (e : Ev) : ¬ G.Reads e := fun ⟨k, hk, hr⟩ => by
  cases e <;> cases hk <;> exact hr

theorem consistent : G.EventConsistent := by
  have hsc : ∀ e, ¬ G.SC e := fun e ⟨u, k, hk⟩ => by cases e <;> cases hk
  refine ⟨⟨fun _ _ h => h.elim, fun r u hr => absurd hr.2 (not_reads r), fun _ _ h => h.elim⟩,
    ⟨fun _ _ h => h.elim, fun u => ⟨fun _ _ h => h, fun _ _ _ _ _ _ h => h.elim,
      fun a b ha hb hne => ?_⟩⟩, fun _ r hr => ?_, fun a b hab h => ?_, fun a h => ?_,
    fun a h => ?_, fun a h => ?_⟩
  · exfalso
    obtain ⟨hu, -⟩ := ha
    obtain ⟨hu', -⟩ := hb
    match a, b, hu, hu', hne with
    | .mk n, _, hu, _, _ => rw [unitOf_mk] at hu; cases hu
    | _, .mk n, _, hu', _ => rw [unitOf_mk] at hu'; cases hu'
    | .w, .w, _, _, hne => exact hne rfl
  · exfalso; cases r <;> cases hr
  · rcases h with rfl | h
    · exact G.po_irrefl _ (hb_po hab)
    · cases h with
      | single h => rcases h with h | h | ⟨⟨_, h, _⟩, _⟩ <;> exact h.elim
      | tail _ h => rcases h with h | h | ⟨⟨_, h, _⟩, _⟩ <;> exact h.elim
  · exact G.po_irrefl _ (hb_po h)
  · have key : ∀ a b, TransGen G.PoRf a b → po a b := by
      intro a b h
      induction h with
      | single h => rcases h with h | h; exact h; exact h.elim
      | tail _ h ih => rcases h with h | h; exact G.po_trans ih h; exact h.elim
    exact G.po_irrefl _ (key a a h)
  · have : ∀ a b, TransGen G.PSC a b → False := by
      intro a b h
      induction h with
      | single h => exact hsc _ h.1
      | tail _ h _ => exact hsc _ h.1
    exact this a a h

end G4

/-- **Witness G4** (C34): `G` and `erasePure(G)` are `EventConsistent`; `G` has no finite causal
past (the write has infinitely many `po` predecessors); `erasePure(G)` has one. -/
theorem witness_g4 : G4.G.EventConsistent ∧ G4.G.erasePure.EventConsistent ∧
    ¬ G4.G.FiniteCausalPast ∧ G4.G.erasePure.FiniteCausalPast := by
  refine ⟨G4.consistent, (G4.G.erasePure_consistent_iff (fun _ _ h => h.elim)
    (fun _ _ h => h.elim)).2 G4.consistent, fun hf => ?_, fun e => ⟨[], fun d hd => ?_⟩⟩
  · exact not_bounded (e := .w) G4.Ev.mk (fun | .mk n => n | .w => 0) (fun _ => rfl)
      (fun _ => .single (.inl trivial)) (hf .w)
  · have hno : ∀ (x y : {e // ¬ G4.G.Pure e}), ¬ G4.G.erasePure.PoSwRf x y := by
      rintro ⟨x, hx⟩ ⟨y, hy⟩ (h | h | h)
      · cases x with
        | mk n => exact hx rfl
        | w => exact h
      · exact G4.not_sw x y ((G4.G.erase_sw_iff (fun _ h => h) ⟨x, hx⟩ ⟨y, hy⟩).1 h)
      · exact h
    cases hd with
    | single h => exact (hno _ _ h).elim
    | tail _ h => exact (hno _ _ h).elim

end Ern.ConcurrencyModel.Events
