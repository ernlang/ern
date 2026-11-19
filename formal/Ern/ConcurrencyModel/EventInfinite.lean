import Ern.ConcurrencyModel.EventLemmas

/-!
# Theorem 10a: an infinite witness for the release sequence (C31, C34, C48)

An infinite event graph on one atomic unit `x`, every event alone in its context, every event
atomic:

* `h = W_rel(x, 1)`;
* for every `n ≥ 1`, `u_n = U_rlx(x: 1 → 1)` and `v_n = U_rlx(x: 7 → 7)`;
* `rf`: `u_1` reads `h`, `u_{n+1}` reads `u_n`, `v_n` reads `v_{n+1}`;
* `mo`: `h`, then the `u_n` by increasing index, then the `v_n` by decreasing index, `v_1` last.

Here `u n` stands for `u_{n+1}` and `v n` for `v_{n+1}`.

What it shows: the seven conjuncts of `EventConsistent` hold (`infinite_consistent`), there is no
race (C33), every `v_n` is a member of the release sequence of `h` under retained reading 5
(`infinite_v_member`), no `rf` chain relates `h` to any `v_n` (`infinite_no_chain`), and no event
other than the `v_n` writes the value `7`. So the finiteness condition of statement 2 of
`EventLemmas` (`chain_iff`) is needed (`infinite_not_finiteBetween`), and `EventConsistent` does
not exclude an infinite sequence of RMWs reading one another with no origin.

What it does not show: it is a declarative graph, with no initial write and no creation of
contexts. Nothing establishes that an ERN execution or a safe program produces it. It documents the
open point on infinite graphs (decision 6 of the tranche); it is not an established defect of the
specification, which states nothing this witness contradicts. Conjunct 2 requires `mo` to be a
strict total order of the modifications of the unit, the represented initial write included as one
of them; it does not require an initial write to exist, and this graph has none.
-/

namespace Ern.ConcurrencyModel.Events

namespace Infinite

open Relation

/-- The events: `h`, `u n` for `u_{n+1}`, `v n` for `v_{n+1}`. -/
inductive Ev where
  | h
  | u (n : Nat)
  | v (n : Nat)
deriving DecidableEq

/-- The attributes: `h = W_rel(x, 1)`, `u_n = U_rlx(x: 1 → 1)`, `v_n = U_rlx(x: 7 → 7)`; each event
alone in its context. -/
def ev : Ev → Event Ev Unit Nat Unit
  | .h => ⟨.h, ⟨0, 0⟩, .marks (some (.atomic () .release (.write 1))) none⟩
  | .u n => ⟨.u n, ⟨0, 0⟩, .marks (some (.atomic () .relaxed (.rmw 1 1))) none⟩
  | .v n => ⟨.v n, ⟨0, 0⟩, .marks (some (.atomic () .relaxed (.rmw 7 7))) none⟩

/-- `rf`: `u_1` reads `h`, `u_{n+1}` reads `u_n`, `v_n` reads `v_{n+1}`. -/
def rf : Ev → Ev → Prop
  | .h, .u m => m = 0
  | .u n, .u m => m = n + 1
  | .v n, .v m => n = m + 1
  | _, _ => False

/-- `mo`: `h`, then the `u_n` increasing, then the `v_n` decreasing. -/
def mo : Ev → Ev → Prop
  | .h, .u _ | .h, .v _ | .u _, .v _ => True
  | .u i, .u j => i < j
  | .v i, .v j => j < i
  | _, _ => False

/-- The graph: no `po` edge, every event being alone in its context. -/
def G : Graph Ev Ev Unit Nat Unit where
  ev := ev
  uRange _ := ⟨0, 1⟩
  po _ _ := False
  rf := rf
  mo := mo
  po_irrefl _ h := h
  po_trans h _ := h.elim
  po_ctx h := h.elim
  po_total {a b} hc hne := by
    exfalso; apply hne
    cases a <;> cases b <;> simp_all [ev]

/-- The access of `h`, `W_rel(x, 1)`. -/
theorem acc_h : G.acc? .h = some (.atomic () .release (.write 1)) := rfl
/-- The access of `u_{n+1}`, `U_rlx(x: 1 → 1)`. -/
theorem acc_u (n : Nat) : G.acc? (.u n) = some (.atomic () .relaxed (.rmw 1 1)) := rfl
/-- The access of `v_{n+1}`, `U_rlx(x: 7 → 7)`. -/
theorem acc_v (n : Nat) : G.acc? (.v n) = some (.atomic () .relaxed (.rmw 7 7)) := rfl

/-- Every event is a modification of the unit. -/
theorem modOn (e : Ev) : G.ModOn e () := by
  cases e <;> exact ⟨rfl, _, rfl, trivial⟩

/-- The events other than `h` are atomic RMW modifications of the unit. -/
theorem rmw_u (n : Nat) : G.AtomicRMWOn (.u n) () := ⟨_, _, _, acc_u n⟩
/-- The `v_n` are atomic RMW modifications of the unit (C31, C48). -/
theorem rmw_v (n : Nat) : G.AtomicRMWOn (.v n) () := ⟨_, _, _, acc_v n⟩

/-- `h` reads nothing. -/
theorem not_reads_h : ¬ G.Reads .h := fun ⟨k, hk, hr⟩ => by
  cases hk; exact hr

/-- `mo` is transitive. -/
theorem mo_trans : ∀ {a b c : Ev}, mo a b → mo b c → mo a c := by
  intro a b c h₁ h₂
  cases a <;> cases b <;> cases c <;> simp_all [mo] <;> omega

/-- `mo` is irreflexive. -/
theorem mo_irrefl : ∀ a : Ev, ¬ mo a a := by
  intro a; cases a <;> simp [mo]

/-- Each `rf` edge is an `mo` edge. -/
theorem rf_mo : ∀ {a b : Ev}, rf a b → mo a b := by
  intro a b h
  cases a <;> cases b <;> simp_all [rf, mo]

/-- No event is release-capable and acquire-capable: no event is acquire-capable. -/
theorem not_acqCap (e : Ev) (u : Unit) : ¬ G.AcqCap e u := by
  rintro ⟨o, k, hk, hr, ho⟩
  cases e with
  | h => cases hk; exact hr
  | u n => cases hk; rcases ho with h | h | h <;> cases h
  | v n => cases hk; rcases ho with h | h | h <;> cases h

/-- `sw` is empty. -/
theorem not_sw (a b : Ev) : ¬ G.SW a b := by
  rintro (⟨u, m, -, hacq, -⟩ | ⟨c, ha, -⟩ | ⟨c, ha, -⟩)
  · exact not_acqCap b u hacq
  · cases a <;> cases ha
  · cases a <;> cases ha

/-- `hb` is empty. -/
theorem not_hb (a b : Ev) : ¬ G.HB a b := by
  intro h
  induction h with
  | single h => rcases h with h | h; exact h; exact not_sw _ _ h
  | tail _ _ ih => exact ih

/-- No event is `seq_cst`. -/
theorem not_sc (e : Ev) : ¬ G.SC e := by
  rintro ⟨u, k, hk⟩
  cases e <;> cases hk

/-- **Infinite witness, consistency** (C34): the seven conjuncts of `EventConsistent` hold. -/
theorem infinite_consistent : G.EventConsistent := by
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, fun _ => ⟨?_, ?_, ?_⟩⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro w r h
    refine ⟨(), modOn w, (modOn r).1, ?_⟩
    cases w <;> cases r <;> first | exact (h : False).elim | exact ⟨_, rfl, trivial⟩
  · intro r u hr
    cases r with
    | h => exact (not_reads_h hr.2).elim
    | u n =>
      refine ⟨?_, fun w w' h₁ h₂ => ?_⟩
      · cases n with
        | zero => exact ⟨.h, rfl⟩
        | succ n => exact ⟨.u n, rfl⟩
      · cases w <;> cases w' <;> simp_all [G, rf] <;> omega
    | v n =>
      refine ⟨⟨.v (n + 1), rfl⟩, fun w w' h₁ h₂ => ?_⟩
      cases w <;> cases w' <;> simp_all [G, rf] <;> omega
  · intro w r h
    cases w <;> cases r <;> simp_all [G, rf] <;> exact ⟨_, rfl, rfl⟩
  · intro a b _; exact ⟨(), modOn a, modOn b⟩
  · intro a _; exact mo_irrefl a
  · intro a b c _ _ _ h₁ h₂; exact mo_trans h₁ h₂
  · intro a b _ _ hne
    cases a <;> cases b <;> simp_all [G, mo] <;> omega
  · intro w r _ h
    refine ⟨rf_mo h, fun x ⟨h₁, h₂⟩ => ?_⟩
    cases w <;> cases r <;> cases x <;> simp_all [G, rf, mo] <;> omega
  · intro a b h; exact (not_hb a b h).elim
  · intro a h; exact not_hb a a h
  · intro a h
    have key : ∀ {b c}, TransGen G.PoRf b c → mo b c := by
      intro b c h
      induction h with
      | single h => rcases h with h | h; exact h.elim; exact rf_mo h
      | tail _ h ih => rcases h with h | h; exact h.elim; exact mo_trans ih (rf_mo h)
    exact mo_irrefl a (key h)
  · intro a h
    cases h with
    | single h => exact not_sc a h.1
    | tail _ h => exact not_sc _ h.1

/-- **Infinite witness, races** (C33): no pair of events is in a race; every event is atomic. -/
theorem infinite_no_race (a b : Ev) : ¬ G.Race a b := by
  have hat : ∀ e : Ev, G.Atomic e := fun e => by
    cases e
    · exact ⟨_, _, _, acc_h⟩
    · exact ⟨_, _, _, acc_u _⟩
    · exact ⟨_, _, _, acc_v _⟩
  exact G.not_race_atomic (hat a) (hat b)

/-- **Infinite witness, release sequence** (C48, retained reading 5): every `v_n` is a member of the
release sequence of `h`. -/
theorem infinite_v_member (n : Nat) : G.RSMember () .h (.v n) := by
  refine .inr ⟨rmw_v n, trivial, fun x _ h₁ _ => ?_⟩
  cases x with
  | h => exact (mo_irrefl Ev.h h₁).elim
  | u k => exact rmw_u k
  | v k => exact rmw_v k

/-- The ends of the chains from `h` are the `u_n`. -/
theorem chain_u {m : Ev} (hc : G.Chain () .h m) : ∃ k, m = .u k := by
  induction hc with
  | @one m _ hrf =>
    cases m with
    | h => exact (hrf : False).elim
    | u k => exact ⟨k, rfl⟩
    | v k => exact (hrf : False).elim
  | @step x m _ _ hrf ih =>
    obtain ⟨k, rfl⟩ := ih
    cases m with
    | h => exact (hrf : False).elim
    | u j => exact ⟨j, rfl⟩
    | v j => exact (hrf : False).elim

/-- **Infinite witness, chains** (C31, C48): no `rf` chain relates `h` to any `v_n`. -/
theorem infinite_no_chain (n : Nat) : ¬ G.Chain () .h (.v n) := fun hc => by
  obtain ⟨k, hk⟩ := chain_u hc
  cases hk

/-- **Infinite witness, values**: no event other than the `v_n` writes the value `7`. -/
theorem infinite_seven (e : Ev) (h : G.valW e = some 7) : ∃ n, e = .v n := by
  cases e with
  | h => cases h
  | u n => cases h
  | v n => exact ⟨n, rfl⟩

/-- **Infinite witness, necessity of the finiteness condition** of statement 2 (`chain_iff`): the
modifications of the unit between `h` and any `v_n` are not finitely many. -/
theorem infinite_not_finiteBetween (n : Nat) : ¬ G.FiniteBetween () .h (.v n) := fun hf => by
  obtain ⟨h1, h2, h3, -⟩ := infinite_consistent
  exact infinite_no_chain n ((G.chain_iff h1 h2 h3 (by simp)).2 ⟨infinite_v_member n, hf⟩)

end Infinite

end Ern.ConcurrencyModel.Events
