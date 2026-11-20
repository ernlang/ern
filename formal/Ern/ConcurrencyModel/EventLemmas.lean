import Ern.ConcurrencyModel.EventGraph

/-!
# Theorem 10a: general lemmas of the event model (C29–C34, C48)

Lemmas on the event graph of `EventGraph`, each with its clause and with its hypotheses explicit:
`hb` (C33); pure authority markers and `sw` (C29, C32); conflicts (C30); races (C33); conjunct 4
entails conjunct 5 (C34); the total order `S` on a finite graph (C34); the consequences of `psc`
(C34); `rb` (C34); the segment of C48 and the `rf` chains of the release sequence (C31, C48).

The release sequence is `RSMember`, retained reading 5 (a formalization hypothesis; on a graph with
the finite causal past of C34 it agrees with the `rf` chains, `rsMember_iff_chain_fcp`). Statements 1
and 2 on chains hold on every graph; statement 3 assumes a finite graph, a hypothesis it states, and
is also a corollary of the finite-causal-past statements (`rsMember_iff_chain_of_finite`); the
infinite witness of `EventInfinite` shows that the finiteness condition of statement 2 is needed, and
it violates the finite causal past of C34 (`witness_g1`).
-/

namespace Ern.ConcurrencyModel.Events

open Relation

namespace Graph

variable {E C U V S : Type} (G : Graph E C U V S)

/-! ## Attribute facts -/

/-- An access designates at most one unit. -/
theorem unitOf_inj {e : E} {u u' : U} (h : G.unitOf e = some u) (h' : G.unitOf e = some u') :
    u = u' := by
  rw [h] at h'; exact Option.some.inj h'

/-- A pure authority marker carries no `acc` (C27). -/
theorem acc?_pure {e : E} (h : G.Pure e) : G.acc? e = none := by
  unfold acc?; rw [h]

/-- A pure authority marker carries no `sync` (C27). -/
theorem sync?_pure {e : E} (h : G.Pure e) : G.sync? e = none := by
  unfold sync?; rw [h]

/-- An access designating a unit is not a pure authority marker. -/
theorem not_pure_of_unitOf {e : E} {u : U} (h : G.unitOf e = some u) : ¬ G.Pure e := fun hp => by
  unfold unitOf at h; rw [G.acc?_pure hp] at h; cases h

/-- An event with an access kind is not a pure authority marker. -/
theorem not_pure_of_kind {e : E} {k : Kind} (h : G.kind? e = some k) : ¬ G.Pure e := fun hp => by
  unfold kind? at h; rw [G.acc?_pure hp] at h; cases h

/-- The unit of an atomic access. -/
theorem unitOf_atomic {e : E} {u : U} {o : MemOrder} {k : UKind V}
    (h : G.acc? e = some (.atomic u o k)) : G.unitOf e = some u := by
  unfold unitOf; rw [h]

/-- The kind of an atomic access. -/
theorem kind?_atomic {e : E} {u : U} {o : MemOrder} {k : UKind V}
    (h : G.acc? e = some (.atomic u o k)) : G.kind? e = some k.kind := by
  unfold kind?; rw [h]

/-- An atomic RMW modification of `u` is a modification of `u` (C31). -/
theorem modOn_of_rmw {e : E} {u : U} (h : G.AtomicRMWOn e u) : G.ModOn e u := by
  obtain ⟨o, vr, vw, h⟩ := h
  exact ⟨G.unitOf_atomic h, _, G.kind?_atomic h, trivial⟩

/-- An atomic RMW modification of `u` has a read component on `u` (C31). -/
theorem readOn_of_rmw {e : E} {u : U} (h : G.AtomicRMWOn e u) : G.ReadOn e u := by
  obtain ⟨o, vr, vw, h⟩ := h
  exact ⟨G.unitOf_atomic h, _, G.kind?_atomic h, trivial⟩

/-- An atomic RMW is an RMW. -/
theorem isRMW_of_rmw {e : E} {u : U} (h : G.AtomicRMWOn e u) : G.IsRMW e := by
  obtain ⟨o, vr, vw, h⟩ := h
  exact G.kind?_atomic h

/-- An atomic RMW is atomic. -/
theorem atomic_of_rmw {e : E} {u : U} (h : G.AtomicRMWOn e u) : G.Atomic e := by
  obtain ⟨o, vr, vw, h⟩ := h
  exact ⟨u, o, _, h⟩

/-- A modification designates its unit. -/
theorem ModOn.unit {e : E} {u : U} (h : G.ModOn e u) : G.unitOf e = some u := h.1

/-! ## `hb` (C33) -/

/-- `hb` is transitive (C33). -/
theorem hb_trans {a b c : E} (h₁ : G.HB a b) (h₂ : G.HB b c) : G.HB a c := TransGen.trans h₁ h₂

/-- `po ⊆ hb` (C33). -/
theorem po_hb {a b : E} (h : G.po a b) : G.HB a b := .single (.inl h)

/-- `sw ⊆ hb` (C33). -/
theorem sw_hb {a b : E} (h : G.SW a b) : G.HB a b := .single (.inr h)

/-! ## Pure authority markers and `sw` (C29, C32) -/

/-- No `sw` edge has a pure authority marker as source or target (C29: a pure authority marker "is
not a source or target of an `sw` edge"; C32). A consequence of the definition of `sw`, not a
hypothesis. -/
theorem sw_not_pure {a b : E} (h : G.SW a b) : ¬ G.Pure a ∧ ¬ G.Pure b := by
  have hacc : ∀ {e : E} {x : Acc U V}, G.acc? e = some x → ¬ G.Pure e := fun h hp => by
    rw [G.acc?_pure hp] at h; cases h
  have hsync : ∀ {e : E} {r : SyncRole C}, G.sync? e = some r → ¬ G.Pure e := fun h hp => by
    rw [G.sync?_pure hp] at h; cases h
  rcases h with ⟨u, m, ⟨o, k, ha, -⟩, ⟨o', k', hb, -⟩, -⟩ | ⟨c, ha, hb⟩ | ⟨c, ha, hb⟩
  · exact ⟨hacc ha, hacc hb⟩
  · exact ⟨hsync ha, hsync hb⟩
  · exact ⟨hsync ha, hsync hb⟩

/-! ## Conflicts (C30) -/

/-- Conflict is symmetric (C30). -/
theorem conflict_symm {a b : E} (h : G.Conflict a b) : G.Conflict b a := by
  obtain ⟨ra, rb, ha, hb, hc, ⟨n, h1, h2⟩, hw⟩ := h
  exact ⟨rb, ra, hb, ha, Ne.symm hc, ⟨n, h2, h1⟩, hw.symm⟩

/-- Two events without a write component do not conflict (C30: "Two read-only events do not
conflict"). -/
theorem not_conflict_reads {a b : E} (ha : ¬ G.Writes a) (hb : ¬ G.Writes b) :
    ¬ G.Conflict a b := fun ⟨_, _, _, _, _, _, hw⟩ => hw.elim ha hb

/-- An RMW counts as a read and as a write (C30). -/
theorem rmw_reads_writes {e : E} (h : G.IsRMW e) : G.Reads e ∧ G.Writes e :=
  ⟨⟨_, h, trivial⟩, ⟨_, h, trivial⟩⟩

/-- An RMW conflicts, as a write, with every access of another context whose range intersects its
own, a read included (C30: "An RMW counts as both a read and a write for this purpose"). -/
theorem conflict_rmw {a b : E} {ra rb : Range} (h : G.IsRMW a) (ha : G.range? a = some ra)
    (hb : G.range? b = some rb) (hc : G.ctx a ≠ G.ctx b) (hi : ra.Inter rb) : G.Conflict a b :=
  ⟨ra, rb, ha, hb, hc, hi, .inl (G.rmw_reads_writes h).2⟩

/-- Conflict is characterized without `hb` (C30: "Conflict is distinct from … whether a sufficient
event-order relation exists"): it reads only the contexts, the ranges and the kinds. -/
theorem conflict_iff {a b : E} : G.Conflict a b ↔ ∃ ra rb, G.range? a = some ra ∧
    G.range? b = some rb ∧ G.ctx a ≠ G.ctx b ∧ ra.Inter rb ∧ (G.Writes a ∨ G.Writes b) :=
  Iff.rfl

/-! ## Races (C33) -/

/-- A race is symmetric (C33). -/
theorem race_symm {a b : E} (h : G.Race a b) : G.Race b a := by
  obtain ⟨hc, hk, ha, h1, h2⟩ := h
  exact ⟨Ne.symm hc, G.conflict_symm hk, ha.symm, h2, h1⟩

/-- Two atomic events are never in a race (C33, condition 3). -/
theorem not_race_atomic {a b : E} (ha : G.Atomic a) (hb : G.Atomic b) : ¬ G.Race a b :=
  fun ⟨_, _, h, _, _⟩ => h.elim (· ha) (· hb)

/-- A pair ordered by `hb` is not in a race (C33, condition 4). -/
theorem not_race_hb {a b : E} (h : G.HB a b ∨ G.HB b a) : ¬ G.Race a b :=
  fun ⟨_, _, _, h1, h2⟩ => h.elim h1 h2

/-! ## Conjuncts 4 and 5 (C34) -/

/-- Conjunct 4 entails conjunct 5 (C34.4, C34.5): coherence makes `hb` irreflexive. -/
theorem hbIrrefl_of_coherence (h : G.Coherence) : G.HbIrrefl := fun a ha => h a a ha (.inl rfl)

/-! ## The total order `S` (C34) -/

/-- A strict total order on the `seq_cst` events that extends `psc` (C34): it relates only `seq_cst`
events, is irreflexive and transitive, relates any two distinct `seq_cst` events, and contains
`psc`. -/
def SOrder (R : E → E → Prop) : Prop :=
  (∀ a b, R a b → G.SC a ∧ G.SC b) ∧ (∀ a, ¬ R a a) ∧ (∀ a b c, R a b → R b c → R a c) ∧
    (∀ a b, G.SC a → G.SC b → a ≠ b → R a b ∨ R b a) ∧ ∀ a b, G.PSC a b → R a b

end Graph

/-- A linear extension, on the elements of a list satisfying `Q`, of a transitive irreflexive
relation `P`. -/
private theorem linext {E : Type} (P : E → E → Prop) (Q : E → Prop)
    (hirr : ∀ a, ¬ P a a) (htr : ∀ a b c, P a b → P b c → P a c) :
    ∀ l : List E, ∃ R : E → E → Prop,
      (∀ a b, R a b → (a ∈ l ∧ Q a) ∧ (b ∈ l ∧ Q b)) ∧ (∀ a, ¬ R a a) ∧
      (∀ a b c, R a b → R b c → R a c) ∧
      (∀ a b, (a ∈ l ∧ Q a) → (b ∈ l ∧ Q b) → a ≠ b → R a b ∨ R b a) ∧
      (∀ a b, (a ∈ l ∧ Q a) → (b ∈ l ∧ Q b) → P a b → R a b)
  | [] => ⟨fun _ _ => False, fun _ _ h => h.elim, fun _ h => h, fun _ _ _ h => h.elim,
      fun _ _ h => absurd h.1 List.not_mem_nil, fun _ _ h => absurd h.1 List.not_mem_nil⟩
  | x :: l => by
    obtain ⟨R, hdom, hirrR, htrR, htot, hext⟩ := linext P Q hirr htr l
    by_cases hnew : Q x ∧ x ∉ l
    · -- `x` is new: place it after every element below one of its `P`-predecessors.
      let A : E → Prop := fun a => a ∈ l ∧ Q a
      let Below : E → Prop := fun a => A a ∧ ∃ p, A p ∧ P p x ∧ (a = p ∨ R a p)
      have hxA : ¬ A x := fun h => hnew.2 h.1
      have hBx : ¬ Below x := fun h => hxA h.1
      refine ⟨fun a b => R a b ∨ (b = x ∧ Below a) ∨ (a = x ∧ A b ∧ ¬ Below b), ?_, ?_, ?_, ?_, ?_⟩
      · intro a b h
        have hA : ∀ e, A e → e ∈ x :: l ∧ Q e := fun e he => ⟨List.mem_cons_of_mem _ he.1, he.2⟩
        have hX : x ∈ x :: l ∧ Q x := ⟨List.mem_cons_self .., hnew.1⟩
        rcases h with h | ⟨rfl, hb⟩ | ⟨rfl, hb, -⟩
        · exact ⟨hA _ (hdom a b h).1, hA _ (hdom a b h).2⟩
        · exact ⟨hA _ hb.1, hX⟩
        · exact ⟨hX, hA _ hb⟩
      · intro a h
        rcases h with h | ⟨rfl, hb⟩ | ⟨rfl, hb, -⟩
        · exact hirrR a h
        · exact hBx hb
        · exact hxA hb
      · intro a b c h₁ h₂
        rcases h₁ with h₁ | ⟨rfl, hb₁⟩ | ⟨rfl, hb₁, hnb₁⟩
        · rcases h₂ with h₂ | ⟨rfl, hb₂⟩ | ⟨rfl, -, -⟩
          · exact .inl (htrR a b c h₁ h₂)
          · obtain ⟨-, p, hp, hpx, hbp⟩ := hb₂
            refine .inr (.inl ⟨rfl, (hdom a b h₁).1, p, hp, hpx, .inr ?_⟩)
            rcases hbp with rfl | hbp
            · exact h₁
            · exact htrR a b p h₁ hbp
          · exact (hxA (hdom a b h₁).2).elim
        · rcases h₂ with h₂ | ⟨rfl, hb₂⟩ | ⟨-, hc, hnc⟩
          · exact (hxA (hdom b c h₂).1).elim
          · exact (hBx hb₂).elim
          · refine .inl ?_
            have hac : a ≠ c := fun e => hnc (e ▸ hb₁)
            rcases htot a c hb₁.1 hc hac with h | h
            · exact h
            · obtain ⟨-, p, hp, hpx, hap⟩ := hb₁
              refine (hnc ⟨hc, p, hp, hpx, .inr ?_⟩).elim
              rcases hap with rfl | hap
              · exact h
              · exact htrR c a p h hap
        · rcases h₂ with h₂ | ⟨rfl, hb₂⟩ | ⟨rfl, -, -⟩
          · refine .inr (.inr ⟨rfl, (hdom b c h₂).2, fun hc => hnb₁ ?_⟩)
            obtain ⟨-, p, hp, hpx, hcp⟩ := hc
            refine ⟨hb₁, p, hp, hpx, .inr ?_⟩
            rcases hcp with rfl | hcp
            · exact h₂
            · exact htrR b c p h₂ hcp
          · exact (hnb₁ hb₂).elim
          · exact (hxA hb₁).elim
      · intro a b ha hb hab
        have hA : ∀ e, e ∈ x :: l ∧ Q e → e ≠ x → A e := fun e he hne =>
          ⟨(List.mem_cons.1 he.1).resolve_left hne, he.2⟩
        by_cases hax : a = x
        · subst hax
          have hbA := hA b hb (Ne.symm hab)
          by_cases hbB : Below b
          · exact .inr (.inr (.inl ⟨rfl, hbB⟩))
          · exact .inl (.inr (.inr ⟨rfl, hbA, hbB⟩))
        · by_cases hbx : b = x
          · subst hbx
            by_cases haB : Below a
            · exact .inl (.inr (.inl ⟨rfl, haB⟩))
            · exact .inr (.inr (.inr ⟨rfl, hA a ha hax, haB⟩))
          · rcases htot a b (hA a ha hax) (hA b hb hbx) hab with h | h
            · exact .inl (.inl h)
            · exact .inr (.inl h)
      · intro a b ha hb hab
        have hA : ∀ e, e ∈ x :: l ∧ Q e → e ≠ x → A e := fun e he hne =>
          ⟨(List.mem_cons.1 he.1).resolve_left hne, he.2⟩
        by_cases hax : a = x
        · subst hax
          have hbx : b ≠ a := fun e => hirr a (e ▸ hab)
          refine .inr (.inr ⟨rfl, hA b hb hbx, fun hB => ?_⟩)
          obtain ⟨-, p, hp, hpx, hbp⟩ := hB
          rcases hbp with rfl | hbp
          · exact hirr b (htr b a b hpx hab)
          · exact hirrR b (htrR b p b hbp (hext p b hp (hA b hb hbx) (htr p a b hpx hab)))
        · by_cases hbx : b = x
          · subst hbx
            exact .inr (.inl ⟨rfl, hA a ha hax, a, hA a ha hax, hab, .inl rfl⟩)
          · exact .inl (hext a b (hA a ha hax) (hA b hb hbx) hab)
    · -- `x` adds nothing: either it is not `seq_cst`, or it is already in `l`.
      have hsame : ∀ e, (e ∈ x :: l ∧ Q e) ↔ (e ∈ l ∧ Q e) := fun e =>
        ⟨fun ⟨hm, hq⟩ => by
          rcases List.mem_cons.1 hm with rfl | hm
          · exact ⟨(not_and.1 hnew hq) |> fun h => Classical.not_not.1 h, hq⟩
          · exact ⟨hm, hq⟩,
         fun ⟨hm, hq⟩ => ⟨List.mem_cons_of_mem _ hm, hq⟩⟩
      refine ⟨R, fun a b h => ⟨(hsame a).2 (hdom a b h).1, (hsame b).2 (hdom a b h).2⟩, hirrR,
        htrR, fun a b ha hb => htot a b ((hsame a).1 ha) ((hsame b).1 hb),
        fun a b ha hb => hext a b ((hsame a).1 ha) ((hsame b).1 hb)⟩

namespace Graph

variable {E C U V S : Type} (G : Graph E C U V S)

/-- **The total order `S`** (C34: "For a finite event graph, this is equivalent to the existence of
a strict total order `S` on the `seq_cst` events that extends `psc`"): on a finite graph,
`SCConsistent` holds exactly when such an order exists. Finiteness is the hypothesis the clause
names; it serves only the direction from acyclicity to the order. -/
theorem scConsistent_iff_order (hfin : Finite E) :
    G.SCConsistent ↔ ∃ R : E → E → Prop, G.SOrder R := by
  constructor
  · intro hac
    obtain ⟨l, hl⟩ := hfin
    obtain ⟨R, hdom, hirr, htr, htot, hext⟩ := linext (TransGen G.PSC) G.SC hac
      (fun _ _ _ h₁ h₂ => TransGen.trans h₁ h₂) l
    refine ⟨R, fun a b h => ⟨(hdom a b h).1.2, (hdom a b h).2.2⟩, hirr, htr,
      fun a b ha hb => htot a b ⟨hl a, ha⟩ ⟨hl b, hb⟩, fun a b h => ?_⟩
    exact hext a b ⟨hl a, h.1⟩ ⟨hl b, h.2.2⟩ (.single h)
  · rintro ⟨R, -, hirr, htr, -, hext⟩ a ha
    have key : ∀ {b c}, TransGen G.PSC b c → R b c := by
      intro b c h
      induction h with
      | single h => exact hext _ _ h
      | tail _ h ih => exact htr _ _ _ ih (hext _ _ h)
    exact hirr a (key ha)

/-! ## Consequences of `psc` (C34) -/

/-- A `seq_cst` modification is release-capable and a `seq_cst` read component is
acquire-capable (C40: "`seq_cst` has release semantics for stores, acquire semantics for loads,
and both for RMWs"). -/
theorem relCap_of_sc {e : E} {u : U} (hs : G.SC e) (hm : G.ModOn e u) : G.RelCap e u := by
  obtain ⟨u', k, h⟩ := hs
  obtain ⟨hu, k', hk, hw⟩ := hm
  rw [G.unitOf_atomic h] at hu; cases hu
  rw [G.kind?_atomic h] at hk; cases hk
  exact ⟨_, k, h, hw, .inr (.inr rfl)⟩

/-- See `relCap_of_sc`. -/
theorem acqCap_of_sc {e : E} {u : U} (hs : G.SC e) (hr : G.ReadOn e u) : G.AcqCap e u := by
  obtain ⟨u', k, h⟩ := hs
  obtain ⟨hu, k', hk, hrd⟩ := hr
  rw [G.unitOf_atomic h] at hu; cases hu
  rw [G.kind?_atomic h] at hk; cases hk
  exact ⟨_, k, h, hrd, .inr (.inr rfl)⟩

/-- A consequence of `psc` (C34: "an `SC` read directly observing an `SC` modification follows that
modification in `S` through `hb|loc`"): if an `SC` read component of the unit `u` reads by `rf` an
`SC` modification of `u`, then `psc` relates the modification to the read, through `hb|loc`. No
conjunct is needed: the `rf` edge is an `sw` edge (C32.1, C48, the head as member). -/
theorem psc_of_rf_sc {w r : E} {u : U} (hw : G.SC w) (hwm : G.ModOn w u) (hr : G.SC r)
    (hrr : G.ReadOn r u) (hrf : G.rf w r) : G.PSC w r ∧ G.HBLoc w r := by
  have hsw : G.SW w r :=
    .inl ⟨u, w, G.relCap_of_sc hw hwm, G.acqCap_of_sc hr hrr, .inl rfl, hrf⟩
  have hl : G.HBLoc w r := ⟨G.sw_hb hsw, u, hwm.1, hrr.1⟩
  exact ⟨⟨hw, .inr (.inr (.inl hl)), hr⟩, hl⟩

/-- A consequence of `psc` (C34: "an `SC` read of a modification `w` precedes every `SC`
modification later than `w` in `mo` through `rb`"): if an `SC` event `r` reads `w` by `rf`, then
`psc` relates `r` to every `SC` event `w'` with `mo(w, w')` other than `r`, through `rb`. No
conjunct is needed. -/
theorem psc_of_rb_sc {w r w' : E} (hr : G.SC r) (hrf : G.rf w r) (hw' : G.SC w')
    (hmo : G.mo w w') (hne : r ≠ w') : G.PSC r w' ∧ G.RB r w' :=
  have hrb : G.RB r w' := ⟨⟨w, hrf, hmo⟩, hne⟩
  ⟨⟨hr, .inr (.inr (.inr (.inr hrb))), hw'⟩, hrb⟩

/-! ## `rb` (C34) -/

/-- `rb` is irreflexive (C34: `\ id`). -/
theorem rb_irrefl (a : E) : ¬ G.RB a a := fun h => h.2 rfl

/-- Under conjuncts 1 and 2, a pair `(a, a)` of `rf⁻¹ ; mo`, removed by `\ id`, is that of an event
that reads and writes, hence of an RMW (C34: "excluding a self-pair on an atomic RMW"). -/
theorem rfmo_self_rmw (h1 : G.RfWF) (h2 : G.MoTotal) {a w : E} (hrf : G.rf w a) (hmo : G.mo w a) :
    G.IsRMW a := by
  obtain ⟨u, -, -, k, hk, hr⟩ := h1.1 w a hrf
  obtain ⟨u', -, -, k', hk', hw⟩ := h2.1 w a hmo
  rw [hk] at hk'; cases hk'
  unfold IsRMW; rw [hk]
  cases k <;> first | rfl | exact hr.elim | exact hw.elim

/-! ## The segment of C48 (retained reading 5) -/

/-- Under conjunct 2, a modification related by `mo` to a modification of `u` is a modification of
`u`. -/
theorem modOn_of_mo (h2 : G.MoTotal) {a b : E} {u : U} (hmo : G.mo a b) (hb : G.ModOn b u) :
    G.ModOn a u ∧ G.ModOn b u := by
  obtain ⟨u', ha', hb'⟩ := h2.1 a b hmo
  cases G.unitOf_inj hb'.1 hb.1
  exact ⟨ha', hb'⟩

/-- See `modOn_of_mo`. -/
theorem modOn_of_mo' (h2 : G.MoTotal) {a b : E} {u : U} (hmo : G.mo a b) (ha : G.ModOn a u) :
    G.ModOn a u ∧ G.ModOn b u := by
  obtain ⟨u', ha', hb'⟩ := h2.1 a b hmo
  cases G.unitOf_inj ha'.1 ha.1
  exact ⟨ha', hb'⟩

/-- Under conjunct 2, `mo` is transitive through modifications of one unit. -/
theorem mo_trans (h2 : G.MoTotal) {a b c : E} {u : U} (hb : G.ModOn b u) (h₁ : G.mo a b)
    (h₂ : G.mo b c) : G.mo a c :=
  (h2.2 u).2.1 a b c (G.modOn_of_mo h2 h₁ hb).1 hb (G.modOn_of_mo' h2 h₂ hb).2 h₁ h₂

/-- Under conjunct 2, `mo` is irreflexive. -/
theorem mo_irrefl (h2 : G.MoTotal) (a : E) : ¬ G.mo a a := fun h => by
  obtain ⟨u, ha, -⟩ := h2.1 a a h
  exact (h2.2 u).1 a ha h

/-- The segment of the release sequence is convex (C48, under conjunct 2; retained reading 5): every
modification of `u` lying in `mo` between `h` and a member is a member. -/
theorem rsMember_between (h2 : G.MoTotal) {u : U} {h m x : E} (hm : G.RSMember u h m)
    (hx : G.ModOn x u) (h₁ : G.mo h x) (h₂ : G.mo x m) : G.RSMember u h x := by
  rcases hm with rfl | ⟨-, -, hall⟩
  · exact (G.mo_irrefl h2 _ (G.mo_trans h2 hx h₁ h₂)).elim
  · refine .inr ⟨hall x hx h₁ h₂, h₁, fun y hy hy₁ hy₂ => hall y hy hy₁ ?_⟩
    exact G.mo_trans h2 hx hy₂ h₂

/-- The segment of the release sequence stops at the first modification that is not an atomic RMW
(C48: "Ordinary atomic stores, including same-thread non-RMW stores, do **not** extend the
sequence"; under conjunct 2; retained reading 5): if a modification `x` of `u` after `h` in `mo` is
not an atomic RMW, neither it nor any modification of `u` after it is a member. The statement does
not assume that a first such modification exists. -/
theorem not_rsMember_after (h2 : G.MoTotal) {u : U} {h x : E} (hx : G.ModOn x u)
    (h₁ : G.mo h x) (hnr : ¬ G.AtomicRMWOn x u) :
    ¬ G.RSMember u h x ∧ ∀ y, G.ModOn y u → G.mo x y → ¬ G.RSMember u h y := by
  refine ⟨fun hm => ?_, fun y hy hxy hm => ?_⟩
  · rcases hm with rfl | ⟨hr, -, -⟩
    · exact G.mo_irrefl h2 _ h₁
    · exact hnr hr
  · rcases hm with rfl | ⟨-, -, hall⟩
    · exact G.mo_irrefl h2 _ (G.mo_trans h2 hx h₁ hxy)
    · exact hnr (hall x hx h₁ hxy)

/-! ## Release sequences and `rf` chains (C31, C48) -/

/-- An `rf` chain from `h` to `m` on the unit `u`: a finite sequence `h = c₀, c₁, …, c_k = m`,
`k ≥ 1`, where each `c_{i+1}` is an atomic RMW modification of `u` that reads `c_i` by `rf`. C48
defines the release sequence by `mo`: chains are not its definition. -/
inductive Chain (u : U) (h : E) : E → Prop where
  | one {m : E} : G.AtomicRMWOn m u → G.rf h m → Chain u h m
  | step {x m : E} : Chain u h x → G.AtomicRMWOn m u → G.rf x m → Chain u h m

/-- The last element of a chain is an atomic RMW modification of the unit. -/
theorem chain_atomicRMW {u : U} {h m : E} (hc : G.Chain u h m) : G.AtomicRMWOn m u := by
  cases hc with
  | one hm _ => exact hm
  | step _ hm _ => exact hm

/-- Under conjuncts 2 and 3, a chain follows `mo` and the head is a modification of the unit. -/
theorem chain_mo (h2 : G.MoTotal) (h3 : G.RmwAtomic) {u : U} {h m : E} (hc : G.Chain u h m) :
    G.mo h m ∧ G.ModOn h u := by
  induction hc with
  | one hm hrf =>
    have hmo := (h3 _ _ (G.isRMW_of_rmw hm) (G.atomic_of_rmw hm) hrf).1
    exact ⟨hmo, (G.modOn_of_mo h2 hmo (G.modOn_of_rmw hm)).1⟩
  | step _ hm hrf ih =>
    have hmo := (h3 _ _ (G.isRMW_of_rmw hm) (G.atomic_of_rmw hm) hrf).1
    have hx := (G.modOn_of_mo' h2 ih.1 ih.2).2
    exact ⟨G.mo_trans h2 hx ih.1 hmo, ih.2⟩

/-- **Release sequence and chains, statement 1** (C31, C48; retained reading 5): on every graph,
under conjuncts 2 and 3, the end of a chain from `h` is a member of the release sequence of `h`.
Conjunct 1 is not used. -/
theorem rsMember_of_chain (h2 : G.MoTotal) (h3 : G.RmwAtomic) {u : U} {h m : E}
    (hc : G.Chain u h m) : G.RSMember u h m := by
  induction hc with
  | @one m hm hrf =>
    have ⟨hmo, himm⟩ := h3 _ _ (G.isRMW_of_rmw hm) (G.atomic_of_rmw hm) hrf
    exact .inr ⟨hm, hmo, fun x _ h₁ h₂ => (himm x ⟨h₁, h₂⟩).elim⟩
  | @step x m hcx hm hrf ih =>
    have ⟨hmo, himm⟩ := h3 _ _ (G.isRMW_of_rmw hm) (G.atomic_of_rmw hm) hrf
    have ⟨hhx, hh⟩ := G.chain_mo h2 h3 hcx
    have hxm := G.modOn_of_rmw (G.chain_atomicRMW hcx)
    refine .inr ⟨hm, G.mo_trans h2 hxm hhx hmo, fun y hy h₁ h₂ => ?_⟩
    by_cases hyx : y = x
    · subst hyx; exact G.chain_atomicRMW hcx
    · rcases (h2.2 u).2.2 y x hy hxm hyx with hyx' | hxy
      · rcases ih with rfl | ⟨-, -, hall⟩
        · exact (G.mo_irrefl h2 _ hhx).elim
        · exact hall y hy h₁ hyx'
      · exact (himm y ⟨hxy, h₂⟩).elim

/-- The modifications of `u` lying in `mo` strictly between `h` and `m` are finitely many. -/
def FiniteBetween (u : U) (h m : E) : Prop :=
  ∃ l : List E, ∀ x, G.ModOn x u → G.mo h x → G.mo x m → x ∈ l

/-- Under conjuncts 2 and 3, the modifications between the head and the end of a chain are finitely
many: they are elements of the chain. -/
theorem finiteBetween_of_chain (h2 : G.MoTotal) (h3 : G.RmwAtomic) {u : U} {h m : E}
    (hc : G.Chain u h m) : G.FiniteBetween u h m := by
  induction hc with
  | @one m hm hrf =>
    obtain ⟨-, himm⟩ := h3 _ _ (G.isRMW_of_rmw hm) (G.atomic_of_rmw hm) hrf
    exact ⟨[], fun x _ h₁ h₂ => (himm x ⟨h₁, h₂⟩).elim⟩
  | @step x m hcx hm hrf ih =>
    obtain ⟨l, hl⟩ := ih
    obtain ⟨-, himm⟩ := h3 _ _ (G.isRMW_of_rmw hm) (G.atomic_of_rmw hm) hrf
    have hxm := G.modOn_of_rmw (G.chain_atomicRMW hcx)
    refine ⟨x :: l, fun y hy h₁ h₂ => ?_⟩
    by_cases hyx : y = x
    · subst hyx; exact List.mem_cons_self ..
    · rcases (h2.2 u).2.2 y x hy hxm hyx with hyx' | hxy
      · exact List.mem_cons_of_mem _ (hl y hy h₁ hyx')
      · exact (himm y ⟨hxy, h₂⟩).elim

/-- The converse of statement 2, by induction on a bound of the number of modifications between
`h` and `m`. -/
private theorem chain_of_rsMember (h1 : G.RfWF) (h2 : G.MoTotal) (h3 : G.RmwAtomic) {u : U}
    {h : E} : ∀ (n : Nat) (m : E) (l : List E), l.length ≤ n →
      (∀ x, G.ModOn x u → G.mo h x → G.mo x m → x ∈ l) → G.RSMember u h m → m ≠ h →
      G.Chain u h m
  | n, m, l, hn, hl, hm, hne => by
    rcases hm with rfl | ⟨hmr, hhm, hall⟩
    · exact (hne rfl).elim
    obtain ⟨⟨w, hrf⟩, -⟩ := h1.2.1 m u (G.readOn_of_rmw hmr)
    have ⟨hwm, himm⟩ := h3 _ _ (G.isRMW_of_rmw hmr) (G.atomic_of_rmw hmr) hrf
    have hmm := G.modOn_of_rmw hmr
    have hw := (G.modOn_of_mo h2 hwm hmm).1
    have hh := (G.modOn_of_mo h2 hhm hmm).1
    by_cases hwh : w = h
    · subst hwh; exact .one hmr hrf
    rcases (h2.2 u).2.2 w h hw hh hwh with hwh' | hhw
    · exact (himm h ⟨hwh', hhm⟩).elim
    have hwr := hall w hw hhw hwm
    have hwl : w ∈ l := hl w hw hhw hwm
    classical
    cases n with
    | zero =>
      cases l with
      | nil => exact (List.not_mem_nil hwl).elim
      | cons _ _ => exact (Nat.not_succ_le_zero _ hn).elim
    | succ n =>
      have hlen : (l.erase w).length ≤ n := by
        rw [List.length_erase_of_mem hwl]; omega
      have hcw := chain_of_rsMember h1 h2 h3 n w (l.erase w) hlen
        (fun y hy h₁ h₂ => (List.mem_erase_of_ne (fun e => by subst e; exact G.mo_irrefl h2 _ h₂)).2
          (hl y hy h₁ (G.mo_trans h2 hw h₂ hwm)))
        (G.rsMember_between h2 (.inr ⟨hmr, hhm, hall⟩) hw hhw hwm) hwh
      exact .step hcw hmr hrf

/-- **Release sequence and chains, statement 2** (C31, C48; retained reading 5): on every graph,
under conjuncts 1 to 3, for `m ≠ h`, a chain relates `h` to `m` exactly when `m` is a member of the
release sequence of `h` and the modifications of the unit lying in `mo` strictly between `h` and `m`
are finitely many. -/
theorem chain_iff (h1 : G.RfWF) (h2 : G.MoTotal) (h3 : G.RmwAtomic) {u : U} {h m : E}
    (hne : m ≠ h) : G.Chain u h m ↔ G.RSMember u h m ∧ G.FiniteBetween u h m :=
  ⟨fun hc => ⟨G.rsMember_of_chain h2 h3 hc, G.finiteBetween_of_chain h2 h3 hc⟩,
   fun ⟨hm, l, hl⟩ => G.chain_of_rsMember h1 h2 h3 l.length m l (Nat.le_refl _) hl hm hne⟩

/-- **Release sequence and chains, statement 3** (C31, C48; retained reading 5): on a finite graph,
under conjuncts 1 to 3, the members of the release sequence of `h` other than `h` are exactly the
atomic RMW modifications that a chain relates to `h`. A corollary of statement 2; finiteness, a
hypothesis of the statement, gives the finitely many modifications in between. On such a
graph the interval reading and the reading by chains give the same members. -/
theorem rsMember_iff_chain (hfin : Finite E) (h1 : G.RfWF) (h2 : G.MoTotal) (h3 : G.RmwAtomic)
    {u : U} {h m : E} : (G.RSMember u h m ∧ m ≠ h) ↔ (G.AtomicRMWOn m u ∧ G.Chain u h m) := by
  obtain ⟨l, hl⟩ := hfin
  constructor
  · rintro ⟨hm, hne⟩
    have hc := (G.chain_iff h1 h2 h3 hne).2 ⟨hm, l, fun x _ _ _ => hl x⟩
    exact ⟨G.chain_atomicRMW hc, hc⟩
  · rintro ⟨-, hc⟩
    refine ⟨G.rsMember_of_chain h2 h3 hc, fun e => ?_⟩
    subst e
    exact G.mo_irrefl h2 _ (G.chain_mo h2 h3 hc).1

end Graph

end Ern.ConcurrencyModel.Events
