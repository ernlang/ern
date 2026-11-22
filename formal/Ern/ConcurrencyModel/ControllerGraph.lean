import Ern.ConcurrencyModel.Controller
import Ern.ConcurrencyModel.Legality

/-!
# Theorem 13d.1: the controller graph of an execution (C31, C34, C48)

For an execution in which a `newMutex` step creates an entry whose controller stays the same leaf
until the end, and a legal order triple, the graph made of the `newMutex` write and of the events
of the protocol steps on the entry, in the order of the trace, each RMW reading the modification
that precedes it, with the roles of R, satisfies realization R, `OrderLegal` and `EventConsistent`, with a
correspondence of fragment F (`controller_graph`). This is the non-vacuity of R on every execution
of this fragment (`OB-C05`, abstract part).
-/

namespace Ern.ConcurrencyModel

open Ern.MemoryModel Ern.MemoryModel.Access

variable {pm : ProviderMeta}

section Construction

variable (L : MutexLayout) (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) (i x : Nat)
  (R : CtlOrders) (v₀ v₁ : Nat)

/-- The events of the controller graph: the controller steps (C48). -/
abbrev CtlEv : Type := {k : Nat // CtlStep L σ lbls i x k}

/-- The context of the label of step `k`. -/
def requesterAt (k : Nat) : Nat := ((lbls[k]?).map Label.requester).getD 0

/-- The access of the event of step `k` under realization R (`ctlAcc`). -/
def accAt (k : Nat) : Events.Acc Nat Nat :=
  match lbls[k]? with
  | some lbl => ctlAcc x R v₀ v₁ lbl
  | none => .unit x (.write v₀)

/-- The `sync` attribute of the event of step `k` under realization R (`ctlSync`). -/
def syncAt (k : Nat) : Option (Events.SyncRole Nat) :=
  match lbls[k]? with
  | some lbl => ctlSync lbl
  | none => none

/-- The controller graph (C26, C31, C48): one event per controller step, of context the context of
its label, of access `ctlAcc` and of `sync` attribute `ctlSync`; `po` is the trace order within a
context;
`rf` relates the last controller step before an `acquire` to it; `mo` is the trace order. -/
def ctlGraph : Events.Graph (CtlEv L σ lbls i x) Nat Nat Nat Unit where
  ev k := ⟨requesterAt lbls k.1, ⟨k.1, 0⟩,
    .marks (some (accAt lbls x R v₀ v₁ k.1)) (syncAt lbls k.1)⟩
  uRange _ := ⟨0, 1⟩
  po a b := requesterAt lbls a.1 = requesterAt lbls b.1 ∧ a.1 < b.1
  rf a b := (∃ c j, lbls[b.1]? = some (.acquire c j)) ∧ LastCtl L σ lbls i x b.1 a.1
  mo a b := a.1 < b.1
  po_irrefl a h := Nat.lt_irrefl _ h.2
  po_trans h₁ h₂ := ⟨h₁.1.trans h₂.1, Nat.lt_trans h₁.2 h₂.2⟩
  po_ctx h := h.1
  po_total {a b} h hne := by
    rcases Nat.lt_trichotomy a.1 b.1 with h' | h' | h'
    · exact .inl ⟨h, h'⟩
    · exact absurd (Subtype.ext h') hne
    · exact .inr ⟨h.symm, h'⟩

/-- The correspondence of the controller graph (fragment F): the event of each controller step,
no lifecycle marker. -/
def ctlK : StepEvents (CtlEv L σ lbls i x) :=
  ⟨fun k => if h : CtlStep L σ lbls i x k then some ⟨k, h⟩ else none, fun _ => none, fun _ => none⟩

end Construction

section Proofs

variable {ks : KShared} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label}
  {i x : Nat} {R : CtlOrders} {v₀ v₁ : Nat}

/-- The event of a controller step under `ctlK`. -/
theorem ctlK_ev {k : Nat} {e : CtlEv L σ lbls i x} :
    (ctlK L σ lbls i x).ev k = some e ↔ e.1 = k := by
  unfold ctlK
  by_cases h : CtlStep L σ lbls i x k
  · simp only [h, dite_true, Option.some.injEq]
    exact ⟨fun e' => by rw [← e'], fun e' => Subtype.ext e'.symm⟩
  · simp only [h, dite_false]
    exact ⟨(fun e' => by cases e'), fun e' => absurd (e' ▸ e.2) h⟩

/-- Every event of the controller graph writes the unit `x`; only an `acquire` reads it. -/
theorem ctlGraph_access (e : CtlEv L σ lbls i x) :
    (ctlGraph L σ lbls i x R v₀ v₁).ModOn e x ∧
    ((ctlGraph L σ lbls i x R v₀ v₁).Reads e → ∃ c j, lbls[e.1]? = some (.acquire c j)) := by
  obtain ⟨lbl, hl⟩ := e.2.label
  have hacc : (ctlGraph L σ lbls i x R v₀ v₁).acc? e = some (ctlAcc x R v₀ v₁ lbl) := by
    show some (accAt lbls x R v₀ v₁ e.1) = _
    unfold accAt; rw [hl]
  refine ⟨⟨?_, ?_⟩, fun ⟨k, hk, hr⟩ => ?_⟩
  · unfold Events.Graph.unitOf; rw [hacc]; cases lbl <;> rfl
  · unfold Events.Graph.Writes Events.Graph.kind?; rw [hacc]
    cases lbl <;> exact ⟨_, rfl, trivial⟩
  · unfold Events.Graph.kind? at hk; rw [hacc] at hk
    cases lbl with
    | acquire c j => exact ⟨c, j, hl⟩
    | _ => cases hk; exact hr.elim

/-- Every controller step is at or after the `newMutex` step `n` that creates the entry. -/
theorem ctl_ge (hr : EncapRun pm ks L σ lbls) {n c g : Nat} (hn : lbls[n]? = some (.newMutex c g))
    (hnc : CtlStep L σ lbls i x n) {w : Nat} (hw : CtlStep L σ lbls i x w) : n ≤ w := by
  have hnl : n < lbls.length := (List.getElem?_eq_some_iff.1 hn).1
  have hlen : (σ n).2.1.length = i := by unfold CtlStep at hnc; rw [hn] at hnc; exact hnc.1
  refine Decidable.byContradiction fun hlt => ?_
  have hwn : w < n := Nat.lt_of_not_le hlt
  have hmono := encapRun_reg_mono hr (a := w + 1) (b := n) (by omega) (Nat.le_of_lt hnl)
  obtain ⟨lbl, hl⟩ := hw.label
  have hwl : w < lbls.length := (List.getElem?_eq_some_iff.1 hl).1
  unfold CtlStep at hw; rw [hl] at hw
  have hmono0 := encapRun_reg_mono hr (Nat.le_of_lt hwn) (Nat.le_of_lt hnl)
  cases lbl with
  | newMutex c' g' =>
    have hs := (hr w hwl).2
    rw [(List.getElem?_eq_some_iff.1 hl).2] at hs
    have := lstep_newMutex hs
    have hl1 : (σ (w + 1)).2.1.length = i + 1 := by rw [this]; simp [hw.1]
    omega
  | acquire c' j | unlock c' j | resetLock c' j =>
    obtain ⟨rfl, hctl⟩ := hw
    unfold ctlOf at hctl
    cases he : (σ w).2.1[j]? with
    | none => rw [he] at hctl; cases hctl
    | some _ =>
      have := (List.getElem?_eq_some_iff.1 he).1
      omega
  | _ => exact hw.elim

/-- A relation that increases the step index is acyclic. -/
theorem acyclic_of_lt {α : Type} {P : α → Prop} {Rel : {k : α // P k} → {k : α // P k} → Prop}
    (f : α → Nat) (h : ∀ a b, Rel a b → f a.1 < f b.1) (a : {k : α // P k}) :
    ¬ Relation.TransGen Rel a a := by
  have key : ∀ a b, Relation.TransGen Rel a b → f a.1 < f b.1 := fun a b hab => by
    induction hab with
    | single h' => exact h _ _ h'
    | tail _ h' ih => exact Nat.lt_trans ih (h _ _ h')
  exact fun hc => Nat.lt_irrefl _ (key a a hc)

/-- In the controller graph, `hb` and `eco` increase the step index (C33, C34). -/
theorem ctlGraph_lt :
    (∀ a b, (ctlGraph L σ lbls i x R v₀ v₁).HB a b → a.1 < b.1) ∧
    (∀ a b, (ctlGraph L σ lbls i x R v₀ v₁).RB a b → a.1 < b.1) ∧
    (∀ a b, (ctlGraph L σ lbls i x R v₀ v₁).ECO a b → a.1 < b.1) := by
  let G := ctlGraph L σ lbls i x R v₀ v₁
  have hrf : ∀ a b, G.rf a b → a.1 < b.1 := fun a b h => h.2.2.1
  have hposw : ∀ a b, G.PoSw a b → a.1 < b.1 := by
    intro a b h
    rcases h with h | h
    · exact h.2
    · rcases h with ⟨u, m, -, -, hm, hrfm⟩ | ⟨c, h, -⟩ | ⟨c, h, -⟩
      · have hmb := hrf m b hrfm
        rcases hm with rfl | ⟨-, hmo, -⟩
        · exact hmb
        · exact Nat.lt_trans hmo hmb
      · exact absurd h (by
          show syncAt lbls a.1 ≠ _
          unfold syncAt; split
          · rename_i lbl _; cases lbl <;> simp [ctlSync]
          · simp)
      · exact absurd h (by
          show syncAt lbls a.1 ≠ _
          unfold syncAt; split
          · rename_i lbl _; cases lbl <;> simp [ctlSync]
          · simp)
  have hhb : ∀ a b, G.HB a b → a.1 < b.1 := fun a b h => by
    induction h with
    | single h' => exact hposw _ _ h'
    | tail _ h' ih => exact Nat.lt_trans ih (hposw _ _ h')
  have hrb : ∀ a b, G.RB a b → a.1 < b.1 := by
    rintro a b ⟨⟨w, ⟨-, hlast⟩, hwb⟩, hne⟩
    rcases Nat.lt_trichotomy a.1 b.1 with h | h | h
    · exact h
    · exact absurd (Subtype.ext h) hne
    · have := hlast.2.2 b.1 b.2 h
      have hwb' : w.1 < b.1 := hwb
      omega
  refine ⟨hhb, hrb, fun a b h => ?_⟩
  induction h with
  | single h' =>
    rcases h' with h' | h' | h'
    · exact hrf _ _ h'
    · exact h'
    · exact hrb _ _ h'
  | tail _ h' ih =>
    refine Nat.lt_trans ih ?_
    rcases h' with h' | h' | h'
    · exact hrf _ _ h'
    · exact h'
    · exact hrb _ _ h'

/-- **Theorem 13d.1**, construction (C31, C34, C48; `OB-C05`, abstract part): for an execution in
which the `newMutex` step `n` creates entry `i` with controller `x`, every later protocol step on
`i` being taken while the controller is `x` (the controller stays the same leaf until the end), a
legal order triple and values `v₀ ≠ v₁`, the controller graph with its correspondence satisfies
realization R, `OrderLegal` (C40), `EventConsistent` (C34), and the correspondence of fragment F
(K1–K4): R is not vacuous on any execution of this fragment. -/
theorem controller_graph (hr : EncapRun pm ks L σ lbls) {n c g : Nat}
    (hn : lbls[n]? = some (.newMutex c g)) (hnc : CtlStep L σ lbls i x n)
    (hstab : ∀ k, n < k → ProtoOn lbls i k → ctlOf L (σ k) i = some x) (hlegal : R.Legal)
    (hv : v₀ ≠ v₁) :
    Realizes (ctlGraph L σ lbls i x R v₀ v₁) L σ lbls (ctlK L σ lbls i x) i x R v₀ v₁ ∧
    (ctlGraph L σ lbls i x R v₀ v₁).OrderLegal ∧
    (ctlGraph L σ lbls i x R v₀ v₁).EventConsistent ∧
    Corresponds (ctlGraph L σ lbls i x R v₀ v₁) σ lbls (ctlK L σ lbls i x) := by
  let G := ctlGraph L σ lbls i x R v₀ v₁
  have hacc : ∀ (e : CtlEv L σ lbls i x) lbl, lbls[e.1]? = some lbl →
      G.acc? e = some (ctlAcc x R v₀ v₁ lbl) := fun e lbl hl => by
    show some (accAt lbls x R v₀ v₁ e.1) = _
    unfold accAt; rw [hl]
  obtain ⟨hhb, hrb, heco⟩ := ctlGraph_lt (L := L) (σ := σ) (lbls := lbls) (i := i) (x := x)
    (R := R) (v₀ := v₀) (v₁ := v₁)
  -- the last controller step before an `acquire`, and the value it writes
  have hlastex : ∀ k c' j, lbls[k]? = some (.acquire c' j) → CtlStep L σ lbls i x k →
      ∃ w, LastCtl L σ lbls i x k w ∧ ∀ c'' j', lbls[w]? ≠ some (.acquire c'' j') := by
    intro k c' j hl hk
    have hkl : k < lbls.length := (List.getElem?_eq_some_iff.1 hl).1
    have hnk : n < k := by
      rcases Nat.lt_or_eq_of_le (ctl_ge hr hn hnc hk) with h | h
      · exact h
      · subst h; rw [hn] at hl; cases hl
    obtain ⟨w, hlast, hiff⟩ := grant_invariant hr hn hnc hstab k hnk (Nat.le_of_lt hkl)
    have hji : j = i := by unfold CtlStep at hk; rw [hl] at hk; exact hk.1
    subst hji
    have hs := (hr k hkl).2
    rw [(List.getElem?_eq_some_iff.1 hl).2] at hs
    exact ⟨w, hlast, hiff.1 ((lstep_reg hs j).2.2.1 c' rfl).1⟩
  have hrfwf : G.RfWF := by
    refine ⟨fun w r hwr => ⟨x, (ctlGraph_access w).1, ?_, ?_⟩, fun r u hru => ?_,
      fun w r hwr => ?_⟩
    · exact (ctlGraph_access r).1.1
    · obtain ⟨⟨c', j, hl⟩, -⟩ := hwr
      exact ⟨.rmw, by unfold Events.Graph.kind?; rw [hacc r _ hl]; rfl, trivial⟩
    · obtain ⟨c', j, hl⟩ := (ctlGraph_access r).2 hru.2
      obtain ⟨w, hlast, -⟩ := hlastex r.1 c' j hl r.2
      refine ⟨⟨⟨w, hlast.1⟩, ⟨c', j, hl⟩, hlast⟩, fun w₁ w₂ h₁ h₂ => ?_⟩
      exact Subtype.ext (h₁.2.unique h₂.2)
    · obtain ⟨⟨c', j, hl⟩, hlast⟩ := hwr
      obtain ⟨w', hlast', hnacq⟩ := hlastex r.1 c' j hl r.2
      have := hlast.unique hlast'
      obtain ⟨lw, hlw⟩ := hlast.1.label
      refine ⟨v₀, ?_, by unfold Events.Graph.valR; rw [hacc r _ hl]; rfl⟩
      unfold Events.Graph.valW; rw [hacc w _ hlw]
      rw [← this] at hnacq
      cases lw with
      | acquire c'' j' => exact absurd hlw (hnacq c'' j')
      | _ => rfl
  have hunit : ∀ e : CtlEv L σ lbls i x, ∀ u, G.ModOn e u → u = x := fun e u h =>
    Events.Graph.unitOf_inj G h.1 (ctlGraph_access e).1.1
  have hmo : G.MoTotal := by
    refine ⟨fun a b _ => ⟨x, (ctlGraph_access a).1, (ctlGraph_access b).1⟩, fun u => ⟨?_, ?_, ?_⟩⟩
    · exact fun a _ h => Nat.lt_irrefl _ h
    · exact fun a b c _ _ _ h₁ h₂ => Nat.lt_trans h₁ h₂
    · intro a b _ _ hne
      rcases Nat.lt_trichotomy a.1 b.1 with h | h | h
      · exact .inl h
      · exact absurd (Subtype.ext h) hne
      · exact .inr h
  have hrmw : G.RmwAtomic := by
    rintro w r - - ⟨-, hlast⟩
    exact ⟨hlast.2.1, fun y ⟨h₁, h₂⟩ => by have := hlast.2.2 y.1 y.2 h₂; exact absurd h₁ (by
      show ¬ w.1 < y.1; omega)⟩
  have hcoh : G.Coherence := fun a b hab h => by
    have := hhb a b hab
    rcases h with rfl | h
    · exact Nat.lt_irrefl _ this
    · have := heco b a h; omega
  have hhbi : G.HbIrrefl := fun a h => Nat.lt_irrefl _ (hhb a a h)
  have hnta : G.NoThinAir := acyclic_of_lt id fun a b h => by
    rcases h with h | h
    · exact h.2
    · exact h.2.2.1
  have hsc : G.SCConsistent := acyclic_of_lt id fun a b h => by
    obtain ⟨-, h, -⟩ := h
    rcases h with h | ⟨y, z, h₁, h₂, h₃⟩ | ⟨h, -⟩ | h | h
    · exact h.2
    · exact Nat.lt_trans h₁.2 (Nat.lt_trans (hhb _ _ h₂) h₃.2)
    · exact hhb _ _ h
    · exact h
    · exact hrb _ _ h
  have hsyn : ∀ (e : CtlEv L σ lbls i x) lbl, lbls[e.1]? = some lbl → G.sync? e = ctlSync lbl :=
    fun e lbl hl => by
      show syncAt lbls e.1 = _
      unfold syncAt; rw [hl]
  refine ⟨⟨hv, fun k lbl hl hk => ⟨⟨k, hk⟩, ctlK_ev.2 rfl, hacc ⟨k, hk⟩ lbl hl,
    hsyn ⟨k, hk⟩ lbl hl⟩,
    fun k k' e e' _ _ he he' => ?_, fun w _ => ⟨w.1, w.2, ctlK_ev.2 rfl⟩⟩, ?_,
    ⟨hrfwf, hmo, hrmw, hcoh, hhbi, hnta, hsc⟩, ?_⟩
  · rw [← ctlK_ev.1 he, ← ctlK_ev.1 he']; exact Iff.rfl
  · intro e u o k he
    obtain ⟨lbl, hl⟩ := e.2.label
    rw [hacc e lbl hl] at he
    cases lbl <;> simp only [ctlAcc] at he <;> cases he
    · trivial
    · exact (rows_agree_orderOK R.rel).2.1.1 hlegal.2.1
    · exact (rows_agree_orderOK R.reset).2.1.1 hlegal.2.2
  · refine ⟨fun k hk e he => ?_, fun k k' e he he' => ?_, fun k k' hk hk' a b hlt hreq ha hb => ?_,
      fun s c' hcr e he => ?_, (fun c' x' h => by cases h), (fun c' x' h => by cases h),
      fun q hq c' d e hlq he => ?_⟩
    · have hke := ctlK_ev.1 he
      subst hke
      show ((lbls[e.1]?).map Label.requester).getD 0 = _
      rw [List.getElem?_eq_getElem hk]; rfl
    · exact (ctlK_ev.1 he).symm.trans (ctlK_ev.1 he')
    · have hka := ctlK_ev.1 ha
      have hkb := ctlK_ev.1 hb
      subst hka hkb
      refine ⟨?_, hlt⟩
      show ((lbls[a.1]?).map Label.requester).getD 0 = ((lbls[b.1]?).map Label.requester).getD 0
      rw [List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hk']
      simp only [Option.map_some, Option.getD_some]; exact hreq
    · exfalso
      have hcs := (ctlK_ev.1 he) ▸ e.2
      obtain ⟨hs, hkind, -⟩ := hcr
      unfold CtlStep at hcs
      rw [List.getElem?_eq_getElem hs] at hcs
      rcases hkind with ⟨_, _, _, h⟩ | ⟨_, _, _, _, h⟩ <;> rw [h] at hcs <;> exact hcs
    · exfalso
      have hcs := (ctlK_ev.1 he) ▸ e.2
      unfold CtlStep at hcs
      rw [List.getElem?_eq_getElem hq, hlq] at hcs
      exact hcs

end Proofs

end Ern.ConcurrencyModel
