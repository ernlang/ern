import Ern.ConcurrencyModel.Rc11Projection
import Ern.ConcurrencyModel.EventDecide

/-!
# Theorem 10e: the witnesses of statements (a) and (c) (C34; `OB-C23`, `OB-C26`)

* (a) **The published model is not included**: `Ga`, the example of the corrigendum with its
  non-atomic read removed, is consistent for the published `rc11.cat`, its projection is rejected
  by conjunct 7 alone, and it is inconsistent for RC11 amended (check `SC`).
* (c) **No converse**: the projection of `Gc` satisfies `EventConsistent`, while `Gc` is
  inconsistent for RC11 in both forms (check `coherence1`): `rs` lets the `relaxed` write of the
  same thread enter the release sequence (`(sb & loc)?`), which C48 does not. This is the difference
  that C34 announces between C48 and the published `rc11.cat`.
* (b) **A graph with a pair**: `Gp`, message passing through an `acq/rel` RMW, satisfies the
  hypotheses of (b) and its projection the conclusion; it exercises the pair branch of `π`. Its
  twin `Gpt`, whose last read returns the initial value, is inconsistent for RC11 in both forms and
  its projection is rejected by conjunct 4 alone.

Each location has its initial write of value `0`. Both witnesses are given without and with `sb`
edges from the initial writes to every event of a thread (`fromInit`); the expected verdicts hold in
both cases. Verdicts are computed by evaluation (`decide +kernel`).
-/

namespace Ern.ConcurrencyModel.Rc11

open Relation Ern.ConcurrencyModel.Events

/-! ## Deciding the checks of `rc11.cat` on an enumerated graph -/

namespace Graph

variable {E T V : Type} (G : Graph E T V) [Enum E] [DecidableEq E] [DecidableEq T]
  [DecidableEq V] [DecidableRel G.sb] [DecidableRel G.rf] [DecidableRel G.mo]

instance (e : E) : Decidable (G.R e) := inferInstanceAs (Decidable (_ = _))
instance (e : E) : Decidable (G.W e) := inferInstanceAs (Decidable (_ = _))
instance (e : E) : Decidable (G.IW e) := inferInstanceAs (Decidable (_ = _))
instance (e : E) : Decidable (G.A e) := inferInstanceAs (Decidable (_ = _))
instance (e : E) : Decidable (G.RLX e) := inferInstanceAs (Decidable (_ = _))
instance (e : E) : Decidable (G.REL e) := inferInstanceAs (Decidable (_ = _))
instance (e : E) : Decidable (G.ACQ_REL e) := inferInstanceAs (Decidable (_ = _))
instance (e : E) : Decidable (G.ACQ e) := inferInstanceAs (Decidable (_ = _))
instance (e : E) : Decidable (G.SC e) := inferInstanceAs (Decidable (_ = _))
instance (e : E) : Decidable (G.Atomic e) := by unfold Atomic; infer_instance
instance : DecidableRel G.rmw := fun _ _ => inferInstanceAs (Decidable (_ = _))
instance (e : E) : Decidable (G.RMW e) := by unfold RMW; infer_instance
instance : DecidableRel G.loc := fun _ _ => inferInstanceAs (Decidable (_ = _))
instance : DecidableRel G.myrmw := fun _ _ => by unfold myrmw; infer_instance
instance : DecidableRel G.rb := fun _ _ => by unfold rb; infer_instance
instance : DecidableRel G.ecoBase := fun _ _ => by unfold ecoBase; infer_instance
instance : DecidableRel G.eco := fun a b => Enum.decTransGen G.ecoBase a b
instance : DecidableRel G.rfMy := fun _ _ => by unfold rfMy; infer_instance
instance : DecidableRel (RTC G.rfMy) := fun a b =>
  haveI := Enum.decTransGen G.rfMy a b
  inferInstanceAs (Decidable (_ ∨ _))
instance : DecidableRel G.rs := fun _ _ => by unfold rs; infer_instance
instance : DecidableRel G.sw := fun _ _ => by unfold sw; infer_instance
instance : DecidableRel G.sbsw := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))
instance : DecidableRel G.hb := fun a b => Enum.decTransGen G.sbsw a b
instance : DecidableRel G.sbl := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
instance : DecidableRel G.hbl := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
instance : DecidableRel G.scbPub := fun _ _ => by unfold scbPub; infer_instance
instance : DecidableRel G.sbNoRmw := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
instance : DecidableRel G.scbAm := fun _ _ => by unfold scbAm; infer_instance
instance : DecidableRel G.sbrf := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))
instance (scb : E → E → Prop) [DecidableRel scb] : DecidableRel (G.psc scb) :=
  fun _ _ => by unfold psc; infer_instance
instance : Decidable G.Coherence1 := by unfold Coherence1; infer_instance
instance : Decidable G.CoherenceRmw := by unfold CoherenceRmw; infer_instance
instance : Decidable G.Atomicity := by unfold Atomicity; infer_instance
instance (scb : E → E → Prop) [DecidableRel scb] : Decidable (G.SCCheck scb) := by
  unfold SCCheck Acyclic; infer_instance
instance : Decidable G.NoThinAir := by unfold NoThinAir Acyclic; infer_instance
instance : Decidable G.ConsistentPub := by unfold ConsistentPub; infer_instance
instance : Decidable G.ConsistentAm := by unfold ConsistentAm; infer_instance

/-! ## Deciding the predicates of the projection -/

instance : DecidablePred G.IsPairW := fun _ => by unfold IsPairW; infer_instance

variable (hF : G.Frag)

instance : DecidableRel (G.proj hF).po := fun a b =>
  inferInstanceAs (Decidable (G.sb a.1 b.1 ∧ ¬ G.IW a.1))
instance : DecidableRel (G.proj hF).rf := fun a b =>
  inferInstanceAs (Decidable (G.rf (G.wc a.1) b.1))
instance : DecidableRel (G.proj hF).mo := fun a b =>
  inferInstanceAs (Decidable (G.mo (G.wc a.1) (G.wc b.1)))

end Graph

/-! ## Graphs of the fragment given by lists -/

/-- A graph of the fragment on `Fin n`, with no pair, given by its labels and the lists of its `rf`
and `mo` edges; `sb` is the order of the indices within each thread, together with edges from every
initial write to every event of a thread when `fromInit` holds. -/
structure LG (n : Nat) (T V : Type) where
  lab : Fin n → Lab T V
  rf : List (Fin n × Fin n)
  mo : List (Fin n × Fin n)
  fromInit : Bool

/-- The graph of the fragment of an `LG`. -/
def LG.toGraph {n : Nat} {T V : Type} [DecidableEq T] (W : LG n T V) : Graph (Fin n) T V where
  lab := W.lab
  partner _ := none
  sb a b := ((W.lab a).thread?.isSome = true ∧ (W.lab a).thread? = (W.lab b).thread? ∧ a < b) ∨
    (W.fromInit = true ∧ (W.lab a).isIW = true ∧ (W.lab b).thread?.isSome = true)
  rf a b := (a, b) ∈ W.rf
  mo a b := (a, b) ∈ W.mo

instance {n : Nat} {T V : Type} [DecidableEq T] (W : LG n T V) : DecidableRel W.toGraph.sb :=
  fun _ _ => inferInstanceAs (Decidable (_ ∨ _))
instance {n : Nat} {T V : Type} [DecidableEq T] (W : LG n T V) : DecidableRel W.toGraph.rf :=
  fun _ _ => inferInstanceAs (Decidable (_ ∈ _))
instance {n : Nat} {T V : Type} [DecidableEq T] (W : LG n T V) : DecidableRel W.toGraph.mo :=
  fun _ _ => inferInstanceAs (Decidable (_ ∈ _))

/-- The annotation conditions of the fragment on one label. -/
def annOK {T V : Type} : Lab T V → Bool
  | .read _ _ _ a => a == .rlx || a == .acq || a == .sc
  | .write _ _ _ a => a == .rlx || a == .rel || a == .sc
  | .init .. => true

/-- The conditions of the fragment on a list graph, in a form decided by evaluation. -/
def LG.Check {n : Nat} {T V : Type} (W : LG n T V) : Prop :=
  (∀ e, ∃ i, (W.lab i).isIW = true ∧ (W.lab i).loc = (W.lab e).loc) ∧
  (∀ i j, (W.lab i).isIW = true → (W.lab j).isIW = true → (W.lab i).loc = (W.lab j).loc →
    i = j) ∧
  (∀ e, annOK (W.lab e) = true) ∧
  (∀ w r, (w, r) ∈ W.rf → (W.lab w).isW = true ∧ (W.lab r).isR = true ∧
    (W.lab w).loc = (W.lab r).loc ∧ (W.lab w).val = (W.lab r).val) ∧
  (∀ r, (W.lab r).isR = true → ∃ w, (w, r) ∈ W.rf) ∧
  (∀ w w' r, (w, r) ∈ W.rf → (w', r) ∈ W.rf → w = w') ∧
  (∀ a b, (a, b) ∈ W.mo → (W.lab a).isW = true ∧ (W.lab b).isW = true ∧
    (W.lab a).loc = (W.lab b).loc) ∧
  (∀ a, (a, a) ∉ W.mo) ∧
  (∀ p ∈ W.mo, ∀ q ∈ W.mo, p.2 = q.1 → (p.1, q.2) ∈ W.mo) ∧
  (∀ a b, (W.lab a).isW = true → (W.lab b).isW = true → (W.lab a).loc = (W.lab b).loc →
    a ≠ b → (a, b) ∈ W.mo ∨ (b, a) ∈ W.mo)

instance {n : Nat} {T V : Type} [DecidableEq V] (W : LG n T V) : Decidable W.Check :=
  haveI : Decidable (∀ e, ∃ i, (W.lab i).isIW = true ∧ (W.lab i).loc = (W.lab e).loc) :=
    inferInstance
  haveI : Decidable (∀ i j, (W.lab i).isIW = true → (W.lab j).isIW = true →
    (W.lab i).loc = (W.lab j).loc → i = j) := inferInstance
  haveI : Decidable (∀ w r, (w, r) ∈ W.rf → (W.lab w).isW = true ∧ (W.lab r).isR = true ∧
    (W.lab w).loc = (W.lab r).loc ∧ (W.lab w).val = (W.lab r).val) := inferInstance
  haveI : Decidable (∀ r, (W.lab r).isR = true → ∃ w, (w, r) ∈ W.rf) := inferInstance
  haveI : Decidable (∀ w w' r, (w, r) ∈ W.rf → (w', r) ∈ W.rf → w = w') := inferInstance
  haveI : Decidable (∀ a b, (a, b) ∈ W.mo → (W.lab a).isW = true ∧ (W.lab b).isW = true ∧
    (W.lab a).loc = (W.lab b).loc) := inferInstance
  haveI : Decidable (∀ a b, (W.lab a).isW = true → (W.lab b).isW = true →
    (W.lab a).loc = (W.lab b).loc → a ≠ b → (a, b) ∈ W.mo ∨ (b, a) ∈ W.mo) := inferInstance
  inferInstanceAs (Decidable (_ ∧ _))

/-- A list graph whose conditions are checked is a graph of the fragment. -/
theorem LG.frag {n : Nat} {T V : Type} [DecidableEq T] (W : LG n T V) (h : W.Check) :
    W.toGraph.Frag := by
  obtain ⟨h_init_exists, h_init_unique, h_ann, h_rf_type, h_rf_exists, h_rf_unique, h_mo_type,
    h_mo_irrefl, h_mo_trans, h_mo_total⟩ := h
  have iw_thread : ∀ e, (W.lab e).isIW = true → (W.lab e).thread? = none := fun e he => by
    cases hl : W.lab e with
    | init => rfl
    | read => rw [hl] at he; cases he
    | write => rw [hl] at he; cases he
  have thread_iw : ∀ e, (W.lab e).thread?.isSome = true → (W.lab e).isIW = false := fun e he => by
    cases hl : W.lab e with
    | init => rw [hl] at he; cases he
    | read => rfl
    | write => rfl
  have isIW_of : ∀ {e l v}, W.lab e = .init l v → (W.lab e).isIW = true := fun h => by rw [h]; rfl
  refine
    { init_exists := fun e => ?_, init_unique := fun i j l v v' hi hj => ?_,
      ann_read := fun e t l v a he => ?_, ann_write := fun e t l v a he => ?_,
      rmw_read := fun _ _ h => (nomatch h), rmw_write := fun _ _ h => (nomatch h),
      rmw_thread := fun _ _ h => (nomatch h), rmw_loc := fun _ _ h => (nomatch h),
      rmw_sb := fun _ _ h => (nomatch h), rmw_imm := fun _ _ _ h => (nomatch h),
      rmw_inj := fun _ _ _ h => (nomatch h), rmw_ann := fun _ _ _ _ h => (nomatch h),
      sb_irrefl := fun a ha => ?_, sb_trans := fun a b c h₁ h₂ => ?_,
      sb_thread := fun a b t hab ha => ?_, sb_not_init := fun a b hab hb => ?_,
      sb_total := fun a b t ha hb hne => ?_,
      rf_type := fun w r hr => h_rf_type w r hr, rf_exists := fun r hr => h_rf_exists r hr,
      rf_unique := fun w w' r h₁ h₂ => h_rf_unique w w' r h₁ h₂,
      mo_type := fun a b hm => h_mo_type a b hm, mo_irrefl := fun a hm => h_mo_irrefl a hm,
      mo_trans := fun a b c h₁ h₂ => h_mo_trans (a, b) h₁ (b, c) h₂ rfl,
      mo_total := fun a b ha hb hl hne => h_mo_total a b ha hb hl hne }
  · obtain ⟨i, hi, hl⟩ := h_init_exists e
    cases hli : W.lab i with
    | init l v =>
      rw [hli] at hl
      exact ⟨i, v, show W.lab i = _ by rw [hli]; exact congrArg (Lab.init · v) hl⟩
    | read => rw [hli] at hi; cases hi
    | write => rw [hli] at hi; cases hi
  · change W.lab i = _ at hi; change W.lab j = _ at hj
    exact h_init_unique i j (isIW_of hi) (isIW_of hj) (by rw [hi, hj]; rfl)
  · have := h_ann e; change W.lab e = _ at he; rw [he] at this
    cases a <;> simp [annOK] at this ⊢
  · have := h_ann e; change W.lab e = _ at he; rw [he] at this
    cases a <;> simp [annOK] at this ⊢
  · rcases ha with ⟨-, -, h⟩ | ⟨-, hi, ht⟩
    · exact Nat.lt_irrefl _ h
    · rw [thread_iw a ht] at hi; cases hi
  · rcases h₁ with ⟨hs, ht, hab⟩ | ⟨hf, hi, hs⟩ <;> rcases h₂ with ⟨hs', ht', hbc⟩ | ⟨hf', hi', hs'⟩
    · exact .inl ⟨hs, ht.trans ht', Nat.lt_trans hab hbc⟩
    · rw [thread_iw b (ht ▸ hs)] at hi'; cases hi'
    · exact .inr ⟨hf, hi, ht' ▸ hs'⟩
    · rw [thread_iw b hs] at hi'; cases hi'
  · rcases hab with ⟨-, ht, -⟩ | ⟨-, hi, -⟩
    · exact ht ▸ ha
    · change (W.lab a).thread? = some t at ha
      rw [iw_thread a hi] at ha; cases ha
  · change (W.lab b).isIW = true at hb
    rcases hab with ⟨hs, ht, -⟩ | ⟨-, -, hs⟩
    · rw [thread_iw b (ht ▸ hs)] at hb; cases hb
    · rw [thread_iw b hs] at hb; cases hb
  · change (W.lab a).thread? = some t at ha
    change (W.lab b).thread? = some t at hb
    have hs : (W.lab a).thread?.isSome = true := by rw [ha]; rfl
    have hab : (W.lab a).thread? = (W.lab b).thread? := ha.trans hb.symm
    rcases Nat.lt_or_ge a b with h | h
    · exact .inl (.inl ⟨hs, hab, h⟩)
    · exact .inr (.inl ⟨hab ▸ hs, hab.symm, Nat.lt_of_le_of_ne h fun e => hne (Fin.ext e.symm)⟩)

/-! ## The witness of (a) -/

/-- `Ga`, the example of the corrigendum with its non-atomic read removed. Thread 0: `R(x)=2`
`ACQ`, which reads `W(x,2)`; `R(y)=0` `SC`, which reads the initial write. Thread 1: `W(x,1)`
`SC`; `W(x,2)` `SC`. Thread 2: `W(y,1)` `SC`; `R(x)=0` `SC`, which reads the initial write.
`mo`: initial `< W(x,1) < W(x,2)`; initial `< W(y,1)`. Locations: `x = 0`, `y = 1`. -/
def Ga (fromInit : Bool) : LG 8 (Fin 3) Nat where
  lab
    | 0 => .init 0 0
    | 1 => .init 1 0
    | 2 => .read 0 0 2 .acq
    | 3 => .read 0 1 0 .sc
    | 4 => .write 1 0 1 .sc
    | 5 => .write 1 0 2 .sc
    | 6 => .write 2 1 1 .sc
    | 7 => .read 2 0 0 .sc
  rf := [(5, 2), (1, 3), (0, 7)]
  mo := [(0, 4), (0, 5), (4, 5), (1, 6)]
  fromInit := fromInit

/-- The conditions of the fragment hold on `Ga`. -/
theorem ga_check (f : Bool) : (Ga f).Check := by cases f <;> decide +kernel

/-- `Ga` is a graph of the fragment. -/
theorem ga_frag (f : Bool) : (Ga f).toGraph.Frag := (Ga f).frag (ga_check f)

/-- **(a)**, RC11 side (C34: "Inclusion of executions consistent with the **published** `rc11.cat`
model is **not** an expected comparison property"): `Ga` is consistent for the published
`rc11.cat` and inconsistent for RC11 amended, by its check `SC` alone. -/
theorem ga_rc11 (f : Bool) : (Ga f).toGraph.ConsistentPub ∧ ¬ (Ga f).toGraph.ConsistentAm ∧
    ¬ (Ga f).toGraph.SCCheck (Ga f).toGraph.scbAm := by
  cases f <;> decide +kernel

/-- **(a)**, ERN side: the projection of `Ga` is rejected by conjunct 7 alone: conjuncts 1 to 6
hold, `SCConsistent` fails (the middle term `po ; hb ; po` from `W(x,1)` to `R(y)=0`, through the
`sw` edge from `W(x,2)` to `R(x)=2`, closes a `psc` cycle). -/
theorem ga_proj (f : Bool) :
    ((Ga f).toGraph.proj (ga_frag f)).RfWF ∧ ((Ga f).toGraph.proj (ga_frag f)).MoTotal ∧
    ((Ga f).toGraph.proj (ga_frag f)).RmwAtomic ∧ ((Ga f).toGraph.proj (ga_frag f)).Coherence ∧
    ((Ga f).toGraph.proj (ga_frag f)).HbIrrefl ∧ ((Ga f).toGraph.proj (ga_frag f)).NoThinAir ∧
    ¬ ((Ga f).toGraph.proj (ga_frag f)).SCConsistent := by
  cases f <;> refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-! ## The witness of (c) -/

/-- `Gc`. Thread 0: `W(d,1)` `RLX`; `W(f,1)` `REL`; `W(f,2)` `RLX`. Thread 1: `R(f)=2` `ACQ`, which
reads `W(f,2)`; `R(d)=0` `RLX`, which reads the initial write. `mo`: initial `< W(d,1)`; initial
`< W(f,1) < W(f,2)`. Locations: `d = 0`, `f = 1`. -/
def Gc (fromInit : Bool) : LG 7 (Fin 2) Nat where
  lab
    | 0 => .init 0 0
    | 1 => .init 1 0
    | 2 => .write 0 0 1 .rlx
    | 3 => .write 0 1 1 .rel
    | 4 => .write 0 1 2 .rlx
    | 5 => .read 1 1 2 .acq
    | 6 => .read 1 0 0 .rlx
  rf := [(4, 5), (0, 6)]
  mo := [(0, 2), (1, 3), (1, 4), (3, 4)]
  fromInit := fromInit

/-- The conditions of the fragment hold on `Gc`. -/
theorem gc_check (f : Bool) : (Gc f).Check := by cases f <;> decide +kernel

/-- `Gc` is a graph of the fragment. -/
theorem gc_frag (f : Bool) : (Gc f).toGraph.Frag := (Gc f).frag (gc_check f)

/-- **(c)**, RC11 side: `Gc` is inconsistent for RC11 in both forms, by its check `coherence1`
(the release sequence of `rs` takes in the `relaxed` write of the same thread through
`(sb & loc)?`); the other checks pass. -/
theorem gc_rc11 (f : Bool) : ¬ (Gc f).toGraph.Coherence1 ∧ (Gc f).toGraph.CoherenceRmw ∧
    (Gc f).toGraph.Atomicity ∧ (Gc f).toGraph.SCCheck (Gc f).toGraph.scbPub ∧
    (Gc f).toGraph.SCCheck (Gc f).toGraph.scbAm ∧ (Gc f).toGraph.NoThinAir ∧
    ¬ (Gc f).toGraph.ConsistentPub ∧ ¬ (Gc f).toGraph.ConsistentAm := by
  cases f <;> decide +kernel

/-- **(c)**, ERN side: the projection of `Gc` satisfies `EventConsistent` (C48: "Ordinary atomic
stores, including same-thread non-RMW stores, do **not** extend the sequence"). -/
theorem gc_proj (f : Bool) : ((Gc f).toGraph.proj (gc_frag f)).EventConsistent := by
  cases f <;> decide +kernel

/-! ## A graph with a pair, for (b) -/

/-- The labels and the `rf`, `mo` edges of `Gp`. Locations: `f = 0`, `d = 1`. Thread 0: `W(d,1)`
`RLX` (event 2), then `W(f,1)` `REL` (3). Thread 1: the pair `R(f)=1` `ACQ` (4) / `W(f,2)` `REL`
(5). Thread 2: `R(f)=2` `ACQ` (6), then `R(d)=1` `RLX` (7). `rf`: `W(f,1)` to the read of the
pair, the write of the pair to `R(f)=2`, `W(d,1)` to `R(d)=1`. `mo`: on `f`, initial, `W(f,1)`, the
write of the pair; on `d`, initial, `W(d,1)`. No `sb` edge from the initial writes. -/
def Wp : LG 8 (Fin 3) Nat where
  lab
    | 0 => .init 0 0
    | 1 => .init 1 0
    | 2 => .write 0 1 1 .rlx
    | 3 => .write 0 0 1 .rel
    | 4 => .read 1 0 1 .acq
    | 5 => .write 1 0 2 .rel
    | 6 => .read 2 0 2 .acq
    | 7 => .read 2 1 1 .rlx
  rf := [(3, 4), (5, 6), (2, 7)]
  mo := [(0, 3), (0, 5), (3, 5), (1, 2)]
  fromInit := false

/-- `Gp`: `Wp` with the single pair `(4, 5)` of `rmw`, of row `acq/rel`. -/
def Gp : Graph (Fin 8) (Fin 3) Nat :=
  { Wp.toGraph with partner := fun e => if e = 4 then some 5 else none }

instance : DecidableRel Gp.sb := fun a b => inferInstanceAs (Decidable (Wp.toGraph.sb a b))
instance : DecidableRel Gp.rf := fun a b => inferInstanceAs (Decidable (Wp.toGraph.rf a b))
instance : DecidableRel Gp.mo := fun a b => inferInstanceAs (Decidable (Wp.toGraph.mo a b))

/-- The only pair of `Gp` is `(4, 5)`. -/
theorem gp_rmw_only : ∀ r w : Fin 8, Gp.rmw r w → r = 4 ∧ w = 5 := by decide +kernel

/-- **`Gp`, fact 1**: `Gp` is a graph of the fragment, its pair conditions included. -/
theorem gp_frag : Gp.Frag :=
  { (Wp.frag (by decide +kernel)) with
    rmw_read := by decide +kernel
    rmw_write := by decide +kernel
    rmw_thread := by decide +kernel
    rmw_loc := by decide +kernel
    rmw_sb := by decide +kernel
    rmw_imm := by decide +kernel
    rmw_inj := by decide +kernel
    rmw_ann := by
      intro r w a a' h ha hw
      obtain ⟨rfl, rfl⟩ := gp_rmw_only r w h
      simp [Gp, Wp, LG.toGraph, Lab.ann?] at ha hw
      subst ha hw; trivial }

/-- **`Gp`, fact 2**: `Gp` is consistent for RC11, amended and published. -/
theorem gp_rc11 : Gp.ConsistentAm ∧ Gp.ConsistentPub := ⟨by decide +kernel, by decide +kernel⟩

/-- **`Gp`, fact 3**: `dr` is empty on `Gp` (`dr_empty`). -/
theorem gp_dr : ∀ a b, ¬ Gp.dr a b := Gp.dr_empty

/-- **`Gp`, fact 4**: the write component of the pair has no image, and the image of the pair is a
single atomic RMW of the unit `f`, of order `acq_rel`, which reads `1` and writes `2`. -/
theorem gp_pair_image : Gp.IsPairW 5 ∧
    (Gp.proj gp_frag).acc? ⟨4, by decide⟩ = some (.atomic 0 .acqRel (.rmw 1 2)) :=
  ⟨⟨4, rfl⟩, by decide +kernel⟩

/-- **`Gp`, fact 5**: the projection of `Gp` satisfies `EventConsistent`, and its `sw` is exactly:
`W(f,1)` to the RMW, the RMW to `R(f)=2`, and `W(f,1)` to `R(f)=2` (the RMW is a member of the
release sequence of `W(f,1)`, retained reading 5). -/
theorem gp_proj : (Gp.proj gp_frag).EventConsistent ∧
    ∀ a b, (Gp.proj gp_frag).SW a b ↔
      (a.1 = 3 ∧ b.1 = 4) ∨ (a.1 = 4 ∧ b.1 = 6) ∨ (a.1 = 3 ∧ b.1 = 6) :=
  ⟨by decide +kernel, by decide +kernel⟩

/-- **`Gp`, fact 6**: `Gp` satisfies the hypotheses of (b) (the fragment, finiteness, consistency
for RC11 amended), and (b) applies to it (`proj_consistent`). -/
theorem gp_b : (Gp.Frag ∧ Events.Finite (Fin 8) ∧ Gp.ConsistentAm) ∧
    (Gp.proj gp_frag).EventConsistent :=
  ⟨⟨gp_frag, ⟨List.finRange 8, List.mem_finRange⟩, gp_rc11.1⟩,
    Graph.proj_consistent gp_frag ⟨List.finRange 8, List.mem_finRange⟩ gp_rc11.1⟩

/-! ## The rejected twin of `Gp` -/

/-- The labels of the twin `Gpt`: `Gp` where the last read of thread 2 returns `0` and reads the
initial write of `d`. -/
def Wpt : LG 8 (Fin 3) Nat :=
  { Wp with
    lab := fun e => if e = 7 then .read 2 1 0 .rlx else Wp.lab e
    rf := [(3, 4), (5, 6), (1, 7)] }

/-- `Gpt`: `Wpt` with the pair `(4, 5)`. -/
def Gpt : Graph (Fin 8) (Fin 3) Nat :=
  { Wpt.toGraph with partner := fun e => if e = 4 then some 5 else none }

instance : DecidableRel Gpt.sb := fun a b => inferInstanceAs (Decidable (Wpt.toGraph.sb a b))
instance : DecidableRel Gpt.rf := fun a b => inferInstanceAs (Decidable (Wpt.toGraph.rf a b))
instance : DecidableRel Gpt.mo := fun a b => inferInstanceAs (Decidable (Wpt.toGraph.mo a b))

/-- The only pair of `Gpt` is `(4, 5)`. -/
theorem gpt_rmw_only : ∀ r w : Fin 8, Gpt.rmw r w → r = 4 ∧ w = 5 := by decide +kernel

/-- `Gpt` is a graph of the fragment. -/
theorem gpt_frag : Gpt.Frag :=
  { (Wpt.frag (by decide +kernel)) with
    rmw_read := by decide +kernel
    rmw_write := by decide +kernel
    rmw_thread := by decide +kernel
    rmw_loc := by decide +kernel
    rmw_sb := by decide +kernel
    rmw_imm := by decide +kernel
    rmw_inj := by decide +kernel
    rmw_ann := by
      intro r w a a' h ha hw
      obtain ⟨rfl, rfl⟩ := gpt_rmw_only r w h
      simp [Gpt, Wpt, Wp, LG.toGraph, Lab.ann?] at ha hw
      subst ha hw; trivial }

/-- **Twin of `Gp`** (C34, C48): `Gpt` is inconsistent for RC11 in both forms, by `coherence1`
(the write of `d` is `hb`-before the read of thread 2 through the `sw` edge of the release sequence,
and the read reads an earlier modification). -/
theorem gpt_rc11 : ¬ Gpt.Coherence1 ∧ ¬ Gpt.ConsistentAm ∧ ¬ Gpt.ConsistentPub :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- **Twin of `Gp`**: the projection of `Gpt` is rejected by conjunct 4 alone. -/
theorem gpt_proj :
    (Gpt.proj gpt_frag).RfWF ∧ (Gpt.proj gpt_frag).MoTotal ∧ (Gpt.proj gpt_frag).RmwAtomic ∧
    ¬ (Gpt.proj gpt_frag).Coherence ∧ (Gpt.proj gpt_frag).HbIrrefl ∧
    (Gpt.proj gpt_frag).NoThinAir ∧ (Gpt.proj gpt_frag).SCConsistent := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

end Ern.ConcurrencyModel.Rc11
