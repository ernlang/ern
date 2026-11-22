import Ern.ConcurrencyModel.EventErasure

/-!
# Theorem 10d: witness graphs and non-vacuity (C30–C34, C48; `OB-C26`)

Witness graphs T1 to T14, each with its admitted twin; T15, a non-atomic RMW that conjunct 3 does
not constrain, with its atomic twin (C34.3); and the two witnesses of 10a on conflicts.
A witness replaces no general proof. Each verdict is computed on the definitions of C34 by
evaluation (`decide +kernel`, through `EventDecide`); the expected verdicts are drawn from the
clauses (C30–C34, C48).

In every witness, context `0` makes the initial writes (non-atomic, designating their unit, value
`0`), then creates the other contexts: the `spawn(c)` to `start(c)` edges are present, and no
witness has a race in the sense of C33 (`noRace_*`). Notation: `W_o(x, v)` an atomic write of order
`o`, `R_o(x) = v` an atomic read, `U_o(x: v → v')` an atomic RMW, `ix` the initial write of `x`.
Events are numbered in the order given; `po` is that order within each context. Each atomic unit
covers its own 8 bytes.

Non-vacuity of the conjuncts (`OB-C26`): T1 satisfies the seven conjuncts together, each exercised
(`rf`, `mo`, an RMW, `hb` edges across contexts, `seq_cst` events); T2 to T7 are rejected by each of
the conjuncts 1, 2, 3, 4, 6, 7 alone. No graph is rejected by conjunct 5 alone, since conjunct 4
entails it (`hbIrrefl_of_coherence`); T8 is a graph that conjunct 5 rejects.

The `sw` edges of the witnesses go through `RSMember`, retained reading 5 (a formalization
hypothesis); on these finite graphs it coincides with the reading by `rf` chains
(`rsMember_iff_chain`), so no verdict depends on it.

The erasures of T1, T13 and T14 are obtained through the equivalences of 10c, whose premises
(no pure authority marker is an endpoint of `rf` or `mo`) are checked on each.
-/

namespace Ern.ConcurrencyModel.Events

namespace Witness

open Ern.ConcurrencyModel (MemOrder)

/-- Events with `k + 1` contexts and `u` units. -/
abbrev Ev (k u : Nat) := Event (Fin (k + 1)) (Fin u) Nat Unit

variable {k u : Nat}

/-- The initial write of a unit, non-atomic, designating it, value `0` (C31). -/
def ini (c : Fin (k + 1)) (x : Fin u) : Ev k u := ⟨c, ⟨0, 0⟩, .marks (some (.unit x (.write 0))) none⟩
/-- `W_o(x, v)`. -/
def wr (c : Fin (k + 1)) (x : Fin u) (o : MemOrder) (v : Nat) : Ev k u :=
  ⟨c, ⟨0, 0⟩, .marks (some (.atomic x o (.write v))) none⟩
/-- `R_o(x) = v`. -/
def rd (c : Fin (k + 1)) (x : Fin u) (o : MemOrder) (v : Nat) : Ev k u :=
  ⟨c, ⟨0, 0⟩, .marks (some (.atomic x o (.read v))) none⟩
/-- `U_o(x: a → b)`. -/
def up (c : Fin (k + 1)) (x : Fin u) (o : MemOrder) (a b : Nat) : Ev k u :=
  ⟨c, ⟨0, 0⟩, .marks (some (.atomic x o (.rmw a b))) none⟩
/-- A `sync` event of role `r`. -/
def sy (c : Fin (k + 1)) (r : SyncRole (Fin (k + 1))) : Ev k u := ⟨c, ⟨0, 0⟩, .marks none (some r)⟩
/-- A pure authority marker. -/
def mk (c : Fin (k + 1)) : Ev k u := ⟨c, ⟨0, 0⟩, .marks none none⟩

/-- A witness graph from the list of its events and of its `rf` and `mo` edges. -/
def lg (n : Nat) (evs : List (Ev k u)) (rf mo : List (Fin n × Fin n)) :
    ListGraph n (Fin (k + 1)) (Fin u) Nat Unit where
  ev i := evs.getD i.val (mk 0)
  uRange x := ⟨x.val * 8, 8⟩
  rf := rf
  mo := mo

instance {E C U V S : Type} [Enum E] [DecidableEq C] [DecidableEq U] [DecidableEq V]
    [DecidableEq S] (G : Graph E C U V S) [DecidableRel G.rf] : Decidable G.RfAvoidsPure := by
  unfold Graph.RfAvoidsPure; infer_instance

instance {E C U V S : Type} [Enum E] [DecidableEq C] [DecidableEq U] [DecidableEq V]
    [DecidableEq S] (G : Graph E C U V S) [DecidableRel G.mo] : Decidable G.MoAvoidsPure := by
  unfold Graph.MoAvoidsPure; infer_instance

/-- The status of each of the seven conjuncts of `EventConsistent`, in the order of C34: a graph
"rejected by conjunct `k` alone" has `false` at `k` and `true` elsewhere. -/
abbrev Verdict {E C U V S : Type} (G : Graph E C U V S) (c1 c2 c3 c4 c5 c6 c7 : Bool) : Prop :=
  (G.RfWF ↔ c1 = true) ∧ (G.MoTotal ↔ c2 = true) ∧ (G.RmwAtomic ↔ c3 = true) ∧
    (G.Coherence ↔ c4 = true) ∧ (G.HbIrrefl ↔ c5 = true) ∧ (G.NoThinAir ↔ c6 = true) ∧
    (G.SCConsistent ↔ c7 = true)

/-! ## T1: the seven conjuncts together -/

/-- T1. c0: `ix`, `il`, spawns, `join(c1)`. c1: `start`, `W_sc(x,1)`, a pure authority marker,
`W_rel(l,1)`, `complete(c1)`. c2: `start`, `U_acq_rel(l: 1→2)`, `R_sc(x)=1`. c3: `start`,
`R_acq(l)=2`, `R_sc(x)=1`. `mo`: `ix < W_sc(x,1)`; `il < W_rel(l,1) < U`. -/
def T1 : ListGraph 17 (Fin 4) (Fin 2) Nat Unit := lg 17
  [ini 0 0, ini 0 1, sy 0 (.spawn 1), sy 0 (.spawn 2), sy 0 (.spawn 3), sy 0 (.join 1),
   sy 1 (.start 1), wr 1 0 .seqCst 1, mk 1, wr 1 1 .release 1, sy 1 (.complete 1),
   sy 2 (.start 2), up 2 1 .acqRel 1 2, rd 2 0 .seqCst 1,
   sy 3 (.start 3), rd 3 1 .acquire 2, rd 3 0 .seqCst 1]
  [(9, 12), (7, 13), (12, 15), (7, 16)]
  [(0, 7), (1, 9), (9, 12), (1, 12)]

/-- **T1** (C34, C48): the seven conjuncts hold. -/
theorem t1_consistent : T1.toGraph.EventConsistent := by decide +kernel

/-- **T1** (C32, C48): the atomic `sw` edges announced: `W_rel(l,1)` to `U`, `U` to `R_acq(l)`,
`W_rel(l,1)` to `R_acq(l)` through the release sequence (`U` is a member), and `W_sc(x,1)` to the
two reads of `x`; the lifecycle edges. -/
theorem t1_sw : T1.toGraph.SW 9 12 ∧ T1.toGraph.SW 12 15 ∧ T1.toGraph.SW 9 15 ∧
    T1.toGraph.RSMember 1 9 12 ∧ T1.toGraph.SW 7 13 ∧ T1.toGraph.SW 7 16 ∧
    T1.toGraph.SW 2 6 ∧ T1.toGraph.SW 3 11 ∧ T1.toGraph.SW 4 14 ∧ T1.toGraph.SW 10 5 := by
  decide +kernel

/-- **T1**: each conjunct is exercised: `rf` and `mo` edges, an RMW, `hb` edges across contexts,
`seq_cst` events related by `psc`. -/
theorem t1_exercised : T1.toGraph.rf 9 12 ∧ T1.toGraph.mo 9 12 ∧ T1.toGraph.IsRMW 12 ∧
    T1.toGraph.HB 0 16 ∧ T1.toGraph.PSC 7 13 := by decide +kernel

/-- **T1** (C33): no pair of events is in a race. -/
theorem noRace_t1 : ∀ a b, ¬ T1.toGraph.Race a b := by decide +kernel

/-- **T1, erased** (C34, 10c): the erasure of T1 is admitted. -/
theorem t1_erased_consistent : T1.toGraph.erasePure.EventConsistent :=
  (Graph.erasePure_consistent_iff (by decide +kernel) (by decide +kernel)).2 t1_consistent

/-! ## T2: conjunct 1 alone -/

/-- T2. c1: `W_rlx(x,1)`. c2: `R_rlx(x)=1`, with no `rf` source. -/
def T2 : ListGraph 7 (Fin 3) (Fin 1) Nat Unit := lg 7
  [ini 0 0, sy 0 (.spawn 1), sy 0 (.spawn 2), sy 1 (.start 1), wr 1 0 .relaxed 1,
   sy 2 (.start 2), rd 2 0 .relaxed 1]
  [] [(0, 4)]

/-- **T2** (C34.1): rejected by conjunct 1 alone. -/
theorem t2_verdict : Verdict T2.toGraph false true true true true true true := by decide +kernel
/-- **T2** (C33): no pair of events is in a race. -/
theorem noRace_t2 : ∀ a b, ¬ T2.toGraph.Race a b := by decide +kernel

/-- Twin of T2: the read has `W_rlx(x,1)` as source. -/
def T2t : ListGraph 7 (Fin 3) (Fin 1) Nat Unit := { T2 with rf := [(4, 6)] }
/-- **Twin of T2** (C34): admitted. -/
theorem t2t_consistent : T2t.toGraph.EventConsistent := by decide +kernel
/-- **Twin of T2** (C33): no pair of events is in a race. -/
theorem noRace_t2t : ∀ a b, ¬ T2t.toGraph.Race a b := by decide +kernel

/-! ## T3: conjunct 2 alone -/

/-- T3. c1: `W_rlx(x,1)`. c2: `W_rlx(x,2)`, absent from `mo`. -/
def T3 : ListGraph 7 (Fin 3) (Fin 1) Nat Unit := lg 7
  [ini 0 0, sy 0 (.spawn 1), sy 0 (.spawn 2), sy 1 (.start 1), wr 1 0 .relaxed 1,
   sy 2 (.start 2), wr 2 0 .relaxed 2]
  [] [(0, 4)]

/-- **T3** (C34.2): rejected by conjunct 2 alone. -/
theorem t3_verdict : Verdict T3.toGraph true false true true true true true := by decide +kernel
/-- **T3** (C33): no pair of events is in a race. -/
theorem noRace_t3 : ∀ a b, ¬ T3.toGraph.Race a b := by decide +kernel

/-- Twin of T3: `W_rlx(x,2)` is in `mo`. -/
def T3t : ListGraph 7 (Fin 3) (Fin 1) Nat Unit := { T3 with mo := [(0, 4), (0, 6), (4, 6)] }
/-- **Twin of T3** (C34): admitted. -/
theorem t3t_consistent : T3t.toGraph.EventConsistent := by decide +kernel
/-- **Twin of T3** (C33): no pair of events is in a race. -/
theorem noRace_t3t : ∀ a b, ¬ T3t.toGraph.Race a b := by decide +kernel

/-! ## T4: conjunct 3 alone -/

/-- T4. c1: `U_rlx(x: 0→1)`. c2: `U_rlx(x: 0→1)`. Both read `ix`; `mo`: `ix < U(c1) < U(c2)`. -/
def T4 : ListGraph 7 (Fin 3) (Fin 1) Nat Unit := lg 7
  [ini 0 0, sy 0 (.spawn 1), sy 0 (.spawn 2), sy 1 (.start 1), up 1 0 .relaxed 0 1,
   sy 2 (.start 2), up 2 0 .relaxed 0 1]
  [(0, 4), (0, 6)] [(0, 4), (0, 6), (4, 6)]

/-- **T4** (C34.3): rejected by conjunct 3 alone. -/
theorem t4_verdict : Verdict T4.toGraph true true false true true true true := by decide +kernel
/-- **T4** (C33): no pair of events is in a race. -/
theorem noRace_t4 : ∀ a b, ¬ T4.toGraph.Race a b := by decide +kernel

/-- Twin of T4: the second RMW reads the first (`1 → 2`). -/
def T4t : ListGraph 7 (Fin 3) (Fin 1) Nat Unit := lg 7
  [ini 0 0, sy 0 (.spawn 1), sy 0 (.spawn 2), sy 1 (.start 1), up 1 0 .relaxed 0 1,
   sy 2 (.start 2), up 2 0 .relaxed 1 2]
  [(0, 4), (4, 6)] [(0, 4), (0, 6), (4, 6)]
/-- **Twin of T4** (C34): admitted. -/
theorem t4t_consistent : T4t.toGraph.EventConsistent := by decide +kernel
/-- **Twin of T4** (C33): no pair of events is in a race. -/
theorem noRace_t4t : ∀ a b, ¬ T4t.toGraph.Race a b := by decide +kernel

/-! ## T5: conjunct 4 alone -/

/-- T5. c1: `W_rlx(d,1)`, `W_rel(f,1)`. c2: `R_acq(f)=1`, `R_rlx(d)=0` reading `id`. -/
def T5 : ListGraph 10 (Fin 3) (Fin 2) Nat Unit := lg 10
  [ini 0 0, ini 0 1, sy 0 (.spawn 1), sy 0 (.spawn 2), sy 1 (.start 1), wr 1 0 .relaxed 1,
   wr 1 1 .release 1, sy 2 (.start 2), rd 2 1 .acquire 1, rd 2 0 .relaxed 0]
  [(6, 8), (0, 9)] [(0, 5), (1, 6)]

/-- **T5** (C34.4): rejected by conjunct 4 alone. -/
theorem t5_verdict : Verdict T5.toGraph true true true false true true true := by decide +kernel
/-- **T5** (C33): no pair of events is in a race. -/
theorem noRace_t5 : ∀ a b, ¬ T5.toGraph.Race a b := by decide +kernel

/-- Twin of T5: the last read returns `1` and reads `W_rlx(d,1)`. -/
def T5t : ListGraph 10 (Fin 3) (Fin 2) Nat Unit := lg 10
  [ini 0 0, ini 0 1, sy 0 (.spawn 1), sy 0 (.spawn 2), sy 1 (.start 1), wr 1 0 .relaxed 1,
   wr 1 1 .release 1, sy 2 (.start 2), rd 2 1 .acquire 1, rd 2 0 .relaxed 1]
  [(6, 8), (5, 9)] [(0, 5), (1, 6)]
/-- **Twin of T5** (C34): admitted. -/
theorem t5t_consistent : T5t.toGraph.EventConsistent := by decide +kernel
/-- **Twin of T5** (C33): no pair of events is in a race. -/
theorem noRace_t5t : ∀ a b, ¬ T5t.toGraph.Race a b := by decide +kernel

/-! ## T6: conjunct 6 alone -/

/-- T6. c1: `R_rlx(x)=1`, `W_rlx(y,1)`. c2: `R_rlx(y)=1`, `W_rlx(x,1)`. -/
def T6 : ListGraph 10 (Fin 3) (Fin 2) Nat Unit := lg 10
  [ini 0 0, ini 0 1, sy 0 (.spawn 1), sy 0 (.spawn 2), sy 1 (.start 1), rd 1 0 .relaxed 1,
   wr 1 1 .relaxed 1, sy 2 (.start 2), rd 2 1 .relaxed 1, wr 2 0 .relaxed 1]
  [(9, 5), (6, 8)] [(0, 9), (1, 6)]

/-- **T6** (C34.6): rejected by conjunct 6 alone. -/
theorem t6_verdict : Verdict T6.toGraph true true true true true false true := by decide +kernel
/-- **T6** (C33): no pair of events is in a race. -/
theorem noRace_t6 : ∀ a b, ¬ T6.toGraph.Race a b := by decide +kernel

/-- Twin of T6: both reads return `0` and read the initial writes. -/
def T6t : ListGraph 10 (Fin 3) (Fin 2) Nat Unit := lg 10
  [ini 0 0, ini 0 1, sy 0 (.spawn 1), sy 0 (.spawn 2), sy 1 (.start 1), rd 1 0 .relaxed 0,
   wr 1 1 .relaxed 1, sy 2 (.start 2), rd 2 1 .relaxed 0, wr 2 0 .relaxed 1]
  [(0, 5), (1, 8)] [(0, 9), (1, 6)]
/-- **Twin of T6** (C34): admitted. -/
theorem t6t_consistent : T6t.toGraph.EventConsistent := by decide +kernel
/-- **Twin of T6** (C33): no pair of events is in a race. -/
theorem noRace_t6t : ∀ a b, ¬ T6t.toGraph.Race a b := by decide +kernel

/-! ## T7: conjunct 7 alone -/

/-- T7. c1: `W_sc(x,1)`, `R_sc(y)=0`. c2: `W_sc(y,1)`, `R_sc(x)=0`. -/
def T7 : ListGraph 10 (Fin 3) (Fin 2) Nat Unit := lg 10
  [ini 0 0, ini 0 1, sy 0 (.spawn 1), sy 0 (.spawn 2), sy 1 (.start 1), wr 1 0 .seqCst 1,
   rd 1 1 .seqCst 0, sy 2 (.start 2), wr 2 1 .seqCst 1, rd 2 0 .seqCst 0]
  [(1, 6), (0, 9)] [(0, 5), (1, 8)]

/-- **T7** (C34.7): rejected by conjunct 7 alone. -/
theorem t7_verdict : Verdict T7.toGraph true true true true true true false := by decide +kernel
/-- **T7** (C33): no pair of events is in a race. -/
theorem noRace_t7 : ∀ a b, ¬ T7.toGraph.Race a b := by decide +kernel

/-- Twin of T7: the read of `x` returns `1` and reads `W_sc(x,1)`. -/
def T7t : ListGraph 10 (Fin 3) (Fin 2) Nat Unit := lg 10
  [ini 0 0, ini 0 1, sy 0 (.spawn 1), sy 0 (.spawn 2), sy 1 (.start 1), wr 1 0 .seqCst 1,
   rd 1 1 .seqCst 0, sy 2 (.start 2), wr 2 1 .seqCst 1, rd 2 0 .seqCst 1]
  [(1, 6), (5, 9)] [(0, 5), (1, 8)]
/-- **Twin of T7** (C34): admitted. -/
theorem t7t_consistent : T7t.toGraph.EventConsistent := by decide +kernel
/-- **Twin of T7** (C33): no pair of events is in a race. -/
theorem noRace_t7t : ∀ a b, ¬ T7t.toGraph.Race a b := by decide +kernel

/-! ## T8: conjunct 5 -/

/-- T8. c1: `R_acq(x)=1`, `W_rel(y,1)`. c2: `R_acq(y)=1`, `W_rel(x,1)`. -/
def T8 : ListGraph 10 (Fin 3) (Fin 2) Nat Unit := lg 10
  [ini 0 0, ini 0 1, sy 0 (.spawn 1), sy 0 (.spawn 2), sy 1 (.start 1), rd 1 0 .acquire 1,
   wr 1 1 .release 1, sy 2 (.start 2), rd 2 1 .acquire 1, wr 2 0 .release 1]
  [(9, 5), (6, 8)] [(0, 9), (1, 6)]

/-- **T8** (C33, C34.5): conjuncts 4, 5 and 6 are false, `hb` having a cycle; the others hold. -/
theorem t8_verdict : Verdict T8.toGraph true true true false false false true := by decide +kernel
/-- **T8** (C33): `hb` has a cycle through `R_acq(x)=1`. -/
theorem t8_hb_cycle : T8.toGraph.HB 5 5 := by decide +kernel
/-- **T8** (C33): no pair of events is in a race. -/
theorem noRace_t8 : ∀ a b, ¬ T8.toGraph.Race a b := by decide +kernel

/-- Twin of T8: both reads return `0` and read the initial writes. -/
def T8t : ListGraph 10 (Fin 3) (Fin 2) Nat Unit := lg 10
  [ini 0 0, ini 0 1, sy 0 (.spawn 1), sy 0 (.spawn 2), sy 1 (.start 1), rd 1 0 .acquire 0,
   wr 1 1 .release 1, sy 2 (.start 2), rd 2 1 .acquire 0, wr 2 0 .release 1]
  [(0, 5), (1, 8)] [(0, 9), (1, 6)]
/-- **Twin of T8** (C34): admitted. -/
theorem t8t_consistent : T8t.toGraph.EventConsistent := by decide +kernel
/-- **Twin of T8** (C33): no pair of events is in a race. -/
theorem noRace_t8t : ∀ a b, ¬ T8t.toGraph.Race a b := by decide +kernel

/-! ## T9 and T10: the release sequence (C48) -/

/-- T9. c1: `W_rlx(d,1)`, `W_rel(f,1)`, `W_rlx(f,2)`. c2: `R_acq(f)=2`, `R_rlx(d)=0`. -/
def T9 : ListGraph 11 (Fin 3) (Fin 2) Nat Unit := lg 11
  [ini 0 0, ini 0 1, sy 0 (.spawn 1), sy 0 (.spawn 2), sy 1 (.start 1), wr 1 0 .relaxed 1,
   wr 1 1 .release 1, wr 1 1 .relaxed 2, sy 2 (.start 2), rd 2 1 .acquire 2, rd 2 0 .relaxed 0]
  [(7, 9), (0, 10)] [(0, 5), (1, 6), (1, 7), (6, 7)]

/-- **T9** (C48: "Ordinary atomic stores, including same-thread non-RMW stores, do **not** extend
the sequence"): admitted; no `sw` edge leaves `W_rel(f,1)`. T9 is the admitted twin of T10. -/
theorem t9_consistent : T9.toGraph.EventConsistent := by decide +kernel
/-- **T9** (C48): no `sw` edge leaves `W_rel(f,1)`: `W_rlx(f,2)` is not a member of its release
sequence (retained reading 5). -/
theorem t9_no_sw : ∀ b, ¬ T9.toGraph.SW 6 b := by decide +kernel
/-- **T9** (C33): no pair of events is in a race. -/
theorem noRace_t9 : ∀ a b, ¬ T9.toGraph.Race a b := by decide +kernel

/-- T10. c1: `W_rlx(d,1)`, `W_rel(f,1)`. c2: `U_rlx(f: 1→2)`. c3: `R_acq(f)=2` reading the RMW,
`R_rlx(d)=0`. -/
def T10 : ListGraph 13 (Fin 4) (Fin 2) Nat Unit := lg 13
  [ini 0 0, ini 0 1, sy 0 (.spawn 1), sy 0 (.spawn 2), sy 0 (.spawn 3), sy 1 (.start 1),
   wr 1 0 .relaxed 1, wr 1 1 .release 1, sy 2 (.start 2), up 2 1 .relaxed 1 2, sy 3 (.start 3),
   rd 3 1 .acquire 2, rd 3 0 .relaxed 0]
  [(7, 9), (9, 11), (0, 12)] [(0, 6), (1, 7), (1, 9), (7, 9)]

/-- **T10** (C48): rejected by conjunct 4 alone; the RMW extends the sequence, and `sw` relates
`W_rel(f,1)` to the read. -/
theorem t10_verdict : Verdict T10.toGraph true true true false true true true := by decide +kernel
/-- **T10** (C32.1, C48): `sw` relates `W_rel(f,1)` to `R_acq(f)=2`, the RMW being a member of its
release sequence (retained reading 5). -/
theorem t10_sw : T10.toGraph.SW 7 11 := by decide +kernel
/-- **T10** (C33): no pair of events is in a race. -/
theorem noRace_t10 : ∀ a b, ¬ T10.toGraph.Race a b := by decide +kernel

/-- Twin of T10: the last read returns `1` and reads `W_rlx(d,1)`. -/
def T10t : ListGraph 13 (Fin 4) (Fin 2) Nat Unit := lg 13
  [ini 0 0, ini 0 1, sy 0 (.spawn 1), sy 0 (.spawn 2), sy 0 (.spawn 3), sy 1 (.start 1),
   wr 1 0 .relaxed 1, wr 1 1 .release 1, sy 2 (.start 2), up 2 1 .relaxed 1 2, sy 3 (.start 3),
   rd 3 1 .acquire 2, rd 3 0 .relaxed 1]
  [(7, 9), (9, 11), (6, 12)] [(0, 6), (1, 7), (1, 9), (7, 9)]
/-- **Twin of T10** (C34): admitted. -/
theorem t10t_consistent : T10t.toGraph.EventConsistent := by decide +kernel
/-- **Twin of T10** (C33): no pair of events is in a race. -/
theorem noRace_t10t : ∀ a b, ¬ T10t.toGraph.Race a b := by decide +kernel

/-! ## T11 and T12: `SCConsistent` (C34) -/

/-- T11. c1: `W_rel(x,1)`, `R_sc(x)=1`, `R_sc(y)=0`. c2: `W_rel(y,1)`, `R_sc(y)=1`, `R_sc(x)=0`. -/
def T11 : ListGraph 12 (Fin 3) (Fin 2) Nat Unit := lg 12
  [ini 0 0, ini 0 1, sy 0 (.spawn 1), sy 0 (.spawn 2), sy 1 (.start 1), wr 1 0 .release 1,
   rd 1 0 .seqCst 1, rd 1 1 .seqCst 0, sy 2 (.start 2), wr 2 1 .release 1, rd 2 1 .seqCst 1,
   rd 2 0 .seqCst 0]
  [(5, 6), (1, 7), (9, 10), (0, 11)] [(0, 5), (1, 9)]

/-- **T11** (C34, LWG 3941): admitted. -/
theorem t11_consistent : T11.toGraph.EventConsistent := by decide +kernel
/-- **T11** (C33): no pair of events is in a race. -/
theorem noRace_t11 : ∀ a b, ¬ T11.toGraph.Race a b := by decide +kernel

/-- T12. c1: `R_acq(x)=1`, `R_sc(y)=0`. c2: `W_sc(x,1)`. c3: `W_sc(y,1)`. c4: `R_acq(y)=1`,
`R_sc(x)=0`. -/
def T12 : ListGraph 16 (Fin 5) (Fin 2) Nat Unit := lg 16
  [ini 0 0, ini 0 1, sy 0 (.spawn 1), sy 0 (.spawn 2), sy 0 (.spawn 3), sy 0 (.spawn 4),
   sy 1 (.start 1), rd 1 0 .acquire 1, rd 1 1 .seqCst 0, sy 2 (.start 2), wr 2 0 .seqCst 1,
   sy 3 (.start 3), wr 3 1 .seqCst 1, sy 4 (.start 4), rd 4 1 .acquire 1, rd 4 0 .seqCst 0]
  [(10, 7), (1, 8), (12, 14), (0, 15)] [(0, 10), (1, 12)]

/-- **T12** (C34): admitted; an `sw` edge leaving a `seq_cst` write directly does not enter
`po ; hb ; po`. -/
theorem t12_consistent : T12.toGraph.EventConsistent := by decide +kernel
/-- **T12** (C33): no pair of events is in a race. -/
theorem noRace_t12 : ∀ a b, ¬ T12.toGraph.Race a b := by decide +kernel

/-! ## T13 and T14: the middle term of `scb` and the erasure (C34) -/

/-- T13. c1: `W_sc(x,1)`, a pure authority marker, `W_rel(x,2)`. c2: `R_acq(x)=2`, `R_sc(y)=0`.
c3: `W_sc(y,1)`, `R_sc(x)=0`. This is the case that made C34 change: under the former term
`po≠loc ; hb ; po≠loc`, T13 was rejected and its erasure admitted. -/
def T13 : ListGraph 15 (Fin 4) (Fin 2) Nat Unit := lg 15
  [ini 0 0, ini 0 1, sy 0 (.spawn 1), sy 0 (.spawn 2), sy 0 (.spawn 3), sy 1 (.start 1),
   wr 1 0 .seqCst 1, mk 1, wr 1 0 .release 2, sy 2 (.start 2), rd 2 0 .acquire 2,
   rd 2 1 .seqCst 0, sy 3 (.start 3), wr 3 1 .seqCst 1, rd 3 0 .seqCst 0]
  [(8, 10), (1, 11), (0, 14)] [(0, 6), (0, 8), (6, 8), (1, 13)]

/-- **T13** (C34): rejected by conjunct 7 alone. -/
theorem t13_verdict : Verdict T13.toGraph true true true true true true false := by decide +kernel
/-- **T13** (C33): no pair of events is in a race. -/
theorem noRace_t13 : ∀ a b, ¬ T13.toGraph.Race a b := by decide +kernel

/-- **T13, erased** (C34, 10c): the erasure of T13 is rejected by conjunct 7 alone too. -/
theorem t13_erased_verdict :
    Verdict T13.toGraph.erasePure true true true true true true false := by
  have hrf : T13.toGraph.RfAvoidsPure := by decide +kernel
  have hmo : T13.toGraph.MoAvoidsPure := by decide +kernel
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := t13_verdict
  exact ⟨(Graph.erasePure_rfWF_iff hrf).trans h1, (Graph.erasePure_moTotal_iff hmo).trans h2,
    (Graph.erasePure_rmwAtomic_iff hrf hmo).trans h3,
    (Graph.erasePure_coherence_iff hrf hmo).trans h4, Graph.erasePure_hbIrrefl_iff.trans h5,
    (Graph.erasePure_noThinAir_iff hrf).trans h6, (Graph.erasePure_scConsistent_iff hrf).trans h7⟩

/-- T14: T13 where the last read becomes `R_sc(x)=1` and reads `W_sc(x,1)`; the twin of T13. -/
def T14 : ListGraph 15 (Fin 4) (Fin 2) Nat Unit := lg 15
  [ini 0 0, ini 0 1, sy 0 (.spawn 1), sy 0 (.spawn 2), sy 0 (.spawn 3), sy 1 (.start 1),
   wr 1 0 .seqCst 1, mk 1, wr 1 0 .release 2, sy 2 (.start 2), rd 2 0 .acquire 2,
   rd 2 1 .seqCst 0, sy 3 (.start 3), wr 3 1 .seqCst 1, rd 3 0 .seqCst 1]
  [(8, 10), (1, 11), (6, 14)] [(0, 6), (0, 8), (6, 8), (1, 13)]

/-- **T14** (C34): admitted. -/
theorem t14_consistent : T14.toGraph.EventConsistent := by decide +kernel
/-- **T14** (C33): no pair of events is in a race. -/
theorem noRace_t14 : ∀ a b, ¬ T14.toGraph.Race a b := by decide +kernel

/-- **T14, erased** (C34, 10c): admitted. -/
theorem t14_erased_consistent : T14.toGraph.erasePure.EventConsistent :=
  (Graph.erasePure_consistent_iff (by decide +kernel) (by decide +kernel)).2 t14_consistent

/-! ## T15: conjunct 3 constrains atomic RMWs only (C34.3) -/

/-- T15. c1: `W_rlx(x,1)`. c2: a **non-atomic** RMW of `x`, `0 → 2`, designating the unit, which
reads `ix`. `mo`: `ix < W_rlx(x,1) < RMW`: the source of the RMW is not its immediate
`mo`-predecessor. -/
def T15 : ListGraph 7 (Fin 3) (Fin 1) Nat Unit := lg 7
  [ini 0 0, sy 0 (.spawn 1), sy 0 (.spawn 2), sy 1 (.start 1), wr 1 0 .relaxed 1,
   sy 2 (.start 2), ⟨2, ⟨0, 0⟩, .marks (some (.unit 0 (.rmw 0 2))) none⟩]
  [(0, 6)] [(0, 4), (0, 6), (4, 6)]

/-- **T15** (C34.3: "the `rf` source of a successful atomic RMW is its immediate
`mo`-predecessor"): the non-atomic RMW is not constrained by conjunct 3, and the seven conjuncts
hold. The two writes of `x` are in a race (C33), which is not a conjunct. -/
theorem t15_consistent : T15.toGraph.RmwAtomic ∧ T15.toGraph.EventConsistent ∧
    T15.toGraph.Race 4 6 := by decide +kernel

/-- The atomic twin of T15: the RMW is an atomic `U_rlx(x: 0 → 2)`. -/
def T15a : ListGraph 7 (Fin 3) (Fin 1) Nat Unit := lg 7
  [ini 0 0, sy 0 (.spawn 1), sy 0 (.spawn 2), sy 1 (.start 1), wr 1 0 .relaxed 1,
   sy 2 (.start 2), up 2 0 .relaxed 0 2]
  [(0, 6)] [(0, 4), (0, 6), (4, 6)]

/-- **Atomic twin of T15** (C34.3): rejected by conjunct 3 alone. -/
theorem t15a_verdict : Verdict T15a.toGraph true true false true true true true := by
  decide +kernel

/-! ## Conflicts do not depend on `hb` (C30; 10a) -/

/-- **Conflict, ordered pair** (C30): in the twin of T2, the initial write of `x` and the read of
`x` by context 2 conflict, and `hb` orders them. -/
theorem conflict_ordered : T2t.toGraph.Conflict 0 6 ∧ T2t.toGraph.HB 0 6 := by decide +kernel

/-- **Conflict, unordered pair** (C30): in T4, the two RMWs conflict, and `hb` orders them in
neither direction. -/
theorem conflict_unordered :
    T4.toGraph.Conflict 4 6 ∧ ¬ T4.toGraph.HB 4 6 ∧ ¬ T4.toGraph.HB 6 4 := by decide +kernel

end Witness

end Ern.ConcurrencyModel.Events
