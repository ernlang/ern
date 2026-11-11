import Ern.Concurrency.EventModel.Graph

/-!
# Witnesses of the event fragment

Brief of milestone 4, slice 2 (layer E), task 3 (`formal/reports/spec2-m4-eventmodel.md`): the
graphs G1 to G19, given explicitly with their events, `rf` and `mo`; facts written from the brief
(WC5.1 corrigé), decided by `decide`. Event `0` is the initial write `init`, of value `0`; events
`1, 2, …` follow the listing of the brief; contexts `c0` and `c1` are `0` and `1`.
-/

set_option autoImplicit false

namespace Ern.Concurrency.EventModel

/-- The strict total order that lists its elements in this order: every pair `(a, b)` with `a`
before `b`. -/
def chain : List Nat → List (Nat × Nat)
  | [] => []
  | a :: l => l.map (fun b => (a, b)) ++ chain l

/-- No `sw` edge in the graph. -/
def NoSW (g : Graph) : Prop := ∀ a ∈ List.range g.size, ∀ b ∈ List.range g.size, ¬ SW g a b

/-- Decidability of `NoSW`. -/
instance (g : Graph) : Decidable (NoSW g) := by unfold NoSW; infer_instance

/-! ## Message passing (WC5.1 corrigé C32 item 1, C33, C40) -/

/-- Message passing: `c0` : `a = write3(d)` (1), `b = writeShared(x, 1, ob)` (2); `c1` :
`e = readShared(x, oe)` (3) reading `1` from `b`, `g = read3(d)` (4); `mo` : `init < b`. -/
def mp (ob oe : MOrd) : Graph :=
  { init := 0,
    evs := [⟨0, .writeD⟩, ⟨0, .wsh ob 1⟩, ⟨1, .rsh oe 1⟩, ⟨1, .readD⟩],
    rf := [(2, 3)], mo := chain [0, 2] }

/-- G1 (brief): `b` in `release`, `e` in `acquire`: well typed, consistent, `sw(b, e)`,
`hb(a, g)`, no race. -/
theorem G1 : WellTyped (mp .rel .acq) ∧ EventConsistent (mp .rel .acq) ∧ SW (mp .rel .acq) 2 3 ∧
    HB (mp .rel .acq) 1 4 ∧ ¬ Racy (mp .rel .acq) := by
  decide

/-- G2 graph: as G1, but `e` reads `0` from `init` and there is no `g`. -/
def g2 : Graph :=
  { init := 0, evs := [⟨0, .writeD⟩, ⟨0, .wsh .rel 1⟩, ⟨1, .rsh .acq 0⟩],
    rf := [(0, 3)], mo := chain [0, 2] }

/-- G2 (brief): well typed, consistent, no `sw` edge, no race. -/
theorem G2 : WellTyped g2 ∧ EventConsistent g2 ∧ NoSW g2 ∧ ¬ Racy g2 := by decide

/-- G3 (brief): `relaxed`, `relaxed`: well typed, consistent, no `sw`, race `(a, g)`. -/
theorem G3 : WellTyped (mp .rlx .rlx) ∧ EventConsistent (mp .rlx .rlx) ∧ NoSW (mp .rlx .rlx) ∧
    RaceOn (mp .rlx .rlx) 1 4 := by
  decide

/-- G4 (brief): `release`, `relaxed`: well typed, consistent, no `sw`, race `(a, g)`. -/
theorem G4 : WellTyped (mp .rel .rlx) ∧ EventConsistent (mp .rel .rlx) ∧ NoSW (mp .rel .rlx) ∧
    RaceOn (mp .rel .rlx) 1 4 := by
  decide

/-- G5 (brief): `relaxed`, `acquire`: well typed, consistent, no `sw`, race `(a, g)`. -/
theorem G5 : WellTyped (mp .rlx .acq) ∧ EventConsistent (mp .rlx .acq) ∧ NoSW (mp .rlx .acq) ∧
    RaceOn (mp .rlx .acq) 1 4 := by
  decide

/-- G6 (brief): `seq_cst`, `seq_cst`, only in their release and acquire roles (WC5.1 corrigé C40):
well typed, consistent, `sw(b, e)`, no race. -/
theorem G6 : WellTyped (mp .sc .sc) ∧ EventConsistent (mp .sc .sc) ∧ SW (mp .sc .sc) 2 3 ∧
    ¬ Racy (mp .sc .sc) := by
  decide

/-! ## Mixed accesses (WC5.1 corrigé C30, C31, C33, C36, C42) -/

/-- G7 graph: `c0` : `s = writeShared(x, 1, relaxed)` (1); `c1` : `r = read3(x)` (2) reading `0`
from `init`; `mo` : `init < s`. -/
def g7 : Graph :=
  { init := 0, evs := [⟨0, .wsh .rlx 1⟩, ⟨1, .readX 0⟩], rf := [(0, 2)], mo := chain [0, 1] }

/-- G7 (brief): well typed, consistent, race `(s, r)`. -/
theorem G7 : WellTyped g7 ∧ EventConsistent g7 ∧ RaceOn g7 1 2 := by decide

/-- G8 graph: `c0` : `s = writeShared(x, 1, relaxed)` (1); `c1` : `w = write3(x, 2)` (2);
`mo` : `init < s < w`. -/
def g8 : Graph :=
  { init := 0, evs := [⟨0, .wsh .rlx 1⟩, ⟨1, .writeX 2⟩], rf := [], mo := chain [0, 1, 2] }

/-- G8 (brief): well typed, consistent, `w` is a modification placed in `mo`, race `(s, w)`. -/
theorem G8 : WellTyped g8 ∧ EventConsistent g8 ∧ g8.isMod 2 = true ∧ MO g8 1 2 ∧
    RaceOn g8 1 2 := by
  decide

/-- G9 graph: `c0` : `s0 = writeShared(x, 1, relaxed)` (1); `c1` : `s1 = writeShared(x, 2,
relaxed)` (2); `mo` : `init < s0 < s1`. -/
def g9 : Graph :=
  { init := 0, evs := [⟨0, .wsh .rlx 1⟩, ⟨1, .wsh .rlx 2⟩], rf := [], mo := chain [0, 1, 2] }

/-- G9 (brief): well typed, consistent, no race. -/
theorem G9 : WellTyped g9 ∧ EventConsistent g9 ∧ ¬ Racy g9 := by decide

/-- G10 graph: `c0` : `write3(d)` (1); `c1` : `write3(d)` (2). -/
def g10 : Graph :=
  { init := 0, evs := [⟨0, .writeD⟩, ⟨1, .writeD⟩], rf := [], mo := [] }

/-- G10 (brief): well typed, consistent, race. -/
theorem G10 : WellTyped g10 ∧ EventConsistent g10 ∧ RaceOn g10 1 2 := by decide

/-! ## RMW (WC5.1 corrigé C31, C32 item 1, C39, C40) -/

/-- G11 graph: `c0` : `m0` RMW reads `0`, writes `1`, `acquire` (1); `c1` : `m1` RMW reads `1`,
writes `1`, `acquire` (2); `rf` : `init → m0`, `m0 → m1`; `mo` : `init < m0 < m1`. -/
def g11 : Graph :=
  { init := 0, evs := [⟨0, .rmw .acq 0 1⟩, ⟨1, .rmw .acq 1 1⟩], rf := [(0, 1), (1, 2)],
    mo := chain [0, 1, 2] }

/-- G11 (brief): well typed, consistent. -/
theorem G11 : WellTyped g11 ∧ EventConsistent g11 := by decide

/-- G12 graphs: as G11, but `m1` reads `0` from `init`; `mo` is `init < m0 < m1` (`[0, 1, 2]`) or
`init < m1 < m0` (`[0, 2, 1]`). -/
def g12 (m : List Nat) : Graph :=
  { init := 0, evs := [⟨0, .rmw .acq 0 1⟩, ⟨1, .rmw .acq 0 1⟩], rf := [(0, 1), (0, 2)],
    mo := chain m }

/-- G12 (brief): not consistent, conjunct 3 failing, for both orders of `mo`. Conjuncts 1, 2, 4
and 5 hold in both: coherence (`hb ; eco?` irreflexive) does not exclude the graph, the `eco`
cycle through the two RMWs having no `hb` edge. -/
theorem G12 : ∀ m ∈ [[0, 1, 2], [0, 2, 1]], WellTyped (g12 m) ∧ ¬ EventConsistent (g12 m) ∧
    ¬ RmwAtomic (g12 m) ∧ RfWF (g12 m) ∧ MoTotal (g12 m) ∧ Coherent (g12 m) ∧
    HbIrrefl (g12 m) := by
  decide

/-- G13 graph: `c0` : `m0` RMW reads `0`, writes `1`, `acquire` (1); `c1` :
`f = readShared(x, relaxed)` (2) reading `1` from `m0` (a failed compare-exchange); `mo` :
`init < m0`. -/
def g13 : Graph :=
  { init := 0, evs := [⟨0, .rmw .acq 0 1⟩, ⟨1, .rsh .rlx 1⟩], rf := [(0, 1), (1, 2)],
    mo := chain [0, 1] }

/-- G13 (brief): well typed, consistent, `f` is not a modification (WC5.1 corrigé C39). -/
theorem G13 : WellTyped g13 ∧ EventConsistent g13 ∧ g13.isMod 2 = false := by decide

/-- The lock graphs: `c0` : `A0` RMW reads `0`, writes `1`, order `oa` (1), `w0 = write3(d)` (2),
`U0 = writeShared(x, 0, ou)` (3); `c1` : `A1` (4), `w1` (5), `U1` (6), likewise; `rf` :
`init → A0`, `U0 → A1`; `mo` : `init < A0 < U0 < A1 < U1`. -/
def lock (oa ou : MOrd) : Graph :=
  { init := 0,
    evs := [⟨0, .rmw oa 0 1⟩, ⟨0, .writeD⟩, ⟨0, .wsh ou 0⟩,
      ⟨1, .rmw oa 0 1⟩, ⟨1, .writeD⟩, ⟨1, .wsh ou 0⟩],
    rf := [(0, 1), (3, 4)], mo := chain [0, 1, 3, 4, 6] }

/-- G14 (brief): `acquire` RMWs, `release` stores: well typed, consistent, `sw(U0, A1)`,
`hb(w0, w1)`, no race. -/
theorem G14 : WellTyped (lock .acq .rel) ∧ EventConsistent (lock .acq .rel) ∧
    SW (lock .acq .rel) 3 4 ∧ HB (lock .acq .rel) 2 5 ∧ ¬ Racy (lock .acq .rel) := by
  decide

/-- G15 (brief): G14 with `U0`, `U1` in `relaxed`: well typed, consistent, no `sw`, race
`(w0, w1)`. -/
theorem G15 : WellTyped (lock .acq .rlx) ∧ EventConsistent (lock .acq .rlx) ∧
    NoSW (lock .acq .rlx) ∧ RaceOn (lock .acq .rlx) 2 5 := by
  decide

/-- G16 (brief): G14 with `A0`, `A1` in `relaxed`: well typed, consistent, no `sw`, race
`(w0, w1)`. -/
theorem G16 : WellTyped (lock .rlx .rel) ∧ EventConsistent (lock .rlx .rel) ∧
    NoSW (lock .rlx .rel) ∧ RaceOn (lock .rlx .rel) 2 5 := by
  decide

/-- G17 graph: `c0` : `a = write3(d)` (1), `m` RMW reads `0`, writes `1`, `acq_rel` (2); `c1` :
`e = readShared(x, acquire)` (3) reading `1` from `m`, `g = read3(d)` (4); `mo` : `init < m`. -/
def g17 : Graph :=
  { init := 0, evs := [⟨0, .writeD⟩, ⟨0, .rmw .acqRel 0 1⟩, ⟨1, .rsh .acq 1⟩, ⟨1, .readD⟩],
    rf := [(0, 2), (2, 3)], mo := chain [0, 2] }

/-- G17 (brief): well typed, consistent, `sw(m, e)`, no race. -/
theorem G17 : WellTyped g17 ∧ EventConsistent g17 ∧ SW g17 2 3 ∧ ¬ Racy g17 := by decide

/-! ## Release sequence and typing (WC5.1 corrigé C32 item 1, C40, C48) -/

/-- G18 graph: `c0` : `a = write3(d)` (1), `b = writeShared(x, 1, release)` (2),
`c = writeShared(x, 2, relaxed)` (3); `c1` : `e = readShared(x, acquire)` (4) reading `2` from
`c`, `g = read3(d)` (5); `mo` : `init < b < c`. -/
def g18 : Graph :=
  { init := 0,
    evs := [⟨0, .writeD⟩, ⟨0, .wsh .rel 1⟩, ⟨0, .wsh .rlx 2⟩, ⟨1, .rsh .acq 2⟩, ⟨1, .readD⟩],
    rf := [(3, 4)], mo := chain [0, 2, 3] }

/-- G18 (brief): well typed, consistent, no `sw` edge into `e`, race `(a, g)`: the non-RMW atomic
write `c` of the same thread does not extend the release of `b` (WC5.1 corrigé C32 item 1, C48;
the divergence with `rc11.cat` is in the report). -/
theorem G18 : WellTyped g18 ∧ EventConsistent g18 ∧
    (∀ w ∈ List.range g18.size, ¬ SW g18 w 4) ∧ RaceOn g18 1 5 := by
  decide

/-- G19 graph: one `readShared(x, release)` reading `0` from `init`. -/
def g19 : Graph := { init := 0, evs := [⟨0, .rsh .rel 0⟩], rf := [(0, 1)], mo := [] }

/-- G19 (brief): ill typed (WC5.1 corrigé C40: `release` is not in the row of `readShared`). -/
theorem G19 : ¬ WellTyped g19 := by decide

end Ern.Concurrency.EventModel
