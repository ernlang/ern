import Ern.Concurrency.Corpus.Frames

/-!
# Corpus of milestone 3, handoff witnesses

`corpus-spec2-m3.md` §2 bis: W-HO, W-HO′ and W-HO″, traces of the authority machine alone. One
theorem per verdict, written from `corpus-spec2-m3.md` §2 bis, preconditions by `decide`. Each
trace is an `EncapsulatedTrace` from the initial state of Spec 1 §47 (no mutex, empty registries),
so `KInvC` holds at its final state by `encapsulated_inv`. Lean names: `W_HO` (W-HO), `W_HO2`
(W-HO′), `W_HO3` (W-HO″).
-/

namespace Ern.Concurrency.Corpus.Handoff

open Ern.MemoryModel.Access Ern.Concurrency Ern.Concurrency.Corpus
open Ern.Concurrency.Traces (L0)

/-! ## W-HO (`corpus-spec2-m3.md` §2 bis W-HO) -/

/-- `c1 : write3(X)` via `a` (O10), from the state of S13 after `spawn c1` yielding `a`
(`Corpus.t2`). -/
def h1 : SC := t2.set (write3Eff (t2.view 1) [1, 2])
/-- `c1 : release(a)` (O3). -/
def h2 : SC := h1.set (releaseEff (h1.view 1) 1)
/-- `c0 : write3(X)` via `root_X` (O10). -/
def h3 : SC := h2.set (write3Eff (h2.view 0) [1, 2])

/-- `corpus-spec2-m3.md` §2 bis W-HO, step 1, `ok` (O10.1): `c1 : write3(X)` via `a`. -/
theorem W_HO_1_ok : opStepC KF (.write 1 [1, 2]) 1 t2 (.ok h1) :=
  ⟨by decide, _, .ok (by decide), rfl⟩

/-- `corpus-spec2-m3.md` §2 bis W-HO, step 2, `ok` (O3.1–O3.3): `c1 : release(a)`. -/
theorem W_HO_2_ok : opStepC KF (.release 1) 1 h1 (.ok h2) :=
  ⟨by decide, _, .ok (by decide), rfl⟩

/-- `corpus-spec2-m3.md` §2 bis W-HO, step 3, `ok` (O10.1; §40 `RootHeld`; §43.2; §62 effect):
`c0 : write3(X)` via `root_X`, context 1 live, with neither `terminate` nor `join`. The twin is
`Corpus.S13_2_ok`; the negative case is `Corpus.S13_1_reject`. -/
theorem W_HO_3_ok : h2.Live 1 ∧ opStepC KF (.write 0 [1, 2]) 0 h2 (.ok h3) :=
  ⟨by decide, by decide, _, .ok (by decide), rfl⟩

/-- `corpus-spec2-m3.md` §2 bis W-HO as an `EncapsulatedTrace` from the initial state of S13;
`KInvC` holds at its final state (`encapsulated_inv`). -/
theorem w_ho_trace : EncapsulatedTrace KF L0 (t0, [], [])
      [.kernel 0 (.derive 0 [1, 2] .modify), .spawn 0 [1] [], .kernel 1 (.write 1 [1, 2]),
       .kernel 1 (.release 1), .kernel 0 (.write 0 [1, 2])] (h3, [], []) ∧ KInvC h3 := by
  obtain ⟨h0, hs, -⟩ := S13_1_reject
  have ht : EncapsulatedTrace KF L0 (t0, [], [])
      [.kernel 0 (.derive 0 [1, 2] .modify), .spawn 0 [1] [], .kernel 1 (.write 1 [1, 2]),
       .kernel 1 (.release 1), .kernel 0 (.write 0 [1, 2])] (h3, [], []) :=
    .cons (fun e he => by cases he) (.kernel h0) <| .cons trivial (.spawn hs) <|
    .cons trivial (.kernel W_HO_1_ok) <| .cons trivial (.kernel W_HO_2_ok) <|
    .cons trivial (.kernel W_HO_3_ok.2) .nil
  exact ⟨ht, (encapsulated_inv (ddKC []) (by decide : StaticsOK xst) ht).1⟩

/-! ## W-HO′ (`corpus-spec2-m3.md` §2 bis W-HO′) -/

/-- Initial state: the local `X` (place 0), `Init`, root authority 0 (`Corpus.yst`). -/
def k0 : SC := SC.ofS3 (S3.init yst)
/-- `a := derive(root_X, Modify)`, authority 1 (O1). -/
def k1 : SC := k0.set (deriveEff (k0.view 0) 0 [0] .modify)
/-- `b := derive(a, Modify)`, authority 2, held by frame 0 (O1). -/
def k2 : SC := k1.set (deriveEff (k1.view 0) 1 [0] .modify)
/-- `spawn c1` yielding `a` while `b` stays held by frame 0 (WC4 C4): context 1, frame 1. -/
def k3 : SC := spawnEff k2 0 [1] []
/-- `c0 : write3(X)` via `b` (O10). -/
def k4 : SC := k3.set (write3Eff (k3.view 0) [0])
/-- `c0 : release(b)` (O3). -/
def k5 : SC := k4.set (releaseEff (k4.view 0) 2)
/-- `c1 : write3(X)` via `a` (O10). -/
def k6 : SC := k5.set (write3Eff (k5.view 1) [0])

/-- `corpus-spec2-m3.md` §2 bis W-HO′, setup, `ok` (WC4 C4.3: `a` is active, derived and held by the
creating frame; C4.5, O6.3: `root_X` is exercisable in no mode from the frame of the child): the
`spawn` yielding `a` while its derivative `b` stays held by frame 0. -/
theorem W_HO2_0_ok : opStepC KF (.derive 0 [0] .modify) 0 k0 (.ok k1) ∧
    opStepC KF (.derive 1 [0] .modify) 0 k1 (.ok k2) ∧ SpawnStep k2 0 [1] [] (.ok k3) :=
  ⟨⟨by decide, _, .ok (by decide), rfl⟩, ⟨by decide, _, .ok (by decide), rfl⟩,
    ⟨by decide, .ok (by decide)⟩⟩

/-- `corpus-spec2-m3.md` §2 bis W-HO′, step 1, `reject` (O10.1: no effective mode, §43.3, the
active `Modify` descendant `b`): `c1 : write3(X)` via `a`. -/
theorem W_HO2_1_reject : opStepC KF (.write 1 [0]) 1 k3 .reject ∧ effective k3.flat 1 0 = none :=
  ⟨⟨by decide, _, .reject (by decide), rfl⟩, by decide⟩

/-- `corpus-spec2-m3.md` §2 bis W-HO′, step 2, `ok` (O10.1): `c0 : write3(X)` via `b`. -/
theorem W_HO2_2_ok : opStepC KF (.write 2 [0]) 0 k3 (.ok k4) :=
  ⟨by decide, _, .ok (by decide), rfl⟩

/-- `corpus-spec2-m3.md` §2 bis W-HO′, step 3, `ok` (O3): `c0 : release(b)`. -/
theorem W_HO2_3_ok : opStepC KF (.release 2) 0 k4 (.ok k5) :=
  ⟨by decide, _, .ok (by decide), rfl⟩

/-- `corpus-spec2-m3.md` §2 bis W-HO′, step 4, `ok` (§43.2): `c1 : write3(X)` via `a`. -/
theorem W_HO2_4_ok : opStepC KF (.write 1 [0]) 1 k5 (.ok k6) :=
  ⟨by decide, _, .ok (by decide), rfl⟩

/-- `corpus-spec2-m3.md` §2 bis W-HO′ as an `EncapsulatedTrace` from the initial state; `KInvC`
holds at its final state (`encapsulated_inv`). -/
theorem w_ho2_trace : EncapsulatedTrace KF L0 (k0, [], [])
      [.kernel 0 (.derive 0 [0] .modify), .kernel 0 (.derive 1 [0] .modify), .spawn 0 [1] [],
       .kernel 0 (.write 2 [0]), .kernel 0 (.release 2), .kernel 1 (.write 1 [0])] (k6, [], []) ∧
    KInvC k6 := by
  obtain ⟨d1, d2, hs⟩ := W_HO2_0_ok
  have ht : EncapsulatedTrace KF L0 (k0, [], [])
      [.kernel 0 (.derive 0 [0] .modify), .kernel 0 (.derive 1 [0] .modify), .spawn 0 [1] [],
       .kernel 0 (.write 2 [0]), .kernel 0 (.release 2), .kernel 1 (.write 1 [0])] (k6, [], []) :=
    .cons (fun e he => by cases he) (.kernel d1) <| .cons (fun e he => by cases he) (.kernel d2) <|
    .cons trivial (.spawn hs) <| .cons trivial (.kernel W_HO2_2_ok) <|
    .cons trivial (.kernel W_HO2_3_ok) <| .cons trivial (.kernel W_HO2_4_ok) .nil
  exact ⟨ht, (encapsulated_inv (ddKC []) (by decide : StaticsOK yst) ht).1⟩

/-! ## W-HO″ (`corpus-spec2-m3.md` §2 bis W-HO″) -/

/-- `a := derive(root_X, Modify)`, authority 1 (O1). -/
def m1 : SC := k0.set (deriveEff (k0.view 0) 0 [0] .modify)
/-- `spawn c1` yielding `a` (WC4 C4): context 1, frame 1. -/
def m2 : SC := spawnEff m1 0 [1] []
/-- `c1 : a₂ := derive(a, Modify)`, authority 2, held by frame 1 (O1). -/
def m3 : SC := m2.set (deriveEff (m2.view 1) 1 [0] .modify)
/-- `c1 : spawn c2` yielding `a₂` (WC4 C4): context 2, frame 2, parent frame 1. -/
def m4 : SC := spawnEff m3 1 [2] []
/-- `c2 : write3(X)` via `a₂` (O10). -/
def m5 : SC := m4.set (write3Eff (m4.view 2) [0])
/-- `c2 : release(a₂)` (O3). -/
def m6 : SC := m5.set (releaseEff (m5.view 2) 2)
/-- `c1 : release(a)` (O3). -/
def m7 : SC := m6.set (releaseEff (m6.view 1) 1)
/-- `c1 : terminate` (WC4 C7). -/
def m8 : SC := termEffC m7 1
/-- `c0 : write3(X)` via `root_X` (O10). -/
def m9 : SC := m8.set (write3Eff (m8.view 0) [0])

/-- The setup of `corpus-spec2-m3.md` §2 bis W-HO″: `derive`, `spawn c1` yielding `a`,
`c1 : a₂ := derive(a, Modify)`, `c1 : spawn c2` yielding `a₂`; the initial frame of context 2 has
parent frame 1. -/
theorem w_ho3_setup : opStepC KF (.derive 0 [0] .modify) 0 k0 (.ok m1) ∧
    SpawnStep m1 0 [1] [] (.ok m2) ∧ opStepC KF (.derive 1 [0] .modify) 1 m2 (.ok m3) ∧
    SpawnStep m3 1 [2] [] (.ok m4) ∧ m4.ctxParent 2 = some 1 :=
  ⟨⟨by decide, _, .ok (by decide), rfl⟩, ⟨by decide, .ok (by decide)⟩,
    ⟨by decide, _, .ok (by decide), rfl⟩, ⟨by decide, .ok (by decide)⟩, by decide⟩

/-- `corpus-spec2-m3.md` §2 bis W-HO″, step 1, `ok` (O10.1): `c2 : write3(X)` via `a₂`. -/
theorem W_HO3_1_ok : opStepC KF (.write 2 [0]) 2 m4 (.ok m5) :=
  ⟨by decide, _, .ok (by decide), rfl⟩

/-- `corpus-spec2-m3.md` §2 bis W-HO″, step 2, `ok` (O3): `c2 : release(a₂)`. -/
theorem W_HO3_2_ok : opStepC KF (.release 2) 2 m5 (.ok m6) :=
  ⟨by decide, _, .ok (by decide), rfl⟩

/-- `corpus-spec2-m3.md` §2 bis W-HO″, step 3, `ok` (O3.3: no active descendant left):
`c1 : release(a)`. -/
theorem W_HO3_3_ok : opStepC KF (.release 1) 1 m6 (.ok m7) :=
  ⟨by decide, _, .ok (by decide), rfl⟩

/-- `corpus-spec2-m3.md` §2 bis W-HO″, step 4, `ok` (WC4 C7): `c1 : terminate` while context 2 is
live; the initial frame of context 2, whose parent was frame 1, is reparented on frame 0 (WC4 C6),
without waiting for the child. -/
theorem W_HO3_4_ok : m7.ctxParent 2 = some 1 ∧ TermStep KF m7 1 (.ok m8) ∧ m8.Live 2 ∧
    m8.ctxParent 2 = some 0 :=
  ⟨by decide, ⟨by decide, .ok (by decide)⟩, by decide, by decide⟩

/-- `corpus-spec2-m3.md` §2 bis W-HO″, step 5, `ok` (WC4 C8): `c0 : join(c1)`. -/
theorem W_HO3_5_ok : JoinStep m8 0 1 (.ok m8) := .ok (by decide) (by decide)

/-- `corpus-spec2-m3.md` §2 bis W-HO″, step 6, `ok` (O10.1, §43.2): `c0 : write3(X)` via `root_X`,
context 2 live. -/
theorem W_HO3_6_ok : m8.Live 2 ∧ opStepC KF (.write 0 [0]) 0 m8 (.ok m9) :=
  ⟨by decide, by decide, _, .ok (by decide), rfl⟩

/-- `corpus-spec2-m3.md` §2 bis W-HO″, negative, `reject` (O3.3: `a₂` is active): step 3 before
step 2, `c1 : release(a)` while the descendant `a₂` of context 2 is active. -/
theorem W_HO3_7_reject : opStepC KF (.release 1) 1 m5 .reject ∧ m5.flat.Active 2 :=
  ⟨⟨by decide, _, .reject (by decide), rfl⟩, by decide⟩

/-- `corpus-spec2-m3.md` §2 bis W-HO″ as an `EncapsulatedTrace` from the initial state; `KInvC`
holds at its final state (`encapsulated_inv`). -/
theorem w_ho3_trace : EncapsulatedTrace KF L0 (k0, [], [])
      [.kernel 0 (.derive 0 [0] .modify), .spawn 0 [1] [], .kernel 1 (.derive 1 [0] .modify),
       .spawn 1 [2] [], .kernel 2 (.write 2 [0]), .kernel 2 (.release 2), .kernel 1 (.release 1),
       .terminate 1, .join 0 1, .kernel 0 (.write 0 [0])] (m9, [], []) ∧ KInvC m9 := by
  obtain ⟨d1, s1, d2, s2, -⟩ := w_ho3_setup
  have ht : EncapsulatedTrace KF L0 (k0, [], [])
      [.kernel 0 (.derive 0 [0] .modify), .spawn 0 [1] [], .kernel 1 (.derive 1 [0] .modify),
       .spawn 1 [2] [], .kernel 2 (.write 2 [0]), .kernel 2 (.release 2), .kernel 1 (.release 1),
       .terminate 1, .join 0 1, .kernel 0 (.write 0 [0])] (m9, [], []) :=
    .cons (fun e he => by cases he) (.kernel d1) <| .cons trivial (.spawn s1) <|
    .cons (fun e he => by cases he) (.kernel d2) <| .cons trivial (.spawn s2) <|
    .cons trivial (.kernel W_HO3_1_ok) <| .cons trivial (.kernel W_HO3_2_ok) <|
    .cons trivial (.kernel W_HO3_3_ok) <| .cons trivial (.terminate W_HO3_4_ok.2.1) <|
    .cons trivial (.join W_HO3_5_ok) <| .cons trivial (.kernel W_HO3_6_ok.2) .nil
  exact ⟨ht, (encapsulated_inv (ddKC []) (by decide : StaticsOK yst) ht).1⟩

end Ern.Concurrency.Corpus.Handoff
