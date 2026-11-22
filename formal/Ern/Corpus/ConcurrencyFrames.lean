import Ern.ConcurrencyModel.WitnessFrames

/-!
# Corpus of the concurrency model: frames, contexts and ordinary authorities (test module)

Cases `R01`–`R12` of the concurrency model
(`specs/ERN_Concurrency_Model_Specification_v0.md`),
replayed on the concurrent authority machine (`LStep`). Each state is reached from the initial
state of Spec 1 §47 by `ok` steps (`LRun`). Each theorem states the obtained verdict of every step
of its case: an outcome of the relation of the step (`opStepC`, `SpawnStep`, `SpawnValStep`,
`TermStep`, `JoinStep`). Its docstring gives the situation, the expected verdict with its clause,
the obtained verdict and the twin. A local that a case initializes is written through its root
authority (`write3`, Spec 1 §67), locals being born `Uninit` (Spec 1 §72); a local of the base
frame is a static place declared `Uninit` (Spec 1 §47). The contract is `kFrames`: no
`SharedMutable` leaf. This is a test module: no model module imports it.
-/

namespace Ern.Corpus.Concurrency

open Ern.MemoryModel.Access Ern.ConcurrencyModel

/-- One `Uninit` static place of one leaf, owned by frame 0 (Spec 1 §47). -/
def oneLocal : Statics := [((none, none, 0), false)]

/-- Two `Uninit` static places of one leaf, owned by frame 0 (Spec 1 §47). -/
def twoLocals : Statics := [((none, none, 0), false), ((none, none, 0), false)]

/-! ## R01, R11: a frame exit with a surviving child authority -/

/-- Initial state with no static (Spec 1 §47). -/
def r01s0 : SC := SC.ofS3 (S3.init [])
/-- Context 0 enters frame 1 with one local `X` (place 0), root authority 0 (O6). -/
def r01s1 : SC := enterEffC r01s0 0 [] [(none, 0)]
/-- `write3(X)` through `root_X` (O10). -/
def r01s2 : SC := r01s1.set (write3Eff (r01s1.view 0) [0])
/-- `a := derive(root_X, Modify)`, authority 1, held by frame 1 (O1). -/
def r01s3 : SC := r01s2.set (deriveEff (r01s2.view 0) 0 [0] .modify)
/-- `spawn` of context 1 yielding `a` (C4): initial frame 2, parented to frame 1. -/
def r01s4 : SC := spawnEff r01s3 0 [1] []

/-- The setup of `R01` and `R11`. -/
def r01L : List Label :=
  [.kernel 0 (.enter [] [(none, 0)]), .kernel 0 (.write 0 [0]), .kernel 0 (.derive 0 [0] .modify),
   .spawn 0 [1] []]

/-- The setup of `R01` and `R11` is reached by `ok` steps (O6, O10, O1, C4). -/
theorem r01_run : LRun kFrames mutexLayout (r01s0, [], []) r01L (r01s4, [], []) :=
  .cons (.kernel (.ok (by decide))) <| .cons (.kernel ⟨_, .ok (by decide), rfl⟩) <|
  .cons (.kernel ⟨_, .ok (by decide), rfl⟩) <| .cons (.spawn (.ok (by decide))) .nil

/-- **R01** (`reject`). Context 0 enters frame 1 with a local `X`, initializes it, derives
`a := derive(root_X, Modify)` and spawns context 1 yielding `a`; then context 0 exits frame 1.
Expected: `reject`, C6.1 by O7.2 and O7.4: a surviving active authority is attached to a local
that dies, and its origin chain reaches a root of the exiting frame (Spec 1 §73.2, §73.4, §54).
Obtained: `reject`. Twin: `R01_twin`. -/
theorem R01 : LRun kFrames mutexLayout (r01s0, [], []) r01L (r01s4, [], []) ∧
    opStepC kFrames.toK .exit 0 r01s4 .reject :=
  ⟨r01_run, .reject (by decide)⟩

/-- `release(a)` by context 1 (O3). -/
def r01t1 : SC := r01s4.set (releaseEff (r01s4.view 1) 1)
/-- `terminate` of context 1 (C7). -/
def r01t2 : SC := termEffC r01t1 1

/-- **R01, twin** (`ok`). From the setup of `R01`: context 1 releases `a`, then terminates;
context 0 joins context 1, then exits frame 1. Expected: each step `ok`; `join(c1)` `ok` by C8.
Obtained: each step `ok`. -/
theorem R01_twin : opStepC kFrames.toK (.release 1) 1 r01s4 (.ok r01t1) ∧
    TermStep kFrames.toK r01t1 1 (.ok r01t2) ∧ JoinStep r01t2 0 1 (.ok r01t2) ∧
    opStepC kFrames.toK .exit 0 r01t2 (.ok (exitEffC r01t2 0)) :=
  ⟨⟨_, .ok (by decide), rfl⟩, .ok (by decide), .ok (by decide) (by decide), .ok (by decide)⟩

/-- `write3(X)` by context 1 through `a` (O10). -/
def r11s1 : SC := r01s4.set (write3Eff (r01s4.view 1) [0])
/-- `release(a)` by context 1, which stays live (O3). -/
def r11s2 : SC := r11s1.set (releaseEff (r11s1.view 1) 1)

/-- **R11** (`ok`). From the setup of `R01`: 1. context 1 writes `X` through `a`; 2. context 1
releases `a` and stays live; 3. context 0 exits frame 1. Expected: 1 `ok`; 2 `ok`; 3 `ok` by O7,
with no wait for the child context (C6). Obtained: each step `ok`; context 1 is still live after
the exit. Twin: step 3 before step 2 is `R01`. -/
theorem R11 : opStepC kFrames.toK (.write 1 [0]) 1 r01s4 (.ok r11s1) ∧
    opStepC kFrames.toK (.release 1) 1 r11s1 (.ok r11s2) ∧
    opStepC kFrames.toK .exit 0 r11s2 (.ok (exitEffC r11s2 0)) ∧ (exitEffC r11s2 0).Live 1 :=
  ⟨⟨_, .ok (by decide), rfl⟩, ⟨_, .ok (by decide), rfl⟩, .ok (by decide), by decide⟩

/-! ## R02: a frame exit that re-anchors a child authority on a surviving root -/

/-- `write3(Y)` through `root_Y`, authority 0 (O10). -/
def r02s1 : SC := (SC.ofS3 (S3.init oneLocal)).set
  (write3Eff ((SC.ofS3 (S3.init oneLocal)).view 0) [0])
/-- `q := derive(root_Y, Modify)`, authority 1 (O1). -/
def r02s2 : SC := r02s1.set (deriveEff (r02s1.view 0) 0 [0] .modify)
/-- Context 0 enters frame 1 yielding `q` (O6). -/
def r02s3 : SC := enterEffC r02s2 0 [1] []
/-- `a := derive(q, Modify)`, authority 2, held by frame 1 (O1). -/
def r02s4 : SC := r02s3.set (deriveEff (r02s3.view 0) 1 [0] .modify)
/-- `spawn` of context 1 yielding `a` (C4): initial frame 2, parented to frame 1. -/
def r02s5 : SC := spawnEff r02s4 0 [2] []
/-- `exitFrame(f1)` by context 0 (O7, C6). -/
def r02s6 : SC := exitEffC r02s5 0

/-- The setup of `R02`. -/
def r02L : List Label :=
  [.kernel 0 (.write 0 [0]), .kernel 0 (.derive 0 [0] .modify), .kernel 0 (.enter [1] []),
   .kernel 0 (.derive 1 [0] .modify), .spawn 0 [2] []]

/-- **R02** (`ok`, then `reject`). Base frame: a local `Y`, initialized; `q := derive(root_Y,
Modify)`; context 0 enters frame 1 yielding `q`; in frame 1, `a := derive(q, Modify)`; context 0
spawns context 1 yielding `a`. Then context 0 exits frame 1, then writes `Y` through `root_Y`.
Expected: the exit `ok` by O7.4 (`q` released, `a` survives, re-anchored on `root_Y`) and C6 (the
initial frame of context 1 is reparented to frame 0); the write `reject` by O10.1 (Spec 1 §43.3).
Obtained: the exit `ok`, with `q` inactive, `a` active of origin `root_Y`, the initial frame 2 of
context 1 of parent frame 0; the write `reject`. Twin: `R01`. -/
theorem R02 : LRun kFrames mutexLayout (SC.ofS3 (S3.init oneLocal), [], []) r02L (r02s5, [], []) ∧
    opStepC kFrames.toK .exit 0 r02s5 (.ok r02s6) ∧ ¬ r02s6.flat.Active 1 ∧
    r02s6.flat.Active 2 ∧ r02s6.flat.org 2 = some 0 ∧ r02s6.parC 2 = some 0 ∧
    opStepC kFrames.toK (.write 0 [0]) 0 r02s6 .reject :=
  ⟨.cons (.kernel ⟨_, .ok (by decide), rfl⟩) <| .cons (.kernel ⟨_, .ok (by decide), rfl⟩) <|
    .cons (.kernel (.ok (by decide))) <| .cons (.kernel ⟨_, .ok (by decide), rfl⟩) <|
    .cons (.spawn (.ok (by decide))) .nil,
   .ok (by decide), by decide, by decide, by decide, by decide, ⟨_, .reject (by decide), rfl⟩⟩

/-! ## R03, R12: a by-value `spawn` -/

/-- The setup of `R03` and `R12` (the states `f0`–`f5` of `WitnessFrames`): context 0 enters
frame 1 with the locals `v` (place 1) and `p` (place 2), initializes them, allocates a root `T′`
(place 3) owned by `v` from the provider `p`, and derives `a := derive(root_p, Modify)`
(authority 4). -/
def r03L : List Label :=
  [.kernel 0 (.enter [] [(none, 0), (none, 0)]), .kernel 0 (.write 1 [1]),
   .kernel 0 (.write 2 [2]), .kernel 0 (.alloc 2 1 [(none, 0)]), .kernel 0 (.derive 2 [2] .modify)]

/-- The setup of `R03` is reached by `ok` steps (O6, O10, O14, O1). -/
theorem r03_run : LRun kFrames mutexLayout (f0, [], []) r03L (f5, [], []) :=
  .cons (.kernel frames_steps.1) <| .cons (.kernel frames_steps.2.1) <|
  .cons (.kernel frames_steps.2.2.1) <| .cons (.kernel frames_steps.2.2.2) <|
  .cons (.kernel ⟨_, .ok (by decide), rfl⟩) .nil

/-- The by-value `spawn` of context 1 from frame 1, creating its local `d` (place 4), moving `v`
into `d` and yielding `a` (C5). -/
def r03s6 : SC := spawnValEff f5 0 [4] [(none, 0)] [(1, 4)]

/-- **R03** (`ok`, then `reject`). Frame 1 of context 0 has the locals `v`, owning a root `T′`, and
`p`, both initialized, and `a := derive(root_p, Modify)`; context 0 spawns context 1 by value,
moving `v` into the fresh local `d` and yielding `a`; then context 0 exits frame 1. Expected: the
`spawn` `ok` by C5 (no parameter covers a leaf of the source, C5 item 5); the exit `reject`, C6.1
by O7.2 and O7.4 (Spec 1 §73.2, §73.4), as in `R01`. Obtained: the `spawn` `ok`; the exit
`reject`. Twin: `R03_twin`. -/
theorem R03 : LRun kFrames mutexLayout (f0, [], []) r03L (f5, [], []) ∧
    SpawnValStep kFrames.toK f5 0 [4] [(none, 0)] [(1, 4)] (.ok r03s6) ∧
    opStepC kFrames.toK .exit 0 r03s6 .reject :=
  ⟨r03_run, .ok (by decide), .reject (by decide)⟩

/-- **R03, twin** (`ok`). From the state before the derivation of `a` (`f4`), the same by-value
`spawn` without parameter (`f6`), then the exit of frame 1 by context 0. Expected: both `ok`.
Obtained: both `ok`. -/
theorem R03_twin : SpawnValStep kFrames.toK f4 0 [] [(none, 0)] [(1, 4)] (.ok f6) ∧
    opStepC kFrames.toK .exit 0 f6 (.ok f7) :=
  ⟨.ok (by decide), .ok (by decide)⟩

/-- `write3(d)` by context 1 through `root_d`, authority 4 (O10). -/
def r12s1 : SC := f6.set (write3Eff (f6.view 1) [4])

/-- **R12** (`ok`; `reject`). From the by-value `spawn` without parameter of `R03_twin` (`f6`): 1.
context 1 writes its local `d` through `root_d`; 2. context 0 reads `v` through `root_v`.
Expected: 1 `ok` by O10.1 and C5 item 2; 2 `reject` by O9.1: the leaves of `v` are `Moved`.
Obtained: 1 `ok`; 2 `reject`, the leaf of `v` being `Moved`. Twin: step 1 is the twin of step
2. -/
theorem R12 : opStepC kFrames.toK (.write 4 [4]) 1 f6 (.ok r12s1) ∧ r12s1.I 1 = .moved ∧
    opStepC kFrames.toK (.read 1 [1]) 0 r12s1 .reject :=
  ⟨⟨_, .ok (by decide), rfl⟩, by decide, ⟨_, .reject (by decide), rfl⟩⟩

/-! ## R04: a write through a root whose derivative was yielded -/

/-- One static place `X = {left, right}` (places 0, 1, 2), `Uninit`, owned by frame 0 (Spec 1
§47). -/
def pairLocal : Statics :=
  [((none, none, 0), false), ((some 0, none, 0), false), ((some 0, none, 0), false)]

/-- `write3(X)` through `root_X`, authority 0 (O10). -/
def r04s1 : SC := (SC.ofS3 (S3.init pairLocal)).set
  (write3Eff ((SC.ofS3 (S3.init pairLocal)).view 0) [1, 2])
/-- `a := derive(root_X, Modify)`, authority 1 (O1). -/
def r04s2 : SC := r04s1.set (deriveEff (r04s1.view 0) 0 [1, 2] .modify)
/-- `spawn` of context 1 yielding `a` (C4). -/
def r04s3 : SC := spawnEff r04s2 0 [1] []

/-- The setup of `R04`. -/
def r04L : List Label :=
  [.kernel 0 (.write 0 [1, 2]), .kernel 0 (.derive 0 [1, 2] .modify), .spawn 0 [1] []]

/-- **R04** (`reject`). Base frame: a local `X = {left, right}`, initialized; `a := derive(root_X,
Modify)`; context 0 spawns context 1 yielding `a`; then context 0 writes `X` through `root_X`.
Expected: `reject` by O10.1: no effective mode (Spec 1 §43.3). Obtained: `reject`. Twins:
`R04_twin_a`, `R04_twin_b`. -/
theorem R04 : LRun kFrames mutexLayout (SC.ofS3 (S3.init pairLocal), [], []) r04L
      (r04s3, [], []) ∧
    opStepC kFrames.toK (.write 0 [1, 2]) 0 r04s3 .reject :=
  ⟨.cons (.kernel ⟨_, .ok (by decide), rfl⟩) <| .cons (.kernel ⟨_, .ok (by decide), rfl⟩) <|
    .cons (.spawn (.ok (by decide))) .nil, ⟨_, .reject (by decide), rfl⟩⟩

/-- `release(a)` by context 1 (O3). -/
def r04a1 : SC := r04s3.set (releaseEff (r04s3.view 1) 1)
/-- `terminate` of context 1 (C7). -/
def r04a2 : SC := termEffC r04a1 1

/-- **R04, twin a** (`ok`). From the setup of `R04`: context 1 releases `a` and terminates;
context 0 joins context 1, then writes `X` through `root_X`. Expected: each step `ok`. Obtained:
each step `ok`. -/
theorem R04_twin_a : opStepC kFrames.toK (.release 1) 1 r04s3 (.ok r04a1) ∧
    TermStep kFrames.toK r04a1 1 (.ok r04a2) ∧ JoinStep r04a2 0 1 (.ok r04a2) ∧
    opStepC kFrames.toK (.write 0 [1, 2]) 0 r04a2
      (.ok (r04a2.set (write3Eff (r04a2.view 0) [1, 2]))) :=
  ⟨⟨_, .ok (by decide), rfl⟩, .ok (by decide), .ok (by decide) (by decide),
    ⟨_, .ok (by decide), rfl⟩⟩

/-- `split(root_X, [left], [right])`: `a1` (authority 1), `a2` (authority 2) (O2). -/
def r04b2 : SC := r04s1.set (splitEff (r04s1.view 0) 0 [[1], [2]])
/-- `spawn` of context 1 yielding `a1` (C4). -/
def r04b3 : SC := spawnEff r04b2 0 [1] []

/-- **R04, twin b** (`ok`). In place of the derivation: `split(root_X, [left], [right])` into `a1`,
`a2`; context 0 spawns context 1 yielding `a1`, then writes `right` through `a2`. Expected: each
step `ok`. Obtained: each step `ok`. -/
theorem R04_twin_b : opStepC kFrames.toK (.split 0 [[1], [2]]) 0 r04s1 (.ok r04b2) ∧
    SpawnStep r04b2 0 [1] [] (.ok r04b3) ∧
    opStepC kFrames.toK (.write 2 [2]) 0 r04b3 (.ok (r04b3.set (write3Eff (r04b3.view 0) [2]))) :=
  ⟨⟨_, .ok (by decide), rfl⟩, .ok (by decide), ⟨_, .ok (by decide), rfl⟩⟩

/-! ## R05: two observations in two contexts -/

/-- `write3(X)` through `root_X` (O10). -/
def r05s1 : SC := (SC.ofS3 (S3.init oneLocal)).set
  (write3Eff ((SC.ofS3 (S3.init oneLocal)).view 0) [0])
/-- `o1 := derive(root_X, Observe)`, authority 1 (O1). -/
def r05s2 : SC := r05s1.set (deriveEff (r05s1.view 0) 0 [0] .observe)
/-- `o2 := derive(root_X, Observe)`, authority 2 (O1). -/
def r05s3 : SC := r05s2.set (deriveEff (r05s2.view 0) 0 [0] .observe)
/-- `spawn` of context 1 yielding `o1` (C4). -/
def r05s4 : SC := spawnEff r05s3 0 [1] []
/-- `read3(X)` by context 0 through `o2` (O9). -/
def r05s5 : SC := r05s4.set (r05s4.view 0)

/-- The setup of `R05`. -/
def r05L : List Label :=
  [.kernel 0 (.write 0 [0]), .kernel 0 (.derive 0 [0] .observe),
   .kernel 0 (.derive 0 [0] .observe), .spawn 0 [1] []]

/-- **R05** (`ok`, `ok`). Base frame: a local `X`, initialized; `o1`, `o2 := derive(root_X,
Observe)`; context 0 spawns context 1 yielding `o1`; then context 0 reads `X` through `o2` and
context 1 reads `X` through `o1`. Expected: both `ok` by O9. Obtained: both `ok`. Twin:
`R05_twin`. -/
theorem R05 : LRun kFrames mutexLayout (SC.ofS3 (S3.init oneLocal), [], []) r05L
      (r05s4, [], []) ∧
    opStepC kFrames.toK (.read 2 [0]) 0 r05s4 (.ok r05s5) ∧
    opStepC kFrames.toK (.read 1 [0]) 1 r05s5 (.ok (r05s5.set (r05s5.view 1))) :=
  ⟨.cons (.kernel ⟨_, .ok (by decide), rfl⟩) <| .cons (.kernel ⟨_, .ok (by decide), rfl⟩) <|
    .cons (.kernel ⟨_, .ok (by decide), rfl⟩) <| .cons (.spawn (.ok (by decide))) .nil,
   ⟨_, .ok (by decide), rfl⟩, ⟨_, .ok (by decide), rfl⟩⟩

/-- **R05, twin** (`reject`). From the setup of `R05`, `o1` being active: context 0 derives
`derive(root_X, Modify)`. Expected: `reject` by O1.2, O1.3. Obtained: `reject`. -/
theorem R05_twin : opStepC kFrames.toK (.derive 0 [0] .modify) 0 r05s4 .reject :=
  ⟨_, .reject (by decide), rfl⟩

/-! ## R06: a transfer that would move an authority out of its anchor's frame -/

/-- `d := derive(root_D, Modify)`, authority 1 (O1); the local `D` (place 0) stays `Uninit`. -/
def r06s1 : SC := (SC.ofS3 (S3.init oneLocal)).set
  (deriveEff ((SC.ofS3 (S3.init oneLocal)).view 0) 0 [0] .modify)
/-- Context 0 enters frame 1 yielding `d`, with the locals `L`, `L2`, `X` (places 1, 2, 3; root
authorities 2, 3, 4) (O6). -/
def r06s2 : SC := enterEffC r06s1 0 [1] [(none, 0), (none, 0), (none, 0)]
/-- `write3(X)` through `root_X` (O10). -/
def r06s3 : SC := r06s2.set (write3Eff (r06s2.view 0) [3])
/-- `x := derive(root_X, Modify)`, authority 5, held by frame 1 (O1). -/
def r06s4 : SC := r06s3.set (deriveEff (r06s3.view 0) 4 [3] .modify)
/-- `store(x, L)` (O8). -/
def r06s5 : SC := storeEffC r06s4 0 5 1

/-- The setup of `R06`. -/
def r06L : List Label :=
  [.kernel 0 (.derive 0 [0] .modify), .kernel 0 (.enter [1] [(none, 0), (none, 0), (none, 0)]),
   .kernel 0 (.write 4 [3]), .kernel 0 (.derive 4 [3] .modify), .kernel 0 (.store 5 1)]

/-- **R06** (`reject`). Base frame: a local `D` of one leaf, `Uninit`; `d := derive(root_D,
Modify)`; context 0 enters frame 1 yielding `d`, with the locals `L`, `L2`, `X` of one leaf; in
frame 1: `X` initialized, `x := derive(root_X, Modify)`, `store(x, L)`; then `transfer(L, D)`.
Expected: `reject` by Spec 1 §63.7: the moved authority `x` would be held by `D`, a place of frame
0, while its effective anchor is in frame 1 (§44). Obtained: `reject`. Twin: `R06_twin`. -/
theorem R06 : LRun kFrames mutexLayout (SC.ofS3 (S3.init oneLocal), [], []) r06L
      (r06s5, [], []) ∧
    opStepC kFrames.toK (.transfer 1 0) 0 r06s5 .reject :=
  ⟨.cons (.kernel ⟨_, .ok (by decide), rfl⟩) <| .cons (.kernel (.ok (by decide))) <|
    .cons (.kernel ⟨_, .ok (by decide), rfl⟩) <| .cons (.kernel ⟨_, .ok (by decide), rfl⟩) <|
    .cons (.kernel (.ok (by decide))) .nil, .reject (by decide)⟩

/-- **R06, twin** (`ok`). From the setup of `R06`: `transfer(L, L2)`. Expected: `ok`. Obtained:
`ok`. -/
theorem R06_twin : opStepC kFrames.toK (.transfer 1 2) 0 r06s5 (.ok (transferEffC r06s5 0 1 2)) :=
  .ok (by decide)

/-! ## R07: a derivative kept by the creator blocks the yielded one -/

/-- `write3(X)` through `root_X` (O10). -/
def r07s1 : SC := r05s1
/-- `a := derive(root_X, Modify)`, authority 1 (O1). -/
def r07s2 : SC := r07s1.set (deriveEff (r07s1.view 0) 0 [0] .modify)
/-- `b := derive(a, Modify)`, authority 2, held by frame 0 (O1). -/
def r07s3 : SC := r07s2.set (deriveEff (r07s2.view 0) 1 [0] .modify)
/-- `spawn` of context 1 yielding `a`, `b` staying with frame 0 (C4). -/
def r07s4 : SC := spawnEff r07s3 0 [1] []
/-- Step 2: `write3(X)` by context 0 through `b` (O10). -/
def r07s5 : SC := r07s4.set (write3Eff (r07s4.view 0) [0])
/-- Step 3: `release(b)` by context 0 (O3). -/
def r07s6 : SC := r07s5.set (releaseEff (r07s5.view 0) 2)

/-- The setup of `R07`. -/
def r07L : List Label :=
  [.kernel 0 (.write 0 [0]), .kernel 0 (.derive 0 [0] .modify), .kernel 0 (.derive 1 [0] .modify),
   .spawn 0 [1] []]

/-- **R07** (`reject`, `ok`, `ok`, `ok`). Base frame: a local `X`, initialized; `a :=
derive(root_X, Modify)`; `b := derive(a, Modify)`; context 0 spawns context 1 yielding `a`, `b`
staying with frame 0 (the `spawn` `ok`, C4.3, C4.5). 1. context 1 writes `X` through `a`; 2.
context 0 writes `X` through `b`; 3. context 0 releases `b`; 4. context 1 writes `X` through `a`.
Expected: 1 `reject` by O10.1 (Spec 1 §43.3, `b` active); 2 `ok`; 3 `ok` by O3; 4 `ok`.
Obtained: the `spawn` `ok`; 1 `reject`; 2, 3, 4 `ok`. Twin: steps 1 and 4. -/
theorem R07 : LRun kFrames mutexLayout (SC.ofS3 (S3.init oneLocal), [], []) r07L
      (r07s4, [], []) ∧
    opStepC kFrames.toK (.write 1 [0]) 1 r07s4 .reject ∧
    opStepC kFrames.toK (.write 2 [0]) 0 r07s4 (.ok r07s5) ∧
    opStepC kFrames.toK (.release 2) 0 r07s5 (.ok r07s6) ∧
    opStepC kFrames.toK (.write 1 [0]) 1 r07s6 (.ok (r07s6.set (write3Eff (r07s6.view 1) [0]))) :=
  ⟨.cons (.kernel ⟨_, .ok (by decide), rfl⟩) <| .cons (.kernel ⟨_, .ok (by decide), rfl⟩) <|
    .cons (.kernel ⟨_, .ok (by decide), rfl⟩) <| .cons (.spawn (.ok (by decide))) .nil,
   ⟨_, .reject (by decide), rfl⟩, ⟨_, .ok (by decide), rfl⟩, ⟨_, .ok (by decide), rfl⟩,
   ⟨_, .ok (by decide), rfl⟩⟩

/-! ## R08: a relay of a derivative through an intermediate context -/

/-- `a := derive(root_X, Modify)`, authority 1 (O1). -/
def r08s2 : SC := r07s2
/-- `spawn` of context 1 yielding `a` (C4): initial frame 1. -/
def r08s3 : SC := spawnEff r08s2 0 [1] []
/-- `a₂ := derive(a, Modify)` by context 1, authority 2 (O1). -/
def r08s4 : SC := r08s3.set (deriveEff (r08s3.view 1) 1 [0] .modify)
/-- `spawn` of context 2 by context 1 yielding `a₂` (C4): initial frame 2, parented to frame 1. -/
def r08s5 : SC := spawnEff r08s4 1 [2] []
/-- Step 1: `write3(X)` by context 2 through `a₂` (O10). -/
def r08s6 : SC := r08s5.set (write3Eff (r08s5.view 2) [0])
/-- Step 2: `release(a₂)` by context 2 (O3). -/
def r08s7 : SC := r08s6.set (releaseEff (r08s6.view 2) 2)
/-- Step 3: `release(a)` by context 1 (O3). -/
def r08s8 : SC := r08s7.set (releaseEff (r08s7.view 1) 1)
/-- Step 4: `terminate` of context 1 (C7). -/
def r08s9 : SC := termEffC r08s8 1

/-- The setup of `R08`. -/
def r08L : List Label :=
  [.kernel 0 (.write 0 [0]), .kernel 0 (.derive 0 [0] .modify), .spawn 0 [1] [],
   .kernel 1 (.derive 1 [0] .modify), .spawn 1 [2] []]

/-- **R08** (six steps `ok`). Base frame: a local `X`, initialized; `a := derive(root_X, Modify)`;
context 0 spawns context 1 yielding `a`; context 1 derives `a₂ := derive(a, Modify)` and spawns
context 2 yielding `a₂`. 1. context 2 writes `X` through `a₂`; 2. context 2 releases `a₂`; 3.
context 1 releases `a`; 4. context 1 terminates; 5. context 0 joins context 1; 6. context 0
writes `X` through `root_X`, context 2 being live. Expected: each step `ok`; at step 4 (C7) the
initial frame of context 2 is reparented to frame 0 (C6); 5 by C8. Obtained: each step `ok`; after
step 4 the initial frame 2 of context 2 has parent frame 0; context 2 is live at step 6. Twin:
`R08_twin`. -/
theorem R08 : LRun kFrames mutexLayout (SC.ofS3 (S3.init oneLocal), [], []) r08L
      (r08s5, [], []) ∧
    opStepC kFrames.toK (.write 2 [0]) 2 r08s5 (.ok r08s6) ∧
    opStepC kFrames.toK (.release 2) 2 r08s6 (.ok r08s7) ∧
    opStepC kFrames.toK (.release 1) 1 r08s7 (.ok r08s8) ∧
    TermStep kFrames.toK r08s8 1 (.ok r08s9) ∧ r08s9.parC 2 = some 0 ∧
    JoinStep r08s9 0 1 (.ok r08s9) ∧ r08s9.Live 2 ∧
    opStepC kFrames.toK (.write 0 [0]) 0 r08s9 (.ok (r08s9.set (write3Eff (r08s9.view 0) [0]))) :=
  ⟨.cons (.kernel ⟨_, .ok (by decide), rfl⟩) <| .cons (.kernel ⟨_, .ok (by decide), rfl⟩) <|
    .cons (.spawn (.ok (by decide))) <| .cons (.kernel ⟨_, .ok (by decide), rfl⟩) <|
    .cons (.spawn (.ok (by decide))) .nil,
   ⟨_, .ok (by decide), rfl⟩, ⟨_, .ok (by decide), rfl⟩, ⟨_, .ok (by decide), rfl⟩,
   .ok (by decide), by decide, .ok (by decide) (by decide), by decide, ⟨_, .ok (by decide), rfl⟩⟩

/-- **R08, twin** (`reject`). Step 3 of `R08` before step 2: context 1 releases `a` while `a₂` is
active. Expected: `reject` by O3.3. Obtained: `reject`. -/
theorem R08_twin : opStepC kFrames.toK (.release 1) 1 r08s6 .reject :=
  ⟨_, .reject (by decide), rfl⟩

/-! ## R09: a transfer after the restitution of a derivative -/

/-- `write3(X)` through `root_X` (O10); `X` is place 0, `Y` place 1. -/
def r09s1 : SC := (SC.ofS3 (S3.init twoLocals)).set
  (write3Eff ((SC.ofS3 (S3.init twoLocals)).view 0) [0])
/-- `a := derive(root_X, Modify)`, authority 2 (O1). -/
def r09s2 : SC := r09s1.set (deriveEff (r09s1.view 0) 0 [0] .modify)
/-- `spawn` of context 1 yielding `a` (C4). -/
def r09s3 : SC := spawnEff r09s2 0 [2] []
/-- Step 1: `write3(X)` by context 1 through `a` (O10). -/
def r09s4 : SC := r09s3.set (write3Eff (r09s3.view 1) [0])
/-- Step 2: `release(a)` by context 1 (O3). -/
def r09s5 : SC := r09s4.set (releaseEff (r09s4.view 1) 2)

/-- The setup of `R09`. -/
def r09L : List Label :=
  [.kernel 0 (.write 0 [0]), .kernel 0 (.derive 0 [0] .modify), .spawn 0 [2] []]

/-- **R09** (three steps `ok`). Base frame: the locals `X`, initialized, and `Y` of the same shape,
`Uninit`; `a := derive(root_X, Modify)`; context 0 spawns context 1 yielding `a`. 1. context 1
writes `X` through `a`; 2. context 1 releases `a`; 3. context 0 transfers `X` into `Y`. Expected:
1, 2 `ok`; 3 `ok` by O4 (Spec 1 §63.1–§63.9). Obtained: each step `ok`. Twin: `R09_twin`. -/
theorem R09 : LRun kFrames mutexLayout (SC.ofS3 (S3.init twoLocals), [], []) r09L
      (r09s3, [], []) ∧
    opStepC kFrames.toK (.write 2 [0]) 1 r09s3 (.ok r09s4) ∧
    opStepC kFrames.toK (.release 2) 1 r09s4 (.ok r09s5) ∧
    opStepC kFrames.toK (.transfer 0 1) 0 r09s5 (.ok (transferEffC r09s5 0 0 1)) :=
  ⟨.cons (.kernel ⟨_, .ok (by decide), rfl⟩) <| .cons (.kernel ⟨_, .ok (by decide), rfl⟩) <|
    .cons (.spawn (.ok (by decide))) .nil,
   ⟨_, .ok (by decide), rfl⟩, ⟨_, .ok (by decide), rfl⟩, .ok (by decide)⟩

/-- **R09, twin** (`reject`). Step 3 of `R09` before step 2: context 0 transfers `X` into `Y`
while `a` is active. Expected: `reject` by Spec 1 §63.1 (§43.3). Obtained: `reject`. -/
theorem R09_twin : opStepC kFrames.toK (.transfer 0 1) 0 r09s4 .reject :=
  .reject (by decide)

/-! ## R10: a `store` after the restitution of a derivative -/

/-- `write3(X)` through `root_X` (O10); `X` is place 0, `Z` place 1. -/
def r10s1 : SC := r09s1
/-- `a := derive(root_X, Modify)`, authority 2 (O1). -/
def r10s2 : SC := r09s2
/-- `z := derive(root_Z, Modify)`, authority 3 (O1). -/
def r10s3 : SC := r10s2.set (deriveEff (r10s2.view 0) 1 [1] .modify)
/-- `spawn` of context 1 yielding `a` (C4). -/
def r10s4 : SC := spawnEff r10s3 0 [2] []
/-- Step 1: `write3(X)` by context 1 through `a` (O10). -/
def r10s5 : SC := r10s4.set (write3Eff (r10s4.view 1) [0])
/-- Step 2: `release(a)` by context 1 (O3). -/
def r10s6 : SC := r10s5.set (releaseEff (r10s5.view 1) 2)

/-- The setup of `R10`. -/
def r10L : List Label :=
  [.kernel 0 (.write 0 [0]), .kernel 0 (.derive 0 [0] .modify), .kernel 0 (.derive 1 [1] .modify),
   .spawn 0 [2] []]

/-- **R10** (three steps `ok`). Base frame: the locals `X` of one leaf, initialized, and `Z`; `a
:= derive(root_X, Modify)`; `z := derive(root_Z, Modify)`; context 0 spawns context 1 yielding
`a`. 1. context 1 writes `X` through `a`; 2. context 1 releases `a`; 3. context 0 stores `z` in
`X`. Expected: 1, 2 `ok`; 3 `ok` by O8 (Spec 1 §65.1–§65.5). Obtained: each step `ok`. Twin:
`R10_twin`. -/
theorem R10 : LRun kFrames mutexLayout (SC.ofS3 (S3.init twoLocals), [], []) r10L
      (r10s4, [], []) ∧
    opStepC kFrames.toK (.write 2 [0]) 1 r10s4 (.ok r10s5) ∧
    opStepC kFrames.toK (.release 2) 1 r10s5 (.ok r10s6) ∧
    opStepC kFrames.toK (.store 3 0) 0 r10s6 (.ok (storeEffC r10s6 0 3 0)) :=
  ⟨.cons (.kernel ⟨_, .ok (by decide), rfl⟩) <| .cons (.kernel ⟨_, .ok (by decide), rfl⟩) <|
    .cons (.kernel ⟨_, .ok (by decide), rfl⟩) <| .cons (.spawn (.ok (by decide))) .nil,
   ⟨_, .ok (by decide), rfl⟩, ⟨_, .ok (by decide), rfl⟩, .ok (by decide)⟩

/-- **R10, twin** (`reject`). Step 3 of `R10` before step 2: context 0 stores `z` in `X` while `a`
is active. Expected: `reject` by Spec 1 §65.2 (§43.3). Obtained: `reject`. -/
theorem R10_twin : opStepC kFrames.toK (.store 3 0) 0 r10s5 .reject :=
  .reject (by decide)

end Ern.Corpus.Concurrency
