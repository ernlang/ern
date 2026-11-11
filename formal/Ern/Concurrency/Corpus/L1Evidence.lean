import Ern.Concurrency.CapPreserve
import Ern.Concurrency.Corpus.Handoff
import Ern.Concurrency.Corpus.AR
import Ern.Concurrency.Traces

/-!
# L1 on steps of existing traces

Concrete instances of L1 on `cap5` (WC5 C45; `cap5_drop_own`): on steps of existing corpus traces
labelled `terminate`, `exitFrame`, `enterFrame`, `spawn`, `split`, `alloc`, `spawnVal` and `issue`,
no context other than the actor sees its `cap5` drop, on any leaf (brief of milestone 4, task 4),
by `decide`, independently of the proof of `cap5_drop_own`.
-/

namespace Ern.Concurrency.Corpus.L1Evidence

open Ern.MemoryModel.Access Ern.Concurrency Ern.Concurrency.Corpus Ern.Concurrency.Traces
open Ern.Concurrency.Corpus.Handoff

/-- The pairs (context, leaf) other than the actor whose `cap5` drops strictly from `(s, reg)` to
`(s', reg')`. -/
def otherDrops (s : SC) (reg : SyncReg) (s' : SC) (reg' : SyncReg) (actor : Nat) :
    List (Nat × Nat) :=
  (List.range s'.C.length).flatMap fun c => (List.range s'.P.length).filterMap fun l =>
    if c ≠ actor ∧ capRank (cap5 s' reg' c l) < capRank (cap5 s reg c l) then some (c, l)
    else none

/-- No drop for another context at: `terminate` and `exitFrame` of S1a (`p5`, `p6`, `p7`);
`enterFrame`, `spawn` and `exitFrame` of S1b (`b1` … `b5`); `split` and `spawn` of S13 (b) (`t0`,
`u1`, `u2`); `enterFrame`, `alloc`, `spawnVal` and `exitFrame` of S4 (`q0` … `q6`); `terminate` of
W-HO″ (`m7`, `m8`); `spawn` and both `issue` of S3 (`a5` … `a11`). -/
theorem no_other_drops :
    [otherDrops p5 [] p6 [] 1, otherDrops p6 [] p7 [] 0, otherDrops b1 [] b2 [] 0,
     otherDrops b3 [] b4 [] 0, otherDrops b4 [] b5 [] 0, otherDrops t0 [] u1 [] 0,
     otherDrops u1 [] u2 [] 0, otherDrops q0 [] q1 [] 0, otherDrops q3 [] q4 [] 0,
     otherDrops q4 [] q5 [] 0, otherDrops q5 [] q6 [] 0, otherDrops m7 [] m8 [] 1,
     otherDrops a5 regA a6 regA 0, otherDrops a7 regA8 a8 regA8 1,
     otherDrops a10 regA10 a11 regA10 0] =
    [[], [], [], [], [], [], [], [], [], [], [], [], [], [], []] := by decide

end Ern.Concurrency.Corpus.L1Evidence
