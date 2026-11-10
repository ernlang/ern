import Ern.Concurrency.Encap5
import Ern.Concurrency.Corpus.Handoff
import Ern.Concurrency.Corpus.GuardedRead

/-!
# Capability values on the handoff witnesses and on W-GR

`cap` (WC5 C43, `Ern.Concurrency.Cap`) of each context on the leaf in play, at each state of the
witnesses W-HO, W-HO′, W-HO″ (`corpus-spec2-m3.md` v4 §2 bis, `Corpus/Handoff.lean`) and W-GR
(§2 ter, `Corpus/GuardedRead.lean`), by `decide`; then `cap5` (brief of milestone 4, task 3) on
the same states with their synchronization registries. Each table lists the states of the witness
trace in order, one row per state, one column per context. The step between two rows is the label
of the trace theorem of the witness (`w_ho_trace`, `w_ho2_trace`, `w_ho3_trace`, `w_gr_trace`).
-/

namespace Ern.Concurrency.Corpus.CapValues

open Ern.MemoryModel.Access Ern.Concurrency Ern.Concurrency.Corpus
open Ern.Concurrency.Corpus.Handoff Ern.Concurrency.Corpus.GuardedRead
open Ern.Concurrency.Traces (L0)

/-- W-HO (`corpus-spec2-m3.md` v4 §2 bis): `cap` of contexts 0 and 1 on the leaf `left` (leaf 1)
of `X` at the states `t0` (initial), `t1` (`derive`), `t2` (`spawn c1` yielding `a`), `h1`
(`c1 : write3`), `h2` (`c1 : release(a)`), `h3` (`c0 : write3`). Drops: context 0 at the `spawn`
(its own step); context 1 at `release(a)` (its own step). -/
theorem w_ho_cap : [t0, t1, t2, h1, h2, h3].map (fun s => [cap s 0 1, cap s 1 1]) =
    [[some .modify, none], [some .modify, none], [none, some .modify], [none, some .modify],
     [some .modify, none], [some .modify, none]] := by decide

/-- W-HO′ (`corpus-spec2-m3.md` v4 §2 bis): `cap` of contexts 0 and 1 on the leaf of `X` at the
states `k0` (initial), `k1` (`derive a`), `k2` (`derive b`), `k3` (`spawn c1` yielding `a`), `k4`
(`c0 : write3` via `b`), `k5` (`c0 : release(b)`), `k6` (`c1 : write3` via `a`). Drop: context 0
at `release(b)` (its own step). -/
theorem w_ho2_cap : [k0, k1, k2, k3, k4, k5, k6].map (fun s => [cap s 0 0, cap s 1 0]) =
    [[some .modify, none], [some .modify, none], [some .modify, none], [some .modify, none],
     [some .modify, none], [none, some .modify], [none, some .modify]] := by decide

/-- W-HO″ (`corpus-spec2-m3.md` v4 §2 bis): `cap` of contexts 0, 1 and 2 on the leaf of `X` at the
states `k0` (initial), `m1` (`derive a`), `m2` (`spawn c1`), `m3` (`c1 : derive a₂`), `m4`
(`c1 : spawn c2`), `m5` (`c2 : write3`), `m6` (`c2 : release(a₂)`), `m7` (`c1 : release(a)`), `m8`
(`c1 : terminate`, then `c0 : join(c1)`), `m9` (`c0 : write3`). Drops: context 0 at its `spawn`,
context 1 at its `spawn`, context 2 at `release(a₂)`, context 1 at `release(a)`, each its own
step. -/
theorem w_ho3_cap :
    [k0, m1, m2, m3, m4, m5, m6, m7, m8, m9].map (fun s => [cap s 0 0, cap s 1 0, cap s 2 0]) =
    [[some .modify, none, none], [some .modify, none, none], [none, some .modify, none],
     [none, some .modify, none], [none, none, some .modify], [none, none, some .modify],
     [none, some .modify, none], [some .modify, none, none], [some .modify, none, none],
     [some .modify, none, none]] := by decide

/-- W-GR (`corpus-spec2-m3.md` v4 §2 ter): `cap` of contexts 0 and 1 on the leaf `T` (leaf 3) at
the states of block MX `x0` … `x4` (`MX₄`), then `gr1` (`c1 : read3(T)` via `guarded`), `gr2`
(`c0 : acquire(e)`), `gr3` (`c0 : write3(T)` via `g`). Drops: context 0 at `derive(root_M,
Observe)` (`x2` to `x3`, its own step); context 1 at `acquire(e)` (`gr1` to `gr2`), a step of
context 0. -/
theorem w_gr_cap : [x0, x1, x2, x3, x4, gr1, gr2, gr3].map (fun s => [cap s 0 3, cap s 1 3]) =
    [[some .modify, none], [some .modify, none], [some .modify, none], [some .observe, none],
     [some .observe, some .observe], [some .observe, some .observe], [some .modify, none],
     [some .modify, none]] := by decide

/-- `c0 : acquire(e)` directly from `MX₄`, without the read of W-GR (WC4 C16). -/
def gx : SC := deriveSyncEff x4 0 3

/-- Counterexample to L1 (WC5 C45, `OB-C17`) for `cap` on an `EncapsulatedTrace` from the initial
state: in W-GR (`corpus-spec2-m3.md` v4 §2 ter), the step `acquire(e)` of context 0, admitted by
`Encap`, lowers `cap` of context 1 on `T` from `Observe` to `none`. The same drop occurs from `MX₄`
without the read of step 1 (`gx`): `cap` of context 1 on `T` in `MX₄` rests on `guarded`, held by
`slot`, through `o1` (third clause of Spec 1 §43). -/
theorem cap_L1_counterexample :
    EncapsulatedTrace KM L0 (x0, [], [])
      [.kernel 0 (.derive 1 [3] .modify), .kernel 0 (.store 3 1), .newMutex 0 3,
       .kernel 0 (.derive 0 [1, 2] .observe), .spawn 0 [4] [], .kernel 1 (.read 3 [3])]
      (gr1, regX, []) ∧
    Encap L0 (gr1, regX) (.acquire 0 0) ∧
    LStep KM L0 (.acquire 0 0) (gr1, regX, []) (gr2, regG, []) ∧
    (Label.acquire 0 0).ctx = 0 ∧ cap gr1 1 3 = some .observe ∧ cap gr2 1 3 = none ∧
    LStep KM L0 (.acquire 0 0) (x4, regX, []) (gx, regG, []) ∧ cap x4 1 3 = some .observe ∧
    cap gx 1 3 = none :=
  ⟨mx4_trace.snoc (lbl := .kernel 1 (.read 3 [3])) (st' := (gr1, regX, [])) trivial
      (.kernel W_GR_1_ok), trivial, .acquire W_GR_2_ok, rfl, by decide, by decide,
    .acquire ⟨by decide, ⟨3, none⟩, rfl, by decide, by decide, rfl⟩, by decide, by decide⟩

/-! ## `cap5` -/

/-- `cap5` on W-HO, W-HO′ and W-HO″ (`corpus-spec2-m3.md` v4 §2 bis): their registries are empty,
so `cap5` coincides with `cap` (`w_ho_cap`, `w_ho2_cap`, `w_ho3_cap`). -/
theorem w_ho_cap5 :
    [t0, t1, t2, h1, h2, h3].map (fun s => [cap5 s [] 0 1, cap5 s [] 1 1]) =
      [t0, t1, t2, h1, h2, h3].map (fun s => [cap s 0 1, cap s 1 1]) ∧
    [k0, k1, k2, k3, k4, k5, k6].map (fun s => [cap5 s [] 0 0, cap5 s [] 1 0]) =
      [k0, k1, k2, k3, k4, k5, k6].map (fun s => [cap s 0 0, cap s 1 0]) ∧
    [k0, m1, m2, m3, m4, m5, m6, m7, m8, m9].map
        (fun s => [cap5 s [] 0 0, cap5 s [] 1 0, cap5 s [] 2 0]) =
      [k0, m1, m2, m3, m4, m5, m6, m7, m8, m9].map
        (fun s => [cap s 0 0, cap s 1 0, cap s 2 0]) := by
  decide

/-- `cap5` on W-GR (`corpus-spec2-m3.md` v4 §2 ter), contexts 0 and 1, leaf `T`, at the states of
`w_gr_cap` with their registries: `x2` appears before and after `newMutex(guarded)`. Drop: context
0 at `newMutex` (`Modify` to `none`, its own step: `guarded` ceases to be attributable). Context 1
has no `cap5` on `T` at any state; the drop of `cap` at `acquire(e)` (`cap_L1_counterexample`) does
not occur. -/
theorem w_gr_cap5 :
    [(x0, []), (x1, []), (x2, []), (x2, regX), (x3, regX), (x4, regX), (gr1, regX), (gr2, regG),
      (gr3, regG)].map (fun (st : SC × SyncReg) => [cap5 st.1 st.2 0 3, cap5 st.1 st.2 1 3]) =
    [[some .modify, none], [some .modify, none], [some .modify, none], [none, none], [none, none],
     [none, none], [none, none], [some .modify, none], [some .modify, none]] := by decide

end Ern.Concurrency.Corpus.CapValues
