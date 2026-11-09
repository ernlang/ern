import Ern.Concurrency.Corpus.MX
import Ern.Concurrency.EncapTraces

/-!
# Corpus of milestone 3: witnesses and corpus theorem

* `corpus-spec2-m3.md` §2 W-C22.3 (b): a transfer whose source is a strict structural subplace of
  `slot`, an `ok` kernel step excluded by `Encap`, after which `SlotInit` fails.
* `corpus-spec2-m3.md` §1 S17a, positive twin as written in the corpus (`endUse(slot)` kills the
  entry, then `endUse(lock)` is admitted by `Encap`).
* `corpus-spec2-m3.md` §3 `CrossContextConflictOnlyShared` and its witness on `MX₄`.

W-C22.2 is `Ern.Concurrency.Corpus.W_C22_2_encap` (block MX).
-/

namespace Ern.Concurrency.Corpus

open Ern.MemoryModel Ern.MemoryModel.Access Ern.MemoryModel.Access.Examples Ern.Concurrency
open Ern.Concurrency.Traces (L0)

/-! ## W-C22.3 (b) (`corpus-spec2-m3.md` §2) -/

/-- Statics (Spec 1 §47): those of `EncapTraces.sst` (`M = {slot = {a, b}, lock}`, `T` owned by
`slot`, `guarded = root_T`) and `6` the one-leaf place `Z`, `Uninit`. Root authorities: `0` of
`M`, `1` of `T` (held by `slot`), `2` of `Z`. -/
def wst : Statics :=
  [((none, none, 0), false), ((some 0, none, 0), false), ((some 1, none, 0), true),
   ((some 1, none, 0), true), ((some 0, none, 0), true), ((none, some 1, 0), true),
   ((none, none, 0), false)]

/-- The statics are well formed (Spec 1 §47). -/
theorem wst_ok : StaticsOK wst := by decide

/-- The contract of this witness: `lock` (place 4) is the only `SharedMutable` leaf. -/
abbrev KW : K := KC [4]

/-- Initial state, in `MX₃` once the entry `⟨1, none⟩` is registered. -/
def w0 : SC := SC.ofS3 (S3.init wst)
/-- `c0 : transfer(a, Z)` (O4). -/
def w1 : SC := transferEffC w0 0 2 6

/-- `corpus-spec2-m3.md` §2 W-C22.3 (b), `ok noyau / hors C22.3 (b)`: after the encapsulated step
`newMutex(guarded)`, `transfer(a, Z)` by context 0, `a` a strict structural subplace of `slot`, is
an `ok` step of Spec 1 §63 re-indexed and `Encap` excludes it; without the exclusion `SlotInit`
(WC4 C21.7) fails after the step. Positive twin: `Ern.Concurrency.EncapTraces.traceA`
(`transfer(M, M′)`). -/
theorem W_C22_3b_encap :
    EncapsulatedTrace KW L0 (w0, [], []) [.newMutex 0 1] (w0, [⟨1, none⟩], []) ∧
    opStepC KW (.transfer 2 6) 0 w0 (.ok w1) ∧
    ¬ Encap L0 (w0, [⟨1, none⟩]) (.kernel 0 (.transfer 2 6)) ∧ ¬ SlotInit w1 [⟨1, none⟩] := by
  have hn : NewMutexOk KW L0 [] w0 [] 0 1 (w0, [⟨1, none⟩]) := ⟨by decide, by decide, rfl⟩
  refine ⟨.cons trivial (.newMutex hn) .nil, ⟨by decide, .ok (by decide)⟩, fun h => ?_,
    fun h => ?_⟩
  · have := (h ⟨1, none⟩ (List.mem_singleton_self _) (by decide)).1
    revert this; decide
  · have := h ⟨1, none⟩ (List.mem_singleton_self _) (by decide)
    revert this; decide

/-! ## S17a, positive twin of the corpus (`corpus-spec2-m3.md` §1 S17a) -/

open Ern.Concurrency.EncapTraces in
/-- `c0 : endUse(slot)` from `EncapTraces.e2` (`MX₃`) (O12). -/
def eS : SC := EncapTraces.e2.set (endUseEff (EncapTraces.e2.view 0) 1)
/-- `c0 : endUse(lock)` (O12). -/
def eL : SC := eS.set (endUseEff (eS.view 0) 2)

/-- `corpus-spec2-m3.md` §1 S17a, positive twin, `ok`: from `MX₃` (`EncapTraces.e2`, reached by
the encapsulated trace `EncapTraces.traceMutex`), `endUse(slot)` is an `ok` step admitted by
`Encap` that kills the entry (§69 releases `guarded`); then `endUse(lock)` is an `ok` step
admitted by `Encap`, no entry being live. -/
theorem S17a_2_ok : opStepC K0 (.endUse 1) 0 EncapTraces.e2 (.ok eS) ∧
    Encap L0 (EncapTraces.e2, EncapTraces.reg1) (.kernel 0 (.endUse 1)) ∧
    ¬ (⟨4, none⟩ : SyncEntry).Live eS ∧ opStepC K0 (.endUse 2) 0 eS (.ok eL) ∧
    Encap L0 (eS, EncapTraces.reg1) (.kernel 0 (.endUse 2)) := by
  refine ⟨⟨by decide, _, .ok (by decide), rfl⟩, ?_, by decide, ⟨by decide, _, .ok (by decide), rfl⟩,
    fun e he hl => ?_⟩
  · exact (by decide : ∀ e ∈ EncapTraces.reg1, e.Live EncapTraces.e2 →
      ControlOf L0 EncapTraces.e2 e ≠ some 1 ∧
      OptP (slotOf EncapTraces.e2 e.guarded) (fun q => partOf EncapTraces.e2.P 1 q → 1 = q) True)
  · exact absurd hl (by rw [List.mem_singleton.1 he]; decide)

/-! ## The separation of the registries is needed by theorem 4 (Spec 1 §56; WC4 C13.7) -/

/-- An arena registry whose entry administers `T` with `internal = guarded` of the live entry of
`MX₃`: excluded on reached states by the unified guard (`NewArenaPreC.guard`, `lstep_adminSep`). -/
def arBad : ArenaReg := [⟨3, 3, [3], []⟩]
/-- `split(guarded, [T])` by context 0 (O2). -/
def xb1 : SC := x2.set (splitEff (x2.view 0) 3 [[3]])
/-- `store` of the block into `slot′` (place 5) by context 0 (O8). -/
def xb2 : SC := storeEffC xb1 0 x2.A.length 5

/-- Necessity of `AdminSep` for theorem 4 on the arena labels (Spec 1 §56: without the guard,
"simultaneous administration of the same `internal`"): in `MX₃`, which satisfies `KInvCA` and
`SyncState`, with an arena entry whose `internal` is the `guarded` of the live entry, `AdminSep`
fails, `issue` of `T` into `slot′` by context 0 is an `ok` step admitted by `Encap` (which has no
arena clause), and after it `GrantDiscipline` (WC4 C22) fails. -/
theorem adminSep_needed : KInvCA x2 ∧ SyncState L0 x2 regX ∧ ¬ AdminSep x2 regX arBad ∧
    IssueStepC KM x2 arBad 0 0 [3] 5
      (.ok (xb2, arBad.set 0 (Arena.issueMeta x2.flat ⟨3, 3, [3], []⟩ [3]))) ∧
    Encap L0 (x2, regX) (.issue 0 0 [3] 5) ∧ ¬ GrantDiscipline xb2 regX := by
  obtain ⟨hk, hs⟩ := init_inv (k := KM) (ddKC [2]) mxst_ok L0
  obtain ⟨hk', hs', -⟩ := trace_inv (ddKC [2]) mx3_trace hk hs
  refine ⟨hk', hs', fun h => h ⟨3, none⟩ (by decide) ⟨3, 3, [3], []⟩ (by decide) (by decide)
    (by decide) rfl, .ok (E := ⟨3, 3, [3], []⟩) rfl (by decide) (by decide)
    ⟨by decide, _, .ok (by decide), rfl⟩ ⟨by decide, .ok (by decide)⟩, trivial, fun h => ?_⟩
  exact (by decide : ¬ NoCoveringDesc xb2 3) (h ⟨3, none⟩ (by decide) (by decide) rfl)

/-! ## `CrossContextConflictOnlyShared` (`corpus-spec2-m3.md` §3) -/

/-- `CrossContextConflictOnlyShared` (`corpus-spec2-m3.md` §3): for two distinct live contexts, a
`writeShared` of `c` (Spec 1 §68) and a `read3`, `write3` or `writeShared` of `c′` (§66–§68), each
enabled on its own view (WC4 C2), share only `K.SharedMutable` leaves. -/
def CrossContextConflictOnlyShared (k : K) (s : SC) : Prop :=
  ∀ c c', s.Live c → s.Live c' → c ≠ c' → ∀ (a b : Nat) (L L' : List Nat),
    WriteSharedPre k (s.view c) a L →
    (Read3Pre (s.view c') b L' ∨ Write3Pre (s.view c') b L' ∨ WriteSharedPre k (s.view c') b L') →
    ∀ l ∈ L, l ∈ L' → k.SharedMutable l

/-- `CrossContextConflictOnlyShared` holds in every state (`corpus-spec2-m3.md` §3; Spec 1 §68.1,
O11.1: every leaf of a `writeShared` region is `K.SharedMutable`). With R4
(`Ern.Concurrency.r4_nonConflict`), the only cross-context conflict that the machine enables, at
the grain of abstract steps, goes through `writeShared` on a `SharedMutable` leaf. This is not a
proof of absence of data races (WC4 OB-C01–OB-C06). -/
theorem crossContextConflictOnlyShared (k : K) (s : SC) : CrossContextConflictOnlyShared k s :=
  fun _ _ _ _ _ _ _ _ _ hw _ l hl _ => hw.shared l hl

/-- Witness of `CrossContextConflictOnlyShared` (`corpus-spec2-m3.md` §3; O11.2, O9): in `MX₄`,
`writeShared(lock)` via `root_M` by context 0 and `read3(lock)` via `o1` by context 1 are both
enabled; their regions share exactly `lock`, which is `SharedMutable`. This is the surface of
OB-C03 and OB-C05. -/
theorem crossContextConflictOnlyShared_witness : x4.Live 0 ∧ x4.Live 1 ∧
    WriteSharedPre KM (x4.view 0) 0 [2] ∧ Read3Pre (x4.view 1) 4 [2] ∧ KM.SharedMutable 2 :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

end Ern.Concurrency.Corpus
