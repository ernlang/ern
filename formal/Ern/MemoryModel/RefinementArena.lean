import Ern.MemoryModel.Refinement
import Ern.MemoryModel.Arena
import Ern.MemoryModel.Access.Preserve.DeriveSplitRelease

/-!
# Refinement of the derived arena operations into the memory machine (spec v0, §82.7)

Source: `specs/ERN_Memory_Model_Specification_v0.md`, §82.7 with Part XIV (§76–§78), the §82
preamble, §82.2–§82.5 and §86.

* Library operations (`LOp`) and their `ok` steps (`LOpStep`): the kernel operations O1–O16 and
  the derived arena operations O17–O19 of `Ern.MemoryModel.Arena`.
* The kernel steps realizing a library step (`kexp`, `kexp_path`, Part XIV): none for `newArena`,
  `split` then `store` for `issue`, `derive` then `release` for `reset`. The raw operations of a
  library step (`lopsOf`) are the raw operations of these kernel steps (`ktrace`).
* Per derived operation: realization, reads, writes and lifetimes (`arena_newArena`,
  `arena_issue`, `arena_reset`, `reset_split`, `issue_pointer_sound`).
* Library runs translated into the memory machine with parameters fixed once per run
  (`LSimRun`): every such run is a kernel simulation run (`LSimRun.simRun`); `lsimulation`.
* §82.7: the machine trace of a library run is the trace of its kernel steps, and no kernel step
  after a legal `reset` uses an authority that the `reset` invalidated (`arena_realized`).

The sequential fragment only (§18, §29): no theorem here says anything about concurrency.
-/

namespace Ern.MemoryModel.RefinementArena

open Ern.MemoryModel.Access Ern.MemoryModel.Refinement Ern.MemoryModel.Arena

/-! ## Library operations and their kernel steps (Part XIV) -/

/-- An operation of a library run (Part XIV): a kernel operation O1–O16 of non-administrative
code (§60–§75), or one of the derived arena operations O17–O19 (§76–§78). -/
inductive LOp where
  /-- A kernel operation O1–O16 (§60–§75). -/
  | kernel (op : KOp)
  /-- O17 `newArena(storage, internal)` (§76); `others` are the other registries of live
  administrations consulted by the guard (§56, §76.4). -/
  | newArena (others : List (List Nat)) (storage internal : Nat)
  /-- O18 `issue(arena, region, destination)` of entry `i` (§77). -/
  | issue (i : Nat) (region : List Nat) (dst : Nat)
  /-- O19 `reset(arena)` of entry `i` (§78). -/
  | reset (i : Nat)

/-- The `ok` step of a library operation (Part XIV, §58): a kernel step leaves the registry
unchanged (§46); the arena operations are the derived operations (`NewArenaStep`, `IssueD`,
`ResetD`). -/
def LOpStep (k : K) : LOp → LState → LState → Prop
  | .kernel op, L, L' => OpStep k op L.kern L'.kern ∧ L'.arenas = L.arenas
  | .newArena others st i, L, L' => NewArenaStep others st i L (.ok L')
  | .issue i region dst, L, L' => IssueD k i region dst L (.ok L')
  | .reset i, L, L' => ResetD i L (.ok L')

/-- A labelled library step is a library step (Part XIV, §76–§78). -/
theorem LOpStep.lstep {k : K} {lop : LOp} {L L' : LState} (h : LOpStep k lop L L') :
    LStep k L L' := by
  cases lop with
  | kernel op =>
    have h' : OpStep k op L.kern L'.kern ∧ L'.arenas = L.arenas := h
    obtain ⟨s', ar⟩ := L'
    obtain ⟨hs, ha⟩ := h'
    dsimp only at hs ha
    subst ha
    exact .kernel hs.kstep
  | newArena => exact .newArena h
  | issue => exact .issue h
  | reset => exact .reset h

/-- Every kernel step is the `ok` step of a kernel operation (§57, §58); the representations
carried by `write` and `writeShared` are not read by the kernel (§10 ¶4). -/
theorem kstep_labelled {k : K} {s s' : S3} (h : KStep k s s') : ∃ op, OpStep k op s s' := by
  cases h with
  | derive h => exact ⟨.derive _ _ _, h⟩
  | split h => exact ⟨.split _ _, h⟩
  | release h => exact ⟨.release _, h⟩
  | transfer h => exact ⟨.transfer _ _, h⟩
  | depend h => exact ⟨.depend _ _, h⟩
  | enter h => exact ⟨.enter _ _, h⟩
  | exit h => exact ⟨.exit, h⟩
  | read h => exact ⟨.read _ _, h⟩
  | write h => exact ⟨.write _ _ fun _ _ => (0, none), h⟩
  | writeShared h => exact ⟨.writeShared _ _ fun _ _ => (0, none), h⟩
  | pin h => exact ⟨.pin _, h⟩
  | unpin h => exact ⟨.unpin _, h⟩
  | endUse h => exact ⟨.endUse _, h⟩
  | free h => exact ⟨.free _ _, h⟩
  | alloc h => exact ⟨.alloc _ _ _, h⟩
  | store h => exact ⟨.store _ _, h⟩

/-- Every library step is the `ok` step of a library operation (Part XIV, §76–§78): labelled
steps cover all library runs. -/
theorem LStep.labelled {k : K} {L L' : LState} (h : LStep k L L') : ∃ lop, LOpStep k lop L L' := by
  cases h with
  | kernel hk =>
    obtain ⟨op, h⟩ := kstep_labelled hk
    exact ⟨.kernel op, h, rfl⟩
  | newArena hs => exact ⟨.newArena _ _ _, hs⟩
  | issue hs => exact ⟨.issue _ _ _, hs⟩
  | reset hs => exact ⟨.reset _, hs⟩

/-- The kernel steps realizing a library operation from `L`, each with the kernel state it starts
from (Part XIV, §82.7): a kernel operation is its own step; `newArena` has none (§76: it registers
an administration without modifying the kernel); `issue` is `split` of `internal` on the region,
then `store` of the block, of fresh identity `|A|`, into the destination (§77); `reset` is
`derive` of `internal` at `Modify` over the storage, then `release` of the derived authority `|A|`
(§78). Without an entry, there is no step. -/
def kexp : LOp → LState → List (KOp × S3)
  | .kernel op, L => [(op, L.kern)]
  | .newArena .., _ => []
  | .issue i region dst, L => match L.arenas[i]? with
    | some E => [(.split E.internal [region], L.kern),
        (.store L.kern.A.length dst, splitEff L.kern E.internal [region])]
    | none => []
  | .reset i, L => match L.arenas[i]? with
    | some E => [(.derive E.internal (footprint L.kern.P E.storage) .modify, L.kern),
        (.release L.kern.A.length,
          deriveEff L.kern E.internal (footprint L.kern.P E.storage) .modify)]
    | none => []

/-- A sequence of `ok` kernel steps (§57, §58), each listed with the state it starts from. -/
inductive KPath (k : K) : S3 → List (KOp × S3) → S3 → Prop where
  | nil (s : S3) : KPath k s [] s
  | cons {op : KOp} {s s₁ s' : S3} {t : List (KOp × S3)} :
      OpStep k op s s₁ → KPath k s₁ t s' → KPath k s ((op, s) :: t) s'

/-- §82.7 (realization by O1–O16; Part XIV): every `ok` library step is the sequence of its
kernel steps `kexp`, from the kernel state before it to the kernel state after it. -/
theorem kexp_path {k : K} {lop : LOp} {L L' : LState} (h : LOpStep k lop L L') :
    KPath k L.kern (kexp lop L) L'.kern := by
  cases lop with
  | kernel op => exact .cons h.1 (.nil _)
  | newArena others st i =>
    rw [newArena_kernel (show NewArenaStep others st i L (.ok L') from h)]
    exact .nil _
  | issue i region dst =>
    have h' : IssueD k i region dst L (.ok L') := h
    cases h' with
    | ok hE _ _ hsp hst =>
      obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hsp
      simp only [kexp, hE]
      exact .cons hsp (.cons hst (.nil _))
  | reset i =>
    have h' : ResetD i L (.ok L') := h
    cases h' with
    | ok hE hd hrl _ =>
      obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hd
      simp only [kexp, hE]
      exact .cons hd (.cons hrl (.nil _))

/-- The steps of a kernel sequence keep the authorities of its first state (§42, §58), and each
is an `ok` step from the state listed with it. -/
theorem KPath.mem {k : K} {s s' : S3} {t : List (KOp × S3)} (hp : KPath k s t s') :
    ∀ q ∈ t, AKeep s q.2 ∧ ∃ s₁, OpStep k q.1 q.2 s₁ := by
  induction hp with
  | nil => intro q hq; cases hq
  | cons h _ ih =>
    intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · exact ⟨akeep_of_eq rfl, _, h⟩
    · obtain ⟨hk, hs⟩ := ih q hq
      exact ⟨(kstep_akeep h.kstep).trans hk, hs⟩

/-- The kernel steps of a library step start from states satisfying `WF3` and `NoDangling` when
the library state does (§49, §54): the states after `split` and after `derive` keep both
(§60, §61). -/
theorem kexp_inv {k : K} {lop : LOp} {L L' : LState} (h : LOpStep k lop L L') (hw : WF3 L.kern)
    (hnd : NoDangling L.kern) : ∀ q ∈ kexp lop L, WF3 q.2 ∧ NoDangling q.2 := by
  cases lop with
  | kernel op =>
    intro q hq
    rw [kexp, List.mem_singleton] at hq
    subst hq
    exact ⟨hw, hnd⟩
  | newArena => intro q hq; cases hq
  | issue i region dst =>
    have h' : IssueD k i region dst L (.ok L') := h
    cases h' with
    | ok hE _ _ hsp _ =>
      have e := (Guarded.ok_iff.1 hsp).2
      subst e
      intro q hq
      simp only [kexp, hE, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact ⟨hw, hnd⟩
      · exact ⟨split_preserves_wf3 hw hsp, split_preserves_noDangling hnd hsp⟩
  | reset i =>
    have h' : ResetD i L (.ok L') := h
    cases h' with
    | ok hE hd _ _ =>
      have e := (Guarded.ok_iff.1 hd).2
      subst e
      intro q hq
      simp only [kexp, hE, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact ⟨hw, hnd⟩
      · exact ⟨derive_preserves_wf3 hw hd, derive_preserves_noDangling hnd hd⟩

/-! ## Raw operations of library steps (§82 preamble, §82.7) -/

section Trace

variable {Ty : Type}

/-- The raw operations realizing a sequence of kernel steps (§82 preamble, §20.3): the raw
operations `opsOf` of each step, in the memory state reached by the previous ones. -/
def ktrace (π : Params Ty) : List (KOp × S3) → Machine.State → List (Machine.Op Ty)
  | [], _ => []
  | (op, s3) :: t, s2 => opsOf π op s3 s2 ++ ktrace π t (run s2 (opsOf π op s3 s2))

/-- The raw operations realizing a library step (§82.7): those of its kernel steps. -/
def lopsOf (π : Params Ty) (lop : LOp) (L : LState) (s2 : Machine.State) : List (Machine.Op Ty) :=
  ktrace π (kexp lop L) s2

/-- The raw operations of composed kernel sequences are composed (§20.3 ¶3). -/
theorem ktrace_append (π : Params Ty) (t t' : List (KOp × S3)) (s2 : Machine.State) :
    ktrace π (t ++ t') s2 = ktrace π t s2 ++ ktrace π t' (run s2 (ktrace π t s2)) := by
  induction t generalizing s2 with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨op, s3⟩ := p
    simp only [List.cons_append, ktrace, ih, run_append, List.append_assoc]

/-- The obligations of each kernel step of a sequence (§20.3, §82; `StepObl`), in the memory
state reached by the previous ones. -/
def KObl (k : K) (C : Nat → Nat → Prop) (ObR : Machine.ReadOblSpec Ty)
    (ObW : Machine.WriteOblSpec Ty) (π : Params Ty) : List (KOp × S3) → Machine.State → Prop
  | [], _ => True
  | (op, s3) :: t, s2 =>
    StepObl k C ObR ObW π op s3 s2 ∧ KObl k C ObR ObW π t (run s2 (opsOf π op s3 s2))

/-- The memory state realizing the initial state (§47, §82 preamble; `repr_init`): the creations
of the static allocations, then the writes of the static leaves declared `Init`. -/
def minit (π : Params Ty) (statics : Statics) : Machine.State :=
  run Machine.State.empty (initOps π.pl π.geom π.rtok π.L π.ty π.ival statics)

end Trace

/-- Realization of a kernel sequence (§82 preamble, R6 of each step): from states satisfying
`WF3` and `NoDangling`, under the obligations of each step, the raw operations of the sequence
form an execution of `ok` raw steps and `Repr` holds after it. -/
theorem r6_path {Ty : Type} {k : K} {C : Nat → Nat → Prop} {ObR : Machine.ReadOblSpec Ty}
    {ObW : Machine.WriteOblSpec Ty} {π : Params Ty} (hπ : ParamsOK C π) {s3 s3' : S3}
    {t : List (KOp × S3)} (hp : KPath k s3 t s3') :
    ∀ {s2 : Machine.State}, (∀ q ∈ t, WF3 q.2 ∧ NoDangling q.2) → KObl k C ObR ObW π t s2 →
      Refinement.Repr π.L π.rtok s3 s2 →
      Machine.Exec C ObR ObW (ktrace π t s2) s2 (run s2 (ktrace π t s2)) ∧
        Refinement.Repr π.L π.rtok s3' (run s2 (ktrace π t s2)) := by
  induction hp with
  | nil => intro s2 _ _ hR; exact ⟨.nil _, hR⟩
  | cons h _ ih =>
    intro s2 hinv hob hR
    obtain ⟨hw, hnd⟩ := hinv _ (List.mem_cons_self ..)
    obtain ⟨hob₁, hob₂⟩ := hob
    obtain ⟨hex, hR₁⟩ := r6 hπ hR hw hnd h hob₁
    obtain ⟨hex', hR'⟩ := ih (fun q hq => hinv q (List.mem_cons_of_mem _ hq)) hob₂ hR₁
    simp only [ktrace]
    rw [run_append]
    exact ⟨exec_append hex hex', hR'⟩

/-- Realization of a library step (§82.7, §82 preamble): from a library state whose kernel
state satisfies `WF3` and `NoDangling`, under the obligations of its kernel steps, the raw
operations of an `ok` library step form an execution of `ok` raw steps and `Repr` holds after
it. -/
theorem lr6 {Ty : Type} {k : K} {C : Nat → Nat → Prop} {ObR : Machine.ReadOblSpec Ty}
    {ObW : Machine.WriteOblSpec Ty} {π : Params Ty} {lop : LOp} {L L' : LState}
    {s2 : Machine.State} (hπ : ParamsOK C π) (hR : Refinement.Repr π.L π.rtok L.kern s2)
    (hw : WF3 L.kern) (hnd : NoDangling L.kern) (h : LOpStep k lop L L')
    (hob : KObl k C ObR ObW π (kexp lop L) s2) :
    Machine.Exec C ObR ObW (lopsOf π lop L s2) s2 (run s2 (lopsOf π lop L s2)) ∧
      Refinement.Repr π.L π.rtok L'.kern (run s2 (lopsOf π lop L s2)) :=
  r6_path hπ (kexp_path h) (kexp_inv h hw hnd) hob hR

/-! ## R4 transported by the derived operations (§82.5, §54) -/

/-- The conclusion of R4 (`r4_no_dead_cover`, §82.5, §54): every leaf covered by an active
authority of `s3` is an existing leaf whose allocation in `s2` is live and contains its range. -/
def LiveCover (L : Layout) (s3 : S3) (s2 : Machine.State) : Prop :=
  ∀ (j : Nat) (y : Authority), s3.A[j]? = some y → y.active = true → ∀ l ∈ y.footprint,
    l < s3.P.length ∧ isLeaf s3.P l ∧
      AllocP s2 (L l).alloc fun a => a.live = true ∧ (L l).off + (L l).len ≤ a.size

/-- R4 (§82.5, §54): `Repr`, `WF3` and `NoDangling` give `LiveCover` (`r4_no_dead_cover`). -/
theorem liveCover_of {L : Layout} {rtok : Nat → Nat} {s3 : S3} {s2 : Machine.State}
    (hR : Refinement.Repr L rtok s3 s2) (hw : WF3 s3) (hnd : NoDangling s3) :
    LiveCover L s3 s2 :=
  fun _ _ hy ya _ hl => r4_no_dead_cover hR hw hnd hy ya hl

/-- A live allocation containing a range stays so along raw operations without deallocation
(§13 ¶3, §16 ¶3). -/
theorem liveWithin_run {Ty : Type} {s2 : Machine.State} (hwf : Machine.WF s2)
    {os : List (Machine.Op Ty)} (hn : ∀ o ∈ os, NoDealloc o) {i off len : Nat}
    (h : AllocP s2 i fun a => a.live = true ∧ off + len ≤ a.size) :
    AllocP (run s2 os) i fun a => a.live = true ∧ off + len ≤ a.size := by
  obtain ⟨a, ha, hl, hsz⟩ := h
  obtain ⟨a', ha', hl'⟩ := live_run os s2 hwf hn ⟨a, ha, hl⟩
  obtain ⟨a'', ha'', -, e, -⟩ := dom_run os s2 hwf i a ha
  rw [ha'] at ha''
  cases ha''
  exact ⟨a', ha', hl', by rw [e]; exact hsz⟩

/-- The raw operations of `store` deallocate nothing (§65, §16). -/
theorem storeOps_noDealloc {Ty : Type} (pe : PtrEnc) (s2 : Machine.State) (L : Layout)
    (ty : Nat → Ty) (s3 : S3) (a p : Nat) : ∀ o ∈ storeOps pe s2 L ty s3 a p, NoDealloc o := by
  unfold storeOps
  split
  · exact writeOps_noDealloc _ _ _ _ _
  · intro o ho; cases ho

/-! ## The derived operations (§76–§78, §82.2–§82.5, §82.7) -/

/-- R1, R2, R4, R6 for `newArena` (§76 `ok` effect, §82.7): no kernel step and no raw operation
(no read, no write; the registry update has no machine realization, reading recorded at
`arena_realized`); `Repr` and `LiveCover` hold after it as before it. -/
theorem arena_newArena {Ty : Type} {π : Params Ty} {others : List (List Nat)} {st i : Nat}
    {L L' : LState} {s2 : Machine.State} (h : NewArenaStep others st i L (.ok L')) :
    kexp (.newArena others st i) L = [] ∧ lopsOf π (.newArena others st i) L s2 = [] ∧
    (Refinement.Repr π.L π.rtok L.kern s2 → Refinement.Repr π.L π.rtok L'.kern s2) ∧
    (LiveCover π.L L.kern s2 → LiveCover π.L L'.kern s2) := by
  rw [newArena_kernel h]
  exact ⟨rfl, rfl, id, id⟩

/-- The raw operations of the derived `issue` of entry `i` (§77, Part XIV): `split` realizes none
(§61), so they are those of `store` of the block into the destination (§65, §82.3). -/
theorem issue_ops {Ty : Type} {π : Params Ty} {L : LState} {i : Nat} {region : List Nat}
    {dst : Nat} {E : ArenaEntry} {s2 : Machine.State} (hE : L.arenas[i]? = some E) :
    lopsOf π (.issue i region dst) L s2 =
      storeOps π.pe s2 π.L π.ty (splitEff L.kern E.internal [region]) L.kern.A.length dst := by
  simp only [lopsOf, kexp, hE, ktrace, List.append_nil]
  rfl

/-- R1, R2, R4, R6 for the derived `issue` of entry `i` (§77, Part XIV, §82.2, §82.3, §82.5,
§82.7). Under `Repr` and `WF3`, for an `ok` issue, when the block's region has a reference address
(`PtrDecided`, not a clause of the spec, see `r6_store`) and the parametric obligations of the
write hold: `split` realizes no raw operation and `store` realizes exactly one raw write, of the
range of the destination, with the bytes of the reference to the block (address `ad`, provenance
the allocation of its effective anchor); no read (R1); the write is an `ok` raw step (R2) and
`Repr` holds after it (R6); `LiveCover` (R4) is kept, the new block included. -/
theorem arena_issue {Ty : Type} {k : K} {C : Nat → Nat → Prop} {ObR : Machine.ReadOblSpec Ty}
    {ObW : Machine.WriteOblSpec Ty} {π : Params Ty} {L L' : LState} {i : Nat}
    {region : List Nat} {dst : Nat} {E : ArenaEntry} {s2 : Machine.State}
    (hE : L.arenas[i]? = some E) (hR : Refinement.Repr π.L π.rtok L.kern s2) (hw : WF3 L.kern)
    (hs : IssueD k i region dst L (.ok L'))
    (hpd : PtrDecided π.L (splitEff L.kern E.internal [region]) L.kern.A.length)
    (hob : OblAlong ObR ObW s2
      (storeOps π.pe s2 π.L π.ty (splitEff L.kern E.internal [region]) L.kern.A.length dst)) :
    (∃ ad, ptrAddr s2 π.L (splitEff L.kern E.internal [region]) L.kern.A.length = some ad ∧
      lopsOf π (.issue i region dst) L s2 = [.write (leafAcc s2 π.L .write dst) (π.ty dst)
        (π.pe.enc ad (some (anchorAlloc π.L (splitEff L.kern E.internal [region])
          L.kern.A.length)))]) ∧
    Machine.Exec C ObR ObW (lopsOf π (.issue i region dst) L s2) s2
      (run s2 (lopsOf π (.issue i region dst) L s2)) ∧
    Refinement.Repr π.L π.rtok L'.kern (run s2 (lopsOf π (.issue i region dst) L s2)) ∧
    (LiveCover π.L L.kern s2 →
      LiveCover π.L L'.kern (run s2 (lopsOf π (.issue i region dst) L s2))) := by
  rw [issue_ops hE]
  cases hs with
  | @ok E' s₁ s₂ hE' _ _ hsp hst =>
  rw [hE] at hE'
  cases hE'
  have e₁ := (Guarded.ok_iff.1 hsp).2
  subst e₁
  have hpre := (Guarded.ok_iff.1 hsp).1
  have hw₁ := split_preserves_wf3 hw hsp
  obtain ⟨hex, hR₂⟩ := r6_store (C := C) (r6_split hR hsp) hw₁ hst hpd hob
  have e₂ := (Guarded.ok_iff.1 hst).2
  subst e₂
  obtain ⟨ad, had⟩ := ptrAddr_isSome (s2 := s2) hpd
  refine ⟨⟨ad, had, by simp only [storeOps, had, writeOps, List.map_cons, List.map_nil]⟩, hex,
    hR₂, ?_⟩
  unfold LiveCover
  intro hlc j y hy ya l hl
  have hwf := hR.adm.wf
  have hn := storeOps_noDealloc π.pe s2 π.L π.ty (splitEff L.kern E.internal [region])
    L.kern.A.length dst
  dsimp only at hy ⊢
  rw [← issueKEff_eq] at hy ⊢
  have hA : (issueKEff L.kern E region dst).A =
      L.kern.A ++ [⟨.modify, some E.internal, region, .place dst, true⟩] := rfl
  rw [hA] at hy
  show l < L.kern.P.length ∧ isLeaf L.kern.P l ∧ _
  by_cases hj : j < L.kern.A.length
  · rw [List.getElem?_append_left hj] at hy
    obtain ⟨h1, h2, h3⟩ := hlc j y hy ya l hl
    exact ⟨h1, h2, liveWithin_run hwf hn h3⟩
  · rw [List.getElem?_append_right (by omega)] at hy
    have hly : l ∈ region := by
      cases h0 : j - L.kern.A.length with
      | zero =>
        rw [h0] at hy
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hy
        rw [← hy] at hl
        exact hl
      | succ n => rw [h0] at hy; simp at hy
    obtain ⟨hin, -⟩ := hpre.within region (List.mem_singleton_self _) l hly
    obtain ⟨yi, hyi, yia⟩ := hpre.active
    have hl' : l ∈ yi.footprint := by simpa [S3.afp, hyi] using hin
    obtain ⟨h1, h2, h3⟩ := hlc _ yi hyi yia l hl'
    exact ⟨h1, h2, liveWithin_run hwf hn h3⟩

/-- The issued region and the memory machine (§82.7, §82.3, §77): after an `ok` issue, under
`Repr`, `WF3` and `NoDangling`, the address `ad` of the reference to the block and the obligation
of the encoding for it (the pointer-size rule and `PtrEncAt`, hypotheses of
`pointer_sound_store`), the range of the destination decodes to `ad`, each of its bytes carries the
provenance of the allocation of the block's effective anchor, and every leaf of the region lies in
that allocation, live and containing the range of the leaf. -/
theorem issue_pointer_sound {Ty : Type} {k : K} {π : Params Ty} {L L' : LState} {i : Nat}
    {region : List Nat} {dst : Nat} {E : ArenaEntry} {s2 : Machine.State} {ad : Nat}
    (hE : L.arenas[i]? = some E) (hR : Refinement.Repr π.L π.rtok L.kern s2) (hw : WF3 L.kern)
    (hnd : NoDangling L.kern) (hs : IssueD k i region dst L (.ok L'))
    (had : ptrAddr s2 π.L (splitEff L.kern E.internal [region]) L.kern.A.length = some ad)
    (hsz : (π.L dst).len = π.pe.size)
    (henc : PtrEncAt π.pe ad
      (some (anchorAlloc π.L (splitEff L.kern E.internal [region]) L.kern.A.length))) :
    π.pe.decode (bytesOf (run s2 (lopsOf π (.issue i region dst) L s2)) π.L dst) = ad ∧
    (∀ n, n < (π.L dst).len → (bytesOf (run s2 (lopsOf π (.issue i region dst) L s2)) π.L dst n).2 =
      some (anchorAlloc π.L (splitEff L.kern E.internal [region]) L.kern.A.length)) ∧
    ∀ l ∈ region,
      (π.L l).alloc = anchorAlloc π.L (splitEff L.kern E.internal [region]) L.kern.A.length ∧
      AllocP s2 (π.L l).alloc fun al => al.live = true ∧ (π.L l).off + (π.L l).len ≤ al.size := by
  rw [issue_ops hE]
  cases hs with
  | @ok E' s₁ s₂ hE' _ _ hsp hst =>
  rw [hE] at hE'
  cases hE'
  have e₁ := (Guarded.ok_iff.1 hsp).2
  subst e₁
  have h := pointer_sound_store (Ty := Ty) (ty := π.ty) (r6_split hR hsp)
    (split_preserves_wf3 hw hsp) (split_preserves_noDangling hnd hsp) hst had hsz henc
  have hafp : (splitEff L.kern E.internal [region]).afp L.kern.A.length = region := by
    simp [S3.afp, split_block]
  exact ⟨h.1, h.2.1, fun l hl => h.2.2.1 l (by rw [hafp]; exact hl)⟩

/-- The raw operations of the derived `reset` (§78, Part XIV): `derive` and `release` realize
none (§60, §62: no storage is created or deallocated). -/
theorem reset_ops {Ty : Type} {π : Params Ty} {L : LState} {i : Nat} {s2 : Machine.State} :
    lopsOf π (.reset i) L s2 = [] := by
  simp only [lopsOf, kexp]
  split <;> rfl

/-- R1, R2, R4, R6 for the derived `reset` (§78, Part XIV, §82.5, §82.7): no raw operation (no
read, no write; the storage stays allocated, §17 "logical invalidation"); `Repr` and `LiveCover`
hold after it as before it. -/
theorem arena_reset {Ty : Type} {π : Params Ty} {L L' : LState} {i : Nat} {s2 : Machine.State}
    (hs : ResetD i L (.ok L')) :
    lopsOf π (.reset i) L s2 = [] ∧
    (Refinement.Repr π.L π.rtok L.kern s2 → Refinement.Repr π.L π.rtok L'.kern s2) ∧
    (LiveCover π.L L.kern s2 → LiveCover π.L L'.kern s2) := by
  cases hs with
  | @ok E s₁ s₂ hE hd hrl _ =>
  refine ⟨reset_ops, fun hR => r6_release (r6_derive hR hd) hrl, ?_⟩
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hd
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hrl
  unfold LiveCover
  intro hlc j y hy ya l hl
  dsimp only at hy ⊢
  rw [← resetKEff_eq] at hy ⊢
  have hA : (resetKEff L.kern E).A = L.kern.A ++
      [⟨.modify, some E.internal, footprint L.kern.P E.storage, .frame L.kern.top, false⟩] := rfl
  rw [hA] at hy
  show l < L.kern.P.length ∧ isLeaf L.kern.P l ∧ _
  by_cases hj : j < L.kern.A.length
  · rw [List.getElem?_append_left hj] at hy
    exact hlc j y hy ya l hl
  · rw [List.getElem?_append_right (by omega)] at hy
    cases h0 : j - L.kern.A.length with
    | zero => rw [h0] at hy; simp at hy; rw [← hy] at ya; cases ya
    | succ n => rw [h0] at hy; simp at hy

/-- `reset` through `split` (Part XIV: "through `derive` or `split`"; §61, §62): on a state
satisfying `WF3` and `I1` (parts of `KInv`, §57, under which `derive` and `split` have the same
preconditions, `derive_iff_split`), the derivation of an `ok` reset may be performed by `split`
of `internal` on the storage: `split` then `release` reach the same kernel state, and realize no
raw operation either. -/
theorem reset_split {Ty : Type} {k : K} {π : Params Ty} {L L' : LState} {i : Nat}
    {E : ArenaEntry} {s2 : Machine.State} (hE : L.arenas[i]? = some E) (hw : WF3 L.kern)
    (h1 : I1 L.kern) (hs : ResetD i L (.ok L')) :
    KPath k L.kern [(.split E.internal [footprint L.kern.P E.storage], L.kern),
      (.release L.kern.A.length, splitEff L.kern E.internal [footprint L.kern.P E.storage])]
      L'.kern ∧
    ktrace π [(.split E.internal [footprint L.kern.P E.storage], L.kern),
      (.release L.kern.A.length, splitEff L.kern E.internal [footprint L.kern.P E.storage])]
      s2 = [] := by
  refine ⟨?_, rfl⟩
  cases hs with
  | @ok E' s₁ s₂ hE' hd hrl _ =>
  rw [hE] at hE'
  cases hE'
  obtain ⟨hdp, rfl⟩ := Guarded.ok_iff.1 hd
  exact .cons (.ok ((derive_iff_split k hw h1 hdp.leaves).1 hdp)) (.cons hrl (.nil _))

/-! ## Library runs in the memory machine (§82 preamble, §82.7) -/

/-- Library runs from `LState.init statics` translated into the memory machine, with the contract
`K`, the deallocation compatibility `C`, the obligations `ObR`, `ObW` and the parameters `π` fixed
once for the run (§20.3 ¶3, §82, §82.7): the initial state with the creations and writes of the
statics (as `SimRun.init`); then each `ok` library step, kernel steps and arena operations
interleaved, from a library state whose kernel state satisfies `WF3` and `NoDangling` (parts of
the kernel invariant, §57, as in `SimRun`), under the obligations of its kernel steps, followed by
the raw operations of its kernel steps. -/
inductive LSimRun {Ty : Type} (k : K) (C : Nat → Nat → Prop) (ObR : Machine.ReadOblSpec Ty)
    (ObW : Machine.WriteOblSpec Ty) (statics : Statics) (π : Params Ty) :
    LState → Machine.State → Prop where
  | init : StaticsOK statics →
      NewLayout π.L (S3.init statics).P 0 0 π.geom (rootIdx (statics.map (·.1))) →
      OblAlong ObR ObW (run Machine.State.empty (allocOps (Ty := Ty) π.pl π.geom π.rtok 0
        Machine.State.empty (rootIdx (statics.map (·.1))))) (writeOps (run Machine.State.empty
          (allocOps (Ty := Ty) π.pl π.geom π.rtok 0 Machine.State.empty
            (rootIdx (statics.map (·.1))))) π.L π.ty π.ival (initLeaves statics)) →
      LSimRun k C ObR ObW statics π (LState.init statics) (minit π statics)
  | step {lop : LOp} {L L' : LState} {s2 : Machine.State} : LSimRun k C ObR ObW statics π L s2 →
      WF3 L.kern → NoDangling L.kern → LOpStep k lop L L' → KObl k C ObR ObW π (kexp lop L) s2 →
      LSimRun k C ObR ObW statics π L' (run s2 (lopsOf π lop L s2))

/-- A kernel simulation run extends along a kernel sequence whose steps start from states
satisfying `WF3` and `NoDangling`, under their obligations (§82 preamble). -/
theorem simRun_path {Ty : Type} {k : K} {C : Nat → Nat → Prop} {ObR : Machine.ReadOblSpec Ty}
    {ObW : Machine.WriteOblSpec Ty} {statics : Statics} {π : Params Ty} {s3 s3' : S3}
    {t : List (KOp × S3)} (hp : KPath k s3 t s3') :
    ∀ {s2 : Machine.State}, SimRun k C ObR ObW statics π s3 s2 →
      (∀ q ∈ t, WF3 q.2 ∧ NoDangling q.2) → KObl k C ObR ObW π t s2 →
      SimRun k C ObR ObW statics π s3' (run s2 (ktrace π t s2)) := by
  induction hp with
  | nil => intro s2 h _ _; exact h
  | cons h _ ih =>
    intro s2 hs hinv hob
    obtain ⟨hw, hnd⟩ := hinv _ (List.mem_cons_self ..)
    obtain ⟨hob₁, hob₂⟩ := hob
    have := ih (SimRun.step hs hw hnd h hob₁) (fun q hq => hinv q (List.mem_cons_of_mem _ hq))
      hob₂
    simp only [ktrace]
    rw [run_append]
    exact this

/-- §82.7 (realization by O1–O16): every translated library run is a translated kernel run of its
kernel steps, with the same parameters, reaching the same kernel and memory states. -/
theorem LSimRun.simRun {Ty : Type} {k : K} {C : Nat → Nat → Prop} {ObR : Machine.ReadOblSpec Ty}
    {ObW : Machine.WriteOblSpec Ty} {statics : Statics} {π : Params Ty} {L : LState}
    {s2 : Machine.State} (h : LSimRun k C ObR ObW statics π L s2) :
    SimRun k C ObR ObW statics π L.kern s2 := by
  induction h with
  | init hst hlay hob => exact SimRun.init hst hlay hob
  | step _ hw hnd hs hob ih => exact simRun_path (kexp_path hs) ih (kexp_inv hs hw hnd) hob

/-- The library states of a translated library run are library-reachable (Part XIV, §82.7). -/
theorem LSimRun.lreach {Ty : Type} {k : K} {C : Nat → Nat → Prop} {ObR : Machine.ReadOblSpec Ty}
    {ObW : Machine.WriteOblSpec Ty} {statics : Statics} {π : Params Ty} {L : LState}
    {s2 : Machine.State} (h : LSimRun k C ObR ObW statics π L s2) : LReach k statics L := by
  induction h with
  | init => exact .init
  | step _ _ _ hs _ ih => exact .step ih hs.lstep

/-- Simulation of library runs (§82 preamble, §82.7, §9 ¶9): for every translated library run,
the memory state is reached from the empty state by an execution of `ok` raw steps, it is related
to the kernel state by `Repr`, and the library state is library-reachable. -/
theorem lsimulation {Ty : Type} {k : K} {C : Nat → Nat → Prop} {ObR : Machine.ReadOblSpec Ty}
    {ObW : Machine.WriteOblSpec Ty} {statics : Statics} {π : Params Ty} {L : LState}
    {s2 : Machine.State} (hπ : ParamsOK C π) (h : LSimRun k C ObR ObW statics π L s2) :
    (∃ ops, Machine.Exec C ObR ObW ops Machine.State.empty s2) ∧
      Refinement.Repr π.L π.rtok L.kern s2 ∧ LReach k statics L := by
  obtain ⟨hex, hR, -⟩ := simulation hπ h.simRun
  exact ⟨hex, hR, h.lreach⟩

/-- R4 along library runs (§82.5, §54): in every state of a translated library run whose kernel
state satisfies `WF3` and `NoDangling`, every leaf covered by an active authority has a live
allocation containing its range. -/
theorem lsim_r4 {Ty : Type} {k : K} {C : Nat → Nat → Prop} {ObR : Machine.ReadOblSpec Ty}
    {ObW : Machine.WriteOblSpec Ty} {statics : Statics} {π : Params Ty} {L : LState}
    {s2 : Machine.State} (hπ : ParamsOK C π) (h : LSimRun k C ObR ObW statics π L s2)
    (hw : WF3 L.kern) (hnd : NoDangling L.kern) : LiveCover π.L L.kern s2 :=
  liveCover_of (lsimulation hπ h).2.1 hw hnd

/-! ## No access after invalidation (§82.7, §78, §86) -/

/-- Labelled library runs (Part XIV, §82.7): each library operation listed with the library
state it starts from. -/
inductive LPath (k : K) : LState → List (LOp × LState) → LState → Prop where
  | nil (L : LState) : LPath k L [] L
  | cons {lop : LOp} {L L₁ L' : LState} {t : List (LOp × LState)} :
      LOpStep k lop L L₁ → LPath k L₁ t L' → LPath k L ((lop, L) :: t) L'

/-- The kernel steps of a labelled library run, in order (Part XIV, §82.7). -/
def ltrace : List (LOp × LState) → List (KOp × S3)
  | [] => []
  | (lop, L) :: t => kexp lop L ++ ltrace t

/-- Kernel steps of composed labelled runs (Part XIV, §82.7). -/
theorem ltrace_append (t t' : List (LOp × LState)) : ltrace (t ++ t') = ltrace t ++ ltrace t' := by
  induction t with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨lop, L⟩ := p
    simp only [List.cons_append, ltrace, ih, List.append_assoc]

/-- Extension of a labelled library run by one step (Part XIV, §82.7). -/
theorem LPath.snoc {k : K} {L₀ L L' : LState} {t : List (LOp × LState)} {lop : LOp}
    (hp : LPath k L₀ t L) (hs : LOpStep k lop L L') : LPath k L₀ (t ++ [(lop, L)]) L' := by
  induction hp with
  | nil => exact .cons hs (.nil _)
  | cons h _ ih => exact .cons h (ih hs)

/-- The continuation of a labelled library run after one of its steps (Part XIV, §82.7). -/
theorem LPath.split {k : K} {lop : LOp} {L L₂ : LState} {t₂ : List (LOp × LState)} :
    ∀ (t₁ : List (LOp × LState)) {L₀ : LState}, LPath k L₀ (t₁ ++ (lop, L) :: t₂) L₂ →
      ∃ L₁, LOpStep k lop L L₁ ∧ LPath k L₁ t₂ L₂
  | [], _, h => by
    cases h with
    | cons hs hp => exact ⟨_, hs, hp⟩
  | (_, _) :: t₁, _, h => by
    cases h with
    | cons _ hp => exact LPath.split t₁ hp

/-- The machine trace of a translated library run is the trace of its kernel steps (§82.7): the
run is a labelled library run from the initial library state, and its memory state is reached
from the initial memory state by the raw operations of its kernel steps, in order. -/
theorem LSimRun.trace {Ty : Type} {k : K} {C : Nat → Nat → Prop} {ObR : Machine.ReadOblSpec Ty}
    {ObW : Machine.WriteOblSpec Ty} {statics : Statics} {π : Params Ty} {L : LState}
    {s2 : Machine.State} (h : LSimRun k C ObR ObW statics π L s2) :
    ∃ t, LPath k (LState.init statics) t L ∧
      s2 = run (minit π statics) (ktrace π (ltrace t) (minit π statics)) := by
  induction h with
  | init => exact ⟨[], .nil _, rfl⟩
  | step _ _ _ hs _ ih =>
    obtain ⟨t, hp, rfl⟩ := ih
    refine ⟨_, hp.snoc hs, ?_⟩
    rw [ltrace_append, ktrace_append, run_append]
    simp only [ltrace, List.append_nil]
    rfl

/-- The authority that a kernel step uses as a means of access (§82.7): the authority through
which `read`, `write` and `writeShared` access leaves (§66.2, §67.1, §68.2), the authority whose
reference `store` writes (§65, §82.3), and the source from which `derive` and `split` create new
means of access (§60.1, §61.1). The other operations use none. -/
def usedAuth : KOp → Option Nat
  | .read a _ => some a
  | .write a _ _ => some a
  | .writeShared a _ _ => some a
  | .store a _ => some a
  | .derive src _ _ => some src
  | .split src _ => some src
  | _ => none

/-- An authority exercisable at some mode is active (§43). -/
theorem active_of_exercisable {s : S3} {a : Nat} {m : Mode} (h : s.ExercisableAt a m) :
    s.Active a := by
  cases h with
  | base hy ha => exact ⟨_, hy, ha⟩
  | held hy ha => exact ⟨_, hy, ha⟩

/-- A kernel step uses only an active authority (§60.1, §61.1, §65.1, §66.2, §67.1, §68.2). -/
theorem usedAuth_active {k : K} {op : KOp} {s s' : S3} {j : Nat} (h : OpStep k op s s')
    (hv : usedAuth op = some j) : s.Active j := by
  cases op with
  | read a ls =>
    obtain rfl : a = j := Option.some.inj hv
    exact active_of_exercisable (Guarded.ok_iff.1 h).1.exercisable
  | write a ls w =>
    obtain rfl : a = j := Option.some.inj hv
    exact active_of_exercisable (Guarded.ok_iff.1 h).1.exercisable
  | writeShared a ls w =>
    obtain rfl : a = j := Option.some.inj hv
    exact active_of_exercisable (Guarded.ok_iff.1 h).1.exercisable
  | store a p =>
    obtain rfl : a = j := Option.some.inj hv
    have hd := (Guarded.ok_iff.1 h).1.derivedHeld
    unfold OptP at hd
    split at hd
    · exact ⟨_, ‹_›, hd.1⟩
    · exact hd.elim
  | derive src r m =>
    obtain rfl : src = j := Option.some.inj hv
    exact (Guarded.ok_iff.1 h).1.active
  | split src rs =>
    obtain rfl : src = j := Option.some.inj hv
    exact (Guarded.ok_iff.1 h).1.active
  | transfer => cases hv
  | release => cases hv
  | depend => cases hv
  | enter => cases hv
  | exit => cases hv
  | pin => cases hv
  | unpin => cases hv
  | endUse => cases hv
  | free => cases hv
  | alloc => cases hv

/-- Along a labelled library run whose start keeps the authorities of `s₀`, no kernel step uses
an authority of `s₀` that is inactive in `s₀` (§42, §58: authorities are never reactivated). -/
theorem lpath_unused {k : K} {s₀ : S3} {j : Nat} (hj : j < s₀.A.length) (hd : ¬ s₀.Active j)
    {L L₂ : LState} {t : List (LOp × LState)} (hp : LPath k L t L₂) :
    AKeep s₀ L.kern → ∀ q ∈ ltrace t, usedAuth q.1 ≠ some j := by
  induction hp with
  | nil => intro _ q hq; cases hq
  | cons hs _ ih =>
    intro hk q hq hv
    simp only [ltrace, List.mem_append] at hq
    rcases hq with hq | hq
    · obtain ⟨hk', s₁, hst⟩ := (kexp_path hs).mem q hq
      exact hd ((hk.trans hk').active_back (usedAuth_active hst hv) hj)
    · exact ih (hk.trans (lstep_akeep hs.lstep)) q hq hv

/-- No access after invalidation (§82.7, §78, §86): after a legal `reset` of entry `i`, along
every continuation of the library run, no kernel step reads, writes or writes in shared mode
through, stores, or derives or splits from an authority derived from `internal` that covered a
leaf of the administered storage; so none of the raw operations of the continuation realizes an
access through it. -/
theorem reset_no_access {k : K} {L L₁ L₂ : LState} {i : Nat} {E : ArenaEntry}
    {t : List (LOp × LState)} (hE : L.arenas[i]? = some E) (hr : ResetD i L (.ok L₁))
    (hp : LPath k L₁ t L₂) {j : Nat} (hj : E.internal ∈ L.kern.ancs j)
    (hc : ∃ l ∈ L.kern.afp j, l ∈ footprint L.kern.P E.storage) :
    ∀ q ∈ ltrace t, usedAuth q.1 ≠ some j := by
  have hjL : j < L.kern.A.length := by
    obtain ⟨l, hl, -⟩ := hc
    cases hlj : L.kern.A[j]? with
    | none => simp [S3.afp, hlj] at hl
    | some _ => exact lt_of_getElem? hlj
  exact lpath_unused ((lstep_akeep (k := k) (.reset hr)).lt hjL) (reset_ends_covering hE hr hj hc)
    hp (akeep_of_eq rfl)

/-- No access through an issued block after a legal reset of its arena (§82.7, §78, §86): for a
live entry satisfying `EntryInv`, after a legal `reset`, along every continuation of the library
run, no kernel step uses a block issued before the reset on a nonempty region. -/
theorem reset_no_access_issued {k : K} {L L₁ L₂ : LState} {i : Nat} {E : ArenaEntry}
    {t : List (LOp × LState)} (hE : L.arenas[i]? = some E) (hinv : EntryInv L.kern E)
    (hr : ResetD i L (.ok L₁)) (hp : LPath k L₁ t L₂) :
    ∀ e ∈ E.issued, e.1 ≠ [] → ∀ q ∈ ltrace t, usedAuth q.1 ≠ some e.2 := by
  intro e he hne
  obtain ⟨y, hy, ho, hlt, hf, -⟩ := hinv.2 e he
  have hj : E.internal ∈ L.kern.ancs e.2 := by
    unfold S3.ancs
    rw [chain_cons (by simp [S3.org, hy, ho]) hlt]
    exact List.mem_cons_self ..
  obtain ⟨l, hl⟩ := List.exists_mem_of_ne_nil _ hne
  exact reset_no_access hE hr hp hj ⟨l, by simp [S3.afp, hy, hf, hl], hinv.1.issuedIn e he l hl⟩

/-- §82.7 for translated library runs: the kernel steps of the derived operations are realized
by O1–O16 without reintroducing access after invalidation. The run is a labelled library run from
the initial library state; its memory state is reached from the initial memory state by the raw
operations of its kernel steps (the machine trace of the run is the trace of its kernel steps);
and after every legal `reset` in the run, no kernel step of the continuation uses an authority
derived from `internal` that covered a leaf of the administered storage, so no raw operation of
the continuation is an access through it.

The metadata (`available`, `issued`) is not realized: it is library state with no machine
realization in this model, so the "metadata" part of §82.7 is not covered. This is a reading,
recorded, not settled by the spec: §46 puts the entries in the library's abstract state, separate
from `S₃`, and §81 leaves the representation of library metadata to Spec 11; §36, §71.2 and §76.5
(with the last paragraph of §77) instead speak of metadata kept in storage (`SharedMutable`
storage updated by `writeShared`, provider metadata, the leaves of the arena value), which would
require raw writes realizing each metadata update. -/
theorem arena_realized {Ty : Type} {k : K} {C : Nat → Nat → Prop} {ObR : Machine.ReadOblSpec Ty}
    {ObW : Machine.WriteOblSpec Ty} {statics : Statics} {π : Params Ty} {L : LState}
    {s2 : Machine.State} (h : LSimRun k C ObR ObW statics π L s2) :
    ∃ t, LPath k (LState.init statics) t L ∧
      s2 = run (minit π statics) (ktrace π (ltrace t) (minit π statics)) ∧
      ∀ t₁ t₂ L₀ i E, t = t₁ ++ (.reset i, L₀) :: t₂ → L₀.arenas[i]? = some E →
        ∀ j, E.internal ∈ L₀.kern.ancs j →
          (∃ l ∈ L₀.kern.afp j, l ∈ footprint L₀.kern.P E.storage) →
          ∀ q ∈ ltrace t₂, usedAuth q.1 ≠ some j := by
  obtain ⟨t, hp, hs⟩ := h.trace
  refine ⟨t, hp, hs, ?_⟩
  rintro t₁ t₂ L₀ i E rfl hE j hj hc
  obtain ⟨L₁, hr, hp₂⟩ := LPath.split t₁ hp
  exact reset_no_access hE hr hp₂ hj hc

/-! ## A concrete library run (non-vacuity; §82.7, Part XIV) -/

section Dec

variable (k : K) [∀ r r', Decidable (k.DeclaredDisjoint r r')] [DecidablePred k.SharedMutable]
  [DecidablePred k.Pinned] [DecidablePred k.ExternalDone] [DecidablePred k.Deallocable]
  [∀ p a, Decidable (k.FreeCompat p a)] [∀ p ls s, Decidable (k.Satisfiable p ls s)]
  {Ty : Type} (C : Nat → Nat → Prop) [DecidableRel C] (ObR : Machine.ReadOblSpec Ty)
  (ObW : Machine.WriteOblSpec Ty) [∀ s o, Decidable (Obl ObR ObW s o)] (π : Params Ty)

/-- Decidability of the obligations of a kernel sequence (§20.3, §82). -/
instance kOblDec : (t : List (KOp × S3)) → (s2 : Machine.State) →
    Decidable (KObl k C ObR ObW π t s2)
  | [], _ => isTrue trivial
  | (op, s3) :: t, s2 =>
    @instDecidableAnd _ _ (stepOblDec k C ObR ObW π op s3 s2) (kOblDec t _)

end Dec

namespace Runs

open Ern.MemoryModel.Access.Examples Ern.MemoryModel.Refinement.Runs

/-- Memory state after the library operations `t`, each listed with the library state it starts
from, from the memory state `m` (§82.7). -/
def lrunM {Ty : Type} (π : Params Ty) : List (LOp × LState) → Machine.State → Machine.State
  | [], m => m
  | (lop, L) :: t, m => lrunM π t (run m (lopsOf π lop L m))

/-- The memory state after library operations is reached by the raw operations of their kernel
steps (§82.7). -/
theorem lrunM_eq {Ty : Type} (π : Params Ty) :
    ∀ (t : List (LOp × LState)) (m : Machine.State), lrunM π t m = run m (ktrace π (ltrace t) m)
  | [], _ => rfl
  | (lop, L) :: t, m => by
    rw [lrunM, lrunM_eq π t, ltrace, ktrace_append, run_append]
    rfl

/-- A library run through every derived arena operation (Part XIV, §76–§78; the states of
`Arena.Witness`): `derive(1, [1], Modify)` and `store(3, 0)` prepare `internal` 3 held by the arena
value 0; `newArena(1, 3)`; `issue(0, [1], 2)` (block 4 stored into 2); `write(4, [1])`;
`endUse(2)`; `reset(0)`; `issue(0, [1], 2)` again (block 6). -/
def tA : List (LOp × LState) :=
  [(.kernel (.derive 1 [1] .modify), Witness.w0), (.kernel (.store 3 0), Witness.w1),
   (.newArena [] 1 3, Witness.w2), (.issue 0 [1] 2, Witness.w3),
   (.kernel (.write 4 [1] wv), Witness.r4), (.kernel (.endUse 2), Witness.r5),
   (.reset 0, Witness.r6), (.issue 0 [1] 2, Witness.r7)]

/-- Parameters of the run, fixed once (§82): the test layout of the three static places. -/
def πA : Params Unit := piOf (S3.init st).P []

/-- Final memory state of the run (§82.7). -/
def finA : Machine.State := lrunM πA tA (minit πA st)

/-- The run is a translated library run (§82.7, non-vacuity of `LSimRun`): each step starts from
a state satisfying `WF3` and `NoDangling`, is an `ok` library step, and its kernel steps satisfy
their obligations under the fixed parameters. -/
theorem runA_lsim : LSimRun K0 (· = ·) obR obW st πA Witness.r8 finA := by
  have h0 : LSimRun K0 (· = ·) obR obW st πA Witness.w0 (minit πA st) :=
    .init (by decide) (by decide) (by decide)
  have h1 := LSimRun.step (lop := .kernel (.derive 1 [1] .modify)) (L' := Witness.w1) h0
    (wf3_of_check (by decide)) (noDangling_of_check (by decide)) ⟨.ok (by decide), rfl⟩
    (by decide)
  have h2 := LSimRun.step (lop := .kernel (.store 3 0)) (L' := Witness.w2) h1
    (wf3_of_check (by decide)) (noDangling_of_check (by decide)) ⟨.ok (by decide), rfl⟩
    (by decide)
  have h3 := LSimRun.step (lop := .newArena [] 1 3) (L' := Witness.w3) h2
    (wf3_of_check (by decide)) (noDangling_of_check (by decide)) (.ok (by decide)) (by decide)
  have h4 := LSimRun.step (lop := .issue 0 [1] 2) (L' := Witness.r4) h3
    (wf3_of_check (by decide)) (noDangling_of_check (by decide))
    (IssueD.ok (E := Witness.wE) (by decide) (by decide) (by decide) (.ok (by decide))
      (.ok (by decide))) (by decide)
  have h5 := LSimRun.step (lop := .kernel (.write 4 [1] wv)) (L' := Witness.r5) h4
    (wf3_of_check (by decide)) (noDangling_of_check (by decide)) ⟨.ok (by decide), rfl⟩
    (by decide)
  have h6 := LSimRun.step (lop := .kernel (.endUse 2)) (L' := Witness.r6) h5
    (wf3_of_check (by decide)) (noDangling_of_check (by decide)) ⟨.ok (by decide), rfl⟩
    (by decide)
  have h7 := LSimRun.step (lop := .reset 0) (L' := Witness.r7) h6
    (wf3_of_check (by decide)) (noDangling_of_check (by decide))
    (ResetD.ok (E := Witness.rE) (by decide) (.ok (by decide)) (.ok (by decide)) (by decide))
    (by decide)
  exact LSimRun.step (lop := .issue 0 [1] 2) (L' := Witness.r8) h7
    (wf3_of_check (by decide)) (noDangling_of_check (by decide))
    (IssueD.ok (E := Witness.rE') (by decide) (by decide) (by decide) (.ok (by decide))
      (.ok (by decide))) (by decide)

/-- Non-vacuity of the library simulation (§82.7, §82.3): the run is translated into an execution
of `ok` raw steps from the empty state, `Repr` holds at its end, the final library state is
library-reachable, and the machine trace is the trace of the kernel steps. The reference written
into the arena value 0 and the one written into the destination 2 by the second issue decode to
the address of the storage leaf 1, which is nonzero and whose allocation is live. The range of
leaf 1 still holds the bytes written through block 4 before the `reset`: the reissued block 6
designates the former value in the memory machine too (no rule of §77 or §78 changes these bytes;
see `Arena.Witness.reissue_reads_former_value` for §86). -/
theorem runA_sim :
    ((∃ ops, Machine.Exec (· = ·) obR obW ops Machine.State.empty finA) ∧
      Refinement.Repr πA.L πA.rtok Witness.r8.kern finA ∧ LReach K0 st Witness.r8) ∧
    finA = run (minit πA st) (ktrace πA (ltrace tA) (minit πA st)) ∧
    decodedAt πA finA 0 = leafAddr finA πA.L 1 ∧ decodedAt πA finA 2 = leafAddr finA πA.L 1 ∧
    leafAddr finA πA.L 1 ≠ 0 ∧ (finA.allocs (πA.L 1).alloc).map (·.live) = some true ∧
    ∀ n < 8, bytesOf finA πA.L 1 n = wv 1 n :=
  ⟨lsimulation (piOf_ok _ []) runA_lsim, lrunM_eq _ _ _, by decide, by decide, by decide,
    by decide, by decide⟩

end Runs

end Ern.MemoryModel.RefinementArena
