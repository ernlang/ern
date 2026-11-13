import Ern.Concurrency.FullEncap.ComplementSweep

/-!
# The kinds that kill places

Brief of milestone 4, slice 3, complement, task 3, third fact (`corpus-spec2-m3.md` v14
§2 terdecies, "Feuilles qui meurent": which kinds kill leaves), taken up by the owner after the
complement. On a `RunFull` from the initial state, a step whose kind is not one of `killKind`
keeps every usable place usable (`usable_run`); hence `KillOK` holds on every such run
(`killOK_run`).

`Usable` is Spec 1 §40, read on the flat state (WC5.2 C2). The proof is a case analysis of the
`LStep` transitions on the states reached by `RunFull` (`usable_step`, under `KInvCA`):

* the effects of the kernel operations other than `transfer`, `enterFrame`, `exitFrame`, `endUse`
  and `free` keep the places and the death markers (Spec 1 §60–§62, §64–§68, §71, §74, §75),
  and those of `newMutex`, `acquire`, `unlock`, `resetLock` (WC5.2 C13, C16–C18), `deriveSync`
  (WC5.2 C15), `join` (WC5.2 C8) and the arena operations (Spec 1 §76–§78) as well;
* `enterFrame` and `spawn` append places and a frame (Spec 1 §72; WC5.2 C3, C4);
* `transfer` changes owners (Spec 1 §63 effect); §63.9 keeps them usable (`transfer_usable_fwd`);
* each transfer phase of the by-value composite (WC5.2 C5, phase 2) changes owners as O4; its
  destination is a fresh root owned by the child frame (WC5.2 C5 item 2), usable after the
  phase, so the same argument applies phase by phase.
-/

set_option autoImplicit false

namespace Ern.Concurrency.FullEncap

open Ern.MemoryModel Ern.MemoryModel.Access Ern.Concurrency Ern.Concurrency.MutexReal
open SyncPreserveAux SyncInitAux TransferPreserveAux PreservationAux
open Ern.Concurrency.FullEncap.Sweep (killKind KillOK)

/-! ## Usability carried by a step -/

/-- Usability on the flat state (Spec 1 §40, WC5.2 C2) is kept by a step that keeps the existing
places, marks no unmarked existing place dead and keeps the globally live frames. -/
theorem flat_usable_fwd {s s' : SC} (hP : ∀ q < s.P.length, s'.P[q]? = s.P[q]?)
    (hd : ∀ q < s.P.length, s.dead q = false → s'.dead q = false)
    (hF : ∀ f ∈ s.frames, f ∈ s'.frames) {q : Nat} (h : s.flat.Usable q) :
    s'.flat.Usable q := by
  induction h with
  | @frame q f pl hpl hdq ho hf =>
    have hq : q < s.P.length := lt_of_getElem? hpl
    exact .frame (pl := pl) ((hP q hq).trans hpl) (hd q hq hdq) ho (hF f hf)
  | @place q o pl hpl hdq ho _ ih =>
    have hq : q < s.P.length := lt_of_getElem? hpl
    exact .place (pl := pl) ((hP q hq).trans hpl) (hd q hq hdq) ho ih

/-- Usability on the flat state is usability on the view of a context (Spec 1 §40, WC5.2 C2). -/
theorem flat_usable_view {s : SC} {c q : Nat} (h : s.flat.Usable q) : (s.view c).Usable q :=
  (usable_mem_congr (t := s.flat) (F' := (s.view c).F) fun _ => SC.mem_view_F).2 h

/-- `enterFrame` executed by `c` keeps every usable place usable (Spec 1 §40, §72 effect; WC5.2
C3). -/
theorem enterC_usable_fwd {s : SC} {c : Nat} {ps : List Nat} {ls : LocalShape} (hfr : FramesC s)
    (hc : s.stk c ≠ []) {q : Nat} (h : s.flat.Usable q) : (enterEffC s c ps ls).flat.Usable q :=
  flat_usable_fwd
    (fun _ hq => by
      show (shapeP s.P _ _)[_]? = _
      exact List.getElem?_append_left hq)
    (fun q hq hd => by
      show (if s.P.length ≤ q then false else s.dead q) = false
      split
      · exact absurd ‹_› (Nat.not_le.2 hq)
      · exact hd)
    (fun f hf => ((enter_push (ps := ps) (ls := ls) hfr hc).mem f).2 (.inr hf)) h

/-- `spawn` executed by `c`, and the creation phase of the by-value composite, keep every usable
place usable (Spec 1 §40, §72 effect; WC5.2 C4 effect, C5 phase 1). -/
theorem spawn_usable_fwd {s : SC} {c : Nat} {ps : List Nat} {ls : LocalShape} (hfr : FramesC s)
    (hc : s.stk c ≠ []) {q : Nat} (h : s.flat.Usable q) : (spawnEff s c ps ls).flat.Usable q :=
  flat_usable_fwd
    (fun _ hq => by
      show (shapeP s.P _ _)[_]? = _
      exact List.getElem?_append_left hq)
    (fun q hq hd => by
      show (if s.P.length ≤ q then false else s.dead q) = false
      split
      · exact absurd ‹_› (Nat.not_le.2 hq)
      · exact hd)
    (fun f hf => ((spawn_push (ps := ps) (ls := ls) hfr hc).mem f).2 (.inr hf)) h

/-- `transfer` executed by `c` keeps every usable place usable when its destination is usable in
the resulting state (Spec 1 §40, §63 effect, §63.9; `transfer_usable_fwd`). -/
theorem transferC_usable_fwd {t : SC} {c src dst : Nat} (hw : WF3 (t.view c))
    (hd' : (transferEff (t.view c) src dst).Usable dst) {q : Nat} (h : t.flat.Usable q) :
    (transferEffC t c src dst).flat.Usable q :=
  (set_usable (s := t) (t := transferEff (t.view c) src dst)
    fun _ => SC.mem_view_F (s := t) (c := c)).2 (transfer_usable_fwd hw hd' (flat_usable_view h))

/-- The kernel operations other than `transfer`, `enterFrame` and the kinds of `killKind`,
executed by `c`, keep every usable place usable: their effects keep the places and the death
markers of the view of `c`, and the contexts (Spec 1 §40; §60–§62, §64–§68, §71, §74, §75
effects; WC5.2 C2). -/
theorem opStepC_usable_fwd_base {k : K} {op : KernelOp} {c : Nat} {s s' : SC}
    (h : opStepC k op c s (.ok s')) (hnt : ∀ src dst, op ≠ .transfer src dst)
    (hne : ∀ ps ls, op ≠ .enter ps ls) (hkill : killKind (.kernel c op) = false) {q : Nat}
    (hq : s.flat.Usable q) : s'.flat.Usable q := by
  cases op with
  | transfer src dst => exact absurd rfl (hnt src dst)
  | enter ps ls => exact absurd rfl (hne ps ls)
  | exit => simp [killKind] at hkill
  | endUse p => simp [killKind] at hkill
  | free p a => simp [killKind] at hkill
  | depend q' x =>
    obtain ⟨-, h⟩ := h; obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
    exact (set_usable_iff rfl rfl).2 hq
  | store a p =>
    obtain ⟨-, h⟩ := h; obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
    exact (set_usable_iff (by unfold storeEff; split <;> rfl)
      (by unfold storeEff; split <;> rfl)).2 hq
  | alloc pr ow ls =>
    obtain ⟨t, hR, rfl⟩ := viewStep_ok h
    cases hR with
    | ok =>
      exact (set_usable (s := s) (t := allocEff (s.view c) ow ls)
        fun _ => SC.mem_view_F (s := s) (c := c)).2 (Alloc.usable_old (flat_usable_view hq))
  | release a =>
    obtain ⟨t, hR, rfl⟩ := viewStep_ok h
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hR
    exact (set_usable_iff (by unfold releaseEff; split <;> rfl)
      (by unfold releaseEff; split <;> rfl)).2 hq
  | derive src region m =>
    obtain ⟨t, hR, rfl⟩ := viewStep_ok h
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hR
    exact (set_usable_iff rfl rfl).2 hq
  | split src rs =>
    obtain ⟨t, hR, rfl⟩ := viewStep_ok h
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hR
    exact (set_usable_iff rfl rfl).2 hq
  | read a ls =>
    obtain ⟨t, hR, rfl⟩ := viewStep_ok h
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hR
    exact (set_usable_iff rfl rfl).2 hq
  | write a ls =>
    obtain ⟨t, hR, rfl⟩ := viewStep_ok h
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hR
    exact (set_usable_iff rfl rfl).2 hq
  | writeShared a ls =>
    obtain ⟨t, hR, rfl⟩ := viewStep_ok h
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hR
    exact (set_usable_iff rfl rfl).2 hq
  | pin p =>
    obtain ⟨t, hR, rfl⟩ := viewStep_ok h
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hR
    exact (set_usable_iff rfl rfl).2 hq
  | unpin o =>
    obtain ⟨t, hR, rfl⟩ := viewStep_ok h
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hR
    exact (set_usable_iff rfl rfl).2 hq

/-- The kernel operations other than the kinds of `killKind`, executed by `c` from a state
satisfying `KInvCA`, keep every usable place usable (Spec 1 §40; §60–§68, §71, §72, §74, §75
effects; §63.9 for `transfer`; WC5.2 C2, C3). -/
theorem opStepC_usable_fwd {k : K} {op : KernelOp} {c : Nat} {s s' : SC} (hk : KInvCA s)
    (h : opStepC k op c s (.ok s')) (hkill : killKind (.kernel c op) = false) {q : Nat}
    (hq : s.flat.Usable q) : s'.flat.Usable q := by
  cases op with
  | transfer src dst =>
    obtain ⟨-, h⟩ := h; obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
    exact transferC_usable_fwd (view_facts hk c).1 hpre.dstUsableAfter hq
  | enter ps ls =>
    obtain ⟨-, h⟩ := h; obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
    exact enterC_usable_fwd hk.1.1.1 hpre.callerLive hq
  | _ =>
    exact opStepC_usable_fwd_base h (fun _ _ e => by cases e) (fun _ _ e => by cases e) hkill hq

/-! ## The by-value composite -/

/-- The transfer phases of the by-value composite (WC5.2 C5 phase 2, effects of O4, Spec 1 §63)
keep every usable place usable: the destination of each phase is owned by a frame and usable at
its start (WC5.2 C5 item 2, `ValTransferPre.dstUsable`), hence usable after it, which is the
§63.9 premise of `transfer_usable_fwd`; `KBase` carries `WF3` from phase to phase
(`transfer_base`). -/
theorem transfers_usable_fwd {k : K} {fin : S3} {c : Nat} :
    ∀ (t : SC) (vs : List (Nat × Nat)), ValTransfersPre k fin c t vs → KBase t →
      (∀ v ∈ vs, FrameOwned t.P v.2) → ∀ (q : Nat), t.flat.Usable q →
        (transfersEff c t vs).flat.Usable q
  | _, [], _, _, _, _, h => h
  | t, v :: vs, ⟨hpre, hrest⟩, hk, hown, q, h => by
    have hd' := transfer_usable_frameOwned (src := v.1) (dst := v.2) hpre.dstUsable
      (hown v (List.mem_cons_self ..))
    have hk₁ := transfer_base hk hpre.srcUsable hpre.dstUsable hpre.depsValid hpre.sameShape
      hpre.disjoint hd'
    exact transfers_usable_fwd (transferEffC t c v.1 v.2) vs hrest hk₁
      (fun w hw => transfer_frameOwned (hown w (List.mem_cons_of_mem _ hw))) q
      (transferC_usable_fwd (view_facts_base hk c).1 hd' h)

/-- The by-value composite (WC5.2 C5) keeps every usable place usable: creation (phase 1,
`spawn_usable_fwd`), transfers (phase 2, `transfers_usable_fwd`), and the yield (phase 3), which
changes holders only (Spec 1 §40). -/
theorem spawnVal_usable_fwd {k : K} {s s' : SC} {c : Nat} {ps : List Nat} {ls : LocalShape}
    {vs : List (Nat × Nat)} (hk : KInvCA s) (h : SpawnValStep k s c ps ls vs (.ok s')) {q : Nat}
    (hq : s.flat.Usable q) : s'.flat.Usable q := by
  obtain ⟨-, h⟩ := h; obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  have h₁ : (spawnCreate s c ls).flat.Usable q := spawn_usable_fwd hk.1.1.1 hpre.creatorLive hq
  have hb₀ : KBase (spawnCreate s c ls) :=
    spawn_base hk hpre.creatorLive (fun _ h => nomatch h) hpre.localsOK
  have h₂ := transfers_usable_fwd (spawnCreate s c ls) vs hpre.transfers hb₀
    (fun v hv => spawn_frameOwned (hpre.freshDst v hv)) q h₁
  exact (S3.Usable.congr (s := (transfersEff c (spawnCreate s c ls) vs).flat)
    (s' := (spawnValEff s c ps ls vs).flat) rfl rfl rfl).2 h₂

/-! ## Every step, every run -/

/-- Per-step form, under the invariant reached by the runs (`KInvCA`): a step whose kind is not
one of `killKind` keeps every usable place usable (Spec 1 §40; the effects of WC5.2 C2–C8,
C13–C18 and Spec 1 §60–§78 on the places, the death markers and the live frames). -/
theorem usable_step {k : K} {L : MutexLayout} {st st' : SC × SyncReg × ArenaReg} {lbl : Label}
    (hk : KInvCA st.1) (hs : LStep k L lbl st st') (hkill : killKind lbl = false) {q : Nat}
    (hq : st.1.flat.Usable q) : st'.1.flat.Usable q := by
  cases hs with
  | kernel h => exact opStepC_usable_fwd hk h hkill hq
  | spawn h =>
    obtain ⟨-, h'⟩ := h; obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h'
    exact spawn_usable_fwd hk.1.1.1 hpre.creatorLive hq
  | terminate => simp [killKind] at hkill
  | join h => cases h; exact hq
  | deriveSync h =>
    obtain ⟨-, h'⟩ := h; obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h'
    exact (set_usable_iff rfl rfl).2 hq
  | newMutex h => obtain ⟨-, -, rfl⟩ := h; exact hq
  | acquire h =>
    obtain ⟨-, _, -, -, -, rfl⟩ := h
    exact (set_usable_iff rfl rfl).2 hq
  | unlock h =>
    obtain ⟨-, _, _, -, -, -, -, -, rfl⟩ := h
    exact (set_usable_iff (by unfold releaseEff; split <;> rfl)
      (by unfold releaseEff; split <;> rfl)).2 hq
  | resetLock h => obtain ⟨-, -, -, -, -, -, rfl⟩ := h; exact hq
  | spawnVal h => exact spawnVal_usable_fwd hk h hq
  | newArena h => obtain ⟨-, -, rfl⟩ := newArenaStepC_ok h; exact hq
  | issue h =>
    obtain ⟨_, _, -, -, -, hsp, hsto, -⟩ := issueStepC_ok h
    exact opStepC_usable_fwd_base hsto (fun _ _ e => by cases e) (fun _ _ e => by cases e) rfl
      (opStepC_usable_fwd_base hsp (fun _ _ e => by cases e) (fun _ _ e => by cases e) rfl hq)
  | reset h =>
    obtain ⟨_, _, -, hd, hrl, -, -⟩ := resetStepC_ok (k := k) h
    exact opStepC_usable_fwd_base hrl (fun _ _ e => by cases e) (fun _ _ e => by cases e) rfl
      (opStepC_usable_fwd_base hd (fun _ _ e => by cases e) (fun _ _ e => by cases e) rfl hq)

/-- Brief of the complement, task 3, third fact: on a `RunFull` from the initial state, under
`DDSound` and `StaticsOK`, a step whose kind is not one of `killKind` (`endUse`, Spec 1 §69;
`free`, §70; `exitFrame`, §73 and WC5.2 C6; `terminate`, WC5.2 C7) keeps every usable place
usable (Spec 1 §40). Invariant used: `KInvCA` before the step (`runFull_inv`). -/
theorem usable_run {k : K} {L : MutexLayout} {statics : Statics}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} (hdd : DDSound k)
    (hstat : StaticsOK statics) (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], []))
    (h : RunFull k L σ lbls) {i : Nat} (hi : i < lbls.length) (hkill : killKind lbls[i] = false)
    {l : Nat} (hu : (σ i).1.flat.Usable l) : (σ (i + 1)).1.flat.Usable l :=
  usable_step (runFull_inv hdd hstat h0 h (Nat.le_of_lt hi)).1 (h i hi).2 hkill hu

/-- `KillOK`, the decidable form checked by `sweep_kill`, holds on every `RunFull` from the
initial state under `DDSound` and `StaticsOK` (brief of the complement, task 3, third fact). -/
theorem killOK_run {k : K} {L : MutexLayout} {statics : Statics}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} (hdd : DDSound k)
    (hstat : StaticsOK statics) (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], []))
    (h : RunFull k L σ lbls) : KillOK σ lbls := fun i hi _ _ hd => by
  cases hb : killKind lbls[i] with
  | true => rfl
  | false => exact absurd (usable_run hdd hstat h0 h hi hb hd.2.1) hd.2.2

end Ern.Concurrency.FullEncap
