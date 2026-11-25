import Ern.ConcurrencyModel.Reachable

/-!
# Theorem 3: frame ancestry under reparenting (C3, C6, C7; `OB-C13`)

Theorem 3 of `formal/DESIGN.md`, Milestone 4, target theorems:

* the properties of C3 on every state whose frame structure satisfies `FramesC` (part of
  `ConcurrentWF`, C20): nonempty local stacks, globally unique frame identities, `ancestorC`
  reflexive, acyclic apart from reflexivity and well-founded through its strict-parent relation,
  and equal to `ancestor` of Spec 1 §39 on single-context states (`ancestry_props`);
* the initial frame of a new context is parented to the creating frame (`spawn_initial_parent`,
  `spawnVal_initial_parent`);
* `spawn`, `exitFrameC` and `terminate`, reparenting included, preserve `FramesC`, hence these
  properties, and the extended ancestry of the surviving frames is the ancestry before the step
  (`spawn_ancestry`, `exitFrameC_ancestry`, `terminate_ancestry`);
* the base frame of the initial context never exits (`base_frame_run`).
-/

namespace Ern.ConcurrencyModel

open Ern.MemoryModel.Access ReparentAux PreservationAux

/-! ## The properties of C3 -/

/-- C3: `ancestorC` is reflexive on live frames. -/
theorem ancestorC_refl {s : SC} {f : Nat} (hf : f ∈ s.frames) : s.ancestorC f f :=
  ⟨hf, .inl rfl⟩

/-- C3: `ancestorC` is acyclic apart from reflexivity. -/
theorem ancestorC_antisymm {s : SC} {f g : Nat} (h₁ : s.ancestorC g f) (h₂ : s.ancestorC f g) :
    g = f := by
  rcases h₁.2 with e | h₁
  · exact e
  · rcases h₂.2 with e | h₂
    · exact e.symm
    · have := chain_lt h₁; have := chain_lt h₂; omega

/-- C3: the strict-parent relation of the live frames is well-founded. -/
theorem parC_wellFounded {s : SC} (hfr : FramesC s) :
    WellFounded (fun g f => f ∈ s.frames ∧ s.parC f = some g) :=
  Subrelation.wf (fun {g f} h => (hfr.parent f h.1 g h.2).2) (measure id).wf

/-- **Theorem 3**, the properties of C3 on a state whose frame structure satisfies `FramesC`
(C20): every live context has a nonempty local stack; frame identities are globally unique;
`ancestorC` is reflexive on live frames and acyclic apart from reflexivity; its strict-parent
relation is well-founded; on a single-context state it coincides with `ancestor` of Spec 1 §39.
Fragment: every state satisfying `FramesC`. -/
theorem ancestry_props {s : SC} (hfr : FramesC s) :
    (∀ c, s.Live c → s.stk c ≠ []) ∧ s.frames.Nodup ∧ (∀ f ∈ s.frames, s.ancestorC f f) ∧
      (∀ f g, s.ancestorC g f → s.ancestorC f g → g = f) ∧
      WellFounded (fun g f => f ∈ s.frames ∧ s.parC f = some g) ∧
      (s.Single → ∀ g f, s.ancestorC g f ↔ ancestor (s.stk 0) g f) :=
  ⟨hfr.nonempty, hfr.nodup, fun _ hf => ancestorC_refl hf, fun _ _ h₁ h₂ => ancestorC_antisymm h₁ h₂,
    parC_wellFounded hfr, fun hs g f => single_ancestorC hs.sole (single_decreasing hs.sole hfr) g f⟩

/-! ## The initial frame of a new context (C3, C4, C5) -/

/-- C3, C4 effect: after `spawn` executed by `c`, the new context `|C|` has the single frame
`nF`, parented to the creating frame, the current frame of `c`. -/
theorem spawn_initial_parent (s : SC) (c : Nat) (ps : List Nat) (ls : LocalShape) :
    (spawnEff s c ps ls).stk s.C.length = [s.nF] ∧
      (spawnEff s c ps ls).ctxParent s.C.length = (s.stk c).head? := by
  refine ⟨by rw [spawn_stk]; simp, ?_⟩
  simp [SC.ctxParent, spawnEff]

/-- The transfer phases of the by-value composite keep the contexts (C5.2: O4 changes only the
kernel components). -/
theorem transfersEff_C (c : Nat) : ∀ (t : SC) (vs : List (Nat × Nat)),
    (transfersEff c t vs).C = t.C
  | _, [] => rfl
  | t, v :: vs => (transfersEff_C c (transferEffC t c v.1 v.2) vs).trans rfl

/-- C3, C5 effect: after the by-value `spawn` executed by `c`, the new context `|C|` has the
single frame `nF`, parented to the creating frame. -/
theorem spawnVal_initial_parent (s : SC) (c : Nat) (ps : List Nat) (ls : LocalShape)
    (vs : List (Nat × Nat)) :
    (spawnValEff s c ps ls vs).stk s.C.length = [s.nF] ∧
      (spawnValEff s c ps ls vs).ctxParent s.C.length = (s.stk c).head? := by
  have hC : (spawnValEff s c ps ls vs).C = (spawnCreate s c ls).C :=
    transfersEff_C c (spawnCreate s c ls) vs
  have h := spawn_initial_parent s c [] ls
  refine ⟨?_, ?_⟩
  · unfold SC.stk at h ⊢; rw [hC]; exact h.1
  · unfold SC.ctxParent at h ⊢; rw [hC]; exact h.2

/-! ## Preservation by `spawn`, `exitFrameC` and `terminate` (C6, C7; `OB-C13`) -/

/-- **Theorem 3** for `spawn` (C3, C4): an `ok` `spawn` preserves `FramesC`; the live frames are
the old ones and the fresh frame `nF`, whose parent is the creating frame; the extended ancestry
between old live frames is unchanged. -/
theorem spawn_ancestry {s s' : SC} {c : Nat} {ps : List Nat} {ls : LocalShape}
    (hfr : FramesC s) (h : SpawnStep s c ps ls (.ok s')) :
    FramesC s' ∧ (∀ f, f ∈ s'.frames ↔ f = s.nF ∨ f ∈ s.frames) ∧
      s'.parC s.nF = some ((s.stk c).headD 0) := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  have hp := spawn_push (ps := ps) (ls := ls) hfr hpre.creatorLive
  exact ⟨hp.framesC hfr, hp.mem, hp.parNew⟩

/-- **Theorem 3** for `exitFrameC` (C6; `OB-C13`): an `ok` `exitFrameC` executed by `c` preserves
`FramesC` (so the properties of C3, well-foundedness included); its live frames are the old ones
without the exiting frame `f`; the extended ancestry between surviving frames is the ancestry
before the step; every surviving context-initial frame whose parent was `f` gets the immediate
caller `p = parent(f)`, the other parents being unchanged. -/
theorem exitFrameC_ancestry {k : K} {s s' : SC} {c : Nat} (hfr : FramesC s)
    (h : opStepC k .exit c s (.ok s')) :
    FramesC s' ∧
      (∀ y, y ∈ s'.frames ↔ y ∈ s.frames ∧ y ≠ (s.stk c).headD 0) ∧
      (∀ g y, g ∈ s'.frames → y ∈ s'.frames → (s'.ancestorC g y ↔ s.ancestorC g y)) ∧
      s.parC ((s.stk c).headD 0) = some ((s.stk c).tail.headD 0) ∧
      ∀ d, s'.Live d → s'.ctxParent d =
        if s.ctxParent d = some ((s.stk c).headD 0) then some ((s.stk c).tail.headD 0)
        else s.ctxParent d := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  have ha := exitEffC_ancestorC (y := 0) (g := 0) hfr hpre.hasCaller
  exact ⟨exitEffC_framesC hfr hpre.hasCaller, fun y => (exitEffC_ancestorC (g := 0) hfr
    hpre.hasCaller).1, fun g y => (exitEffC_ancestorC hfr hpre.hasCaller).2,
    (exitEffC_reparent hfr hpre.hasCaller).1, (exitEffC_reparent hfr hpre.hasCaller).2⟩

/-- **Theorem 3** for `terminate` (C7, C6; `OB-C13`): an `ok` `terminate` executed by `c`
preserves `FramesC`; its live frames are the old ones without the initial frame `f` of `c`; the
extended ancestry between surviving frames is the ancestry before the step; every surviving
context-initial frame whose parent was `f` gets the parent of `f`, the others being unchanged. -/
theorem terminate_ancestry {k : K} {s s' : SC} {c : Nat} (hfr : FramesC s)
    (h : TermStep k s c (.ok s')) :
    FramesC s' ∧
      (∀ y, y ∈ s'.frames ↔ y ∈ s.frames ∧ y ≠ (s.stk c).headD 0) ∧
      (∀ g y, g ∈ s'.frames → y ∈ s'.frames → (s'.ancestorC g y ↔ s.ancestorC g y)) ∧
      s.parC ((s.stk c).headD 0) = some ((s.ctxParent c).getD 0) ∧
      ∀ d, s'.Live d → s'.ctxParent d =
        if s.ctxParent d = some ((s.stk c).headD 0) then some ((s.ctxParent c).getD 0)
        else s.ctxParent d := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  have hpar : s.ctxParent c ≠ none := by
    intro e; have := hpre.hasParent; rw [e] at this; exact this
  exact ⟨termEffC_framesC hfr hpre.nonInitial hpre.initialOnly hpar,
    fun y => (termEffC_ancestorC (g := 0) hfr hpre.initialOnly hpar).1,
    fun g y => (termEffC_ancestorC hfr hpre.initialOnly hpar).2,
    (termEffC_reparent hfr hpre.initialOnly hpar).1, (termEffC_reparent hfr hpre.initialOnly hpar).2⟩

/-! ## The base frame never exits (C3, C6, C7) -/

/-- The last element of a list is that of its tail when the tail is nonempty. -/
theorem getLast?_tail {l : List Nat} (h : l.tail ≠ []) : l.tail.getLast? = l.getLast? := by
  cases l with
  | nil => rfl
  | cons a t =>
    cases t with
    | nil => exact absurd rfl h
    | cons b u => simp [List.getLast?_cons_cons]

/-- A kernel operation other than `enterFrame` and `exitFrameC` keeps every local stack (C2: it
changes only the kernel components). -/
theorem opStepC_stk {k : K} {op : KernelOp} {c : Nat} {s s' : SC}
    (hne : ∀ ps ls, op ≠ .enter ps ls) (hnx : op ≠ .exit) (h : opStepC k op c s (.ok s')) :
    ∀ d, s'.stk d = s.stk d := by
  intro d
  cases op
  case transfer src dst => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; rfl
  case depend q x => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; rfl
  case store a p => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; rfl
  case enter ps ls => exact absurd rfl (hne ps ls)
  case exit => exact absurd rfl hnx
  all_goals
    obtain ⟨o₃, -, ho⟩ := h
    cases o₃ with
    | ok t => cases ho; rfl
    | reject => cases ho
    | fail => cases ho

/-- A step of a kernel operation keeps the bottom of the local stack of context 0: `enterFrame`
pushes on a nonempty stack, `exitFrameC` pops a frame that has a caller in the same stack (C6),
the other operations keep the stacks (C2). -/
theorem opStepC_base {k : K} {op : KernelOp} {c : Nat} {s s' : SC} (hfr : FramesC s)
    (h : opStepC k op c s (.ok s')) : (s'.stk 0).getLast? = (s.stk 0).getLast? := by
  cases op
  case transfer src dst => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; rfl
  case depend q x => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; rfl
  case store a p => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; rfl
  case enter ps ls =>
    obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
    rw [enter_stk hpre.callerLive]
    by_cases e : (0 : Nat) = c
    · subst e
      simp only [↓reduceIte]
      obtain ⟨f, t, ht⟩ := List.exists_cons_of_ne_nil hpre.callerLive
      rw [ht, List.getLast?_cons_cons]
    · simp [e]
  case exit =>
    obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
    rw [(exitEffC_pop hfr.nodup hpre.hasCaller).stk 0]
    by_cases e : (0 : Nat) = c
    · subst e; simp only [↓reduceIte]; exact getLast?_tail hpre.hasCaller
    · simp [e]
  all_goals
    obtain ⟨o₃, -, ho⟩ := h
    cases o₃ with
    | ok t => cases ho; rfl
    | reject => cases ho
    | fail => cases ho

/-- A labelled step keeps the bottom of the local stack of context 0: no step ends the base frame
(C3; C6: `exitFrameC` needs a caller in the same stack; C7: `terminate` is for non-initial
contexts). -/
theorem lstep_base {ks : KShared} {L : MutexLayout} {lbl : Label}
    {st st' : SC × SyncReg × ArenaReg} (hfr : FramesC st.1) (h : LStep ks L lbl st st') :
    (st'.1.stk 0).getLast? = (st.1.stk 0).getLast? := by
  have h0 : 0 < st.1.C.length := by
    have := hfr.initial; unfold OptP at this; split at this
    · exact lt_of_getElem? ‹_›
    · exact this.elim
  cases h with
  | kernel h => exact opStepC_base hfr h
  | spawn h =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
    rw [spawn_stk]; simp [h0]
  | @terminate s s' reg ar c h =>
    obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
    have hpar : s.ctxParent c ≠ none := by
      intro e; have := hpre.hasParent; rw [e] at this; exact this
    rw [(termEffC_pop hfr.nodup hpre.initialOnly hpar).stk 0]
    have : (0 : Nat) ≠ c := fun e => hpre.nonInitial e.symm
    simp [this]
  | join h => cases h; rfl
  | deriveSync h => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; rfl
  | newMutex h => obtain ⟨-, -, rfl⟩ := h; rfl
  | acquire h => obtain ⟨-, _, -, -, -, rfl⟩ := h; rfl
  | unlock h => obtain ⟨-, _, _, -, -, -, -, -, -, rfl⟩ := h; rfl
  | resetLock h => obtain ⟨-, _, -, -, -, -, -, rfl⟩ := h; rfl
  | @spawnVal s s' reg ar c ps ls vs h =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
    have hC : (spawnValEff s c ps ls vs).C = (spawnCreate s c ls).C :=
      transfersEff_C c (spawnCreate s c ls) vs
    have e : (spawnValEff s c ps ls vs).stk 0 = (spawnCreate s c ls).stk 0 := by
      unfold SC.stk; rw [hC]
    rw [e, spawnCreate, spawn_stk]; simp [h0]
  | newArena h => obtain ⟨-, -, rfl⟩ := newArenaStepC_ok h; rfl
  | issue h =>
    obtain ⟨E, s₁, -, -, -, hsp, hsto, -⟩ := issueStepC_ok h
    rw [opStepC_stk (fun _ _ e => by cases e) (fun e => by cases e) hsto,
      opStepC_stk (fun _ _ e => by cases e) (fun e => by cases e) hsp]
  | reset h =>
    obtain ⟨E, s₁, -, hd, hrl, -, -⟩ := resetStepC_ok (k := ks.toK) h
    rw [opStepC_stk (fun _ _ e => by cases e) (fun e => by cases e) hrl,
      opStepC_stk (fun _ _ e => by cases e) (fun e => by cases e) hd]
  | readShared h => rfl
  | writeShared h => exact opStepC_base hfr (writeSharedC_ok_kernel h)
  | cas h =>
    rcases cas_ok_cases h with hk | e
    · exact opStepC_base hfr hk
    · rw [e]

/-- **Theorem 3** (C3): along every run from the initial state of Spec 1 §47 (one context, empty
registries), the bottom of the local stack of context 0 stays the base frame 0, under `DDSound`
(Spec 1 §80) and well-formed statics (Spec 1 §47). Fragment: every run of the labelled step
relation, without trace restriction. -/
theorem base_frame_run {ks : KShared} {L : MutexLayout} {statics : Statics} {lbls : List Label}
    {st' : SC × SyncReg × ArenaReg} (hdd : DDSound ks.toK) (hst : StaticsOK statics)
    (h : LRun ks L (SC.ofS3 (S3.init statics), [], []) lbls st') :
    (st'.1.stk 0).getLast? = some 0 := by
  have key : ∀ {st st' : SC × SyncReg × ArenaReg} {lbls : List Label}, LRun ks L st lbls st' →
      KInvCA st.1 → (st'.1.stk 0).getLast? = (st.1.stk 0).getLast? := by
    intro st st' lbls h hk
    induction h with
    | nil => rfl
    | cons hs _ ih =>
      rw [ih (lstep_kInvCA hdd hs hk)]
      exact lstep_base hk.1.1.1 hs
  rw [key h (init_inv hdd hst L).1]
  rfl

end Ern.ConcurrencyModel
