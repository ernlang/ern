import Ern.Concurrency.FullEncap.Inventory
import Ern.Concurrency.MutexReal.Classify

/-!
# Capacity required by the footprint

Brief of milestone 4, slice 3, task 4: on a `RunFull` from the initial state, a step of a context
`c` whose final footprint `TouchesF` contains an already existing leaf `l` is made with
`cap5(c, l)` (WC5.2 C43) at least the mode that the operation requires on `l`. This generalizes
`cap5_sound_C` (`read3`, `write3`, `writeShared`).

The required mode is read off the clause of each kind (`CapReq`):

* `read3` (Spec 1 §66.2), `writeShared` (§68.2): `Observe` on its leaves; `write3` (§67.1):
  `Modify`;
* `store` (§65.2), `transfer` (§63.1), `issue` (§77.2): `Modify` on the target, the source and
  destination leaves, the destination;
* `endUse` (§69.1), `free` (§70.3): `Modify` on the leaves of `place`; the clauses require no mode
  on the other leaves that die with it;
* `alloc` (§71.2, §71.3): on the provider, `Modify`, or `Observe` with `K.SharedMutable` (the
  `writeShared` branch of §68); on the owner, `Modify`;
* `newMutex` (WC5.2 C13 item 11): `Modify` on the controller; `acquire`, `unlock`, `resetLock`
  (C14 item 3, C17 item 4, C18 item 4, with §68.2): `Observe` on the controller;
* `exitFrame`, `terminate` (§73; WC5.2 C7): no mode required on the leaves that die;
* by-value `spawn`: `Modify` on each source, at the start of its transfer phase (WC5.2 C5.2;
  `capacity_spawnVal`);
* the other kinds have an empty footprint or touch fresh places only (`touchesF_void`).
-/

set_option autoImplicit false

namespace Ern.Concurrency.FullEncap

open Ern.MemoryModel Ern.MemoryModel.Access Ern.Concurrency Ern.Concurrency.MutexReal

/-! ## Required mode -/

/-- The capacity a step requires on a touched leaf `l`, read off its clause (brief of slice 3,
task 4); see the module docstring for the clause of each kind. -/
def CapReq (k : K) (st : SC × SyncReg × ArenaReg) : Label → Nat → Prop
  | .kernel c (.read _ _), l | .kernel c (.writeShared _ _), l =>
      Allows (cap5 st.1 st.2.1 c l) .observe
  | .kernel c (.write _ _), l | .kernel c (.store _ _), l | .kernel c (.transfer _ _), l =>
      Allows (cap5 st.1 st.2.1 c l) .modify
  | .kernel c (.endUse p), l | .kernel c (.free p _), l =>
      l ∈ footprint st.1.P p → Allows (cap5 st.1 st.2.1 c l) .modify
  | .kernel c (.alloc pr ow _), l =>
      (l ∈ footprint st.1.P pr → Allows (cap5 st.1 st.2.1 c l) .observe ∧
        (Allows (cap5 st.1 st.2.1 c l) .modify ∨ k.SharedMutable l)) ∧
      (l = ow → Allows (cap5 st.1 st.2.1 c l) .modify)
  | .issue c _ _ _, l | .newMutex c _, l => Allows (cap5 st.1 st.2.1 c l) .modify
  | .acquire c _, l | .unlock c _, l | .resetLock c _, l => Allows (cap5 st.1 st.2.1 c l) .observe
  | _, _ => True

/-! ## From the guard-free forms to `cap5` -/

/-- `Modify` permits `Observe` (Spec 1 §43: `Observe ≤ Modify`). -/
theorem allows_observe_of_modify {e : Option Mode} (h : Allows e .modify) : Allows e .observe := by
  cases e with
  | none => exact h
  | some m => exact Or.inl rfl

/-- A guard-free right over a place bounds `cap5` from below on its leaves (WC5.2 C43). -/
theorem cap5_of_hasRight5 {s : SC} {reg : SyncReg} {c q l : Nat} {m : Mode} (hne : s.stk c ≠ [])
    (h : HasRight5 (s, reg) c m q) (hl : l ∈ footprint s.P q) : Allows (cap5 s reg c l) m := by
  obtain ⟨a, -, hx, hall⟩ := h
  exact cap5_of (Exer5.attr5 hne hx) (hall l hl)

/-- A guard-free controller-access right bounds `cap5` from below on the controller (WC5.2 C14
item 3, C43). -/
theorem cap5_of_ctrlRight5 {L : MutexLayout} {s : SC} {reg : SyncReg} {e : SyncEntry} {c l : Nat}
    (hne : s.stk c ≠ []) (h : CtrlRight5 L (s, reg) e c) (hctl : ControlOf L s e = some l) :
    Allows (cap5 s reg c l) .observe := by
  unfold CtrlRight5 at h
  rw [hctl] at h
  obtain ⟨a, -, hx, he⟩ := h
  exact cap5_of (Exer5.attr5 hne hx) (allows_observe he)

/-- The guard-free controller access of an entry of the registry, read through `bind`. -/
theorem cap5_of_ctrl_bind {L : MutexLayout} {s : SC} {reg : SyncReg} {i c l : Nat}
    {P : SyncEntry → Prop} (hne : s.stk c ≠ [])
    (h : OptP (reg[i]?) (fun e => CtrlRight5 L (s, reg) e c ∧ P e) False)
    (ht : (reg[i]?).bind (ControlOf L s) = some l) : Allows (cap5 s reg c l) .observe := by
  revert h ht
  cases reg[i]? with
  | none => intro h; exact h.elim
  | some e => exact fun h ht => cap5_of_ctrlRight5 hne h.1 ht

/-- A leaf of the places is in its own footprint. -/
theorem mem_footprint_self {P : List Place} {l : Nat} (hleaf : isLeaf P l) (hlt : l < P.length) :
    l ∈ footprint P l :=
  (Arena.mem_footprint_leaf hleaf hlt).2 rfl

/-- Brief of slice 3, task 4, step form: an `ok` step whose guard-free forms hold, from a state
whose live contexts have nonempty stacks (`FramesC`, WC5.2 C3), is made with `cap5` at least the
required mode on every existing leaf of its final footprint. -/
theorem capacity_step {k : K} {L : MutexLayout} {st st' : SC × SyncReg × ArenaReg} {lbl : Label}
    {l : Nat} (hF : FramesC st.1) (hs : LStep k L lbl st st') (hp : PremG k L st lbl)
    (hleaf : isLeaf st.1.P l) (hlt : l < st.1.P.length) (ht : TouchesF L st lbl l) :
    CapReq k st lbl l := by
  cases hs with
  | @kernel s s' reg ar c op hk =>
    cases op with
    | read a ls => exact (cap5_sound_state hF).1 hp hk l ht
    | write a ls => exact (cap5_sound_state hF).2.1 hp hk l ht
    | writeShared a ls => exact (cap5_sound_state hF).2.2 hp hk l ht
    | store a p =>
      have hne := hF.nonempty c hk.1
      have hl : l = p := ht
      subst hl
      exact cap5_of_hasRight5 hne hp.1 (mem_footprint_self hleaf hlt)
    | transfer src dst =>
      have hne := hF.nonempty c hk.1
      rcases ht with hl | hl
      · exact cap5_of_hasRight5 hne hp.1 hl
      · exact cap5_of_hasRight5 hne hp.2.1 hl
    | endUse p => exact fun hl => cap5_of_hasRight5 (hF.nonempty c hk.1) hp.1 hl
    | free p au => exact fun hl => cap5_of_hasRight5 (hF.nonempty c hk.1) hp.1 hl
    | alloc pr ow ls =>
      have hne := hF.nonempty c hk.1
      refine ⟨fun hl => ?_, fun hl => ?_⟩
      · rcases hp.1 with hr | ⟨via, -, hws, hx⟩
        · have hm := cap5_of_hasRight5 hne hr hl
          exact ⟨allows_observe_of_modify hm, .inl hm⟩
        · exact ⟨cap5_of (Exer5.attr5 hne hx) (allows_observe (hws.effectivePresent l hl)),
            .inr (hws.shared l hl)⟩
      · subst hl
        exact cap5_of_hasRight5 hne hp.2 (mem_footprint_self hleaf hlt)
    | _ => trivial
  | @newMutex s reg ar c g st₁ hn =>
    have hne := hF.nonempty c hn.1
    have hr := hp.2
    have hc : ControlOf L s ⟨g, none⟩ = some l := ht
    unfold NewMutexRightG at hr
    rw [hc] at hr
    obtain ⟨a, -, hx, he⟩ := hr
    exact cap5_of (Exer5.attr5 hne hx) (by rw [he]; exact Or.inr rfl)
  | @acquire s reg ar c i st₁ ha =>
    exact cap5_of_ctrl_bind (P := fun e => AuthG L (s, reg) c e.guarded) (hF.nonempty c ha.1) hp ht
  | @unlock s reg ar c i st₁ hu =>
    refine cap5_of_ctrl_bind (P := fun _ => True) (hF.nonempty c hu.1) ?_ ht
    have h2 := hp
    simp only [PremG] at h2
    revert h2
    cases reg[i]? with
    | none => exact id
    | some e => exact fun h => ⟨h.2, trivial⟩
  | @resetLock s reg ar c i st₁ hr =>
    refine cap5_of_ctrl_bind (P := fun _ => True) (hF.nonempty c hr.1) ?_ ht
    have h2 := hp.2
    revert h2
    cases reg[i]? with
    | none => exact id
    | some e => exact fun h => ⟨h, trivial⟩
  | @issue s reg ar c i region dst st₁ hs =>
    obtain ⟨E, s₁, hE, -, -, hsp, -, -⟩ := issueStepC_ok hs
    have hne := hF.nonempty c hsp.1
    have hl : l = dst := ht
    subst hl
    have h2 := hp
    simp only [PremG] at h2
    rw [hE] at h2
    exact cap5_of_hasRight5 hne h2.2.1 (mem_footprint_self hleaf hlt)
  | _ => trivial

/-- The states of a `RunFull` from the initial state of Spec 1 §47, under `DDSound` (Spec 1 §80),
satisfy the kernel and library invariants (`trace_inv`). -/
theorem runFull_inv {k : K} {L : MutexLayout} {statics : Statics}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} (hdd : DDSound k)
    (hstat : StaticsOK statics) (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], []))
    (h : RunFull k L σ lbls) {i : Nat} (hi : i ≤ lbls.length) :
    KInvCA (σ i).1 ∧ LibInv L (σ i) := by
  have htr := run5R_prefix (run7_run5R (runFull_run7 h)) hi
  rw [h0] at htr
  obtain ⟨hk₀, hs₀⟩ := init_inv (k := k) hdd hstat L
  exact trace_inv hdd htr hk₀ hs₀

/-- Brief of slice 3, task 4: on a `RunFull` from the initial state, under `DDSound`, every step of
a context whose final footprint contains an existing leaf `l` is made with `cap5` at least the
mode its clause requires on `l` (`CapReq`). -/
theorem capacity_run {k : K} {L : MutexLayout} {statics : Statics}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} (hdd : DDSound k)
    (hstat : StaticsOK statics) (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], []))
    (h : RunFull k L σ lbls) {i : Nat} (hi : i < lbls.length) {l : Nat}
    (hleaf : isLeaf (σ i).1.P l) (hlt : l < (σ i).1.P.length)
    (ht : TouchesF L (σ i) lbls[i] l) : CapReq k (σ i) lbls[i] l :=
  capacity_step (runFull_inv hdd hstat h0 h (Nat.le_of_lt hi)).1.parts.1 (h i hi).2 (h i hi).1.2
    hleaf hlt ht

/-! ## Kinds without object -/

/-- The kinds whose final footprint is empty (`derive`, `split`, `release`, `depend`, `pin`,
`unpin`, `join`, raw `deriveSync`, `newArena`, `reset`) or made of fresh places only
(`enterFrame`, `spawn`). -/
def VoidKind : Label → Prop
  | .kernel _ (.derive _ _ _) | .kernel _ (.split _ _) | .kernel _ (.release _)
  | .kernel _ (.depend _ _) | .kernel _ (.pin _) | .kernel _ (.unpin _)
  | .kernel _ (.enter _ _) | .spawn _ _ _ | .join _ _ | .deriveSync _ _ | .newArena _ _ _
  | .reset _ _ => True
  | _ => False

/-- Brief of slice 3, task 4, "sans objet": the final footprint of these kinds contains no existing
place. -/
theorem touchesF_void {L : MutexLayout} {st : SC × SyncReg × ArenaReg} {lbl : Label} {l : Nat}
    (hv : VoidKind lbl) (ht : TouchesF L st lbl l) : st.1.P.length ≤ l := by
  cases lbl with
  | kernel c op =>
    cases op <;> first | exact ht.elim | exact ht | exact hv.elim
  | spawn => exact ht
  | _ => first | exact ht.elim | exact hv.elim

/-! ## By-value `spawn` -/

/-- The capacity of `c` on the sources of the transfer phases (WC5.2 C5.2): at the start of each
phase, `Modify` on every leaf of its source. -/
def PhaseCap (reg : SyncReg) (c : Nat) : SC → List (Nat × Nat) → Prop
  | _, [] => True
  | t, v :: vs => (∀ l ∈ footprint t.P v.1, Allows (cap5 t reg c l) .modify) ∧
      PhaseCap reg c (transferEffC t c v.1 v.2) vs

/-- The phases of the by-value composite keep the stack of the executing context (`SC.set` keeps
the contexts, WC5.2 C2). -/
theorem phaseCap_of {reg : SyncReg} {c : Nat} :
    ∀ (t : SC) (vs : List (Nat × Nat)), t.stk c ≠ [] → ValRightsG reg c t vs → PhaseCap reg c t vs
  | _, [], _, _ => trivial
  | t, v :: vs, hne, ⟨⟨hr, _⟩, h⟩ =>
    ⟨fun _ hl => cap5_of_hasRight5 hne hr hl, phaseCap_of (transferEffC t c v.1 v.2) vs hne h⟩

/-- The creation phase of the by-value composite keeps the stack of the creating context (WC5.2
C5 phase 1: the new context is appended). -/
theorem stk_spawnCreate {s : SC} {c : Nat} {ls : LocalShape} (hl : s.Live c) :
    (spawnCreate s c ls).stk c = s.stk c := by
  have hc : c < s.C.length := by
    unfold SC.Live at hl
    cases hx : s.C[c]? with
    | none => rw [hx] at hl; exact hl.elim
    | some x => exact (List.getElem?_eq_some_iff.1 hx).1
  unfold SC.stk
  simp only [spawnCreate, spawnEff]
  rw [List.getElem?_append_left hc]

/-- An `ok` by-value `spawn` is executed by a live context (WC5.2 C4 item 1). -/
theorem live_of_spawnVal {k : K} {L : MutexLayout} {c : Nat} {ps : List Nat} {ls : LocalShape}
    {vs : List (Nat × Nat)} {st st' : SC × SyncReg × ArenaReg}
    (h : LStep k L (.spawnVal c ps ls vs) st st') : st.1.Live c := by
  cases h with
  | spawnVal hv => exact hv.1

/-- Brief of slice 3, task 4, by-value `spawn`: on a `RunFull` from the initial state, at the start
of each transfer phase of a by-value `spawn` step (WC5.2 C5.2), the creating context has `cap5`
`Modify` on every leaf of the source of that phase, read in the phase state. -/
theorem capacity_spawnVal {k : K} {L : MutexLayout} {statics : Statics}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} (hdd : DDSound k)
    (hstat : StaticsOK statics) (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], []))
    (h : RunFull k L σ lbls) {i : Nat} (hi : i < lbls.length) {c : Nat} {ps : List Nat}
    {ls : LocalShape} {vs : List (Nat × Nat)} (hl : lbls[i] = .spawnVal c ps ls vs) :
    PhaseCap (σ i).2.1 c (spawnCreate (σ i).1 c ls) vs := by
  have hF := (runFull_inv hdd hstat h0 h (Nat.le_of_lt hi)).1.parts.1
  have hs := (h i hi).2
  have hp := (h i hi).1.2
  rw [hl] at hs hp
  have hlv := live_of_spawnVal hs
  exact phaseCap_of _ vs (by rw [stk_spawnCreate hlv]; exact hF.nonempty c hlv) hp

end Ern.Concurrency.FullEncap
