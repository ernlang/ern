import Ern.Concurrency.FullEncap.KillKinds
import Ern.Concurrency.FullEncap.DyingCap
import Ern.Concurrency.FullEncap.SpawnValCap
import Ern.Concurrency.EventsStrictProtocols

/-!
# Extended abstract handoff: definitions

Brief of milestone 4, slice 4 (`formal/reports/spec2-m4-handoff-ext.md`; `corpus-spec2-m3.md`
v15 §2 quaterdecies, "Vocabulaire"). The handoff results of the event pass (`lossStep_own`,
`handoffOrdered_no_raceS`) cover the pairs of direct accesses only (`ExclPair`). This module
extends the pair, the frontier and the race to every step that touches a leaf, beside the
existing definitions, which are unchanged.

Scope (brief, "Portée du résultat"): the statements bear on the abstract steps and on the graph
with one event per step. They say nothing of the physical accesses a composite step generates,
nor of their order (WC5.3 `OB-C19`, `OB-C20`). "Touching a leaf" is a notion of the model; it does
not extend the normative domain of WC5.3 C44–C46, which speaks of access events. The criterion of
exclusivity is the mode the clause requires (WC5.3 C44), not the byte conflict of C30. Extended
handoff order is the abstract analogue of C46, not C46; an extended race is a fact about the
model, not a normative verdict.

* `Created`, `CW`: a place created by a step, a leaf created and written by it (`Init` after the
  step; Spec 1 §59; WC5.3 C5 effects).
* `TouchL`: a step touches a leaf `l` when `l` is an existing leaf in its final footprint
  (`TouchesF`), a created leaf in it, or a leaf it creates and writes.
* `ClassD`, `ClassC`, `ClassE`, `ClassN`: the classes of a touch, read in that order of priority.
  `HasReq` and `ReqMode` read the required mode off the clause, as `CapReq` does.
* `ExtPair`: the extended exclusive pair. `TouchCompat`, `FrontAt`, `IsFrontier`: the abstract
  handoff frontier. `HandoffOrderedExtAt`, `HandoffOrderedExt`, `RaceExt` and their strict forms.
-/

set_option autoImplicit false

namespace Ern.Concurrency.FullEncap.HandoffExt

open Ern.MemoryModel Ern.MemoryModel.Access Ern.Concurrency Ern.Concurrency.MutexReal

/-! ## Touching a leaf -/

/-- A place created by the step from `st` to `st'`: an identity at least the number of places
before the step and below the number after it (Spec 1 §40, §71, §72 effects; WC5.3 C4 effect,
C5 phase 1). -/
def Created (st st' : SC × SyncReg × ArenaReg) (l : Nat) : Prop :=
  st.1.P.length ≤ l ∧ l < st'.1.P.length

/-- Decidability of `Created`. -/
instance (st st' : SC × SyncReg × ArenaReg) (l : Nat) : Decidable (Created st st' l) := by
  unfold Created; infer_instance

/-- A leaf created and written by the step (brief, class C, "feuille créée et écrite par le pas ;
elle se lit dans l'état d'après le pas"): created, a leaf after the step and `Init` after it. A
leaf becomes `Init` only through a permitted write or a transfer (Spec 1 §59); the destinations of
a by-value `spawn` become `Init` by its transfer phase (WC5.3 C5 effects). -/
def CW (st st' : SC × SyncReg × ArenaReg) (l : Nat) : Prop :=
  Created st st' l ∧ isLeaf st'.1.P l ∧ st'.1.I l = .init

/-- Decidability of `CW`. -/
instance (st st' : SC × SyncReg × ArenaReg) (l : Nat) : Decidable (CW st st' l) := by
  unfold CW; infer_instance

/-- A step touches the leaf `l` (brief, "Toucher"; corpus v15 §2 quaterdecies, "Vocabulaire"):
`l` is in its final footprint (`TouchesF`, the footprint of the capacity table of slice 3) and is
an existing leaf before the step or a leaf created by it; or the step creates `l` and writes it.
The touch is read on leaves: `TouchesF` also holds of identities the step does not create (the
fresh part `|P| ≤ l` of `enterFrame`, `spawn`, `alloc` and the by-value `spawn`), which are no
leaf. -/
def TouchL (L : MutexLayout) (st st' : SC × SyncReg × ArenaReg) (lbl : Label) (l : Nat) : Prop :=
  (l < st.1.P.length ∧ isLeaf st.1.P l ∧ TouchesF L st lbl l) ∨
    (Created st st' l ∧ isLeaf st'.1.P l ∧ TouchesF L st lbl l) ∨ CW st st' l

/-- Decidability of `TouchL`. -/
instance (L : MutexLayout) (st st' : SC × SyncReg × ArenaReg) (lbl : Label) (l : Nat) :
    Decidable (TouchL L st st' lbl l) := by
  unfold TouchL; infer_instance

/-! ## Required mode -/

/-- The leaves on which the clause of the step requires a mode, as in `CapReq` (brief of slice 3,
task 4): the leaves of the accesses (Spec 1 §66.2, §67.1, §68.2), every touched leaf of `store`,
`transfer` (§65.2, §63.1), `issue` (§77.2), `newMutex` (WC5.3 C13 item 11), `acquire`, `unlock`,
`resetLock` (C14 item 3, C17 item 4, C18 item 4); the leaves of `place` for `endUse` and `free`
(§69.1, §70.3); the provider and the owner of `alloc` (§71.2, §71.3); the leaves of the sources of
a by-value `spawn` (WC5.3 C5, additional precondition 1). -/
def HasReq (st : SC × SyncReg × ArenaReg) : Label → Nat → Prop
  | .kernel _ (.read _ _), _ | .kernel _ (.write _ _), _ | .kernel _ (.writeShared _ _), _
  | .kernel _ (.store _ _), _ | .kernel _ (.transfer _ _), _ => True
  | .kernel _ (.endUse p), l | .kernel _ (.free p _), l => l ∈ footprint st.1.P p
  | .kernel _ (.alloc pr ow _), l => l ∈ footprint st.1.P pr ∨ l = ow
  | .issue _ _ _ _, _ | .newMutex _ _, _ | .acquire _ _, _ | .unlock _ _, _
  | .resetLock _ _, _ => True
  | .spawnVal _ _ _ vs, l => ∃ v ∈ vs, l ∈ footprint st.1.P v.1
  | _, _ => False

/-- Decidability of `HasReq`. -/
instance (st : SC × SyncReg × ArenaReg) (lbl : Label) (l : Nat) : Decidable (HasReq st lbl l) := by
  unfold HasReq; split <;> infer_instance

/-- The mode the clause of the step requires on `l`, as `CapReq` reads it: `Observe` for `read3`,
`writeShared`, `acquire`, `unlock`, `resetLock`; `Modify` for the others. For the provider of
`alloc`, §71.2 admits two branches, exercisable `Modify` or a `writeShared` over `SharedMutable`
metadata; `CapReq` encodes them on each leaf by `Allows Observe ∧ (Allows Modify ∨
K.SharedMutable l)`, so the required mode is `Observe` on a `SharedMutable` leaf and `Modify`
otherwise. On the owner (§71.3), `Modify`. On the sources of a by-value `spawn`, `Modify` at the
start of their transfer phase (WC5.3 C5, additional precondition 1; `spawnVal_cap_pre`). -/
def ReqMode (k : K) (st : SC × SyncReg × ArenaReg) : Label → Nat → Mode → Prop
  | .kernel _ (.read _ _), _, m | .kernel _ (.writeShared _ _), _, m => m = .observe
  | .kernel _ (.write _ _), _, m | .kernel _ (.store _ _), _, m
  | .kernel _ (.transfer _ _), _, m => m = .modify
  | .kernel _ (.endUse p), l, m | .kernel _ (.free p _), l, m =>
    l ∈ footprint st.1.P p ∧ m = .modify
  | .kernel _ (.alloc pr ow _), l, m => (l = ow ∧ m = .modify) ∨
    (l ≠ ow ∧ l ∈ footprint st.1.P pr ∧
      ((k.SharedMutable l ∧ m = .observe) ∨ (¬ k.SharedMutable l ∧ m = .modify)))
  | .issue _ _ _ _, _, m | .newMutex _ _, _, m => m = .modify
  | .acquire _ _, _, m | .unlock _ _, _, m | .resetLock _ _, _, m => m = .observe
  | .spawnVal _ _ _ vs, l, m => (∃ v ∈ vs, l ∈ footprint st.1.P v.1) ∧ m = .modify
  | _, _, _ => False

/-- Decidability of `ReqMode`, for a contract whose `SharedMutable` is decidable. -/
instance (k : K) [DecidablePred k.SharedMutable] (st : SC × SyncReg × ArenaReg) (lbl : Label)
    (l : Nat) (m : Mode) : Decidable (ReqMode k st lbl l m) := by
  unfold ReqMode; split <;> infer_instance

/-- `ReqMode` names one mode at most. -/
theorem reqMode_unique {k : K} {st : SC × SyncReg × ArenaReg} {lbl : Label} {l : Nat}
    {m m' : Mode} (h : ReqMode k st lbl l m) (h' : ReqMode k st lbl l m') : m = m' := by
  cases lbl with
  | kernel c op =>
    cases op with
    | read | writeShared | write | store | transfer =>
      simp only [ReqMode] at h h'; rw [h, h']
    | endUse | free =>
      simp only [ReqMode] at h h'; rw [h.2, h'.2]
    | alloc pr ow ls =>
      simp only [ReqMode] at h h'
      rcases h with ⟨rfl, rfl⟩ | ⟨hne, -, ⟨hs, rfl⟩ | ⟨hs, rfl⟩⟩ <;>
        rcases h' with ⟨he, rfl⟩ | ⟨hne', -, ⟨hs', rfl⟩ | ⟨hs', rfl⟩⟩ <;>
        first | rfl | exact absurd he hne | exact absurd rfl hne' | exact absurd hs hs' |
          exact absurd hs' hs
    | _ => simp only [ReqMode] at h
  | issue | newMutex | acquire | unlock | resetLock =>
    simp only [ReqMode] at h h'; rw [h, h']
  | spawnVal => simp only [ReqMode] at h h'; rw [h.2, h'.2]
  | _ => simp only [ReqMode] at h

/-- A required mode is on a leaf where a mode is required. -/
theorem hasReq_of_reqMode {k : K} {st : SC × SyncReg × ArenaReg} {lbl : Label} {l : Nat}
    {m : Mode} (h : ReqMode k st lbl l m) : HasReq st lbl l := by
  cases lbl with
  | kernel c op =>
    cases op with
    | read | writeShared | write | store | transfer => trivial
    | endUse | free => exact h.1
    | alloc pr ow ls =>
      rcases h with ⟨rfl, -⟩ | ⟨-, hl, -⟩
      · exact .inr rfl
      · exact .inl hl
    | _ => exact h.elim
  | issue | newMutex | acquire | unlock | resetLock => trivial
  | spawnVal => exact h.1
  | _ => exact h.elim

/-! ## Classes of a touch -/

/-- Class D (brief): an existing leaf that dies in the step (`Dying`), read on the transition,
before and after. -/
def ClassD (st st' : SC × SyncReg × ArenaReg) (l : Nat) : Prop := Dying st.1 st'.1 l

/-- Class C (brief): a leaf created and written by the step, read in the state after it. -/
def ClassC (st st' : SC × SyncReg × ArenaReg) (l : Nat) : Prop := CW st st' l

/-- Class E (brief): an existing leaf that does not die, on which the clause requires a mode. -/
def ClassE (st st' : SC × SyncReg × ArenaReg) (lbl : Label) (l : Nat) : Prop :=
  l < st.1.P.length ∧ isLeaf st.1.P l ∧ ¬ Dying st.1 st'.1 l ∧ HasReq st lbl l

/-- Class E with its required mode `m`. -/
def ClassEm (k : K) (st st' : SC × SyncReg × ArenaReg) (lbl : Label) (l : Nat) (m : Mode) :
    Prop :=
  ClassE st st' lbl l ∧ ReqMode k st lbl l m

/-- Class N (brief): every other touched leaf. -/
def ClassN (L : MutexLayout) (st st' : SC × SyncReg × ArenaReg) (lbl : Label) (l : Nat) : Prop :=
  TouchL L st st' lbl l ∧ ¬ ClassD st st' l ∧ ¬ ClassC st st' l ∧ ¬ ClassE st st' lbl l

/-- Decidability of `ClassD`. -/
instance (st st' : SC × SyncReg × ArenaReg) (l : Nat) : Decidable (ClassD st st' l) := by
  unfold ClassD; infer_instance

/-- Decidability of `ClassC`. -/
instance (st st' : SC × SyncReg × ArenaReg) (l : Nat) : Decidable (ClassC st st' l) := by
  unfold ClassC; infer_instance

/-- Decidability of `ClassE`. -/
instance (st st' : SC × SyncReg × ArenaReg) (lbl : Label) (l : Nat) :
    Decidable (ClassE st st' lbl l) := by
  unfold ClassE; infer_instance

/-- Decidability of `ClassEm`. -/
instance (k : K) [DecidablePred k.SharedMutable] (st st' : SC × SyncReg × ArenaReg) (lbl : Label)
    (l : Nat) (m : Mode) : Decidable (ClassEm k st st' lbl l m) := by
  unfold ClassEm; infer_instance

/-- Decidability of `ClassN`. -/
instance (L : MutexLayout) (st st' : SC × SyncReg × ArenaReg) (lbl : Label) (l : Nat) :
    Decidable (ClassN L st st' lbl l) := by
  unfold ClassN; infer_instance

/-- An exclusive touch (brief, "Toucher exclusif"): class D, class C, or class E with `Modify`
required. -/
def ExclTouch (k : K) (L : MutexLayout) (st st' : SC × SyncReg × ArenaReg) (lbl : Label)
    (l : Nat) : Prop :=
  TouchL L st st' lbl l ∧ (ClassD st st' l ∨ ClassC st st' l ∨ ClassEm k st st' lbl l .modify)

/-- Decidability of `ExclTouch`. -/
instance (k : K) [DecidablePred k.SharedMutable] (L : MutexLayout)
    (st st' : SC × SyncReg × ArenaReg) (lbl : Label) (l : Nat) :
    Decidable (ExclTouch k L st st' lbl l) := by
  unfold ExclTouch; infer_instance

/-! ## Extended exclusive pairs, frontier, races -/

/-- Extended exclusive pair `(i, j, l)` (brief, "Paire exclusive étendue"): `i < j`, steps of
distinct contexts, both touching `l`, at least one of them exclusively. -/
def ExtPair (k : K) (L : MutexLayout) (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label)
    (i j l : Nat) : Prop :=
  i < j ∧ OptP (lbls[i]?) (fun li => OptP (lbls[j]?) (fun lj => li.ctx ≠ lj.ctx ∧
    TouchL L (σ i) (σ (i + 1)) li l ∧ TouchL L (σ j) (σ (j + 1)) lj l ∧
    (ExclTouch k L (σ i) (σ (i + 1)) li l ∨ ExclTouch k L (σ j) (σ (j + 1)) lj l)) False) False

/-- Decidability of `ExtPair`. -/
instance (k : K) [DecidablePred k.SharedMutable] (L : MutexLayout)
    (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) (i j l : Nat) :
    Decidable (ExtPair k L σ lbls i j l) := by
  unfold ExtPair; infer_instance

/-- A capability `o` of the context of step `i` is compatible with the touch of step `j` (brief,
"Compatibilité avec le toucher de `j`"): `o = none` when the touch of `j` is of class D; `CapCompat`
with the required mode when it is of class E. The required mode is read universally, which is
equivalent since it is unique (`touchCompat_iff_of_classEm`). A touch of class C or N has no
compatible capability. -/
def TouchCompat (k : K) (st st' : SC × SyncReg × ArenaReg) (lbl : Label) (l : Nat)
    (o : Option Mode) : Prop :=
  (ClassD st st' l ∧ o = none) ∨
    (ClassE st st' lbl l ∧ (ReqMode k st lbl l .observe → CapCompat o .observe = true) ∧
      (ReqMode k st lbl l .modify → CapCompat o .modify = true))

/-- Decidability of `TouchCompat`. -/
instance (k : K) [DecidablePred k.SharedMutable] (st st' : SC × SyncReg × ArenaReg) (lbl : Label)
    (l : Nat) (o : Option Mode) : Decidable (TouchCompat k st st' lbl l o) := by
  unfold TouchCompat; infer_instance

/-- On a touch of class E with required mode `m`, `TouchCompat` is `CapCompat` with `m`. -/
theorem touchCompat_iff_of_classEm {k : K} {st st' : SC × SyncReg × ArenaReg} {lbl : Label}
    {l : Nat} {m : Mode} (h : ClassEm k st st' lbl l m) (o : Option Mode) :
    TouchCompat k st st' lbl l o ↔ CapCompat o m = true := by
  obtain ⟨hE, hm⟩ := h
  constructor
  · rintro (⟨hD, -⟩ | ⟨-, ho, hmo⟩)
    · exact absurd hD hE.2.2.1
    · cases m with
      | observe => exact ho hm
      | modify => exact hmo hm
  · intro hc
    refine .inr ⟨hE, fun h' => ?_, fun h' => ?_⟩
    · rw [← reqMode_unique hm h']; exact hc
    · rw [← reqMode_unique hm h']; exact hc

/-- On a touch of class D, `TouchCompat` is `o = none`. -/
theorem touchCompat_iff_of_classD {k : K} {st st' : SC × SyncReg × ArenaReg} {lbl : Label}
    {l : Nat} (h : ClassD st st' l) (o : Option Mode) :
    TouchCompat k st st' lbl l o ↔ o = none := by
  constructor
  · rintro (⟨-, ho⟩ | ⟨hE, -⟩)
    · exact ho
    · exact absurd h hE.2.2.1
  · intro ho; exact .inl ⟨h, ho⟩

/-- The frontier predicate at step `q` for the pair `(i, j, l)`: at the issue of step `q`, `cap5`
of the context of step `i` on `l` is compatible with the touch of step `j`. -/
def FrontAt (k : K) (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) (i j l q : Nat) :
    Prop :=
  OptP (lbls[i]?) (fun li => OptP (lbls[j]?) (fun lj =>
    TouchCompat k (σ j) (σ (j + 1)) lj l (cap5 (σ (q + 1)).1 (σ (q + 1)).2.1 li.ctx l)) False)
    False

/-- Decidability of `FrontAt`. -/
instance (k : K) [DecidablePred k.SharedMutable] (σ : Nat → SC × SyncReg × ArenaReg)
    (lbls : List Label) (i j l q : Nat) : Decidable (FrontAt k σ lbls i j l q) := by
  unfold FrontAt; infer_instance

/-- The abstract handoff frontier of `(i, j, l)` is `r` (brief, "Frontière de passation
abstraite"): the first step `r ≥ i` of the trace at the issue of which `cap5` of the context of
`i` on `l` is compatible with the touch of `j`. As for `lossStep`, it is searched in the whole
trace and not bounded by `j`. A frontier is unique (`isFrontier_unique`); "none" is the absence of
any. -/
def IsFrontier (k : K) (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) (i j l r : Nat) :
    Prop :=
  i ≤ r ∧ r < lbls.length ∧ FrontAt k σ lbls i j l r ∧
    ∀ q ∈ List.range r, i ≤ q → ¬ FrontAt k σ lbls i j l q

/-- Decidability of `IsFrontier`. -/
instance (k : K) [DecidablePred k.SharedMutable] (σ : Nat → SC × SyncReg × ArenaReg)
    (lbls : List Label) (i j l r : Nat) : Decidable (IsFrontier k σ lbls i j l r) := by
  unfold IsFrontier; infer_instance

/-- A frontier is unique. -/
theorem isFrontier_unique {k : K} {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label}
    {i j l r r' : Nat} (h : IsFrontier k σ lbls i j l r) (h' : IsFrontier k σ lbls i j l r') :
    r = r' := by
  rcases Nat.lt_trichotomy r r' with hl | he | hg
  · exact absurd h.2.2.1 (h'.2.2.2 r (List.mem_range.2 hl) h.1)
  · exact he
  · exact absurd h'.2.2.1 (h.2.2.2 r' (List.mem_range.2 hg) h'.1)

/-- Extended handoff order for one pair (brief, "Passation ordonnée étendue"): the frontier
exists and is `hb`-before step `j`. A missing frontier is a failure (WC5.3 C46, by analogy). -/
def HandoffOrderedExtAt (k : K) (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label)
    (i j l : Nat) : Prop :=
  ∃ r ∈ List.range lbls.length, IsFrontier k σ lbls i j l r ∧ HB σ lbls (.step r) (.step j)

/-- Extended handoff order on the strict graph. -/
def HandoffOrderedExtAtS (k : K) (σ : Nat → SC × SyncReg × ArenaReg) (L : MutexLayout)
    (lbls : List Label) (i j l : Nat) : Prop :=
  ∃ r ∈ List.range lbls.length, IsFrontier k σ lbls i j l r ∧ HBS σ L lbls (.step r) (.step j)

/-- Decidability of `HandoffOrderedExtAt`. -/
instance (k : K) [DecidablePred k.SharedMutable] (σ : Nat → SC × SyncReg × ArenaReg)
    (lbls : List Label) (i j l : Nat) : Decidable (HandoffOrderedExtAt k σ lbls i j l) := by
  unfold HandoffOrderedExtAt; infer_instance

/-- Decidability of `HandoffOrderedExtAtS`. -/
instance (k : K) [DecidablePred k.SharedMutable] (σ : Nat → SC × SyncReg × ArenaReg)
    (L : MutexLayout) (lbls : List Label) (i j l : Nat) :
    Decidable (HandoffOrderedExtAtS k σ L lbls i j l) := by
  unfold HandoffOrderedExtAtS; infer_instance

/-- Extended handoff order (brief): every extended exclusive pair satisfies
`HandoffOrderedExtAt`. -/
def HandoffOrderedExt (k : K) (L : MutexLayout) (σ : Nat → SC × SyncReg × ArenaReg)
    (lbls : List Label) : Prop :=
  ∀ i j l, ExtPair k L σ lbls i j l → HandoffOrderedExtAt k σ lbls i j l

/-- Extended handoff order on the strict graph. -/
def HandoffOrderedExtS (k : K) (L : MutexLayout) (σ : Nat → SC × SyncReg × ArenaReg)
    (lbls : List Label) : Prop :=
  ∀ i j l, ExtPair k L σ lbls i j l → HandoffOrderedExtAtS k σ L lbls i j l

/-- Extended race (brief, "course étendue"): an extended exclusive pair without `hb`. A fact
about the abstract model, not a verdict of WC5.3 C46. -/
def RaceExt (k : K) (L : MutexLayout) (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) :
    Prop :=
  ∃ i j l, ExtPair k L σ lbls i j l ∧ ¬ HB σ lbls (.step i) (.step j)

/-- Extended race on the strict graph. -/
def RaceExtS (k : K) (L : MutexLayout) (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) :
    Prop :=
  ∃ i j l, ExtPair k L σ lbls i j l ∧ ¬ HBS σ L lbls (.step i) (.step j)

end Ern.Concurrency.FullEncap.HandoffExt
