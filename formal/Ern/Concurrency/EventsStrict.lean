import Ern.Concurrency.Events

/-!
# The strict mutex edge

Brief of milestone 4, strict mutex edge, task 3 (`formal/reports/spec2-m4-events.md`, § Arête
stricte du mutex). The edge of the mutex of `Ern.Concurrency.Events` goes from an `unlock(e)` to the
next successful `acquire(e)`; WC5.1 requires the `acquire` to read directly, on the same atomic
unit, the publication of the `unlock` (WC5.1 C32 item 1, C48). The strict edge keeps it only when
no `resetLock(e)` lies between the two steps (WC5.1 C18 effect, C49) and the controller of `e`
designates the same leaf in every state between them (WC5.1 C21 item 3; `corpus-spec2-m3.md` v9
§2 octies). The strict graph has the same `po` and the same `spawn` and `join` edges. Nothing of
`Ern.Concurrency.Events` is changed.
-/

namespace Ern.Concurrency

open Ern.MemoryModel.Access

/-! ## Definitions -/

/-- The entry reset by `lbl` (WC5.1 C18). -/
def Label.resetLockOf : Label → Option Nat
  | .resetLock _ i => some i
  | _ => none

/-- The controller of entry `i` in the state `σ k`, as the model computes it (`ControlOf`, WC5.1
C21 item 3); `none` if there is no entry `i` or no controller. -/
def ctlAt (σ : Nat → SC × SyncReg × ArenaReg) (L : MutexLayout) (i k : Nat) : Option Nat :=
  ((σ k).2.1[i]?).bind (ControlOf L (σ k).1)

/-- The conditions of the strict mutex edge from an `unlock(e)` at step `u` to an `acquire(e)` at
step `a` (brief, "Arête stricte du mutex"): no `resetLock(e)` at a step strictly between `u` and
`a`; and the controller of `e` designates the same leaf in every state from the issue of step `u`
(`σ (u + 1)`) to the entry of step `a` (`σ a`): it is defined at `σ (u + 1)` and equal to that
leaf at every state up to `σ a`. -/
def MutexGap (σ : Nat → SC × SyncReg × ArenaReg) (L : MutexLayout) (lbls : List Label)
    (e u a : Nat) : Prop :=
  (∀ p ∈ List.range a, u < p → (lbls[p]?).bind Label.resetLockOf ≠ some e) ∧
    ctlAt σ L e (u + 1) ≠ none ∧
    ∀ k ∈ List.range (a + 1), u + 1 ≤ k → ctlAt σ L e k = ctlAt σ L e (u + 1)

/-- Decidability of `MutexGap`. -/
instance (σ : Nat → SC × SyncReg × ArenaReg) (L : MutexLayout) (lbls : List Label)
    (e u a : Nat) : Decidable (MutexGap σ L lbls e u a) := by
  unfold MutexGap; infer_instance

/-- Strict `sw` (brief, "Graphe strict"): the edges of `SW` from `spawn` or `spawnVal` to
`start(c)` and from `terminate(c)` to a later `join` of `c`, unchanged; the strict mutex edge, from
`unlock(e)` to the first later `acquire(e)` when `MutexGap` holds between them. -/
def SWS (σ : Nat → SC × SyncReg × ArenaReg) (L : MutexLayout) (lbls : List Label) :
    Ev → Ev → Prop
  | .step i, .start j => i = j ∧ (lbls[i]?).map Label.creates = some true
  | .step i, .step j =>
    i < j ∧ j < lbls.length ∧
      (OptP ((lbls[i]?).bind Label.termOf) (fun d => (lbls[j]?).bind Label.joinOf = some d) False ∨
       OptP ((lbls[i]?).bind Label.unlockOf) (fun e => (lbls[j]?).bind Label.acquireOf = some e ∧
         (∀ p ∈ List.range j, i < p → (lbls[p]?).bind Label.acquireOf ≠ some e) ∧
         MutexGap σ L lbls e i j) False)
  | _, _ => False

/-- Decidability of `SWS`. -/
instance (σ : Nat → SC × SyncReg × ArenaReg) (L : MutexLayout) (lbls : List Label) (e e' : Ev) :
    Decidable (SWS σ L lbls e e') := by
  unfold SWS; split <;> infer_instance

/-- An edge of the strict graph: `po` or strict `sw`. -/
def EdgeS (σ : Nat → SC × SyncReg × ArenaReg) (L : MutexLayout) (lbls : List Label)
    (e e' : Ev) : Prop :=
  PO σ lbls e e' ∨ SWS σ L lbls e e'

/-- Decidability of `EdgeS`. -/
instance (σ : Nat → SC × SyncReg × ArenaReg) (L : MutexLayout) (lbls : List Label) (e e' : Ev) :
    Decidable (EdgeS σ L lbls e e') := by
  unfold EdgeS; infer_instance

/-- Strict `hb` (brief, "Graphe strict"): the transitive closure of `po` and strict `sw`. -/
def HBS (σ : Nat → SC × SyncReg × ArenaReg) (L : MutexLayout) (lbls : List Label) :
    Ev → Ev → Prop :=
  Relation.TransGen (EdgeS σ L lbls)

/-- Strict `Race` (brief): `Race` read on strict `hb`. -/
def RaceS (σ : Nat → SC × SyncReg × ArenaReg) (L : MutexLayout) (lbls : List Label) : Prop :=
  ∃ i j l, ExclPair lbls i j l ∧ ¬ HBS σ L lbls (.step i) (.step j)

/-- Strict `HandoffOrderedAt` (brief): `HandoffOrderedAt` read on strict `hb`; `lossStep` is
unchanged. -/
def HandoffOrderedAtS (σ : Nat → SC × SyncReg × ArenaReg) (L : MutexLayout) (lbls : List Label)
    (i j l : Nat) : Prop :=
  ∃ r, lossStep σ lbls i j l = some r ∧ HBS σ L lbls (.step r) (.step j)

/-- Strict `HandoffOrdered` (brief): every exclusive pair satisfies `HandoffOrderedAtS`. -/
def HandoffOrderedS (σ : Nat → SC × SyncReg × ArenaReg) (L : MutexLayout)
    (lbls : List Label) : Prop :=
  ∀ i j l, ExclPair lbls i j l → HandoffOrderedAtS σ L lbls i j l

/-! ## Inclusion into the graph of `Ern.Concurrency.Events` -/

/-- Brief, task 3: every strict `sw` edge is an `sw` edge. -/
theorem sws_sw {σ : Nat → SC × SyncReg × ArenaReg} {L : MutexLayout} {lbls : List Label}
    {e e' : Ev} (h : SWS σ L lbls e e') : SW lbls e e' := by
  cases e with
  | step i =>
    cases e' with
    | step j =>
      obtain ⟨h1, h2, h3 | h3⟩ := h
      · exact ⟨h1, h2, Or.inl h3⟩
      · refine ⟨h1, h2, Or.inr ?_⟩
        revert h3
        cases (lbls[i]?).bind Label.unlockOf with
        | none => exact id
        | some e => exact fun ⟨a, b, _⟩ => ⟨a, b⟩
    | start j => exact h
  | start i => cases e' <;> exact False.elim h

/-- Every edge of the strict graph is an edge of the graph. -/
theorem edgeS_edge {σ : Nat → SC × SyncReg × ArenaReg} {L : MutexLayout} {lbls : List Label}
    {e e' : Ev} (h : EdgeS σ L lbls e e') : Edge σ lbls e e' :=
  h.imp id sws_sw

/-- Brief, task 3: strict `hb` entails `hb`. -/
theorem hbS_hb {σ : Nat → SC × SyncReg × ArenaReg} {L : MutexLayout} {lbls : List Label}
    {e e' : Ev} (h : HBS σ L lbls e e') : HB σ lbls e e' := by
  induction h with
  | single h => exact .single (edgeS_edge h)
  | tail _ h ih => exact .tail ih (edgeS_edge h)

/-- Brief, task 3: `Race` entails strict `Race`. -/
theorem race_raceS {σ : Nat → SC × SyncReg × ArenaReg} {L : MutexLayout} {lbls : List Label}
    (h : Race σ lbls) : RaceS σ L lbls := by
  obtain ⟨i, j, l, hp, hnb⟩ := h
  exact ⟨i, j, l, hp, fun hs => hnb (hbS_hb hs)⟩

/-- Strict `HandoffOrderedAt` entails `HandoffOrderedAt`. -/
theorem handoffOrderedAtS_imp {σ : Nat → SC × SyncReg × ArenaReg} {L : MutexLayout}
    {lbls : List Label} {i j l : Nat} (h : HandoffOrderedAtS σ L lbls i j l) :
    HandoffOrderedAt σ lbls i j l := by
  obtain ⟨r, hr, hb⟩ := h
  exact ⟨r, hr, hbS_hb hb⟩

/-- Brief, task 3: strict `HandoffOrdered` entails `HandoffOrdered`. -/
theorem handoffOrderedS_imp {σ : Nat → SC × SyncReg × ArenaReg} {L : MutexLayout}
    {lbls : List Label} (h : HandoffOrderedS σ L lbls) : HandoffOrdered σ lbls :=
  fun i j l hp => handoffOrderedAtS_imp (h i j l hp)

/-! ## Order, irreflexivity, decision -/

/-- Brief, task 3: strict `hb` only relates events in increasing position. -/
theorem hbS_pos {σ : Nat → SC × SyncReg × ArenaReg} {L : MutexLayout} {lbls : List Label}
    {e e' : Ev} (h : HBS σ L lbls e e') : e.pos < e'.pos :=
  hb_pos (hbS_hb h)

/-- Brief, task 3: strict `hb` is irreflexive (WC5.1 C33: acyclicity). -/
theorem hbS_irrefl {σ : Nat → SC × SyncReg × ArenaReg} {L : MutexLayout} {lbls : List Label}
    (e : Ev) : ¬ HBS σ L lbls e e :=
  fun h => Nat.lt_irrefl _ (hbS_pos h)

/-- Strict `hb` as computed by `reachList`. -/
theorem hbS_iff_reach {σ : Nat → SC × SyncReg × ArenaReg} {L : MutexLayout} {lbls : List Label}
    {e e' : Ev} : HBS σ L lbls e e' ↔
      ((reachList (EdgeS σ L lbls) e (e'.pos + 1))[e'.pos]?).getD false = true := by
  rw [reachList_spec _ _ (fun _ _ h => (edge_pos (edgeS_edge h)).1) _ _ (Nat.lt_succ_self _),
    Ev.ofPos_pos]
  rfl

/-- Brief, task 3: decidability of strict `hb` on a finite trace. -/
instance (σ : Nat → SC × SyncReg × ArenaReg) (L : MutexLayout) (lbls : List Label) (e e' : Ev) :
    Decidable (HBS σ L lbls e e') :=
  decidable_of_iff _ hbS_iff_reach.symm

/-- `HandoffOrderedAtS` as an `OptP` on the loss step. -/
theorem handoffOrderedAtS_iff {σ : Nat → SC × SyncReg × ArenaReg} {L : MutexLayout}
    {lbls : List Label} {i j l : Nat} : HandoffOrderedAtS σ L lbls i j l ↔
      OptP (lossStep σ lbls i j l) (fun r => HBS σ L lbls (.step r) (.step j)) False := by
  unfold HandoffOrderedAtS
  cases lossStep σ lbls i j l with
  | none => simp [OptP]
  | some r => simp [OptP]

/-- Decidability of `HandoffOrderedAtS`. -/
instance (σ : Nat → SC × SyncReg × ArenaReg) (L : MutexLayout) (lbls : List Label)
    (i j l : Nat) : Decidable (HandoffOrderedAtS σ L lbls i j l) :=
  decidable_of_iff _ handoffOrderedAtS_iff.symm

end Ern.Concurrency
