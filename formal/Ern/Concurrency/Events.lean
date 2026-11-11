import Ern.Concurrency.Encap5R

/-!
# Abstract event graph of an authority trace

Brief of milestone 4, event pass, task 1 (`formal/reports/spec2-m4-events.md`): the event graph of
WC5.1 C26 and C28 on a trace with named states, with the program order and the three reference
synchronization edges of WC5.1 C32 (items 2 and 3), C47 and C48 taken abstractly, and `hb`, the
transitive closure of WC5.1 C33. The edge of the mutex goes from `unlock(e)` to the next
successful `acquire(e)` in trace order; its realization by `rf` is `OB-C05` (WC5.1 C48), not proved
here. No value, `rf`, `mo`, atomic or memory order; the events internal to a step are not modeled.
Every step of a trace is an `ok` step (`LStep`), so every `join` and `acquire` of a trace is a
successful one.
-/

namespace Ern.Concurrency

open Ern.MemoryModel.Access

/-! ## Runs under `Encap5R` -/

/-- An `EncapsulatedTrace5R` with named states, as `Run5C`: `σ 0` is the first state, `σ (i + 1)`
the state after step `i`. -/
def Run5R (k : K) (L : MutexLayout) (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) :
    Prop :=
  ∀ i (h : i < lbls.length), Encap5R k L (σ i) lbls[i] ∧ LStep k L lbls[i] (σ i) (σ (i + 1))

/-- Every `Run5R` is a `Run5C`. -/
theorem run5R_imp {k : K} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg}
    {lbls : List Label} (h : Run5R k L σ lbls) : Run5C k L σ lbls :=
  fun i hi => ⟨(h i hi).1.1, (h i hi).2⟩

/-- A `Run5R` is an `EncapsulatedTrace5R` from its first state to its last. -/
theorem run5R_trace {k : K} {L : MutexLayout} :
    ∀ {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label}, Run5R k L σ lbls →
      EncapsulatedTrace5R k L (σ 0) lbls (σ lbls.length)
  | _, [], _ => .nil
  | σ, _ :: lbls, h =>
    .cons (h 0 (Nat.succ_pos _)).1 (h 0 (Nat.succ_pos _)).2
      (run5R_trace (σ := fun i => σ (i + 1)) (lbls := lbls)
        (fun i hi => h (i + 1) (Nat.succ_lt_succ hi)))

/-- A run through an explicit list of states: each step satisfies `Encap5R` in its state and is an
`ok` step from it to the next one. -/
inductive Steps5R (k : K) (L : MutexLayout) :
    List (SC × SyncReg × ArenaReg) → List Label → Prop where
  | nil {st : SC × SyncReg × ArenaReg} : Steps5R k L [st] []
  | cons {st st' : SC × SyncReg × ArenaReg} {sts : List (SC × SyncReg × ArenaReg)} {lbl : Label}
      {lbls : List Label} : Encap5R k L st lbl → LStep k L lbl st st' →
      Steps5R k L (st' :: sts) lbls → Steps5R k L (st :: st' :: sts) (lbl :: lbls)

/-- A run through an explicit list of states is a `Run5R` on that list. -/
theorem Steps5R.run {k : K} {L : MutexLayout} {sts : List (SC × SyncReg × ArenaReg)}
    {lbls : List Label} (h : Steps5R k L sts lbls) (d : SC × SyncReg × ArenaReg) :
    Run5R k L (fun i => sts.getD i d) lbls := by
  induction h with
  | nil => intro i hi; exact absurd hi (Nat.not_lt_zero _)
  | cons he hs _ ih =>
    intro i hi
    cases i with
    | zero => exact ⟨he, hs⟩
    | succ i => exact ih i (Nat.lt_of_succ_lt_succ hi)

/-- The transfer phases of the by-value composite satisfy WC5.1 C22 item 3 without a registered
entry. -/
theorem encapVals_nil (L : MutexLayout) (c : Nat) : ∀ (t : SC) (vs : List (Nat × Nat)),
    EncapVals L [] c t vs
  | _, [] => trivial
  | _, _ :: vs => ⟨fun _ he => (by cases he), encapVals_nil L c _ vs⟩

/-- Without a registered entry, every `ok` step satisfies `Encap5R`: every requirement of WC5.1
C22 reads the entries of the registry. -/
theorem encap5R_nil {k : K} {L : MutexLayout} {lbl : Label} {s : SC} {ar : ArenaReg}
    {st' : SC × SyncReg × ArenaReg} (h : LStep k L lbl (s, [], ar) st') :
    Encap5R k L (s, [], ar) lbl := by
  have hng : ∀ e ∈ ([] : SyncReg), ¬ e.Live s := fun _ he => by cases he
  refine ⟨⟨?_, chainExcl_of_noLive hng h, ?_⟩,
    placeExcl_of_noLive (fun _ he => by cases he) hng h⟩
  · cases lbl with
    | kernel c op => cases op <;> first | trivial | exact fun _ he => by cases he
    | spawnVal c ps ls vs => exact encapVals_nil L c _ vs
    | deriveSync c g => exact fun _ he => by cases he
    | _ => trivial
  · cases lbl with
    | kernel c op => cases op <;> first | trivial | exact fun _ he => by cases he
    | _ => trivial

/-! ## Lifecycle of the contexts along a step -/

/-- Lifecycle states of the contexts, by identity (WC5.1 C2). -/
def SC.lifes (s : SC) : List Life := s.C.map (·.life)

/-- Change of the lifecycle states by an `ok` step: `spawn` and `spawnVal` append a live context
(`spawnEff`; WC5.1 C4, C5 phase 1), `terminate c` completes `c` (WC5.1 C7 effect); the other steps
keep them. -/
def Label.lifeEff : Label → List Life → List Life
  | .spawn .., ls | .spawnVal .., ls => ls ++ [.live]
  | .terminate c, ls => ls.set c .done
  | _, ls => ls

/-- A context of `C` is live only if it exists (WC5.1 C2). -/
theorem SC.lt_of_live {s : SC} {c : Nat} (h : s.Live c) : c < s.C.length := by
  unfold SC.Live at h
  cases hc : s.C[c]? with
  | none => rw [hc] at h; exact h.elim
  | some x => exact (List.getElem?_eq_some_iff.1 hc).1

/-- An operation run on the view of `c` keeps the contexts (WC5.1 C2). -/
theorem viewStep_C {R : S3 → Outcome3 S3 → Prop} {c : Nat} {s s' : SC}
    (h : ViewStep R c s (.ok s')) : s.Live c ∧ s'.C = s.C := by
  obtain ⟨hl, o₃, -, ho⟩ := h
  cases o₃ with
  | ok t => cases ho; exact ⟨hl, rfl⟩
  | reject => cases ho
  | fail => cases ho

/-- Changing the stacks keeps the lifecycle states. -/
theorem lifes_modify (f : Ctx → Ctx) (hf : ∀ x, (f x).life = x.life) :
    ∀ (C : List Ctx) (c : Nat), (C.modify c f).map (·.life) = C.map (·.life)
  | [], _ => by rw [List.modify_nil]
  | x :: C, 0 => by rw [List.modify_zero_cons, List.map_cons, List.map_cons, hf]
  | x :: C, c + 1 => by
    rw [List.modify_succ_cons, List.map_cons, List.map_cons, lifes_modify f hf C c]

/-- Reparenting keeps the lifecycle states (WC5.1 C6). -/
theorem lifes_reparent (C : List Ctx) (f p : Nat) :
    (reparent C f p).map (·.life) = C.map (·.life) := by
  simp only [reparent, List.map_map]
  congr 1
  funext x
  by_cases h : x.life = .live ∧ x.parent = some f <;> simp [h]

/-- Completing context `c` (WC5.1 C7 effect). -/
theorem lifes_done : ∀ (C : List Ctx) (c : Nat),
    (C.modify c fun x => { x with stack := [], life := .done }).map (·.life) =
      (C.map (·.life)).set c .done
  | [], _ => by rw [List.modify_nil]; rfl
  | x :: C, 0 => by rw [List.modify_zero_cons]; rfl
  | x :: C, c + 1 => by
    rw [List.modify_succ_cons, List.map_cons, List.map_cons, List.set_cons_succ, lifes_done C c]

/-- The by-value transfers keep the contexts. -/
theorem transfersEff_C (c : Nat) : ∀ (t : SC) (vs : List (Nat × Nat)),
    (transfersEff c t vs).C = t.C
  | _, [] => rfl
  | t, v :: vs => (transfersEff_C c (transferEffC t c v.1 v.2) vs).trans rfl

/-- Every `ok` step is executed by a live context (each step relation of `LStep` requires it; WC5.1
C4 item 1 for `spawn`) and changes the lifecycle states by `Label.lifeEff`. -/
theorem lstep_lifes {k : K} {L : MutexLayout} {lbl : Label} {st st' : SC × SyncReg × ArenaReg}
    (h : LStep k L lbl st st') : st.1.Live lbl.ctx ∧ st'.1.lifes = lbl.lifeEff st.1.lifes := by
  have same : ∀ {s s' : SC}, s'.C = s.C → s'.lifes = s.lifes := fun h => by
    unfold SC.lifes; rw [h]
  cases h with
  | @kernel s s' reg ar c op hk =>
    cases op with
    | transfer src dst =>
      obtain ⟨hl, hg⟩ := hk; obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hg; exact ⟨hl, rfl⟩
    | depend q x =>
      obtain ⟨hl, hg⟩ := hk; obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hg; exact ⟨hl, rfl⟩
    | store a p =>
      obtain ⟨hl, hg⟩ := hk; obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hg; exact ⟨hl, rfl⟩
    | enter ps ls =>
      obtain ⟨hl, hg⟩ := hk; obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hg
      exact ⟨hl, lifes_modify (fun x => { x with stack := s.nF :: x.stack }) (fun _ => rfl) _ _⟩
    | exit =>
      obtain ⟨hl, hg⟩ := hk; obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hg
      exact ⟨hl, (lifes_reparent _ _ _).trans
        (lifes_modify (fun x => { x with stack := x.stack.tail }) (fun _ => rfl) _ _)⟩
    | derive => have h := viewStep_C hk; exact ⟨h.1, same h.2⟩
    | split => have h := viewStep_C hk; exact ⟨h.1, same h.2⟩
    | release => have h := viewStep_C hk; exact ⟨h.1, same h.2⟩
    | read => have h := viewStep_C hk; exact ⟨h.1, same h.2⟩
    | write => have h := viewStep_C hk; exact ⟨h.1, same h.2⟩
    | writeShared => have h := viewStep_C hk; exact ⟨h.1, same h.2⟩
    | _ => have h := viewStep_C hk; exact ⟨h.1, same h.2⟩
  | spawn hs =>
    obtain ⟨hl, hg⟩ := hs; obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hg
    exact ⟨hl, List.map_append ..⟩
  | terminate ht =>
    obtain ⟨hl, hg⟩ := ht; obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hg
    exact ⟨hl, (lifes_reparent _ _ _).trans (lifes_done _ _)⟩
  | join hj => cases hj with | ok hl _ => exact ⟨hl, rfl⟩
  | deriveSync hd =>
    obtain ⟨hl, hg⟩ := hd; obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hg; exact ⟨hl, rfl⟩
  | newMutex hn => obtain ⟨hl, -, rfl⟩ := hn; exact ⟨hl, rfl⟩
  | acquire ha => obtain ⟨hl, _, -, -, -, rfl⟩ := ha; exact ⟨hl, rfl⟩
  | unlock hu => obtain ⟨hl, _, _, -, -, -, -, -, rfl⟩ := hu; exact ⟨hl, rfl⟩
  | resetLock hr => obtain ⟨hl, _, -, -, -, -, rfl⟩ := hr; exact ⟨hl, rfl⟩
  | @spawnVal s s' reg ar c ps ls vs hs =>
    obtain ⟨hl, hg⟩ := hs; obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hg
    refine ⟨hl, ?_⟩
    show (transfersEff c (spawnCreate s c ls) vs).C.map _ = _
    rw [transfersEff_C]
    exact List.map_append ..
  | newArena hn =>
    obtain ⟨hl, hg⟩ := hn; obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hg; exact ⟨hl, rfl⟩
  | issue hi =>
    cases hi with
    | ok _ _ _ h1 h2 =>
      have k1 := viewStep_C h1
      obtain ⟨-, hg⟩ := h2; obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hg
      exact ⟨k1.1, same k1.2⟩
  | reset hr =>
    obtain ⟨hl, o₃, -, ho⟩ := hr
    cases o₃ with
    | ok t => cases ho; exact ⟨hl, rfl⟩
    | reject => cases ho
    | fail => cases ho

/-- `Label.lifeEff` never shortens the list. -/
theorem lifeEff_length (lbl : Label) (ls : List Life) : ls.length ≤ (lbl.lifeEff ls).length := by
  cases lbl <;> simp [Label.lifeEff]

/-- Along the `ok` steps of a trace, the number of contexts never decreases (context identities are
the indices of `SC.C`). -/
theorem len_mono {k : K} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label}
    (hs : ∀ i (h : i < lbls.length), LStep k L lbls[i] (σ i) (σ (i + 1))) {a : Nat} :
    ∀ b, a ≤ b → b ≤ lbls.length → (σ a).1.C.length ≤ (σ b).1.C.length
  | 0, hab, _ => by obtain rfl := Nat.le_zero.1 hab; exact Nat.le_refl _
  | b + 1, hab, hb => by
    rcases Nat.lt_or_ge b a with h | h
    · obtain rfl : a = b + 1 := by omega
      exact Nat.le_refl _
    · have h1 := len_mono hs b h (by omega)
      have h2 := lifeEff_length lbls[b] (σ b).1.lifes
      rw [← (lstep_lifes (hs b (by omega))).2] at h2
      simp only [SC.lifes, List.length_map] at h2
      omega

/-! ## Events -/

/-- Event of a trace (WC5.1 C26, C28; brief, "Événements"): `step i`, the event of step `i`, of
context `Label.ctx`; `start i`, the marker `start(c)` of the context created by step `i` when this
step is a `spawn` or a `spawnVal`. -/
inductive Ev where
  | step (i : Nat)
  | start (i : Nat)
deriving DecidableEq

/-- Position of an event (brief, task 1): `start(c)` is placed at its `spawn`, right after it. -/
def Ev.pos : Ev → Nat
  | .step i => 2 * i
  | .start i => 2 * i + 1

/-- The event at a position. -/
def Ev.ofPos (p : Nat) : Ev := if p % 2 = 0 then .step (p / 2) else .start (p / 2)

/-- `Ev.ofPos` inverts `Ev.pos`. -/
theorem Ev.ofPos_pos : ∀ e : Ev, Ev.ofPos e.pos = e
  | .step i => by
    have h : 2 * i % 2 = 0 := by omega
    simp only [Ev.ofPos, Ev.pos, h, ↓reduceIte, Ev.step.injEq]; omega
  | .start i => by
    have h : ¬ (2 * i + 1) % 2 = 0 := by omega
    simp only [Ev.ofPos, Ev.pos, h, ↓reduceIte, Ev.start.injEq]; omega

/-- `Ev.pos` inverts `Ev.ofPos`. -/
theorem Ev.pos_ofPos (p : Nat) : (Ev.ofPos p).pos = p := by
  unfold Ev.ofPos
  split
  · show 2 * (p / 2) = p; omega
  · show 2 * (p / 2) + 1 = p; omega

/-- Step `lbl` creates a context: `spawn` (WC5.1 C4) or `spawnVal` (WC5.1 C5). -/
def Label.creates : Label → Bool
  | .spawn .. | .spawnVal .. => true
  | _ => false

/-- The context terminated by `lbl` (WC5.1 C7). -/
def Label.termOf : Label → Option Nat
  | .terminate c => some c
  | _ => none

/-- The context joined by `lbl` (WC5.1 C8). -/
def Label.joinOf : Label → Option Nat
  | .join _ d => some d
  | _ => none

/-- The entry unlocked by `lbl` (WC5.1 C17). -/
def Label.unlockOf : Label → Option Nat
  | .unlock _ i => some i
  | _ => none

/-- The entry acquired by `lbl` (WC5.1 C16). -/
def Label.acquireOf : Label → Option Nat
  | .acquire _ i => some i
  | _ => none

/-- Identity of the context created by step `i`, a `spawn` or a `spawnVal`: the fresh identity of
WC5.1 C4 item 2, `|C|` in the state where the step is taken (`spawnEff`; `spawnCreate` for the
create phase of WC5.1 C5). -/
def created (σ : Nat → SC × SyncReg × ArenaReg) (i : Nat) : Nat := (σ i).1.C.length

/-- `po` (WC5.1 C28; brief, "po"): between two steps of the same context, in trace order;
`start(c)` precedes every step of `c`. The clause `i < j` of the second case holds on every trace
(`po_start_iff`). -/
def PO (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) : Ev → Ev → Prop
  | .step i, .step j =>
    i < j ∧ j < lbls.length ∧ (lbls[i]?).map Label.ctx = (lbls[j]?).map Label.ctx
  | .start i, .step j =>
    i < j ∧ j < lbls.length ∧ (lbls[i]?).map Label.creates = some true ∧
      (lbls[j]?).map Label.ctx = some (created σ i)
  | _, _ => False

/-- Decidability of `PO`. -/
instance (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) (e e' : Ev) :
    Decidable (PO σ lbls e e') := by
  unfold PO; split <;> infer_instance

/-- `sw` (WC5.1 C32 items 2 and 3, C47, C48; brief, "sw"): from the step `spawn` or `spawnVal`
creating `c` to `start(c)`; from `terminate(c)` to every `join` of `c` after it; from `unlock(e)`
to the first `acquire(e)` after it. -/
def SW (lbls : List Label) : Ev → Ev → Prop
  | .step i, .start j => i = j ∧ (lbls[i]?).map Label.creates = some true
  | .step i, .step j =>
    i < j ∧ j < lbls.length ∧
      (OptP ((lbls[i]?).bind Label.termOf) (fun d => (lbls[j]?).bind Label.joinOf = some d) False ∨
       OptP ((lbls[i]?).bind Label.unlockOf) (fun e => (lbls[j]?).bind Label.acquireOf = some e ∧
         ∀ p ∈ List.range j, i < p → (lbls[p]?).bind Label.acquireOf ≠ some e) False)
  | _, _ => False

/-- Decidability of `SW`. -/
instance (lbls : List Label) (e e' : Ev) : Decidable (SW lbls e e') := by
  unfold SW; split <;> infer_instance

/-- An edge of `po ∪ sw`. -/
def Edge (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) (e e' : Ev) : Prop :=
  PO σ lbls e e' ∨ SW lbls e e'

/-- Decidability of `Edge`. -/
instance (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) (e e' : Ev) :
    Decidable (Edge σ lbls e e') := by
  unfold Edge; infer_instance

/-- `hb` (WC5.1 C33; brief, "hb"): the transitive closure of `po ∪ sw`. -/
def HB (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) : Ev → Ev → Prop :=
  Relation.TransGen (Edge σ lbls)

/-- A step of `lbls` exists. -/
theorem lt_of_map_some {α : Type} {lbls : List Label} {i : Nat} {f : Label → α} {a : α}
    (h : (lbls[i]?).map f = some a) : i < lbls.length := by
  cases hi : lbls[i]? with
  | none => rw [hi] at h; cases h
  | some x => exact (List.getElem?_eq_some_iff.1 hi).1

/-- Every edge of `po ∪ sw` goes to a later position of the trace. -/
theorem edge_pos {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} {e e' : Ev}
    (h : Edge σ lbls e e') : e.pos < e'.pos ∧ e'.pos < 2 * lbls.length := by
  rcases h with h | h
  · cases e <;> cases e' <;> simp only [PO] at h
    · obtain ⟨h1, h2, -⟩ := h; exact ⟨by simp only [Ev.pos]; omega, by simp only [Ev.pos]; omega⟩
    · obtain ⟨h1, h2, -⟩ := h; exact ⟨by simp only [Ev.pos]; omega, by simp only [Ev.pos]; omega⟩
  · cases e <;> cases e' <;> simp only [SW] at h
    · obtain ⟨h1, h2, -⟩ := h; exact ⟨by simp only [Ev.pos]; omega, by simp only [Ev.pos]; omega⟩
    · obtain ⟨rfl, h2⟩ := h
      have := lt_of_map_some h2
      exact ⟨by simp only [Ev.pos]; omega, by simp only [Ev.pos]; omega⟩

/-- Brief, task 1: `hb` only relates events in increasing position. -/
theorem hb_pos {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} {e e' : Ev}
    (h : HB σ lbls e e') : e.pos < e'.pos := by
  induction h with
  | single h => exact (edge_pos h).1
  | tail _ h ih => exact Nat.lt_trans ih (edge_pos h).1

/-- Brief, task 1: `hb` is irreflexive (WC5.1 C33: acyclicity). -/
theorem hb_irrefl {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} (e : Ev) :
    ¬ HB σ lbls e e :=
  fun h => Nat.lt_irrefl _ (hb_pos h)

/-! ## Decision of `hb` -/

/-- Reachability from `src` along `R` of the positions below `n`, computed in one pass by
increasing position. -/
def reachList (R : Ev → Ev → Prop) [DecidableRel R] (src : Ev) : Nat → List Bool
  | 0 => []
  | n + 1 =>
    let v := reachList R src n
    v ++ [decide (R src (Ev.ofPos n)) ||
      (List.range n).any fun r => (v[r]?).getD false && decide (R (Ev.ofPos r) (Ev.ofPos n))]

/-- `reachList R src n` has `n` entries. -/
theorem reachList_length (R : Ev → Ev → Prop) [DecidableRel R] (src : Ev) :
    ∀ n, (reachList R src n).length = n
  | 0 => rfl
  | n + 1 => by simp [reachList, reachList_length R src n]

/-- When `R` increases positions, `reachList` computes the transitive closure of `R`. -/
theorem reachList_spec (R : Ev → Ev → Prop) [DecidableRel R] (src : Ev)
    (hmono : ∀ e e', R e e' → e.pos < e'.pos) :
    ∀ n q, q < n → (((reachList R src n)[q]?).getD false = true ↔
      Relation.TransGen R src (Ev.ofPos q))
  | 0, _, hq => absurd hq (Nat.not_lt_zero _)
  | n + 1, q, hq => by
    have ih := reachList_spec R src hmono n
    have hlen := reachList_length R src n
    simp only [reachList]
    rcases Nat.lt_or_ge q n with h | h
    · rw [List.getElem?_append_left (by rw [hlen]; exact h)]
      exact ih q h
    · obtain rfl : q = n := by omega
      rw [List.getElem?_append_right (Nat.le_of_eq hlen), hlen, Nat.sub_self]
      simp only [List.getElem?_cons_zero, Option.getD_some, Bool.or_eq_true, decide_eq_true_eq,
        List.any_eq_true, List.mem_range, Bool.and_eq_true]
      constructor
      · rintro (h1 | ⟨r, hr, h2, h3⟩)
        · exact .single h1
        · exact .tail ((ih r hr).1 h2) h3
      · intro ht
        cases ht with
        | single h1 => exact Or.inl h1
        | @tail y _ hy h3 =>
          have hp := hmono _ _ h3
          rw [Ev.pos_ofPos] at hp
          refine Or.inr ⟨y.pos, hp, (ih y.pos hp).2 (by rw [Ev.ofPos_pos]; exact hy), ?_⟩
          rw [Ev.ofPos_pos]; exact h3

/-- `hb` as computed by `reachList`. -/
theorem hb_iff_reach {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} {e e' : Ev} :
    HB σ lbls e e' ↔ ((reachList (Edge σ lbls) e (e'.pos + 1))[e'.pos]?).getD false = true := by
  rw [reachList_spec _ _ (fun _ _ h => (edge_pos h).1) _ _ (Nat.lt_succ_self _), Ev.ofPos_pos]
  rfl

/-- Decidability of `hb` on a finite trace (brief, "hb"). -/
instance (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) (e e' : Ev) :
    Decidable (HB σ lbls e e') :=
  decidable_of_iff _ hb_iff_reach.symm

/-! ## Exclusive pairs, races, loss step, `HandoffOrdered` -/

/-- Exclusive pair `(i, j, l)` (brief, "Paire exclusive"; WC5.1 C44): `i < j`, distinct contexts,
both steps access the leaf `l` (`Label.Access`), at least one of them requiring `Modify`. -/
def ExclPair (lbls : List Label) (i j l : Nat) : Prop :=
  ∃ (hij : i < j) (hj : j < lbls.length) (c c' : Nat) (m m' : Mode), c ≠ c' ∧
    (lbls[i]'(Nat.lt_trans hij hj)).Access c' l m ∧ lbls[j].Access c l m' ∧
    (m = .modify ∨ m' = .modify)

/-- `Race` (brief, "Race"; WC5.1 C33 restricted to the accesses `read3`, `write3`, `writeShared`
and to the pairs with a member requiring `Modify`, C44): an exclusive pair without `hb`. -/
def Race (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) : Prop :=
  ∃ i j l, ExclPair lbls i j l ∧ ¬ HB σ lbls (.step i) (.step j)

/-- Mode required by an access step, as in `Label.Access` (Spec 1 §66.2, §67.1, §68.2). -/
def Label.accMode : Label → Option Mode
  | .kernel _ (.read _ _) => some .observe
  | .kernel _ (.write _ _) => some .modify
  | .kernel _ (.writeShared _ _) => some .observe
  | _ => none

/-- A capability `o` is compatible with the mode `m` of a later access of another context (brief,
"Pas de perte"; WC5.1 C45): `none` if `m` is `Modify`, other than `Modify` if `m` is `Observe`. -/
def CapCompat : Option Mode → Mode → Bool
  | none, _ => true
  | some .observe, .observe => true
  | _, _ => false

/-- Loss step `r(i, j, l)` (brief, "Pas de perte"; WC5.1 C45): the first step `k > i` of the trace
at the issue of which `cap5` of the context of step `i` on `l` is compatible with the mode of step
`j`; `none` if there is none. -/
def lossStep (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) (i j l : Nat) :
    Option Nat :=
  match (lbls[i]?).map Label.ctx, (lbls[j]?).bind Label.accMode with
  | some c', some m' => (List.range lbls.length).find? fun k =>
      decide (i < k) && CapCompat (cap5 (σ (k + 1)).1 (σ (k + 1)).2.1 c' l) m'
  | _, _ => none

/-- `HandoffOrdered` for one pair (brief, "HandoffOrdered"; WC5.1 C46): the loss step exists and is
`hb`-before step `j`. A missing marker is a failure, not a vacuous success (WC5.1 C46). -/
def HandoffOrderedAt (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) (i j l : Nat) :
    Prop :=
  ∃ r, lossStep σ lbls i j l = some r ∧ HB σ lbls (.step r) (.step j)

/-- `HandoffOrderedAt` as an `OptP` on the loss step. -/
theorem handoffOrderedAt_iff {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label}
    {i j l : Nat} : HandoffOrderedAt σ lbls i j l ↔
      OptP (lossStep σ lbls i j l) (fun r => HB σ lbls (.step r) (.step j)) False := by
  unfold HandoffOrderedAt
  cases lossStep σ lbls i j l with
  | none => simp [OptP]
  | some r => simp [OptP]

/-- Decidability of `HandoffOrderedAt`. -/
instance (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) (i j l : Nat) :
    Decidable (HandoffOrderedAt σ lbls i j l) :=
  decidable_of_iff _ handoffOrderedAt_iff.symm

/-- `HandoffOrdered` (brief, "HandoffOrdered"; WC5.1 C46): every exclusive pair satisfies
`HandoffOrderedAt`. -/
def HandoffOrdered (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) : Prop :=
  ∀ i j l, ExclPair lbls i j l → HandoffOrderedAt σ lbls i j l

/-! ## `po` from `start(c)` on a trace -/

/-- On the `ok` steps of a trace, every step of the context created by step `i` comes after step
`i`: the created context has the fresh identity `|C|` (WC5.1 C4 item 2, `spawnEff`), only a live
context steps (`lstep_lifes`), and `C` never shrinks (`len_mono`). -/
theorem step_after_create {k : K} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg}
    {lbls : List Label} (hs : ∀ i (h : i < lbls.length), LStep k L lbls[i] (σ i) (σ (i + 1)))
    {i j : Nat} (hi : (lbls[i]?).map Label.creates = some true) (hj : j < lbls.length)
    (hc : (lbls[j]?).map Label.ctx = some (created σ i)) : i < j := by
  have hil := lt_of_map_some hi
  refine Nat.lt_of_not_le fun hji => ?_
  rw [List.getElem?_eq_getElem hj, Option.map_some] at hc
  have hlive := (lstep_lifes (hs j hj)).1
  rw [Option.some.inj hc] at hlive
  have h1 := SC.lt_of_live hlive
  have h2 := len_mono hs i hji (Nat.le_of_lt hil)
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h1 h2)

/-- On the `ok` steps of a trace, `po` from `start(c)` is the clause of the brief, "`start(c)`
précède tous les pas de `c`", without the order clause. -/
theorem po_start_iff {k : K} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg}
    {lbls : List Label} (hs : ∀ i (h : i < lbls.length), LStep k L lbls[i] (σ i) (σ (i + 1)))
    {i j : Nat} : PO σ lbls (.start i) (.step j) ↔ j < lbls.length ∧
      (lbls[i]?).map Label.creates = some true ∧ (lbls[j]?).map Label.ctx = some (created σ i) :=
  ⟨fun ⟨_, h2, h3, h4⟩ => ⟨h2, h3, h4⟩,
   fun ⟨h2, h3, h4⟩ => ⟨step_after_create hs h3 h2 h4, h2, h3, h4⟩⟩

end Ern.Concurrency
