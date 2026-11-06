/-!
# Access kernel: state and derived notions

Abstract authority machine of `specs/ERN_Memory_Model_Specification_v0.1.md`, Parts IV–VII:
frames (§39), places, leaves and footprints (§40), initialization states (§41), authorities
(§42), dynamic pinning obligations (§74, §75), the state `S3` (§38), the external contract `K`
(§48, §80), and the derived notions that the operations of §60–§75 read: usability (§40),
effective modes, exercisability and the grounding of a right (§43; §63.4, §69.2, §70.3),
effective anchors and anchor order (§44), outcomes (§58).

Identities of places and authorities are list indices; index order represents acyclicity of
parent and origin links (§49, last paragraph). Reading decisions are recorded in the reference
pass readings, never in this file.
-/

namespace Ern.MemoryModel.Access

/-! ## Frames (§39) -/

/-- Frame stack `F` (§39): frame identities, current frame first; the parent of a frame is the
next element. -/
abbrev Frames := List Nat

/-- `ancestor(f₁, f₂)` (§39): `f₁` is `f₂` or one of its ancestors in the stack. -/
def ancestor (F : Frames) (f₁ f₂ : Nat) : Prop := f₁ ∈ F.dropWhile (· != f₂)

/-- Decidability of `ancestor` (§39). -/
instance (F : Frames) (f₁ f₂ : Nat) : Decidable (ancestor F f₁ f₂) :=
  inferInstanceAs (Decidable (_ ∈ _))

/-! ## Parent chains (§40, §42) -/

/-- Strict ancestors of `i` along the link `org`, nearest first, within fuel `k` (§40 structural
parents, §42 origins). Only links to a smaller index are followed (§49, last paragraph). -/
def chainF (org : Nat → Option Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, i =>
    match org i with
    | some o => if o < i then o :: chainF org k o else []
    | none => []

/-- Strict ancestors of `i` along `org` (§40, §42); fuel `i` suffices since the chain
decreases. -/
def chain (org : Nat → Option Nat) (i : Nat) : List Nat := chainF org i i

/-! ## Places, leaves, footprints (§40) -/

/-- Holder of an authority (§42) or owner of a place (§40): a frame or a place. -/
inductive Holder where
  | frame (f : Nat)
  | place (p : Nat)
deriving DecidableEq, Repr

/-- Logical place (§40): optional structural parent, owner, abstract `kind`. Its identity is its
index in `P`; its death marker is `S3.dead`. -/
structure Place where
  parent : Option Nat
  owner : Holder
  kind : Nat
deriving DecidableEq, Repr

/-- Structural parent of place `i` (§40). -/
def parentOf (P : List Place) (i : Nat) : Option Nat := (P[i]?).bind (·.parent)

/-- `partOf(p, q)` (§40): `p` is a place of `P` and `q` is `p` or one of its structural
ancestors. -/
def partOf (P : List Place) (p q : Nat) : Prop :=
  p < P.length ∧ (p = q ∨ q ∈ chain (parentOf P) p)

/-- Decidability of `partOf` (§40). -/
instance (P : List Place) (p q : Nat) : Decidable (partOf P p q) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Leaf (§40): a place with no structural child. -/
def isLeaf (P : List Place) (l : Nat) : Prop := ∀ r < P.length, parentOf P r ≠ some l

/-- Decidability of `isLeaf` (§40). -/
instance (P : List Place) (l : Nat) : Decidable (isLeaf P l) :=
  inferInstanceAs (Decidable (∀ _, _))

/-- `footprint(q)` (§40): the leaves of `P` that are parts of `q`. -/
def footprint (P : List Place) (q : Nat) : List Nat :=
  (List.range P.length).filter fun l => decide (isLeaf P l ∧ partOf P l q)

/-- Two places overlap when their footprints share a leaf (§63.3). -/
def overlap (P : List Place) (p q : Nat) : Prop := ∃ l ∈ footprint P p, l ∈ footprint P q

/-- Decidability of `overlap` (§63.3). -/
instance (P : List Place) (p q : Nat) : Decidable (overlap P p q) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- `OwnedIn P src q` (§40, §33): the ownership chain of `q` reaches a place owned by `src` or by
one of its parts, that is, `q` is storage owned, directly or transitively, by the value at
`src`. -/
inductive OwnedIn (P : List Place) (src : Nat) : Nat → Prop where
  | direct {q o : Nat} {pl : Place} : P[q]? = some pl → pl.owner = .place o → partOf P o src →
      OwnedIn P src q
  | step {q o : Nat} {pl : Place} : P[q]? = some pl → pl.owner = .place o → OwnedIn P src o →
      OwnedIn P src q

/-! ## State (§38, §41, §42) -/

/-- Initialization state of a leaf (§41). -/
inductive InitSt where
  | uninit
  | init
  | moved
deriving DecidableEq, Repr

/-- Mode of an authority or of a request (§42, §43). -/
inductive Mode where
  | observe
  | modify
deriving DecidableEq, Repr

/-- Order of requested modes, `Observe ≤ Modify` (§43). -/
def Mode.le (m m' : Mode) : Prop := m = .observe ∨ m' = .modify

/-- Decidability of the mode order (§43). -/
instance (m m' : Mode) : Decidable (m.le m') := inferInstanceAs (Decidable (_ ∨ _))

/-- Authority (§42): own mode, optional origin, footprint (a list of leaves read
extensionally), holder, activity. Its identity is its index in `A`. -/
structure Authority where
  mode : Mode
  origin : Option Nat
  footprint : List Nat
  holder : Holder
  active : Bool
deriving DecidableEq, Repr

/-- Dynamic pinning obligation (§74, §75): the place `pin` was applied to, the leaves it pins, and
whether it is still active. Its identity is its index in `S3.pins`. -/
structure PinOb where
  place : Nat
  leaves : List Nat
  active : Bool
deriving DecidableEq, Repr

/-- State `S3` (§38). `F`, `P`, `I`, `A`, `D` are the components of §38. `nF` (next fresh frame
identity, §39), `dead` (death marker of places, §40) and `pins` (dynamic pinning obligations,
§74, §75) are auxiliary information that creates no right (§38). -/
structure S3 where
  F : Frames
  nF : Nat
  P : List Place
  I : Nat → InitSt
  A : List Authority
  D : Nat → List Nat
  dead : Nat → Bool
  pins : List PinOb

/-- Leaf `l` is dynamically pinned (§74): an active pinning obligation covers it. -/
def S3.pin (s : S3) (l : Nat) : Bool := s.pins.any fun o => o.active && o.leaves.contains l

/-- Shape of the locals of `enterFrame` (§72) and of an allocation (§71.1): each element is an
optional structural parent (a place index) and a `kind`. Every element is owned by the holder
receiving the shape. -/
abbrev LocalShape := List (Option Nat × Nat)

/-- External contract `K` (§48, §80): `DeclaredDisjoint` on regions (§23, §61.3);
`SharedMutable` and `Pinned` on leaves (§68.1, §63.5); `ExternalDone` on dynamic pinning
obligations, by identity (§75); `Deallocable` on places (§70.2); `FreeCompat place auth` (§70.2);
`Satisfiable provider shape s` (§71). Obligations of `K` are hypotheses of theorems, never
fields. -/
structure K where
  DeclaredDisjoint : List Nat → List Nat → Prop
  SharedMutable : Nat → Prop
  Pinned : Nat → Prop
  ExternalDone : Nat → Prop
  Deallocable : Nat → Prop
  FreeCompat : Nat → Nat → Prop
  Satisfiable : Nat → LocalShape → S3 → Prop

/-- `DDSound(K)` (§80, §23): no declared disjointness relates two regions sharing a leaf. -/
def DDSound (k : K) : Prop := ∀ r r', k.DeclaredDisjoint r r' → ∀ l ∈ r, l ∉ r'

/-- `origin` link of authority `i` (§42). -/
def S3.org (s : S3) (i : Nat) : Option Nat := (s.A[i]?).bind (·.origin)

/-- Strict ancestors of authority `i` along its origin chain (§42, §43). -/
def S3.ancs (s : S3) (i : Nat) : List Nat := chain s.org i

/-- Effective anchor of `x` (§44): the root reached along its origin chain, the last element of
`x :: s.ancs x`. -/
def S3.effAnchor (s : S3) (x : Nat) : Nat := (s.ancs x).getLastD x

/-- Active authority (§42); as an anchor, a valid anchor (§44). -/
def S3.Active (s : S3) (x : Nat) : Prop := ∃ y, s.A[x]? = some y ∧ y.active = true

/-- Decidability of `S3.Active` (§42, §44). -/
instance (s : S3) (x : Nat) : Decidable (s.Active x) :=
  match h : s.A[x]? with
  | some y => if hy : y.active = true then isTrue ⟨y, h, hy⟩
    else isFalse fun ⟨y', h', hy'⟩ => by rw [h] at h'; cases h'; exact hy hy'
  | none => isFalse fun ⟨_, h', _⟩ => by rw [h] at h'; cases h'

/-- Current frame, the top of the stack (§39). -/
def S3.top (s : S3) : Nat := s.F.headD 0

/-! ## Decidable helpers -/

/-- Predicate on an optional value, `P y` for `some y` and `d` for `none`; used to read the
components of `S3` (§38). -/
def OptP {α : Type} (o : Option α) (P : α → Prop) (d : Prop) : Prop :=
  match o with
  | some y => P y
  | none => d

/-- Decidability of `OptP` (§38). -/
instance {α : Type} (o : Option α) (P : α → Prop) (d : Prop) [DecidablePred P] [Decidable d] :
    Decidable (OptP o P d) :=
  match o with
  | some y => inferInstanceAs (Decidable (P y))
  | none => inferInstanceAs (Decidable d)

/-- An index with a value is in range (§38: identities are list indices). -/
theorem lt_of_getElem? {α : Type} {l : List α} {i : Nat} {x : α} (h : l[i]? = some x) :
    i < l.length := (List.getElem?_eq_some_iff.1 h).1

/-! ## Least fixed points on a bounded universe

`Usable` (§40), `FrameOf` (§40), `OwnedIn` (§40) and `ExercisableAt` (§43) are inductive
predicates, each the least fixed point of a monotone rule over identities below a bound `n`; the
Kleene iteration is stable after `n + 1` steps, which makes them decidable. -/

/-- `k`-th Kleene iterate of a rule `R` on Boolean predicates over `Nat` (decision procedure for
§40 and §43). -/
def kiter (R : (Nat → Bool) → Nat → Bool) : Nat → Nat → Bool
  | 0, _ => false
  | k + 1, a => R (kiter R k) a

/-- A monotone rule whose conclusions lie below `n` and which reads its premise only below `n`
(decision procedure for §40 and §43). -/
structure KRule (n : Nat) (R : (Nat → Bool) → Nat → Bool) : Prop where
  mono : ∀ p q : Nat → Bool, (∀ a, p a = true → q a = true) → ∀ a, R p a = true → R q a = true
  bound : ∀ p a, R p a = true → a < n
  loc : ∀ p q : Nat → Bool, (∀ a, a < n → p a = q a) → ∀ a, R p a = R q a

/-- The iteration of a monotone rule is increasing (decision procedure for §40 and §43). -/
theorem kiter_mono {n : Nat} {R : (Nat → Bool) → Nat → Bool} (h : KRule n R) :
    ∀ k a, kiter R k a = true → kiter R (k + 1) a = true
  | 0, _, hk => by simp [kiter] at hk
  | k + 1, a, hk => h.mono _ _ (kiter_mono h k) a hk

/-- Conclusions of the iteration lie below the bound (decision procedure for §40 and §43). -/
theorem kiter_bound {n : Nat} {R : (Nat → Bool) → Nat → Bool} (h : KRule n R) :
    ∀ k a, kiter R k a = true → a < n
  | 0, _, hk => by simp [kiter] at hk
  | _ + 1, a, hk => h.bound _ a hk

/-- `countP` is monotone in the predicate (decision procedure for §40 and §43). -/
theorem countP_le_of {l : List Nat} {p q : Nat → Bool} (hpq : ∀ a ∈ l, p a = true → q a = true) :
    l.countP p ≤ l.countP q := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.countP_cons]
    have := ih fun b hb => hpq b (List.mem_cons_of_mem _ hb)
    cases hp : p a <;> cases hq : q a <;> simp_all <;> omega

/-- `countP` grows strictly when one more element satisfies the predicate (decision procedure
for §40 and §43). -/
theorem countP_lt_of {l : List Nat} {p q : Nat → Bool} (hpq : ∀ a ∈ l, p a = true → q a = true)
    {x : Nat} (hx : x ∈ l) (hqx : q x = true) (hpx : p x = false) : l.countP p < l.countP q := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    simp only [List.countP_cons]
    have hle := countP_le_of (l := l) fun b hb => hpq b (List.mem_cons_of_mem _ hb)
    rcases List.mem_cons.1 hx with rfl | hx
    · simp [hqx, hpx]; omega
    · have := ih (fun b hb => hpq b (List.mem_cons_of_mem _ hb)) hx
      cases hp : p a <;> cases hq : q a <;> simp_all <;> omega

/-- A failed `all` has a witness (decision procedure for §40 and §43). -/
theorem all_false_exists {α : Type} {p : α → Bool} : ∀ {l : List α}, l.all p = false →
    ∃ a ∈ l, p a = false
  | [], h => by simp at h
  | a :: l, h => by
    simp only [List.all_cons, Bool.and_eq_false_iff] at h
    rcases h with h | h
    · exact ⟨a, List.mem_cons_self .., h⟩
    · obtain ⟨b, hb, hb'⟩ := all_false_exists h; exact ⟨b, List.mem_cons_of_mem _ hb, hb'⟩

/-- Stability of the iteration at step `k`, below `n` (decision procedure for §40 and §43). -/
def kstab (R : (Nat → Bool) → Nat → Bool) (n k : Nat) : Bool :=
  (List.range n).all fun a => kiter R (k + 1) a == kiter R k a

/-- A stable iteration stays stable one step later (decision procedure for §40 and §43). -/
theorem kstab_succ {n : Nat} {R : (Nat → Bool) → Nat → Bool} (h : KRule n R) {k : Nat}
    (hs : kstab R n k = true) : kstab R n (k + 1) = true := by
  simp only [kstab, List.all_eq_true, List.mem_range, beq_iff_eq] at hs ⊢
  intro a ha
  show R (kiter R (k + 1)) a = R (kiter R k) a
  exact h.loc _ _ (fun b hb => hs b hb) a

/-- A stable iteration stays stable (decision procedure for §40 and §43). -/
theorem kstab_le {n : Nat} {R : (Nat → Bool) → Nat → Bool} (h : KRule n R) {k : Nat}
    (hs : kstab R n k = true) : ∀ j, k ≤ j → kstab R n j = true
  | j, hj => by
    induction j with
    | zero => obtain rfl : k = 0 := by omega
              exact hs
    | succ j ih =>
      rcases Nat.lt_or_ge k (j + 1) with hlt | hge
      · exact kstab_succ h (ih (by omega))
      · obtain rfl : k = j + 1 := by omega
        exact hs

/-- Before stabilizing, each step adds a conclusion (decision procedure for §40 and §43). -/
theorem kstab_exists {n : Nat} {R : (Nat → Bool) → Nat → Bool} (h : KRule n R) :
    ∀ k, (∃ j, j < k ∧ kstab R n j = true) ∨ k ≤ (List.range n).countP (kiter R k)
  | 0 => .inr (Nat.zero_le _)
  | k + 1 => by
    rcases kstab_exists h k with hj | hc
    · obtain ⟨j, hj, hs⟩ := hj; exact .inl ⟨j, by omega, hs⟩
    · cases hs : kstab R n k
      · obtain ⟨a, ha, hne⟩ := all_false_exists hs
        simp only [List.mem_range, beq_eq_false_iff_ne] at ha hne
        have hk : kiter R k a = false := by
          cases e : kiter R k a
          · rfl
          · exact absurd (kiter_mono h k a e) (by rw [e] at hne; simpa using hne)
        have hk1 : kiter R (k + 1) a = true := by
          cases e : kiter R (k + 1) a
          · rw [e, hk] at hne; exact absurd rfl hne
          · rfl
        have := countP_lt_of (l := List.range n) (fun b _ hb => kiter_mono h k b hb)
          (List.mem_range.2 ha) hk1 hk
        exact .inr (by omega)
      · exact .inl ⟨k, by omega, hs⟩

/-- The iteration is stable from step `n + 1` on (decision procedure for §40 and §43). -/
theorem kiter_fix {n : Nat} {R : (Nat → Bool) → Nat → Bool} (h : KRule n R) (a : Nat) :
    kiter R (n + 2) a = kiter R (n + 1) a := by
  rcases kstab_exists h (n + 1) with ⟨j, hj, hs⟩ | hc
  · have hs' := kstab_le h hs (n + 1) (by omega)
    by_cases ha : a < n
    · simp only [kstab, List.all_eq_true, List.mem_range, beq_iff_eq] at hs'
      exact hs' a ha
    · cases e : kiter R (n + 2) a
      · cases e' : kiter R (n + 1) a
        · rfl
        · exact absurd (kiter_bound h _ a e') ha
      · exact absurd (kiter_bound h _ a e) ha
  · have := List.countP_le_length (p := kiter R (n + 1)) (l := List.range n)
    simp at this; omega

/-- Monotonicity of the iteration over several steps (decision procedure for §40 and §43). -/
theorem kiter_mono_le {n : Nat} {R : (Nat → Bool) → Nat → Bool} (h : KRule n R) :
    ∀ j k a, kiter R k a = true → kiter R (k + j) a = true
  | 0, _, _, hk => hk
  | j + 1, k, a, hk => kiter_mono h _ a (kiter_mono_le h j k a hk)

/-- The iteration is constant after step `n + 1` (decision procedure for §40 and §43). -/
theorem kiter_ge {n : Nat} {R : (Nat → Bool) → Nat → Bool} (h : KRule n R) :
    ∀ j, kiter R (n + 1 + j) = kiter R (n + 1)
  | 0 => rfl
  | j + 1 => funext fun a => by
    show R (kiter R (n + 1 + j)) a = kiter R (n + 1) a
    rw [kiter_ge h j]; exact kiter_fix h a

/-- A conclusion reached at some step is reached at step `n + 1` (decision procedure for §40 and
§43). -/
theorem kiter_up {n : Nat} {R : (Nat → Bool) → Nat → Bool} (h : KRule n R) :
    ∀ k a, kiter R k a = true → kiter R (n + 1) a = true := by
  intro k a hk
  by_cases hkn : k ≤ n + 1
  · have := kiter_mono_le h (n + 1 - k) k a hk
    rwa [show k + (n + 1 - k) = n + 1 by omega] at this
  · obtain ⟨j, rfl⟩ : ∃ j, k = n + 1 + j := ⟨k - (n + 1), by omega⟩
    rwa [kiter_ge h j] at hk

/-! ## Usable places (§40) -/

/-- `Usable(s, p)` (§40, items 1–3): `p` exists, is not marked dead, and its owner is a frame of
the stack or a usable place. Inductive, so an ownership cycle makes no place usable (§40). -/
inductive S3.Usable (s : S3) : Nat → Prop where
  | frame {q f : Nat} {pl : Place} : s.P[q]? = some pl → s.dead q = false →
      pl.owner = .frame f → f ∈ s.F → S3.Usable s q
  | place {q o : Nat} {pl : Place} : s.P[q]? = some pl → s.dead q = false →
      pl.owner = .place o → S3.Usable s o → S3.Usable s q

/-- A usable place exists (§40, item 1). -/
theorem S3.Usable.lt {s : S3} {q : Nat} (h : s.Usable q) : q < s.P.length := by
  cases h <;> exact lt_of_getElem? ‹_›

/-- One step of `Usable` read on a Boolean premise (decision procedure for §40). -/
def usableR (s : S3) (U : Nat → Bool) (q : Nat) : Bool :=
  match s.P[q]? with
  | some pl => !s.dead q && match pl.owner with
    | .frame f => decide (f ∈ s.F)
    | .place o => decide (o < s.P.length) && U o
  | none => false

/-- The place case of `usableR` (decision procedure for §40). -/
theorem usableR_place {s : S3} {U : Nat → Bool} {q o : Nat} {pl : Place} (hpl : s.P[q]? = some pl)
    (hd : s.dead q = false) (ho : pl.owner = .place o) (hlt : o < s.P.length) (hU : U o = true) :
    usableR s U q = true := by
  simp [usableR, hpl, hd, ho, hlt, hU]

/-- `usableR` is a bounded monotone rule (decision procedure for §40). -/
theorem usableR_rule (s : S3) : KRule s.P.length (usableR s) where
  mono p q hpq a h := by
    unfold usableR at h ⊢; split at h
    · split at h <;> simp_all
    · exact h
  bound p a h := by
    unfold usableR at h; split at h
    · exact lt_of_getElem? ‹_›
    · cases h
  loc p q hpq a := by
    unfold usableR; split
    · split
      · rfl
      · rename_i o _; by_cases ho : o < s.P.length <;> simp [ho, hpq o]
    · rfl

/-- Soundness of the iteration for `Usable` (decision procedure for §40). -/
theorem usable_of_kiter (s : S3) : ∀ k q, kiter (usableR s) k q = true → s.Usable q
  | 0, _, h => by simp [kiter] at h
  | k + 1, q, h => by
    simp only [kiter, usableR] at h
    split at h
    · rename_i pl hpl
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
      obtain ⟨hd, h⟩ := h
      split at h
      · exact .frame hpl hd ‹_› (by simpa using h)
      · simp only [Bool.and_eq_true] at h
        exact .place hpl hd ‹_› (usable_of_kiter s k _ h.2)
    · cases h

/-- `Usable` is computed by `|P| + 1` steps of `usableR` (decision procedure for §40). -/
theorem usable_iff {s : S3} {q : Nat} :
    s.Usable q ↔ kiter (usableR s) (s.P.length + 1) q = true := by
  refine ⟨fun h => ?_, usable_of_kiter s _ q⟩
  induction h with
  | frame hpl hd ho hf =>
    show usableR s _ _ = true
    simp [usableR, hpl, hd, ho, hf]
  | place hpl hd ho hu ih =>
    rw [← kiter_fix (usableR_rule s)]
    show usableR s _ _ = true
    exact usableR_place hpl hd ho hu.lt ih

/-- Decidability of `Usable` (§40). -/
instance (s : S3) (q : Nat) : Decidable (s.Usable q) := decidable_of_iff _ usable_iff.symm

/-- Live holder (§49.8): a frame of the stack or a usable place. -/
def HolderLive (s : S3) : Holder → Prop
  | .frame f => f ∈ s.F
  | .place p => s.Usable p

/-- Decidability of `HolderLive` (§49.8). -/
instance (s : S3) (h : Holder) : Decidable (HolderLive s h) := by
  cases h <;> unfold HolderLive <;> infer_instance

/-! ## Frame of a place (§40, §44) -/

/-- Frame ending the ownership chain of `q`, searched within `k` steps (`placeFrame`, §40). -/
def pframeF (s : S3) : Nat → Nat → Option Nat
  | 0, _ => none
  | k + 1, q =>
    match s.P[q]? with
    | some pl =>
      match pl.owner with
      | .frame f => some f
      | .place o => pframeF s k o
    | none => none

/-- `placeFrame(q)` (§40): the frame ending the ownership chain of `q`, within `|P| + 1`
steps. -/
def S3.pframe (s : S3) (q : Nat) : Option Nat := pframeF s (s.P.length + 1) q

/-- Frame of a holder (§44): the frame itself, or the frame of the holding place. -/
def S3.hframe (s : S3) : Holder → Option Nat
  | .frame f => some f
  | .place p => s.pframe p

/-- `FrameOf s q f` (§40, `placeFrame`; §49.3): the ownership chain of `q` is finite and ends at
frame `f`. -/
inductive FrameOf (s : S3) : Nat → Nat → Prop where
  | frame {q f : Nat} {pl : Place} : s.P[q]? = some pl → pl.owner = .frame f → FrameOf s q f
  | place {q o f : Nat} {pl : Place} : s.P[q]? = some pl → pl.owner = .place o → FrameOf s o f →
      FrameOf s q f

/-- A place with a frame exists (§40). -/
theorem FrameOf.lt {s : S3} {q f : Nat} (h : FrameOf s q f) : q < s.P.length := by
  cases h <;> exact lt_of_getElem? ‹_›

/-- One step of `FrameOf s · f` read on a Boolean premise (decision procedure for §40). -/
def frR (s : S3) (f : Nat) (U : Nat → Bool) (q : Nat) : Bool :=
  match s.P[q]? with
  | some pl => match pl.owner with
    | .frame g => decide (g = f)
    | .place o => decide (o < s.P.length) && U o
  | none => false

/-- `frR` is a bounded monotone rule (decision procedure for §40). -/
theorem frR_rule (s : S3) (f : Nat) : KRule s.P.length (frR s f) where
  mono p q hpq a h := by
    unfold frR at h ⊢; split at h
    · split at h <;> simp_all
    · exact h
  bound p a h := by
    unfold frR at h; split at h
    · exact lt_of_getElem? ‹_›
    · cases h
  loc p q hpq a := by
    unfold frR; split
    · split
      · rfl
      · rename_i o _; by_cases ho : o < s.P.length <;> simp [ho, hpq o]
    · rfl

/-- `pframeF` is the iteration of `frR` (decision procedure for §40). -/
theorem pframeF_kiter (s : S3) (f : Nat) :
    ∀ k q, pframeF s k q = some f ↔ kiter (frR s f) k q = true
  | 0, q => by simp [pframeF, kiter]
  | k + 1, q => by
    simp only [pframeF, kiter, frR]
    split
    · split
      · simp
      · rename_i o _
        by_cases hlt : o < s.P.length
        · simp [hlt, pframeF_kiter s f k o]
        · simp only [hlt, decide_false, Bool.false_and]
          cases k with
          | zero => simp [pframeF]
          | succ k => simp [pframeF, List.getElem?_eq_none_iff.2 (Nat.le_of_not_lt hlt)]
    · simp

/-- Soundness of the iteration for `FrameOf` (decision procedure for §40). -/
theorem frameOf_of_kiter (s : S3) (f : Nat) : ∀ k q, kiter (frR s f) k q = true → FrameOf s q f
  | 0, _, h => by simp [kiter] at h
  | k + 1, q, h => by
    simp only [kiter, frR] at h
    split at h
    · rename_i pl hpl
      split at h
      · rename_i g hg; simp only [decide_eq_true_eq] at h; subst h; exact .frame hpl hg
      · rename_i o ho; simp only [Bool.and_eq_true] at h
        exact .place hpl ho (frameOf_of_kiter s f k o h.2)
    · cases h

/-- `pframe` computes `FrameOf` (§40, `placeFrame`). -/
theorem pframe_iff {s : S3} {q f : Nat} : s.pframe q = some f ↔ FrameOf s q f := by
  rw [S3.pframe, pframeF_kiter]
  refine ⟨frameOf_of_kiter s f _ q, fun h => ?_⟩
  induction h with
  | frame hpl ho => exact kiter_up (frR_rule s _) 1 _ (by simp [kiter, frR, hpl, ho])
  | place hpl ho hf ih =>
    apply kiter_up (frR_rule s _) (s.P.length + 2) _
    show frR s _ (kiter (frR s _) (s.P.length + 1)) _ = true
    simp [frR, hpl, ho, ih, hf.lt]

/-! ## Transitive ownership (§40) -/

/-- One step of `OwnedIn P src` read on a Boolean premise (decision procedure for §40). -/
def owR (P : List Place) (src : Nat) (U : Nat → Bool) (q : Nat) : Bool :=
  match P[q]? with
  | some pl => match pl.owner with
    | .place o => decide (partOf P o src) || (decide (o < P.length) && U o)
    | .frame _ => false
  | none => false

/-- A place owned through the value at `src` exists (§40). -/
theorem OwnedIn.lt {P : List Place} {src q : Nat} (h : OwnedIn P src q) : q < P.length := by
  cases h <;> exact lt_of_getElem? ‹_›

/-- `owR` is a bounded monotone rule (decision procedure for §40). -/
theorem owR_rule (P : List Place) (src : Nat) : KRule P.length (owR P src) where
  mono p q hpq a h := by
    unfold owR at h ⊢; split at h
    · split at h
      · simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
        rcases h with h | ⟨h1, h2⟩
        · exact .inl h
        · exact .inr ⟨h1, hpq _ h2⟩
      · exact h
    · exact h
  bound p a h := by
    unfold owR at h; split at h
    · exact lt_of_getElem? ‹_›
    · cases h
  loc p q hpq a := by
    unfold owR; split
    · split
      · rename_i o _; by_cases ho : o < P.length <;> simp [ho, hpq o]
      · rfl
    · rfl

/-- Soundness of the iteration for `OwnedIn` (decision procedure for §40). -/
theorem ownedIn_of_kiter (P : List Place) (src : Nat) :
    ∀ k q, kiter (owR P src) k q = true → OwnedIn P src q
  | 0, _, h => by simp [kiter] at h
  | k + 1, q, h => by
    simp only [kiter, owR] at h
    split at h
    · rename_i pl hpl
      split at h
      · rename_i o ho
        simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
        rcases h with h | ⟨-, h⟩
        · exact .direct hpl ho h
        · exact .step hpl ho (ownedIn_of_kiter P src k o h)
      · cases h
    · cases h

/-- `OwnedIn` is computed by `|P| + 1` steps of `owR` (decision procedure for §40). -/
theorem ownedIn_iff {P : List Place} {src q : Nat} :
    OwnedIn P src q ↔ kiter (owR P src) (P.length + 1) q = true := by
  refine ⟨fun h => ?_, ownedIn_of_kiter P src _ q⟩
  induction h with
  | direct hpl ho hp => exact kiter_up (owR_rule P src) 1 _ (by simp [kiter, owR, hpl, ho, hp])
  | step hpl ho ho' ih =>
    apply kiter_up (owR_rule P src) (P.length + 2) _
    show owR P src (kiter (owR P src) (P.length + 1)) _ = true
    simp [owR, hpl, ho, ih, ho'.lt]

/-- Decidability of `OwnedIn` (§40). -/
instance (P : List Place) (src q : Nat) : Decidable (OwnedIn P src q) :=
  decidable_of_iff _ ownedIn_iff.symm

/-! ## Effective modes (§43) -/

/-- Modes of the active descendants of `a` whose footprint covers leaf `p` (§43). -/
def descModes (s : S3) (a p : Nat) : List Mode :=
  (List.range s.A.length).filterMap fun j =>
    match s.A[j]? with
    | some y => if y.active = true ∧ p ∈ y.footprint ∧ a ∈ s.ancs j then some y.mode else none
    | none => none

/-- Cases 2–4 of §43 for an active authority of own mode `m` covering the leaf, whose covering
active descendants have modes `ds`. -/
def effOf (m : Mode) (ds : List Mode) : Option Mode :=
  if ds = [] then some m else if Mode.modify ∈ ds then none else some .observe

/-- `effective(s, a, l)` (§43, cases 1–4), computed per leaf. -/
def effective (s : S3) (a p : Nat) : Option Mode :=
  match s.A[a]? with
  | some x => if x.active = true ∧ p ∈ x.footprint then effOf x.mode (descModes s a p) else none
  | none => none

/-- Compatible effective modes for independent ordinary accesses: only `Observe`/`Observe`
(§50). -/
def Compat (m₁ m₂ : Mode) : Prop := m₁ = .observe ∧ m₂ = .observe

/-- Effective mode `e` permits the requested mode `m`: present and not exceeded (§43). -/
def Allows (e : Option Mode) (m : Mode) : Prop := OptP e (fun e => m.le e) False

/-- Decidability of `Allows` (§43). -/
instance (e : Option Mode) (m : Mode) : Decidable (Allows e m) := by
  unfold Allows; infer_instance

/-- Footprint of authority `a` (§42), empty if it does not exist. -/
def S3.afp (s : S3) (a : Nat) : List Nat := match s.A[a]? with
  | some x => x.footprint
  | none => []

/-- Adds an authority with fresh identity `s.A.length` (§42, §60). -/
def S3.addAuth (s : S3) (y : Authority) : S3 := { s with A := s.A ++ [y] }

/-! ## Exercisable authorities (§43) -/

/-- `ExercisableAt(s, a, m)` (§43): `a` is active, its own mode permits `m`, and it is held by
the current frame, or by a place `p` such that an authority itself exercisable at `m` has an
effective mode permitting `m` on every leaf of `p`. Inductive along the holder chain (§43), so no
holder cycle justifies a right. -/
inductive S3.ExercisableAt (s : S3) : Nat → Mode → Prop where
  | base {a : Nat} {m : Mode} {y : Authority} : s.A[a]? = some y → y.active = true → m.le y.mode →
      y.holder = .frame s.top → S3.ExercisableAt s a m
  | held {a p b : Nat} {m : Mode} {y : Authority} : s.A[a]? = some y → y.active = true →
      m.le y.mode → y.holder = .place p → S3.ExercisableAt s b m →
      (∀ l ∈ footprint s.P p, Allows (effective s b l) m) → S3.ExercisableAt s a m

/-- One step of `ExercisableAt · m` read on a Boolean premise (decision procedure for §43). -/
def exR (s : S3) (m : Mode) (E : Nat → Bool) (a : Nat) : Bool :=
  match s.A[a]? with
  | some y => y.active && decide (m.le y.mode) && match y.holder with
    | .frame f => decide (f = s.top)
    | .place p => (List.range s.A.length).any fun b =>
        decide (∀ l ∈ footprint s.P p, Allows (effective s b l) m) && E b
  | none => false

/-- `any` depends only on the values of the predicate on the list (decision procedure for
§43). -/
theorem any_congr' {α : Type} {f g : α → Bool} : ∀ {l : List α}, (∀ b ∈ l, f b = g b) →
    l.any f = l.any g
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.any_cons, h a (List.mem_cons_self ..),
      any_congr' fun b hb => h b (List.mem_cons_of_mem a hb)]

/-- `exR` is a bounded monotone rule (decision procedure for §43). -/
theorem exR_rule (s : S3) (m : Mode) : KRule s.A.length (exR s m) where
  mono p q hpq a h := by
    unfold exR at h ⊢; split at h
    · simp only [Bool.and_eq_true] at h ⊢
      refine ⟨h.1, ?_⟩; split at h
      · simpa using h.2
      · simp only [Bool.and_eq_true, List.any_eq_true] at h ⊢
        obtain ⟨b, hb, hc, he⟩ := h.2
        exact ⟨b, hb, hc, hpq b he⟩
    · exact h
  bound p a h := by
    unfold exR at h; split at h
    · exact lt_of_getElem? ‹_›
    · cases h
  loc p q hpq a := by
    unfold exR; split
    · congr 1; split
      · rfl
      · exact any_congr' fun b hb => by rw [hpq b (List.mem_range.1 hb)]
    · rfl

/-- Soundness of the iteration for `ExercisableAt` (decision procedure for §43). -/
theorem exercisableAt_of_kiter (s : S3) (m : Mode) :
    ∀ k a, kiter (exR s m) k a = true → s.ExercisableAt a m
  | 0, _, h => by simp [kiter] at h
  | k + 1, a, h => by
    simp only [kiter, exR] at h
    split at h
    · rename_i y hy
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨ha, hm⟩, h⟩ := h
      split at h
      · rename_i f hf; exact .base hy ha hm (by simp at h; rw [hf, h])
      · rename_i p hp
        simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨b, -, hc, hb⟩ := h
        exact .held hy ha hm hp (exercisableAt_of_kiter s m k b hb) hc
    · cases h

/-- The frame-held case of `exR` (decision procedure for §43). -/
theorem exR_base {s : S3} {m : Mode} {E : Nat → Bool} {a : Nat} {y : Authority}
    (hy : s.A[a]? = some y) (ha : y.active = true) (hm : m.le y.mode)
    (hf : y.holder = .frame s.top) : exR s m E a = true := by
  unfold exR; rw [hy]; simp [ha, hm, hf]

/-- The place-held case of `exR` (decision procedure for §43). -/
theorem exR_held {s : S3} {m : Mode} {E : Nat → Bool} {a p b : Nat} {y : Authority}
    (hy : s.A[a]? = some y) (ha : y.active = true) (hm : m.le y.mode) (hp : y.holder = .place p)
    (hb : b < s.A.length) (hc : ∀ l ∈ footprint s.P p, Allows (effective s b l) m)
    (hE : E b = true) : exR s m E a = true := by
  simp only [exR, hy, ha, hp, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq,
    List.any_eq_true, List.mem_range]
  exact ⟨hm, b, hb, hc, hE⟩

/-- `ExercisableAt` is computed by `|A| + 1` steps of `exR` (decision procedure for §43). -/
theorem exercisableAt_iff {s : S3} {a : Nat} {m : Mode} :
    s.ExercisableAt a m ↔ kiter (exR s m) (s.A.length + 1) a = true := by
  refine ⟨fun h => ?_, exercisableAt_of_kiter s m _ a⟩
  induction h with
  | base hy ha hm hf => exact exR_base hy ha hm hf
  | held hy ha hm hp hb hc ih =>
    rw [← kiter_fix (exR_rule s _)]
    have hb' := kiter_bound (exR_rule s _) _ _ ih
    exact exR_held hy ha hm hp hb' hc ih

/-- Decidability of `ExercisableAt` (§43). -/
instance (s : S3) (a : Nat) (m : Mode) : Decidable (s.ExercisableAt a m) :=
  decidable_of_iff _ exercisableAt_iff.symm

/-- `HasRight(s, m, q)` (§43): the current frame has an authority exercisable at `m` whose
effective mode permits `m` on every leaf of `q`'s footprint. -/
def HasRight (s : S3) (m : Mode) (q : Nat) : Prop :=
  ∃ a ∈ List.range s.A.length, s.ExercisableAt a m ∧
    ∀ l ∈ footprint s.P q, Allows (effective s a l) m

/-- Decidability of `HasRight` (§43). -/
instance (s : S3) (m : Mode) (q : Nat) : Decidable (HasRight s m q) := by
  unfold HasRight; infer_instance

/-- Authority `g` grounds the right `HasRight(s, m, q)` (§43; §63.4, §69.2, §70.3: "the
exercisable authority on which that right rests"): it is exercisable at `m` and its effective mode
permits `m` on every leaf of `q`'s footprint. -/
def Grounds (s : S3) (m : Mode) (q g : Nat) : Prop :=
  g ∈ List.range s.A.length ∧ s.ExercisableAt g m ∧
    ∀ l ∈ footprint s.P q, Allows (effective s g l) m

/-- Decidability of `Grounds` (§63.4, §69.2, §70.3). -/
instance (s : S3) (m : Mode) (q g : Nat) : Decidable (Grounds s m q g) := by
  unfold Grounds; infer_instance

/-- Authority `j` is the grounding authority `g` or belongs to its origin chain (§63.4, §69.2,
§70.3: "the exercisable authority on which that right rests and its origin chain"). -/
def RightChain (s : S3) (g j : Nat) : Prop := j = g ∨ j ∈ s.ancs g

/-- Decidability of `RightChain` (§63.4, §69.2, §70.3). -/
instance (s : S3) (g j : Nat) : Decidable (RightChain s g j) := by
  unfold RightChain; infer_instance

/-! ## Dependencies and anchors (§44) -/

/-- Anchors of the value at `q`, inherited from its parts (§44: dependencies of contained values
are accounted for transitively). -/
def depsOf (s : S3) (q : Nat) : List Nat :=
  ((List.range s.P.length).filter fun r => decide (partOf s.P r q)).flatMap s.D

/-- The anchors of every place containing leaf `p` are valid, that is, active (§44; §66.3,
§67.3, §68.3). -/
def DepsValid (s : S3) (p : Nat) : Prop :=
  ∀ q ∈ List.range s.P.length, partOf s.P p q → ∀ x ∈ s.D q, s.Active x

/-- Decidability of `DepsValid` (§44). -/
instance (s : S3) (p : Nat) : Decidable (DepsValid s p) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- The frame of the effective anchor of `x` (the frame of its holder) exists and is `fd` or an
ancestor of `fd` (§44). -/
def EffAnchorOK (s : S3) (x : Nat) (fd : Option Nat) : Prop :=
  OptP (s.A[s.effAnchor x]?) (fun z => OptP (s.hframe z.holder)
    (fun g => OptP fd (fun f => ancestor s.F g f) False) False) False

/-- Decidability of `EffAnchorOK` (§44). -/
instance (s : S3) (x : Nat) (fd : Option Nat) : Decidable (EffAnchorOK s x fd) := by
  unfold EffAnchorOK; infer_instance

/-- `AnchorOrder` (§44, §54): for every anchor `x ∈ D(q)` of a usable place `q`, the frame of the
effective anchor of `x` is the frame of `q` or an ancestor. -/
def AnchorOrder (s : S3) : Prop := ∀ q, s.Usable q → ∀ x ∈ s.D q, EffAnchorOK s x (s.pframe q)

/-- `AnchorOrder` read on the places of `P` (decision procedure for §44). -/
theorem anchorOrder_iff {s : S3} : AnchorOrder s ↔
    ∀ q ∈ List.range s.P.length, s.Usable q → ∀ x ∈ s.D q, EffAnchorOK s x (s.pframe q) :=
  ⟨fun h q _ hq => h q hq, fun h q hq => h q (List.mem_range.2 hq.lt) hq⟩

/-- Decidability of `AnchorOrder` (§44). -/
instance (s : S3) : Decidable (AnchorOrder s) := decidable_of_iff _ anchorOrder_iff.symm

/-- `AnchorOrderHeld` (§44, §54): the rule of `AnchorOrder` for every active authority held by a
usable place `q`. -/
def AnchorOrderHeld (s : S3) : Prop :=
  ∀ q, s.Usable q → ∀ (x : Nat) (y : Authority), s.A[x]? = some y → y.active = true →
    y.holder = .place q → EffAnchorOK s x (s.pframe q)

/-- `AnchorOrderHeld` read on the places of `P` and the authorities of `A` (decision procedure for
§44). -/
theorem anchorOrderHeld_iff {s : S3} : AnchorOrderHeld s ↔
    ∀ q ∈ List.range s.P.length, s.Usable q → ∀ x ∈ List.range s.A.length,
      OptP (s.A[x]?) (fun y => y.active = true → y.holder = .place q →
        EffAnchorOK s x (s.pframe q)) True := by
  constructor
  · intro h q _ hq x _
    unfold OptP; split
    · rename_i y hy; exact h q hq x y hy
    · trivial
  · intro h q hq x y hy ya hh
    have := h q (List.mem_range.2 hq.lt) hq x (List.mem_range.2 (lt_of_getElem? hy))
    simp only [OptP, hy] at this; exact this ya hh

/-- Decidability of `AnchorOrderHeld` (§44). -/
instance (s : S3) : Decidable (AnchorOrderHeld s) := decidable_of_iff _ anchorOrderHeld_iff.symm

/-! ## Outcomes (§58) -/

/-- `Outcome3 = ok(new_state) | reject | fail` (§58). `fail` leaves the state unchanged and
carries none. -/
inductive Outcome3 (σ : Type) where
  | ok (s : σ)
  | reject
  | fail

/-- A kernel transition other than `alloc` (§58): `ok` with the effect when the preconditions
hold, `reject` otherwise; never `fail`. -/
inductive Guarded {σ : Type} (Pre : Prop) (eff : σ) : Outcome3 σ → Prop where
  | ok : Pre → Guarded Pre eff (.ok eff)
  | reject : ¬ Pre → Guarded Pre eff .reject

end Ern.MemoryModel.Access
