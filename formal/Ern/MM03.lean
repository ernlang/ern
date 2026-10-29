import Ern.MM02

/-!
# MM-03.3 v0.2: kernel of the access discipline (exploratory model, milestone 1, pass 2)

Abstract layer of `formal/DESIGN.md` ("Abstract model"): memory is a finite tree of places.
Refinement towards MM-02 (MM-03.3 §9) is milestone 2 and is not treated here; the module
imports `Ern.MM02` without using or changing it. Covered fragment: sequential execution of the
kernel operations (MM-03.3 §3–5) and of the arena (§6); no concurrency, no persistent handles.

Pass 2 follows arbitrages A1–A11 of the task: authorities are held by a frame or a place (A4),
places are owned by a frame or a place (A5), rights are exercised through `Exercisable` (A2),
values end by `endUse` and owned storage is released by `free` (A6).
-/

namespace Ern.MM03

/-! ## Frames (MM-03.3.1) -/

/-- Frame stack `F` (MM-03.3.1): frame identities, current frame first. The parent of a frame
is the next element; the last element is the initial frame. -/
abbrev Frames := List Nat

/-- `ancestor F f₁ f₂` (MM-03.3.1): `f₁` is `f₂` itself or one of its ancestors in `F`, that is,
`f₁` occurs in `F` from the first occurrence of `f₂` on. -/
def ancestor (F : Frames) (f₁ f₂ : Nat) : Prop := f₁ ∈ F.dropWhile (· != f₂)

instance (F : Frames) (f₁ f₂ : Nat) : Decidable (ancestor F f₁ f₂) :=
  inferInstanceAs (Decidable (_ ∈ _))

/-! ## Parent chains

Places (by `parent`) and authorities (by `origin`) form forests whose identities are indices.
A chain only follows a link to a strictly smaller index; the fuel `k` only ensures
termination. -/

/-- Strict ancestors of `i` along the link `org`, nearest first. -/
def chainF (org : Nat → Option Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, i =>
    match org i with
    | some o => if o < i then o :: chainF org k o else []
    | none => []

/-- Strict ancestors of `i` along `org` (fuel `i`, enough since the chain decreases). -/
def chain (org : Nat → Option Nat) (i : Nat) : List Nat := chainF org i i

theorem chainF_none {org : Nat → Option Nat} {i : Nat} (h : org i = none) :
    ∀ k, chainF org k i = []
  | 0 => rfl
  | _ + 1 => by simp [chainF, h]

theorem chainF_fuel (org : Nat → Option Nat) :
    ∀ k₁ k₂ i, i ≤ k₁ → i ≤ k₂ → chainF org k₁ i = chainF org k₂ i
  | 0, 0, _, _, _ => rfl
  | 0, _ + 1, i, h, _ => by
    obtain rfl : i = 0 := by omega
    simp only [chainF]; split <;> simp
  | _ + 1, 0, i, _, h => by
    obtain rfl : i = 0 := by omega
    simp only [chainF]; split <;> simp
  | k₁ + 1, k₂ + 1, i, h₁, h₂ => by
    simp only [chainF]; split
    · split
      · rw [chainF_fuel org k₁ k₂ _ (by omega) (by omega)]
      · rfl
    · rfl

theorem chain_none {org : Nat → Option Nat} {i : Nat} (h : org i = none) : chain org i = [] :=
  chainF_none h i

theorem chain_cons {org : Nat → Option Nat} {i o : Nat} (h : org i = some o) (hlt : o < i) :
    chain org i = o :: chain org o := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  simp only [chain, chainF, h, hlt, ↓reduceIte]
  rw [chainF_fuel org k o o (by omega) (Nat.le_refl o)]

theorem chainF_lt {org : Nat → Option Nat} : ∀ k i j, j ∈ chainF org k i → j < i
  | 0, _, _, h => by simp [chainF] at h
  | k + 1, i, j, h => by
    simp only [chainF] at h; split at h
    · split at h
      · rcases List.mem_cons.1 h with rfl | h
        · assumption
        · exact Nat.lt_trans (chainF_lt k _ j h) ‹_›
      · simp at h
    · simp at h

/-- Every element of a chain is strictly smaller than its start: the walk along a chain
terminates (A7). -/
theorem chain_lt {org : Nat → Option Nat} {i j : Nat} (h : j ∈ chain org i) : j < i :=
  chainF_lt i i j h

theorem chainF_length {org : Nat → Option Nat} : ∀ k i, (chainF org k i).length ≤ k
  | 0, _ => by simp [chainF]
  | k + 1, i => by
    simp only [chainF]; split
    · split
      · simp only [List.length_cons]; have := chainF_length (org := org) k ‹_›; omega
      · simp
    · simp

/-- A chain from `i` has at most `i` elements (A7: termination of the walk). -/
theorem chain_length (org : Nat → Option Nat) (i : Nat) : (chain org i).length ≤ i :=
  chainF_length i i

theorem chainF_congr {org org' : Nat → Option Nat} :
    ∀ k i, (∀ j ≤ i, org j = org' j) → chainF org k i = chainF org' k i
  | 0, _, _ => rfl
  | k + 1, i, h => by
    simp only [chainF]; rw [h i (Nat.le_refl i)]; split
    · split
      · rw [chainF_congr k _ fun j hj => h j (by omega)]
      · rfl
    · rfl

theorem chain_congr {org org' : Nat → Option Nat} {i : Nat} (h : ∀ j ≤ i, org j = org' j) :
    chain org i = chain org' i := chainF_congr i i h

/-- Two roots (elements without link) of one chain are equal. -/
theorem chainF_root {org : Nat → Option Nat} : ∀ k i r r', r ∈ chainF org k i → org r = none →
    r' ∈ chainF org k i → org r' = none → r = r'
  | 0, _, _, _, h, _, _, _ => by simp [chainF] at h
  | k + 1, i, r, r', h, hr, h', hr' => by
    simp only [chainF] at h h'; split at h
    · rename_i o ho; simp only [ho] at h'
      split at h
      · rename_i hlt; simp only [hlt, ↓reduceIte] at h'
        rcases List.mem_cons.1 h with rfl | h <;> rcases List.mem_cons.1 h' with rfl | h'
        · rfl
        · rw [chainF_none hr] at h'; simp at h'
        · rw [chainF_none hr'] at h; simp at h
        · exact chainF_root k _ r r' h hr h' hr'
      · simp at h
    · simp at h

/-! ## Places (MM-03.3.2, A5) -/

/-- Holder of an authority (A4) or owner of a place (A5): a frame or a place. -/
inductive Holder where
  | frame (f : Nat)
  | place (p : Nat)
deriving DecidableEq, Repr

/-- Logical place (MM-03.3.2: `Place { id, parent?, frame, kind }`). Its identity is its index
in `P`. The field `frame` of MM-03.3.2 is generalised by `owner` (A5): a place is owned by a
frame or by another place (owned storage). A part has the owner of its parent (`WF3`). `kind`
is not interpreted: MM-03.3.2 gives no values for it. -/
structure Place where
  parent : Option Nat
  owner : Holder
  kind : Nat
deriving DecidableEq, Repr

/-- `parent` link of the place with index `i` (MM-03.3.2). -/
def parentOf (P : List Place) (i : Nat) : Option Nat := (P[i]?).bind (·.parent)

/-- `partOf P p q` (MM-03.3.2, logical composition): `p` is a place of `P` and `q` is `p` itself
or one of its ancestors along `parent`. -/
def partOf (P : List Place) (p q : Nat) : Prop :=
  p < P.length ∧ (p = q ∨ q ∈ chain (parentOf P) p)

instance (P : List Place) (p q : Nat) : Decidable (partOf P p q) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Storage leaf (MM-03.3.2): a place without a strict part. -/
def isLeaf (P : List Place) (l : Nat) : Prop := ∀ r < P.length, parentOf P r ≠ some l

instance (P : List Place) (l : Nat) : Decidable (isLeaf P l) :=
  inferInstanceAs (Decidable (∀ _, _))

/-- `footprint P q` (MM-03.3.2): the leaves of `P` that are parts of `q`. -/
def footprint (P : List Place) (q : Nat) : List Nat :=
  (List.range P.length).filter fun l => decide (isLeaf P l ∧ partOf P l q)

/-- Two places overlap when their footprints share a leaf (MM-03.3.2). -/
def overlap (P : List Place) (p q : Nat) : Prop := ∃ l ∈ footprint P p, l ∈ footprint P q

instance (P : List Place) (p q : Nat) : Decidable (overlap P p q) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- Structural disjointness (MM-03.3.2): neither path is a part of the other. -/
def structurallyDisjoint (P : List Place) (p q : Nat) : Prop := ¬ partOf P p q ∧ ¬ partOf P q p

instance (P : List Place) (p q : Nat) : Decidable (structurallyDisjoint P p q) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem mem_footprint {P : List Place} {q l : Nat} :
    l ∈ footprint P q ↔ l < P.length ∧ isLeaf P l ∧ partOf P l q := by
  simp [footprint, List.mem_filter, List.mem_range]

/-! ## State `S3` (MM-03.3 §1) -/

/-- Initialisation state of a leaf (MM-03.3.3). -/
inductive InitSt where
  | uninit
  | init
  | moved
deriving DecidableEq, Repr

/-- Mode of an authority (MM-03.3.4). -/
inductive Mode where
  | observe
  | modify
deriving DecidableEq, Repr

/-- Order of modes: `Observe` does not exceed `Modify` (MM-03.3.4: `Modify` allows
modifications and observations). -/
def Mode.le (m m' : Mode) : Prop := m = .observe ∨ m' = .modify

instance (m m' : Mode) : Decidable (m.le m') := inferInstanceAs (Decidable (_ ∨ _))

/-- Authority (MM-03.3.4: `Authority { id, mode, origin?, footprint, frame, active }`). Its
identity is its index in `A`; its footprint is a list of leaves; no `Suspended` status is
stored. The field `frame` of MM-03.3.4 is generalised by `holder` (A4): a frame or the place
whose value contains the authority. -/
structure Authority where
  mode : Mode
  origin : Option Nat
  footprint : List Nat
  holder : Holder
  active : Bool
deriving DecidableEq, Repr

/-- State `S3 = (F, P, I, A, D)` (MM-03.3 §1), without component `M` (pass-1 arbitrage 1).
`nF` is the next frame identity, so that an exited frame is never reused. `D q` lists the
anchors of place `q`, each an authority identity (pass-1 arbitrage 2). `dead q`: the place is
logically dead (A6, `endUse` and `free`); `freed q`: its storage was released by `free` (A6);
`pin l`: leaf `l` is dynamically pinned (A8). -/
structure S3 where
  F : Frames
  nF : Nat
  P : List Place
  I : Nat → InitSt
  A : List Authority
  D : Nat → List Nat
  dead : Nat → Bool
  freed : Nat → Bool
  pin : Nat → Bool

/-- Contracts `K` (MM-03.3.8) for an execution. Types are a representation choice: regions as
lists of leaves; `SharedMutable`, `Pinned` and `ExternalDone` on leaves; `Invalidates s r x`
for "in state `s`, the invalidating operation of resource `r` invalidates anchor `x`";
`Deallocable p` and `FreeCompat p auth` for `free` (A6). The obligations of each contract are
named hypotheses of theorems, never fields. -/
structure K where
  DeclaredDisjoint : List Nat → List Nat → Prop
  SharedMutable : Nat → Prop
  Pinned : Nat → Prop
  Invalidates : S3 → Nat → Nat → Prop
  ExternalDone : Nat → Prop
  Deallocable : Nat → Prop
  FreeCompat : Nat → Nat → Prop

/-- Obligation of `DeclaredDisjoint` (MM-03.3.8): a declaration never covers two regions that
really overlap. -/
def DDSound (k : K) : Prop := ∀ r r', k.DeclaredDisjoint r r' → ∀ l ∈ r, l ∉ r'

/-- Initial state: one frame, no place, no authority. -/
def S3.init : S3 :=
  ⟨[0], 1, [], fun _ => .uninit, [], fun _ => [], fun _ => false, fun _ => false, fun _ => false⟩

/-- `origin` link of the authority with index `i` (MM-03.3.4). -/
def S3.org (s : S3) (i : Nat) : Option Nat := (s.A[i]?).bind (·.origin)

/-- Strict ancestors of authority `i` along `origin`: `i` descends from each (MM-03.3.5). -/
def S3.ancs (s : S3) (i : Nat) : List Nat := chain s.org i

/-- Active authority, that is, valid anchor (pass-1 arbitrage 2). -/
def S3.Active (s : S3) (x : Nat) : Prop := ∃ y, s.A[x]? = some y ∧ y.active = true

instance (s : S3) (x : Nat) : Decidable (s.Active x) :=
  match h : s.A[x]? with
  | some y => if hy : y.active = true then isTrue ⟨y, h, hy⟩
    else isFalse fun ⟨y', h', hy'⟩ => by rw [h] at h'; cases h'; exact hy hy'
  | none => isFalse fun ⟨_, h', _⟩ => by rw [h] at h'; cases h'

/-- Current frame: the head of the stack (MM-03.3.1). -/
def S3.top (s : S3) : Nat := s.F.headD 0

/-! ## Decidable helpers -/

/-- Predicate on an optional value: `P y` for `some y`, `d` for `none`. -/
def OptP {α : Type} (o : Option α) (P : α → Prop) (d : Prop) : Prop :=
  match o with
  | some y => P y
  | none => d

instance {α : Type} (o : Option α) (P : α → Prop) (d : Prop) [DecidablePred P] [Decidable d] :
    Decidable (OptP o P d) :=
  match o with
  | some y => inferInstanceAs (Decidable (P y))
  | none => inferInstanceAs (Decidable d)

theorem lt_of_getElem? {α : Type} {l : List α} {i : Nat} {x : α} (h : l[i]? = some x) :
    i < l.length := (List.getElem?_eq_some_iff.1 h).1

/-! ## Least fixed points on a bounded universe

`Usable` (A5) and `Exercisable` (A2) are inductive predicates. Each is the least fixed point of
a monotone rule over identities below a bound `n`; its Kleene iteration is stable after `n + 1`
steps, which makes it decidable. -/

/-- `k`-th Kleene iterate of a rule `R` on Boolean predicates over `Nat`. -/
def kiter (R : (Nat → Bool) → Nat → Bool) : Nat → Nat → Bool
  | 0, _ => false
  | k + 1, a => R (kiter R k) a

/-- A monotone rule whose conclusions lie below `n` and which reads its premise only below
`n`. -/
structure KRule (n : Nat) (R : (Nat → Bool) → Nat → Bool) : Prop where
  mono : ∀ p q : Nat → Bool, (∀ a, p a = true → q a = true) → ∀ a, R p a = true → R q a = true
  bound : ∀ p a, R p a = true → a < n
  loc : ∀ p q : Nat → Bool, (∀ a, a < n → p a = q a) → ∀ a, R p a = R q a

theorem kiter_mono {n : Nat} {R : (Nat → Bool) → Nat → Bool} (h : KRule n R) :
    ∀ k a, kiter R k a = true → kiter R (k + 1) a = true
  | 0, _, hk => by simp [kiter] at hk
  | k + 1, a, hk => h.mono _ _ (kiter_mono h k) a hk

theorem kiter_bound {n : Nat} {R : (Nat → Bool) → Nat → Bool} (h : KRule n R) :
    ∀ k a, kiter R k a = true → a < n
  | 0, _, hk => by simp [kiter] at hk
  | _ + 1, a, hk => h.bound _ a hk

theorem countP_le_of {l : List Nat} {p q : Nat → Bool} (hpq : ∀ a ∈ l, p a = true → q a = true) :
    l.countP p ≤ l.countP q := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.countP_cons]
    have := ih fun b hb => hpq b (List.mem_cons_of_mem _ hb)
    cases hp : p a <;> cases hq : q a <;> simp_all <;> omega

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

theorem all_false_exists {α : Type} {p : α → Bool} : ∀ {l : List α}, l.all p = false →
    ∃ a ∈ l, p a = false
  | [], h => by simp at h
  | a :: l, h => by
    simp only [List.all_cons, Bool.and_eq_false_iff] at h
    rcases h with h | h
    · exact ⟨a, List.mem_cons_self .., h⟩
    · obtain ⟨b, hb, hb'⟩ := all_false_exists h; exact ⟨b, List.mem_cons_of_mem _ hb, hb'⟩

/-- Stability of the iteration at step `k`, below `n`. -/
def kstab (R : (Nat → Bool) → Nat → Bool) (n k : Nat) : Bool :=
  (List.range n).all fun a => kiter R (k + 1) a == kiter R k a

theorem kstab_succ {n : Nat} {R : (Nat → Bool) → Nat → Bool} (h : KRule n R) {k : Nat}
    (hs : kstab R n k = true) : kstab R n (k + 1) = true := by
  simp only [kstab, List.all_eq_true, List.mem_range, beq_iff_eq] at hs ⊢
  intro a ha
  show R (kiter R (k + 1)) a = R (kiter R k) a
  exact h.loc _ _ (fun b hb => hs b hb) a

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

/-- The iteration is stable from step `n + 1` on. -/
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

/-! ## Usable places (MM-03.3.1, A5) -/

/-- `s.Usable q` (A5): place `q` exists, is not logically dead, and the chain of its owners ends
at a frame on the stack. Inductive, so a cycle of owners never makes a place usable. -/
inductive S3.Usable (s : S3) : Nat → Prop where
  | frame {q f : Nat} {pl : Place} : s.P[q]? = some pl → s.dead q = false →
      pl.owner = .frame f → f ∈ s.F → S3.Usable s q
  | place {q o : Nat} {pl : Place} : s.P[q]? = some pl → s.dead q = false →
      pl.owner = .place o → S3.Usable s o → S3.Usable s q

theorem S3.Usable.lt {s : S3} {q : Nat} (h : s.Usable q) : q < s.P.length := by
  cases h <;> exact lt_of_getElem? ‹_›

/-- One step of `Usable`, read on a Boolean premise. -/
def usableR (s : S3) (U : Nat → Bool) (q : Nat) : Bool :=
  match s.P[q]? with
  | some pl => !s.dead q && match pl.owner with
    | .frame f => decide (f ∈ s.F)
    | .place o => decide (o < s.P.length) && U o
  | none => false

theorem usableR_place {s : S3} {U : Nat → Bool} {q o : Nat} {pl : Place} (hpl : s.P[q]? = some pl)
    (hd : s.dead q = false) (ho : pl.owner = .place o) (hlt : o < s.P.length) (hU : U o = true) :
    usableR s U q = true := by
  simp [usableR, hpl, hd, ho, hlt, hU]

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

instance (s : S3) (q : Nat) : Decidable (s.Usable q) := decidable_of_iff _ usable_iff.symm

/-- A holder is live (A4, A5): a frame on the stack, or a usable place. -/
def HolderLive (s : S3) : Holder → Prop
  | .frame f => f ∈ s.F
  | .place p => s.Usable p

instance (s : S3) (h : Holder) : Decidable (HolderLive s h) := by
  cases h <;> unfold HolderLive <;> infer_instance

/-- Frame ending the owner chain of place `q`, searched within `k` steps (MM-03.3.1, A5). -/
def pframeF (s : S3) : Nat → Nat → Option Nat
  | 0, _ => none
  | k + 1, q =>
    match s.P[q]? with
    | some pl =>
      match pl.owner with
      | .frame f => some f
      | .place o => pframeF s k o
    | none => none

/-- Frame of place `q`: the frame at the end of its owner chain (A5), within `|P| + 1` steps,
enough for a chain without repetition. -/
def S3.pframe (s : S3) (q : Nat) : Option Nat := pframeF s (s.P.length + 1) q

/-- Frame of a holder (A4). -/
def S3.hframe (s : S3) : Holder → Option Nat
  | .frame f => some f
  | .place p => s.pframe p

/-! ## Effective authority (MM-03.3.5) -/

/-- Modes of the active descendants of `a` whose footprint covers leaf `p` (MM-03.3.5). -/
def descModes (s : S3) (a p : Nat) : List Mode :=
  (List.range s.A.length).filterMap fun j =>
    match s.A[j]? with
    | some y => if y.active = true ∧ p ∈ y.footprint ∧ a ∈ s.ancs j then some y.mode else none
    | none => none

/-- Cases 1 to 3 of MM-03.3.5 for an active authority covering the leaf, of mode `m`, whose
active covering descendants have modes `ds`. -/
def effOf (m : Mode) (ds : List Mode) : Option Mode :=
  if ds = [] then some m else if Mode.modify ∈ ds then none else some .observe

/-- `effective(a, p)` (MM-03.3.5), computed per leaf, with no stored status: absent if `a` is
inactive or does not cover `p`, `effOf` otherwise. -/
def effective (s : S3) (a p : Nat) : Option Mode :=
  match s.A[a]? with
  | some x => if x.active = true ∧ p ∈ x.footprint then effOf x.mode (descModes s a p) else none
  | none => none

/-- Compatibility of effective modes for ordinary accesses (MM-03.3 §2, I1): only
`Observe`/`Observe` is compatible. -/
def Compat (m₁ m₂ : Mode) : Prop := m₁ = .observe ∧ m₂ = .observe

/-- Effective mode `e` permits the requested mode `m`: present and not exceeded
(MM-03.3 §3, O1.3). -/
def Allows (e : Option Mode) (m : Mode) : Prop := OptP e (fun e => m.le e) False

instance (e : Option Mode) (m : Mode) : Decidable (Allows e m) := by
  unfold Allows; infer_instance

/-- Footprint of authority `a`, empty if it does not exist. -/
def S3.afp (s : S3) (a : Nat) : List Nat := match s.A[a]? with
  | some x => x.footprint
  | none => []

/-- Appends an authority to `A`: its identity is `s.A.length`. -/
def S3.addAuth (s : S3) (y : Authority) : S3 := { s with A := s.A ++ [y] }

/-- Anchors of the value at `q`, inherited from its parts (MM-03.3.6: a containing value
inherits the dependencies of the contained values). -/
def depsOf (s : S3) (q : Nat) : List Nat :=
  ((List.range s.P.length).filter fun r => decide (partOf s.P r q)).flatMap s.D

/-- Dependencies still valid for the values containing leaf `p` (MM-03.3 §5): every anchor of a
place of which `p` is a part is active. -/
def DepsValid (s : S3) (p : Nat) : Prop :=
  ∀ q ∈ List.range s.P.length, partOf s.P p q → ∀ x ∈ s.D q, s.Active x

instance (s : S3) (p : Nat) : Decidable (DepsValid s p) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- Non-escape restriction (MM-03.3.6) for anchor `x` and a destination of frame `fd`: if `x`
is a local anchor (no origin), its frame is `fd` or an ancestor of it, so `fd` does not outlive
it. The frame of an anchor is the frame of its holder (A4, A5). -/
def NoEscape (s : S3) (x : Nat) (fd : Option Nat) : Prop :=
  OptP (s.A[x]?) (fun y => y.origin = none →
    OptP (s.hframe y.holder) (fun g => OptP fd (fun f => ancestor s.F g f) True) True) True

instance (s : S3) (x : Nat) (fd : Option Nat) : Decidable (NoEscape s x fd) := by
  unfold NoEscape; infer_instance

/-- `mapI f i l` applies `f` to each element of `l` with its index, counted from `i`. -/
def mapI {α β : Type} (f : Nat → α → β) : Nat → List α → List β
  | _, [] => []
  | i, a :: l => f i a :: mapI f (i + 1) l

theorem length_mapI {α β : Type} (f : Nat → α → β) :
    ∀ (i : Nat) (l : List α), (mapI f i l).length = l.length
  | _, [] => rfl
  | i, _ :: l => by simp [mapI, length_mapI f (i + 1) l]

theorem getElem?_mapI {α β : Type} (f : Nat → α → β) :
    ∀ (i : Nat) (l : List α) (j : Nat), (mapI f i l)[j]? = (l[j]?).map (f (i + j))
  | _, [], _ => rfl
  | i, a :: l, 0 => by simp [mapI]
  | i, a :: l, j + 1 => by
    simp only [mapI, List.getElem?_cons_succ, getElem?_mapI f (i + 1) l j]
    congr 2; omega

/-! ## Exercisable authorities (A2) -/

/-- `s.Exercisable a` (A2): base case, an active authority held by the current frame; inductive
case, an active authority held by a usable place `p` for which the current frame already has an
exercisable authority whose effective mode permits the mode of `a` on the whole footprint of
`p`. Inductive, so no cycle justifies a right. A2 says "mode effectif ≥" without naming the
comparand; comparing with the mode of `a` is an interpretation (see the report). -/
inductive S3.Exercisable (s : S3) : Nat → Prop where
  | base {a : Nat} {y : Authority} : s.A[a]? = some y → y.active = true →
      y.holder = .frame s.top → S3.Exercisable s a
  | held {a p b : Nat} {y : Authority} : s.A[a]? = some y → y.active = true →
      y.holder = .place p → s.Usable p → S3.Exercisable s b →
      (∀ l ∈ footprint s.P p, Allows (effective s b l) y.mode) → S3.Exercisable s a

/-- One step of `Exercisable`, read on a Boolean premise. -/
def exR (s : S3) (E : Nat → Bool) (a : Nat) : Bool :=
  match s.A[a]? with
  | some y => y.active && match y.holder with
    | .frame f => decide (f = s.top)
    | .place p => decide (s.Usable p) && (List.range s.A.length).any fun b =>
        decide (∀ l ∈ footprint s.P p, Allows (effective s b l) y.mode) && E b
  | none => false

theorem any_congr' {α : Type} {f g : α → Bool} : ∀ {l : List α}, (∀ b ∈ l, f b = g b) →
    l.any f = l.any g
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.any_cons, h a (List.mem_cons_self ..),
      any_congr' fun b hb => h b (List.mem_cons_of_mem a hb)]

theorem exR_rule (s : S3) : KRule s.A.length (exR s) where
  mono p q hpq a h := by
    unfold exR at h ⊢; split at h
    · simp only [Bool.and_eq_true] at h ⊢
      refine ⟨h.1, ?_⟩; split at h
      · simpa using h.2
      · simp only [Bool.and_eq_true, List.any_eq_true] at h ⊢
        obtain ⟨hu, b, hb, hc, he⟩ := h.2
        exact ⟨hu, b, hb, hc, hpq b he⟩
    · exact h
  bound p a h := by
    unfold exR at h; split at h
    · exact lt_of_getElem? ‹_›
    · cases h
  loc p q hpq a := by
    unfold exR; split
    · congr 1; split
      · rfl
      · congr 1
        exact any_congr' fun b hb => by rw [hpq b (List.mem_range.1 hb)]
    · rfl

theorem exercisable_of_kiter (s : S3) : ∀ k a, kiter (exR s) k a = true → s.Exercisable a
  | 0, _, h => by simp [kiter] at h
  | k + 1, a, h => by
    simp only [kiter, exR] at h
    split at h
    · rename_i y hy
      simp only [Bool.and_eq_true] at h
      obtain ⟨ha, h⟩ := h
      split at h
      · rename_i f hf; exact .base hy ha (by simp at h; rw [hf, h])
      · rename_i p hp
        simp only [Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq] at h
        obtain ⟨hu, b, -, hc, hb⟩ := h
        exact .held hy ha hp hu (exercisable_of_kiter s k b hb) hc
    · cases h

theorem exR_base {s : S3} {E : Nat → Bool} {a : Nat} {y : Authority} (hy : s.A[a]? = some y)
    (ha : y.active = true) (hf : y.holder = .frame s.top) : exR s E a = true := by
  unfold exR; rw [hy]; simp only [ha, hf, Bool.true_and, decide_true]

theorem exR_held {s : S3} {E : Nat → Bool} {a p b : Nat} {y : Authority} (hy : s.A[a]? = some y)
    (ha : y.active = true) (hp : y.holder = .place p) (hu : s.Usable p) (hb : b < s.A.length)
    (hc : ∀ l ∈ footprint s.P p, Allows (effective s b l) y.mode) (hE : E b = true) :
    exR s E a = true := by
  simp only [exR, hy, ha, hp, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq,
    List.any_eq_true, List.mem_range]
  exact ⟨hu, b, hb, hc, hE⟩

theorem exercisable_iff {s : S3} {a : Nat} :
    s.Exercisable a ↔ kiter (exR s) (s.A.length + 1) a = true := by
  refine ⟨fun h => ?_, exercisable_of_kiter s _ a⟩
  induction h with
  | base hy ha hf => exact exR_base hy ha hf
  | held hy ha hp hu hb hc ih =>
    rw [← kiter_fix (exR_rule s)]
    have hb' := kiter_bound (exR_rule s) _ _ ih
    exact exR_held hy ha hp hu hb' hc ih

instance (s : S3) (a : Nat) : Decidable (s.Exercisable a) :=
  decidable_of_iff _ exercisable_iff.symm

/-- The current frame has an exercisable authority whose effective mode permits `m` on every
leaf of `q` (A2: exercisable `Modify` on a place). -/
def HasRight (s : S3) (m : Mode) (q : Nat) : Prop :=
  ∃ a ∈ List.range s.A.length, s.Exercisable a ∧ ∀ l ∈ footprint s.P q, Allows (effective s a l) m

instance (s : S3) (m : Mode) (q : Nat) : Decidable (HasRight s m q) := by
  unfold HasRight; infer_instance

/-! ## Outcomes and guarded relations (MM-03.3 §3) -/

/-- `Outcome3` (MM-03.3 §3): `ok` with the new state, or `reject`, refusal by the static
discipline, distinct from a defined failure of an abstraction and from `ub` of MM-02. -/
inductive Outcome3 (σ : Type) where
  | ok (s : σ)
  | reject

/-- Common form of the transition rules of MM-03.3 §3–5: `ok` with the effect when the
precondition holds, `reject` otherwise. -/
inductive Guarded {σ : Type} (Pre : Prop) (eff : σ) : Outcome3 σ → Prop where
  | ok : Pre → Guarded Pre eff (.ok eff)
  | reject : ¬ Pre → Guarded Pre eff .reject

theorem Guarded.det {σ : Type} {Pre : Prop} {eff : σ} {o₁ o₂ : Outcome3 σ}
    (h₁ : Guarded Pre eff o₁) (h₂ : Guarded Pre eff o₂) : o₁ = o₂ := by
  cases h₁ <;> cases h₂ <;> first | rfl | contradiction

theorem Guarded.ok_iff {σ : Type} {Pre : Prop} {eff s' : σ} :
    Guarded Pre eff (.ok s') ↔ Pre ∧ s' = eff :=
  ⟨fun h => by cases h; exact ⟨‹_›, rfl⟩, fun ⟨h, e⟩ => e ▸ .ok h⟩

theorem Guarded.reject_iff {σ : Type} {Pre : Prop} {eff : σ} :
    Guarded Pre eff .reject ↔ ¬ Pre :=
  ⟨fun h => by cases h; assumption, fun h => .reject h⟩

/-! ## O1 `derive` (MM-03.3 §3) -/

/-- Effect of `derive(source, place, mode)` (MM-03.3 §3, O1): a new active authority with
origin `src`, footprint `footprint place`, mode `m`, held by the current frame. -/
def deriveEff (s : S3) (src q : Nat) (m : Mode) : S3 :=
  s.addAuth ⟨m, some src, footprint s.P q, .frame s.top, true⟩

/-- O1.4 (MM-03.3 §3): every existing authority stays compatible with the derived one in the
resulting state. Not a precondition of `derive`: it follows from O1.1 and O1.3 under I1
(`derive_compat_redundant`, A11). -/
def DeriveCompat (s : S3) (src q : Nat) (m : Mode) : Prop :=
  ∀ b ∈ List.range s.A.length, ∀ p ∈ footprint s.P q,
    OptP (effective (deriveEff s src q m) b p) (fun e => Compat e m) True

/-- Preconditions of `derive` (MM-03.3 §3, O1), in order: 1 active origin, exercisable (A2);
place still usable (MM-03.3.1); 2 requested footprint within the origin's; 3 mode permitted by
the effective authority of the origin on each leaf. O1.4 is removed (A11): it follows from the
others under I1 (`derive_compat_redundant`). O1.5 is not restated: `derive` deactivates
nothing. -/
def DerivePre (s : S3) (src q : Nat) (m : Mode) : Prop :=
  s.Active src ∧ s.Exercisable src ∧ s.Usable q ∧
  (∀ p ∈ footprint s.P q, p ∈ s.afp src) ∧
  (∀ p ∈ footprint s.P q, Allows (effective s src p) m)

instance (s : S3) (src q : Nat) (m : Mode) : Decidable (DerivePre s src q m) := by
  unfold DerivePre; infer_instance

/-- `derive` as a relation (MM-03.3 §3, O1). -/
def DeriveStep (src q : Nat) (m : Mode) (s : S3) : Outcome3 S3 → Prop :=
  Guarded (DerivePre s src q m) (deriveEff s src q m)

/-! ## O2 `split` (MM-03.3 §3) -/

/-- Effect of `split(source, regions)` (MM-03.3 §3, O2): one derived `Modify` authority per
region, held by the current frame; the origin remains a logical authority. -/
def splitEff (s : S3) (src : Nat) (rs : List (List Nat)) : S3 :=
  { s with A := s.A ++ rs.map fun r => ⟨.modify, some src, r, .frame s.top, true⟩ }

/-- Exclusive right already distributed by `src` on leaf `p`: an active descendant of `src` in
mode `Modify` covering `p` (MM-03.3 §3, O2.4). -/
def DistribExcl (s : S3) (src j p : Nat) : Prop :=
  OptP (s.A[j]?) (fun y => y.active = true ∧ src ∈ s.ancs j ∧ p ∈ y.footprint ∧ y.mode = .modify)
    False

instance (s : S3) (src j p : Nat) : Decidable (DistribExcl s src j p) := by
  unfold DistribExcl; infer_instance

/-- Preconditions of `split` (MM-03.3 §3, O2), in order: 1 the origin is an active, exercisable
(A2) authority with effective `Modify` on every leaf of the regions; 2 regions within the available footprint
(the origin's footprint where its effective authority is present); 3 regions pairwise disjoint,
structurally (no shared leaf) or by `DeclaredDisjoint` (MM-03.3.8); 4 no region covers an
exclusive right already distributed. O2.5 is not restated: `split` changes neither `D` nor
activity. -/
def SplitPre (k : K) (s : S3) (src : Nat) (rs : List (List Nat)) : Prop :=
  s.Active src ∧ s.Exercisable src ∧ (∀ r ∈ rs, ∀ p ∈ r, effective s src p = some .modify) ∧
  (∀ r ∈ rs, ∀ p ∈ r, p ∈ s.afp src ∧ effective s src p ≠ none) ∧
  rs.Pairwise (fun r r' => (∀ l ∈ r, l ∉ r') ∨ k.DeclaredDisjoint r r') ∧
  (∀ r ∈ rs, ∀ p ∈ r, ∀ j ∈ List.range s.A.length, ¬ DistribExcl s src j p)

instance (k : K) [∀ r r', Decidable (k.DeclaredDisjoint r r')] (s : S3) (src : Nat)
    (rs : List (List Nat)) : Decidable (SplitPre k s src rs) := by
  unfold SplitPre; infer_instance

/-- `split` as a relation (MM-03.3 §3, O2). -/
def SplitStep (k : K) (src : Nat) (rs : List (List Nat)) (s : S3) : Outcome3 S3 → Prop :=
  Guarded (SplitPre k s src rs) (splitEff s src rs)

/-! ## O3 `release` (MM-03.3 §3, A6) -/

/-- Effect of `release(authority)` (MM-03.3 §3, O3; A6: end of a temporary access): the
authority becomes inactive. -/
def releaseEff (s : S3) (a : Nat) : S3 := match s.A[a]? with
  | some x => { s with A := s.A.set a { x with active := false } }
  | none => s

/-- Preconditions of `release` (MM-03.3 §3, O3), in order: 1 active authority; 2 no active
descendant; 3 no usable place has `a` as anchor. O3.4 (guarantees of associated abstractions)
is not represented in the kernel. -/
def ReleasePre (s : S3) (a : Nat) : Prop :=
  s.Active a ∧
  (∀ j ∈ List.range s.A.length, a ∈ s.ancs j → ¬ s.Active j) ∧
  (∀ q ∈ List.range s.P.length, s.Usable q → a ∉ s.D q)

instance (s : S3) (a : Nat) : Decidable (ReleasePre s a) := by unfold ReleasePre; infer_instance

/-- `release` as a relation (MM-03.3 §3, O3). -/
def ReleaseStep (a : Nat) (s : S3) : Outcome3 S3 → Prop :=
  Guarded (ReleasePre s a) (releaseEff s a)

/-! ## O4 `transfer` (MM-03.3 §3, A4, A5) -/

/-- Holder within the value at `q` (A4): a place that is `q` or one of its parts. -/
def heldIn (P : List Place) (q : Nat) : Holder → Prop
  | .place r => partOf P r q
  | .frame _ => False

instance (P : List Place) (q : Nat) (h : Holder) : Decidable (heldIn P q h) := by
  cases h <;> unfold heldIn <;> infer_instance

/-- Effect of `transfer(source, destination)` (MM-03.3 §3, O4; A4; A5): the destination becomes
`Init`, the source `Moved`; the anchors of the source, inherited ones included, join those of
the destination and leave the source and its parts; every authority held by the source or one
of its parts is now held by the destination (A4); every place owned by the source or one of its
parts is now owned by the destination, without moving (A5). -/
def transferEff (s : S3) (src dst : Nat) : S3 :=
  { s with
    P := s.P.map fun pl => if heldIn s.P src pl.owner then { pl with owner := .place dst } else pl
    I := fun l => if l ∈ footprint s.P dst then .init
      else if l ∈ footprint s.P src then .moved else s.I l
    D := fun q => if q = dst then s.D dst ++ depsOf s src
      else if partOf s.P q src then [] else s.D q
    A := s.A.map fun y => if heldIn s.P src y.holder then { y with holder := .place dst } else y }

/-- Active derived access covering a leaf of the source and not moved with it
(MM-03.3 §3, O4.4; A4). -/
def ActiveDerivedOutside (s : S3) (src j : Nat) : Prop :=
  OptP (s.A[j]?) (fun y => y.active = true ∧ y.origin ≠ none ∧ ¬ heldIn s.P src y.holder ∧
    ∃ l ∈ y.footprint, l ∈ footprint s.P src) False

instance (s : S3) (src j : Nat) : Decidable (ActiveDerivedOutside s src j) := by
  unfold ActiveDerivedOutside; infer_instance

/-- Preconditions of `transfer` (MM-03.3 §3, O4), in order: source usable (MM-03.3.1) and
1 initialised; 2 destination usable, without an `Init` leaf, sharing no leaf with the source,
and still usable once it owns the source's storage (no ownership cycle); exercisable `Modify`
on the source and on the destination (A2); 4 no active derived
access on the source other than those it holds; 5 anchors of the value valid; 6 non-escape
(MM-03.3.6) towards the destination's frame; 7 no leaf of the source pinned, statically
(`Pinned`, MM-03.3.8) or dynamically (A8). O4.3 holds by construction. -/
def TransferPre (k : K) (s : S3) (src dst : Nat) : Prop :=
  s.Usable src ∧ (∀ l ∈ footprint s.P src, s.I l = .init) ∧
  s.Usable dst ∧ (∀ l ∈ footprint s.P dst, s.I l ≠ .init) ∧ ¬ overlap s.P src dst ∧
  HasRight s .modify src ∧ HasRight s .modify dst ∧
  (transferEff s src dst).Usable dst ∧
  (∀ j ∈ List.range s.A.length, ¬ ActiveDerivedOutside s src j) ∧
  (∀ x ∈ depsOf s src, s.Active x) ∧
  (∀ x ∈ depsOf s src, NoEscape s x (s.pframe dst)) ∧
  (∀ l ∈ footprint s.P src, ¬ k.Pinned l ∧ s.pin l = false)

instance (k : K) [DecidablePred k.Pinned] (s : S3) (src dst : Nat) :
    Decidable (TransferPre k s src dst) := by
  unfold TransferPre; infer_instance

/-- `transfer` as a relation (MM-03.3 §3, O4). -/
def TransferStep (k : K) (src dst : Nat) (s : S3) : Outcome3 S3 → Prop :=
  Guarded (TransferPre k s src dst) (transferEff s src dst)

/-! ## O5 `depend` (MM-03.3 §3) -/

/-- Effect of `depend(result, anchor)` (MM-03.3 §3, O5): the anchor joins the dependencies of
the result place; existing dependencies are kept; propagation to containing values is computed
by `depsOf`. -/
def dependEff (s : S3) (q x : Nat) : S3 :=
  { s with D := fun r => if r = q then s.D q ++ [x] else s.D r }

/-- Preconditions of `depend` (MM-03.3 §3, O5), in order: result place usable (MM-03.3.1);
1 valid anchor; 5 non-escape (MM-03.3.6). O5.2 (real origin of the rights or storage) is not
representable: the state does not relate a value to the origin of its content. O5.3 and O5.4
hold by construction. -/
def DependPre (s : S3) (q x : Nat) : Prop :=
  s.Usable q ∧ s.Active x ∧ NoEscape s x (s.pframe q)

instance (s : S3) (q x : Nat) : Decidable (DependPre s q x) := by
  unfold DependPre; infer_instance

/-- `depend` as a relation (MM-03.3 §3, O5). -/
def DependStep (q x : Nat) (s : S3) : Outcome3 S3 → Prop :=
  Guarded (DependPre s q x) (dependEff s q x)

/-! ## O6 `enterFrame` (MM-03.3 §4, A5) -/

/-- Owner of the local of index `i` of `ls` (parent, owning local, kind) in the new frame `f`:
the owning local if any, the new frame otherwise (A5). -/
def localOwner (ls : List (Option Nat × Option Nat × Nat)) (f i : Nat) : Holder :=
  match (ls[i]?).bind (·.2.1) with
  | some o => .place o
  | none => .frame f

/-- Places after `enterFrame`: the locals `ls` appended, owned by the new frame `nF` or by an
earlier local (A5). -/
def enterP (s : S3) (ls : List (Option Nat × Option Nat × Nat)) : List Place :=
  s.P ++ (List.range ls.length).map fun i =>
    ⟨(ls[i]?).bind (·.1), localOwner ls s.nF i, ((ls[i]?).map (·.2.2)).getD 0⟩

/-- Indices, relative to `ls`, of the root locals (no parent). -/
def rootIdx (ls : List (Option Nat × Option Nat × Nat)) : List Nat :=
  (List.range ls.length).filter fun i => ((ls[i]?).bind (·.1)).isNone

/-- Effect of `enterFrame` (MM-03.3 §4, O6) with parameters `ps` and locals `ls`: new frame
`nF` pushed; the parameters, derived by the caller, are now held by the new frame (A3); locals
appended, uninitialised, without dependency, alive and unpinned; one active root `Modify`
authority per root local on its footprint, held by the owner of the local (pass-1
arbitrage 2; A4). -/
def enterEff (s : S3) (ps : List Nat) (ls : List (Option Nat × Option Nat × Nat)) : S3 :=
  { F := s.nF :: s.F, nF := s.nF + 1, P := enterP s ls
    I := fun l => if s.P.length ≤ l then .uninit else s.I l
    A := mapI (fun j y => if j ∈ ps then { y with holder := .frame s.nF } else y) 0 s.A ++
      (rootIdx ls).map fun i =>
      ⟨.modify, none, footprint (enterP s ls) (s.P.length + i), localOwner ls s.nF i, true⟩
    D := fun q => if s.P.length ≤ q then [] else s.D q
    dead := fun q => if s.P.length ≤ q then false else s.dead q
    freed := fun q => if s.P.length ≤ q then false else s.freed q
    pin := fun q => if s.P.length ≤ q then false else s.pin q }

/-- Preconditions of `enterFrame` (MM-03.3 §4, O6): the calling frame is active (non-empty
stack); each parameter is an active authority derived by the caller and held by it (A3); the
parent and the owner of a local are earlier locals; a part has the owner of its
parent. -/
def EnterPre (s : S3) (ps : List Nat) (ls : List (Option Nat × Option Nat × Nat)) : Prop :=
  s.F ≠ [] ∧
  (∀ a ∈ ps, OptP (s.A[a]?) (fun y => y.active = true ∧ y.holder = .frame s.top ∧
    y.origin ≠ none) False) ∧
  ∀ i ∈ List.range ls.length,
    OptP ((ls[i]?).bind (·.1)) (fun r => s.P.length ≤ r ∧ r < s.P.length + i ∧
      (ls[i]?).bind (·.2.1) = (ls[r - s.P.length]?).bind (·.2.1)) True ∧
    OptP ((ls[i]?).bind (·.2.1)) (fun o => s.P.length ≤ o ∧ o < s.P.length + i) True

instance (s : S3) (ps : List Nat) (ls : List (Option Nat × Option Nat × Nat)) :
    Decidable (EnterPre s ps ls) := by
  unfold EnterPre; infer_instance

/-- `enterFrame` as a relation (MM-03.3 §4, O6; A3). -/
def EnterStep (ps : List Nat) (ls : List (Option Nat × Option Nat × Nat)) (s : S3) :
    Outcome3 S3 → Prop :=
  Guarded (EnterPre s ps ls) (enterEff s ps ls)

/-! ## O7 `exitFrame` (MM-03.3 §4, A4, A5, A7) -/

/-- Authority `x` survives the exit to stack `F₀`: active, and held by a holder still live once
the frame is popped, through transitive ownership (A4, A5). A7 speaks of an authority held by
a surviving frame; an authority held by a place is read as held by the frame that ends its
owner chain. -/
def Survives (s : S3) (F₀ : Frames) (x : Nat) : Prop :=
  OptP (s.A[x]?) (fun y => y.active = true ∧ HolderLive { s with F := F₀ } y.holder) False

instance (s : S3) (F₀ : Frames) (x : Nat) : Decidable (Survives s F₀ x) := by
  unfold Survives; infer_instance

/-- First surviving authority of a list (A7). -/
def firstSurv (s : S3) (F₀ : Frames) (l : List Nat) : Option Nat :=
  l.find? fun z => decide (Survives s F₀ z)

/-- Authority `a` after the exit (MM-03.3 §4, O7; A7): released unless it survives; a surviving
authority is re-attached to its first surviving strict ancestor along `origin`, which is its
origin when that origin survives. -/
def exitG (s : S3) (F₀ : Frames) (a : Nat) (y : Authority) : Authority :=
  if Survives s F₀ a then
    match y.origin with
    | none => y
    | some _ => { y with origin := firstSurv s F₀ (s.ancs a) }
  else { y with active := false }

/-- Preconditions of `exitFrame` (MM-03.3 §4, O7; A7): the exiting frame has a caller; every
anchor of a place still usable after the exit has a surviving authority among itself and its
ancestors along `origin`; every surviving derived authority has a surviving strict ancestor.
Otherwise the chain reaches a root that does not survive, and the exit is rejected. -/
def ExitPre (s : S3) : Prop :=
  match s.F with
  | _ :: F₀ => F₀ ≠ [] ∧
      (∀ q ∈ List.range s.P.length, ({ s with F := F₀ } : S3).Usable q →
        ∀ x ∈ s.D q, firstSurv s F₀ (x :: s.ancs x) ≠ none) ∧
      (∀ a ∈ List.range s.A.length, Survives s F₀ a → s.org a ≠ none →
        firstSurv s F₀ (s.ancs a) ≠ none)
  | [] => False

instance (s : S3) : Decidable (ExitPre s) := by
  unfold ExitPre; split <;> infer_instance

/-- Effect of `exitFrame` (MM-03.3 §4, O7; A4; A5; A7): return to the caller; each anchor
replaced by the first surviving authority among itself and its ancestors; authorities that do
not survive released; surviving derived authorities re-attached. -/
def exitEff (s : S3) : S3 :=
  match s.F with
  | _ :: F₀ =>
    { s with
      F := F₀
      D := fun q => (s.D q).map fun x => (firstSurv s F₀ (x :: s.ancs x)).getD x
      A := mapI (exitG s F₀) 0 s.A }
  | [] => s

/-- `exitFrame` as a relation (MM-03.3 §4, O7). -/
def ExitStep (s : S3) : Outcome3 S3 → Prop := Guarded (ExitPre s) (exitEff s)

/-! ## Abstract reads and writes (MM-03.3 §5) -/

/-- Ordinary read condition of a leaf by authority `a` (MM-03.3 §5, `canRead3`): an effective
authority permits observation, the leaf is initialised, the needed dependencies are valid. The
type and storage contract is not represented. -/
def CanReadLeaf (s : S3) (a p : Nat) : Prop :=
  effective s a p ≠ none ∧ s.I p = .init ∧ DepsValid s p

instance (s : S3) (a p : Nat) : Decidable (CanReadLeaf s a p) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- `canRead3` (MM-03.3 §5): ordinary read of leaves `ls` by authority `a`, exercisable by the
current frame (A2). -/
def canRead3 (s : S3) (a : Nat) (ls : List Nat) : Prop :=
  s.Exercisable a ∧ ∀ p ∈ ls, CanReadLeaf s a p

instance (s : S3) (a : Nat) (ls : List Nat) : Decidable (canRead3 s a ls) := by
  unfold canRead3; infer_instance

/-- `read3` as a relation (MM-03.3 §5): a read does not change the state. -/
def Read3Step (a : Nat) (ls : List Nat) (s : S3) : Outcome3 S3 → Prop :=
  Guarded (canRead3 s a ls) s

/-- `canWrite3` (MM-03.3 §5): `a` exercisable by the current frame (A2); on each leaf, effective
`Modify` of `a` and needed dependencies valid. The clause "no other ordinary authority with an
incompatible effective right" is removed (A11): it follows from the first under I1
(`canWrite3_excl_redundant`). The type and storage condition is not represented. -/
def canWrite3 (s : S3) (a : Nat) (ls : List Nat) : Prop :=
  s.Exercisable a ∧ ∀ p ∈ ls, effective s a p = some .modify ∧ DepsValid s p

instance (s : S3) (a : Nat) (ls : List Nat) : Decidable (canWrite3 s a ls) := by
  unfold canWrite3; infer_instance

/-- Effect of a write (MM-03.3 §5): written leaves become `Init`. -/
def write3Eff (s : S3) (ls : List Nat) : S3 := { s with I := fun p => if p ∈ ls then .init else s.I p }

/-- `write3` as a relation (MM-03.3 §5). -/
def Write3Step (a : Nat) (ls : List Nat) (s : S3) : Outcome3 S3 → Prop :=
  Guarded (canWrite3 s a ls) (write3Eff s ls)

/-! ## Lemmas on the effective authority (MM-03.3.5) -/

theorem effOf_cases {m m' : Mode} {ds : List Mode} (h : effOf m ds = some m') :
    (ds = [] ∧ m' = m) ∨ (ds ≠ [] ∧ Mode.modify ∉ ds ∧ m' = .observe) := by
  unfold effOf at h
  by_cases h0 : ds = []
  · simp [h0] at h; exact .inl ⟨h0, h.symm⟩
  · by_cases h1 : Mode.modify ∈ ds
    · simp [h0, h1] at h
    · simp [h0, h1] at h; exact .inr ⟨h0, h1, h.symm⟩

theorem mode_eq_observe {m : Mode} (h : m ≠ .modify) : m = .observe := by cases m <;> simp_all

theorem mem_descModes {s : S3} {a p : Nat} {m : Mode} :
    m ∈ descModes s a p ↔ ∃ j y, s.A[j]? = some y ∧ y.active = true ∧ p ∈ y.footprint ∧
      a ∈ s.ancs j ∧ y.mode = m := by
  simp only [descModes, List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨j, -, h⟩
    split at h
    · rename_i y hy
      split at h
      · rename_i hc; cases h; exact ⟨j, y, hy, hc.1, hc.2.1, hc.2.2, rfl⟩
      · cases h
    · cases h
  · rintro ⟨j, y, hy, h1, h2, h3, rfl⟩
    refine ⟨j, (List.getElem?_eq_some_iff.1 hy).1, ?_⟩
    simp [hy, h1, h2, h3]

theorem effective_some {s : S3} {a p : Nat} {m : Mode} (h : effective s a p = some m) :
    ∃ x, s.A[a]? = some x ∧ x.active = true ∧ p ∈ x.footprint ∧
      effOf x.mode (descModes s a p) = some m := by
  unfold effective at h
  split at h
  · rename_i x hx; split at h
    · rename_i hc; exact ⟨x, hx, hc.1, hc.2, h⟩
    · cases h
  · cases h

theorem effective_eq {s : S3} {a p : Nat} {x : Authority} (hx : s.A[a]? = some x)
    (ha : x.active = true) (hp : p ∈ x.footprint) :
    effective s a p = effOf x.mode (descModes s a p) := by
  simp [effective, hx, ha, hp]

theorem Mode.le_refl (m : Mode) : m.le m := by cases m <;> simp [Mode.le]

/-- The effective mode does not exceed the mode of the authority (MM-03.3.5). -/
theorem effective_le {s : S3} {a p : Nat} {m : Mode} {x : Authority} (hx : s.A[a]? = some x)
    (h : effective s a p = some m) : m.le x.mode := by
  obtain ⟨x', hx', -, -, he⟩ := effective_some h
  rw [hx] at hx'; cases hx'
  rcases effOf_cases he with ⟨-, rfl⟩ | ⟨-, -, rfl⟩
  · exact Mode.le_refl _
  · simp [Mode.le]


theorem Mode.le_trans {a b c : Mode} (h₁ : a.le b) (h₂ : b.le c) : a.le c := by
  cases a <;> cases b <;> cases c <;> simp_all [Mode.le]

theorem Mode.le_observe {m : Mode} (h : m.le .observe) : m = .observe := by
  cases m <;> simp_all [Mode.le]

/-- The mode permitted by a present effective mode does not exceed it. -/
theorem allows_effOf {m m' : Mode} {ds : List Mode} (h : Allows (effOf m ds) m') :
    (ds = [] ∧ m'.le m) ∨ (Mode.modify ∉ ds ∧ m' = .observe) := by
  unfold Allows OptP at h
  split at h
  · rename_i e he
    rcases effOf_cases he with ⟨h0, rfl⟩ | ⟨-, hn, rfl⟩
    · exact .inl ⟨h0, h⟩
    · exact .inr ⟨hn, Mode.le_observe h⟩
  · exact h.elim

/-! ## Invariants (MM-03.3 §2, A1) -/

/-- I1, effective exclusivity strengthened structurally (MM-03.3 §2, A1): two distinct active
authorities, unrelated by `origin`, covering the same leaf, `SharedMutable` leaves included,
both have the proper mode `Observe`. The pass-1 statement on effective modes is the theorem
`effective_compat`. -/
def I1 (s : S3) : Prop :=
  ∀ (a b : Nat) (x y : Authority) (p : Nat), a ≠ b → s.A[a]? = some x → s.A[b]? = some y →
    x.active = true → y.active = true → p ∈ x.footprint → p ∈ y.footprint →
    a ∉ s.ancs b → b ∉ s.ancs a → x.mode = .observe ∧ y.mode = .observe

/-- I2, conservation of authorities (MM-03.3 §2): the origin of a derived authority exists, and
on each leaf of the derived footprint, the leaf is in the footprint of the origin and the
derived mode does not exceed the origin's. -/
def I2 (s : S3) : Prop :=
  ∀ (b : Nat) (y : Authority) (a : Nat), s.A[b]? = some y → y.origin = some a →
    ∃ x : Authority, s.A[a]? = some x ∧ ∀ p ∈ y.footprint, p ∈ x.footprint ∧ y.mode.le x.mode

/-- I3, validity of dependencies (MM-03.3 §2): every anchor of a usable place is valid, that is,
active (pass-1 arbitrage 2). -/
def I3 (s : S3) : Prop := ∀ q, s.Usable q → ∀ x ∈ s.D q, s.Active x

/-- I4, validity of consumed values (MM-03.3 §2), first sentence as a state predicate: no
`Moved` leaf is readable. The other sentences concern `transfer` and are theorems. -/
def I4 (s : S3) : Prop := ∀ a p, s.I p = .moved → ¬ CanReadLeaf s a p

/-- `Inv3 = I1 ∧ I2 ∧ I3 ∧ I4` (MM-03.3 §2): the safety invariant. -/
def Inv3 (s : S3) : Prop := I1 s ∧ I2 s ∧ I3 s ∧ I4 s

/-- I4 holds in every state: the read condition requires `Init` (MM-03.3 §2, I4; §5). -/
theorem i4_always (s : S3) : I4 s := fun _ _ hm h => by rw [h.2.1] at hm; cases hm

/-- `WF3` (A1): well-formedness, the domain of admissible states, separate from the safety
invariant `Inv3`. Origins precede their derivations; footprints are made of existing places;
the stack is non-empty and without duplicates, below `nF`; owner frames are below `nF`; owner
places exist; a part comes after its parent and has its owner and its `dead` flag; every active
authority has a live holder (possession). -/
def WF3 (s : S3) : Prop :=
  (∀ (b : Nat) (y : Authority) (a : Nat), s.A[b]? = some y → y.origin = some a → a < b) ∧
  (∀ (a : Nat) (x : Authority), s.A[a]? = some x → ∀ l ∈ x.footprint, l < s.P.length) ∧
  s.F ≠ [] ∧ s.F.Nodup ∧ (∀ f ∈ s.F, f < s.nF) ∧
  (∀ (q : Nat) (pl : Place) (f : Nat), s.P[q]? = some pl → pl.owner = .frame f → f < s.nF) ∧
  (∀ (q : Nat) (pl : Place) (o : Nat), s.P[q]? = some pl → pl.owner = .place o →
    o < s.P.length) ∧
  (∀ (q : Nat) (pl : Place) (r : Nat), s.P[q]? = some pl → pl.parent = some r →
    ∃ pr : Place, s.P[r]? = some pr ∧ r < q ∧ pr.owner = pl.owner ∧ s.dead r = s.dead q) ∧
  (∀ (a : Nat) (y : Authority), s.A[a]? = some y → y.active = true → HolderLive s y.holder)

/-- The pass-1 exclusivity on effective modes (MM-03.3 §2, I1) is a theorem under the
strengthened I1 (A1). -/
theorem effective_compat {s : S3} (h : I1 s) :
    ∀ a b p m₁ m₂, a ≠ b → effective s a p = some m₁ → effective s b p = some m₂ →
      Compat m₁ m₂ := by
  intro a b p m₁ m₂ hab ha hb
  obtain ⟨x, hx, xa, xp, ex⟩ := effective_some ha
  obtain ⟨y, hy, ya, yp, ey⟩ := effective_some hb
  have obs₁ : x.mode = .observe → m₁ = .observe := fun hm => by
    rcases effOf_cases ex with ⟨-, rfl⟩ | ⟨-, -, rfl⟩ <;> simp [hm]
  have obs₂ : y.mode = .observe → m₂ = .observe := fun hm => by
    rcases effOf_cases ey with ⟨-, rfl⟩ | ⟨-, -, rfl⟩ <;> simp [hm]
  by_cases hba : b ∈ s.ancs a
  · have hm : x.mode ∈ descModes s b p := mem_descModes.2 ⟨a, x, hx, xa, xp, hba, rfl⟩
    rcases effOf_cases ey with ⟨h0, -⟩ | ⟨-, hn, rfl⟩
    · simp [h0] at hm
    · have : x.mode = .observe := mode_eq_observe fun e => hn (e ▸ hm)
      exact ⟨obs₁ this, rfl⟩
  by_cases hab' : a ∈ s.ancs b
  · have hm : y.mode ∈ descModes s a p := mem_descModes.2 ⟨b, y, hy, ya, yp, hab', rfl⟩
    rcases effOf_cases ex with ⟨h0, -⟩ | ⟨-, hn, rfl⟩
    · simp [h0] at hm
    · have : y.mode = .observe := mode_eq_observe fun e => hn (e ▸ hm)
      exact ⟨rfl, obs₂ this⟩
  obtain ⟨h₁, h₂⟩ := h a b x y p hab hx hy xa ya xp yp hab' hba
  exact ⟨obs₁ h₁, obs₂ h₂⟩

/-- `effective_exclusive` (MM-03.3 §10): under I1, an authority with effective `Modify` on a leaf
is the only one with a present effective mode there. -/
theorem effective_exclusive {s : S3} (h : I1 s) {a b p : Nat} (hab : a ≠ b)
    (ha : effective s a p = some .modify) : effective s b p = none := by
  cases hb : effective s b p with
  | none => rfl
  | some m => exact absurd (effective_compat h a b p _ _ hab ha hb).1 (by simp)

/-- `shared_keeps_exclusivity` (A9): I1 holds on `SharedMutable` leaves like on any other leaf:
two unrelated active authorities covering such a leaf are both in `Observe`. -/
theorem shared_keeps_exclusivity {k : K} {s : S3} (h : I1 s) {a b : Nat} {x y : Authority}
    {p : Nat} (_hsh : k.SharedMutable p) (hab : a ≠ b) (hx : s.A[a]? = some x)
    (hy : s.A[b]? = some y) (xa : x.active = true) (ya : y.active = true)
    (xp : p ∈ x.footprint) (yp : p ∈ y.footprint) (hnab : a ∉ s.ancs b) (hnba : b ∉ s.ancs a) :
    x.mode = .observe ∧ y.mode = .observe :=
  h a b x y p hab hx hy xa ya xp yp hnab hnba

/-- Central theorem (MM-03.3 §5): in a state satisfying `Inv3`, an authorised ordinary write
coexists with no other authority with a present effective mode on the written leaves. The proof
uses only the effective `Modify` of the writer. -/
theorem write3_exclusive {s s' : S3} {a : Nat} {ls : List Nat} (hinv : Inv3 s)
    (h : Write3Step a ls s (.ok s')) : ∀ p ∈ ls, ∀ b, b ≠ a → effective s b p = none := by
  intro p hp b hb
  obtain ⟨⟨-, hw⟩, -⟩ := Guarded.ok_iff.1 h
  exact effective_exclusive hinv.1 (Ne.symm hb) (hw p hp).1

/-! ## Reused lemmas on chains, additions and skeletons -/

theorem nil_of_forall_not_mem {α : Type} : ∀ {l : List α}, (∀ a, a ∉ l) → l = []
  | [], _ => rfl
  | a :: _, h => absurd (List.mem_cons_self ..) (h a)

theorem pairwise_lt_range : ∀ n, (List.range n).Pairwise (· < ·)
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.pairwise_append]
    exact ⟨pairwise_lt_range n, by simp, fun a ha b hb => by
      simp at hb; subst hb; exact List.mem_range.1 ha⟩

theorem filterMap_congr' {α β : Type} {f g : α → Option β} :
    ∀ {l : List α}, (∀ a ∈ l, f a = g a) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.filterMap_cons, h a (List.mem_cons_self ..),
      filterMap_congr' fun b hb => h b (List.mem_cons_of_mem a hb)]

theorem addAuth_get {s : S3} {y₀ z : Authority} {j : Nat} (h : (s.addAuth y₀).A[j]? = some z) :
    (j < s.A.length ∧ s.A[j]? = some z) ∨ (j = s.A.length ∧ z = y₀) := by
  simp only [S3.addAuth] at h
  by_cases hj : j < s.A.length
  · exact .inl ⟨hj, by rwa [List.getElem?_append_left hj] at h⟩
  · rw [List.getElem?_append_right (by omega)] at h
    have : j - s.A.length = 0 := by
      have := lt_of_getElem? h; simp at this; omega
    rw [this] at h; simp at h
    exact .inr ⟨by have := lt_of_getElem? (l := s.A ++ [y₀]) (i := j) (x := z) (by
      rw [List.getElem?_append_right (by omega), this]; simp [h]); simp at this; omega, h.symm⟩

theorem addAuth_lt {s : S3} {y₀ : Authority} {j : Nat} (h : j < s.A.length) :
    (s.addAuth y₀).A[j]? = s.A[j]? := List.getElem?_append_left h

theorem addAuth_self (s : S3) (y₀ : Authority) : (s.addAuth y₀).A[s.A.length]? = some y₀ := by
  simp [S3.addAuth]

theorem ancs_addAuth_lt {s : S3} {y₀ : Authority} {j : Nat} (h : j < s.A.length) :
    (s.addAuth y₀).ancs j = s.ancs j :=
  chain_congr fun i hi => by simp only [S3.org, addAuth_lt (Nat.lt_of_le_of_lt hi h)]

theorem ancs_addAuth_self {s : S3} {y₀ : Authority} {src : Nat} (ho : y₀.origin = some src)
    (hs : src < s.A.length) : (s.addAuth y₀).ancs s.A.length = src :: s.ancs src := by
  unfold S3.ancs
  rw [chain_cons (by simp [S3.org, addAuth_self, ho]) hs]
  exact congrArg _ (ancs_addAuth_lt hs)

theorem active_addAuth {s : S3} {y₀ : Authority} {x : Nat} (h : s.Active x) :
    (s.addAuth y₀).Active x := by
  obtain ⟨y, hy, ha⟩ := h; exact ⟨y, by rw [addAuth_lt (lt_of_getElem? hy)]; exact hy, ha⟩

theorem descModes_addAuth (s : S3) (y₀ : Authority) (a p : Nat) :
    descModes (s.addAuth y₀) a p = descModes s a p ++
      (if y₀.active = true ∧ p ∈ y₀.footprint ∧ a ∈ (s.addAuth y₀).ancs s.A.length
        then [y₀.mode] else []) := by
  have hl : (s.addAuth y₀).A.length = s.A.length + 1 := by simp [S3.addAuth]
  unfold descModes
  rw [hl, List.range_succ, List.filterMap_append]
  congr 1
  · refine filterMap_congr' fun j hj => ?_
    have hj' := List.mem_range.1 hj
    rw [addAuth_lt hj', ancs_addAuth_lt hj']
  · simp only [List.filterMap_cons, List.filterMap_nil, addAuth_self]
    split <;> simp_all

/-- An authority derived from `src` with a mode permitted on `p`, and an active authority
covering `p` unrelated to the new one, are both in observation (MM-03.3 §2, I1). -/
theorem new_vs_old {s : S3} (ht : I1 s) {src b p : Nat} {x y : Authority} {m : Mode}
    (hx : s.A[src]? = some x) (xa : x.active = true) (xp : p ∈ x.footprint)
    (hal : Allows (effective s src p) m) (hy : s.A[b]? = some y) (ya : y.active = true)
    (yp : p ∈ y.footprint) (hbs : b ≠ src) (hbn : b ∉ s.ancs src) :
    m = .observe ∧ y.mode = .observe := by
  rw [effective_eq hx xa xp] at hal
  by_cases hsb : src ∈ s.ancs b
  · have hm : y.mode ∈ descModes s src p := mem_descModes.2 ⟨b, y, hy, ya, yp, hsb, rfl⟩
    rcases allows_effOf hal with ⟨h0, -⟩ | ⟨hn, rfl⟩
    · simp [h0] at hm
    · exact ⟨rfl, mode_eq_observe fun e => hn (e ▸ hm)⟩
  · obtain ⟨h₁, h₂⟩ := ht src b x y p (Ne.symm hbs) hx hy xa ya xp yp hsb hbn
    rcases allows_effOf hal with ⟨-, hl⟩ | ⟨-, rfl⟩
    · exact ⟨Mode.le_observe (h₁ ▸ hl), h₂⟩
    · exact ⟨rfl, h₂⟩

theorem Compat.symm {m₁ m₂ : Mode} (h : Compat m₁ m₂) : Compat m₂ m₁ := ⟨h.2, h.1⟩

/-- Skeleton of an authority: everything but its holder. -/
def skel (z : Authority) : Mode × Option Nat × List Nat × Bool := (z.mode, z.origin, z.footprint, z.active)

/-- `s'` has the same authorities as `s`, up to their holders. -/
def SameSkel (s s' : S3) : Prop :=
  s'.A.length = s.A.length ∧ ∀ j : Nat, (s'.A[j]?).map skel = (s.A[j]?).map skel

theorem SameSkel.get {s s' : S3} (h : SameSkel s s') {j : Nat} {y' : Authority}
    (hj : s'.A[j]? = some y') : ∃ y, s.A[j]? = some y ∧ skel y' = skel y := by
  have := h.2 j; rw [hj] at this
  cases hy : s.A[j]? with
  | none => rw [hy] at this; cases this
  | some y => rw [hy] at this; exact ⟨y, rfl, Option.some.inj this⟩

theorem SameSkel.get' {s s' : S3} (h : SameSkel s s') {j : Nat} {y : Authority}
    (hj : s.A[j]? = some y) : ∃ y', s'.A[j]? = some y' ∧ skel y' = skel y := by
  have := h.2 j; rw [hj] at this
  cases hy : s'.A[j]? with
  | none => rw [hy] at this; cases this
  | some y' => rw [hy] at this; exact ⟨y', rfl, Option.some.inj this⟩

theorem SameSkel.org {s s' : S3} (h : SameSkel s s') : s'.org = s.org := by
  funext j
  cases hy : s.A[j]? with
  | none =>
    cases hy' : s'.A[j]? with
    | none => simp [S3.org, hy, hy']
    | some y' => obtain ⟨y, h1, -⟩ := h.get hy'; rw [hy] at h1; cases h1
  | some y => obtain ⟨y', hy', e⟩ := h.get' hy; simp [skel] at e; simp [S3.org, hy, hy', e.2.1]

theorem SameSkel.ancs {s s' : S3} (h : SameSkel s s') : s'.ancs = s.ancs := by
  funext j; simp [S3.ancs, h.org]

theorem SameSkel.active {s s' : S3} (h : SameSkel s s') {x : Nat} : s'.Active x ↔ s.Active x := by
  constructor
  · rintro ⟨y', hy', ha⟩; obtain ⟨y, hy, he⟩ := h.get hy'
    exact ⟨y, hy, by simp [skel] at he; rw [← he.2.2.2]; exact ha⟩
  · rintro ⟨y, hy, ha⟩; obtain ⟨y', hy', he⟩ := h.get' hy
    exact ⟨y', hy', by simp [skel] at he; rw [he.2.2.2]; exact ha⟩

theorem SameSkel.descModes {s s' : S3} (h : SameSkel s s') (a p : Nat) :
    descModes s' a p = descModes s a p := by
  unfold MM03.descModes; rw [h.1, h.ancs]
  refine filterMap_congr' fun j _ => ?_
  cases hy : s.A[j]? with
  | none => have := h.2 j; rw [hy] at this; cases hy' : s'.A[j]? <;> simp_all
  | some y =>
    obtain ⟨y', hy', he⟩ := h.get' hy
    simp [skel] at he; simp [hy', he]

theorem SameSkel.effective {s s' : S3} (h : SameSkel s s') (a p : Nat) :
    effective s' a p = effective s a p := by
  unfold MM03.effective; rw [h.descModes]
  cases hy : s.A[a]? with
  | none => have := h.2 a; rw [hy] at this; cases hy' : s'.A[a]? <;> simp_all
  | some y =>
    obtain ⟨y', hy', he⟩ := h.get' hy
    simp [skel] at he; simp [hy', he]

theorem effective_addAuth_notin {s : S3} {y₀ : Authority} {a p : Nat} (ha : a < s.A.length)
    (hp : p ∉ y₀.footprint) : effective (s.addAuth y₀) a p = effective s a p := by
  unfold effective; rw [addAuth_lt ha, descModes_addAuth]; simp [hp]

theorem splitEff_cons (s : S3) (src : Nat) (r : List Nat) (rs : List (List Nat)) :
    splitEff s src (r :: rs) =
      splitEff (s.addAuth ⟨.modify, some src, r, .frame s.top, true⟩) src rs := by
  simp [splitEff, S3.addAuth, S3.top]


theorem set_get {l : List Authority} {a j : Nat} {x' : Authority} (ha : a < l.length) :
    (l.set a x')[j]? = if a = j then some x' else l[j]? := by
  rw [List.getElem?_set]; split <;> simp_all

theorem releaseEff_eq {s : S3} {a : Nat} {x : Authority} (hx : s.A[a]? = some x) :
    releaseEff s a = { s with A := s.A.set a { x with active := false } } := by
  simp [releaseEff, hx]

theorem release_org {s : S3} {a : Nat} {x : Authority} (hx : s.A[a]? = some x) :
    (releaseEff s a).org = s.org := by
  funext j; rw [releaseEff_eq hx]
  simp only [S3.org, set_get (lt_of_getElem? hx)]
  split
  · subst_vars; simp [hx]
  · rfl

theorem release_ancs {s : S3} {a : Nat} {x : Authority} (hx : s.A[a]? = some x) :
    (releaseEff s a).ancs = s.ancs := by
  funext j; simp only [S3.ancs, release_org hx]



/-! ## Projections of `WF3` -/

section WF3proj
variable {s : S3} (h : WF3 s)
include h

theorem WF3.origin : ∀ (b : Nat) (y : Authority) (a : Nat), s.A[b]? = some y →
    y.origin = some a → a < b := h.1
theorem WF3.fp : ∀ (a : Nat) (x : Authority), s.A[a]? = some x → ∀ l ∈ x.footprint,
    l < s.P.length := h.2.1
theorem WF3.ne : s.F ≠ [] := h.2.2.1
theorem WF3.nodup : s.F.Nodup := h.2.2.2.1
theorem WF3.frames : ∀ f ∈ s.F, f < s.nF := h.2.2.2.2.1
theorem WF3.ownerFrame : ∀ (q : Nat) (pl : Place) (f : Nat), s.P[q]? = some pl →
    pl.owner = .frame f → f < s.nF := h.2.2.2.2.2.1
theorem WF3.ownerPlace : ∀ (q : Nat) (pl : Place) (o : Nat), s.P[q]? = some pl →
    pl.owner = .place o → o < s.P.length := h.2.2.2.2.2.2.1
theorem WF3.parts : ∀ (q : Nat) (pl : Place) (r : Nat), s.P[q]? = some pl → pl.parent = some r →
    ∃ pr : Place, s.P[r]? = some pr ∧ r < q ∧ pr.owner = pl.owner ∧ s.dead r = s.dead q :=
  h.2.2.2.2.2.2.2.1
theorem WF3.poss : ∀ (a : Nat) (y : Authority), s.A[a]? = some y → y.active = true →
    HolderLive s y.holder := h.2.2.2.2.2.2.2.2

end WF3proj

theorem top_mem {s : S3} (h : s.F ≠ []) : s.top ∈ s.F := by
  unfold S3.top; cases hF : s.F with
  | nil => exact absurd hF h
  | cons f F => simp

/-! ## Usability lemmas (A5) -/

/-- Usability depends only on places, stack and `dead` flags; it shrinks with the stack and
grows... never: a smaller stack and more dead places give fewer usable places. -/
theorem S3.Usable.mono {s s' : S3} (hP : s'.P = s.P) (hF : ∀ f ∈ s'.F, f ∈ s.F)
    (hd : ∀ q, s'.dead q = false → s.dead q = false) {q : Nat} (h : s'.Usable q) :
    s.Usable q := by
  induction h with
  | frame hpl hdq ho hf => exact .frame (by rw [← hP]; exact hpl) (hd _ hdq) ho (hF _ hf)
  | place hpl hdq ho _ ih => exact .place (by rw [← hP]; exact hpl) (hd _ hdq) ho ih

theorem S3.Usable.congr {s s' : S3} (hP : s'.P = s.P) (hF : s'.F = s.F) (hd : s'.dead = s.dead)
    {q : Nat} : s'.Usable q ↔ s.Usable q :=
  ⟨S3.Usable.mono hP (fun f h => hF ▸ h) (fun q h => hd ▸ h),
   S3.Usable.mono hP.symm (fun f h => hF ▸ h) (fun q h => by rw [hd]; exact h)⟩

theorem HolderLive.congr {s s' : S3} (hP : s'.P = s.P) (hF : s'.F = s.F) (hd : s'.dead = s.dead)
    (h : Holder) : HolderLive s' h ↔ HolderLive s h := by
  cases h with
  | frame f => simp [HolderLive, hF]
  | place p => exact S3.Usable.congr hP hF hd

/-- A place with the owner and the `dead` flag of a usable place is usable. -/
theorem S3.Usable.of_same {s : S3} {q r : Nat} {pl pr : Place} (h : s.Usable q)
    (hq : s.P[q]? = some pl) (hr : s.P[r]? = some pr) (ho : pr.owner = pl.owner)
    (hd : s.dead r = s.dead q) : s.Usable r := by
  cases h with
  | frame hpl hdq hof hf =>
    rw [hq] at hpl; cases hpl; exact .frame hr (by rw [hd]; exact hdq) (by rw [ho]; exact hof) hf
  | place hpl hdq hof hu =>
    rw [hq] at hpl; cases hpl; exact .place hr (by rw [hd]; exact hdq) (by rw [ho]; exact hof) hu

/-- A part of a usable place is usable (A5, `WF3`). -/
theorem usable_of_partOf {s : S3} (hw : WF3 s) :
    ∀ n r q, r < n → partOf s.P r q → s.Usable q → s.Usable r
  | 0, _, _, h, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, r, q, hr, ⟨hlen, hrq⟩, hu => by
    rcases hrq with rfl | hc
    · exact hu
    cases hpo : parentOf s.P r with
    | none => rw [chain_none hpo] at hc; simp at hc
    | some p =>
      obtain ⟨pl, hpl, hpar⟩ : ∃ pl, s.P[r]? = some pl ∧ pl.parent = some p := by
        simp only [parentOf] at hpo
        cases h' : s.P[r]? with
        | none => rw [h'] at hpo; cases hpo
        | some pl => rw [h'] at hpo; exact ⟨pl, rfl, hpo⟩
      obtain ⟨pr, hpr, hlt, ho, hd⟩ := hw.parts r pl p hpl hpar
      rw [chain_cons hpo hlt] at hc
      have hup : s.Usable p := by
        rcases List.mem_cons.1 hc with rfl | hc
        · exact hu
        · exact usable_of_partOf hw n p q (by omega) ⟨lt_of_getElem? hpr, .inr hc⟩ hu
      exact hup.of_same hpr hpl ho.symm hd.symm

/-! ## Additions of authorities -/

theorem addAuth_P (s : S3) (y : Authority) : (s.addAuth y).P = s.P := rfl
theorem addAuth_F (s : S3) (y : Authority) : (s.addAuth y).F = s.F := rfl
theorem addAuth_dead (s : S3) (y : Authority) : (s.addAuth y).dead = s.dead := rfl

/-- Adding a derived authority whose mode is permitted by the effective authority of its origin
on each leaf of its footprint preserves I1 (MM-03.3 §2, I1, A1; §3, O1.3). -/
theorem addAuth_I1 {s : S3} (ht : I1 s) {src : Nat} {x : Authority} {m : Mode} {fp : List Nat}
    {hd : Holder} (hx : s.A[src]? = some x) (hal : ∀ p ∈ fp, Allows (effective s src p) m) :
    I1 (s.addAuth ⟨m, some src, fp, hd, true⟩) := by
  have hs := lt_of_getElem? hx
  have hxp : ∀ p ∈ fp, x.active = true ∧ p ∈ x.footprint := fun p hp => by
    have := hal p hp; unfold Allows OptP at this; split at this
    · rename_i e he
      obtain ⟨x', hx', xa', xp', -⟩ := effective_some he
      rw [hx] at hx'; cases hx'; exact ⟨xa', xp'⟩
    · exact this.elim
  intro a b x' y' p hab ha hb xa' ya' xp yp hnab hnba
  rcases addAuth_get ha with ⟨ha', ha''⟩ | ⟨rfl, rfl⟩ <;>
    rcases addAuth_get hb with ⟨hb', hb''⟩ | ⟨rfl, rfl⟩
  · rw [ancs_addAuth_lt hb'] at hnab; rw [ancs_addAuth_lt ha'] at hnba
    exact ht a b x' y' p hab ha'' hb'' xa' ya' xp yp hnab hnba
  · rw [ancs_addAuth_self rfl hs] at hnab
    exact (new_vs_old ht hx (hxp p yp).1 (hxp p yp).2 (hal p yp) ha'' xa' xp
      (fun e => hnab (e ▸ List.mem_cons_self ..)) fun e => hnab (List.mem_cons_of_mem _ e)).symm
  · rw [ancs_addAuth_self rfl hs] at hnba
    exact new_vs_old ht hx (hxp p xp).1 (hxp p xp).2 (hal p xp) hb'' ya' yp
      (fun e => hnba (e ▸ List.mem_cons_self ..)) fun e => hnba (List.mem_cons_of_mem _ e)
  · exact absurd rfl hab

/-- Adding an active authority derived from `src`, with a footprint within `src`'s, a mode
permitted on each leaf, and a live holder, preserves `WF3` and `Inv3`. Shared by `derive`,
`split` and `issue`. -/
theorem addAuth_preserves {s : S3} (hwf : WF3 s) (hinv : Inv3 s) {src : Nat} {x : Authority}
    {m : Mode} {fp : List Nat} {hd : Holder} (hx : s.A[src]? = some x)
    (hfp : ∀ p ∈ fp, p ∈ x.footprint) (hal : ∀ p ∈ fp, Allows (effective s src p) m)
    (hl : HolderLive s hd) :
    WF3 (s.addAuth ⟨m, some src, fp, hd, true⟩) ∧ Inv3 (s.addAuth ⟨m, some src, fp, hd, true⟩) := by
  obtain ⟨i1, i2, i3, -⟩ := hinv
  have hs := lt_of_getElem? hx
  have live := HolderLive.congr (addAuth_P s ⟨m, some src, fp, hd, true⟩) rfl rfl
  refine ⟨⟨?_, ?_, hwf.ne, hwf.nodup, hwf.frames, hwf.ownerFrame, hwf.ownerPlace, hwf.parts, ?_⟩,
    addAuth_I1 i1 hx hal, ?_, fun q hq y hy => active_addAuth (i3 q ?_ y hy), i4_always _⟩
  · intro b y a hb ho
    rcases addAuth_get hb with ⟨-, hb''⟩ | ⟨rfl, rfl⟩
    · exact hwf.origin b y a hb'' ho
    · cases ho; exact hs
  · intro a y hy l hl'
    rcases addAuth_get hy with ⟨-, hy'⟩ | ⟨-, rfl⟩
    · exact hwf.fp a y hy' l hl'
    · exact hwf.fp src x hx l (hfp l hl')
  · intro a y hy ya
    rcases addAuth_get hy with ⟨-, hy'⟩ | ⟨-, rfl⟩
    · exact (live _).2 (hwf.poss a y hy' ya)
    · exact (live _).2 hl
  · intro b y a hb ho
    rcases addAuth_get hb with ⟨-, hb''⟩ | ⟨rfl, rfl⟩
    · obtain ⟨x₁, hx₁, h⟩ := i2 b y a hb'' ho
      exact ⟨x₁, by rw [addAuth_lt (lt_of_getElem? hx₁)]; exact hx₁, h⟩
    · cases ho
      refine ⟨x, by rw [addAuth_lt hs]; exact hx, fun p hp => ⟨hfp p hp, ?_⟩⟩
      have := hal p hp; unfold Allows OptP at this; split at this
      · rename_i e he; exact Mode.le_trans this (effective_le hx he)
      · exact this.elim
  · exact (S3.Usable.congr (addAuth_P s _) rfl rfl).1 hq

/-! ## Preservation by `derive`, `split`, `release` (MM-03.3 §3, §10) -/

/-- `derive` preserves `WF3` and `Inv3` (MM-03.3 §3, O1; §10). The proof does not use O1.4. -/
theorem derive_preserves {s s' : S3} {src q : Nat} {m : Mode} (hwf : WF3 s) (hinv : Inv3 s)
    (h : DeriveStep src q m s (.ok s')) : WF3 s' ∧ Inv3 s' := by
  obtain ⟨⟨⟨x, hx, -⟩, -, -, hfp, hal⟩, rfl⟩ := Guarded.ok_iff.1 h
  exact addAuth_preserves hwf hinv hx (fun p hp => by simpa [S3.afp, hx] using hfp p hp) hal
    (top_mem hwf.ne)

/-- `derive_preserves_exclusivity` (MM-03.3 §10): `derive` preserves I1, under I1 alone. -/
theorem derive_preserves_exclusivity {s s' : S3} {src q : Nat} {m : Mode} (h1 : I1 s)
    (h : DeriveStep src q m s (.ok s')) : I1 s' := by
  obtain ⟨⟨⟨x, hx, -⟩, -, -, -, hal⟩, rfl⟩ := Guarded.ok_iff.1 h
  exact addAuth_I1 h1 hx hal

theorem split_aux {src : Nat} {x : Authority} : ∀ (rs : List (List Nat)) (s : S3), WF3 s →
    Inv3 s → s.A[src]? = some x →
    (∀ r ∈ rs, ∀ p ∈ r, effective s src p = some .modify ∧ p ∈ x.footprint) →
    rs.Pairwise (fun r r' => ∀ l ∈ r, l ∉ r') →
    WF3 (splitEff s src rs) ∧ Inv3 (splitEff s src rs)
  | [], s, hwf, hinv, _, _, _ => by
    have : splitEff s src [] = s := by simp [splitEff]
    rw [this]; exact ⟨hwf, hinv⟩
  | r :: rs, s, hwf, hinv, hx, hr, hpw => by
    rw [splitEff_cons]
    have hs := lt_of_getElem? hx
    obtain ⟨hwf₁, hinv₁⟩ := addAuth_preserves (hd := .frame s.top) hwf hinv hx
      (fun p hp => (hr r (List.mem_cons_self ..) p hp).2)
      (fun p hp => by rw [(hr r (List.mem_cons_self ..) p hp).1]; simp [Allows, OptP, Mode.le])
      (top_mem hwf.ne)
    obtain ⟨hpr, hpw⟩ := List.pairwise_cons.1 hpw
    refine split_aux rs _ hwf₁ hinv₁ (by rw [addAuth_lt hs]; exact hx) (fun r' hr' p hp => ?_) hpw
    rw [effective_addAuth_notin hs fun h => hpr r' hr' p h hp]
    exact hr r' (List.mem_cons_of_mem _ hr') p hp

/-- `split` preserves `WF3` and `Inv3` (MM-03.3 §3, O2; §10), under the obligation `DDSound k`
of `DeclaredDisjoint` (MM-03.3.8). -/
theorem split_preserves_underDD {k : K} (hdd : DDSound k) {s s' : S3} {src : Nat}
    {rs : List (List Nat)} (hwf : WF3 s) (hinv : Inv3 s) (h : SplitStep k src rs s (.ok s')) :
    WF3 s' ∧ Inv3 s' := by
  obtain ⟨⟨⟨x, hx, -⟩, -, h1, h2, h3, -⟩, rfl⟩ := Guarded.ok_iff.1 h
  refine split_aux rs s hwf hinv hx (fun r hr p hp => ⟨h1 r hr p hp, ?_⟩)
    (h3.imp fun {r r'} h => h.elim id fun hd => hdd r r' hd)
  simpa [S3.afp, hx] using (h2 r hr p hp).1


/-- `release` preserves `WF3` and `Inv3` (MM-03.3 §3, O3; §10). Under the strengthened I1 (A1),
releasing an authority only shrinks the set of active authorities. -/
theorem release_preserves {s s' : S3} {a : Nat} (hwf : WF3 s) (hinv : Inv3 s)
    (h : ReleaseStep a s (.ok s')) : WF3 s' ∧ Inv3 s' := by
  obtain ⟨⟨⟨x, hx, xa⟩, -, h3⟩, rfl⟩ := Guarded.ok_iff.1 h
  obtain ⟨i1, i2, i3, -⟩ := hinv
  have ha := lt_of_getElem? hx
  have e := releaseEff_eq hx
  have get : ∀ j, (releaseEff s a).A[j]? = if a = j then some { x with active := false }
      else s.A[j]? := fun j => by rw [e]; exact set_get ha
  have back : ∀ j z, (releaseEff s a).A[j]? = some z → ∃ z₀, s.A[j]? = some z₀ ∧
      z.mode = z₀.mode ∧ z.origin = z₀.origin ∧ z.footprint = z₀.footprint ∧
      z.holder = z₀.holder ∧ (z.active = true → z₀.active = true ∧ j ≠ a) := fun j z hz => by
    rw [get] at hz; split at hz
    · subst_vars; cases hz; exact ⟨x, hx, rfl, rfl, rfl, rfl, by simp⟩
    · exact ⟨z, hz, rfl, rfl, rfl, rfl, fun hz' => ⟨hz', Ne.symm ‹_›⟩⟩
  have hP : (releaseEff s a).P = s.P := by rw [e]
  have hF : (releaseEff s a).F = s.F := by rw [e]
  have hd : (releaseEff s a).dead = s.dead := by rw [e]
  have hnF : (releaseEff s a).nF = s.nF := by rw [e]
  refine ⟨⟨fun b y o hb ho => ?_, fun b y hb l hl => ?_, hF ▸ hwf.ne, hF ▸ hwf.nodup,
    hF ▸ hnF ▸ hwf.frames, hP ▸ hnF ▸ hwf.ownerFrame, hP ▸ hwf.ownerPlace, hP ▸ hd ▸ hwf.parts,
    fun b y hb ya => ?_⟩, fun a' b' x' y' p hab ha' hb' xa' ya' xp yp hnab hnba => ?_,
    fun b y o hb ho => ?_, fun q hq y hy => ?_, i4_always _⟩
  · obtain ⟨y₀, hy₀, -, e', -⟩ := back b y hb; exact hwf.origin b y₀ o hy₀ (e' ▸ ho)
  · obtain ⟨y₀, hy₀, -, -, e', -⟩ := back b y hb; rw [hP]; exact hwf.fp b y₀ hy₀ l (e' ▸ hl)
  · obtain ⟨y₀, hy₀, -, -, -, eh, ea⟩ := back b y hb
    rw [eh, HolderLive.congr hP hF hd]; exact hwf.poss b y₀ hy₀ (ea ya).1
  · obtain ⟨x₀, hx₀, m₁, -, f₁, -, ac₁⟩ := back a' x' ha'
    obtain ⟨y₀, hy₀, m₂, -, f₂, -, ac₂⟩ := back b' y' hb'
    rw [release_ancs hx] at hnab hnba; rw [m₁, m₂]
    exact i1 a' b' x₀ y₀ p hab hx₀ hy₀ (ac₁ xa').1 (ac₂ ya').1 (f₁ ▸ xp) (f₂ ▸ yp) hnab hnba
  · obtain ⟨y₀, hy₀, m₀, e', f₀, -⟩ := back b y hb
    obtain ⟨x₁, hx₁, hh⟩ := i2 b y₀ o hy₀ (e' ▸ ho)
    refine ⟨if a = o then { x with active := false } else x₁, by rw [get]; split <;> simp_all,
      fun p hp => ?_⟩
    have := hh p (f₀ ▸ hp); rw [m₀]
    split
    · subst_vars; rw [hx] at hx₁; cases hx₁; exact this
    · exact this
  · have hq' := (S3.Usable.congr hP hF hd).1 hq
    have hy' : y ∈ s.D q := by rw [e] at hy; exact hy
    obtain ⟨z, hz, za⟩ := i3 q hq' y hy'
    refine ⟨z, ?_, za⟩
    rw [get]; split
    · subst_vars; exact absurd hy' (h3 q (List.mem_range.2 hq'.lt) hq')
    · exact hz

/-! ## States with the same authority skeleton -/

theorem SameSkel.i1 {s s' : S3} (h : SameSkel s s') (h1 : I1 s) : I1 s' := by
  intro a b x' y' p hab ha hb xa ya xp yp hnab hnba
  obtain ⟨x, hx, ex⟩ := h.get ha; obtain ⟨y, hy, ey⟩ := h.get hb
  simp [skel] at ex ey; rw [h.ancs] at hnab hnba
  rw [ex.1, ey.1]
  exact h1 a b x y p hab hx hy (ex.2.2.2 ▸ xa) (ey.2.2.2 ▸ ya) (ex.2.2.1 ▸ xp) (ey.2.2.1 ▸ yp)
    hnab hnba

theorem SameSkel.i2 {s s' : S3} (h : SameSkel s s') (h2 : I2 s) : I2 s' := by
  intro b y a hb ho
  obtain ⟨y₀, hy₀, e⟩ := h.get hb; simp [skel] at e
  obtain ⟨x₀, hx₀, hh⟩ := h2 b y₀ a hy₀ (e.2.1 ▸ ho)
  obtain ⟨x', hx', e'⟩ := h.get' hx₀; simp [skel] at e'
  exact ⟨x', hx', fun p hp => by rw [e.1, e'.1, e'.2.2.1]; exact hh p (e.2.2.1 ▸ hp)⟩

theorem SameSkel.origin {s s' : S3} (h : SameSkel s s') (hw : ∀ (b : Nat) (y : Authority) (a : Nat),
    s.A[b]? = some y → y.origin = some a → a < b) :
    ∀ (b : Nat) (y : Authority) (a : Nat), s'.A[b]? = some y → y.origin = some a → a < b := by
  intro b y a hb ho
  obtain ⟨y₀, hy₀, e⟩ := h.get hb; simp [skel] at e
  exact hw b y₀ a hy₀ (e.2.1 ▸ ho)

theorem SameSkel.fp {s s' : S3} (h : SameSkel s s') {n : Nat} (hw : ∀ (a : Nat) (x : Authority),
    s.A[a]? = some x → ∀ l ∈ x.footprint, l < n) :
    ∀ (a : Nat) (x : Authority), s'.A[a]? = some x → ∀ l ∈ x.footprint, l < n := by
  intro a x hx l hl
  obtain ⟨x₀, hx₀, e⟩ := h.get hx; simp [skel] at e
  exact hw a x₀ hx₀ l (e.2.2.1 ▸ hl)

/-! ## Preservation by `transfer` (MM-03.3 §3, O4; A4; A5) -/

theorem transfer_P_get (s : S3) (src dst q : Nat) :
    (transferEff s src dst).P[q]? = (s.P[q]?).map fun pl =>
      if heldIn s.P src pl.owner then { pl with owner := .place dst } else pl := by
  simp [transferEff]

theorem transfer_A_get (s : S3) (src dst j : Nat) :
    (transferEff s src dst).A[j]? = (s.A[j]?).map fun y =>
      if heldIn s.P src y.holder then { y with holder := .place dst } else y := by
  simp [transferEff]

theorem transfer_len (s : S3) (src dst : Nat) :
    (transferEff s src dst).P.length = s.P.length := by simp [transferEff]

theorem transfer_parentOf (s : S3) (src dst : Nat) :
    parentOf (transferEff s src dst).P = parentOf s.P := by
  funext i; simp only [parentOf, transfer_P_get]
  cases s.P[i]? with
  | none => rfl
  | some pl => simp only [Option.map_some, Option.bind_some]; split <;> rfl

theorem footprint_congr {P P' : List Place} (hlen : P'.length = P.length)
    (hpar : parentOf P' = parentOf P) (q : Nat) : footprint P' q = footprint P q := by
  unfold footprint; rw [hlen]; congr 1; funext l
  exact decide_eq_decide.2 (by simp only [isLeaf, partOf, hpar, hlen])

theorem transfer_footprint (s : S3) (src dst q : Nat) :
    footprint (transferEff s src dst).P q = footprint s.P q :=
  footprint_congr (transfer_len s src dst) (transfer_parentOf s src dst) q

theorem transfer_partOf (s : S3) (src dst r q : Nat) :
    partOf (transferEff s src dst).P r q ↔ partOf s.P r q := by
  simp only [partOf, transfer_parentOf, transfer_len]

/-- `transfer` changes no skeleton: it creates and duplicates no authority (O4.3). -/
theorem transfer_skel (s : S3) (src dst : Nat) : SameSkel s (transferEff s src dst) := by
  refine ⟨by simp [transferEff], fun j => ?_⟩
  rw [transfer_A_get]
  cases s.A[j]? with
  | none => rfl
  | some y => simp only [Option.map_some]; split <;> rfl

/-- A place usable after the transfer was usable before (A5). -/
theorem transfer_usable_back {s : S3} {src dst : Nat} (hwf : WF3 s) (hsrc : s.Usable src) {q : Nat}
    (h : (transferEff s src dst).Usable q) : s.Usable q := by
  induction h with
  | @frame q f pl hpl hd ho hf =>
    rw [transfer_P_get] at hpl
    cases h' : s.P[q]? with
    | none => rw [h'] at hpl; cases hpl
    | some pl =>
      rw [h'] at hpl; simp only [Option.map_some, Option.some.injEq] at hpl; subst hpl
      split at ho
      · cases ho
      · exact .frame h' hd ho hf
  | @place q o pl hpl hd ho _ ih =>
    rw [transfer_P_get] at hpl
    cases h' : s.P[q]? with
    | none => rw [h'] at hpl; cases hpl
    | some pl =>
      rw [h'] at hpl; simp only [Option.map_some, Option.some.injEq] at hpl; subst hpl
      split at ho
      · rename_i hh
        cases hpo : pl.owner with
        | frame f => rw [hpo] at hh; exact hh.elim
        | place r =>
          rw [hpo] at hh
          exact .place h' hd hpo (usable_of_partOf hwf (r + 1) r src (Nat.lt_succ_self r) hh hsrc)
      · exact .place h' hd ho ih

/-- A place usable before the transfer stays usable when the destination is usable after it
(A5). -/
theorem transfer_usable_fwd {s : S3} {src dst : Nat} (hd' : (transferEff s src dst).Usable dst)
    {q : Nat} (h : s.Usable q) : (transferEff s src dst).Usable q := by
  induction h with
  | @frame q f pl hpl hd ho hf =>
    exact .frame (by rw [transfer_P_get, hpl]; rfl) hd (by simp [ho, heldIn]) hf
  | @place q o pl hpl hd ho _ ih =>
    by_cases hh : heldIn s.P src (.place o)
    · exact .place (by rw [transfer_P_get, hpl]; rfl) hd (by simp [ho, hh]) hd'
    · exact .place (by rw [transfer_P_get, hpl]; rfl) hd (by simp [ho, hh]) ih

/-- `transfer` preserves `WF3` and `Inv3` (MM-03.3 §3, O4; §10; A4; A5). -/
theorem transfer_preserves {k : K} {s s' : S3} {src dst : Nat} (hwf : WF3 s) (hinv : Inv3 s)
    (h : TransferStep k src dst s (.ok s')) : WF3 s' ∧ Inv3 s' := by
  obtain ⟨⟨hsrc, -, hdst, -, -, -, -, hd', -, h5, -, -⟩, rfl⟩ := Guarded.ok_iff.1 h
  have sk := transfer_skel s src dst
  obtain ⟨i1, i2, i3, -⟩ := hinv
  refine ⟨⟨sk.origin hwf.origin, ?_, hwf.ne, hwf.nodup, hwf.frames, ?_, ?_, ?_, ?_⟩,
    sk.i1 i1, sk.i2 i2, fun q hq x hx => ?_, i4_always _⟩
  · rw [transfer_len]; exact sk.fp hwf.fp
  · intro q pl f hq ho
    rw [transfer_P_get] at hq
    cases h' : s.P[q]? with
    | none => rw [h'] at hq; cases hq
    | some pl₀ =>
      rw [h'] at hq; simp only [Option.map_some, Option.some.injEq] at hq; subst hq
      split at ho
      · cases ho
      · exact hwf.ownerFrame q pl₀ f h' ho
  · intro q pl o hq ho
    rw [transfer_len]; rw [transfer_P_get] at hq
    cases h' : s.P[q]? with
    | none => rw [h'] at hq; cases hq
    | some pl₀ =>
      rw [h'] at hq; simp only [Option.map_some, Option.some.injEq] at hq; subst hq
      split at ho
      · cases ho; exact hdst.lt
      · exact hwf.ownerPlace q pl₀ o h' ho
  · intro q pl r hq hp
    rw [transfer_P_get] at hq
    cases h' : s.P[q]? with
    | none => rw [h'] at hq; cases hq
    | some pl₀ =>
      rw [h'] at hq; simp only [Option.map_some, Option.some.injEq] at hq; subst hq
      have hp₀ : pl₀.parent = some r := by split at hp <;> exact hp
      obtain ⟨pr, hpr, hlt, ho, hdd⟩ := hwf.parts q pl₀ r h' hp₀
      refine ⟨_, by rw [transfer_P_get, hpr]; rfl, hlt, ?_, hdd⟩
      by_cases hc : heldIn s.P src pl₀.owner <;> simp [hc, ho]
  · intro a y hy ya
    rw [transfer_A_get] at hy
    cases h' : s.A[a]? with
    | none => rw [h'] at hy; cases hy
    | some y₀ =>
      rw [h'] at hy; simp only [Option.map_some, Option.some.injEq] at hy; subst hy
      have ya₀ : y₀.active = true := by split at ya <;> exact ya
      have hl := hwf.poss a y₀ h' ya₀
      split
      · exact hd'
      · cases hh : y₀.holder with
        | frame f => rw [hh] at hl; exact hl
        | place p => rw [hh] at hl; exact transfer_usable_fwd hd' hl
  · have hq' := transfer_usable_back hwf hsrc hq
    refine sk.active.2 ?_
    simp only [transferEff] at hx
    split at hx
    · rename_i hqd; subst hqd; rcases List.mem_append.1 hx with hx | hx
      · exact i3 _ hq' x hx
      · exact h5 x hx
    · split at hx
      · simp at hx
      · exact i3 q hq' x hx

/-- `transfer_no_duplicate_authority` (MM-03.3 §3, O4.3; §2, I4; §10; A4): no authority is
created or duplicated, each keeps mode, origin, footprint and activity; the authorities held by
the source or one of its parts are now held by the destination; the others keep their holder,
so a root held by a frame never moves. -/
theorem transfer_no_duplicate_authority {k : K} {s s' : S3} {src dst : Nat}
    (h : TransferStep k src dst s (.ok s')) :
    SameSkel s s' ∧ ∀ (b : Nat) (y : Authority), s.A[b]? = some y →
      s'.A[b]? = some (if heldIn s.P src y.holder then { y with holder := .place dst } else y) := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
  exact ⟨transfer_skel s src dst, fun b y hy => by rw [transfer_A_get, hy]; rfl⟩

/-- Ownership moves with the value (A5): every place owned by the source or one of its parts is
now owned by the destination, and keeps its parent (it does not move). -/
theorem transfer_moves_ownership {k : K} {s s' : S3} {src dst : Nat}
    (h : TransferStep k src dst s (.ok s')) :
    ∀ (q : Nat) (pl : Place), s.P[q]? = some pl →
      s'.P[q]? = some (if heldIn s.P src pl.owner then { pl with owner := .place dst } else pl) := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
  exact fun q pl hq => by rw [transfer_P_get, hq]; rfl

/-- `transfer_invalidates_source` (MM-03.3 §3, O4; §2, I4): after a transfer, every leaf of the
source is `Moved` and readable by no authority. -/
theorem transfer_invalidates_source {k : K} {s s' : S3} {src dst : Nat}
    (h : TransferStep k src dst s (.ok s')) :
    ∀ l ∈ footprint s.P src, s'.I l = .moved ∧ ∀ a, ¬ CanReadLeaf s' a l := by
  obtain ⟨⟨-, -, -, -, hov, -⟩, rfl⟩ := Guarded.ok_iff.1 h
  intro l hl
  have hm : (transferEff s src dst).I l = .moved := by
    simp only [transferEff, show l ∉ footprint s.P dst from fun h' => hov ⟨l, hl, h'⟩, hl,
      ↓reduceIte]
  exact ⟨hm, fun a => i4_always _ a l hm⟩

/-- Moved dependencies (MM-03.3.6; MM-03.3 §3, O4): those of the source go with the destination
and leave the source and its parts. -/
theorem transfer_moves_deps {k : K} {s s' : S3} {src dst : Nat}
    (h : TransferStep k src dst s (.ok s')) :
    (∀ x ∈ depsOf s src, x ∈ s'.D dst) ∧ ∀ r, r ≠ dst → partOf s.P r src → s'.D r = [] := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
  exact ⟨fun x hx => by simp [transferEff, hx], fun r hr hp => by simp [transferEff, hr, hp]⟩

/-! ## Preservation by `depend`, `read3`, `write3` -/

theorem WF3.of_eq {s s' : S3} (h : WF3 s) (hA : s'.A = s.A) (hP : s'.P = s.P) (hF : s'.F = s.F)
    (hn : s'.nF = s.nF) (hd : s'.dead = s.dead) : WF3 s' := by
  obtain ⟨w0, w2, wne, wnd, wfr, wof, wop, wpa, wpo⟩ := h
  refine ⟨hA ▸ w0, by rw [hA, hP]; exact w2, hF ▸ wne, hF ▸ wnd, by rw [hF, hn]; exact wfr,
    by rw [hP, hn]; exact wof, by rw [hP]; exact wop, by rw [hP, hd]; exact wpa, ?_⟩
  intro a y hy ya
  rw [hA] at hy; rw [HolderLive.congr hP hF hd]; exact wpo a y hy ya

/-- `depend` preserves `WF3` and `Inv3` (MM-03.3 §3, O5; §10). -/
theorem depend_preserves {s s' : S3} {q x : Nat} (hwf : WF3 s) (hinv : Inv3 s)
    (h : DependStep q x s (.ok s')) : WF3 s' ∧ Inv3 s' := by
  obtain ⟨⟨-, hx, -⟩, rfl⟩ := Guarded.ok_iff.1 h
  obtain ⟨i1, i2, i3, -⟩ := hinv
  refine ⟨hwf.of_eq rfl rfl rfl rfl rfl, i1, i2, fun r hr y hy => ?_, i4_always _⟩
  have hr' := (S3.Usable.congr (s := s) (s' := dependEff s q x) rfl rfl rfl).1 hr
  simp only [dependEff] at hy
  split at hy
  · subst_vars; rcases List.mem_append.1 hy with hy | hy
    · exact i3 _ hr' y hy
    · simp at hy; exact hy ▸ hx
  · exact i3 r hr' y hy

/-- `depend_preserves_anchor_validity` (MM-03.3 §3, O5; §2, I3; §10): I3 is preserved and the
validity of every anchor is unchanged; `depend` lengthens the validity of no origin. -/
theorem depend_preserves_anchor_validity {s s' : S3} {q x : Nat} (hi3 : I3 s)
    (h : DependStep q x s (.ok s')) : I3 s' ∧ ∀ y, s'.Active y ↔ s.Active y := by
  obtain ⟨⟨-, hx, -⟩, rfl⟩ := Guarded.ok_iff.1 h
  refine ⟨fun r hr y hy => ?_, fun _ => Iff.rfl⟩
  have hr' := (S3.Usable.congr (s := s) (s' := dependEff s q x) rfl rfl rfl).1 hr
  simp only [dependEff] at hy
  split at hy
  · subst_vars; rcases List.mem_append.1 hy with hy | hy
    · exact hi3 _ hr' y hy
    · simp at hy; exact hy ▸ hx
  · exact hi3 r hr' y hy

/-- `read3` keeps the state (MM-03.3 §5: a read does not change the authorities). -/
theorem read3_preserves {s s' : S3} {a : Nat} {ls : List Nat} (h : Read3Step a ls s (.ok s')) :
    s' = s := (Guarded.ok_iff.1 h).2

/-- `write3` preserves `WF3` and `Inv3` (MM-03.3 §5; §10). -/
theorem write3_preserves {s s' : S3} {a : Nat} {ls : List Nat} (hwf : WF3 s) (hinv : Inv3 s)
    (h : Write3Step a ls s (.ok s')) : WF3 s' ∧ Inv3 s' := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
  exact ⟨hwf.of_eq rfl rfl rfl rfl rfl, hinv.1, hinv.2.1, fun q hq x hx =>
    hinv.2.2.1 q ((S3.Usable.congr (s := s) (s' := write3Eff s ls) rfl rfl rfl).1 hq) x hx,
    i4_always _⟩

/-! ## Preservation by `enterFrame` (MM-03.3 §4, O6; A3; A5) -/

theorem enterP_len (s : S3) (ls : List (Option Nat × Option Nat × Nat)) :
    (enterP s ls).length = s.P.length + ls.length := by simp [enterP]

theorem enterP_lt {s : S3} {ls : List (Option Nat × Option Nat × Nat)} {q : Nat}
    (h : q < s.P.length) : (enterP s ls)[q]? = s.P[q]? := List.getElem?_append_left h

theorem enterP_new {s : S3} {ls : List (Option Nat × Option Nat × Nat)} {i : Nat}
    (h : i < ls.length) : (enterP s ls)[s.P.length + i]? =
      some ⟨(ls[i]?).bind (·.1), localOwner ls s.nF i, ((ls[i]?).map (·.2.2)).getD 0⟩ := by
  simp only [enterP, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    List.getElem?_map, List.getElem?_range h, Option.map_some]

theorem enterP_get {s : S3} {ls : List (Option Nat × Option Nat × Nat)} {q : Nat} {pl : Place}
    (h : (enterP s ls)[q]? = some pl) :
    (q < s.P.length ∧ s.P[q]? = some pl) ∨ (s.P.length ≤ q ∧ ∃ i, i < ls.length ∧
      q = s.P.length + i ∧ pl = ⟨(ls[i]?).bind (·.1), localOwner ls s.nF i,
        ((ls[i]?).map (·.2.2)).getD 0⟩) := by
  by_cases hq : q < s.P.length
  · exact .inl ⟨hq, by rwa [enterP_lt hq] at h⟩
  · have hi : q - s.P.length < ls.length := by
      have := lt_of_getElem? h; rw [enterP_len] at this; omega
    have e : q = s.P.length + (q - s.P.length) := by omega
    rw [e, enterP_new hi] at h; cases h
    exact .inr ⟨by omega, _, hi, e, rfl⟩

theorem enter_get {s : S3} {ps : List Nat} {ls : List (Option Nat × Option Nat × Nat)} {j : Nat}
    {z : Authority} (h : (enterEff s ps ls).A[j]? = some z) :
    (j < s.A.length ∧ ∃ y, s.A[j]? = some y ∧
      z = if j ∈ ps then { y with holder := .frame s.nF } else y) ∨
    (s.A.length ≤ j ∧ ∃ i, (rootIdx ls)[j - s.A.length]? = some i ∧
      z = ⟨.modify, none, footprint (enterP s ls) (s.P.length + i), localOwner ls s.nF i, true⟩) := by
  simp only [enterEff] at h
  by_cases hj : j < s.A.length
  · have hj' : j < (mapI (fun j y => if j ∈ ps then { y with holder := .frame s.nF } else y) 0
        s.A).length := by rw [length_mapI]; exact hj
    rw [List.getElem?_append_left hj', getElem?_mapI] at h
    cases hy : s.A[j]? with
    | none => rw [hy] at h; cases h
    | some y => rw [hy] at h; cases h; exact .inl ⟨hj, y, rfl, by simp⟩
  · rw [List.getElem?_append_right (by rw [length_mapI]; omega), length_mapI,
      List.getElem?_map] at h
    cases hi : (rootIdx ls)[j - s.A.length]? with
    | none => rw [hi] at h; cases h
    | some i => rw [hi] at h; cases h; exact .inr ⟨by omega, i, rfl, rfl⟩

theorem enter_lt {s : S3} {ps : List Nat} {ls : List (Option Nat × Option Nat × Nat)} {j : Nat}
    (h : j < s.A.length) : (enterEff s ps ls).A[j]? =
      (s.A[j]?).map fun y => if j ∈ ps then { y with holder := .frame s.nF } else y := by
  simp only [enterEff]
  rw [List.getElem?_append_left (by rw [length_mapI]; exact h), getElem?_mapI]; simp

theorem enter_org_lt {s : S3} {ps : List Nat} {ls : List (Option Nat × Option Nat × Nat)}
    {j : Nat} (h : j < s.A.length) : (enterEff s ps ls).org j = s.org j := by
  simp only [S3.org, enter_lt h]
  cases s.A[j]? with
  | none => rfl
  | some y => simp only [Option.map_some, Option.bind_some]; split <;> rfl

theorem enter_ancs_lt {s : S3} {ps : List Nat} {ls : List (Option Nat × Option Nat × Nat)}
    {j : Nat} (h : j < s.A.length) : (enterEff s ps ls).ancs j = s.ancs j :=
  chain_congr fun _ hi => enter_org_lt (Nat.lt_of_le_of_lt hi h)

theorem rootIdx_mem {ls : List (Option Nat × Option Nat × Nat)} {k i : Nat}
    (h : (rootIdx ls)[k]? = some i) : i < ls.length ∧ (ls[i]?).bind (·.1) = none := by
  have := List.mem_of_getElem? h
  simp only [rootIdx, List.mem_filter, List.mem_range, Option.isNone_iff_eq_none] at this
  exact this

theorem enter_parentOf_new {s : S3} {ls : List (Option Nat × Option Nat × Nat)} {i : Nat}
    (h : i < ls.length) : parentOf (enterP s ls) (s.P.length + i) = (ls[i]?).bind (·.1) := by
  simp [parentOf, enterP_new h]

theorem enter_parentOf_lt {s : S3} {ls : List (Option Nat × Option Nat × Nat)} {q : Nat}
    (h : q < s.P.length) : parentOf (enterP s ls) q = parentOf s.P q := by
  simp [parentOf, enterP_lt h]

theorem enter_root_fp_ge {s : S3} {ls : List (Option Nat × Option Nat × Nat)} {i l : Nat}
    (h : l ∈ footprint (enterP s ls) (s.P.length + i)) : s.P.length ≤ l := by
  obtain ⟨-, -, -, h | h⟩ := mem_footprint.1 h
  · omega
  · have := chain_lt h; omega

theorem enter_roots_disjoint {s : S3} {ls : List (Option Nat × Option Nat × Nat)} {i i' l : Nat}
    (hii : i ≠ i') (hn : (ls[i]?).bind (·.1) = none) (hn' : (ls[i']?).bind (·.1) = none)
    (h : l ∈ footprint (enterP s ls) (s.P.length + i))
    (h' : l ∈ footprint (enterP s ls) (s.P.length + i')) : False := by
  have hlt : ∀ {j}, l ∈ footprint (enterP s ls) (s.P.length + j) → j < ls.length := fun hj => by
    obtain ⟨hl, -, -, hq⟩ := mem_footprint.1 hj
    rw [enterP_len] at hl
    rcases hq with hq | hq
    · omega
    · have := chain_lt hq; omega
  have hi := hlt h; have hi' := hlt h'
  have r := enter_parentOf_new (s := s) hi; rw [hn] at r
  have r' := enter_parentOf_new (s := s) hi'; rw [hn'] at r'
  obtain ⟨-, -, -, h | h⟩ := mem_footprint.1 h <;> obtain ⟨-, -, -, h' | h'⟩ := mem_footprint.1 h'
  · omega
  · subst h; rw [chain_none r] at h'; simp at h'
  · subst h'; rw [chain_none r'] at h; simp at h
  · exact hii (by have := chainF_root _ _ _ _ h r h' r'; omega)

/-- New locals are usable once the frame is entered (A5). -/
theorem enter_usable_new {s : S3} {ps : List Nat} {ls : List (Option Nat × Option Nat × Nat)}
    (hpre : EnterPre s ps ls) : ∀ n i, i < n → i < ls.length →
      (enterEff s ps ls).Usable (s.P.length + i)
  | 0, _, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, i, _, hi => by
    have hpl := enterP_new (s := s) hi
    have hd : (enterEff s ps ls).dead (s.P.length + i) = false := by simp [enterEff]
    unfold localOwner at hpl
    cases ho : (ls[i]?).bind (·.2.1) with
    | none =>
      rw [ho] at hpl
      exact .frame (show (enterP s ls)[_]? = _ from hpl) hd rfl (List.mem_cons_self ..)
    | some o =>
      rw [ho] at hpl
      have h2 := (hpre.2.2 i (List.mem_range.2 hi)).2
      rw [ho] at h2; obtain ⟨h₁, h₂⟩ := h2
      have := enter_usable_new hpre n (o - s.P.length) (by omega) (by omega)
      rw [show s.P.length + (o - s.P.length) = o by omega] at this
      exact .place (show (enterP s ls)[_]? = _ from hpl) hd rfl this

/-- Old places keep their usability when a frame is entered (A5). -/
theorem enter_usable_old {s : S3} {ps : List Nat} {ls : List (Option Nat × Option Nat × Nat)}
    {q : Nat} (h : s.Usable q) : (enterEff s ps ls).Usable q := by
  induction h with
  | @frame q f pl hpl hd ho hf =>
    exact .frame (show (enterP s ls)[q]? = _ by rw [enterP_lt (lt_of_getElem? hpl)]; exact hpl)
      (by simp [enterEff, hd]) ho (List.mem_cons_of_mem _ hf)
  | @place q o pl hpl hd ho _ ih =>
    exact .place (show (enterP s ls)[q]? = _ by rw [enterP_lt (lt_of_getElem? hpl)]; exact hpl)
      (by simp [enterEff, hd]) ho ih

theorem enter_usable_back {s : S3} {ps : List Nat} {ls : List (Option Nat × Option Nat × Nat)}
    (hwf : WF3 s) {q : Nat} (h : (enterEff s ps ls).Usable q) (hq : q < s.P.length) :
    s.Usable q := by
  induction h with
  | @frame q f pl hpl hd ho hf =>
    have hpl' : s.P[q]? = some pl := by
      have : (enterP s ls)[q]? = some pl := hpl
      rwa [enterP_lt hq] at this
    have hd' : s.dead q = false := by simpa [enterEff, hq] using hd
    have hlt := hwf.ownerFrame q pl f hpl' ho
    rcases List.mem_cons.1 hf with e | hf
    · subst e; exact absurd hlt (Nat.lt_irrefl _)
    · exact .frame hpl' hd' ho hf
  | @place q o pl hpl hd ho _ ih =>
    have hpl' : s.P[q]? = some pl := by
      have : (enterP s ls)[q]? = some pl := hpl
      rwa [enterP_lt hq] at this
    have hd' : s.dead q = false := by simpa [enterEff, hq] using hd
    exact .place hpl' hd' ho (ih (hwf.ownerPlace q pl o hpl' ho))

theorem enter_localOwner_live {s : S3} {ps : List Nat} {ls : List (Option Nat × Option Nat × Nat)}
    (hpre : EnterPre s ps ls) {i : Nat} (hi : i < ls.length) :
    HolderLive (enterEff s ps ls) (localOwner ls s.nF i) := by
  unfold localOwner
  cases ho : (ls[i]?).bind (·.2.1) with
  | none => exact List.mem_cons_self ..
  | some o =>
    have h2 := (hpre.2.2 i (List.mem_range.2 hi)).2
    rw [ho] at h2
    have := enter_usable_new hpre (o - s.P.length + 1) (o - s.P.length) (Nat.lt_succ_self _)
      (by simp only [OptP] at h2; omega)
    simp only [OptP] at h2
    rwa [show s.P.length + (o - s.P.length) = o by omega] at this

/-- `enterFrame` preserves `WF3` and `Inv3` (MM-03.3 §4, O6; §10; A3; A5). -/
theorem enter_preserves {s s' : S3} {ps : List Nat} {ls : List (Option Nat × Option Nat × Nat)}
    (hwf : WF3 s) (hinv : Inv3 s) (h : EnterStep ps ls s (.ok s')) : WF3 s' ∧ Inv3 s' := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  obtain ⟨i1, i2, i3, -⟩ := hinv
  have nodup : (rootIdx ls).Nodup :=
    ((pairwise_lt_range _).sublist List.filter_sublist).imp Nat.ne_of_lt
  have skel_old : ∀ {j z}, (enterEff s ps ls).A[j]? = some z → j < s.A.length →
      ∃ y, s.A[j]? = some y ∧ z.mode = y.mode ∧ z.origin = y.origin ∧
        z.footprint = y.footprint ∧ z.active = y.active ∧
        (z.holder = y.holder ∨ (j ∈ ps ∧ z.holder = .frame s.nF)) := by
    intro j z hz hj
    rcases enter_get hz with ⟨-, y, hy, rfl⟩ | ⟨hj', -⟩
    · refine ⟨y, hy, ?_⟩; split <;> simp_all
    · omega
  have live : ∀ (hd : Holder), HolderLive s hd → HolderLive (enterEff s ps ls) hd := by
    intro hd hl; cases hd with
    | frame f => exact List.mem_cons_of_mem _ hl
    | place p => exact enter_usable_old hl
  refine ⟨⟨?_, ?_, by simp [enterEff], ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, i4_always _⟩
  · intro b y a hb ho
    rcases enter_get hb with ⟨hb', y₀, hy₀, rfl⟩ | ⟨-, _, -, hz⟩
    · exact hwf.origin b y₀ a hy₀ (by split at ho <;> exact ho)
    · rw [hz] at ho; cases ho
  · intro a y hy l hl
    show l < (enterP s ls).length
    rw [enterP_len]
    rcases enter_get hy with ⟨-, y₀, hy₀, rfl⟩ | ⟨-, i, -, rfl⟩
    · have := hwf.fp a y₀ hy₀ l (by split at hl <;> exact hl); omega
    · have := (mem_footprint.1 hl).1; rwa [enterP_len] at this
  · exact List.nodup_cons.2 ⟨fun hm => Nat.lt_irrefl _ (hwf.frames _ hm), hwf.nodup⟩
  · intro f hf; rcases List.mem_cons.1 hf with rfl | hf
    · exact Nat.lt_succ_self _
    · exact Nat.lt_succ_of_lt (hwf.frames f hf)
  · intro q pl f hq ho
    rcases enterP_get hq with ⟨-, hq'⟩ | ⟨-, i, -, -, rfl⟩
    · exact Nat.lt_succ_of_lt (hwf.ownerFrame q pl f hq' ho)
    · simp only [localOwner] at ho; split at ho
      · cases ho
      · cases ho; exact Nat.lt_succ_self _
  · intro q pl o hq ho
    show o < (enterP s ls).length
    rw [enterP_len]
    rcases enterP_get hq with ⟨-, hq'⟩ | ⟨-, i, hi, -, rfl⟩
    · have := hwf.ownerPlace q pl o hq' ho; omega
    · simp only [localOwner] at ho; split at ho
      · rename_i o' ho'; cases ho
        have h2 := (hpre.2.2 i (List.mem_range.2 hi)).2
        rw [ho'] at h2; exact Nat.lt_of_lt_of_le h2.2 (by omega)
      · cases ho
  · intro q pl r hq hp
    rcases enterP_get hq with ⟨hq', hq''⟩ | ⟨hq', i, hi, rfl, rfl⟩
    · obtain ⟨pr, hpr, hlt, ho, hd⟩ := hwf.parts q pl r hq'' hp
      refine ⟨pr, by show (enterP s ls)[r]? = _; rw [enterP_lt (by omega)]; exact hpr, hlt, ho, ?_⟩
      simp [enterEff, show ¬ s.P.length ≤ r by omega, show ¬ s.P.length ≤ q by omega, hd]
    · have h1 := (hpre.2.2 i (List.mem_range.2 hi)).1
      simp only at hp; rw [hp] at h1; obtain ⟨hr₁, hr₂, hown⟩ := h1
      have hri : r - s.P.length < ls.length := by omega
      refine ⟨_, by show (enterP s ls)[r]? = _; rw [show r = s.P.length + (r - s.P.length) by omega,
        enterP_new hri], by omega, ?_, by simp [enterEff, show s.P.length ≤ r by omega]⟩
      simp only [localOwner, hown]
  · intro a y hy ya
    rcases enter_get hy with ⟨-, y₀, hy₀, rfl⟩ | ⟨hj, i, hi, rfl⟩
    · split
      · exact List.mem_cons_self ..
      · exact live _ (hwf.poss a y₀ hy₀ (by split at ya <;> simp_all))
    · exact enter_localOwner_live hpre (rootIdx_mem hi).1
  · intro a b x y p hab ha hb xa ya xp yp hnab hnba
    rcases enter_get ha with ⟨ha', x₀, hx₀, rfl⟩ | ⟨ha', i, hi, rfl⟩ <;>
      rcases enter_get hb with ⟨hb', y₀, hy₀, rfl⟩ | ⟨hb', i', hi', rfl⟩
    · rw [enter_ancs_lt hb'] at hnab; rw [enter_ancs_lt ha'] at hnba
      have := i1 a b x₀ y₀ p hab hx₀ hy₀ (by split at xa <;> exact xa) (by split at ya <;> exact ya)
        (by split at xp <;> exact xp) (by split at yp <;> exact yp) hnab hnba
      constructor
      · split <;> exact this.1
      · split <;> exact this.2
    · have := hwf.fp a x₀ hx₀ p (by split at xp <;> exact xp)
      have := enter_root_fp_ge yp; omega
    · have := hwf.fp b y₀ hy₀ p (by split at yp <;> exact yp)
      have := enter_root_fp_ge xp; omega
    · have hk : a - s.A.length ≠ b - s.A.length := by omega
      have hii : i ≠ i' := fun e => hk ((nodup.getElem?_inj (lt_of_getElem? hi)).1 (by
        rw [hi, hi', e]))
      exact (enter_roots_disjoint hii (rootIdx_mem hi).2 (rootIdx_mem hi').2 xp yp).elim
  · intro b y a hb ho
    rcases enter_get hb with ⟨-, y₀, hy₀, rfl⟩ | ⟨-, _, -, hz⟩
    · obtain ⟨x₁, hx₁, hh⟩ := i2 b y₀ a hy₀ (by split at ho <;> exact ho)
      refine ⟨_, by rw [enter_lt (lt_of_getElem? hx₁), hx₁]; rfl, fun p hp => ?_⟩
      have := hh p (by split at hp <;> exact hp)
      constructor
      · split <;> exact this.1
      · split <;> split <;> exact this.2
    · rw [hz] at ho; cases ho
  · intro q hq x hx
    by_cases hlt : q < s.P.length
    · have hx' : x ∈ s.D q := by simpa [enterEff, show ¬ s.P.length ≤ q by omega] using hx
      obtain ⟨y, hy, ya⟩ := i3 q (enter_usable_back hwf hq hlt) x hx'
      refine ⟨_, by rw [enter_lt (lt_of_getElem? hy), hy]; rfl, ?_⟩
      split <;> exact ya
    · simp [enterEff, show s.P.length ≤ q by omega] at hx

/-! ## Preservation by `exitFrame` (MM-03.3 §4, O7; A4; A5; A7) -/

/-- Termination of the walk along origins (A7): the walk from `x` visits at most `x + 1`
authorities, with strictly decreasing identities. -/
theorem reanchor_terminates (s : S3) (x : Nat) :
    (x :: s.ancs x).length ≤ x + 1 ∧ ∀ z ∈ s.ancs x, z < x :=
  ⟨by simp only [List.length_cons]; have := chain_length s.org x; unfold S3.ancs; omega,
   fun _ hz => chain_lt hz⟩

theorem org_lt {s : S3} (hw : ∀ (b : Nat) (y : Authority) (a : Nat), s.A[b]? = some y →
    y.origin = some a → a < b) {x o : Nat} (h : s.org x = some o) : o < x := by
  simp only [S3.org] at h
  cases hy : s.A[x]? with
  | none => rw [hy] at h; cases h
  | some y => rw [hy] at h; exact hw x y o hy h

theorem ancs_cons {s : S3} (hw : ∀ (b : Nat) (y : Authority) (a : Nat), s.A[b]? = some y →
    y.origin = some a → a < b) {x o : Nat} (h : s.org x = some o) :
    s.ancs x = o :: s.ancs o := chain_cons h (org_lt hw h)

/-- One step of a chain of origins: the chain from `x` starts with the origin of `x`, which is
smaller, or it is empty. -/
theorem ancs_step {s : S3} {x o : Nat} (h : s.org x = some o) :
    (o < x ∧ s.ancs x = o :: s.ancs o) ∨ s.ancs x = [] := by
  by_cases hlt : o < x
  · exact .inl ⟨hlt, chain_cons h hlt⟩
  · right; unfold S3.ancs chain
    cases x with
    | zero => rfl
    | succ k => simp [chainF, h, hlt]

/-- The first surviving strict ancestor along `origin` (A7): it is an ancestor, it survives, and
every surviving ancestor is it or one of its own ancestors. -/
theorem firstSurv_ancs {s : S3} {F₀ : Frames} :
    ∀ n x, x < n → ∀ z, firstSurv s F₀ (s.ancs x) = some z →
      z ∈ s.ancs x ∧ Survives s F₀ z ∧
        ∀ w ∈ s.ancs x, Survives s F₀ w → w = z ∨ w ∈ s.ancs z
  | 0, _, h, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, x, hx, z, hz => by
    cases ho : s.org x with
    | none => rw [S3.ancs, chain_none ho] at hz; simp [firstSurv] at hz
    | some o =>
      obtain ⟨hlt, he⟩ : o < x ∧ s.ancs x = o :: s.ancs o := by
        rcases ancs_step ho with h | he
        · exact h
        · rw [he] at hz; simp [firstSurv] at hz
      rw [he] at hz ⊢
      by_cases hs : Survives s F₀ o
      · simp only [firstSurv, List.find?_cons_of_pos (p := fun z => decide (Survives s F₀ z))
          (by simpa using hs), Option.some.injEq] at hz
        subst hz
        refine ⟨List.mem_cons_self .., hs, fun w hw' _ => ?_⟩
        rcases List.mem_cons.1 hw' with rfl | hw'
        · exact .inl rfl
        · exact .inr hw'
      · simp only [firstSurv, List.find?_cons_of_neg (p := fun z => decide (Survives s F₀ z))
          (by simpa using hs)] at hz
        obtain ⟨h1, h2, h3⟩ := firstSurv_ancs n o (by omega) z hz
        refine ⟨List.mem_cons_of_mem _ h1, h2, fun w hw' hws => ?_⟩
        rcases List.mem_cons.1 hw' with rfl | hw'
        · exact absurd hws hs
        · exact h3 w hw' hws

theorem firstSurv_none {s : S3} {F₀ : Frames} {l : List Nat} (h : firstSurv s F₀ l = none) :
    ∀ w ∈ l, ¬ Survives s F₀ w := by
  intro w hw hs
  have := List.find?_eq_none.1 h w hw
  simp [hs] at this

theorem firstSurv_some {s : S3} {F₀ : Frames} {l : List Nat} {z : Nat}
    (h : firstSurv s F₀ l = some z) : z ∈ l ∧ Survives s F₀ z :=
  ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

/-- Conservation along a chain of origins (MM-03.3 §2, I2): a derived authority is within every
ancestor's footprint, with a mode not exceeding it. -/
theorem i2_chain {s : S3} (h2 : I2 s) :
    ∀ n b, b < n → ∀ (y : Authority) z, s.A[b]? = some y → z ∈ s.ancs b →
      ∃ x : Authority, s.A[z]? = some x ∧ ∀ p ∈ y.footprint, p ∈ x.footprint ∧ y.mode.le x.mode
  | 0, _, h, _, _, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, b, hb, y, z, hy, hz => by
    cases ho : y.origin with
    | none =>
      have : s.org b = none := by simp [S3.org, hy, ho]
      rw [S3.ancs, chain_none this] at hz; simp at hz
    | some o =>
      have hob : s.org b = some o := by simp [S3.org, hy, ho]
      obtain ⟨hlt, he⟩ : o < b ∧ s.ancs b = o :: s.ancs o := by
        rcases ancs_step hob with h | he
        · exact h
        · rw [he] at hz; simp at hz
      rw [he] at hz
      obtain ⟨x, hx, hh⟩ := h2 b y o hy ho
      rcases List.mem_cons.1 hz with rfl | hz
      · exact ⟨x, hx, hh⟩
      · obtain ⟨x', hx', hh'⟩ := i2_chain h2 n o (by omega) x z hx hz
        exact ⟨x', hx', fun p hp => ⟨(hh' p (hh p hp).1).1,
          Mode.le_trans (hh p hp).2 (hh' p (hh p hp).1).2⟩⟩

theorem exitEff_eq {s : S3} {f : Nat} {F₀ : Frames} (hF : s.F = f :: F₀) :
    exitEff s =
      { s with
        F := F₀
        D := fun q => (s.D q).map fun x => (firstSurv s F₀ (x :: s.ancs x)).getD x
        A := mapI (exitG s F₀) 0 s.A } := by
  simp [exitEff, hF]

theorem exit_A_get {s : S3} {f : Nat} {F₀ : Frames} (hF : s.F = f :: F₀) (j : Nat) :
    (exitEff s).A[j]? = (s.A[j]?).map (exitG s F₀ j) := by
  rw [exitEff_eq hF, getElem?_mapI]; simp

theorem exitG_same (s : S3) (F₀ : Frames) (a : Nat) (y : Authority) :
    (exitG s F₀ a y).mode = y.mode ∧ (exitG s F₀ a y).footprint = y.footprint ∧
    (exitG s F₀ a y).holder = y.holder := by
  unfold exitG; split
  · split <;> simp
  · simp

theorem exitG_active {s : S3} {F₀ : Frames} {a : Nat} {y : Authority} :
    (exitG s F₀ a y).active = true → Survives s F₀ a := by
  unfold exitG; split
  · intro; assumption
  · simp

theorem exitG_surv {s : S3} {F₀ : Frames} {a : Nat} {y : Authority} (hy : s.A[a]? = some y)
    (h : Survives s F₀ a) : (exitG s F₀ a y).active = true := by
  have hya : y.active = true := by unfold Survives at h; rw [hy] at h; exact h.1
  unfold exitG; simp only [h, ↓reduceIte]; split <;> simpa using hya

theorem exitG_active' {s : S3} {F₀ : Frames} {a : Nat} {y : Authority} (hy : s.A[a]? = some y)
    (h : (exitG s F₀ a y).active = true) : y.active = true := by
  have := exitG_active h; unfold Survives at this; rw [hy] at this; exact this.1

theorem exitG_origin {s : S3} {F₀ : Frames} {a : Nat} {y : Authority} :
    (exitG s F₀ a y).origin = y.origin ∨
    (Survives s F₀ a ∧ y.origin ≠ none ∧ (exitG s F₀ a y).origin = firstSurv s F₀ (s.ancs a)) := by
  unfold exitG; split
  · rename_i hs; split
    · exact .inl rfl
    · rename_i o ho; exact .inr ⟨hs, by simp [ho], rfl⟩
  · exact .inl rfl

/-- After the exit, the surviving ancestors of any authority are still its ancestors (A7). -/
theorem exit_ancs_keep {s : S3} {f : Nat} {F₀ : Frames} (hF : s.F = f :: F₀) :
    ∀ n x, x < n → ∀ w ∈ s.ancs x, Survives s F₀ w → w ∈ (exitEff s).ancs x
  | 0, _, h, _, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, x, hx, w, hw', hws => by
    cases hy : s.A[x]? with
    | none =>
      have : s.org x = none := by simp [S3.org, hy]
      rw [S3.ancs, chain_none this] at hw'; simp at hw'
    | some y =>
      cases ho : y.origin with
      | none =>
        have : s.org x = none := by simp [S3.org, hy, ho]
        rw [S3.ancs, chain_none this] at hw'; simp at hw'
      | some o =>
        have hob : s.org x = some o := by simp [S3.org, hy, ho]
        obtain ⟨hlt, hax⟩ : o < x ∧ s.ancs x = o :: s.ancs o := by
          rcases ancs_step hob with h | hax
          · exact h
          · rw [hax] at hw'; simp at hw'
        have e' : (exitEff s).org x = (exitG s F₀ x y).origin := by
          simp [S3.org, exit_A_get hF, hy]
        rcases exitG_origin (s := s) (F₀ := F₀) (a := x) (y := y) with e | ⟨-, -, e⟩
        · rw [e, ho] at e'
          rw [show (exitEff s).ancs x = o :: (exitEff s).ancs o from chain_cons e' hlt]
          rw [hax] at hw'
          rcases List.mem_cons.1 hw' with rfl | hw'
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (exit_ancs_keep hF n o (by omega) w hw' hws)
        · rw [e] at e'
          cases hz : firstSurv s F₀ (s.ancs x) with
          | none => exact absurd hws (firstSurv_none hz w hw')
          | some z =>
            rw [hz] at e'
            obtain ⟨hz1, -, hz3⟩ := firstSurv_ancs (x + 1) x (Nat.lt_succ_self x) z hz
            have hzx := chain_lt hz1
            rw [show (exitEff s).ancs x = z :: (exitEff s).ancs z from chain_cons e' hzx]
            rcases hz3 w hw' hws with rfl | hw''
            · exact List.mem_cons_self ..
            · exact List.mem_cons_of_mem _ (exit_ancs_keep hF n z (by omega) w hw'' hws)

/-- `exitFrame` preserves `Inv3` without `WF3` (MM-03.3 §4, O7; A1; A7). -/
theorem exit_preserves_inv3 {s s' : S3} (hinv : Inv3 s) (h : ExitStep s (.ok s')) : Inv3 s' := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  unfold ExitPre at hpre
  split at hpre
  · rename_i f F₀ hF
    obtain ⟨-, hR1, -⟩ := hpre
    obtain ⟨i1, i2, -, -⟩ := hinv
    have e := exitEff_eq hF
    have get := exit_A_get hF
    have get' : ∀ {j z}, (exitEff s).A[j]? = some z → ∃ z₀, s.A[j]? = some z₀ ∧
        z = exitG s F₀ j z₀ := fun {j z} hz => by
      rw [get] at hz
      cases h₀ : s.A[j]? with
      | none => rw [h₀] at hz; cases hz
      | some z₀ => rw [h₀] at hz; cases hz; exact ⟨z₀, rfl, rfl⟩
    have hP : (exitEff s).P = s.P := by rw [e]
    have hd : (exitEff s).dead = s.dead := by rw [e]
    have hFe : (exitEff s).F = F₀ := by rw [e]
    have keep := exit_ancs_keep hF
    refine ⟨fun a b x y p hab ha hb xa ya xp yp hnab hnba => ?_,
      fun b y a hb ho => ?_, fun q hq x hx => ?_, i4_always _⟩
    · obtain ⟨x₀, hx₀, rfl⟩ := get' ha; obtain ⟨y₀, hy₀, rfl⟩ := get' hb
      have sa := exitG_active xa; have sb := exitG_active ya
      have xa₀ : x₀.active = true := by unfold Survives at sa; rw [hx₀] at sa; exact sa.1
      have ya₀ : y₀.active = true := by unfold Survives at sb; rw [hy₀] at sb; exact sb.1
      rw [(exitG_same s F₀ a x₀).1, (exitG_same s F₀ b y₀).1]
      refine i1 a b x₀ y₀ p hab hx₀ hy₀ xa₀ ya₀ ((exitG_same s F₀ a x₀).2.1 ▸ xp)
        ((exitG_same s F₀ b y₀).2.1 ▸ yp) (fun hm => hnab ?_) (fun hm => hnba ?_)
      · exact keep (b + 1) b (Nat.lt_succ_self b) a hm sa
      · exact keep (a + 1) a (Nat.lt_succ_self a) b hm sb
    · obtain ⟨y₀, hy₀, rfl⟩ := get' hb
      obtain ⟨ym, yf, -⟩ := exitG_same s F₀ b y₀
      have lift : ∀ {a x₁}, s.A[a]? = some x₁ → (exitEff s).A[a]? = some (exitG s F₀ a x₁) :=
        fun h => by rw [get, h]; rfl
      rcases exitG_origin (s := s) (F₀ := F₀) (a := b) (y := y₀) with e' | ⟨-, -, e'⟩
      · obtain ⟨x₁, hx₁, hh⟩ := i2 b y₀ a hy₀ (e' ▸ ho)
        obtain ⟨xm, xf, -⟩ := exitG_same s F₀ a x₁
        exact ⟨_, lift hx₁, fun p hp => by rw [ym, xm, xf]; exact hh p (yf ▸ hp)⟩
      · rw [e'] at ho
        obtain ⟨x₁, hx₁, hh⟩ := i2_chain i2 (b + 1) b (Nat.lt_succ_self b) y₀ a hy₀
          (firstSurv_some ho).1
        obtain ⟨xm, xf, -⟩ := exitG_same s F₀ a x₁
        exact ⟨_, lift hx₁, fun p hp => by rw [ym, xm, xf]; exact hh p (yf ▸ hp)⟩
    · have hq₁ : ({ s with F := F₀ } : S3).Usable q :=
        (S3.Usable.congr (s := ({ s with F := F₀ } : S3)) hP hFe hd).1 hq
      have hq₀ : s.Usable q :=
        S3.Usable.mono (s := s) (s' := ({ s with F := F₀ } : S3)) rfl
          (fun g hg => by rw [hF]; exact List.mem_cons_of_mem _ hg) (fun _ h => h) hq₁
      rw [e] at hx; simp only [List.mem_map] at hx
      obtain ⟨x₀, hx₀, rfl⟩ := hx
      have hne' := hR1 q (List.mem_range.2 hq₀.lt) hq₁ x₀ hx₀
      cases hz : firstSurv s F₀ (x₀ :: s.ancs x₀) with
      | none => exact absurd hz hne'
      | some z =>
        simp only [Option.getD_some]
        obtain ⟨-, hzs⟩ := firstSurv_some hz
        have hzA : ∃ y, s.A[z]? = some y := by
          unfold Survives at hzs
          cases hy : s.A[z]? with
          | none => rw [hy] at hzs; exact hzs.elim
          | some y => exact ⟨y, rfl⟩
        obtain ⟨y, hy⟩ := hzA
        exact ⟨_, by rw [get, hy]; rfl, exitG_surv hy hzs⟩
  · exact hpre.elim

/-- `exitFrame` preserves `WF3` and `Inv3` (MM-03.3 §4, O7; §10; A4; A5; A7). -/
theorem exit_preserves {s s' : S3} (hwf : WF3 s) (hinv : Inv3 s) (h : ExitStep s (.ok s')) :
    WF3 s' ∧ Inv3 s' := by
  have hinv' := exit_preserves_inv3 hinv h
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  unfold ExitPre at hpre
  split at hpre
  · rename_i f F₀ hF
    obtain ⟨hne, -, -⟩ := hpre
    have e := exitEff_eq hF
    have get := exit_A_get hF
    have get' : ∀ {j z}, (exitEff s).A[j]? = some z → ∃ z₀, s.A[j]? = some z₀ ∧
        z = exitG s F₀ j z₀ := fun {j z} hz => by
      rw [get] at hz
      cases h₀ : s.A[j]? with
      | none => rw [h₀] at hz; cases hz
      | some z₀ => rw [h₀] at hz; cases hz; exact ⟨z₀, rfl, rfl⟩
    have hP : (exitEff s).P = s.P := by rw [e]
    have hd : (exitEff s).dead = s.dead := by rw [e]
    have hn : (exitEff s).nF = s.nF := by rw [e]
    have hFe : (exitEff s).F = F₀ := by rw [e]
    have live₁ : ∀ hh, HolderLive (exitEff s) hh ↔ HolderLive ({ s with F := F₀ } : S3) hh :=
      HolderLive.congr hP hFe hd
    have hnd := List.nodup_cons.1 (hF ▸ hwf.nodup)
    refine ⟨⟨fun b y a hb ho => ?_, fun a x hx l hl => ?_, hFe ▸ hne, hFe ▸ hnd.2,
      fun g hg => ?_, hP ▸ hn ▸ hwf.ownerFrame, hP ▸ hwf.ownerPlace, hP ▸ hd ▸ hwf.parts,
      fun a y hy ya => ?_⟩, hinv'⟩
    · obtain ⟨y₀, hy₀, rfl⟩ := get' hb
      rcases exitG_origin (s := s) (F₀ := F₀) (a := b) (y := y₀) with e' | ⟨-, -, e'⟩
      · exact hwf.origin b y₀ a hy₀ (e' ▸ ho)
      · rw [e'] at ho; exact chain_lt (firstSurv_some ho).1
    · obtain ⟨x₀, hx₀, rfl⟩ := get' hx
      rw [hP]; exact hwf.fp a x₀ hx₀ l ((exitG_same s F₀ a x₀).2.1 ▸ hl)
    · rw [hFe] at hg; rw [hn]; exact hwf.frames g (hF ▸ List.mem_cons_of_mem _ hg)
    · obtain ⟨y₀, hy₀, rfl⟩ := get' hy
      have hs := exitG_active ya
      rw [(exitG_same s F₀ a y₀).2.2, live₁]
      unfold Survives at hs; rw [hy₀] at hs; exact hs.2
  · exact hpre.elim

/-- `exitFrame_releases_all` (MM-03.3 §4, O7; §10): after the exit, every active authority has
a live holder; none is held by the exited frame. The stack has no duplicate (a clause of `WF3`):
otherwise the exited frame is still on the stack and its authorities survive
(`exit_duplicate_frame`). -/
theorem exitFrame_releases_all {s s' : S3} {f : Nat} {F₀ : Frames} (hnd : s.F.Nodup)
    (hF : s.F = f :: F₀) (h : ExitStep s (.ok s')) :
    ∀ (j : Nat) (y : Authority), s'.A[j]? = some y → y.active = true →
      HolderLive s' y.holder ∧ y.holder ≠ .frame f := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
  intro j y hy ya
  rw [exit_A_get hF] at hy
  obtain ⟨y₀, hy₀, rfl⟩ := Option.map_eq_some_iff.1 hy
  have hs := exitG_active ya
  unfold Survives at hs; rw [hy₀] at hs
  obtain ⟨-, hl⟩ := hs
  rw [(exitG_same s F₀ j y₀).2.2]
  have e := exitEff_eq hF
  refine ⟨(HolderLive.congr (s := ({ s with F := F₀ } : S3)) (s' := exitEff s) (by rw [e])
    (by rw [e]) (by rw [e]) _).2 hl, fun he => ?_⟩
  rw [he] at hl
  exact (List.nodup_cons.1 (hF ▸ hnd)).1 hl

/-- `exitFrame_kills_locals` (MM-03.3.1; MM-03.3 §4, O7; A5): after the exit, every usable place
was usable before; a place owned by the exited frame is no longer usable; and no active
authority is held by a holder that is no longer live. -/
theorem exitFrame_kills_locals {s s' : S3} {f : Nat} {F₀ : Frames} (hwf : WF3 s) (hinv : Inv3 s)
    (hF : s.F = f :: F₀) (h : ExitStep s (.ok s')) :
    (∀ q, s'.Usable q → s.Usable q) ∧
    (∀ (q : Nat) (pl : Place), s.P[q]? = some pl → pl.owner = .frame f → ¬ s'.Usable q) ∧
    (∀ (j : Nat) (y : Authority), s'.A[j]? = some y → y.active = true → HolderLive s' y.holder) := by
  have hp := exit_preserves hwf hinv h
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
  have e := exitEff_eq hF
  have hnd := List.nodup_cons.1 (hF ▸ hwf.nodup)
  refine ⟨fun q hq => ?_, fun q pl hq ho hu => ?_, hp.1.poss⟩
  · exact S3.Usable.mono (by rw [e]) (fun g hg => by rw [e] at hg; exact hF ▸ List.mem_cons_of_mem _ hg)
      (fun _ h => by rw [e] at h; exact h) hq
  · cases hu with
    | frame hpl _ ho' hf =>
      have : (exitEff s).P = s.P := by rw [e]
      rw [this, hq] at hpl; cases hpl; rw [ho] at ho'; cases ho'
      rw [e] at hf; exact hnd.1 hf
    | place hpl _ ho' _ =>
      have : (exitEff s).P = s.P := by rw [e]
      rw [this, hq] at hpl; cases hpl; rw [ho] at ho'; cases ho'

/-- `exitFrame_reanchors_to_origin` (MM-03.3.7; A7): every anchor of a place usable after the
exit is replaced by the first surviving authority among itself and its ancestors along `origin`,
which is valid after the exit. -/
theorem exitFrame_reanchors_to_origin {s s' : S3} {f : Nat} {F₀ : Frames} (hwf : WF3 s)
    (hinv : Inv3 s) (hF : s.F = f :: F₀) (h : ExitStep s (.ok s')) :
    ∀ q, s'.Usable q → ∀ x ∈ s.D q, ∃ z, firstSurv s F₀ (x :: s.ancs x) = some z ∧
      (z = x ∨ z ∈ s.ancs x) ∧ z ∈ s'.D q ∧ s'.Active z := by
  have hp := exit_preserves hwf hinv h
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  unfold ExitPre at hpre; rw [hF] at hpre
  obtain ⟨-, hR1, -⟩ := hpre
  have e := exitEff_eq hF
  intro q hq x hx
  have hq₁ : ({ s with F := F₀ } : S3).Usable q :=
    (S3.Usable.congr (s := ({ s with F := F₀ } : S3)) (by rw [e]) (by rw [e]) (by rw [e])).1 hq
  have hne := hR1 q (List.mem_range.2 hq₁.lt) hq₁ x hx
  cases hz : firstSurv s F₀ (x :: s.ancs x) with
  | none => exact absurd hz hne
  | some z =>
    have hmem : z ∈ (exitEff s).D q := by
      rw [e]; exact List.mem_map.2 ⟨x, hx, by simp [hz]⟩
    refine ⟨z, rfl, ?_, hmem, hp.2.2.2.1 q hq z hmem⟩
    exact List.mem_cons.1 (firstSurv_some hz).1

/-- `dependent_cannot_escape_frame` (MM-03.3.6; MM-03.3 §4, O7.3; §10): after the exit, every
anchor of a usable place is active and held by a live holder, so by no authority of the exited
frame. -/
theorem dependent_cannot_escape_frame {s s' : S3} {f : Nat} {F₀ : Frames} (hwf : WF3 s)
    (hinv : Inv3 s) (hF : s.F = f :: F₀) (h : ExitStep s (.ok s')) :
    ∀ q, s'.Usable q → ∀ x ∈ s'.D q, ∃ y, s'.A[x]? = some y ∧ y.active = true ∧
      HolderLive s' y.holder ∧ y.holder ≠ .frame f := by
  intro q hq x hx
  obtain ⟨y, hy, ya⟩ := (exit_preserves hwf hinv h).2.2.2.1 q hq x hx
  exact ⟨y, hy, ya, exitFrame_releases_all hwf.nodup hF h x y hy ya⟩

/-! ## Release of authorities whose holder died (A4, A5, A6) -/

/-- Releases every authority whose holder is no longer live (A4, A5): its value has ended or its
storage is dead. -/
def cleanup (s : S3) : S3 :=
  { s with A := s.A.map fun y => if HolderLive s y.holder then y else { y with active := false } }

/-- The authorities of `s₁` are those of `s`, some of them released. -/
def OnlyReleases (s s₁ : S3) : Prop :=
  s₁.A.length = s.A.length ∧ ∀ (j : Nat) (z : Authority), s₁.A[j]? = some z →
    ∃ y, s.A[j]? = some y ∧ z.mode = y.mode ∧ z.origin = y.origin ∧ z.footprint = y.footprint ∧
      z.holder = y.holder ∧ (z.active = true → y.active = true)

theorem OnlyReleases.org {s s₁ : S3} (h : OnlyReleases s s₁) : s₁.org = s.org := by
  funext j; simp only [S3.org]
  cases hz : s₁.A[j]? with
  | none =>
    have : s.A.length ≤ j := by have := List.getElem?_eq_none_iff.1 hz; rw [h.1] at this; exact this
    rw [List.getElem?_eq_none_iff.2 this]
  | some z => obtain ⟨y, hy, -, ho, -⟩ := h.2 j z hz; simp [hy, ho]

theorem cleanup_get (s : S3) (j : Nat) : (cleanup s).A[j]? =
    (s.A[j]?).map fun y => if HolderLive s y.holder then y else { y with active := false } := by
  simp [cleanup]

theorem cleanup_releases {s : S3} : OnlyReleases s (cleanup s) := by
  refine ⟨by simp [cleanup], fun j z hz => ?_⟩
  rw [cleanup_get] at hz
  cases hy : s.A[j]? with
  | none => rw [hy] at hz; cases hz
  | some y =>
    rw [hy] at hz; simp only [Option.map_some, Option.some.injEq] at hz; subst hz
    refine ⟨y, rfl, ?_⟩; split <;> simp_all

theorem OnlyReleases.trans {s s₁ s₂ : S3} (h₁ : OnlyReleases s s₁) (h₂ : OnlyReleases s₁ s₂) :
    OnlyReleases s s₂ := by
  refine ⟨h₂.1.trans h₁.1, fun j z hz => ?_⟩
  obtain ⟨y₁, hy₁, m₁, o₁, f₁, h₁', a₁⟩ := h₂.2 j z hz
  obtain ⟨y, hy, m, o, f, hh, a⟩ := h₁.2 j y₁ hy₁
  exact ⟨y, hy, m₁.trans m, o₁.trans o, f₁.trans f, h₁'.trans hh, fun h => a (a₁ h)⟩

/-- `Inv3` part of `releases_preserve`, without `WF3` (A1): releasing authorities and then those
whose holder died preserves `Inv3`, provided no usable place keeps an anchor that is
released. -/
theorem releases_preserve_inv3 {s s₁ : S3} (hinv : Inv3 s) (hr : OnlyReleases s s₁)
    (hI3 : ∀ q, s₁.Usable q → ∀ x ∈ s₁.D q, (cleanup s₁).Active x) : Inv3 (cleanup s₁) := by
  have hc := hr.trans cleanup_releases
  obtain ⟨i1, i2, -, -⟩ := hinv
  have hancs : (cleanup s₁).ancs = s.ancs := by funext j; simp only [S3.ancs, hc.org]
  refine ⟨fun a b x y p hab ha hb xa ya xp yp hnab hnba => ?_, fun b y a hb ho => ?_,
    fun q hq x hx => hI3 q ((S3.Usable.congr (s := s₁) (s' := cleanup s₁) rfl rfl rfl).1 hq) x hx,
    i4_always _⟩
  · obtain ⟨x₀, hx₀, m₁, -, f₁, -, a₁⟩ := hc.2 a x ha
    obtain ⟨y₀, hy₀, m₂, -, f₂, -, a₂⟩ := hc.2 b y hb
    rw [hancs] at hnab hnba; rw [m₁, m₂]
    exact i1 a b x₀ y₀ p hab hx₀ hy₀ (a₁ xa) (a₂ ya) (f₁ ▸ xp) (f₂ ▸ yp) hnab hnba
  · obtain ⟨y₀, hy₀, m₀, e, f₀, -⟩ := hc.2 b y hb
    obtain ⟨x₁, hx₁, hh⟩ := i2 b y₀ a hy₀ (e ▸ ho)
    have hlen : a < (cleanup s₁).A.length := by rw [hc.1]; exact lt_of_getElem? hx₁
    obtain ⟨x', hx'⟩ : ∃ x', (cleanup s₁).A[a]? = some x' :=
      ⟨_, (List.getElem?_eq_some_iff.2 ⟨hlen, rfl⟩)⟩
    obtain ⟨x₂, hx₂, mx, -, fx, -⟩ := hc.2 a x' hx'
    rw [hx₁] at hx₂; cases hx₂
    exact ⟨x', hx', fun p hp => by rw [m₀, mx, fx]; exact hh p (f₀ ▸ hp)⟩

/-- Releasing authorities, marking places dead, and then releasing those whose holder died
preserves `WF3` and `Inv3`, provided the dead marks respect parts and no usable place keeps an
anchor that is released. Shared by `endUse` and `free` (A6). -/
theorem releases_preserve {s s₁ : S3} (hwf : WF3 s) (hinv : Inv3 s) (hr : OnlyReleases s s₁)
    (hP : s₁.P = s.P) (hF : s₁.F = s.F) (hn : s₁.nF = s.nF)
    (hparts : ∀ (q : Nat) (pl : Place) (r : Nat), s.P[q]? = some pl → pl.parent = some r →
      s₁.dead r = s₁.dead q)
    (hI3 : ∀ q, s₁.Usable q → ∀ x ∈ s₁.D q, (cleanup s₁).Active x) :
    WF3 (cleanup s₁) ∧ Inv3 (cleanup s₁) := by
  have hc := hr.trans cleanup_releases
  have cP : (cleanup s₁).P = s.P := hP
  have cF : (cleanup s₁).F = s.F := hF
  have live₁ : ∀ hh, HolderLive (cleanup s₁) hh ↔ HolderLive s₁ hh := HolderLive.congr rfl rfl rfl
  refine ⟨⟨fun b y a hb ho => ?_, fun a x hx l hl => ?_, cF ▸ hwf.ne, cF ▸ hwf.nodup,
    by rw [cF, show (cleanup s₁).nF = s.nF from hn]; exact hwf.frames,
    by rw [cP, show (cleanup s₁).nF = s.nF from hn]; exact hwf.ownerFrame,
    by rw [cP]; exact hwf.ownerPlace, fun q pl r hq hp => ?_, fun a y hy ya => ?_⟩,
    releases_preserve_inv3 hinv hr hI3⟩
  · obtain ⟨y₀, hy₀, -, e, -⟩ := hc.2 b y hb; exact hwf.origin b y₀ a hy₀ (e ▸ ho)
  · obtain ⟨x₀, hx₀, -, -, e, -⟩ := hc.2 a x hx; rw [cP]; exact hwf.fp a x₀ hx₀ l (e ▸ hl)
  · rw [cP] at hq
    obtain ⟨pr, hpr, hlt, ho, -⟩ := hwf.parts q pl r hq hp
    exact ⟨pr, by rw [cP]; exact hpr, hlt, ho, hparts q pl r hq hp⟩
  · rw [cleanup_get] at hy
    cases hz : s₁.A[a]? with
    | none => rw [hz] at hy; cases hy
    | some z =>
      rw [hz] at hy; simp only [Option.map_some, Option.some.injEq] at hy
      split at hy
      · subst hy; exact (live₁ _).2 ‹_›
      · subst hy; simp at ya

/-! ## `writeShared` (A9) -/

/-- Preconditions of `writeShared` (A9), the only mutation permitted from an `Observe`
authority: `a` exercisable (A2); on each leaf, a present effective mode of `a`, a
`SharedMutable` leaf (MM-03.3.8), valid dependencies. -/
def WriteSharedPre (k : K) (s : S3) (a : Nat) (ls : List Nat) : Prop :=
  s.Exercisable a ∧ ∀ p ∈ ls, effective s a p ≠ none ∧ k.SharedMutable p ∧ DepsValid s p

instance (k : K) [DecidablePred k.SharedMutable] (s : S3) (a : Nat) (ls : List Nat) :
    Decidable (WriteSharedPre k s a ls) := by
  unfold WriteSharedPre; infer_instance

/-- `writeShared` as a relation (A9): written leaves become `Init`; no authority changes. -/
def WriteSharedStep (k : K) (a : Nat) (ls : List Nat) (s : S3) : Outcome3 S3 → Prop :=
  Guarded (WriteSharedPre k s a ls) (write3Eff s ls)

/-- `writeShared_only_shared` (A9): a shared write only touches `SharedMutable` leaves. -/
theorem writeShared_only_shared {k : K} {s s' : S3} {a : Nat} {ls : List Nat}
    (h : WriteSharedStep k a ls s (.ok s')) : ∀ p ∈ ls, k.SharedMutable p :=
  fun p hp => ((Guarded.ok_iff.1 h).1.2 p hp).2.1

/-- `writeShared` preserves `WF3` and `Inv3` (A9: it does not weaken I1). -/
theorem writeShared_preserves {k : K} {s s' : S3} {a : Nat} {ls : List Nat} (hwf : WF3 s)
    (hinv : Inv3 s) (h : WriteSharedStep k a ls s (.ok s')) : WF3 s' ∧ Inv3 s' := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
  exact ⟨hwf.of_eq rfl rfl rfl rfl rfl, hinv.1, hinv.2.1, fun q hq x hx =>
    hinv.2.2.1 q ((S3.Usable.congr (s := s) (s' := write3Eff s ls) rfl rfl rfl).1 hq) x hx,
    i4_always _⟩

/-! ## Dynamic pinning (A8) -/

/-- Preconditions of `pin p` (A8): `p` usable, exercisable `Modify` on `p` (A2 requires an
exercisable right for `pin` without naming its mode; `Modify` is a choice: the external use, a
DMA, writes the storage). -/
def PinPre (s : S3) (p : Nat) : Prop := s.Usable p ∧ HasRight s .modify p

instance (s : S3) (p : Nat) : Decidable (PinPre s p) := by unfold PinPre; infer_instance

/-- Effect of `pin p` / `unpin p` (A8): the leaves of `p` become pinned or unpinned. -/
def pinEff (s : S3) (p : Nat) (b : Bool) : S3 :=
  { s with pin := fun l => if l ∈ footprint s.P p then b else s.pin l }

/-- `pin` as a relation (A8). -/
def PinStep (p : Nat) (s : S3) : Outcome3 S3 → Prop := Guarded (PinPre s p) (pinEff s p true)

/-- Preconditions of `unpin p` (A8): the external use of every leaf of `p` is done
(`ExternalDone`, MM-03.3.8). -/
def UnpinPre (k : K) (s : S3) (p : Nat) : Prop :=
  ∀ l ∈ footprint s.P p, k.ExternalDone l

instance (k : K) [DecidablePred k.ExternalDone] (s : S3) (p : Nat) :
    Decidable (UnpinPre k s p) := by
  unfold UnpinPre; infer_instance

/-- `unpin` as a relation (A8). -/
def UnpinStep (k : K) (p : Nat) (s : S3) : Outcome3 S3 → Prop :=
  Guarded (UnpinPre k s p) (pinEff s p false)

/-- Pinning changes neither authorities nor places: `WF3` and `Inv3` are preserved (A8). -/
theorem pinEff_preserves {s : S3} {p : Nat} {b : Bool} (hwf : WF3 s) (hinv : Inv3 s) :
    WF3 (pinEff s p b) ∧ Inv3 (pinEff s p b) :=
  ⟨hwf.of_eq rfl rfl rfl rfl rfl, hinv.1, hinv.2.1, fun q hq x hx =>
    hinv.2.2.1 q ((S3.Usable.congr (s := s) (s' := pinEff s p b) rfl rfl rfl).1 hq) x hx,
    i4_always _⟩

/-! ## `endUse` (A6) -/

/-- The value at `p` ends (A6), before releasing authorities whose holder died: the leaves of
`p` become `Uninit`; the authorities held by `p` or one of its parts are released; the anchors
of `p` and its parts are removed; the places owned by `p` or one of its parts are logically
dead. -/
def endUseS (s : S3) (p : Nat) : S3 :=
  { s with
    I := fun l => if l ∈ footprint s.P p then .uninit else s.I l
    D := fun q => if partOf s.P q p then [] else s.D q
    dead := fun q => s.dead q || match s.P[q]? with
      | some pl => decide (heldIn s.P p pl.owner)
      | none => false
    A := s.A.map fun y => if heldIn s.P p y.holder then { y with active := false } else y }

/-- Effect of `endUse p` (A6): `endUseS`, then the authorities whose holder died are released.
No storage is released: `freed` is unchanged. -/
def endUseEff (s : S3) (p : Nat) : S3 := cleanup (endUseS s p)

/-- Leaves that end with the value at `p` (A6): those of `p`, and those of places that stop
being usable. -/
def EndingLeaf (s : S3) (p l : Nat) : Prop :=
  l ∈ footprint s.P p ∨ (s.Usable l ∧ ¬ (endUseS s p).Usable l)

instance (s : S3) (p l : Nat) : Decidable (EndingLeaf s p l) := by
  unfold EndingLeaf; infer_instance

/-- Root of the value at `p` (A6, pass-1 arbitrage 2): an authority without origin covering a
leaf of `p`. -/
def IsRootOf (s : S3) (p : Nat) (y : Authority) : Prop :=
  y.origin = none ∧ ∃ l ∈ footprint s.P p, l ∈ y.footprint

instance (s : S3) (p : Nat) (y : Authority) : Decidable (IsRootOf s p y) := by
  unfold IsRootOf; infer_instance

/-- Authority `a` is held within the value at `p` (A4): by `p` or one of its parts. -/
def HeldWithin (s : S3) (p a : Nat) : Prop := OptP (s.A[a]?) (fun z => heldIn s.P p z.holder) False

instance (s : S3) (p a : Nat) : Decidable (HeldWithin s p a) := by
  unfold HeldWithin; infer_instance

/-- Authority `j` does not block the end of the value at `p` (A6): if it is an active derived
authority on an ending leaf, or descending from an authority held within `p` (which the end
releases, MM-03.3 §3, O3.2), it is held within `p` or its holder dies. -/
def EndUseAccessOK (s : S3) (p j : Nat) : Prop :=
  OptP (s.A[j]?) (fun y => y.active = true → y.origin ≠ none →
    ((∃ l ∈ y.footprint, EndingLeaf s p l) ∨ ∃ a ∈ s.ancs j, HeldWithin s p a) →
      heldIn s.P p y.holder ∨ ¬ HolderLive (endUseS s p) y.holder) True

instance (s : S3) (p j : Nat) : Decidable (EndUseAccessOK s p j) := by
  unfold EndUseAccessOK OptP; split <;> infer_instance

/-- Anchor `x` survives the end of the value at `p` (A6): not held within `p`, not the root of
`p`, with a holder that stays live. -/
def EndUseAnchorOK (s : S3) (p x : Nat) : Prop :=
  OptP (s.A[x]?) (fun y => ¬ heldIn s.P p y.holder ∧ ¬ IsRootOf s p y ∧
    HolderLive (endUseS s p) y.holder) True

instance (s : S3) (p x : Nat) : Decidable (EndUseAnchorOK s p x) := by
  unfold EndUseAnchorOK OptP; split <;> infer_instance

/-- Preconditions of `endUse p` (A6). Usability of the anchored places is read after the end:
a place that dies with `p` has no usable dependent afterwards. In order: `p` usable;
exercisable `Modify` on `p` (A2);
no active derived authority on an ending leaf held elsewhere than in `p` and staying live; no
usable place anchored on an authority held by `p`, on its root, or held by a holder that dies;
no ending leaf pinned (dynamically, A8, or statically, `Pinned`) without `ExternalDone`. The
ending leaves include those of the owned places, which die (A6). -/
def EndUsePre (k : K) (s : S3) (p : Nat) : Prop :=
  s.Usable p ∧ HasRight s .modify p ∧
  (∀ j ∈ List.range s.A.length, EndUseAccessOK s p j) ∧
  (∀ q ∈ List.range s.P.length, (endUseS s p).Usable q → ∀ x ∈ (endUseS s p).D q,
    EndUseAnchorOK s p x) ∧
  (∀ l ∈ List.range s.P.length, EndingLeaf s p l → (s.pin l = true ∨ k.Pinned l) →
    k.ExternalDone l)

instance (k : K) [DecidablePred k.Pinned] [DecidablePred k.ExternalDone] (s : S3) (p : Nat) :
    Decidable (EndUsePre k s p) := by
  unfold EndUsePre; infer_instance

/-- `endUse` as a relation (A6). -/
def EndUseStep (k : K) (p : Nat) (s : S3) : Outcome3 S3 → Prop :=
  Guarded (EndUsePre k s p) (endUseEff s p)

theorem endUseS_releases (s : S3) (p : Nat) : OnlyReleases s (endUseS s p) := by
  refine ⟨by simp [endUseS], fun j z hz => ?_⟩
  simp only [endUseS, List.getElem?_map] at hz
  cases hy : s.A[j]? with
  | none => rw [hy] at hz; cases hz
  | some y =>
    rw [hy] at hz; simp only [Option.map_some, Option.some.injEq] at hz; subst hz
    refine ⟨y, rfl, ?_⟩; split <;> simp_all

theorem endUseS_get (s : S3) (p j : Nat) : (endUseS s p).A[j]? =
    (s.A[j]?).map fun y => if heldIn s.P p y.holder then { y with active := false } else y := by
  simp [endUseS]

/-- Under `EndUsePre` (A6), every anchor of a place usable after the end stays active. -/
theorem endUse_anchors {k : K} {s : S3} {p : Nat} (hinv : Inv3 s) (hpre : EndUsePre k s p) :
    ∀ q, (endUseS s p).Usable q → ∀ x ∈ (endUseS s p).D q, (cleanup (endUseS s p)).Active x := by
  obtain ⟨-, -, -, hanc, -⟩ := hpre
  intro q hq x hx
  have hq₀ : s.Usable q := S3.Usable.mono (s := s) (s' := endUseS s p) rfl (fun _ h => h)
    (fun q h => by simp only [endUseS, Bool.or_eq_false_iff] at h; exact h.1) hq
  have hx₀ : x ∈ s.D q := by
    simp only [endUseS] at hx; split at hx
    · simp at hx
    · exact hx
  obtain ⟨y, hy, ya⟩ := hinv.2.2.1 q hq₀ x hx₀
  have hc := hanc q (List.mem_range.2 hq₀.lt) hq x hx
  unfold EndUseAnchorOK OptP at hc
  rw [hy] at hc; obtain ⟨hnh, -, hl⟩ := hc
  refine ⟨_, by rw [cleanup_get, endUseS_get, hy]; rfl, ?_⟩
  simp only [hnh, ↓reduceIte]
  have : HolderLive (endUseS s p) y.holder := hl
  simp only [this, ↓reduceIte, ya]

/-- `endUse` preserves `WF3` and `Inv3` (A6). -/
theorem endUse_preserves {k : K} {s s' : S3} {p : Nat} (hwf : WF3 s) (hinv : Inv3 s)
    (h : EndUseStep k p s (.ok s')) : WF3 s' ∧ Inv3 s' := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  refine releases_preserve hwf hinv (endUseS_releases s p) rfl rfl rfl ?_ (endUse_anchors hinv hpre)
  intro q pl r hq hp
  obtain ⟨pr, hpr, -, ho, hd⟩ := hwf.parts q pl r hq hp
  simp only [endUseS, hq, hpr, ho, hd]

/-- `endUse` preserves `Inv3` without `WF3` (A1; A6). -/
theorem endUse_preserves_inv3 {k : K} {s s' : S3} {p : Nat} (hinv : Inv3 s)
    (h : EndUseStep k p s (.ok s')) : Inv3 s' := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  exact releases_preserve_inv3 hinv (endUseS_releases s p) (endUse_anchors hinv hpre)

/-- `endUse_no_dealloc_event` (A6): `endUse` releases no storage and kills no owned place
physically: `freed` is unchanged. -/
theorem endUse_no_dealloc_event {k : K} {s s' : S3} {p : Nat} (h : EndUseStep k p s (.ok s')) :
    s'.freed = s.freed := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; rfl

/-- `endUse_preserves_dependents` (A6): no usable dependent loses an anchor; a usable place other
than a part of `p` keeps its anchors, all valid. -/
theorem endUse_preserves_dependents {k : K} {s s' : S3} {p : Nat} (hwf : WF3 s) (hinv : Inv3 s)
    (h : EndUseStep k p s (.ok s')) :
    ∀ q, s'.Usable q → ¬ partOf s.P q p → s'.D q = s.D q ∧ ∀ x ∈ s'.D q, s'.Active x := by
  have hp := endUse_preserves hwf hinv h
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
  intro q hq hnp
  exact ⟨by simp [endUseEff, cleanup, endUseS, hnp], hp.2.2.2.1 q hq⟩

/-! ## `free` (A6) -/

/-- The holder is a place (A4, A5). -/
def Holder.isPlace : Holder → Bool
  | .place _ => true
  | .frame _ => false

/-- The place `p` is an owned root (A6, owned place): no parent, owned by a place. -/
def OwnedRoot (s : S3) (p : Nat) : Prop :=
  OptP (s.P[p]?) (fun pl => pl.parent = none ∧ pl.owner.isPlace = true) False

instance (s : S3) (p : Nat) : Decidable (OwnedRoot s p) := by
  unfold OwnedRoot; infer_instance

/-- Storage at `p` released (A6), before releasing authorities whose holder died: `p` and its
parts are dead, `p` is freed, every authority covering a leaf of `p` or held within `p` is
released, the anchors of `p` and its parts are removed. -/
def freeS (s : S3) (p : Nat) : S3 :=
  { s with
    D := fun q => if partOf s.P q p then [] else s.D q
    dead := fun q => s.dead q || decide (partOf s.P q p)
    freed := fun q => s.freed q || decide (q = p)
    A := s.A.map fun y => if (∃ l ∈ y.footprint, l ∈ footprint s.P p) ∨ heldIn s.P p y.holder then
      { y with active := false } else y }

/-- Effect of `free p auth` (A6): `freeS`, then the authorities whose holder died are
released. -/
def freeEff (s : S3) (p : Nat) : S3 := cleanup (freeS s p)

/-- Leaves whose storage ends with the release of `p` (A6): those of `p`, and those of places
that stop being usable, such as the places owned by `p`. -/
def FreedLeaf (s : S3) (p l : Nat) : Prop :=
  l ∈ footprint s.P p ∨ (s.Usable l ∧ ¬ (freeS s p).Usable l)

instance (s : S3) (p l : Nat) : Decidable (FreedLeaf s p l) := by
  unfold FreedLeaf; infer_instance

/-- Authority `a` is deactivated by the release of `p` (A6): it covers a leaf of `p` or is held
within `p`. -/
def FreeDeact (s : S3) (p a : Nat) : Prop :=
  OptP (s.A[a]?) (fun z => (∃ l ∈ z.footprint, l ∈ footprint s.P p) ∨ heldIn s.P p z.holder) False

instance (s : S3) (p a : Nat) : Decidable (FreeDeact s p a) := by
  unfold FreeDeact; infer_instance

/-- Authority `j` does not block the release of `p` (A6): if it is an active derived authority on
a freed leaf, or descending from an authority the release deactivates (MM-03.3 §3, O3.2), it is
held within `p` or its holder dies. -/
def FreeAccessOK (s : S3) (p j : Nat) : Prop :=
  OptP (s.A[j]?) (fun y => y.active = true → y.origin ≠ none →
    ((∃ l ∈ y.footprint, FreedLeaf s p l) ∨ ∃ a ∈ s.ancs j, FreeDeact s p a) →
      heldIn s.P p y.holder ∨ ¬ HolderLive (freeS s p) y.holder) True

instance (s : S3) (p j : Nat) : Decidable (FreeAccessOK s p j) := by
  unfold FreeAccessOK OptP; split <;> infer_instance

/-- Anchor `x` survives the release of `p` (A6): it covers no leaf of `p`, is not held within
`p`, and its holder stays live. -/
def FreeAnchorOK (s : S3) (p x : Nat) : Prop :=
  OptP (s.A[x]?) (fun y => ¬ (∃ l ∈ y.footprint, l ∈ footprint s.P p) ∧ ¬ heldIn s.P p y.holder ∧
    HolderLive (freeS s p) y.holder) True

instance (s : S3) (p x : Nat) : Decidable (FreeAnchorOK s p x) := by
  unfold FreeAnchorOK OptP; split <;> infer_instance

/-- Preconditions of `free p auth` (A6), in order: `p` deallocable by the allocator contract
(`Deallocable`) and `auth` a compatible deallocation authority (`FreeCompat`, MM-03.3.8); `p` a
usable owned root (a part is not a unit of storage, and `WF3` gives a part the `dead` flag of its
parent); exercisable `Modify` on `p` (A2); no active derived authority on a freed leaf, or
descending from a deactivated authority, held elsewhere and staying live; no usable place
anchored on an authority covering `p`, held within `p`, or whose holder dies; no freed leaf
pinned, dynamically or statically (A6 forbids any pinned leaf for `free`, which also implies
the rejection of A8). -/
def FreePre (k : K) (s : S3) (p auth : Nat) : Prop :=
  k.Deallocable p ∧ k.FreeCompat p auth ∧ s.Usable p ∧ OwnedRoot s p ∧ HasRight s .modify p ∧
  (∀ j ∈ List.range s.A.length, FreeAccessOK s p j) ∧
  (∀ q ∈ List.range s.P.length, (freeS s p).Usable q → ∀ x ∈ (freeS s p).D q,
    FreeAnchorOK s p x) ∧
  (∀ l ∈ List.range s.P.length, FreedLeaf s p l → s.pin l = false ∧ ¬ k.Pinned l)

instance (k : K) [DecidablePred k.Pinned]
    [DecidablePred k.Deallocable] [∀ p a, Decidable (k.FreeCompat p a)] (s : S3) (p auth : Nat) :
    Decidable (FreePre k s p auth) := by
  unfold FreePre; infer_instance

/-- `free` as a relation (A6). -/
def FreeStep (k : K) (p auth : Nat) (s : S3) : Outcome3 S3 → Prop :=
  Guarded (FreePre k s p auth) (freeEff s p)

theorem freeS_get (s : S3) (p j : Nat) : (freeS s p).A[j]? = (s.A[j]?).map fun y =>
    if (∃ l ∈ y.footprint, l ∈ footprint s.P p) ∨ heldIn s.P p y.holder then
      { y with active := false } else y := by
  simp [freeS]

theorem freeS_releases (s : S3) (p : Nat) : OnlyReleases s (freeS s p) := by
  refine ⟨by simp [freeS], fun j z hz => ?_⟩
  rw [freeS_get] at hz
  cases hy : s.A[j]? with
  | none => rw [hy] at hz; cases hz
  | some y =>
    rw [hy] at hz; simp only [Option.map_some, Option.some.injEq] at hz; subst hz
    refine ⟨y, rfl, ?_⟩; split <;> simp_all

theorem partOf_parent {P : List Place} {q r p : Nat} (hp : parentOf P q = some r)
    (hlt : r < q) (hr : r < P.length) (hroot : parentOf P p = none) :
    partOf P q p ↔ partOf P r p := by
  have hq : q < P.length := by
    simp only [parentOf] at hp
    cases h : P[q]? with
    | none => rw [h] at hp; cases hp
    | some _ => exact lt_of_getElem? h
  simp only [partOf, hq, hr, true_and]
  rw [chain_cons hp hlt]
  constructor
  · rintro (rfl | h)
    · rw [hroot] at hp; cases hp
    · rcases List.mem_cons.1 h with rfl | h
      · exact .inl rfl
      · exact .inr h
  · rintro (rfl | h)
    · exact .inr (List.mem_cons_self ..)
    · exact .inr (List.mem_cons_of_mem _ h)

/-- Under `FreePre` (A6), every anchor of a place usable after the release stays active. -/
theorem free_anchors {k : K} {s : S3} {p auth : Nat} (hinv : Inv3 s) (hpre : FreePre k s p auth) :
    ∀ q, (freeS s p).Usable q → ∀ x ∈ (freeS s p).D q, (cleanup (freeS s p)).Active x := by
  obtain ⟨-, -, -, -, -, -, hanc, -⟩ := hpre
  intro q hq x hx
  have hq₀ : s.Usable q := S3.Usable.mono (s := s) (s' := freeS s p) rfl (fun _ h => h)
    (fun q h => by simp only [freeS, Bool.or_eq_false_iff] at h; exact h.1) hq
  have hx₀ : x ∈ s.D q := by
    simp only [freeS] at hx; split at hx
    · simp at hx
    · exact hx
  obtain ⟨y, hy, ya⟩ := hinv.2.2.1 q hq₀ x hx₀
  have hc := hanc q (List.mem_range.2 hq₀.lt) hq x hx
  unfold FreeAnchorOK OptP at hc
  rw [hy] at hc; obtain ⟨hcov, hnh, hl⟩ := hc
  refine ⟨_, by rw [cleanup_get, freeS_get, hy]; rfl, ?_⟩
  have hn : ¬ ((∃ l ∈ y.footprint, l ∈ footprint s.P p) ∨ heldIn s.P p y.holder) :=
    fun h => h.elim hcov hnh
  simp only [hn, ↓reduceIte]
  have : HolderLive (freeS s p) y.holder := hl
  simp only [this, ↓reduceIte, ya]

/-- `free` preserves `WF3` and `Inv3` (A6). -/
theorem free_preserves {k : K} {s s' : S3} {p auth : Nat} (hwf : WF3 s) (hinv : Inv3 s)
    (h : FreeStep k p auth s (.ok s')) : WF3 s' ∧ Inv3 s' := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  have hroot := hpre.2.2.2.1
  have hpr : parentOf s.P p = none := by
    unfold OwnedRoot OptP at hroot; split at hroot
    · rename_i pl hpl; simp [parentOf, hpl, hroot.1]
    · exact hroot.elim
  refine releases_preserve hwf hinv (freeS_releases s p) rfl rfl rfl ?_ (free_anchors hinv hpre)
  intro q pl r hq hp
  obtain ⟨pr, hpr', hlt, -, hd⟩ := hwf.parts q pl r hq hp
  have hpo : parentOf s.P q = some r := by simp [parentOf, hq, hp]
  simp only [freeS, hd, partOf_parent hpo hlt (lt_of_getElem? hpr') hpr]

/-- `free` preserves `Inv3` without `WF3` (A1; A6). -/
theorem free_preserves_inv3 {k : K} {s s' : S3} {p auth : Nat} (hinv : Inv3 s)
    (h : FreeStep k p auth s (.ok s')) : Inv3 s' := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  exact releases_preserve_inv3 hinv (freeS_releases s p) (free_anchors hinv hpre)

/-- `free_no_dangling` (A6): after `free p`, no active authority covers a leaf of `p`, and every
active authority has a live holder: no usable access reaches the released storage. -/
theorem free_no_dangling {k : K} {s s' : S3} {p auth : Nat} (hwf : WF3 s) (hinv : Inv3 s)
    (h : FreeStep k p auth s (.ok s')) :
    ∀ (j : Nat) (y : Authority), s'.A[j]? = some y → y.active = true →
      (∀ l ∈ y.footprint, l ∉ footprint s.P p) ∧ HolderLive s' y.holder := by
  have hp := free_preserves hwf hinv h
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
  intro j y hy ya
  refine ⟨fun l hl hlp => ?_, hp.1.poss j y hy ya⟩
  rw [freeEff, cleanup_get, freeS_get] at hy
  cases h₀ : s.A[j]? with
  | none => rw [h₀] at hy; cases hy
  | some y₀ =>
    rw [h₀] at hy; simp only [Option.map_some, Option.some.injEq] at hy
    by_cases hc : (∃ l ∈ y₀.footprint, l ∈ footprint s.P p) ∨ heldIn s.P p y₀.holder
    · simp only [hc, ↓reduceIte] at hy; subst hy; split at ya <;> simp at ya
    · simp only [hc, ↓reduceIte] at hy
      split at hy
      · subst hy; exact hc (.inl ⟨l, hl, hlp⟩)
      · subst hy; simp at ya

/-- `free p` releases the storage of `p` (A6): `freed` marks exactly `p` in addition. -/
theorem free_marks_freed {k : K} {s s' : S3} {p auth : Nat} (h : FreeStep k p auth s (.ok s')) :
    ∀ q, s'.freed q = (s.freed q || decide (q = p)) := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; intro q; rfl

/-! ## Exercise requires holding (A2) -/

/-- `exercise_requires_hold` (A2): an exercisable authority is active and held by the current
frame, or held by a usable place on which the current frame already has an exercisable
authority permitting its mode. -/
theorem exercise_requires_hold {s : S3} {a : Nat} (h : s.Exercisable a) :
    ∃ y, s.A[a]? = some y ∧ y.active = true ∧
      (y.holder = .frame s.top ∨ ∃ p, y.holder = .place p ∧ s.Usable p ∧ HasRight s y.mode p) := by
  cases h with
  | base hy ha hf => exact ⟨_, hy, ha, .inl hf⟩
  | @held _ p b y hy ha hp hu hb hc =>
    have hlt : b < s.A.length := by
      cases hb with
      | base hy' _ _ => exact lt_of_getElem? hy'
      | held hy' _ _ _ _ _ => exact lt_of_getElem? hy'
    exact ⟨y, hy, ha, .inr ⟨p, hp, hu, b, List.mem_range.2 hlt, hb, hc⟩⟩

/-! ## Reachability (MM-03.3 §10) -/

/-- States reached from the initial state (one frame, no place) by `ok` transitions of the
kernel operations, for fixed contracts `k` (MM-03.3.8). -/
inductive Reachable (k : K) : S3 → Prop where
  | init : Reachable k S3.init
  | derive {s s' : S3} {src q : Nat} {m : Mode} :
      Reachable k s → DeriveStep src q m s (.ok s') → Reachable k s'
  | split {s s' : S3} {src : Nat} {rs : List (List Nat)} :
      Reachable k s → SplitStep k src rs s (.ok s') → Reachable k s'
  | release {s s' : S3} {a : Nat} : Reachable k s → ReleaseStep a s (.ok s') → Reachable k s'
  | transfer {s s' : S3} {src dst : Nat} :
      Reachable k s → TransferStep k src dst s (.ok s') → Reachable k s'
  | depend {s s' : S3} {q x : Nat} : Reachable k s → DependStep q x s (.ok s') → Reachable k s'
  | enter {s s' : S3} {ps : List Nat} {ls : List (Option Nat × Option Nat × Nat)} :
      Reachable k s → EnterStep ps ls s (.ok s') → Reachable k s'
  | exit {s s' : S3} : Reachable k s → ExitStep s (.ok s') → Reachable k s'
  | read {s s' : S3} {a : Nat} {ls : List Nat} :
      Reachable k s → Read3Step a ls s (.ok s') → Reachable k s'
  | write {s s' : S3} {a : Nat} {ls : List Nat} :
      Reachable k s → Write3Step a ls s (.ok s') → Reachable k s'
  | writeShared {s s' : S3} {a : Nat} {ls : List Nat} :
      Reachable k s → WriteSharedStep k a ls s (.ok s') → Reachable k s'
  | pin {s s' : S3} {p : Nat} : Reachable k s → PinStep p s (.ok s') → Reachable k s'
  | unpin {s s' : S3} {p : Nat} : Reachable k s → UnpinStep k p s (.ok s') → Reachable k s'
  | endUse {s s' : S3} {p : Nat} : Reachable k s → EndUseStep k p s (.ok s') → Reachable k s'
  | free {s s' : S3} {p auth : Nat} :
      Reachable k s → FreeStep k p auth s (.ok s') → Reachable k s'

theorem init_wf : WF3 S3.init ∧ Inv3 S3.init := by
  refine ⟨⟨fun _ _ _ h => by simp [S3.init] at h, fun _ _ h => by simp [S3.init] at h,
    by simp [S3.init], by simp [S3.init], by simp [S3.init], fun _ _ _ h => by simp [S3.init] at h,
    fun _ _ _ h => by simp [S3.init] at h, fun _ _ _ h => by simp [S3.init] at h,
    fun _ _ h => by simp [S3.init] at h⟩,
    fun _ _ _ _ _ _ h => by simp [S3.init] at h, fun _ _ _ h => by simp [S3.init] at h,
    fun _ _ _ h => by simp [S3.init] at h, i4_always _⟩

/-- `reachable_access_invariant` (MM-03.3 §10): every reached state satisfies `WF3` and `Inv3`.
Conditional on the obligation `DDSound k` of `DeclaredDisjoint` (MM-03.3.8), used by `split`. -/
theorem reachable_access_invariant_underDD {k : K} (hdd : DDSound k) {s : S3}
    (h : Reachable k s) : WF3 s ∧ Inv3 s := by
  induction h with
  | init => exact init_wf
  | derive _ hs ih => exact derive_preserves ih.1 ih.2 hs
  | split _ hs ih => exact split_preserves_underDD hdd ih.1 ih.2 hs
  | release _ hs ih => exact release_preserves ih.1 ih.2 hs
  | transfer _ hs ih => exact transfer_preserves ih.1 ih.2 hs
  | depend _ hs ih => exact depend_preserves ih.1 ih.2 hs
  | enter _ hs ih => exact enter_preserves ih.1 ih.2 hs
  | exit _ hs ih => exact exit_preserves ih.1 ih.2 hs
  | read _ hs ih => rw [read3_preserves hs]; exact ih
  | write _ hs ih => exact write3_preserves ih.1 ih.2 hs
  | writeShared _ hs ih => exact writeShared_preserves ih.1 ih.2 hs
  | pin _ hs ih => rw [(Guarded.ok_iff.1 hs).2]; exact pinEff_preserves ih.1 ih.2
  | unpin _ hs ih => rw [(Guarded.ok_iff.1 hs).2]; exact pinEff_preserves ih.1 ih.2
  | endUse _ hs ih => exact endUse_preserves ih.1 ih.2 hs
  | free _ hs ih => exact free_preserves ih.1 ih.2 hs

/-! ## Redundant preconditions (A11) -/

/-- O1.4 follows from O1.1 and O1.3 under I1 (MM-03.3 §3, O1; A11): it is not a precondition of
`derive`. -/
theorem derive_compat_redundant {s : S3} {src q : Nat} {m : Mode} (h1 : I1 s) (hs : s.Active src)
    (h3 : ∀ p ∈ footprint s.P q, Allows (effective s src p) m) : DeriveCompat s src q m := by
  obtain ⟨x, hx, -⟩ := hs
  have hI := addAuth_I1 (hd := .frame s.top) h1 hx h3
  intro b hb p hpq
  have hn : effective (deriveEff s src q m) s.A.length p = some m := by
    rw [deriveEff, effective_eq (addAuth_self _ _) rfl hpq]
    have : descModes (s.addAuth ⟨m, some src, footprint s.P q, .frame s.top, true⟩)
        s.A.length p = [] := by
      apply nil_of_forall_not_mem; intro e he
      obtain ⟨j, y, hy, -, -, hj, -⟩ := mem_descModes.1 he
      have h1 := chain_lt hj
      have h2 := lt_of_getElem? hy; simp [S3.addAuth] at h2; omega
    simp [this, effOf]
  cases he : effective (deriveEff s src q m) b p with
  | none => trivial
  | some e => exact effective_compat hI b _ p e m (by have := List.mem_range.1 hb; omega) he hn

/-- The removed clause of `canWrite3` follows from its first clause under I1 (MM-03.3 §5;
A11). -/
theorem canWrite3_excl_redundant {s : S3} (h1 : I1 s) {a : Nat} {ls : List Nat}
    (hw : canWrite3 s a ls) : ∀ p ∈ ls, ∀ b, b ≠ a → effective s b p = none :=
  fun p hp _ hb => effective_exclusive h1 (Ne.symm hb) (hw.2 p hp).1

/-! ## Arena (MM-03.3 §6, A10) -/

/-- Logical state of an arena (MM-03.3 §6; A10): `storage` is a place owned by the arena value;
`internal` is its root authority, held by the arena value; `issued` maps each issued region to
the issued block. The anchor of §6 is not a field: dependents anchor on the blocks (A10). -/
structure Arena where
  storage : Nat
  internal : Nat
  available : List Nat
  issued : List (List Nat × Nat)

/-- The place of the arena value: the owner of its storage (A10). -/
def arenaValue (s : S3) (ar : Arena) : Option Nat :=
  match s.P[ar.storage]? with
  | some pl =>
    match pl.owner with
    | .place v => some v
    | .frame _ => none
  | none => none

/-- Metadata leaves of the arena: the footprint of the arena value (A10). -/
def metaLeaves (s : S3) (ar : Arena) : List Nat :=
  match arenaValue s ar with
  | some v => footprint s.P v
  | none => []

/-- Arena invariant (MM-03.3 §6; A10). Clauses of §6: issued regions within the administered
storage (the footprint of `internal`); two simultaneously valid issued regions disjoint;
available regions disjoint from the still distributed ones; added: available regions within the
storage. Clauses of A10: each emission is a `Modify` authority derived from `internal` on its
region; the storage is an owned root; `internal` is a `Modify` root held by the owner of the
storage, that is, by the arena value, and covering exactly the footprint of the storage
(`internal` is its root). -/
def ArenaInv (s : S3) (ar : Arena) : Prop :=
  (∀ l ∈ ar.available, l ∈ s.afp ar.internal) ∧
  (∀ e ∈ ar.issued, ∀ l ∈ e.1, l ∈ s.afp ar.internal) ∧
  ar.issued.Pairwise (fun e e' => s.Active e.2 → s.Active e'.2 → ∀ l ∈ e.1, l ∉ e'.1) ∧
  (∀ e ∈ ar.issued, s.Active e.2 → ∀ l ∈ e.1, l ∉ ar.available) ∧
  (∀ e ∈ ar.issued, ∃ y, s.A[e.2]? = some y ∧ y.origin = some ar.internal ∧
    y.footprint = e.1 ∧ y.mode = .modify) ∧
  OwnedRoot s ar.storage ∧
  (∃ (y : Authority) (pl : Place), s.A[ar.internal]? = some y ∧ s.P[ar.storage]? = some pl ∧
    y.origin = none ∧ y.mode = .modify ∧ y.holder = pl.owner) ∧
  (∀ l, l ∈ s.afp ar.internal ↔ l ∈ footprint s.P ar.storage)

/-- Right to update the metadata of the arena (A10): an exercisable authority `via` with a
present effective mode on every metadata leaf, all `SharedMutable` (a `writeShared`, A9), with
valid dependencies. -/
def MetaRight (k : K) (s : S3) (ar : Arena) (via : Nat) : Prop :=
  s.Exercisable via ∧ arenaValue s ar ≠ none ∧
  ∀ l ∈ metaLeaves s ar, effective s via l ≠ none ∧ k.SharedMutable l ∧ DepsValid s l

instance (k : K) [DecidablePred k.SharedMutable] (s : S3) (ar : Arena) (via : Nat) :
    Decidable (MetaRight k s ar via) := by
  unfold MetaRight; infer_instance

/-- Static preconditions of `arena.issue(region)` (MM-03.3 §6; A10): metadata right (A10); the
region lies in the storage administered by `internal`; the destination `dst` of the block is
usable, exercisable in `Modify` (A2) and holds no initialised value. -/
def IssueStatic (k : K) (s : S3) (ar : Arena) (via : Nat) (region : List Nat) (dst : Nat) :
    Prop :=
  MetaRight k s ar via ∧ s.Active ar.internal ∧ (∀ l ∈ region, l ∈ s.afp ar.internal) ∧
  s.Usable dst ∧ HasRight s .modify dst ∧ (∀ l ∈ footprint s.P dst, s.I l ≠ .init)

instance (k : K) [DecidablePred k.SharedMutable] (s : S3) (ar : Arena) (via : Nat)
    (region : List Nat) (dst : Nat) : Decidable (IssueStatic k s ar via region dst) := by
  unfold IssueStatic; infer_instance

/-- The region is available (MM-03.3 §6): otherwise `issue` fails (A10). -/
def Avail (ar : Arena) (region : List Nat) : Prop := ∀ l ∈ region, l ∈ ar.available

instance (ar : Arena) (region : List Nat) : Decidable (Avail ar region) := by
  unfold Avail; infer_instance

/-- The abstraction has, through `internal`, effective `Modify` on the region (MM-03.3 §6:
the abstraction has the authority needed to distribute the region). The
disjointness from active emissions is removed (A11): it follows from this right
(`issue_disjoint_redundant`). -/
def IssueRight (s : S3) (ar : Arena) (region : List Nat) : Prop :=
  ∀ l ∈ region, effective s ar.internal l = some .modify

instance (s : S3) (ar : Arena) (region : List Nat) : Decidable (IssueRight s ar region) := by
  unfold IssueRight; infer_instance

/-- Effect of `arena.issue(region)` (MM-03.3 §6; A10): a `Modify` block derived from `internal`
on the region, held by the destination value; the destination and the metadata become `Init`;
the region leaves `available` and joins `issued`. -/
def issueEff (s : S3) (ar : Arena) (region : List Nat) (dst : Nat) : S3 × Arena :=
  ({ s.addAuth ⟨.modify, some ar.internal, region, .place dst, true⟩ with
      I := fun l => if l ∈ footprint s.P dst ∨ l ∈ metaLeaves s ar then .init else s.I l },
   { ar with
      available := ar.available.filter fun l => decide (l ∉ region)
      issued := (region, s.A.length) :: ar.issued })

/-- Outcomes of `issue` (A10): `ok`, defined failure `fail` with the state unchanged, `reject`
(pass-1 arbitrage 6). -/
inductive IOutcome where
  | ok (s : S3) (ar : Arena)
  | fail (s : S3) (ar : Arena)
  | reject

/-- `arena.issue` as a relation (MM-03.3 §6; A10): `reject` when a static precondition fails;
`fail`, with the state unchanged, when the region is unavailable; `reject` when the region is
available but `internal` lacks the right to distribute it; `ok` otherwise. -/
inductive IssueStep (k : K) (ar : Arena) (via : Nat) (region : List Nat) (dst : Nat) (s : S3) :
    IOutcome → Prop where
  | ok : IssueStatic k s ar via region dst → Avail ar region → IssueRight s ar region →
      IssueStep k ar via region dst s
        (.ok (issueEff s ar region dst).1 (issueEff s ar region dst).2)
  | fail : IssueStatic k s ar via region dst → ¬ Avail ar region →
      IssueStep k ar via region dst s (.fail s ar)
  | reject : ¬ IssueStatic k s ar via region dst → IssueStep k ar via region dst s .reject
  | noRight : IssueStatic k s ar via region dst → Avail ar region → ¬ IssueRight s ar region →
      IssueStep k ar via region dst s .reject

/-- Determinism of `issue` (MM-03.3 §6; A10). -/
theorem issue_det {k : K} {ar : Arena} {via dst : Nat} {region : List Nat} {s : S3}
    {o₁ o₂ : IOutcome} (h₁ : IssueStep k ar via region dst s o₁)
    (h₂ : IssueStep k ar via region dst s o₂) : o₁ = o₂ := by
  cases h₁ <;> cases h₂ <;> first | rfl | contradiction

/-- `ok` outcome of `arena.issue` (MM-03.3 §6; A10). -/
theorem issue_ok_iff {k : K} {ar ar' : Arena} {via dst : Nat} {region : List Nat} {s s' : S3} :
    IssueStep k ar via region dst s (.ok s' ar') ↔ IssueStatic k s ar via region dst ∧
      Avail ar region ∧ IssueRight s ar region ∧ (s', ar') = issueEff s ar region dst := by
  constructor
  · intro h; cases h with
    | ok h1 h2 h3 => exact ⟨h1, h2, h3, rfl⟩
  · rintro ⟨h1, h2, h3, e⟩
    have e1 := congrArg Prod.fst e; have e2 := congrArg Prod.snd e
    simp only at e1 e2; subst e1 e2; exact .ok h1 h2 h3

/-- Preconditions of `arena.reset()` (MM-03.3 §6; A10): metadata right; no active authority
derived from `internal`; no usable place anchored on `internal` or on an authority derived from
it. -/
def ResetPre (k : K) (s : S3) (ar : Arena) (via : Nat) : Prop :=
  MetaRight k s ar via ∧
  (∀ j ∈ List.range s.A.length, ar.internal ∈ s.ancs j → ¬ s.Active j) ∧
  (∀ q ∈ List.range s.P.length, s.Usable q → ∀ x ∈ s.D q, x ≠ ar.internal ∧ ar.internal ∉ s.ancs x)

instance (k : K) [DecidablePred k.SharedMutable] (s : S3) (ar : Arena) (via : Nat) :
    Decidable (ResetPre k s ar via) := by
  unfold ResetPre; infer_instance

/-- Effect of `arena.reset()` (MM-03.3 §6; A10): the whole storage becomes available, the past
emissions are forgotten, the metadata become `Init`. -/
def resetEff (s : S3) (ar : Arena) : S3 × Arena :=
  ({ s with I := fun l => if l ∈ metaLeaves s ar then .init else s.I l },
   { ar with available := s.afp ar.internal, issued := [] })

/-- `arena.reset` as a relation (MM-03.3 §6; A10). -/
def ResetStep (k : K) (ar : Arena) (via : Nat) (s : S3) : Outcome3 (S3 × Arena) → Prop :=
  Guarded (ResetPre k s ar via) (resetEff s ar)

theorem afp_addAuth_lt {s : S3} {y₀ : Authority} {j : Nat} (h : j < s.A.length) :
    (s.addAuth y₀).afp j = s.afp j := by simp only [S3.afp, addAuth_lt h]

theorem active_addAuth_iff {s : S3} {y₀ : Authority} {x : Nat} (hx : x < s.A.length) :
    (s.addAuth y₀).Active x ↔ s.Active x := by
  simp only [S3.Active, addAuth_lt hx]

/-- The disjointness of a new emission from the active ones follows from the authority of
`internal` (MM-03.3 §6; A11): an active block derived from `internal` covering a leaf takes the
effective `Modify` of `internal` away from it. -/
theorem issue_disjoint_redundant {s : S3} {ar : Arena} {region : List Nat} (hwf : WF3 s)
    (hai : ArenaInv s ar) (hm : ∀ l ∈ region, effective s ar.internal l = some .modify) :
    ∀ e ∈ ar.issued, s.Active e.2 → ∀ l ∈ region, l ∉ e.1 := by
  intro e he ha l hl hle
  obtain ⟨y, hy, ho, hf, hmd⟩ := hai.2.2.2.2.1 e he
  obtain ⟨y', hy', ya⟩ := ha; rw [hy] at hy'; cases hy'
  have hlt := hwf.origin e.2 y ar.internal hy ho
  have hanc : ar.internal ∈ s.ancs e.2 := by
    unfold S3.ancs; rw [chain_cons (by simp [S3.org, hy, ho]) hlt]; exact List.mem_cons_self ..
  have hd : Mode.modify ∈ descModes s ar.internal l :=
    mem_descModes.2 ⟨e.2, y, hy, ya, hf ▸ hle, hanc, hmd⟩
  obtain ⟨x, hx, -, -, he'⟩ := effective_some (hm l hl)
  rcases effOf_cases he' with ⟨h0, -⟩ | ⟨-, hn, -⟩
  · simp [h0] at hd
  · exact hn hd

/-- `issue_fail_unchanged` (A10): a failed emission leaves state and arena unchanged, and happens
exactly when the static preconditions hold and the region is unavailable. -/
theorem issue_fail_unchanged {k : K} {s s' : S3} {ar ar' : Arena} {via dst : Nat}
    {region : List Nat} (h : IssueStep k ar via region dst s (.fail s' ar')) :
    s' = s ∧ ar' = ar ∧ IssueStatic k s ar via region dst ∧ ¬ Avail ar region := by
  cases h with
  | fail hp ha => exact ⟨rfl, rfl, hp, ha⟩

/-- `arena_issue_preserves_disjointness` (MM-03.3 §6, §10; A10): `issue` preserves `WF3`, `Inv3`
and the arena invariant. The disjointness of the new region is obtained from the access
discipline (`issue_disjoint_redundant`), not from a precondition. No hypothesis on `K`. -/
theorem arena_issue_preserves_disjointness {k : K} {s s' : S3} {ar ar' : Arena} {via dst : Nat}
    {region : List Nat} (hwf : WF3 s) (hinv : Inv3 s) (hai : ArenaInv s ar)
    (h : IssueStep k ar via region dst s (.ok s' ar')) : WF3 s' ∧ Inv3 s' ∧ ArenaInv s' ar' := by
  cases h with
  | ok hp hav hright =>
  obtain ⟨-, ⟨x, hx, -⟩, hreg', hdst, -, -⟩ := hp
  have hreg : ∀ l ∈ region, l ∈ s.afp ar.internal ∧ effective s ar.internal l = some .modify :=
    fun l hl => ⟨hreg' l hl, hright l hl⟩
  have hs := lt_of_getElem? hx
  obtain ⟨hwf₁, hinv₁⟩ := addAuth_preserves (hd := .place dst) hwf hinv hx
    (fun l hl => by simpa [S3.afp, hx] using (hreg l hl).1)
    (fun l hl => by rw [(hreg l hl).2]; simp [Allows, OptP, Mode.le]) hdst
  have hdis := issue_disjoint_redundant hwf hai fun l hl => (hreg l hl).2
  obtain ⟨c0, c1, c2, c3, c4, c5, ⟨yi, pli, hyi, hpli, hoi, hmi, hhi⟩, c7⟩ := hai
  have old : ∀ e ∈ ar.issued, e.2 < s.A.length := fun e he => by
    obtain ⟨y, hy, -⟩ := c4 e he; exact lt_of_getElem? hy
  have hi := lt_of_getElem? hyi
  refine ⟨hwf₁.of_eq rfl rfl rfl rfl rfl, ⟨hinv₁.1, hinv₁.2.1, fun q hq y hy =>
    hinv₁.2.2.1 q ((S3.Usable.congr (s' := (issueEff s ar region dst).1)
      (s := s.addAuth ⟨.modify, some ar.internal, region, .place dst, true⟩) rfl rfl rfl).1 hq) y hy,
    i4_always _⟩, ?_⟩
  refine ⟨fun l hl => ?_, fun e he l hl => ?_, ?_, fun e he ha l hl => ?_, fun e he => ?_, c5,
    ⟨yi, pli, by show (s.addAuth _).A[ar.internal]? = _; rw [addAuth_lt hi]; exact hyi, hpli, hoi,
      hmi, hhi⟩, fun l => by
      show l ∈ (s.addAuth _).afp ar.internal ↔ _; rw [afp_addAuth_lt hi]; exact c7 l⟩
  · show l ∈ (s.addAuth _).afp ar.internal
    rw [afp_addAuth_lt hi]; exact c0 l (List.mem_filter.1 hl).1
  · show l ∈ (s.addAuth _).afp ar.internal
    rw [afp_addAuth_lt hi]
    rcases List.mem_cons.1 he with rfl | he
    · exact (hreg l hl).1
    · exact c1 e he l hl
  · refine List.pairwise_cons.2 ⟨fun e he _ ha l hl hle => ?_, c2.imp_of_mem fun {e e'} he he' h ha ha' =>
      h ((active_addAuth_iff (old e he)).1 ha) ((active_addAuth_iff (old e' he')).1 ha')⟩
    exact hdis e he ((active_addAuth_iff (old e he)).1 ha) l hl hle
  · rcases List.mem_cons.1 he with rfl | he
    · intro h'; have := (List.mem_filter.1 h').2; simp at this; exact this hl
    · have := c3 e he ((active_addAuth_iff (old e he)).1 ha) l hl
      exact fun h' => this (List.mem_filter.1 h').1
  · rcases List.mem_cons.1 he with rfl | he
    · exact ⟨_, addAuth_self _ _, rfl, rfl, rfl⟩
    · obtain ⟨y, hy, hh⟩ := c4 e he
      exact ⟨y, by show (s.addAuth _).A[e.2]? = _; rw [addAuth_lt (old e he)]; exact hy, hh⟩

/-- `arena_issue_keeps_earlier_blocks` (MM-03.3 §6, §10): earlier emissions stay issued with
their authority unchanged, and the new region is disjoint from those still active. No hypothesis
on `K`. -/
theorem arena_issue_keeps_earlier_blocks {k : K} {s s' : S3} {ar ar' : Arena} {via dst : Nat}
    {region : List Nat} (hwf : WF3 s) (hai : ArenaInv s ar)
    (h : IssueStep k ar via region dst s (.ok s' ar')) :
    ∀ e ∈ ar.issued, e ∈ ar'.issued ∧ s'.A[e.2]? = s.A[e.2]? ∧
      (s.Active e.2 → ∀ l ∈ region, l ∉ e.1) := by
  cases h with
  | ok _ _ hright =>
  intro e he
  obtain ⟨y, hy, -⟩ := hai.2.2.2.2.1 e he
  exact ⟨List.mem_cons_of_mem _ he, addAuth_lt (lt_of_getElem? hy),
    issue_disjoint_redundant hwf hai hright e he⟩

/-- `arena_reset_rejects_live_dependents` (MM-03.3 §6, I3, §10; A10): a usable place anchored on
`internal` or on an authority derived from it makes `reset` rejected. No hypothesis on `K`. -/
theorem arena_reset_rejects_live_dependents {k : K} {s : S3} {ar : Arena} {via q x : Nat}
    (hq : s.Usable q) (hx : x ∈ s.D q) (hxa : x = ar.internal ∨ ar.internal ∈ s.ancs x) :
    ResetStep k ar via s .reject :=
  .reject fun h => by
    have := h.2.2 q (List.mem_range.2 hq.lt) hq x hx
    rcases hxa with rfl | hxa
    · exact this.1 rfl
    · exact this.2 hxa

/-- An active authority derived from `internal`, a block still in use or an access derived from
it, makes `reset` rejected (MM-03.3 §6; A10). -/
theorem arena_reset_rejects_live_access {k : K} {s : S3} {ar : Arena} {via j : Nat}
    (hj : ar.internal ∈ s.ancs j) (ha : s.Active j) : ResetStep k ar via s .reject :=
  .reject fun h => by
    obtain ⟨y, hy, ya⟩ := ha
    exact h.2.1 j (List.mem_range.2 (lt_of_getElem? hy)) hj ⟨y, hy, ya⟩

/-- A live issued block makes `reset` rejected (MM-03.3 §6; A10): under the arena invariant and
the order of origins of `WF3`, an issued block derives from `internal`. -/
theorem arena_reset_rejects_live_issued {k : K} {s : S3} {ar : Arena} {via : Nat}
    {e : List Nat × Nat} (hwf : WF3 s) (hai : ArenaInv s ar) (he : e ∈ ar.issued)
    (ha : s.Active e.2) : ResetStep k ar via s .reject := by
  obtain ⟨y, hy, ho, -, -⟩ := hai.2.2.2.2.1 e he
  have hor : s.org e.2 = some ar.internal := by simp [S3.org, hy, ho]
  exact arena_reset_rejects_live_access
    (by rw [S3.ancs, chain_cons hor (hwf.origin e.2 y ar.internal hy ho)]; exact List.mem_cons_self ..)
    ha

/-- `reset` preserves the arena invariant, and modifies `available` and `issued`
(MM-03.3 §6; A10). -/
theorem arena_reset_preserves {k : K} {s s' : S3} {ar ar' : Arena} {via : Nat}
    (hai : ArenaInv s ar) (h : ResetStep k ar via s (.ok (s', ar'))) :
    ArenaInv s' ar' ∧ ar'.available = s.afp ar.internal ∧ ar'.issued = [] := by
  obtain ⟨-, e⟩ := Guarded.ok_iff.1 h
  have e1 := congrArg Prod.fst e; have e2 := congrArg Prod.snd e
  simp only [resetEff] at e1 e2; subst e1 e2
  obtain ⟨-, -, -, -, -, c5, c6, c7⟩ := hai
  exact ⟨⟨fun l hl => hl, fun _ he => (by cases he), List.Pairwise.nil, fun _ he => (by cases he),
      fun _ he => (by cases he), c5, c6, c7⟩, rfl, rfl⟩

/-- `reset` preserves `WF3` and `Inv3` (MM-03.3 §6; A10): it only writes the metadata. -/
theorem arena_reset_preserves_wf {k : K} {s s' : S3} {ar ar' : Arena} {via : Nat} (hwf : WF3 s)
    (hinv : Inv3 s) (h : ResetStep k ar via s (.ok (s', ar'))) : WF3 s' ∧ Inv3 s' := by
  obtain ⟨-, e⟩ := Guarded.ok_iff.1 h
  have e1 := congrArg Prod.fst e; simp only [resetEff] at e1; subst e1
  exact ⟨hwf.of_eq rfl rfl rfl rfl rfl, ⟨hinv.1, hinv.2.1, fun q hq y hy =>
    hinv.2.2.1 q ((S3.Usable.congr (s := s)
      (s' := { s with I := fun l => if l ∈ metaLeaves s ar then .init else s.I l })
      rfl rfl rfl).1 hq) y hy, i4_always _⟩⟩

/-- `arena_reuse_safe` (MM-03.3 §6; A10): after `reset`, issuing again, a region already issued
included, preserves `WF3`, `Inv3` and the arena invariant, and leaves every past emission
inactive: no stale access. -/
theorem arena_reuse_safe {k : K} {s s₁ s₂ : S3} {ar ar₁ ar₂ : Arena} {via via' dst : Nat}
    {region : List Nat} (hwf : WF3 s) (hinv : Inv3 s) (hai : ArenaInv s ar)
    (hr : ResetStep k ar via s (.ok (s₁, ar₁)))
    (hi : IssueStep k ar₁ via' region dst s₁ (.ok s₂ ar₂)) :
    WF3 s₂ ∧ Inv3 s₂ ∧ ArenaInv s₂ ar₂ ∧ ∀ e ∈ ar.issued, ¬ s₂.Active e.2 := by
  obtain ⟨hwf₁, hinv₁⟩ := arena_reset_preserves_wf hwf hinv hr
  obtain ⟨hai₁, -, -⟩ := arena_reset_preserves hai hr
  obtain ⟨hwf₂, hinv₂, hai₂⟩ := arena_issue_preserves_disjointness hwf₁ hinv₁ hai₁ hi
  refine ⟨hwf₂, hinv₂, hai₂, fun e he ha => ?_⟩
  obtain ⟨⟨-, hno, -⟩, e'⟩ := Guarded.ok_iff.1 hr
  have e1 := congrArg Prod.fst e'; simp only [resetEff] at e1; subst e1
  obtain ⟨y, hy, ho, -⟩ := hai.2.2.2.2.1 e he
  have hlt := hwf.origin e.2 y ar.internal hy ho
  have hanc : ar.internal ∈ s.ancs e.2 := by
    unfold S3.ancs; rw [chain_cons (by simp [S3.org, hy, ho]) hlt]; exact List.mem_cons_self ..
  cases hi with
  | ok _ _ _ =>
    have hl := lt_of_getElem? hy
    have : ({ s with I := fun l => if l ∈ metaLeaves s ar then .init else s.I l } : S3).Active e.2 :=
      (active_addAuth_iff (y₀ := ⟨.modify, some ar₁.internal, region, .place dst, true⟩) hl).1 ha
    exact hno e.2 (List.mem_range.2 hl) hanc this

/-! ## The arena invariant under kernel operations (A10) -/

theorem enter_chain_ge {s : S3} {ps : List Nat} {ls : List (Option Nat × Option Nat × Nat)}
    (hpre : EnterPre s ps ls) : ∀ n q, q < n → s.P.length ≤ q →
      ∀ x ∈ chain (parentOf (enterP s ls)) q, s.P.length ≤ x
  | 0, _, h, _, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, q, hq, hge, x, hx => by
    have hi : q - s.P.length < ls.length := by
      cases hpo : parentOf (enterP s ls) q with
      | none => rw [chain_none hpo] at hx; simp at hx
      | some r =>
        simp only [parentOf] at hpo
        cases h' : (enterP s ls)[q]? with
        | none => rw [h'] at hpo; cases hpo
        | some _ => have := lt_of_getElem? h'; rw [enterP_len] at this; omega
    have hpo := enter_parentOf_new (s := s) hi
    rw [show s.P.length + (q - s.P.length) = q by omega] at hpo
    cases hb : (ls[q - s.P.length]?).bind (·.1) with
    | none => rw [hb] at hpo; rw [chain_none hpo] at hx; simp at hx
    | some r =>
      rw [hb] at hpo
      have h1 := (hpre.2.2 (q - s.P.length) (List.mem_range.2 hi)).1
      rw [hb] at h1; simp only [OptP] at h1
      rw [chain_cons hpo (by omega)] at hx
      rcases List.mem_cons.1 hx with rfl | hx
      · omega
      · exact enter_chain_ge hpre n r (by omega) (by omega) x hx

/-- The footprint of an existing place does not change when a frame is entered: new places have
new parents (MM-03.3.2; MM-03.3 §4, O6). -/
theorem enter_footprint_old {s : S3} {ps : List Nat} {ls : List (Option Nat × Option Nat × Nat)}
    (hpre : EnterPre s ps ls) {q : Nat} (hq : q < s.P.length) :
    ∀ l, l ∈ footprint (enterP s ls) q ↔ l ∈ footprint s.P q := by
  have hpar : ∀ j < s.P.length, parentOf (enterP s ls) j = parentOf s.P j :=
    fun j hj => enter_parentOf_lt hj
  have hch : ∀ l < s.P.length, chain (parentOf (enterP s ls)) l = chain (parentOf s.P) l :=
    fun l hl => chain_congr fun j hj => hpar j (by omega)
  intro l
  simp only [mem_footprint, isLeaf, partOf, enterP_len]
  constructor
  · rintro ⟨hl, hleaf, -, hpo⟩
    have hln : l < s.P.length := by
      rcases Nat.lt_or_ge l s.P.length with h | h
      · exact h
      · rcases hpo with rfl | hpo
        · omega
        · have := enter_chain_ge hpre (l + 1) l (Nat.lt_succ_self l) h q hpo; omega
    refine ⟨hln, fun r hr => by rw [← hpar r hr]; exact hleaf r (by omega), hln, ?_⟩
    rwa [hch l hln] at hpo
  · rintro ⟨hl, hleaf, -, hpo⟩
    refine ⟨by omega, fun r hr => ?_, by omega, by rwa [hch l hl]⟩
    by_cases hrn : r < s.P.length
    · rw [hpar r hrn]; exact hleaf r hrn
    · intro he
      have hi : r - s.P.length < ls.length := by omega
      have hpo' := enter_parentOf_new (s := s) hi
      rw [show s.P.length + (r - s.P.length) = r by omega, he] at hpo'
      have h1 := (hpre.2.2 (r - s.P.length) (List.mem_range.2 hi)).1
      rw [← hpo'] at h1; simp only [OptP] at h1; omega

/-- One `ok` transition of a kernel operation (MM-03.3 §3–5; A6–A9). -/
inductive KStep (k : K) : S3 → S3 → Prop where
  | derive {s s' : S3} {src q : Nat} {m : Mode} : DeriveStep src q m s (.ok s') → KStep k s s'
  | split {s s' : S3} {src : Nat} {rs : List (List Nat)} :
      SplitStep k src rs s (.ok s') → KStep k s s'
  | release {s s' : S3} {a : Nat} : ReleaseStep a s (.ok s') → KStep k s s'
  | transfer {s s' : S3} {src dst : Nat} : TransferStep k src dst s (.ok s') → KStep k s s'
  | depend {s s' : S3} {q x : Nat} : DependStep q x s (.ok s') → KStep k s s'
  | enter {s s' : S3} {ps : List Nat} {ls : List (Option Nat × Option Nat × Nat)} :
      EnterStep ps ls s (.ok s') → KStep k s s'
  | exit {s s' : S3} : ExitStep s (.ok s') → KStep k s s'
  | read {s s' : S3} {a : Nat} {ls : List Nat} : Read3Step a ls s (.ok s') → KStep k s s'
  | write {s s' : S3} {a : Nat} {ls : List Nat} : Write3Step a ls s (.ok s') → KStep k s s'
  | writeShared {s s' : S3} {a : Nat} {ls : List Nat} :
      WriteSharedStep k a ls s (.ok s') → KStep k s s'
  | pin {s s' : S3} {p : Nat} : PinStep p s (.ok s') → KStep k s s'
  | unpin {s s' : S3} {p : Nat} : UnpinStep k p s (.ok s') → KStep k s s'
  | endUse {s s' : S3} {p : Nat} : EndUseStep k p s (.ok s') → KStep k s s'
  | free {s s' : S3} {p auth : Nat} : FreeStep k p auth s (.ok s') → KStep k s s'

/-- Sufficient conditions for the arena invariant to carry over to a new state: existing
authorities keep mode and footprint, only lose activity, keep an origin equal to `internal` or
absent; the storage stays an owned root; `internal` stays held by the owner of the storage. -/
theorem arenaInv_transport {s s' : S3} {ar : Arena} (hai : ArenaInv s ar)
    (hA : ∀ (j : Nat) (y : Authority), s.A[j]? = some y → ∃ y', s'.A[j]? = some y' ∧
      y'.mode = y.mode ∧ y'.footprint = y.footprint ∧ (y'.active = true → y.active = true) ∧
      (y.origin = some ar.internal → y'.origin = some ar.internal) ∧
      (y.origin = none → y'.origin = none))
    (hroot : OwnedRoot s' ar.storage)
    (hown : ∀ (y y' : Authority) (pl : Place), s.A[ar.internal]? = some y →
      s'.A[ar.internal]? = some y' → s.P[ar.storage]? = some pl → y.holder = pl.owner →
      ∃ pl', s'.P[ar.storage]? = some pl' ∧ y'.holder = pl'.owner)
    (hfoot : ∀ l, l ∈ footprint s'.P ar.storage ↔ l ∈ footprint s.P ar.storage) :
    ArenaInv s' ar := by
  obtain ⟨c0, c1, c2, c3, c4, -, ⟨yi, pli, hyi, hpli, hoi, hmi, hhi⟩, c7⟩ := hai
  obtain ⟨yi', hyi', mi, fi, -, -, oi⟩ := hA _ yi hyi
  have hafp : s'.afp ar.internal = s.afp ar.internal := by simp [S3.afp, hyi, hyi', fi]
  have act : ∀ x, s'.Active x → x < s.A.length → s.Active x := fun x ⟨y', hy', ya'⟩ hx => by
    obtain ⟨y, hy⟩ : ∃ y, s.A[x]? = some y := ⟨_, List.getElem?_eq_some_iff.2 ⟨hx, rfl⟩⟩
    obtain ⟨y'', hy'', -, -, ha, -⟩ := hA x y hy
    rw [hy'] at hy''; cases hy''; exact ⟨y, hy, ha ya'⟩
  have old : ∀ e ∈ ar.issued, e.2 < s.A.length := fun e he => by
    obtain ⟨y, hy, -⟩ := c4 e he; exact lt_of_getElem? hy
  obtain ⟨pl', hpl', hh'⟩ := hown yi yi' pli hyi hyi' hpli hhi
  refine ⟨fun l hl => hafp ▸ c0 l hl, fun e he l hl => hafp ▸ c1 e he l hl,
    c2.imp_of_mem fun {e e'} he he' h ha ha' => h (act _ ha (old e he)) (act _ ha' (old e' he')),
    fun e he ha => c3 e he (act _ ha (old e he)), fun e he => ?_, hroot,
    ⟨yi', pl', hyi', hpl', oi hoi, mi ▸ hmi, hh'⟩, fun l => by rw [hafp, hfoot]; exact c7 l⟩
  obtain ⟨y, hy, ho, hf, hm⟩ := c4 e he
  obtain ⟨y', hy', m', f', -, o', -⟩ := hA _ y hy
  exact ⟨y', hy', o' ho, f'.trans hf, m'.trans hm⟩

theorem OwnedRoot.of_P {s s' : S3} {q : Nat} (h : OwnedRoot s q) (hP : s'.P[q]? = s.P[q]?) :
    OwnedRoot s' q := by
  unfold OwnedRoot at h ⊢; rw [hP]; exact h

/-- `arena_inv_preserved` (MM-03.3 §6; A10): every `ok` transition of a kernel operation
preserves the arena invariant. -/
theorem arena_inv_preserved {k : K} {s s' : S3} {ar : Arena} (hwf : WF3 s) (hinv : Inv3 s)
    (hai : ArenaInv s ar) (h : KStep k s s') : ArenaInv s' ar := by
  have hroot := hai.2.2.2.2.2.1
  obtain ⟨yi, pli, hyi, hpli, hoi, -, hhi⟩ := hai.2.2.2.2.2.2.1
  have hi := lt_of_getElem? hyi
  have same : ∀ s₁ : S3, s₁.A = s.A → s₁.P = s.P → ArenaInv s₁ ar := fun s₁ hA hP =>
    arenaInv_transport hai (fun j y hy => ⟨y, by rw [hA]; exact hy, rfl, rfl, id, id, id⟩)
      (hroot.of_P (by rw [hP])) (fun y y' pl h1 h2 h3 h4 => ⟨pl, by rw [hP]; exact h3,
        by rw [hA, h1] at h2; cases h2; exact h4⟩) (fun l => by rw [hP])
  have append : ∀ (l : List Authority), ArenaInv { s with A := s.A ++ l } ar := fun l =>
    arenaInv_transport hai (fun j y hy => ⟨y, List.getElem?_append_left (lt_of_getElem? hy) ▸ hy,
      rfl, rfl, id, id, id⟩) hroot
      (fun y y' pl h1 h2 h3 h4 => ⟨pl, h3, by
        rw [show ({ s with A := s.A ++ l } : S3).A = s.A ++ l from rfl,
          List.getElem?_append_left hi, h1] at h2; cases h2; exact h4⟩) (fun _ => Iff.rfl)
  have releases : ∀ s₁, OnlyReleases s s₁ → s₁.P = s.P → ArenaInv s₁ ar := fun s₁ hr hP =>
    arenaInv_transport hai (fun j y hy => by
      obtain ⟨y', hy'⟩ : ∃ y', s₁.A[j]? = some y' :=
        ⟨_, List.getElem?_eq_some_iff.2 ⟨by rw [hr.1]; exact lt_of_getElem? hy, rfl⟩⟩
      obtain ⟨y₀, hy₀, m, o, f, -, a⟩ := hr.2 j y' hy'
      rw [hy] at hy₀; cases hy₀
      exact ⟨y', hy', m, f, a, fun h => o ▸ h, fun h => o ▸ h⟩)
      (hroot.of_P (by rw [hP]))
      (fun y y' pl h1 h2 h3 h4 => by
        obtain ⟨y₀, hy₀, -, -, -, hh, -⟩ := hr.2 _ y' h2
        rw [h1] at hy₀; cases hy₀
        exact ⟨pl, by rw [hP]; exact h3, hh ▸ h4⟩) (fun l => by rw [hP])
  cases h with
  | derive hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact append _
  | split hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact append _
  | release hs =>
    obtain ⟨⟨⟨x, hx, -⟩, -⟩, rfl⟩ := Guarded.ok_iff.1 hs
    refine releases _ ⟨by rw [releaseEff_eq hx]; simp, fun j z hz => ?_⟩ (by rw [releaseEff_eq hx])
    rw [releaseEff_eq hx] at hz; rw [set_get (lt_of_getElem? hx)] at hz
    split at hz
    · subst_vars; cases hz; exact ⟨x, hx, rfl, rfl, rfl, rfl, by simp⟩
    · exact ⟨z, hz, rfl, rfl, rfl, rfl, id⟩
  | transfer hs =>
    rename_i src dst
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
    refine arenaInv_transport hai (fun j y hy =>
      ⟨if heldIn s.P src y.holder then { y with holder := .place dst } else y,
        by rw [transfer_A_get, hy]; rfl, ?_⟩) ?_ ?_ (fun l => by rw [transfer_footprint])
    · by_cases hc : heldIn s.P src y.holder <;> simp [hc]
    · have hr : pli.parent = none ∧ pli.owner.isPlace = true := by
        simpa [OwnedRoot, OptP, hpli] using hroot
      simp only [OwnedRoot, OptP, transfer_P_get, hpli, Option.map_some]
      by_cases hc : heldIn s.P src pli.owner
      · simp [hc, hr, Holder.isPlace]
      · simp [hc, hr]
    · intro y y' pl h1 h2 h3 h4
      rw [transfer_A_get, h1] at h2; cases h2
      refine ⟨_, by rw [transfer_P_get, h3]; rfl, ?_⟩
      by_cases hc : heldIn s.P src pl.owner <;> simp [hc, h4]
  | depend hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact same _ rfl rfl
  | read hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact same _ rfl rfl
  | write hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact same _ rfl rfl
  | writeShared hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact same _ rfl rfl
  | pin hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact same _ rfl rfl
  | unpin hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact same _ rfl rfl
  | enter hs =>
    rename_i ps ls
    obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 hs
    have hst := lt_of_getElem? hpli
    have hnot : ar.internal ∉ ps := fun hm => by
      have h1 := hpre.2.1 _ hm
      simp only [OptP, hyi] at h1
      obtain ⟨-, hp, -⟩ := h1
      have hr : pli.parent = none ∧ pli.owner.isPlace = true := by
        simpa [OwnedRoot, OptP, hpli] using hroot
      have h2 := hr.2; rw [← hhi, hp] at h2; simp [Holder.isPlace] at h2
    refine arenaInv_transport hai (fun j y hy => ⟨_, by rw [enter_lt (lt_of_getElem? hy), hy]; rfl,
      ?_⟩) (hroot.of_P (enterP_lt hst)) ?_ (enter_footprint_old hpre hst)
    · split <;> simp
    · intro y y' pl h1 h2 h3 h4
      rw [enter_lt hi, h1] at h2; simp only [Option.map_some, Option.some.injEq, hnot,
        ↓reduceIte] at h2
      exact ⟨pl, by show (enterP s ls)[_]? = _; rw [enterP_lt hst]; exact h3, h2 ▸ h4⟩
  | exit hs =>
    obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 hs
    unfold ExitPre at hpre
    split at hpre
    · rename_i f F₀ hF
      obtain ⟨-, -, hR2⟩ := hpre
      refine arenaInv_transport hai (fun j y hy => ⟨_, by rw [exit_A_get hF, hy]; rfl,
        (exitG_same s F₀ j y).1, (exitG_same s F₀ j y).2.1, exitG_active' hy, fun ho => ?_,
        fun ho => ?_⟩) (hroot.of_P (by rw [exitEff_eq hF])) ?_ (fun l => by rw [exitEff_eq hF])
      · rcases exitG_origin (s := s) (F₀ := F₀) (a := j) (y := y) with e | ⟨hsv, -, e⟩
        · rw [e, ho]
        · rw [e]
          have hob : s.org j = some ar.internal := by simp [S3.org, hy, ho]
          have hnone : s.org ar.internal = none := by simp [S3.org, hyi, hoi]
          have hanc : s.ancs j = [ar.internal] := by
            rw [ancs_cons hwf.origin hob]; simp [S3.ancs, chain_none hnone]
          have hne := hR2 j (List.mem_range.2 (lt_of_getElem? hy)) hsv (by rw [hob]; simp)
          rw [hanc] at hne ⊢
          cases hfs : firstSurv s F₀ [ar.internal] with
          | none => exact absurd hfs hne
          | some z => rw [(List.mem_singleton.1 (firstSurv_some hfs).1)]
      · rcases exitG_origin (s := s) (F₀ := F₀) (a := j) (y := y) with e | ⟨-, hn, -⟩
        · rw [e, ho]
        · exact absurd ho hn
      · intro y y' pl h1 h2 h3 h4
        rw [exit_A_get hF, h1] at h2; cases h2
        exact ⟨pl, by rw [exitEff_eq hF]; exact h3, (exitG_same s F₀ _ y).2.2 ▸ h4⟩
    · exact hpre.elim
  | endUse hs =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
    exact releases _ ((endUseS_releases s _).trans cleanup_releases) rfl
  | free hs =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
    exact releases _ ((freeS_releases s _).trans cleanup_releases) rfl

/-! ## Determinism and `ok` outcomes (MM-03.3 §3–5; A6–A10) -/

/-- Determinism of `derive` (MM-03.3 §3, O1). -/
theorem derive_det {src q : Nat} {m : Mode} {s : S3} {o₁ o₂ : Outcome3 S3}
    (h₁ : DeriveStep src q m s o₁) (h₂ : DeriveStep src q m s o₂) : o₁ = o₂ := Guarded.det h₁ h₂

/-- `ok` outcome of `derive` (MM-03.3 §3, O1). -/
theorem derive_ok_iff {src q : Nat} {m : Mode} {s s' : S3} :
    DeriveStep src q m s (.ok s') ↔ DerivePre s src q m ∧ s' = deriveEff s src q m := Guarded.ok_iff

/-- Determinism of `split` (MM-03.3 §3, O2). -/
theorem split_det {k : K} {src : Nat} {rs : List (List Nat)} {s : S3} {o₁ o₂ : Outcome3 S3}
    (h₁ : SplitStep k src rs s o₁) (h₂ : SplitStep k src rs s o₂) : o₁ = o₂ := Guarded.det h₁ h₂

/-- `ok` outcome of `split` (MM-03.3 §3, O2). -/
theorem split_ok_iff {k : K} {src : Nat} {rs : List (List Nat)} {s s' : S3} :
    SplitStep k src rs s (.ok s') ↔ SplitPre k s src rs ∧ s' = splitEff s src rs := Guarded.ok_iff

/-- Determinism of `release` (MM-03.3 §3, O3). -/
theorem release_det {a : Nat} {s : S3} {o₁ o₂ : Outcome3 S3}
    (h₁ : ReleaseStep a s o₁) (h₂ : ReleaseStep a s o₂) : o₁ = o₂ := Guarded.det h₁ h₂

/-- `ok` outcome of `release` (MM-03.3 §3, O3). -/
theorem release_ok_iff {a : Nat} {s s' : S3} :
    ReleaseStep a s (.ok s') ↔ ReleasePre s a ∧ s' = releaseEff s a := Guarded.ok_iff

/-- Determinism of `transfer` (MM-03.3 §3, O4). -/
theorem transfer_det {k : K} {src dst : Nat} {s : S3} {o₁ o₂ : Outcome3 S3}
    (h₁ : TransferStep k src dst s o₁) (h₂ : TransferStep k src dst s o₂) : o₁ = o₂ := Guarded.det h₁ h₂

/-- `ok` outcome of `transfer` (MM-03.3 §3, O4). -/
theorem transfer_ok_iff {k : K} {src dst : Nat} {s s' : S3} :
    TransferStep k src dst s (.ok s') ↔ TransferPre k s src dst ∧ s' = transferEff s src dst := Guarded.ok_iff

/-- Determinism of `depend` (MM-03.3 §3, O5). -/
theorem depend_det {q x : Nat} {s : S3} {o₁ o₂ : Outcome3 S3}
    (h₁ : DependStep q x s o₁) (h₂ : DependStep q x s o₂) : o₁ = o₂ := Guarded.det h₁ h₂

/-- `ok` outcome of `depend` (MM-03.3 §3, O5). -/
theorem depend_ok_iff {q x : Nat} {s s' : S3} :
    DependStep q x s (.ok s') ↔ DependPre s q x ∧ s' = dependEff s q x := Guarded.ok_iff

/-- Determinism of `enter` (MM-03.3 §4, O6). -/
theorem enter_det {ps : List Nat} {ls : List (Option Nat × Option Nat × Nat)} {s : S3} {o₁ o₂ : Outcome3 S3}
    (h₁ : EnterStep ps ls s o₁) (h₂ : EnterStep ps ls s o₂) : o₁ = o₂ := Guarded.det h₁ h₂

/-- `ok` outcome of `enter` (MM-03.3 §4, O6). -/
theorem enter_ok_iff {ps : List Nat} {ls : List (Option Nat × Option Nat × Nat)} {s s' : S3} :
    EnterStep ps ls s (.ok s') ↔ EnterPre s ps ls ∧ s' = enterEff s ps ls := Guarded.ok_iff

/-- Determinism of `exit` (MM-03.3 §4, O7). -/
theorem exit_det  {s : S3} {o₁ o₂ : Outcome3 S3}
    (h₁ : ExitStep s o₁) (h₂ : ExitStep s o₂) : o₁ = o₂ := Guarded.det h₁ h₂

/-- `ok` outcome of `exit` (MM-03.3 §4, O7). -/
theorem exit_ok_iff  {s s' : S3} :
    ExitStep s (.ok s') ↔ ExitPre s ∧ s' = exitEff s := Guarded.ok_iff

/-- Determinism of `read3` (MM-03.3 §5). -/
theorem read3_det {a : Nat} {ls : List Nat} {s : S3} {o₁ o₂ : Outcome3 S3}
    (h₁ : Read3Step a ls s o₁) (h₂ : Read3Step a ls s o₂) : o₁ = o₂ := Guarded.det h₁ h₂

/-- `ok` outcome of `read3` (MM-03.3 §5). -/
theorem read3_ok_iff {a : Nat} {ls : List Nat} {s s' : S3} :
    Read3Step a ls s (.ok s') ↔ canRead3 s a ls ∧ s' = s := Guarded.ok_iff

/-- Determinism of `write3` (MM-03.3 §5). -/
theorem write3_det {a : Nat} {ls : List Nat} {s : S3} {o₁ o₂ : Outcome3 S3}
    (h₁ : Write3Step a ls s o₁) (h₂ : Write3Step a ls s o₂) : o₁ = o₂ := Guarded.det h₁ h₂

/-- `ok` outcome of `write3` (MM-03.3 §5). -/
theorem write3_ok_iff {a : Nat} {ls : List Nat} {s s' : S3} :
    Write3Step a ls s (.ok s') ↔ canWrite3 s a ls ∧ s' = write3Eff s ls := Guarded.ok_iff

/-- Determinism of `writeShared` (A9). -/
theorem writeShared_det {k : K} {a : Nat} {ls : List Nat} {s : S3} {o₁ o₂ : Outcome3 S3}
    (h₁ : WriteSharedStep k a ls s o₁) (h₂ : WriteSharedStep k a ls s o₂) : o₁ = o₂ := Guarded.det h₁ h₂

/-- `ok` outcome of `writeShared` (A9). -/
theorem writeShared_ok_iff {k : K} {a : Nat} {ls : List Nat} {s s' : S3} :
    WriteSharedStep k a ls s (.ok s') ↔ WriteSharedPre k s a ls ∧ s' = write3Eff s ls := Guarded.ok_iff

/-- Determinism of `pin` (A8). -/
theorem pin_det {p : Nat} {s : S3} {o₁ o₂ : Outcome3 S3}
    (h₁ : PinStep p s o₁) (h₂ : PinStep p s o₂) : o₁ = o₂ := Guarded.det h₁ h₂

/-- `ok` outcome of `pin` (A8). -/
theorem pin_ok_iff {p : Nat} {s s' : S3} :
    PinStep p s (.ok s') ↔ PinPre s p ∧ s' = pinEff s p true := Guarded.ok_iff

/-- Determinism of `unpin` (A8). -/
theorem unpin_det {k : K} {p : Nat} {s : S3} {o₁ o₂ : Outcome3 S3}
    (h₁ : UnpinStep k p s o₁) (h₂ : UnpinStep k p s o₂) : o₁ = o₂ := Guarded.det h₁ h₂

/-- `ok` outcome of `unpin` (A8). -/
theorem unpin_ok_iff {k : K} {p : Nat} {s s' : S3} :
    UnpinStep k p s (.ok s') ↔ UnpinPre k s p ∧ s' = pinEff s p false := Guarded.ok_iff

/-- Determinism of `endUse` (A6). -/
theorem endUse_det {k : K} {p : Nat} {s : S3} {o₁ o₂ : Outcome3 S3}
    (h₁ : EndUseStep k p s o₁) (h₂ : EndUseStep k p s o₂) : o₁ = o₂ := Guarded.det h₁ h₂

/-- `ok` outcome of `endUse` (A6). -/
theorem endUse_ok_iff {k : K} {p : Nat} {s s' : S3} :
    EndUseStep k p s (.ok s') ↔ EndUsePre k s p ∧ s' = endUseEff s p := Guarded.ok_iff

/-- Determinism of `free` (A6). -/
theorem free_det {k : K} {p auth : Nat} {s : S3} {o₁ o₂ : Outcome3 S3}
    (h₁ : FreeStep k p auth s o₁) (h₂ : FreeStep k p auth s o₂) : o₁ = o₂ := Guarded.det h₁ h₂

/-- `ok` outcome of `free` (A6). -/
theorem free_ok_iff {k : K} {p auth : Nat} {s s' : S3} :
    FreeStep k p auth s (.ok s') ↔ FreePre k s p auth ∧ s' = freeEff s p := Guarded.ok_iff

/-- Determinism of `arena.reset` (MM-03.3 §6; A10). -/
theorem reset_det {k : K} {ar : Arena} {via : Nat} {s : S3} {o₁ o₂ : Outcome3 (S3 × Arena)}
    (h₁ : ResetStep k ar via s o₁) (h₂ : ResetStep k ar via s o₂) : o₁ = o₂ := Guarded.det h₁ h₂

/-- `ok` outcome of `arena.reset` (MM-03.3 §6; A10). -/
theorem reset_ok_iff {k : K} {ar : Arena} {via : Nat} {s : S3} {r : S3 × Arena} :
    ResetStep k ar via s (.ok r) ↔ ResetPre k s ar via ∧ r = resetEff s ar := Guarded.ok_iff

/-! ## Pass-1 statements restored on the pass-2 model -/

theorem effOf_some_of_not_mem {m : Mode} {ds : List Mode} (h : Mode.modify ∉ ds) :
    ∃ e, effOf m ds = some e := by
  unfold effOf; by_cases h0 : ds = []
  · simp [h0]
  · simp [h0, h]

/-- Adding an authority can only lower an existing effective mode to `Observe` (MM-03.3.5). -/
theorem effective_addAuth_old {s : S3} {y₀ : Authority} {a p : Nat} {e' : Mode}
    (ha : a < s.A.length) (h : effective (s.addAuth y₀) a p = some e') :
    ∃ e, effective s a p = some e ∧ (e' = e ∨ e' = .observe) := by
  obtain ⟨x, hx, xa, xp, he⟩ := effective_some h
  rw [addAuth_lt ha] at hx
  rw [effective_eq hx xa xp]
  rw [descModes_addAuth] at he
  split at he
  · rcases effOf_cases he with ⟨h0, -⟩ | ⟨-, hn, rfl⟩
    · simp at h0
    · obtain ⟨e, he'⟩ := effOf_some_of_not_mem (m := x.mode) fun hm => hn (List.mem_append_left _ hm)
      exact ⟨e, he', .inr rfl⟩
  · rw [List.append_nil] at he; exact ⟨e', he, .inl rfl⟩

theorem org_addAuth_lt {s : S3} {y₀ : Authority} {j : Nat} (h : j < s.A.length) :
    (s.addAuth y₀).org j = s.org j := by simp only [S3.org, addAuth_lt h]

theorem enter_root_parent {s : S3} {ls : List (Option Nat × Option Nat × Nat)} {i : Nat}
    (h : (ls[i]?).bind (·.1) = none) : parentOf (enterP s ls) (s.P.length + i) = none := by
  by_cases hi : i < ls.length
  · rw [enter_parentOf_new hi]; exact h
  · simp only [parentOf]
    rw [List.getElem?_eq_none (by rw [enterP_len]; omega)]; rfl

theorem SameSkel.refl (s : S3) : SameSkel s s := ⟨rfl, fun _ => rfl⟩

/-- `derive` deactivates no authority: O1.5 (the needed anchors stay valid) always
holds (MM-03.3 §3, O1). -/
theorem derive_keeps_active {s : S3} {src q x : Nat} {m : Mode} (h : s.Active x) :
    (deriveEff s src q m).Active x := active_addAuth h

/-- `Inv3` part of `addAuth_preserves`, without `WF3`. -/
theorem addAuth_inv3 {s : S3} (hinv : Inv3 s) {src : Nat} {x : Authority} {m : Mode}
    {fp : List Nat} {hd : Holder} (hx : s.A[src]? = some x)
    (hfp : ∀ p ∈ fp, p ∈ x.footprint) (hal : ∀ p ∈ fp, Allows (effective s src p) m) :
    Inv3 (s.addAuth ⟨m, some src, fp, hd, true⟩) := by
  obtain ⟨i1, i2, i3, -⟩ := hinv
  have hs := lt_of_getElem? hx
  refine ⟨addAuth_I1 i1 hx hal, fun b y a hb ho => ?_, fun q hq y hy =>
    active_addAuth (i3 q ((S3.Usable.congr (addAuth_P s _) rfl rfl).1 hq) y hy), i4_always _⟩
  rcases addAuth_get hb with ⟨-, hb''⟩ | ⟨rfl, rfl⟩
  · obtain ⟨x₁, hx₁, h⟩ := i2 b y a hb'' ho
    exact ⟨x₁, by rw [addAuth_lt (lt_of_getElem? hx₁)]; exact hx₁, h⟩
  · cases ho
    refine ⟨x, by rw [addAuth_lt hs]; exact hx, fun p hp => ⟨hfp p hp, ?_⟩⟩
    have := hal p hp; unfold Allows OptP at this; split at this
    · rename_i e he; exact Mode.le_trans this (effective_le hx he)
    · exact this.elim

/-- `derive` preserves `Inv3` without `WF3` (MM-03.3 §3, O1; A1). -/
theorem derive_preserves_inv3 {s s' : S3} {src q : Nat} {m : Mode} (hinv : Inv3 s)
    (h : DeriveStep src q m s (.ok s')) : Inv3 s' := by
  obtain ⟨⟨⟨x, hx, -⟩, -, -, hfp, hal⟩, rfl⟩ := Guarded.ok_iff.1 h
  exact addAuth_inv3 hinv hx (fun p hp => by simpa [S3.afp, hx] using hfp p hp) hal

theorem split_aux_inv3 {src : Nat} {x : Authority} : ∀ (rs : List (List Nat)) (s : S3), Inv3 s →
    s.A[src]? = some x →
    (∀ r ∈ rs, ∀ p ∈ r, effective s src p = some .modify ∧ p ∈ x.footprint) →
    rs.Pairwise (fun r r' => ∀ l ∈ r, l ∉ r') → Inv3 (splitEff s src rs)
  | [], s, hinv, _, _, _ => by
    have : splitEff s src [] = s := by simp [splitEff]
    rw [this]; exact hinv
  | r :: rs, s, hinv, hx, hr, hpw => by
    rw [splitEff_cons]
    have hs := lt_of_getElem? hx
    have hinv₁ := addAuth_inv3 (m := .modify) (hd := .frame s.top) hinv hx
      (fun p hp => (hr r (List.mem_cons_self ..) p hp).2)
      (fun p hp => by rw [(hr r (List.mem_cons_self ..) p hp).1]; simp [Allows, OptP, Mode.le])
    obtain ⟨hpr, hpw⟩ := List.pairwise_cons.1 hpw
    refine split_aux_inv3 rs _ hinv₁ (by rw [addAuth_lt hs]; exact hx) (fun r' hr' p hp => ?_) hpw
    rw [effective_addAuth_notin hs fun h => hpr r' hr' p h hp]
    exact hr r' (List.mem_cons_of_mem _ hr') p hp

/-- `split` preserves `Inv3` without `WF3` (MM-03.3 §3, O2; A1), under `DDSound k`
(MM-03.3.8). -/
theorem split_preserves_inv3_underDD {k : K} (hdd : DDSound k) {s s' : S3} {src : Nat}
    {rs : List (List Nat)} (hinv : Inv3 s) (h : SplitStep k src rs s (.ok s')) : Inv3 s' := by
  obtain ⟨⟨⟨x, hx, -⟩, -, h1, h2, h3, -⟩, rfl⟩ := Guarded.ok_iff.1 h
  refine split_aux_inv3 rs s hinv hx (fun r hr p hp => ⟨h1 r hr p hp, ?_⟩)
    (h3.imp fun {r r'} h => h.elim id fun hd => hdd r r' hd)
  simpa [S3.afp, hx] using (h2 r hr p hp).1

/-- `split_preserves_exclusivity` (MM-03.3 §10): `split` preserves I1 under `Inv3` alone,
conditional on `DDSound k` (MM-03.3.8). -/
theorem split_preserves_exclusivity_underDD {k : K} (hdd : DDSound k) {s s' : S3} {src : Nat}
    {rs : List (List Nat)} (hinv : Inv3 s) (h : SplitStep k src rs s (.ok s')) : I1 s' :=
  (split_preserves_inv3_underDD hdd hinv h).1

/-- `release` preserves `Inv3` without `WF3` (MM-03.3 §3, O3; A1): the strengthened I1 only
constrains active authorities, which `release` removes. -/
theorem release_preserves_inv3 {s s' : S3} {a : Nat} (hinv : Inv3 s)
    (h : ReleaseStep a s (.ok s')) : Inv3 s' := by
  obtain ⟨⟨⟨x, hx, xa⟩, -, h3⟩, rfl⟩ := Guarded.ok_iff.1 h
  obtain ⟨i1, i2, i3, -⟩ := hinv
  have ha := lt_of_getElem? hx
  have e := releaseEff_eq hx
  have get : ∀ j, (releaseEff s a).A[j]? = if a = j then some { x with active := false }
      else s.A[j]? := fun j => by rw [e]; exact set_get ha
  have back : ∀ (j : Nat) (z : Authority), (releaseEff s a).A[j]? = some z →
      ∃ z₀ : Authority, s.A[j]? = some z₀ ∧
      z.mode = z₀.mode ∧ z.origin = z₀.origin ∧ z.footprint = z₀.footprint ∧
      (z.active = true → z₀.active = true) := fun j z hz => by
    rw [get] at hz; split at hz
    · subst_vars; cases hz; exact ⟨x, hx, rfl, rfl, rfl, by simp⟩
    · exact ⟨z, hz, rfl, rfl, rfl, id⟩
  have hP : (releaseEff s a).P = s.P := by rw [e]
  have hF : (releaseEff s a).F = s.F := by rw [e]
  have hd : (releaseEff s a).dead = s.dead := by rw [e]
  refine ⟨fun a' b' x' y' p hab ha' hb' xa' ya' xp yp hnab hnba => ?_,
    fun b y o hb ho => ?_, fun q hq y hy => ?_, i4_always _⟩
  · obtain ⟨x₀, hx₀, m₁, -, f₁, ac₁⟩ := back a' x' ha'
    obtain ⟨y₀, hy₀, m₂, -, f₂, ac₂⟩ := back b' y' hb'
    rw [release_ancs hx] at hnab hnba; rw [m₁, m₂]
    exact i1 a' b' x₀ y₀ p hab hx₀ hy₀ (ac₁ xa') (ac₂ ya') (f₁ ▸ xp) (f₂ ▸ yp) hnab hnba
  · obtain ⟨y₀, hy₀, m₀, e', f₀, -⟩ := back b y hb
    obtain ⟨x₁, hx₁, hh⟩ := i2 b y₀ o hy₀ (e' ▸ ho)
    refine ⟨if a = o then { x with active := false } else x₁, by rw [get]; split <;> simp_all,
      fun p hp => ?_⟩
    have := hh p (f₀ ▸ hp); rw [m₀]
    split
    · subst_vars; rw [hx] at hx₁; cases hx₁; exact this
    · exact this
  · have hq' := (S3.Usable.congr hP hF hd).1 hq
    have hy' : y ∈ s.D q := by rw [e] at hy; exact hy
    obtain ⟨z, hz, za⟩ := i3 q hq' y hy'
    refine ⟨z, ?_, za⟩
    rw [get]; split
    · subst_vars; exact absurd hy' (h3 q (List.mem_range.2 hq'.lt) hq')
    · exact hz

/-- `depend` preserves `Inv3` without `WF3` (MM-03.3 §3, O5). -/
theorem depend_preserves_inv3 {s s' : S3} {q x : Nat} (hinv : Inv3 s)
    (h : DependStep q x s (.ok s')) : Inv3 s' := by
  obtain ⟨⟨-, hx, -⟩, rfl⟩ := Guarded.ok_iff.1 h
  obtain ⟨i1, i2, i3, -⟩ := hinv
  refine ⟨i1, i2, fun r hr y hy => ?_, i4_always _⟩
  have hr' := (S3.Usable.congr (s := s) (s' := dependEff s q x) rfl rfl rfl).1 hr
  simp only [dependEff] at hy
  split at hy
  · subst_vars; rcases List.mem_append.1 hy with hy | hy
    · exact i3 _ hr' y hy
    · simp at hy; exact hy ▸ hx
  · exact i3 r hr' y hy

/-- `write3` preserves `Inv3` without `WF3` (MM-03.3 §5). -/
theorem write3_preserves_inv3 {s s' : S3} {a : Nat} {ls : List Nat} (hinv : Inv3 s)
    (h : Write3Step a ls s (.ok s')) : Inv3 s' := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
  exact ⟨hinv.1, hinv.2.1, fun q hq x hx =>
    hinv.2.2.1 q ((S3.Usable.congr (s := s) (s' := write3Eff s ls) rfl rfl rfl).1 hq) x hx,
    i4_always _⟩

/-- `issue` preserves `Inv3` without `WF3` (MM-03.3 §6; A1; A10). -/
theorem issue_preserves_inv3 {k : K} {s s' : S3} {ar ar' : Arena} {via dst : Nat}
    {region : List Nat} (hinv : Inv3 s) (h : IssueStep k ar via region dst s (.ok s' ar')) :
    Inv3 s' := by
  cases h with
  | ok hp _ hright =>
  obtain ⟨-, ⟨x, hx, -⟩, -, -, -, -⟩ := hp
  have h₁ := addAuth_inv3 (m := .modify) (hd := .place dst) hinv hx
    (fun l hl => by
      obtain ⟨x', hx', -, hl', -⟩ := effective_some (hright l hl)
      rw [hx] at hx'; cases hx'; exact hl')
    (fun l hl => by rw [hright l hl]; simp [Allows, OptP, Mode.le])
  exact ⟨h₁.1, h₁.2.1, fun q hq y hy => h₁.2.2.1 q
    ((S3.Usable.congr (s := s.addAuth ⟨.modify, some ar.internal, region, .place dst, true⟩)
      (s' := (issueEff s ar region dst).1) rfl rfl rfl).1 hq) y hy, i4_always _⟩

/-- `release_restores_authority` (MM-03.3 §3, O3; §10): if `b`, derived from `a`, is the only
active descendant of `a` covering `p`, then after `release b` the effective authority of `a` on
`p` is its mode; before, if `b` is in `Modify` on `p`, it was absent. -/
theorem release_restores_authority {s s' : S3} {b a p : Nat} {y x : Authority} (hwf : WF3 s)
    (h : ReleaseStep b s (.ok s')) (hy : s.A[b]? = some y) (ho : y.origin = some a)
    (hx : s.A[a]? = some x) (xa : x.active = true) (xp : p ∈ x.footprint)
    (honly : ∀ j z, s.A[j]? = some z → z.active = true → p ∈ z.footprint → a ∈ s.ancs j → j = b) :
    (y.mode = .modify → p ∈ y.footprint → effective s a p = none) ∧
    effective s' a p = some x.mode := by
  obtain ⟨⟨⟨y', hy', ya⟩, -, -⟩, rfl⟩ := Guarded.ok_iff.1 h
  rw [hy] at hy'; cases hy'
  have hab : a < b := hwf.origin b y a hy ho
  have hanc : a ∈ s.ancs b := by
    unfold S3.ancs; rw [chain_cons (by simp [S3.org, hy, ho]) hab]; exact List.mem_cons_self ..
  refine ⟨fun hm hp => ?_, ?_⟩
  · rw [effective_eq hx xa xp]
    have : Mode.modify ∈ descModes s a p := mem_descModes.2 ⟨b, y, hy, ya, hp, hanc, hm⟩
    unfold effOf; simp only [List.ne_nil_of_mem this, this, ↓reduceIte]
  · have hb := lt_of_getElem? hy
    have hx' : (releaseEff s b).A[a]? = some x := by
      rw [releaseEff_eq hy, set_get hb]; simp only [show ¬ b = a by omega, ↓reduceIte]; exact hx
    rw [effective_eq hx' xa xp]
    have : descModes (releaseEff s b) a p = [] := by
      apply nil_of_forall_not_mem; intro e he
      obtain ⟨j, z, hz, za, zp, hj, -⟩ := mem_descModes.1 he
      rw [release_ancs hy] at hj
      rw [releaseEff_eq hy, set_get hb] at hz
      split at hz
      · cases hz; simp at za
      · exact ‹¬b = j› (honly j z hz za zp hj).symm
    simp [this, effOf]

/-- `enterFrame` (MM-03.3 §4, O6) does not preserve `Inv3` alone (A1): in a state satisfying
`Inv3` where an authority covers a leaf that does not exist yet, the root of the new place covers
it too in `Modify`. `WF3` (footprints made of existing places) excludes this state. -/
theorem enter_not_inv3_preserving :
    let s : S3 := ⟨[0], 1, [], fun _ => .uninit, [⟨.modify, none, [0], .frame 0, true⟩],
      fun _ => [], fun _ => false, fun _ => false, fun _ => false⟩
    Inv3 s ∧ EnterStep [] [(none, none, 0)] s (.ok (enterEff s [] [(none, none, 0)])) ∧
      ¬ I1 (enterEff s [] [(none, none, 0)]) := by
  intro s
  refine ⟨⟨fun a b x y p hab ha hb _ _ _ _ _ _ => ?_, fun b y a hb ho => ?_,
    fun q hq => ?_, i4_always _⟩, .ok (by decide), fun h => ?_⟩
  · have h1 := lt_of_getElem? ha; have h2 := lt_of_getElem? hb
    simp [s] at h1 h2; omega
  · have := lt_of_getElem? hb; simp [s] at this; subst this; simp [s] at hb; subst hb; cases ho
  · have := hq.lt; simp [s] at this
  · have := h 0 1 ⟨.modify, none, [0], .frame 0, true⟩ ⟨.modify, none, [0], .frame 1, true⟩ 0
      (by decide) (by decide) (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide)
    exact absurd this.1 (by decide)

/-! ## Test cases (MM-03.3 §11 and the task of pass 2)

Each verdict is obtained by `decide` on the precondition of the operation concerned. States are
built from `S3.init` by the effects of operations. Classification of each case (kernel,
abstraction with `K` instantiated, out of kernel) is given in the report. -/

/-- Test contracts: `SharedMutable`, `Pinned`, `ExternalDone`, `Deallocable` given by lists of
leaves or places, `FreeCompat` by a list of pairs; no declared disjointness, no
invalidation. -/
def KT (sh pinned done dealloc : List Nat) (compat : List (Nat × Nat)) : K :=
  ⟨fun _ _ => False, (· ∈ sh), (· ∈ pinned), fun _ _ _ => False, (· ∈ done), (· ∈ dealloc),
    fun p a => (p, a) ∈ compat⟩

section TestContracts
variable (sh pinned done dealloc : List Nat) (compat : List (Nat × Nat))
instance : ∀ r r', Decidable ((KT sh pinned done dealloc compat).DeclaredDisjoint r r') :=
  fun _ _ => instDecidableFalse
instance : DecidablePred (KT sh pinned done dealloc compat).SharedMutable :=
  fun l => inferInstanceAs (Decidable (l ∈ sh))
instance : DecidablePred (KT sh pinned done dealloc compat).Pinned :=
  fun l => inferInstanceAs (Decidable (l ∈ pinned))
instance : DecidablePred (KT sh pinned done dealloc compat).ExternalDone :=
  fun l => inferInstanceAs (Decidable (l ∈ done))
instance : DecidablePred (KT sh pinned done dealloc compat).Deallocable :=
  fun p => inferInstanceAs (Decidable (p ∈ dealloc))
instance : ∀ p a, Decidable ((KT sh pinned done dealloc compat).FreeCompat p a) :=
  fun p a => inferInstanceAs (Decidable ((p, a) ∈ compat))
end TestContracts

/-- Empty contracts. -/
abbrev K0 : K := KT [] [] [] [] []

theorem KT_dd (sh pinned done dealloc : List Nat) (compat : List (Nat × Nat)) :
    DDSound (KT sh pinned done dealloc compat) := fun _ _ h => h.elim

/-- Entering frame 1 from the initial frame with locals `ls`. -/
def enter1 (ls : List (Option Nat × Option Nat × Nat)) : S3 := enterEff S3.init [] ls

/-! ### Case 1: two observations of a leaf (expected: allowed) -/

def c1a : S3 := write3Eff (enter1 [(none, none, 0)]) [0]
def c1b : S3 := deriveEff c1a 0 0 .observe
def c1c : S3 := deriveEff c1b 0 0 .observe
example : Write3Step 0 [0] (enter1 [(none, none, 0)]) (.ok c1a) := .ok (by decide)
example : DeriveStep 0 0 .observe c1a (.ok c1b) := .ok (by decide)
example : DeriveStep 0 0 .observe c1b (.ok c1c) := .ok (by decide)
example : Read3Step 1 [0] c1c (.ok c1c) ∧ Read3Step 2 [0] c1c (.ok c1c) :=
  ⟨.ok (by decide), .ok (by decide)⟩

/-! ### Case 2: observation and incompatible modification (expected: reject) -/

example : DeriveStep 0 0 .modify c1b .reject := .reject (by decide)
example : Write3Step 0 [0] c1b .reject := .reject (by decide)

/-! ### Case 3: two really disjoint fields (expected: simultaneous modifications allowed) -/

def c3a : S3 := enter1 [(none, none, 0), (some 0, none, 0), (some 0, none, 0)]
def c3b : S3 := deriveEff (deriveEff c3a 0 1 .modify) 0 2 .modify
example : DeriveStep 0 1 .modify c3a (.ok (deriveEff c3a 0 1 .modify)) := .ok (by decide)
example : DeriveStep 0 2 .modify (deriveEff c3a 0 1 .modify) (.ok c3b) := .ok (by decide)
example : Write3Step 1 [1] c3b (.ok (write3Eff c3b [1])) := .ok (by decide)
example : Write3Step 2 [2] (write3Eff c3b [1]) (.ok (write3Eff (write3Eff c3b [1]) [2])) :=
  .ok (by decide)

/-! ### Case 4: observation of an element and invalidating modification of the container
(expected: reject). The elements are parts of the container (pass-1 arbitrage 3). -/

def c4b : S3 := deriveEff c3a 0 1 .observe
example : DeriveStep 0 1 .observe c3a (.ok c4b) := .ok (by decide)
example : Write3Step 0 [1, 2] c4b .reject := .reject (by decide)
example : Write3Step 0 [1, 2] c3a (.ok (write3Eff c3a [1, 2])) := .ok (by decide)

/-! ### Case 5: split of a region into two parts (expected: independent authorities) -/

def c5b : S3 := splitEff c3a 0 [[1], [2]]
example : SplitStep K0 0 [[1], [2]] c3a (.ok c5b) := .ok (by decide)
example : Write3Step 1 [1] c5b (.ok (write3Eff c5b [1])) := .ok (by decide)
example : Write3Step 2 [2] c5b (.ok (write3Eff c5b [2])) := .ok (by decide)
example : effective c5b 0 1 = none ∧ effective c5b 0 2 = none := by decide

/-! ### Case 6: two successive emissions from an arena (expected: allowed)

Frame 1: 0 arena value (metadata leaf), 1 storage owned by 0 with leaves 2 and 3, 4 and 5 block
destinations. Root authorities: 0 (place 0), 1 (`internal`, held by place 0), 2, 3. -/

abbrev KA : K := KT [0] [] [] [] []
def c6a : S3 := enter1 [(none, none, 0), (none, some 0, 0), (some 1, some 0, 0),
  (some 1, some 0, 0), (none, none, 0), (none, none, 0)]
def ar6 : Arena := ⟨1, 1, [2, 3], []⟩
def c6b : S3 × Arena := issueEff c6a ar6 [2] 4
def c6c : S3 × Arena := issueEff c6b.1 c6b.2 [3] 5
example : IssueStep KA ar6 0 [2] 4 c6a (.ok c6b.1 c6b.2) := .ok (by decide) (by decide) (by decide)
example : IssueStep KA c6b.2 0 [3] 5 c6b.1 (.ok c6c.1 c6c.2) := .ok (by decide) (by decide) (by decide)
/-- An emission on a region still held by a live block fails (A10: region unavailable). -/
example : IssueStep KA c6b.2 0 [2] 5 c6b.1 (.fail c6b.1 c6b.2) := .fail (by decide) (by decide)
example : ArenaInv c6a ar6 :=
  ⟨(by decide), (by decide), (by decide), (by decide), fun _ h => (nomatch h), (by decide),
    ⟨_, _, rfl, rfl, rfl, rfl, rfl⟩,
    fun _ => by rw [show c6a.afp ar6.internal = footprint c6a.P ar6.storage by decide]⟩
example : WF3 c6a ∧ Inv3 c6a :=
  reachable_access_invariant_underDD (KT_dd [] [] [] [] []) (.enter .init (.ok (by decide)))

/-! ### Case 7: `arena.reset()` with a usable dependent (expected: reject) -/

def c7a : S3 := dependEff c6b.1 5 4
example : DependStep 5 4 c6b.1 (.ok c7a) := .ok (by decide)
example : ResetStep KA c6b.2 0 c7a .reject := .reject (by decide)
example : ResetStep KA c6b.2 0 c6b.1 .reject := .reject (by decide)

/-! ### Case 8: return of a buffer depending on a parameter of the caller (expected: allowed
under contract). Caller: 0 data, 1 result. Parameters derived by the caller (A3): 2 observes 0,
3 modifies 1. Callee: 2 value. -/

def c8a : S3 := write3Eff (enter1 [(none, none, 0), (none, none, 0)]) [0]
def c8b : S3 := deriveEff (deriveEff c8a 0 0 .observe) 1 1 .modify
def c8c : S3 := enterEff c8b [2, 3] [(none, none, 0)]
def c8d : S3 := dependEff (write3Eff c8c [2]) 2 2
def c8e : S3 := transferEff c8d 2 1
example : DeriveStep 0 0 .observe c8a (.ok (deriveEff c8a 0 0 .observe)) := .ok (by decide)
example : DeriveStep 1 1 .modify (deriveEff c8a 0 0 .observe) (.ok c8b) := .ok (by decide)
example : EnterStep [2, 3] [(none, none, 0)] c8b (.ok c8c) := .ok (by decide)
example : Write3Step 4 [2] c8c (.ok (write3Eff c8c [2])) := .ok (by decide)
example : DependStep 2 2 (write3Eff c8c [2]) (.ok c8d) := .ok (by decide)
example : TransferStep K0 2 1 c8d (.ok c8e) := .ok (by decide)
example : ExitStep c8e (.ok (exitEff c8e)) := .ok (by decide)
example : (exitEff c8e).D 1 = [0] := by decide

/-! ### Case 9: temporary capture of an access by a non-escaping value (expected: allowed) -/

def c9a : S3 := write3Eff (deriveEff (enter1 [(none, none, 0), (none, none, 0)]) 0 0 .observe) [1]
example : DependStep 1 2 c9a (.ok (dependEff c9a 1 2)) := .ok (by decide)
example : ReleaseStep 2 (dependEff c9a 1 2) .reject := .reject (by decide)

/-! ### Case 10: capture of a local access in an escaping value (expected: reject). Caller: 0
result, parameter 1. Callee: 1 local, 2 value capturing access 4 derived from the local. -/

def c10a : S3 := enterEff (deriveEff (enter1 [(none, none, 0)]) 0 0 .modify) [1]
  [(none, none, 0), (none, none, 0)]
def c10b : S3 := write3Eff (deriveEff c10a 2 1 .observe) [2]
def c10c : S3 := transferEff (dependEff c10b 2 4) 2 0
example : DeriveStep 2 1 .observe c10a (.ok (deriveEff c10a 2 1 .observe)) := .ok (by decide)
example : DependStep 2 4 c10b (.ok (dependEff c10b 2 4)) := .ok (by decide)
example : TransferStep K0 2 0 (dependEff c10b 2 4) (.ok c10c) := .ok (by decide)
example : ExitStep c10c .reject := .reject (by decide)

/-! ### Case 11: transfer invalidating an active projection (expected: reject) -/

def c11a : S3 := write3Eff (enter1 [(none, none, 0), (some 0, none, 0), (some 0, none, 0),
  (none, none, 0)]) [1, 2]
example : TransferStep K0 0 3 (deriveEff c11a 0 1 .observe) .reject := .reject (by decide)
example : TransferStep K0 0 3 c11a (.ok (transferEff c11a 0 3)) := .ok (by decide)

/-! ### Case 13: pinned storage for DMA (expected: no physical move while registered) -/

def c13a : S3 := write3Eff (enter1 [(none, none, 0), (none, none, 0)]) [0]
example : PinStep 0 c13a (.ok (pinEff c13a 0 true)) := .ok (by decide)
example : TransferStep K0 0 1 (pinEff c13a 0 true) .reject := .reject (by decide)
example : UnpinStep K0 0 (pinEff c13a 0 true) .reject := .reject (by decide)
example : UnpinStep (KT [] [] [0] [] []) 0 (pinEff c13a 0 true)
    (.ok (pinEff (pinEff c13a 0 true) 0 false)) := .ok (by decide)
example : TransferStep K0 0 1 (pinEff (pinEff c13a 0 true) 0 false)
    (.ok (transferEff (pinEff (pinEff c13a 0 true) 0 false) 0 1)) := .ok (by decide)

/-! ### Case 15: two disjoint SoA columns (expected: independent modifications) -/

def c15a : S3 := enter1 [(none, none, 0), (some 0, none, 0), (some 0, none, 0), (some 1, none, 0),
  (some 1, none, 0), (some 2, none, 0), (some 2, none, 0)]
def c15b : S3 := deriveEff (deriveEff c15a 0 1 .modify) 0 2 .modify
example : DeriveStep 0 2 .modify (deriveEff c15a 0 1 .modify) (.ok c15b) := .ok (by decide)
example : Write3Step 1 [3, 4] c15b (.ok (write3Eff c15b [3, 4])) := .ok (by decide)
example : Write3Step 2 [5, 6] (write3Eff c15b [3, 4])
    (.ok (write3Eff (write3Eff c15b [3, 4]) [5, 6])) := .ok (by decide)

/-! ### Case 16: return of a buffer depending on the caller's arena (expected: `ok`), then
`endUse(buffer)` and `reset` (expected: `ok`). Caller: 0 arena value, 1 storage owned by 0 with
leaves 2, 3; 4 buffer destination. Parameters: 3 observes the arena value, 4 modifies the
destination. Callee: 5 receives the block. -/

def c16a : S3 := enter1 [(none, none, 0), (none, some 0, 0), (some 1, some 0, 0),
  (some 1, some 0, 0), (none, none, 0)]
def ar16 : Arena := ⟨1, 1, [2, 3], []⟩
def c16b : S3 := enterEff (deriveEff (deriveEff c16a 0 0 .observe) 2 4 .modify) [3, 4]
  [(none, none, 0)]
def c16c : S3 × Arena := issueEff c16b ar16 [2] 5
def c16d : S3 := exitEff (transferEff c16c.1 5 4)
example : EnterStep [3, 4] [(none, none, 0)] (deriveEff (deriveEff c16a 0 0 .observe) 2 4 .modify)
    (.ok c16b) := .ok (by decide)
example : IssueStep KA ar16 3 [2] 5 c16b (.ok c16c.1 c16c.2) := .ok (by decide) (by decide) (by decide)
example : TransferStep KA 5 4 c16c.1 (.ok (transferEff c16c.1 5 4)) := .ok (by decide)
example : ExitStep (transferEff c16c.1 5 4) (.ok c16d) := .ok (by decide)
example : c16d.Active 6 ∧ (c16d.A[6]?).map (·.holder) = some (.place 4) := by decide
example : ResetStep KA c16c.2 0 c16d .reject := .reject (by decide)
example : EndUseStep KA 4 c16d (.ok (endUseEff c16d 4)) := .ok (by decide)
example : ResetStep KA c16c.2 0 (endUseEff c16d 4) (.ok (resetEff (endUseEff c16d 4) c16c.2)) :=
  .ok (by decide)

/-! ### Case 17: return of a value anchored on a local place of the callee (expected: reject) -/

def c17a : S3 := write3Eff (enterEff (deriveEff (enter1 [(none, none, 0)]) 0 0 .modify) [1]
  [(none, none, 0), (none, none, 0)]) [2]
example : DependStep 2 2 c17a (.ok (dependEff c17a 2 2)) := .ok (by decide)
example : TransferStep K0 2 0 (dependEff c17a 2 2) .reject := .reject (by decide)

/-! ### New cases of pass 2 -/

/-- The callee reads a local of the caller without a parameter (expected: reject). -/
example : Read3Step 0 [0] (enterEff c13a [] [(none, none, 0)]) .reject := .reject (by decide)

/-- `create_arena()` returned by a function (expected: `ok`, usable by the caller). Caller: 0
result, 1 buffer destination; parameter 2 modifies 0. Callee: 2 arena value, 3 storage owned by
2 with leaves 4, 5; `internal` is authority 4, held by place 2, then by place 0. -/
def n2a : S3 := enterEff (deriveEff (enter1 [(none, none, 0), (none, none, 0)]) 0 0 .modify) [2]
  [(none, none, 0), (none, some 2, 0), (some 3, some 2, 0), (some 3, some 2, 0)]
def n2b : S3 := exitEff (transferEff (write3Eff n2a [2]) 2 0)
def arN2 : Arena := ⟨3, 4, [4, 5], []⟩
example : TransferStep KA 2 0 (write3Eff n2a [2]) (.ok (transferEff (write3Eff n2a [2]) 2 0)) :=
  .ok (by decide)
example : ExitStep (transferEff (write3Eff n2a [2]) 2 0) (.ok n2b) := .ok (by decide)
example : n2b.Usable 3 ∧ n2b.Active 4 := by decide
example : IssueStep KA arN2 0 [4] 1 n2b (.ok (issueEff n2b arN2 [4] 1).1
    (issueEff n2b arN2 [4] 1).2) := .ok (by decide) (by decide) (by decide)

/-- `Vec` with owned storage returned by a function (expected: `ok`). Callee: 2 vector value,
3 buffer owned by 2; the caller then reads the buffer. -/
def n3a : S3 := enterEff (deriveEff (enter1 [(none, none, 0)]) 0 0 .modify) [1]
  [(none, none, 0), (none, some 1, 0)]
def n3b : S3 := exitEff (transferEff (write3Eff (write3Eff n3a [1]) [2]) 1 0)
example : Write3Step 3 [2] (write3Eff n3a [1]) (.ok (write3Eff (write3Eff n3a [1]) [2])) :=
  .ok (by decide)
example : TransferStep K0 1 0 (write3Eff (write3Eff n3a [1]) [2])
    (.ok (transferEff (write3Eff (write3Eff n3a [1]) [2]) 1 0)) := .ok (by decide)
example : ExitStep (transferEff (write3Eff (write3Eff n3a [1]) [2]) 1 0) (.ok n3b) := .ok (by decide)
example : Read3Step 3 [2] n3b (.ok n3b) := .ok (by decide)

/-- `endUse(p)` with an active derived authority held elsewhere (expected: reject), and with a
usable dependent anchored on `p` (expected: reject). -/
example : EndUseStep K0 0 (deriveEff c13a 0 0 .observe) .reject := .reject (by decide)
example : EndUseStep K0 0 (dependEff c13a 1 0) .reject := .reject (by decide)

/-- `alloc`, `process`, `free` at the end of the frame (`defer`), then `endUse` (expected:
`ok`); `free` during an active access, without a compatible deallocation authority, or of an
arena block (expected: reject). Frame 1: 0 box value, 1 owned storage. -/
abbrev KF : K := KT [] [] [] [1] [(1, 7)]
def n6a : S3 := write3Eff (enter1 [(none, none, 0), (none, some 0, 0)]) [1]
example : Write3Step 1 [1] (enter1 [(none, none, 0), (none, some 0, 0)]) (.ok n6a) := .ok (by decide)
example : FreeStep KF 1 7 n6a (.ok (freeEff n6a 1)) := .ok (by decide)
example : EndUseStep KF 0 (freeEff n6a 1) (.ok (endUseEff (freeEff n6a 1) 0)) := .ok (by decide)
example : FreeStep KF 1 7 (deriveEff n6a 1 1 .observe) .reject := .reject (by decide)
example : FreeStep KF 1 8 n6a .reject := .reject (by decide)
example : FreeStep (KT [0] [] [] [1] [(2, 7)]) 2 7 c6b.1 .reject := .reject (by decide)

/-- `endUse` of a value whose owned storage was not freed (expected: `ok`, reported as a leak):
the storage is logically dead and not freed. -/
example : EndUseStep KF 0 n6a (.ok (endUseEff n6a 0)) := .ok (by decide)
example : (endUseEff n6a 0).dead 1 = true ∧ (endUseEff n6a 0).freed 1 = false := by decide

/-- Two incompatible ordinary `Modify` authorities on a `SharedMutable` leaf (expected: reject);
two observations and a `writeShared` within the contract (expected: `ok`). -/
example : DeriveStep 0 0 .modify (deriveEff (enter1 [(none, none, 0)]) 0 0 .modify) .reject :=
  .reject (by decide)
example : WriteSharedStep KA 1 [0] c1c (.ok (write3Eff c1c [0])) := .ok (by decide)
example : WriteSharedStep K0 1 [0] c1c .reject := .reject (by decide)

/-- Return of a value anchored on a derivation of a derivation of a parameter (expected: `ok`).
Callee of case 8: 5 derived from parameter 2, 6 derived from 5; the value depends on 6. -/
def n9a : S3 := deriveEff (deriveEff c8c 2 0 .observe) 5 0 .observe
def n9b : S3 := transferEff (dependEff (write3Eff n9a [2]) 2 6) 2 1
example : DeriveStep 5 0 .observe (deriveEff c8c 2 0 .observe) (.ok n9a) := .ok (by decide)
example : TransferStep K0 2 1 (dependEff (write3Eff n9a [2]) 2 6) (.ok n9b) := .ok (by decide)
example : ExitStep n9b (.ok (exitEff n9b)) := .ok (by decide)
example : (exitEff n9b).D 1 = [0] := by decide

/-- Return of a value anchored on a local of the callee through two derivations (expected:
reject). Callee of case 10: 4 derived from the root of the local, 5 derived from 4. -/
def n9c : S3 := deriveEff (deriveEff c10a 2 1 .observe) 4 1 .observe
def n9d : S3 := transferEff (dependEff (write3Eff n9c [2]) 2 5) 2 0
example : TransferStep K0 2 0 (dependEff (write3Eff n9c [2]) 2 5) (.ok n9d) := .ok (by decide)
example : ExitStep n9d .reject := .reject (by decide)

/-- `issue` on a full arena (expected: `fail`, state unchanged): both regions issued, both
blocks ended, no `reset`. -/
def n10a : S3 := endUseEff (endUseEff c6c.1 4) 5
example : EndUseStep KA 4 c6c.1 (.ok (endUseEff c6c.1 4)) := .ok (by decide)
example : EndUseStep KA 5 (endUseEff c6c.1 4) (.ok n10a) := .ok (by decide)
example : IssueStep KA c6c.2 0 [2] 4 n10a (.fail n10a c6c.2) := .fail (by decide) (by decide)

/-- Pinning (A8): a value with an in-place pinned leaf cannot be transferred (case 13); a value
whose only owned storage is pinned can; `endUse` on a pinned leaf without `ExternalDone` is
rejected. -/
def n11a : S3 := write3Eff (enter1 [(none, none, 0), (none, some 0, 0), (none, none, 0)]) [0]
example : PinStep 1 n11a (.ok (pinEff n11a 1 true)) := .ok (by decide)
example : TransferStep K0 0 2 (pinEff n11a 1 true) (.ok (transferEff (pinEff n11a 1 true) 0 2)) :=
  .ok (by decide)
example : EndUseStep K0 0 (pinEff c13a 0 true) .reject := .reject (by decide)

/-! ## Findings cited by the report -/

/-- Contracts declaring every pair of regions disjoint, without the obligation `DDSound`. -/
def KDD : K := ⟨fun _ _ => True, fun _ => False, fun _ => False, fun _ _ _ => False, fun _ => False,
  fun _ => False, fun _ _ => False⟩
instance : ∀ r r', Decidable (KDD.DeclaredDisjoint r r') := fun _ _ => instDecidableTrue

/-- Without the obligation `DDSound` (MM-03.3.8), `split` (MM-03.3 §3, O2) accepts two overlapping
regions and breaks I1: the hypothesis of `split_preserves_underDD` is needed. -/
theorem split_unsound_without_DD :
    SplitStep KDD 0 [[1], [1]] c3a (.ok (splitEff c3a 0 [[1], [1]])) ∧
    ¬ I1 (splitEff c3a 0 [[1], [1]]) := by
  refine ⟨.ok (by decide), fun h => ?_⟩
  have := h 1 2 ⟨.modify, some 0, [1], .frame 1, true⟩ ⟨.modify, some 0, [1], .frame 1, true⟩ 1
    (by decide) (by decide) (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide)
  exact absurd this.1 (by decide)

/-- `exitFrame` (MM-03.3 §4, O7) accepts the exit of a frame whose local is pinned without
`ExternalDone`, while `endUse` and `transfer` of that local are rejected (A8 lists `transfer`,
`free`, `endUse`, `unpin`, not `exitFrame`). -/
example : ExitStep (pinEff c13a 0 true) (.ok (exitEff (pinEff c13a 0 true))) := .ok (by decide)
example : EndUseStep K0 0 (pinEff c13a 0 true) .reject := .reject (by decide)

/-- A callee releases a root authority of its caller without holding any right on it: `release`
is not in the list of A2, and O3 has no right condition. -/
example : ReleaseStep 0 (enterEff c13a [] [(none, none, 0)])
    (.ok (releaseEff (enterEff c13a [] [(none, none, 0)]) 0)) := .ok (by decide)

/-- Reading of A2 ("mode effectif ≥" compared with the mode of the held authority): while a value
is shared in `Observe`, the root of its owned storage, a `Modify` authority held by the value,
cannot be exercised, even to read. Frame 1: 0 value, 1 owned storage. -/
example : Read3Step 1 [1] n6a (.ok n6a) := .ok (by decide)
example : Read3Step 1 [1] (deriveEff n6a 0 0 .observe) .reject := .reject (by decide)

/-- `transfer` (MM-03.3 §3, O4; A5) does not preserve `Inv3` alone (A1): a part with another
owner than its parent (excluded by `WF3`) is not usable while its parent is; a place owned by
that part is not usable either and keeps an invalid anchor (5, which does not exist). The
transfer gives that place to the destination: it becomes usable with an invalid anchor. -/
theorem transfer_not_inv3_preserving :
    let s : S3 := ⟨[1, 0], 2, [⟨none, .frame 1, 0⟩, ⟨some 0, .frame 5, 0⟩, ⟨none, .place 1, 0⟩,
      ⟨none, .frame 1, 0⟩], fun l => if l = 1 then .init else .uninit,
      [⟨.modify, none, [1], .frame 1, true⟩, ⟨.modify, none, [3], .frame 1, true⟩],
      fun q => if q = 2 then [5] else [], fun _ => false, fun _ => false, fun _ => false⟩
    Inv3 s ∧ TransferStep K0 0 3 s (.ok (transferEff s 0 3)) ∧ ¬ I3 (transferEff s 0 3) := by
  intro s
  refine ⟨⟨fun a b x y p hab ha hb _ _ xp yp _ _ => ?_, fun b y a hb ho => ?_,
    fun q hq z hz => ?_, i4_always _⟩, .ok (by decide), fun h => ?_⟩
  · have h1 := lt_of_getElem? ha; have h2 := lt_of_getElem? hb
    simp [s] at h1 h2
    obtain rfl | rfl : a = 0 ∨ a = 1 := by omega
    all_goals obtain rfl | rfl : b = 0 ∨ b = 1 := by omega
    all_goals first | exact absurd rfl hab | (simp [s] at ha hb; subst ha hb; simp at xp yp; omega)
  · have := lt_of_getElem? hb; simp [s] at this
    obtain rfl | rfl : b = 0 ∨ b = 1 := by omega
    all_goals simp [s] at hb; subst hb; cases ho
  · cases Nat.decEq q 2 with
    | isTrue e => subst e; exact absurd hq (by decide)
    | isFalse e => simp [s, e] at hz
  · exact absurd (h 2 (by decide) 5 (by decide)) (by decide)

/-- With a duplicated frame on the stack (excluded by `WF3`), `exitFrame` (MM-03.3 §4, O7; A4)
keeps active an authority held by the exited frame: the hypothesis `s.F.Nodup` of
`exitFrame_releases_all` is needed. -/
theorem exit_duplicate_frame :
    let s : S3 := { enter1 [(none, none, 0)] with F := [1, 1, 0] }
    ExitStep s (.ok (exitEff s)) ∧
      (exitEff s).A[0]? = some ⟨.modify, none, [0], .frame 1, true⟩ := by
  intro s; exact ⟨.ok (by decide), by decide⟩

/-- Adding an authority held by a holder that is not live breaks the possession clause of `WF3`
(A4): the hypothesis `HolderLive s hd` of `addAuth_preserves` is needed. -/
theorem addAuth_needs_live_holder :
    let s : S3 := enter1 [(none, none, 0)]
    WF3 s ∧ Inv3 s ∧ Allows (effective s 0 0) .observe ∧
      ¬ WF3 (s.addAuth ⟨.observe, some 0, [0], .frame 7, true⟩) := by
  intro s
  have h : WF3 s ∧ Inv3 s :=
    reachable_access_invariant_underDD (KT_dd [] [] [] [] []) (.enter .init (.ok (by decide)))
  refine ⟨h.1, h.2, by decide, fun h' => ?_⟩
  exact absurd (h'.poss 1 ⟨.observe, some 0, [0], .frame 7, true⟩ (by decide) rfl) (by decide)

end Ern.MM03
