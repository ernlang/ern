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
`p`. Inductive, so no cycle justifies a right. -/
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

/-- Preconditions of `derive` (MM-03.3 §3, O1), in order: 1 active origin, exercisable (A2);
place still usable
(MM-03.3.1); 2 requested footprint within the origin's; 3 mode permitted by the effective
authority of the origin on each leaf; 4 every existing authority stays compatible with the
derived one in the resulting state. O1.5 is not restated: `derive` deactivates nothing. -/
def DerivePre (s : S3) (src q : Nat) (m : Mode) : Prop :=
  s.Active src ∧ s.Exercisable src ∧ s.Usable q ∧
  (∀ p ∈ footprint s.P q, p ∈ s.afp src) ∧
  (∀ p ∈ footprint s.P q, Allows (effective s src p) m) ∧
  (∀ b ∈ List.range s.A.length, ∀ p ∈ footprint s.P q,
    OptP (effective (deriveEff s src q m) b p) (fun e => Compat e m) True)

instance (s : S3) (src q : Nat) (m : Mode) : Decidable (DerivePre s src q m) := by
  unfold DerivePre Compat; infer_instance

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
the frame is popped, through transitive ownership (A4, A5). -/
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

/-- `canWrite3` (MM-03.3 §5): `a` exercisable by the current frame (A2); on each leaf,
effective `Modify` of `a`, no other authority with
a present effective mode, needed dependencies valid. The type and storage condition is not
represented. -/
def canWrite3 (s : S3) (a : Nat) (ls : List Nat) : Prop :=
  s.Exercisable a ∧ ∀ p ∈ ls, effective s a p = some .modify ∧
    (∀ b ∈ List.range s.A.length, b ≠ a → effective s b p = none) ∧ DepsValid s p

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
    {hd : Holder} (hx : s.A[src]? = some x) (xa : x.active = true)
    (hfp : ∀ p ∈ fp, p ∈ x.footprint) (hal : ∀ p ∈ fp, Allows (effective s src p) m) :
    I1 (s.addAuth ⟨m, some src, fp, hd, true⟩) := by
  have hs := lt_of_getElem? hx
  intro a b x' y' p hab ha hb xa' ya' xp yp hnab hnba
  rcases addAuth_get ha with ⟨ha', ha''⟩ | ⟨rfl, rfl⟩ <;>
    rcases addAuth_get hb with ⟨hb', hb''⟩ | ⟨rfl, rfl⟩
  · rw [ancs_addAuth_lt hb'] at hnab; rw [ancs_addAuth_lt ha'] at hnba
    exact ht a b x' y' p hab ha'' hb'' xa' ya' xp yp hnab hnba
  · rw [ancs_addAuth_self rfl hs] at hnab
    exact (new_vs_old ht hx xa (hfp p yp) (hal p yp) ha'' xa' xp
      (fun e => hnab (e ▸ List.mem_cons_self ..)) fun e => hnab (List.mem_cons_of_mem _ e)).symm
  · rw [ancs_addAuth_self rfl hs] at hnba
    exact new_vs_old ht hx xa (hfp p xp) (hal p xp) hb'' ya' yp
      (fun e => hnba (e ▸ List.mem_cons_self ..)) fun e => hnba (List.mem_cons_of_mem _ e)
  · exact absurd rfl hab

/-- Adding an active authority derived from `src`, with a footprint within `src`'s, a mode
permitted on each leaf, and a live holder, preserves `WF3` and `Inv3`. Shared by `derive`,
`split` and `issue`. -/
theorem addAuth_preserves {s : S3} (hwf : WF3 s) (hinv : Inv3 s) {src : Nat} {x : Authority}
    {m : Mode} {fp : List Nat} {hd : Holder} (hx : s.A[src]? = some x) (xa : x.active = true)
    (hfp : ∀ p ∈ fp, p ∈ x.footprint) (hal : ∀ p ∈ fp, Allows (effective s src p) m)
    (hl : HolderLive s hd) :
    WF3 (s.addAuth ⟨m, some src, fp, hd, true⟩) ∧ Inv3 (s.addAuth ⟨m, some src, fp, hd, true⟩) := by
  obtain ⟨i1, i2, i3, -⟩ := hinv
  have hs := lt_of_getElem? hx
  have live := HolderLive.congr (addAuth_P s ⟨m, some src, fp, hd, true⟩) rfl rfl
  refine ⟨⟨?_, ?_, hwf.ne, hwf.nodup, hwf.frames, hwf.ownerFrame, hwf.ownerPlace, hwf.parts, ?_⟩,
    addAuth_I1 i1 hx xa hfp hal, ?_, fun q hq y hy => active_addAuth (i3 q ?_ y hy), i4_always _⟩
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
  obtain ⟨⟨⟨x, hx, xa⟩, -, -, hfp, hal, -⟩, rfl⟩ := Guarded.ok_iff.1 h
  exact addAuth_preserves hwf hinv hx xa (fun p hp => by simpa [S3.afp, hx] using hfp p hp) hal
    (top_mem hwf.ne)

/-- `derive_preserves_exclusivity` (MM-03.3 §10): `derive` preserves I1, under I1 alone. -/
theorem derive_preserves_exclusivity {s s' : S3} {src q : Nat} {m : Mode} (h1 : I1 s)
    (h : DeriveStep src q m s (.ok s')) : I1 s' := by
  obtain ⟨⟨⟨x, hx, xa⟩, -, -, hfp, hal, -⟩, rfl⟩ := Guarded.ok_iff.1 h
  exact addAuth_I1 h1 hx xa (fun p hp => by simpa [S3.afp, hx] using hfp p hp) hal

theorem split_aux {src : Nat} {x : Authority} : ∀ (rs : List (List Nat)) (s : S3), WF3 s →
    Inv3 s → s.A[src]? = some x → x.active = true →
    (∀ r ∈ rs, ∀ p ∈ r, effective s src p = some .modify ∧ p ∈ x.footprint) →
    rs.Pairwise (fun r r' => ∀ l ∈ r, l ∉ r') →
    WF3 (splitEff s src rs) ∧ Inv3 (splitEff s src rs)
  | [], s, hwf, hinv, _, _, _, _ => by
    have : splitEff s src [] = s := by simp [splitEff]
    rw [this]; exact ⟨hwf, hinv⟩
  | r :: rs, s, hwf, hinv, hx, xa, hr, hpw => by
    rw [splitEff_cons]
    have hs := lt_of_getElem? hx
    obtain ⟨hwf₁, hinv₁⟩ := addAuth_preserves (hd := .frame s.top) hwf hinv hx xa
      (fun p hp => (hr r (List.mem_cons_self ..) p hp).2)
      (fun p hp => by rw [(hr r (List.mem_cons_self ..) p hp).1]; simp [Allows, OptP, Mode.le])
      (top_mem hwf.ne)
    obtain ⟨hpr, hpw⟩ := List.pairwise_cons.1 hpw
    refine split_aux rs _ hwf₁ hinv₁ (by rw [addAuth_lt hs]; exact hx) xa (fun r' hr' p hp => ?_) hpw
    rw [effective_addAuth_notin hs fun h => hpr r' hr' p h hp]
    exact hr r' (List.mem_cons_of_mem _ hr') p hp

/-- `split` preserves `WF3` and `Inv3` (MM-03.3 §3, O2; §10), under the obligation `DDSound k`
of `DeclaredDisjoint` (MM-03.3.8). -/
theorem split_preserves_underDD {k : K} (hdd : DDSound k) {s s' : S3} {src : Nat}
    {rs : List (List Nat)} (hwf : WF3 s) (hinv : Inv3 s) (h : SplitStep k src rs s (.ok s')) :
    WF3 s' ∧ Inv3 s' := by
  obtain ⟨⟨⟨x, hx, xa⟩, -, h1, h2, h3, -⟩, rfl⟩ := Guarded.ok_iff.1 h
  refine split_aux rs s hwf hinv hx xa (fun r hr p hp => ⟨h1 r hr p hp, ?_⟩)
    (h3.imp fun {r r'} h => h.elim id fun hd => hdd r r' hd)
  simpa [S3.afp, hx] using (h2 r hr p hp).1

/-- `split_preserves_exclusivity` (MM-03.3 §10), under `DDSound k` (MM-03.3.8). -/
theorem split_preserves_exclusivity_underDD {k : K} (hdd : DDSound k) {s s' : S3} {src : Nat}
    {rs : List (List Nat)} (hwf : WF3 s) (hinv : Inv3 s) (h : SplitStep k src rs s (.ok s')) :
    I1 s' := (split_preserves_underDD hdd hwf hinv h).2.1

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
    (hii : i ≠ i') (hi : i < ls.length) (hi' : i' < ls.length) (hn : (ls[i]?).bind (·.1) = none)
    (hn' : (ls[i']?).bind (·.1) = none)
    (h : l ∈ footprint (enterP s ls) (s.P.length + i))
    (h' : l ∈ footprint (enterP s ls) (s.P.length + i')) : False := by
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
      exact (enter_roots_disjoint hii (rootIdx_mem hi).1 (rootIdx_mem hi').1 (rootIdx_mem hi).2
        (rootIdx_mem hi').2 xp yp).elim
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

/-- The first surviving strict ancestor along `origin` (A7): it is an ancestor, it survives, and
every surviving ancestor is it or one of its own ancestors. -/
theorem firstSurv_ancs {s : S3} {F₀ : Frames} (hw : ∀ (b : Nat) (y : Authority) (a : Nat),
    s.A[b]? = some y → y.origin = some a → a < b) :
    ∀ n x, x < n → ∀ z, firstSurv s F₀ (s.ancs x) = some z →
      z ∈ s.ancs x ∧ Survives s F₀ z ∧
        ∀ w ∈ s.ancs x, Survives s F₀ w → w = z ∨ w ∈ s.ancs z
  | 0, _, h, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, x, hx, z, hz => by
    cases ho : s.org x with
    | none => rw [S3.ancs, chain_none ho] at hz; simp [firstSurv] at hz
    | some o =>
      have hlt := org_lt hw ho
      rw [ancs_cons hw ho] at hz ⊢
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
        obtain ⟨h1, h2, h3⟩ := firstSurv_ancs hw n o (by omega) z hz
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
theorem i2_chain {s : S3} (h2 : I2 s) (hw : ∀ (b : Nat) (y : Authority) (a : Nat),
    s.A[b]? = some y → y.origin = some a → a < b) :
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
      rw [ancs_cons hw hob] at hz
      obtain ⟨x, hx, hh⟩ := h2 b y o hy ho
      rcases List.mem_cons.1 hz with rfl | hz
      · exact ⟨x, hx, hh⟩
      · obtain ⟨x', hx', hh'⟩ := i2_chain h2 hw n o (by have := org_lt hw hob; omega) x z hx hz
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

theorem exitG_origin {s : S3} {F₀ : Frames} {a : Nat} {y : Authority} :
    (exitG s F₀ a y).origin = y.origin ∨
    (Survives s F₀ a ∧ y.origin ≠ none ∧ (exitG s F₀ a y).origin = firstSurv s F₀ (s.ancs a)) := by
  unfold exitG; split
  · rename_i hs; split
    · exact .inl rfl
    · rename_i o ho; exact .inr ⟨hs, by simp [ho], rfl⟩
  · exact .inl rfl

/-- After the exit, the surviving ancestors of any authority are still its ancestors (A7). -/
theorem exit_ancs_keep {s : S3} {f : Nat} {F₀ : Frames} (hF : s.F = f :: F₀)
    (hw : ∀ (b : Nat) (y : Authority) (a : Nat), s.A[b]? = some y → y.origin = some a → a < b) :
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
        have hlt := org_lt hw hob
        have e' : (exitEff s).org x = (exitG s F₀ x y).origin := by
          simp [S3.org, exit_A_get hF, hy]
        rcases exitG_origin (s := s) (F₀ := F₀) (a := x) (y := y) with e | ⟨-, -, e⟩
        · rw [e, ho] at e'
          rw [show (exitEff s).ancs x = o :: (exitEff s).ancs o from chain_cons e' hlt]
          rw [ancs_cons hw hob] at hw'
          rcases List.mem_cons.1 hw' with rfl | hw'
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (exit_ancs_keep hF hw n o (by omega) w hw' hws)
        · rw [e] at e'
          cases hz : firstSurv s F₀ (s.ancs x) with
          | none => exact absurd hws (firstSurv_none hz w hw')
          | some z =>
            rw [hz] at e'
            obtain ⟨hz1, -, hz3⟩ := firstSurv_ancs hw (x + 1) x (Nat.lt_succ_self x) z hz
            have hzx := chain_lt hz1
            rw [show (exitEff s).ancs x = z :: (exitEff s).ancs z from chain_cons e' hzx]
            rcases hz3 w hw' hws with rfl | hw''
            · exact List.mem_cons_self ..
            · exact List.mem_cons_of_mem _ (exit_ancs_keep hF hw n z (by omega) w hw'' hws)

/-- `exitFrame` preserves `WF3` and `Inv3` (MM-03.3 §4, O7; §10; A4; A5; A7). -/
theorem exit_preserves {s s' : S3} (hwf : WF3 s) (hinv : Inv3 s) (h : ExitStep s (.ok s')) :
    WF3 s' ∧ Inv3 s' := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  unfold ExitPre at hpre
  split at hpre
  · rename_i f F₀ hF
    obtain ⟨hne, hR1, -⟩ := hpre
    obtain ⟨i1, i2, i3, -⟩ := hinv
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
    have keep := exit_ancs_keep hF hwf.origin
    refine ⟨⟨fun b y a hb ho => ?_, fun a x hx l hl => ?_, hFe ▸ hne, hFe ▸ hnd.2,
      fun g hg => ?_, hP ▸ hn ▸ hwf.ownerFrame, hP ▸ hwf.ownerPlace, hP ▸ hd ▸ hwf.parts,
      fun a y hy ya => ?_⟩, fun a b x y p hab ha hb xa ya xp yp hnab hnba => ?_,
      fun b y a hb ho => ?_, fun q hq x hx => ?_, i4_always _⟩
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
        obtain ⟨x₁, hx₁, hh⟩ := i2_chain i2 hwf.origin (b + 1) b (Nat.lt_succ_self b) y₀ a hy₀
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

/-- `exitFrame_releases_all` (MM-03.3 §4, O7; §10): after the exit, every active authority has
a live holder; none is held by the exited frame. -/
theorem exitFrame_releases_all {s s' : S3} {f : Nat} {F₀ : Frames} (hwf : WF3 s) (hinv : Inv3 s)
    (hF : s.F = f :: F₀) (h : ExitStep s (.ok s')) :
    ∀ (j : Nat) (y : Authority), s'.A[j]? = some y → y.active = true →
      HolderLive s' y.holder ∧ y.holder ≠ .frame f := by
  have hp := exit_preserves hwf hinv h
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
  intro j y hy ya
  have hl := hp.1.poss j y hy ya
  refine ⟨hl, fun he => ?_⟩
  rw [he] at hl
  have hnd := List.nodup_cons.1 (hF ▸ hwf.nodup)
  have : (exitEff s).F = F₀ := by rw [exitEff_eq hF]
  exact hnd.1 (this ▸ hl)

/-- `exitFrame_kills_locals` (MM-03.3.1; MM-03.3 §4, O7; A5): after the exit, every usable place
was usable before; a place owned by the exited frame is no longer usable, nor is any place whose
owner chain passed through such a place; and no active authority is held by a holder that is no
longer live. -/
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
    ∀ q, s'.Usable q → ∀ x ∈ s.D q, ∃ z, (z = x ∨ z ∈ s.ancs x) ∧ z ∈ s'.D q ∧ s'.Active z := by
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
    refine ⟨z, ?_, hmem, hp.2.2.2.1 q hq z hmem⟩
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
  exact ⟨y, hy, ya, exitFrame_releases_all hwf hinv hF h x y hy ya⟩

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

end Ern.MM03
