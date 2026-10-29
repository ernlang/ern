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
      · simp only [kstab, List.all_eq_false, List.mem_range, beq_iff_eq] at hs
        obtain ⟨a, ha, hne⟩ := hs
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
    | .frame f => f == s.top
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
  simp [exR, hy, ha, hf]

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
leaf of `q` (A2: "`Modify` exerçable sur `p`"). -/
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

end Ern.MM03
