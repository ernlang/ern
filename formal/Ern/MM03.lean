import Ern.MM02

/-!
# MM-03.3 v0.2: kernel of the access discipline (exploratory model, milestone 1, pass 3)

Abstract layer of `formal/DESIGN.md` ("Abstract model"): memory is a finite tree of places.
Refinement towards MM-02 (MM-03.3 §9) is milestone 2 and is not treated here; the module
imports `Ern.MM02` without using or changing it. Covered fragment: sequential execution of the
kernel operations (MM-03.3 §3–5) and of the arena (§6); no concurrency, no persistent handles.

Pass 2 follows arbitrages A1–A11 of the task: authorities are held by a frame or a place (A4),
places are owned by a frame or a place (A5), rights are exercised through `ExercisableAt` (A2, B2),
values end by `endUse` and owned storage is released by `free` (A6). Pass 3 adds arbitrages
B1–B10: two clauses of `WF3` (B1) and the clause `AnchorOrder` of `Inv3` (B8).
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

theorem footprint_congr {P P' : List Place} (hlen : P'.length = P.length)
    (hpar : parentOf P' = parentOf P) (q : Nat) : footprint P' q = footprint P q := by
  unfold footprint; rw [hlen]; congr 1; funext l
  exact decide_eq_decide.2 (by simp only [isLeaf, partOf, hpar, hlen])

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

/-- An arena entry (MM-03.3 §6; A10; D3; F1): `storage` is the place of the administered storage;
`internal` is the authority that administers it, named by `newArena` (F1); `available` and
`issued` are the logical state of §6, `issued` mapping each issued region to the issued block.
The arena value is not a field: it is the place that holds `internal` (F1), which follows
transfers (A4). The anchor of §6 is not a field either: dependents anchor on the blocks (A10). -/
structure Arena where
  storage : Nat
  internal : Nat
  available : List Nat
  issued : List (List Nat × Nat)
deriving DecidableEq

/-- State `S3 = (F, P, I, A, D)` (MM-03.3 §1), without component `M` (pass-1 arbitrage 1).
`nF` is the next frame identity, so that an exited frame is never reused. `D q` lists the
anchors of place `q`, each an authority identity (pass-1 arbitrage 2). `dead q`: the place is
logically dead (A6, `endUse` and `free`); `freed q`: its storage was released by `free` (A6);
`pin l`: leaf `l` is dynamically pinned (A8). `arenas`: the arena entries registered by
`newArena` (D3). `callParams f`: the parameters given to frame `f` by `enterFrame`, a ghost record
(F6): set by `enterFrame`, never modified, read by no operation. -/
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
  arenas : List Arena
  callParams : Nat → List Nat

/-- Contracts `K` (MM-03.3.8) for an execution. Types are a representation choice: regions as
lists of leaves; `SharedMutable`, `Pinned` and `ExternalDone` on leaves; `Deallocable p` and
`FreeCompat p auth` for `free` (A6); `Satisfiable provider shape s` for `alloc` (B5; C9: it
depends on the current state `s`, with the shape encoded as the locals of `enterFrame`, C6).
`Invalidates` is removed (B9). The obligations of each contract are named hypotheses of theorems, never
fields. -/
structure K where
  DeclaredDisjoint : List Nat → List Nat → Prop
  SharedMutable : Nat → Prop
  Pinned : Nat → Prop
  ExternalDone : Nat → Prop
  Deallocable : Nat → Prop
  FreeCompat : Nat → Nat → Prop
  Satisfiable : Nat → List (Option Nat × Option Nat × Nat) → S3 → Prop

/-- Obligation of `DeclaredDisjoint` (MM-03.3.8): a declaration never covers two regions that
really overlap. -/
def DDSound (k : K) : Prop := ∀ r r', k.DeclaredDisjoint r r' → ∀ l ∈ r, l ∉ r'

/-- `origin` link of the authority with index `i` (MM-03.3.4). -/
def S3.org (s : S3) (i : Nat) : Option Nat := (s.A[i]?).bind (·.origin)

/-- Strict ancestors of authority `i` along `origin`: `i` descends from each (MM-03.3.5). -/
def S3.ancs (s : S3) (i : Nat) : List Nat := chain s.org i

/-- Effective anchor of an anchor `x` (C1): the root of its chain of origins (`RootChain`), the
last element of `x :: s.ancs x`. -/
def S3.effAnchor (s : S3) (x : Nat) : Nat := (s.ancs x).getLastD x

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

`Usable` (A5) and `ExercisableAt` (B2) are inductive predicates. Each is the least fixed point of
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

/-! ## Frames of places (A5) -/

theorem kiter_mono_le {n : Nat} {R : (Nat → Bool) → Nat → Bool} (h : KRule n R) :
    ∀ j k a, kiter R k a = true → kiter R (k + j) a = true
  | 0, _, _, hk => hk
  | j + 1, k, a, hk => kiter_mono h _ a (kiter_mono_le h j k a hk)

theorem kiter_ge {n : Nat} {R : (Nat → Bool) → Nat → Bool} (h : KRule n R) :
    ∀ j, kiter R (n + 1 + j) = kiter R (n + 1)
  | 0 => rfl
  | j + 1 => funext fun a => by
    show R (kiter R (n + 1 + j)) a = kiter R (n + 1) a
    rw [kiter_ge h j]; exact kiter_fix h a

/-- A conclusion reached at some step of the iteration is reached at step `n + 1`. -/
theorem kiter_up {n : Nat} {R : (Nat → Bool) → Nat → Bool} (h : KRule n R) :
    ∀ k a, kiter R k a = true → kiter R (n + 1) a = true := by
  intro k a hk
  by_cases hkn : k ≤ n + 1
  · have := kiter_mono_le h (n + 1 - k) k a hk
    rwa [show k + (n + 1 - k) = n + 1 by omega] at this
  · obtain ⟨j, rfl⟩ : ∃ j, k = n + 1 + j := ⟨k - (n + 1), by omega⟩
    rwa [kiter_ge h j] at hk

/-- `FrameOf s q f` (A5): the owner chain of place `q` ends at frame `f`. -/
inductive FrameOf (s : S3) : Nat → Nat → Prop where
  | frame {q f : Nat} {pl : Place} : s.P[q]? = some pl → pl.owner = .frame f → FrameOf s q f
  | place {q o f : Nat} {pl : Place} : s.P[q]? = some pl → pl.owner = .place o → FrameOf s o f →
      FrameOf s q f

theorem FrameOf.lt {s : S3} {q f : Nat} (h : FrameOf s q f) : q < s.P.length := by
  cases h <;> exact lt_of_getElem? ‹_›

/-- The frame of a place is unique. -/
theorem FrameOf.det {s : S3} {q f f' : Nat} (h : FrameOf s q f) (h' : FrameOf s q f') : f = f' := by
  induction h generalizing f' with
  | frame hpl ho => cases h' with
    | frame hpl' ho' => rw [hpl] at hpl'; cases hpl'; rw [ho] at ho'; cases ho'; rfl
    | place hpl' ho' _ => rw [hpl] at hpl'; cases hpl'; rw [ho] at ho'; cases ho'
  | place hpl ho _ ih => cases h' with
    | frame hpl' ho' => rw [hpl] at hpl'; cases hpl'; rw [ho] at ho'; cases ho'
    | place hpl' ho' hf' => rw [hpl] at hpl'; cases hpl'; rw [ho] at ho'; cases ho'; exact ih hf'

/-- One step of `FrameOf s · f`, read on a Boolean premise. -/
def frR (s : S3) (f : Nat) (U : Nat → Bool) (q : Nat) : Bool :=
  match s.P[q]? with
  | some pl => match pl.owner with
    | .frame g => decide (g = f)
    | .place o => decide (o < s.P.length) && U o
  | none => false

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
          | succ k => simp [pframeF, List.getElem?_eq_none (Nat.le_of_not_lt hlt)]
    · simp

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

/-- `pframe` computes `FrameOf` (A5): the fuel `|P| + 1` suffices. -/
theorem pframe_iff {s : S3} {q f : Nat} : s.pframe q = some f ↔ FrameOf s q f := by
  rw [S3.pframe, pframeF_kiter]
  refine ⟨frameOf_of_kiter s f _ q, fun h => ?_⟩
  induction h with
  | frame hpl ho => exact kiter_up (frR_rule s _) 1 _ (by simp [kiter, frR, hpl, ho])
  | place hpl ho hf ih =>
    apply kiter_up (frR_rule s _) (s.P.length + 2) _
    show frR s _ (kiter (frR s _) (s.P.length + 1)) _ = true
    simp [frR, hpl, ho, ih, hf.lt]

/-- A usable place has a frame on the stack (A5). -/
theorem S3.Usable.frameOf {s : S3} {q : Nat} (h : s.Usable q) : ∃ f, FrameOf s q f ∧ f ∈ s.F := by
  induction h with
  | frame hpl _ ho hf => exact ⟨_, .frame hpl ho, hf⟩
  | place hpl _ ho _ ih => obtain ⟨f, hf, hm⟩ := ih; exact ⟨f, .place hpl ho hf, hm⟩

theorem FrameOf.congr {s s' : S3} (hP : s'.P = s.P) {q f : Nat} : FrameOf s' q f ↔ FrameOf s q f :=
  ⟨fun h => by induction h with
    | frame hpl ho => exact .frame (hP ▸ hpl) ho
    | place hpl ho _ ih => exact .place (hP ▸ hpl) ho ih,
   fun h => by induction h with
    | frame hpl ho => exact .frame (hP ▸ hpl) ho
    | place hpl ho _ ih => exact .place (hP ▸ hpl) ho ih⟩

theorem S3.pframe_congr {s s' : S3} (hP : s'.P = s.P) (q : Nat) : s'.pframe q = s.pframe q :=
  Option.ext fun f => by rw [pframe_iff, pframe_iff, FrameOf.congr hP]

theorem S3.hframe_congr {s s' : S3} (hP : s'.P = s.P) (h : Holder) : s'.hframe h = s.hframe h := by
  cases h with
  | frame f => rfl
  | place p => exact S3.pframe_congr hP p

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

/-- C1: the frame of the effective anchor of `x` exists and is `fd`, the frame of the dependent,
or one of its ancestors (MM-03.3.1, `ancestor`). The frame of an authority is the frame of its
holder (A4, A5). -/
def EffAnchorOK (s : S3) (x : Nat) (fd : Option Nat) : Prop :=
  OptP (s.A[s.effAnchor x]?) (fun z => OptP (s.hframe z.holder)
    (fun g => OptP fd (fun f => ancestor s.F g f) False) False) False

instance (s : S3) (x : Nat) (fd : Option Nat) : Decidable (EffAnchorOK s x fd) := by
  unfold EffAnchorOK; infer_instance

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

/-! ## Exercisable authorities (A2, B2) -/

/-- `s.ExercisableAt a m` (B2): authority `a` is exercisable at mode `m` when `m` does not exceed its
mode and it is held by the current frame, or held by a place `p` such that an authority
exercisable at mode `m` has an effective mode permitting `m` on the whole footprint of `p`. The
authority is active: the rights of a released authority cannot be exercised (MM-03.3 §3, O3).
Inductive, so no cycle justifies a right. -/
inductive S3.ExercisableAt (s : S3) : Nat → Mode → Prop where
  | base {a : Nat} {m : Mode} {y : Authority} : s.A[a]? = some y → y.active = true → m.le y.mode →
      y.holder = .frame s.top → S3.ExercisableAt s a m
  | held {a p b : Nat} {m : Mode} {y : Authority} : s.A[a]? = some y → y.active = true →
      m.le y.mode → y.holder = .place p → S3.ExercisableAt s b m →
      (∀ l ∈ footprint s.P p, Allows (effective s b l) m) → S3.ExercisableAt s a m

/-- One step of `ExercisableAt · m`, read on a Boolean premise. -/
def exR (s : S3) (m : Mode) (E : Nat → Bool) (a : Nat) : Bool :=
  match s.A[a]? with
  | some y => y.active && decide (m.le y.mode) && match y.holder with
    | .frame f => decide (f = s.top)
    | .place p => (List.range s.A.length).any fun b =>
        decide (∀ l ∈ footprint s.P p, Allows (effective s b l) m) && E b
  | none => false

theorem any_congr' {α : Type} {f g : α → Bool} : ∀ {l : List α}, (∀ b ∈ l, f b = g b) →
    l.any f = l.any g
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.any_cons, h a (List.mem_cons_self ..),
      any_congr' fun b hb => h b (List.mem_cons_of_mem a hb)]

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

theorem exR_base {s : S3} {m : Mode} {E : Nat → Bool} {a : Nat} {y : Authority}
    (hy : s.A[a]? = some y) (ha : y.active = true) (hm : m.le y.mode)
    (hf : y.holder = .frame s.top) : exR s m E a = true := by
  unfold exR; rw [hy]; simp [ha, hm, hf]

theorem exR_held {s : S3} {m : Mode} {E : Nat → Bool} {a p b : Nat} {y : Authority}
    (hy : s.A[a]? = some y) (ha : y.active = true) (hm : m.le y.mode) (hp : y.holder = .place p)
    (hb : b < s.A.length) (hc : ∀ l ∈ footprint s.P p, Allows (effective s b l) m)
    (hE : E b = true) : exR s m E a = true := by
  simp only [exR, hy, ha, hp, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq,
    List.any_eq_true, List.mem_range]
  exact ⟨hm, b, hb, hc, hE⟩

theorem exercisableAt_iff {s : S3} {a : Nat} {m : Mode} :
    s.ExercisableAt a m ↔ kiter (exR s m) (s.A.length + 1) a = true := by
  refine ⟨fun h => ?_, exercisableAt_of_kiter s m _ a⟩
  induction h with
  | base hy ha hm hf => exact exR_base hy ha hm hf
  | held hy ha hm hp hb hc ih =>
    rw [← kiter_fix (exR_rule s _)]
    have hb' := kiter_bound (exR_rule s _) _ _ ih
    exact exR_held hy ha hm hp hb' hc ih

instance (s : S3) (a : Nat) (m : Mode) : Decidable (s.ExercisableAt a m) :=
  decidable_of_iff _ exercisableAt_iff.symm

/-- The current frame has an authority exercisable at mode `m` whose effective mode permits `m` on
every leaf of `q` (B2: an operation requires the mode it requests). -/
def HasRight (s : S3) (m : Mode) (q : Nat) : Prop :=
  ∃ a ∈ List.range s.A.length, s.ExercisableAt a m ∧
    ∀ l ∈ footprint s.P q, Allows (effective s a l) m

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

/-- Preconditions of `derive` (MM-03.3 §3, O1), in order: 1 active origin, exercisable at the
requested mode (B2);
place still usable (MM-03.3.1); 2 requested footprint within the origin's; 3 mode permitted by
the effective authority of the origin on each leaf. O1.4 is removed (A11): it follows from the
others under I1 (`derive_compat_redundant`). O1.5 is not restated: `derive` deactivates
nothing. -/
def DerivePre (s : S3) (src q : Nat) (m : Mode) : Prop :=
  s.Active src ∧ s.ExercisableAt src m ∧ s.Usable q ∧
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

/-- Preconditions of `split` (MM-03.3 §3, O2), in order: 1 the origin is an active authority,
exercisable at `Modify` (B2), with effective `Modify` on every leaf of the regions; 2 regions within the available footprint
(the origin's footprint where its effective authority is present); 3 regions pairwise disjoint,
structurally (no shared leaf) or by `DeclaredDisjoint` (MM-03.3.8); 4 no region covers an
exclusive right already distributed. O2.5 is not restated: `split` changes neither `D` nor
activity. -/
def SplitPre (k : K) (s : S3) (src : Nat) (rs : List (List Nat)) : Prop :=
  s.Active src ∧ s.ExercisableAt src .modify ∧ (∀ r ∈ rs, ∀ p ∈ r, effective s src p = some .modify) ∧
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
authority becomes inactive. F4: an authority held by a place `q` leaves the anchors of `q` in the
same transition. -/
def releaseEff (s : S3) (a : Nat) : S3 := match s.A[a]? with
  | some x => { s with
      A := s.A.set a { x with active := false }
      D := fun q => if x.holder = .place q then (s.D q).filter (· != a) else s.D q }
  | none => s

/-- Right of the current frame on a holder (C4): the holder is the current frame, or a place on
which the current frame has exercisable `Modify` (`HasRight`, B2). -/
def HolderRight (s : S3) : Holder → Prop
  | .frame f => f = s.top
  | .place p => HasRight s .modify p

instance (s : S3) (h : Holder) : Decidable (HolderRight s h) := by
  cases h <;> unfold HolderRight <;> infer_instance

/-- Preconditions of `release` (MM-03.3 §3, O3), in order: 1 active authority; 2 no active
descendant; 3 no usable place has `a` as anchor, except the place that holds `a`, whose anchor
`a` is removed by the release (F4); C4: the authority is derived, an authority
without origin is rejected, and its holder is the current frame or a place on which the current
frame has exercisable `Modify` (`HolderRight`). O3.4 (guarantees of associated abstractions) is
not represented in the kernel. -/
def ReleasePre (s : S3) (a : Nat) : Prop :=
  s.Active a ∧
  (∀ j ∈ List.range s.A.length, a ∈ s.ancs j → ¬ s.Active j) ∧
  (∀ q ∈ List.range s.P.length, s.Usable q → a ∈ s.D q → (s.A[a]?).map (·.holder) = some (.place q)) ∧
  OptP (s.A[a]?) (fun y => y.origin ≠ none ∧ HolderRight s y.holder) False

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

/-- Place `q` is owned by `src` or one of its parts, directly or through other owned places,
searched within `k` steps (A5). -/
def ownedWithinF (s : S3) (src : Nat) : Nat → Nat → Bool
  | 0, _ => false
  | k + 1, q =>
    match s.P[q]? with
    | some pl =>
      match pl.owner with
      | .place o => decide (partOf s.P o src) || ownedWithinF s src k o
      | .frame _ => false
    | none => false

/-- Place `q` is owned, transitively, by the value at `src` (A5): its frame changes with the
value when `src` is transferred. -/
def OwnedWithin (s : S3) (src q : Nat) : Prop := ownedWithinF s src (s.P.length + 1) q = true

instance (s : S3) (src q : Nat) : Decidable (OwnedWithin s src q) :=
  inferInstanceAs (Decidable (_ = true))

/-- `OwnedIn P src q` (A5): the owner chain of place `q` reaches a place owned by `src` or one of
its parts. -/
inductive OwnedIn (P : List Place) (src : Nat) : Nat → Prop where
  | direct {q o : Nat} {pl : Place} : P[q]? = some pl → pl.owner = .place o → partOf P o src →
      OwnedIn P src q
  | step {q o : Nat} {pl : Place} : P[q]? = some pl → pl.owner = .place o → OwnedIn P src o →
      OwnedIn P src q

theorem OwnedIn.lt {P : List Place} {src q : Nat} (h : OwnedIn P src q) : q < P.length := by
  cases h <;> exact lt_of_getElem? ‹_›

/-- One step of `OwnedIn`, read on a Boolean premise. -/
def owR (s : S3) (src : Nat) (U : Nat → Bool) (q : Nat) : Bool :=
  match s.P[q]? with
  | some pl => match pl.owner with
    | .place o => decide (partOf s.P o src) || (decide (o < s.P.length) && U o)
    | .frame _ => false
  | none => false

theorem owR_rule (s : S3) (src : Nat) : KRule s.P.length (owR s src) where
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
      · rename_i o _; by_cases ho : o < s.P.length <;> simp [ho, hpq o]
      · rfl
    · rfl

theorem ownedWithinF_kiter (s : S3) (src : Nat) :
    ∀ k q, ownedWithinF s src k q = kiter (owR s src) k q
  | 0, _ => rfl
  | k + 1, q => by
    simp only [ownedWithinF, kiter, owR]
    split
    · split
      · rename_i o _
        by_cases hlt : o < s.P.length
        · simp [hlt, ownedWithinF_kiter s src k o]
        · have : ownedWithinF s src k o = false := by
            cases k with
            | zero => rfl
            | succ k => simp [ownedWithinF, List.getElem?_eq_none (Nat.le_of_not_lt hlt)]
          simp [hlt, this]
      · rfl
    · rfl

theorem ownedIn_of_kiter (s : S3) (src : Nat) :
    ∀ k q, kiter (owR s src) k q = true → OwnedIn s.P src q
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
        · exact .step hpl ho (ownedIn_of_kiter s src k o h)
      · cases h
    · cases h

/-- `OwnedWithin` computes `OwnedIn` (A5): the fuel `|P| + 1` suffices. -/
theorem ownedWithin_iff {s : S3} {src q : Nat} : OwnedWithin s src q ↔ OwnedIn s.P src q := by
  unfold OwnedWithin; rw [ownedWithinF_kiter]
  refine ⟨ownedIn_of_kiter s src _ q, fun h => ?_⟩
  induction h with
  | direct hpl ho hp => exact kiter_up (owR_rule s src) 1 _ (by simp [kiter, owR, hpl, ho, hp])
  | step hpl ho ho' ih =>
    apply kiter_up (owR_rule s src) (s.P.length + 2) _
    show owR s src (kiter (owR s src) (s.P.length + 1)) _ = true
    simp [owR, hpl, ho, ih, ho'.lt]

instance (s : S3) (src q : Nat) : Decidable (OwnedIn s.P src q) :=
  decidable_of_iff _ ownedWithin_iff

/-- The holder moves with the value at `src` (A4, A5): `src` or one of its parts, or a place they
own, transitively. Its frame becomes the frame of the destination. -/
def HolderMoves (s : S3) (src : Nat) : Holder → Prop
  | .place p => partOf s.P p src ∨ OwnedWithin s src p
  | .frame _ => False

instance (s : S3) (src : Nat) (h : Holder) : Decidable (HolderMoves s src h) := by
  cases h <;> unfold HolderMoves <;> infer_instance

/-- Anchor `x` moves with the value at `src` (B8): its holder moves with it. -/
def AnchorMoves (s : S3) (src x : Nat) : Prop :=
  OptP (s.A[x]?) (fun y => HolderMoves s src y.holder) False

instance (s : S3) (src x : Nat) : Decidable (AnchorMoves s src x) := by
  unfold AnchorMoves; infer_instance

/-- Anchors of the places whose frame changes when the value at `src` is transferred (A5;
MM-03.3.6): `src`, its parts, and the usable places it owns, transitively. An anchor of a dead
owned place is not read: no usable place depends on it (MM-03.3.6). -/
def movedDeps (s : S3) (src : Nat) : List Nat :=
  ((List.range s.P.length).filter fun q =>
    decide (partOf s.P q src ∨ (OwnedWithin s src q ∧ s.Usable q))).flatMap s.D

/-- Preconditions of `transfer` (MM-03.3 §3, O4), in order: source usable (MM-03.3.1) and
1 initialised; 2 destination usable, without an `Init` leaf, sharing no leaf with the source (F5:
the footprints of source and destination are disjoint, the clause `¬ overlap`, redundant with
clauses 1 and 2 by `transfer_overlap_redundant`),
and still usable once it owns the source's storage (no ownership cycle); exercisable `Modify`
on the source and on the destination (B2); 4 no active derived
access on the source other than those it holds; 5 anchors of the value valid; 6 non-escape
(MM-03.3.6) towards the destination's frame, for the anchors of the value and of the usable
places it owns, whose frame changes with it (A5), each frame read after the transfer (B7);
7 no leaf of the source pinned, statically
(`Pinned`, MM-03.3.8) or dynamically (A8); B8 on the effective anchor (C1): for every dependent
usable after the transfer, if its effective anchor moves with the value, or if the dependent
itself moves (the destination, or a place the value owns), the frame of the effective anchor is
the dependent's frame or an ancestor of it, both frames read after the transfer
(`EffAnchorOK`). O4.3 holds by construction. -/
def TransferPre (k : K) (s : S3) (src dst : Nat) : Prop :=
  s.Usable src ∧ (∀ l ∈ footprint s.P src, s.I l = .init) ∧
  s.Usable dst ∧ (∀ l ∈ footprint s.P dst, s.I l ≠ .init) ∧ ¬ overlap s.P src dst ∧
  HasRight s .modify src ∧ HasRight s .modify dst ∧
  (transferEff s src dst).Usable dst ∧
  (∀ j ∈ List.range s.A.length, ¬ ActiveDerivedOutside s src j) ∧
  (∀ x ∈ depsOf s src, s.Active x) ∧
  (∀ x ∈ movedDeps s src,
    NoEscape (transferEff s src dst) x ((transferEff s src dst).pframe dst)) ∧
  (∀ l ∈ footprint s.P src, ¬ k.Pinned l ∧ s.pin l = false) ∧
  (∀ q ∈ List.range s.P.length, (transferEff s src dst).Usable q →
    ∀ x ∈ (transferEff s src dst).D q,
      (AnchorMoves s src (s.effAnchor x) ∨ q = dst ∨ OwnedWithin s src q) →
      EffAnchorOK (transferEff s src dst) x ((transferEff s src dst).pframe q))

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
1 valid anchor; 5 non-escape (MM-03.3.6); B3: exercisable `Modify` on the result; C1: the frame
of the effective anchor is the frame of the result or an ancestor of it (`EffAnchorOK`). O5.2
(real origin of the rights or storage) is not representable: the state does not relate a value
to the origin of its content. O5.3 and O5.4 hold by construction. -/
def DependPre (s : S3) (q x : Nat) : Prop :=
  s.Usable q ∧ s.Active x ∧ NoEscape s x (s.pframe q) ∧ HasRight s .modify q ∧
    EffAnchorOK s x (s.pframe q)

instance (s : S3) (q x : Nat) : Decidable (DependPre s q x) := by
  unfold DependPre; infer_instance

/-- `depend` as a relation (MM-03.3 §3, O5). -/
def DependStep (q x : Nat) (s : S3) : Outcome3 S3 → Prop :=
  Guarded (DependPre s q x) (dependEff s q x)

/-! ## F4 `store` -/

/-- Effect of `store a p` (F4), the write of a reference into a value: `a` is now held by the
place `p`; `a` joins the anchors of `p`; the leaves of `p` become `Init`. -/
def storeEff (s : S3) (a p : Nat) : S3 := match s.A[a]? with
  | some y => { s with
      A := s.A.set a { y with holder := .place p }
      D := fun q => if q = p then s.D p ++ [a] else s.D q
      I := fun l => if l ∈ footprint s.P p then .init else s.I l }
  | none => s

/-- Preconditions of `store a p` (F4), in order: `a` active, derived (`a.origin ≠ none`), held by
the current frame; `p` usable; exercisable `Modify` on `p` (B2, `HasRight`); `a` covers no leaf
of `p` nor of its owned storage, transitively (A5, `OwnedIn`); `AnchorOrder` for the added
anchor (C1, `EffAnchorOK`): the frame of the effective anchor of `a` is the frame of `p` or one
of its ancestors. No inverse operation exists (F4). -/
def StorePre (s : S3) (a p : Nat) : Prop :=
  OptP (s.A[a]?) (fun y => y.active = true ∧ y.origin ≠ none ∧ y.holder = .frame s.top) False ∧
  s.Usable p ∧ HasRight s .modify p ∧
  (∀ l ∈ s.afp a, l ∉ footprint s.P p ∧
    ∀ q ∈ List.range s.P.length, OwnedIn s.P p q → l ∉ footprint s.P q) ∧
  EffAnchorOK s a (s.pframe p)

instance (s : S3) (a p : Nat) : Decidable (StorePre s a p) := by unfold StorePre; infer_instance

/-- `store` as a relation (F4). -/
def StoreStep (a p : Nat) (s : S3) : Outcome3 S3 → Prop :=
  Guarded (StorePre s a p) (storeEff s a p)

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
arbitrage 2; A4); the ghost record `callParams` of the new frame is `ps` (F6). -/
def enterEff (s : S3) (ps : List Nat) (ls : List (Option Nat × Option Nat × Nat)) : S3 :=
  { F := s.nF :: s.F, nF := s.nF + 1, P := enterP s ls
    I := fun l => if s.P.length ≤ l then .uninit else s.I l
    A := mapI (fun j y => if j ∈ ps then { y with holder := .frame s.nF } else y) 0 s.A ++
      (rootIdx ls).map fun i =>
      ⟨.modify, none, footprint (enterP s ls) (s.P.length + i), localOwner ls s.nF i, true⟩
    D := fun q => if s.P.length ≤ q then [] else s.D q
    dead := fun q => if s.P.length ≤ q then false else s.dead q
    freed := fun q => if s.P.length ≤ q then false else s.freed q
    pin := fun q => if s.P.length ≤ q then false else s.pin q
    arenas := s.arenas
    callParams := fun f => if f = s.nF then ps else s.callParams f }

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

/-- Preconditions of `exitFrame` (MM-03.3 §4, O7; A7; B4): the exiting frame has a caller; every
anchor of a place still usable after the exit has a surviving authority among itself and its
ancestors along `origin`; every surviving derived authority has a surviving strict ancestor;
B4: no leaf of a place that dies with the frame, transitively owned storage included, is
pinned, dynamically (A8) or statically (`Pinned`, MM-03.3.8). Otherwise the exit is rejected. -/
def ExitPre (k : K) (s : S3) : Prop :=
  match s.F with
  | _ :: F₀ => F₀ ≠ [] ∧
      (∀ q ∈ List.range s.P.length, ({ s with F := F₀ } : S3).Usable q →
        ∀ x ∈ s.D q, firstSurv s F₀ (x :: s.ancs x) ≠ none) ∧
      (∀ a ∈ List.range s.A.length, Survives s F₀ a → s.org a ≠ none →
        firstSurv s F₀ (s.ancs a) ≠ none) ∧
      (∀ q ∈ List.range s.P.length, s.Usable q → ¬ ({ s with F := F₀ } : S3).Usable q →
        ∀ l ∈ footprint s.P q, s.pin l = false ∧ ¬ k.Pinned l)
  | [] => False

instance (k : K) [DecidablePred k.Pinned] (s : S3) : Decidable (ExitPre k s) := by
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
def ExitStep (k : K) (s : S3) : Outcome3 S3 → Prop := Guarded (ExitPre k s) (exitEff s)

/-! ## Abstract reads and writes (MM-03.3 §5) -/

/-- Ordinary read condition of a leaf by authority `a` (MM-03.3 §5, `canRead3`): an effective
authority permits observation, the leaf is initialised, the needed dependencies are valid. The
type and storage contract is not represented. -/
def CanReadLeaf (s : S3) (a p : Nat) : Prop :=
  effective s a p ≠ none ∧ s.I p = .init ∧ DepsValid s p

instance (s : S3) (a p : Nat) : Decidable (CanReadLeaf s a p) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- `canRead3` (MM-03.3 §5): ordinary read of leaves `ls` by authority `a`, exercisable at
`Observe` (B2). -/
def canRead3 (s : S3) (a : Nat) (ls : List Nat) : Prop :=
  s.ExercisableAt a .observe ∧ ∀ p ∈ ls, CanReadLeaf s a p

instance (s : S3) (a : Nat) (ls : List Nat) : Decidable (canRead3 s a ls) := by
  unfold canRead3; infer_instance

/-- `read3` as a relation (MM-03.3 §5): a read does not change the state. -/
def Read3Step (a : Nat) (ls : List Nat) (s : S3) : Outcome3 S3 → Prop :=
  Guarded (canRead3 s a ls) s

/-- `canWrite3` (MM-03.3 §5): `a` exercisable at `Modify` (B2); on each leaf, effective
`Modify` of `a` and needed dependencies valid. The clause "no other ordinary authority with an
incompatible effective right" is removed (A11): it follows from the first under I1
(`canWrite3_excl_redundant`). The type and storage condition is not represented. -/
def canWrite3 (s : S3) (a : Nat) (ls : List Nat) : Prop :=
  s.ExercisableAt a .modify ∧ ∀ p ∈ ls, effective s a p = some .modify ∧ DepsValid s p

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

/-- `AnchorOrder` (B8 as corrected by C1): for every usable place and every anchor of it, the
frame of the effective anchor (`S3.effAnchor`, the root of the chain of origins) is the frame of
the place or one of its ancestors (MM-03.3.1, `ancestor`). It holds for every anchor. -/
def AnchorOrder (s : S3) : Prop := ∀ q, s.Usable q → ∀ x ∈ s.D q, EffAnchorOK s x (s.pframe q)

/-- `I1 ∧ I2 ∧ I3 ∧ I4`, the invariant `Inv3` written in MM-03.3 §2, before the clause
`AnchorOrder` that B8 adds to it. -/
def Inv3base (s : S3) : Prop := I1 s ∧ I2 s ∧ I3 s ∧ I4 s

/-- `NoDangling` (C2): no active authority covers a leaf of a place that is not usable in the sense
of `Usable` (existence, `dead` mark, chain of owners). It says nothing of initialisation: a leaf
`Uninit` or `Moved` of a usable place may stay covered. -/
def NoDangling (s : S3) : Prop :=
  ∀ (j : Nat) (y : Authority), s.A[j]? = some y → y.active = true →
    ∀ q, ¬ s.Usable q → ∀ l ∈ footprint s.P q, l ∉ y.footprint

/-- `Inv3` (MM-03.3 §2; B8, C1, C2): the safety invariant,
`I1 ∧ I2 ∧ I3 ∧ I4 ∧ AnchorOrder ∧ NoDangling`. -/
def Inv3 (s : S3) : Prop := Inv3base s ∧ AnchorOrder s ∧ NoDangling s

theorem Inv3.base {s : S3} (h : Inv3 s) : Inv3base s := h.1
theorem Inv3.ao {s : S3} (h : Inv3 s) : AnchorOrder s := h.2.1
theorem Inv3.nd {s : S3} (h : Inv3 s) : NoDangling s := h.2.2

/-- `AnchorOrder` read on the places of `P`: decidable form. -/
theorem anchorOrder_iff {s : S3} : AnchorOrder s ↔
    ∀ q ∈ List.range s.P.length, s.Usable q → ∀ x ∈ s.D q, EffAnchorOK s x (s.pframe q) :=
  ⟨fun h q _ hq => h q hq, fun h q hq => h q (List.mem_range.2 hq.lt) hq⟩

/-- `NoDangling` read on the authorities of `A` and on the places containing each covered leaf:
decidable form. -/
theorem noDangling_iff {s : S3} : NoDangling s ↔
    ∀ j ∈ List.range s.A.length, s.Active j → ∀ l ∈ s.afp j, l < s.P.length → isLeaf s.P l →
      ∀ q ∈ l :: chain (parentOf s.P) l, s.Usable q := by
  constructor
  · intro h j _ ⟨y, hy, ya⟩ l hl hlP hleaf q hq
    have hl' : l ∈ y.footprint := by simpa [S3.afp, hy] using hl
    exact Decidable.byContradiction fun hu => h j y hy ya q hu l
      (mem_footprint.2 ⟨hlP, hleaf, hlP, (List.mem_cons.1 hq).imp Eq.symm id⟩) hl'
  · intro h j y hy ya q hu l hl hly
    obtain ⟨hlP, hleaf, -, hq⟩ := mem_footprint.1 hl
    exact hu (h j (List.mem_range.2 (lt_of_getElem? hy)) ⟨y, hy, ya⟩ l
      (by simp only [S3.afp, hy]; exact hly) hlP hleaf q (List.mem_cons.2 (hq.imp Eq.symm id)))

/-- I4 holds in every state: the read condition requires `Init` (MM-03.3 §2, I4; §5). -/
theorem i4_always (s : S3) : I4 s := fun _ _ hm h => by rw [h.2.1] at hm; cases hm

/-- Root place (MM-03.3.2; B1): an existing place without parent. -/
def RootPlace (P : List Place) (r : Nat) : Prop := r < P.length ∧ parentOf P r = none

instance (P : List Place) (r : Nat) : Decidable (RootPlace P r) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- First clause of B1: two distinct root places have disjoint footprints. Parts and their
containing places are not concerned. -/
def RootsDisjoint (P : List Place) : Prop :=
  ∀ r r', RootPlace P r → RootPlace P r' → r ≠ r' → ∀ l ∈ footprint P r, l ∉ footprint P r'

/-- Second clause of B1: the chain of origins of an authority covering a leaf ends at the root
authority of the root place of that leaf, an authority without origin whose footprint is the
footprint of that root place. -/
def RootChain (s : S3) : Prop :=
  ∀ (a : Nat) (y : Authority) (l : Nat), s.A[a]? = some y → l ∈ y.footprint → isLeaf s.P l →
    ∃ x z r, (x = a ∨ x ∈ s.ancs a) ∧ s.A[x]? = some z ∧ z.origin = none ∧ RootPlace s.P r ∧
      partOf s.P l r ∧ ∀ l', l' ∈ z.footprint ↔ l' ∈ footprint s.P r

/-- A4, "Une racine reste détenue par le propriétaire de son emplacement", a possession condition
that A1 keeps in `WF3`: an authority without origin is held by the owner of the root place of
every leaf it covers. -/
def RootHeld (s : S3) : Prop :=
  ∀ (x : Nat) (z : Authority) (l r : Nat), s.A[x]? = some z → z.origin = none → l ∈ z.footprint →
    RootPlace s.P r → partOf s.P l r → ∃ pr, s.P[r]? = some pr ∧ z.holder = pr.owner

/-- `WF3` (A1, A4, B1, C3): well-formedness, the domain of admissible states, separate from the
safety invariant `Inv3`. Origins precede their derivations; footprints are made of existing
places; the stack is non-empty and without duplicates, below `nF`; owner frames are below `nF`;
owner places exist; a part comes after its parent and has its owner and its `dead` flag; every
active authority has a live holder (possession); B1: the chain of origins of an authority covering
a leaf ends at the root authority of its root place (`RootChain`); A4: a root is held by the owner
of its place (`RootHeld`). C3: the first clause of B1, `RootsDisjoint`, is not a clause: it holds
for every list of places (`rootsDisjoint_always`). -/
def WF3 (s : S3) : Prop :=
  (∀ (b : Nat) (y : Authority) (a : Nat), s.A[b]? = some y → y.origin = some a → a < b) ∧
  (∀ (a : Nat) (x : Authority), s.A[a]? = some x → ∀ l ∈ x.footprint, l < s.P.length) ∧
  s.F ≠ [] ∧ s.F.Nodup ∧ (∀ f ∈ s.F, f < s.nF) ∧
  (∀ (q : Nat) (pl : Place) (f : Nat), s.P[q]? = some pl → pl.owner = .frame f → f < s.nF) ∧
  (∀ (q : Nat) (pl : Place) (o : Nat), s.P[q]? = some pl → pl.owner = .place o →
    o < s.P.length) ∧
  (∀ (q : Nat) (pl : Place) (r : Nat), s.P[q]? = some pl → pl.parent = some r →
    ∃ pr : Place, s.P[r]? = some pr ∧ r < q ∧ pr.owner = pl.owner ∧ s.dead r = s.dead q) ∧
  (∀ (a : Nat) (y : Authority), s.A[a]? = some y → y.active = true → HolderLive s y.holder) ∧
  RootChain s ∧ RootHeld s

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

/-- Central theorem (MM-03.3 §5): in a state satisfying `Inv3base`, an authorised ordinary write
coexists with no other authority with a present effective mode on the written leaves. The proof
uses only the effective `Modify` of the writer. -/
theorem write3_exclusive {s s' : S3} {a : Nat} {ls : List Nat} (hinv : Inv3base s)
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
    releaseEff s a = { s with
      A := s.A.set a { x with active := false }
      D := fun q => if x.holder = .place q then (s.D q).filter (· != a) else s.D q } := by
  simp [releaseEff, hx]

/-- The anchors after a release (F4): those before, without `a` at the place that holds it. -/
theorem release_D_mem {s : S3} {a q y : Nat} {x : Authority} (hx : s.A[a]? = some x)
    (hy : y ∈ (releaseEff s a).D q) : y ∈ s.D q ∧ (y = a → x.holder ≠ .place q) := by
  rw [releaseEff_eq hx] at hy; simp only at hy
  split at hy
  · rename_i hh
    obtain ⟨hy, hne⟩ := List.mem_filter.1 hy
    exact ⟨hy, fun e => by subst e; simp at hne⟩
  · exact ⟨hy, fun _ => ‹_›⟩

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
    HolderLive s y.holder := h.2.2.2.2.2.2.2.2.1
theorem WF3.rootChain : RootChain s := h.2.2.2.2.2.2.2.2.2.1
theorem WF3.rootHeld : RootHeld s := h.2.2.2.2.2.2.2.2.2.2

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

theorem S3.Usable.of_eqs {s s' : S3} {q : Nat} (h : s'.Usable q) (hP : s'.P = s.P)
    (hF : s'.F = s.F) (hd : s'.dead = s.dead) : s.Usable q :=
  S3.Usable.mono hP (fun _ h => hF ▸ h) (fun _ h => hd ▸ h) h

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

/-! ## Clauses of B1 -/

/-- A place has at most one root place (MM-03.3.2). -/
theorem rootOf_unique {P : List Place} {l r r' : Nat} (hr : RootPlace P r) (hr' : RootPlace P r')
    (h : partOf P l r) (h' : partOf P l r') : r = r' := by
  obtain ⟨-, hr⟩ := hr; obtain ⟨-, hr'⟩ := hr'
  obtain ⟨-, h | h⟩ := h <;> obtain ⟨-, h' | h'⟩ := h'
  · exact h.symm.trans h'
  · subst h; rw [chain_none hr] at h'; simp at h'
  · subst h'; rw [chain_none hr'] at h; simp at h
  · exact chainF_root _ _ _ _ h hr h' hr'

/-- The first clause of B1 holds for every list of places: the root places of a leaf coincide, so
two distinct root places share no leaf. -/
theorem rootsDisjoint_always (P : List Place) : RootsDisjoint P :=
  fun _ _ hr hr' hne _ hl hl' => hne (rootOf_unique hr hr' (mem_footprint.1 hl).2.2
    (mem_footprint.1 hl').2.2)

/-- `RootHeld` (A4) carries over to a state with the same places, whose roots are roots of the
former state with the same footprint and holder. -/
theorem RootHeld.transport {s s' : S3} (h : RootHeld s) (hP : s'.P = s.P)
    (hA : ∀ (x : Nat) (z' : Authority), s'.A[x]? = some z' → z'.origin = none →
      ∃ z, s.A[x]? = some z ∧ z.origin = none ∧ z'.footprint = z.footprint ∧
        z'.holder = z.holder) : RootHeld s' := by
  intro x z' l r hx ho hl hr hlr
  obtain ⟨z, hz, hzo, hf, hh⟩ := hA x z' hx ho
  rw [hP] at hr hlr
  obtain ⟨pr, hpr, hpr'⟩ := h x z l r hz hzo (hf ▸ hl) hr hlr
  exact ⟨pr, by rw [hP]; exact hpr, hh.trans hpr'⟩

/-- `RootChain` carries over to a state with the same tree of places, the same chains of origins,
the same footprints, and the same roots. -/
theorem RootChain.transport {s s' : S3} (h : RootChain s) (hlen : s'.P.length = s.P.length)
    (hpar : parentOf s'.P = parentOf s.P) (hanc : ∀ a, s'.ancs a = s.ancs a)
    (hA : ∀ (a : Nat) (y' : Authority), s'.A[a]? = some y' →
      ∃ y, s.A[a]? = some y ∧ y'.footprint = y.footprint)
    (hroot : ∀ (x : Nat) (z : Authority), s.A[x]? = some z → z.origin = none →
      ∃ z', s'.A[x]? = some z' ∧ z'.origin = none ∧ z'.footprint = z.footprint) :
    RootChain s' := by
  intro a y' l ha hl hleaf
  obtain ⟨y, hy, hf⟩ := hA a y' ha
  have hleaf0 : isLeaf s.P l := by simpa only [isLeaf, hlen, hpar] using hleaf
  obtain ⟨x, z, r, hx, hz, hzo, hr, hlr, hfz⟩ := h a y l hy (hf ▸ hl) hleaf0
  obtain ⟨z', hz', hz'o, hz'f⟩ := hroot x z hz hzo
  refine ⟨x, z', r, by rw [hanc]; exact hx, hz', hz'o, ?_, ?_, fun l' => ?_⟩
  · simpa only [RootPlace, hlen, hpar] using hr
  · simpa only [partOf, hlen, hpar] using hlr
  · rw [hz'f, footprint_congr hlen hpar]; exact hfz l'

/-! ## Additions of authorities -/

theorem addAuth_P (s : S3) (y : Authority) : (s.addAuth y).P = s.P := rfl
theorem addAuth_F (s : S3) (y : Authority) : (s.addAuth y).F = s.F := rfl
theorem addAuth_dead (s : S3) (y : Authority) : (s.addAuth y).dead = s.dead := rfl

/-- Adding an authority derived from `src`, within its footprint, preserves `RootChain` (B1). -/
theorem rootChain_addAuth {s : S3} (h : RootChain s) {src : Nat} {x y₀ : Authority}
    (hx : s.A[src]? = some x) (ho : y₀.origin = some src)
    (hfp : ∀ p ∈ y₀.footprint, p ∈ x.footprint) : RootChain (s.addAuth y₀) := by
  have hs := lt_of_getElem? hx
  intro a y l ha hl hleaf
  rcases addAuth_get ha with ⟨ha', ha''⟩ | ⟨rfl, rfl⟩
  · obtain ⟨x0, z, r, hx0, hz, rest⟩ := h a y l ha'' hl hleaf
    have hx0lt : x0 < s.A.length := by
      rcases hx0 with rfl | hx0
      · exact ha'
      · exact Nat.lt_trans (chain_lt hx0) ha'
    exact ⟨x0, z, r, by rw [ancs_addAuth_lt ha']; exact hx0, by rw [addAuth_lt hx0lt]; exact hz,
      rest⟩
  · obtain ⟨x0, z, r, hx0, hz, rest⟩ := h src x l hx (hfp l hl) hleaf
    have hx0lt : x0 < s.A.length := by
      rcases hx0 with rfl | hx0
      · exact hs
      · exact Nat.lt_trans (chain_lt hx0) hs
    refine ⟨x0, z, r, .inr ?_, by rw [addAuth_lt hx0lt]; exact hz, rest⟩
    rw [ancs_addAuth_self ho hs]
    rcases hx0 with rfl | hx0
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ hx0

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
permitted on each leaf, and a live holder, preserves `WF3` and `Inv3base`. Shared by `derive`,
`split` and `issue`. -/
theorem addAuth_preserves {s : S3} (hwf : WF3 s) (hinv : Inv3base s) {src : Nat} {x : Authority}
    {m : Mode} {fp : List Nat} {hd : Holder} (hx : s.A[src]? = some x)
    (hfp : ∀ p ∈ fp, p ∈ x.footprint) (hal : ∀ p ∈ fp, Allows (effective s src p) m)
    (hl : HolderLive s hd) :
    WF3 (s.addAuth ⟨m, some src, fp, hd, true⟩) ∧ Inv3base (s.addAuth ⟨m, some src, fp, hd, true⟩) := by
  obtain ⟨i1, i2, i3, -⟩ := hinv
  have hs := lt_of_getElem? hx
  have live := HolderLive.congr (addAuth_P s ⟨m, some src, fp, hd, true⟩) rfl rfl
  refine ⟨⟨?_, ?_, hwf.ne, hwf.nodup, hwf.frames, hwf.ownerFrame, hwf.ownerPlace, hwf.parts, ?_,
    rootChain_addAuth hwf.rootChain hx rfl hfp,
    hwf.rootHeld.transport rfl fun x z' hx' ho => ?_⟩,
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
  · rcases addAuth_get hx' with ⟨-, hx''⟩ | ⟨-, rfl⟩
    · exact ⟨z', hx'', ho, rfl, rfl⟩
    · cases ho
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

/-- `derive` preserves `WF3` and `Inv3base` (MM-03.3 §3, O1; §10). The proof does not use O1.4. -/
theorem derive_preserves {s s' : S3} {src q : Nat} {m : Mode} (hwf : WF3 s) (hinv : Inv3base s)
    (h : DeriveStep src q m s (.ok s')) : WF3 s' ∧ Inv3base s' := by
  obtain ⟨⟨⟨x, hx, -⟩, -, -, hfp, hal⟩, rfl⟩ := Guarded.ok_iff.1 h
  exact addAuth_preserves hwf hinv hx (fun p hp => by simpa [S3.afp, hx] using hfp p hp) hal
    (top_mem hwf.ne)

/-- `derive_preserves_exclusivity` (MM-03.3 §10): `derive` preserves I1, under I1 alone. -/
theorem derive_preserves_exclusivity {s s' : S3} {src q : Nat} {m : Mode} (h1 : I1 s)
    (h : DeriveStep src q m s (.ok s')) : I1 s' := by
  obtain ⟨⟨⟨x, hx, -⟩, -, -, -, hal⟩, rfl⟩ := Guarded.ok_iff.1 h
  exact addAuth_I1 h1 hx hal

theorem split_aux {src : Nat} {x : Authority} : ∀ (rs : List (List Nat)) (s : S3), WF3 s →
    Inv3base s → s.A[src]? = some x →
    (∀ r ∈ rs, ∀ p ∈ r, effective s src p = some .modify ∧ p ∈ x.footprint) →
    rs.Pairwise (fun r r' => ∀ l ∈ r, l ∉ r') →
    WF3 (splitEff s src rs) ∧ Inv3base (splitEff s src rs)
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

/-- `split` preserves `WF3` and `Inv3base` (MM-03.3 §3, O2; §10), under the obligation `DDSound k`
of `DeclaredDisjoint` (MM-03.3.8). -/
theorem split_preserves_underDD {k : K} (hdd : DDSound k) {s s' : S3} {src : Nat}
    {rs : List (List Nat)} (hwf : WF3 s) (hinv : Inv3base s) (h : SplitStep k src rs s (.ok s')) :
    WF3 s' ∧ Inv3base s' := by
  obtain ⟨⟨⟨x, hx, -⟩, -, h1, h2, h3, -⟩, rfl⟩ := Guarded.ok_iff.1 h
  refine split_aux rs s hwf hinv hx (fun r hr p hp => ⟨h1 r hr p hp, ?_⟩)
    (h3.imp fun {r r'} h => h.elim id fun hd => hdd r r' hd)
  simpa [S3.afp, hx] using (h2 r hr p hp).1


/-- `release` preserves `WF3` and `Inv3base` (MM-03.3 §3, O3; §10). Under the strengthened I1 (A1),
releasing an authority only shrinks the set of active authorities. -/
theorem release_preserves {s s' : S3} {a : Nat} (hwf : WF3 s) (hinv : Inv3base s)
    (h : ReleaseStep a s (.ok s')) : WF3 s' ∧ Inv3base s' := by
  obtain ⟨⟨⟨x, hx, xa⟩, -, h3, -⟩, rfl⟩ := Guarded.ok_iff.1 h
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
    fun b y hb ya => ?_, hwf.rootChain.transport (by rw [hP]) (by rw [hP])
      (fun _ => by rw [release_ancs hx])
      (fun b y' hb => by obtain ⟨y₀, hy₀, -, -, e', -⟩ := back b y' hb; exact ⟨y₀, hy₀, e'⟩)
      (fun x' z hz hzo => by
        by_cases e' : a = x'
        · subst e'; rw [hx] at hz; cases hz
          exact ⟨{ x with active := false }, by rw [get]; simp, hzo, rfl⟩
        · exact ⟨z, by rw [get]; simp [e', hz], hzo, rfl⟩),
      hwf.rootHeld.transport hP fun x' z' hx' ho => by
        obtain ⟨z, hz, -, e1, e2, e3, -⟩ := back x' z' hx'
        exact ⟨z, hz, by rw [← e1]; exact ho, e2, e3⟩⟩,
    fun a' b' x' y' p hab ha' hb' xa' ya' xp yp hnab hnba => ?_,
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
    obtain ⟨hy', hya⟩ := release_D_mem hx hy
    obtain ⟨z, hz, za⟩ := i3 q hq' y hy'
    refine ⟨z, ?_, za⟩
    rw [get]; split
    · subst_vars
      have := h3 q (List.mem_range.2 hq'.lt) hq' hy'
      rw [hx] at this; exact absurd (Option.some.inj this) (hya rfl)
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

theorem SameSkel.rootChain {s s' : S3} (h : SameSkel s s') (hc : RootChain s)
    (hlen : s'.P.length = s.P.length) (hpar : parentOf s'.P = parentOf s.P) : RootChain s' :=
  hc.transport hlen hpar (fun a => by rw [h.ancs])
    (fun a y' ha => by obtain ⟨y, hy, e⟩ := h.get ha; simp [skel] at e; exact ⟨y, hy, e.2.2.1⟩)
    (fun x z hz hzo => by
      obtain ⟨z', hz', e⟩ := h.get' hz; simp [skel] at e; exact ⟨z', hz', e.2.1.trans hzo, e.2.2.1⟩)

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

/-- `transfer` preserves `RootHeld` (A4): the holder of a root and the owner of its root place
change together, under the same condition. -/
theorem transfer_rootHeld {s : S3} {src dst : Nat} (hr : RootHeld s) :
    RootHeld (transferEff s src dst) := by
  intro x z' l r hx ho hl hrp hlr
  rw [transfer_A_get] at hx
  obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.1 hx
  have ho' : z.origin = none := by split at ho <;> exact ho
  have hl' : l ∈ z.footprint := by split at hl <;> exact hl
  have hrp' : RootPlace s.P r := by simpa only [RootPlace, transfer_len, transfer_parentOf] using hrp
  have hlr' : partOf s.P l r := (transfer_partOf s src dst l r).1 hlr
  obtain ⟨pr, hpr, hh⟩ := hr x z l r hz ho' hl' hrp' hlr'
  refine ⟨_, by rw [transfer_P_get, hpr]; rfl, ?_⟩
  by_cases hc : heldIn s.P src pr.owner <;> simp [hc, hh]

/-- `transfer` preserves `WF3` and `Inv3base` (MM-03.3 §3, O4; §10; A4; A5). -/
theorem transfer_preserves {k : K} {s s' : S3} {src dst : Nat} (hwf : WF3 s) (hinv : Inv3base s)
    (h : TransferStep k src dst s (.ok s')) : WF3 s' ∧ Inv3base s' := by
  obtain ⟨⟨hsrc, -, hdst, -, -, -, -, hd', -, h5, -, -, -⟩, rfl⟩ := Guarded.ok_iff.1 h
  have sk := transfer_skel s src dst
  obtain ⟨i1, i2, i3, -⟩ := hinv
  refine ⟨⟨sk.origin hwf.origin, ?_, hwf.ne, hwf.nodup, hwf.frames, ?_, ?_, ?_, ?_,
    sk.rootChain hwf.rootChain (transfer_len s src dst) (transfer_parentOf s src dst),
    transfer_rootHeld hwf.rootHeld⟩,
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

/-- F5: an accepted `transfer` has disjoint footprints of source and destination. The clause is
the explicit precondition `¬ overlap s.P src dst` of `TransferPre`. -/
theorem transfer_footprints_disjoint {k : K} {s s' : S3} {src dst : Nat}
    (h : TransferStep k src dst s (.ok s')) : ∀ l ∈ footprint s.P src, l ∉ footprint s.P dst :=
  fun l hl hl' => (Guarded.ok_iff.1 h).1.2.2.2.2.1 ⟨l, hl, hl'⟩

/-- F5: the clause `¬ overlap s.P src dst` of `TransferPre` is redundant: it follows from clause 1
(source initialised) and clause 2 (destination without an `Init` leaf). It stays explicit (F5:
nothing removed). -/
theorem transfer_overlap_redundant {s : S3} {src dst : Nat}
    (h1 : ∀ l ∈ footprint s.P src, s.I l = .init)
    (h2 : ∀ l ∈ footprint s.P dst, s.I l ≠ .init) : ¬ overlap s.P src dst :=
  fun ⟨l, hl, hl'⟩ => h2 l hl' (h1 l hl)

/-! ## Preservation by `depend`, `read3`, `write3` -/

theorem WF3.of_eq {s s' : S3} (h : WF3 s) (hA : s'.A = s.A) (hP : s'.P = s.P) (hF : s'.F = s.F)
    (hn : s'.nF = s.nF) (hd : s'.dead = s.dead) : WF3 s' := by
  obtain ⟨w0, w2, wne, wnd, wfr, wof, wop, wpa, wpo, wrc, wrh⟩ := h
  refine ⟨hA ▸ w0, by rw [hA, hP]; exact w2, hF ▸ wne, hF ▸ wnd, by rw [hF, hn]; exact wfr,
    by rw [hP, hn]; exact wof, by rw [hP]; exact wop, by rw [hP, hd]; exact wpa, ?_,
    wrc.transport (by rw [hP]) (by rw [hP])
      (fun a => by unfold S3.ancs; congr 1; funext i; simp only [S3.org, hA])
      (fun a y' h => ⟨y', hA ▸ h, rfl⟩)
      (fun x z h hz => ⟨z, hA ▸ h, hz, rfl⟩),
    wrh.transport hP fun x z h' hz => ⟨z, hA ▸ h', hz, rfl, rfl⟩⟩
  intro a y hy ya
  rw [hA] at hy; rw [HolderLive.congr hP hF hd]; exact wpo a y hy ya

/-- `depend` preserves `WF3` and `Inv3base` (MM-03.3 §3, O5; §10). -/
theorem depend_preserves {s s' : S3} {q x : Nat} (hwf : WF3 s) (hinv : Inv3base s)
    (h : DependStep q x s (.ok s')) : WF3 s' ∧ Inv3base s' := by
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

/-- `write3` preserves `WF3` and `Inv3base` (MM-03.3 §5; §10). -/
theorem write3_preserves {s s' : S3} {a : Nat} {ls : List Nat} (hwf : WF3 s) (hinv : Inv3base s)
    (h : Write3Step a ls s (.ok s')) : WF3 s' ∧ Inv3base s' := by
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

/-- `enterFrame` preserves `RootChain` (B1): old authorities keep their chains and the footprints
of old places are unchanged; each new root authority is the root authority of its local. -/
theorem enter_rootChain {s : S3} {ps : List Nat} {ls : List (Option Nat × Option Nat × Nat)}
    (hwf : WF3 s) (hpre : EnterPre s ps ls) : RootChain (enterEff s ps ls) := by
  intro a y l ha hl hleaf
  rcases enter_get ha with ⟨ha', y₀, hy₀, rfl⟩ | ⟨ha', i, hi, rfl⟩
  · have hl0 : l ∈ y₀.footprint := by split at hl <;> exact hl
    have hlt := hwf.fp a y₀ hy₀ l hl0
    have hleaf0 : isLeaf s.P l := fun r hr => by
      have := hleaf r (by show r < (enterP s ls).length; rw [enterP_len]; omega)
      rwa [show parentOf (enterEff s ps ls).P r = parentOf s.P r from enter_parentOf_lt hr] at this
    obtain ⟨x0, z, r, hx0, hz, hzo, ⟨hrl, hrp⟩, ⟨hl', hc⟩, hfz⟩ :=
      hwf.rootChain a y₀ l hy₀ hl0 hleaf0
    have hx0lt : x0 < s.A.length := by
      rcases hx0 with rfl | hx0
      · exact ha'
      · exact Nat.lt_trans (chain_lt hx0) ha'
    refine ⟨x0, _, r, by rw [enter_ancs_lt ha']; exact hx0, by rw [enter_lt hx0lt, hz]; rfl, ?_,
      ⟨?_, ?_⟩, ⟨?_, ?_⟩, fun l' => ?_⟩
    · split <;> exact hzo
    · show r < (enterP s ls).length; rw [enterP_len]; omega
    · show parentOf (enterP s ls) r = none; rw [enter_parentOf_lt hrl]; exact hrp
    · show l < (enterP s ls).length; rw [enterP_len]; omega
    · rcases hc with rfl | hc
      · exact .inl rfl
      · right
        show r ∈ chain (parentOf (enterP s ls)) l
        rwa [chain_congr (fun j hj => enter_parentOf_lt (Nat.lt_of_le_of_lt hj hl'))]
    · show _ ↔ l' ∈ footprint (enterP s ls) r
      rw [enter_footprint_old hpre hrl]
      split <;> exact hfz l'
  · obtain ⟨hil, hin⟩ := rootIdx_mem hi
    refine ⟨a, _, s.P.length + i, .inl rfl, ha, rfl, ⟨?_, ?_⟩, (mem_footprint.1 hl).2.2,
      fun _ => Iff.rfl⟩
    · show s.P.length + i < (enterP s ls).length; rw [enterP_len]; omega
    · show parentOf (enterP s ls) (s.P.length + i) = none; rw [enter_parentOf_new hil]; exact hin

/-- `enterFrame` preserves `RootHeld` (A4): the root of each new local is held by its owner; a
parameter is never a root (A3). -/
theorem enter_rootHeld {s : S3} {ps : List Nat} {ls : List (Option Nat × Option Nat × Nat)}
    (hwf : WF3 s) (hpre : EnterPre s ps ls) (hr : RootHeld s) : RootHeld (enterEff s ps ls) := by
  intro x z l r hx ho hl hrp hlr
  rcases enter_get hx with ⟨-, z₀, hz₀, rfl⟩ | ⟨-, i, hi, rfl⟩
  · have ho' : z₀.origin = none := by split at ho <;> exact ho
    have hl' : l ∈ z₀.footprint := by split at hl <;> exact hl
    have hnp : x ∉ ps := fun hp => by
      have := hpre.2.1 x hp; simp only [OptP, hz₀] at this; exact this.2.2 ho'
    have hlt := hwf.fp x z₀ hz₀ l hl'
    obtain ⟨-, hc⟩ := hlr
    have hch : chain (parentOf (enterP s ls)) l = chain (parentOf s.P) l :=
      chain_congr fun j hj => enter_parentOf_lt (Nat.lt_of_le_of_lt hj hlt)
    have hrl : r < s.P.length := by
      rcases hc with rfl | hc
      · exact hlt
      · have : r ∈ chain (parentOf s.P) l := by rw [← hch]; exact hc
        exact Nat.lt_trans (chain_lt this) hlt
    have hrp' : RootPlace s.P r := ⟨hrl, by rw [← enter_parentOf_lt hrl]; exact hrp.2⟩
    have hlr' : partOf s.P l r := ⟨hlt, by
      rcases hc with rfl | hc
      · exact .inl rfl
      · right; rw [← hch]; exact hc⟩
    obtain ⟨pr, hpr, hh⟩ := hr x z₀ l r hz₀ ho' hl' hrp' hlr'
    exact ⟨pr, by show (enterP s ls)[r]? = _; rw [enterP_lt hrl]; exact hpr, by simp [hnp, hh]⟩
  · obtain ⟨hil, hin⟩ := rootIdx_mem hi
    have hroot : RootPlace (enterEff s ps ls).P (s.P.length + i) :=
      ⟨by show s.P.length + i < (enterP s ls).length; rw [enterP_len]; omega,
        by show parentOf (enterP s ls) (s.P.length + i) = none; rw [enter_parentOf_new hil]; exact hin⟩
    obtain rfl := rootOf_unique hrp hroot hlr (mem_footprint.1 hl).2.2
    exact ⟨_, enterP_new hil, rfl⟩

/-- `enterFrame` preserves `WF3` (MM-03.3 §4, O6; A3; A5; B1). -/
theorem enter_preserves_wf {s : S3} {ps : List Nat} {ls : List (Option Nat × Option Nat × Nat)}
    (hwf : WF3 s) (hpre : EnterPre s ps ls) : WF3 (enterEff s ps ls) := by
  have live : ∀ (hd : Holder), HolderLive s hd → HolderLive (enterEff s ps ls) hd := by
    intro hd hl; cases hd with
    | frame f => exact List.mem_cons_of_mem _ hl
    | place p => exact enter_usable_old hl
  refine ⟨?_, ?_, by simp [enterEff], ?_, ?_, ?_, ?_, ?_, ?_,
    enter_rootChain hwf hpre, enter_rootHeld hwf hpre hwf.rootHeld⟩
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
/-- `enterFrame` preserves `WF3` and `Inv3base` (MM-03.3 §4, O6; §10; A3; A5). -/
theorem enter_preserves {s s' : S3} {ps : List Nat} {ls : List (Option Nat × Option Nat × Nat)}
    (hwf : WF3 s) (hinv : Inv3base s) (h : EnterStep ps ls s (.ok s')) : WF3 s' ∧ Inv3base s' := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  obtain ⟨i1, i2, i3, -⟩ := hinv
  have nodup : (rootIdx ls).Nodup :=
    ((pairwise_lt_range _).sublist List.filter_sublist).imp Nat.ne_of_lt
  refine ⟨enter_preserves_wf hwf hpre, ?_, ?_, ?_, i4_always _⟩
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

/-- Under the order of origins of `WF3`, the walk along origins from `x` (A7) reaches a root:
some authority among `x` and its ancestors has no origin. Without that order, `chain` stops at
the first link that does not decrease. -/
theorem reanchor_reaches_root {s : S3} (hw : ∀ (b : Nat) (y : Authority) (a : Nat),
    s.A[b]? = some y → y.origin = some a → a < b) :
    ∀ n x, x < n → ∃ r, (r = x ∨ r ∈ s.ancs x) ∧ s.org r = none
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, x, hx => by
    cases ho : s.org x with
    | none => exact ⟨x, .inl rfl, ho⟩
    | some o =>
      have hlt := org_lt hw ho
      obtain ⟨r, hr, hro⟩ := reanchor_reaches_root hw n o (by omega)
      refine ⟨r, .inr ?_, hro⟩
      rw [ancs_cons hw ho]
      rcases hr with rfl | hr
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ hr

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

/-- On a chain of origins, an element without origin comes after every other element. -/
theorem ancs_root_after {s : S3} : ∀ n a, a < n → ∀ y w, y ∈ s.ancs a → w ∈ s.ancs a →
    s.org w = none → w = y ∨ w ∈ s.ancs y
  | 0, _, h, _, _, _, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, a, ha, y, w, hy, hw, hwo => by
    cases ho : s.org a with
    | none => rw [S3.ancs, chain_none ho] at hy; simp at hy
    | some o =>
      rcases ancs_step ho with ⟨hlt, he⟩ | he
      · rw [he] at hy hw
        rcases List.mem_cons.1 hy with rfl | hy
        · rcases List.mem_cons.1 hw with rfl | hw
          · exact .inl rfl
          · exact .inr hw
        · rcases List.mem_cons.1 hw with rfl | hw
          · rw [S3.ancs, chain_none hwo] at hy; simp at hy
          · exact ancs_root_after n o (by omega) y w hy hw hwo
      · rw [he] at hy; simp at hy

/-- The root of a chain of origins stays on the chain after the exit (A7), when every surviving
derived authority has a surviving strict ancestor (`ExitPre`). -/
theorem exit_root_kept {s : S3} {f : Nat} {F₀ : Frames} (hF : s.F = f :: F₀)
    (h3 : ∀ a ∈ List.range s.A.length, Survives s F₀ a → s.org a ≠ none →
      firstSurv s F₀ (s.ancs a) ≠ none) :
    ∀ n a, a < n → ∀ x0, x0 ∈ s.ancs a → s.org x0 = none → x0 ∈ (exitEff s).ancs a
  | 0, _, h, _, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, a, ha, x0, hx0, hx0o => by
    cases hy : s.A[a]? with
    | none =>
      have : s.org a = none := by simp [S3.org, hy]
      rw [S3.ancs, chain_none this] at hx0; simp at hx0
    | some y =>
      cases ho : y.origin with
      | none =>
        have : s.org a = none := by simp [S3.org, hy, ho]
        rw [S3.ancs, chain_none this] at hx0; simp at hx0
      | some o =>
        have hob : s.org a = some o := by simp [S3.org, hy, ho]
        obtain ⟨hlt, hax⟩ : o < a ∧ s.ancs a = o :: s.ancs o := by
          rcases ancs_step hob with h | hax
          · exact h
          · rw [hax] at hx0; simp at hx0
        have e' : (exitEff s).org a = (exitG s F₀ a y).origin := by
          simp [S3.org, exit_A_get hF, hy]
        rcases exitG_origin (s := s) (F₀ := F₀) (a := a) (y := y) with e | ⟨hsv, -, e⟩
        · rw [e, ho] at e'
          rw [show (exitEff s).ancs a = o :: (exitEff s).ancs o from chain_cons e' hlt]
          rw [hax] at hx0
          rcases List.mem_cons.1 hx0 with rfl | hx0
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (exit_root_kept hF h3 n o (by omega) x0 hx0 hx0o)
        · rw [e] at e'
          cases hz : firstSurv s F₀ (s.ancs a) with
          | none =>
            exact absurd hz (h3 a (List.mem_range.2 (lt_of_getElem? hy)) hsv (by rw [hob]; simp))
          | some z =>
            rw [hz] at e'
            have hz1 := (firstSurv_some hz).1
            have hzx := chain_lt hz1
            rw [show (exitEff s).ancs a = z :: (exitEff s).ancs z from chain_cons e' hzx]
            rcases ancs_root_after (a + 1) a (Nat.lt_succ_self a) z x0 hz1 hx0 hx0o with rfl | hx'
            · exact List.mem_cons_self ..
            · exact List.mem_cons_of_mem _ (exit_root_kept hF h3 n z (by omega) x0 hx' hx0o)

/-- `exitFrame` preserves `RootChain` (B1; A7): re-attachment keeps the root of each chain. -/
theorem exit_rootChain {s : S3} {f : Nat} {F₀ : Frames} (hc : RootChain s) (hF : s.F = f :: F₀)
    (h3 : ∀ a ∈ List.range s.A.length, Survives s F₀ a → s.org a ≠ none →
      firstSurv s F₀ (s.ancs a) ≠ none) : RootChain (exitEff s) := by
  have hP : (exitEff s).P = s.P := by rw [exitEff_eq hF]
  intro a y l ha hl hleaf
  rw [exit_A_get hF] at ha
  obtain ⟨y₀, hy₀, rfl⟩ := Option.map_eq_some_iff.1 ha
  rw [(exitG_same s F₀ a y₀).2.1] at hl
  rw [hP] at hleaf
  obtain ⟨x0, z, r, hx0, hz, hzo, hr, hlr, hfz⟩ := hc a y₀ l hy₀ hl hleaf
  have hx0o : s.org x0 = none := by simp [S3.org, hz, hzo]
  refine ⟨x0, exitG s F₀ x0 z, r, ?_, by rw [exit_A_get hF, hz]; rfl, ?_, by rw [hP]; exact hr,
    by rw [hP]; exact hlr, fun l' => by rw [(exitG_same s F₀ x0 z).2.1, hP]; exact hfz l'⟩
  · rcases hx0 with rfl | hx0
    · exact .inl rfl
    · exact .inr (exit_root_kept hF h3 (a + 1) a (Nat.lt_succ_self a) x0 hx0 hx0o)
  · rcases exitG_origin (s := s) (F₀ := F₀) (a := x0) (y := z) with e | ⟨-, hn, -⟩
    · rw [e]; exact hzo
    · exact absurd hzo hn

/-- `exitFrame` preserves `RootHeld` (A4): holders and places do not change, and a root after the
exit was a root before, when every surviving derived authority has a surviving strict ancestor
(`ExitPre`). -/
theorem exit_rootHeld {s : S3} {f : Nat} {F₀ : Frames} (hr : RootHeld s) (hF : s.F = f :: F₀)
    (h3 : ∀ a ∈ List.range s.A.length, Survives s F₀ a → s.org a ≠ none →
      firstSurv s F₀ (s.ancs a) ≠ none) : RootHeld (exitEff s) := by
  refine hr.transport (by rw [exitEff_eq hF]) fun x z' hx ho => ?_
  rw [exit_A_get hF] at hx
  obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.1 hx
  refine ⟨z, hz, ?_, (exitG_same s F₀ x z).2.1, (exitG_same s F₀ x z).2.2⟩
  rcases exitG_origin (s := s) (F₀ := F₀) (a := x) (y := z) with e | ⟨hsv, hn, e⟩
  · rw [← e]; exact ho
  · rw [e] at ho
    exact absurd ho (h3 x (List.mem_range.2 (lt_of_getElem? hz)) hsv (by simp [S3.org, hz, hn]))

/-- `exitFrame` preserves `Inv3base` without `WF3` (MM-03.3 §4, O7; A1; A7). -/
theorem exit_preserves_inv3 {k : K} {s s' : S3} (hinv : Inv3base s) (h : ExitStep k s (.ok s')) : Inv3base s' := by
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

/-- `exitFrame` preserves `WF3` and `Inv3base` (MM-03.3 §4, O7; §10; A4; A5; A7). -/
theorem exit_preserves {k : K} {s s' : S3} (hwf : WF3 s) (hinv : Inv3base s) (h : ExitStep k s (.ok s')) :
    WF3 s' ∧ Inv3base s' := by
  have hinv' := exit_preserves_inv3 hinv h
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  unfold ExitPre at hpre
  split at hpre
  · rename_i f F₀ hF
    obtain ⟨hne, -, hR2, -⟩ := hpre
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
      fun a y hy ya => ?_, exit_rootChain hwf.rootChain hF hR2,
      exit_rootHeld hwf.rootHeld hF hR2⟩, hinv'⟩
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
theorem exitFrame_releases_all {k : K} {s s' : S3} {f : Nat} {F₀ : Frames} (hnd : s.F.Nodup)
    (hF : s.F = f :: F₀) (h : ExitStep k s (.ok s')) :
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
theorem exitFrame_kills_locals {k : K} {s s' : S3} {f : Nat} {F₀ : Frames} (hwf : WF3 s) (hinv : Inv3base s)
    (hF : s.F = f :: F₀) (h : ExitStep k s (.ok s')) :
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

/-- Place `q` belongs to frame `f` through ownership (A5): it is owned by `f`, or by a place that
belongs to `f`. -/
inductive OwnedByFrame (P : List Place) (f : Nat) : Nat → Prop where
  | frame {q : Nat} {pl : Place} : P[q]? = some pl → pl.owner = .frame f → OwnedByFrame P f q
  | place {q o : Nat} {pl : Place} : P[q]? = some pl → pl.owner = .place o → OwnedByFrame P f o →
      OwnedByFrame P f q

/-- After the exit, no place that belongs to the exited frame through ownership is usable
(MM-03.3.1; MM-03.3 §4, O7; A5): the locals of the frame and their owned storage, transitively. -/
theorem exitFrame_kills_owned {k : K} {s s' : S3} {f : Nat} {F₀ : Frames} (hwf : WF3 s) (hinv : Inv3base s)
    (hF : s.F = f :: F₀) (h : ExitStep k s (.ok s')) :
    ∀ q, OwnedByFrame s.P f q → ¬ s'.Usable q := by
  have hk := (exitFrame_kills_locals hwf hinv hF h).2.1
  have hP : s'.P = s.P := by obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; rw [exitEff_eq hF]
  intro q hq
  induction hq with
  | @frame q pl hpl ho => exact hk q pl hpl ho
  | @place q o pl hpl ho _ ih =>
    intro hu
    cases hu with
    | frame hpl' _ ho' _ => rw [hP, hpl] at hpl'; cases hpl'; rw [ho] at ho'; cases ho'
    | place hpl' _ ho' hU =>
      rw [hP, hpl] at hpl'; cases hpl'; rw [ho] at ho'; cases ho'; exact ih hU

/-- `exitFrame_reanchors_to_origin` (MM-03.3.7; A7): every anchor of a place usable after the
exit is replaced by the first surviving authority among itself and its ancestors along `origin`,
which is valid after the exit. -/
theorem exitFrame_reanchors_to_origin {k : K} {s s' : S3} {f : Nat} {F₀ : Frames} (hwf : WF3 s)
    (hinv : Inv3base s) (hF : s.F = f :: F₀) (h : ExitStep k s (.ok s')) :
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
theorem dependent_cannot_escape_frame {k : K} {s s' : S3} {f : Nat} {F₀ : Frames} (hwf : WF3 s)
    (hinv : Inv3base s) (hF : s.F = f :: F₀) (h : ExitStep k s (.ok s')) :
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

theorem OnlyReleases.rootChain {s s₁ : S3} (h : OnlyReleases s s₁) (hc : RootChain s)
    (hP : s₁.P = s.P) : RootChain s₁ :=
  hc.transport (by rw [hP]) (by rw [hP]) (fun a => by unfold S3.ancs; rw [h.org])
    (fun a y' ha => by obtain ⟨y, hy, -, -, e, -⟩ := h.2 a y' ha; exact ⟨y, hy, e⟩)
    (fun x z hz hzo => by
      obtain ⟨z', hz'⟩ : ∃ z', s₁.A[x]? = some z' :=
        ⟨_, List.getElem?_eq_some_iff.2 ⟨by rw [h.1]; exact lt_of_getElem? hz, rfl⟩⟩
      obtain ⟨z₀, hz₀, -, e1, e2, -⟩ := h.2 x z' hz'
      rw [hz] at hz₀; cases hz₀
      exact ⟨z', hz', e1.trans hzo, e2⟩)

theorem OnlyReleases.rootHeld {s s₁ : S3} (h : OnlyReleases s s₁) (hr : RootHeld s)
    (hP : s₁.P = s.P) : RootHeld s₁ :=
  hr.transport hP fun x z' hx ho => by
    obtain ⟨z, hz, -, e1, e2, e3, -⟩ := h.2 x z' hx
    exact ⟨z, hz, e1 ▸ ho, e2, e3⟩

/-- `Inv3base` part of `releases_preserve`, without `WF3` (A1): releasing authorities and then those
whose holder died preserves `Inv3base`, provided no usable place keeps an anchor that is
released. -/
theorem releases_preserve_inv3 {s s₁ : S3} (hinv : Inv3base s) (hr : OnlyReleases s s₁)
    (hI3 : ∀ q, s₁.Usable q → ∀ x ∈ s₁.D q, (cleanup s₁).Active x) : Inv3base (cleanup s₁) := by
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
preserves `WF3` and `Inv3base`, provided the dead marks respect parts and no usable place keeps an
anchor that is released. Shared by `endUse` and `free` (A6). -/
theorem releases_preserve {s s₁ : S3} (hwf : WF3 s) (hinv : Inv3base s) (hr : OnlyReleases s s₁)
    (hP : s₁.P = s.P) (hF : s₁.F = s.F) (hn : s₁.nF = s.nF)
    (hparts : ∀ (q : Nat) (pl : Place) (r : Nat), s.P[q]? = some pl → pl.parent = some r →
      s₁.dead r = s₁.dead q)
    (hI3 : ∀ q, s₁.Usable q → ∀ x ∈ s₁.D q, (cleanup s₁).Active x) :
    WF3 (cleanup s₁) ∧ Inv3base (cleanup s₁) := by
  have hc := hr.trans cleanup_releases
  have cP : (cleanup s₁).P = s.P := hP
  have cF : (cleanup s₁).F = s.F := hF
  have live₁ : ∀ hh, HolderLive (cleanup s₁) hh ↔ HolderLive s₁ hh := HolderLive.congr rfl rfl rfl
  refine ⟨⟨fun b y a hb ho => ?_, fun a x hx l hl => ?_, cF ▸ hwf.ne, cF ▸ hwf.nodup,
    by rw [cF, show (cleanup s₁).nF = s.nF from hn]; exact hwf.frames,
    by rw [cP, show (cleanup s₁).nF = s.nF from hn]; exact hwf.ownerFrame,
    by rw [cP]; exact hwf.ownerPlace, fun q pl r hq hp => ?_, fun a y hy ya => ?_,
    hc.rootChain hwf.rootChain cP, hc.rootHeld hwf.rootHeld cP⟩,
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
authority: `a` exercisable at `Observe`, the mode it requests (B2); on each leaf, a present
effective mode of `a`, a
`SharedMutable` leaf (MM-03.3.8), valid dependencies. -/
def WriteSharedPre (k : K) (s : S3) (a : Nat) (ls : List Nat) : Prop :=
  s.ExercisableAt a .observe ∧ ∀ p ∈ ls, effective s a p ≠ none ∧ k.SharedMutable p ∧ DepsValid s p

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

/-- `writeShared` preserves `WF3` and `Inv3base` (A9: it does not weaken I1). -/
theorem writeShared_preserves {k : K} {s s' : S3} {a : Nat} {ls : List Nat} (hwf : WF3 s)
    (hinv : Inv3base s) (h : WriteSharedStep k a ls s (.ok s')) : WF3 s' ∧ Inv3base s' := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
  exact ⟨hwf.of_eq rfl rfl rfl rfl rfl, hinv.1, hinv.2.1, fun q hq x hx =>
    hinv.2.2.1 q ((S3.Usable.congr (s := s) (s' := write3Eff s ls) rfl rfl rfl).1 hq) x hx,
    i4_always _⟩

/-! ## Dynamic pinning (A8) -/

/-- Preconditions of `pin p` (A8): `p` usable, exercisable `Modify` on `p` (B2; `Modify` for
`pin`, B10). -/
def PinPre (s : S3) (p : Nat) : Prop := s.Usable p ∧ HasRight s .modify p

instance (s : S3) (p : Nat) : Decidable (PinPre s p) := by unfold PinPre; infer_instance

/-- Effect of `pin p` / `unpin p` (A8): the leaves of `p` become pinned or unpinned. -/
def pinEff (s : S3) (p : Nat) (b : Bool) : S3 :=
  { s with pin := fun l => if l ∈ footprint s.P p then b else s.pin l }

/-- `pin` as a relation (A8). -/
def PinStep (p : Nat) (s : S3) : Outcome3 S3 → Prop := Guarded (PinPre s p) (pinEff s p true)

/-- Preconditions of `unpin p` (A8): the external use of every leaf of `p` is done
(`ExternalDone`, MM-03.3.8); B3: the right of `pin`, exercisable `Modify` on `p`. -/
def UnpinPre (k : K) (s : S3) (p : Nat) : Prop :=
  (∀ l ∈ footprint s.P p, k.ExternalDone l) ∧ HasRight s .modify p

instance (k : K) [DecidablePred k.ExternalDone] (s : S3) (p : Nat) :
    Decidable (UnpinPre k s p) := by
  unfold UnpinPre; infer_instance

/-- `unpin` as a relation (A8). -/
def UnpinStep (k : K) (p : Nat) (s : S3) : Outcome3 S3 → Prop :=
  Guarded (UnpinPre k s p) (pinEff s p false)

/-- Pinning changes neither authorities nor places: `WF3` and `Inv3base` are preserved (A8). -/
theorem pinEff_preserves {s : S3} {p : Nat} {b : Bool} (hwf : WF3 s) (hinv : Inv3base s) :
    WF3 (pinEff s p b) ∧ Inv3base (pinEff s p b) :=
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

/-- Authority `a` is released by the end of the value at `p` (A4, A6): it is active, and held
within `p` (released by `endUseS`) or by a holder that is not live after `endUseS` (released by
`cleanup`). Under the possession clause of `WF3`, that holder dies with `p`. -/
def EndUseReleased (s : S3) (p a : Nat) : Prop :=
  OptP (s.A[a]?) (fun z => z.active = true ∧
    (heldIn s.P p z.holder ∨ ¬ HolderLive (endUseS s p) z.holder)) False

instance (s : S3) (p a : Nat) : Decidable (EndUseReleased s p a) := by
  unfold EndUseReleased; infer_instance

/-- Authority `j` does not block the end of the value at `p` (A6): if it is an active derived
authority on an ending leaf, or descending from an authority that the end releases
(MM-03.3 §3, O3.2), it is held within `p` or its holder dies. -/
def EndUseAccessOK (s : S3) (p j : Nat) : Prop :=
  OptP (s.A[j]?) (fun y => y.active = true → y.origin ≠ none →
    ((∃ l ∈ y.footprint, EndingLeaf s p l) ∨ ∃ a ∈ s.ancs j, EndUseReleased s p a) →
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
no active derived authority on an ending leaf, or descending from an authority that the end
releases (MM-03.3 §3, O3.2), held elsewhere than in `p` and staying live; no
usable place anchored on an authority held by `p`, on its root, or held by a holder that dies;
C5: no ending leaf pinned, dynamically (A8) or statically (`Pinned`), whatever `ExternalDone`
says: external obligations end only through `unpin`. The ending leaves include those of the
owned places, which die (A6). C8: `p` itself stays usable, its leaves `Uninit`. -/
def EndUsePre (k : K) (s : S3) (p : Nat) : Prop :=
  s.Usable p ∧ HasRight s .modify p ∧
  (∀ j ∈ List.range s.A.length, EndUseAccessOK s p j) ∧
  (∀ q ∈ List.range s.P.length, (endUseS s p).Usable q → ∀ x ∈ (endUseS s p).D q,
    EndUseAnchorOK s p x) ∧
  (∀ l ∈ List.range s.P.length, EndingLeaf s p l → s.pin l = false ∧ ¬ k.Pinned l)

instance (k : K) [DecidablePred k.Pinned] (s : S3) (p : Nat) :
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
theorem endUse_anchors {k : K} {s : S3} {p : Nat} (hinv : Inv3base s) (hpre : EndUsePre k s p) :
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

/-- `endUse` preserves `WF3` and `Inv3base` (A6). -/
theorem endUse_preserves {k : K} {s s' : S3} {p : Nat} (hwf : WF3 s) (hinv : Inv3base s)
    (h : EndUseStep k p s (.ok s')) : WF3 s' ∧ Inv3base s' := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  refine releases_preserve hwf hinv (endUseS_releases s p) rfl rfl rfl ?_ (endUse_anchors hinv hpre)
  intro q pl r hq hp
  obtain ⟨pr, hpr, -, ho, hd⟩ := hwf.parts q pl r hq hp
  simp only [endUseS, hq, hpr, ho, hd]

/-- `endUse` preserves `Inv3base` without `WF3` (A1; A6). -/
theorem endUse_preserves_inv3 {k : K} {s s' : S3} {p : Nat} (hinv : Inv3base s)
    (h : EndUseStep k p s (.ok s')) : Inv3base s' := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  exact releases_preserve_inv3 hinv (endUseS_releases s p) (endUse_anchors hinv hpre)

/-- `endUse_no_dealloc_event` (A6): `endUse` releases no storage and kills no owned place
physically: `freed` is unchanged. -/
theorem endUse_no_dealloc_event {k : K} {s s' : S3} {p : Nat} (h : EndUseStep k p s (.ok s')) :
    s'.freed = s.freed := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; rfl

/-- `endUse_preserves_dependents` (A6): no usable dependent loses an anchor; a usable place other
than a part of `p` keeps its anchors, all valid. -/
theorem endUse_preserves_dependents {k : K} {s s' : S3} {p : Nat} (hwf : WF3 s) (hinv : Inv3base s)
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

/-- Authority `a` is released by the release of `p` (A4, A6): it is active, and covers a leaf of
`p` or is held within `p` (released by `freeS`), or its holder is not live after `freeS`
(released by `cleanup`). Under the possession clause of `WF3`, that holder dies with `p`. -/
def FreeDeact (s : S3) (p a : Nat) : Prop :=
  OptP (s.A[a]?) (fun z => z.active = true ∧ ((∃ l ∈ z.footprint, l ∈ footprint s.P p) ∨
    heldIn s.P p z.holder ∨ ¬ HolderLive (freeS s p) z.holder)) False

instance (s : S3) (p a : Nat) : Decidable (FreeDeact s p a) := by
  unfold FreeDeact; infer_instance

/-- Authority `j` does not block the release of `p` (A6): if it is an active derived authority on
a freed leaf, or descending from an authority that the release releases (MM-03.3 §3, O3.2), it
is held within `p` or its holder dies. -/
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
parent); exercisable `Modify` on `p` (B2); no active derived authority on a freed leaf, or
descending from a deactivated authority, held elsewhere and staying live; no usable place
anchored on an authority covering `p`, held within `p`, or whose holder dies; no freed leaf
pinned, statically (`Pinned`) or dynamically, without exception (B6: external obligations end
only through `unpin` under `ExternalDone`). -/
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
theorem free_anchors {k : K} {s : S3} {p auth : Nat} (hinv : Inv3base s) (hpre : FreePre k s p auth) :
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

/-- `free` preserves `WF3` and `Inv3base` (A6). -/
theorem free_preserves {k : K} {s s' : S3} {p auth : Nat} (hwf : WF3 s) (hinv : Inv3base s)
    (h : FreeStep k p auth s (.ok s')) : WF3 s' ∧ Inv3base s' := by
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

/-- `free` preserves `Inv3base` without `WF3` (A1; A6). -/
theorem free_preserves_inv3 {k : K} {s s' : S3} {p auth : Nat} (hinv : Inv3base s)
    (h : FreeStep k p auth s (.ok s')) : Inv3base s' := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  exact releases_preserve_inv3 hinv (freeS_releases s p) (free_anchors hinv hpre)

/-- `free_no_dangling` (A6): after `free p`, no active authority covers a leaf of `p`, and every
active authority has a live holder: no usable access reaches the released storage. -/
theorem free_no_dangling {k : K} {s s' : S3} {p auth : Nat} (hwf : WF3 s) (hinv : Inv3base s)
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

theorem FreedLeaf.lt {s : S3} {p l : Nat} (h : FreedLeaf s p l) : l < s.P.length := by
  rcases h with h | ⟨h, -⟩
  · exact (mem_footprint.1 h).1
  · exact h.lt

/-- `free_no_pin` (B6): after `free p`, no freed leaf is pinned, dynamically or statically; no pin
state survives a release. -/
theorem free_no_pin {k : K} {s s' : S3} {p auth : Nat} (h : FreeStep k p auth s (.ok s')) :
    ∀ l, FreedLeaf s p l → s'.pin l = false ∧ ¬ k.Pinned l := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  intro l hl
  exact hpre.2.2.2.2.2.2.2 l (List.mem_range.2 hl.lt) hl

/-! ## `alloc` (B5, C6, C9) -/

/-- Outcomes of `alloc` (B5): `ok`; `fail`, a defined failure of the allocator contract, with the
state unchanged; `reject` by the static discipline (MM-03.3 §3). -/
inductive AOutcome where
  | ok (s : S3)
  | fail (s : S3)
  | reject

/-- Right to update the metadata of the allocator value at `provider` (B5): exercisable `Modify` on
`provider`, or a `writeShared` right (A9) on its leaves, all `SharedMutable`. -/
def ProviderRight (k : K) (s : S3) (provider : Nat) : Prop :=
  HasRight s .modify provider ∨
  ∃ via ∈ List.range s.A.length, s.ExercisableAt via .observe ∧
    ∀ l ∈ footprint s.P provider, effective s via l ≠ none ∧ k.SharedMutable l ∧ DepsValid s l

instance (k : K) [DecidablePred k.SharedMutable] (s : S3) (provider : Nat) :
    Decidable (ProviderRight k s provider) := by
  unfold ProviderRight; infer_instance

/-- Owner of the element of index `i` of a shape `ls` (A5; C6): its owning element if any, `hd`
otherwise. The owner of a local of `enterFrame` is the case `hd = .frame f` (`localOwner`). -/
def shapeOwner (ls : List (Option Nat × Option Nat × Nat)) (hd : Holder) (i : Nat) : Holder :=
  match (ls[i]?).bind (·.2.1) with
  | some o => .place o
  | none => hd

/-- Places `P` followed by the elements of the shape `ls` (C6: the encoding of the locals of
`enterFrame`, an indexed forest of (parent, owning element, kind)); the elements without owning
element are owned by `hd` (A5). -/
def shapeP (P : List Place) (hd : Holder) (ls : List (Option Nat × Option Nat × Nat)) :
    List Place :=
  P ++ (List.range ls.length).map fun i =>
    ⟨(ls[i]?).bind (·.1), shapeOwner ls hd i, ((ls[i]?).map (·.2.2)).getD 0⟩

/-- `enterFrame` lays out its locals as a shape (C6). -/
theorem enterP_eq_shapeP (s : S3) (ls : List (Option Nat × Option Nat × Nat)) :
    enterP s ls = shapeP s.P (.frame s.nF) ls := rfl

/-- Well-formed shape at offset `n` (MM-03.3 §4, O6; C6): the parent and the owning element of an
element are earlier elements, and a part has the owning element of its parent. It is the clause
of `EnterPre` on the locals (`enterPre_shapeOK`). -/
def ShapeOK (n : Nat) (ls : List (Option Nat × Option Nat × Nat)) : Prop :=
  ∀ i ∈ List.range ls.length,
    OptP ((ls[i]?).bind (·.1)) (fun r => n ≤ r ∧ r < n + i ∧
      (ls[i]?).bind (·.2.1) = (ls[r - n]?).bind (·.2.1)) True ∧
    OptP ((ls[i]?).bind (·.2.1)) (fun o => n ≤ o ∧ o < n + i) True

instance (n : Nat) (ls : List (Option Nat × Option Nat × Nat)) : Decidable (ShapeOK n ls) := by
  unfold ShapeOK; infer_instance

theorem enterPre_shapeOK {s : S3} {ps : List Nat} {ls : List (Option Nat × Option Nat × Nat)}
    (h : EnterPre s ps ls) : ShapeOK s.P.length ls := h.2.2

/-- Static preconditions of `alloc provider owner shape` (B5; C6; D2): the allocator value at
`provider` is usable, with the right to update its metadata; the place `owner`, which receives
the ownership, is usable, with exercisable `Modify`; the leaves of the provider are `Init`; the
shape is well-formed and not empty (D2: an allocation of size zero is a shape of one leaf). -/
def AllocStatic (k : K) (s : S3) (provider owner : Nat)
    (ls : List (Option Nat × Option Nat × Nat)) : Prop :=
  s.Usable provider ∧ ProviderRight k s provider ∧ s.Usable owner ∧ HasRight s .modify owner ∧
    (∀ l ∈ footprint s.P provider, s.I l = .init) ∧ ShapeOK s.P.length ls ∧ ls ≠ []

instance (k : K) [DecidablePred k.SharedMutable] (s : S3) (provider owner : Nat)
    (ls : List (Option Nat × Option Nat × Nat)) : Decidable (AllocStatic k s provider owner ls) := by
  unfold AllocStatic; infer_instance

/-- Places after `alloc` (B5; C6): the elements of the shape appended, those without owning
element owned by `owner`. -/
def allocP (s : S3) (owner : Nat) (ls : List (Option Nat × Option Nat × Nat)) : List Place :=
  shapeP s.P (.place owner) ls

/-- Effect of `alloc provider owner shape` (B5; C6): the elements of the shape appended as places
of fresh identities, `Uninit`, without anchor, alive, not freed, not pinned; one root authority
`Modify` per root element, on its footprint, held by the owner of the element (A4); the metadata
of the provider, its leaves, set to `Init`. The shape is abstract: it fixes neither alignment nor
layout (milestone 2). -/
def allocEff (s : S3) (provider owner : Nat) (ls : List (Option Nat × Option Nat × Nat)) : S3 :=
  { s with
    P := allocP s owner ls
    I := fun l => if s.P.length ≤ l then .uninit
      else if l ∈ footprint s.P provider then .init else s.I l
    A := s.A ++ (rootIdx ls).map fun i =>
      ⟨.modify, none, footprint (allocP s owner ls) (s.P.length + i),
        shapeOwner ls (.place owner) i, true⟩
    D := fun q => if s.P.length ≤ q then [] else s.D q
    dead := fun q => if s.P.length ≤ q then false else s.dead q
    freed := fun q => if s.P.length ≤ q then false else s.freed q
    pin := fun q => if s.P.length ≤ q then false else s.pin q }

/-- `alloc provider owner shape` as a relation (B5; C6; C9): `reject` when a static precondition
fails; `fail`, with the state unchanged, when the allocator contract cannot satisfy the request in
the current state (`Satisfiable`); `ok` otherwise. -/
inductive AllocStep (k : K) (provider owner : Nat) (ls : List (Option Nat × Option Nat × Nat))
    (s : S3) : AOutcome → Prop where
  | ok : AllocStatic k s provider owner ls → k.Satisfiable provider ls s →
      AllocStep k provider owner ls s (.ok (allocEff s provider owner ls))
  | fail : AllocStatic k s provider owner ls → ¬ k.Satisfiable provider ls s →
      AllocStep k provider owner ls s (.fail s)
  | reject : ¬ AllocStatic k s provider owner ls → AllocStep k provider owner ls s .reject

/-- Determinism of `alloc` (B5). -/
theorem alloc_det {k : K} {pr ow : Nat} {ls : List (Option Nat × Option Nat × Nat)} {s : S3}
    {o₁ o₂ : AOutcome} (h₁ : AllocStep k pr ow ls s o₁) (h₂ : AllocStep k pr ow ls s o₂) :
    o₁ = o₂ := by
  cases h₁ <;> cases h₂ <;> first | rfl | contradiction

/-- `alloc_fail_unchanged` (B5; C9): a failed allocation leaves the state unchanged, and happens
exactly when the static preconditions hold and the allocator contract cannot satisfy the request
in the current state. -/
theorem alloc_fail_unchanged {k : K} {pr ow : Nat} {ls : List (Option Nat × Option Nat × Nat)}
    {s s' : S3} (h : AllocStep k pr ow ls s (.fail s')) :
    s' = s ∧ AllocStatic k s pr ow ls ∧ ¬ k.Satisfiable pr ls s := by
  cases h with
  | fail h1 h2 => exact ⟨rfl, h1, h2⟩

section Shape
variable {P : List Place} {hd : Holder} {ls : List (Option Nat × Option Nat × Nat)}

theorem shapeP_len (P : List Place) (hd : Holder) (ls : List (Option Nat × Option Nat × Nat)) :
    (shapeP P hd ls).length = P.length + ls.length := by simp [shapeP]

theorem shapeP_lt {q : Nat} (h : q < P.length) : (shapeP P hd ls)[q]? = P[q]? :=
  List.getElem?_append_left h

theorem shapeP_new {i : Nat} (h : i < ls.length) : (shapeP P hd ls)[P.length + i]? =
    some ⟨(ls[i]?).bind (·.1), shapeOwner ls hd i, ((ls[i]?).map (·.2.2)).getD 0⟩ := by
  simp only [shapeP, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    List.getElem?_map, List.getElem?_range h, Option.map_some]

theorem shapeP_get {q : Nat} {pl : Place} (h : (shapeP P hd ls)[q]? = some pl) :
    (q < P.length ∧ P[q]? = some pl) ∨ (P.length ≤ q ∧ ∃ i, i < ls.length ∧
      q = P.length + i ∧ pl = ⟨(ls[i]?).bind (·.1), shapeOwner ls hd i,
        ((ls[i]?).map (·.2.2)).getD 0⟩) := by
  by_cases hq : q < P.length
  · exact .inl ⟨hq, by rwa [shapeP_lt hq] at h⟩
  · have hi : q - P.length < ls.length := by
      have := lt_of_getElem? h; rw [shapeP_len] at this; omega
    have e : q = P.length + (q - P.length) := by omega
    rw [e, shapeP_new hi] at h; cases h
    exact .inr ⟨by omega, _, hi, e, rfl⟩

theorem shape_parentOf_new {i : Nat} (h : i < ls.length) :
    parentOf (shapeP P hd ls) (P.length + i) = (ls[i]?).bind (·.1) := by
  simp [parentOf, shapeP_new h]

theorem shape_parentOf_lt {q : Nat} (h : q < P.length) :
    parentOf (shapeP P hd ls) q = parentOf P q := by
  simp [parentOf, shapeP_lt h]

theorem shape_root_fp_ge {i l : Nat} (h : l ∈ footprint (shapeP P hd ls) (P.length + i)) :
    P.length ≤ l := by
  obtain ⟨-, -, -, h | h⟩ := mem_footprint.1 h
  · omega
  · have := chain_lt h; omega

theorem shape_roots_disjoint {i i' l : Nat} (hii : i ≠ i') (hn : (ls[i]?).bind (·.1) = none)
    (hn' : (ls[i']?).bind (·.1) = none) (h : l ∈ footprint (shapeP P hd ls) (P.length + i))
    (h' : l ∈ footprint (shapeP P hd ls) (P.length + i')) : False := by
  have hlt : ∀ {j}, l ∈ footprint (shapeP P hd ls) (P.length + j) → j < ls.length := fun hj => by
    obtain ⟨hl, -, -, hq⟩ := mem_footprint.1 hj
    rw [shapeP_len] at hl
    rcases hq with hq | hq
    · omega
    · have := chain_lt hq; omega
  have hi := hlt h; have hi' := hlt h'
  have r := shape_parentOf_new (P := P) (hd := hd) hi; rw [hn] at r
  have r' := shape_parentOf_new (P := P) (hd := hd) hi'; rw [hn'] at r'
  obtain ⟨-, -, -, h | h⟩ := mem_footprint.1 h <;> obtain ⟨-, -, -, h' | h'⟩ := mem_footprint.1 h'
  · omega
  · subst h; rw [chain_none r] at h'; simp at h'
  · subst h'; rw [chain_none r'] at h; simp at h
  · exact hii (by have := chainF_root _ _ _ _ h r h' r'; omega)

theorem shape_chain_ge (hsh : ShapeOK P.length ls) : ∀ n q, q < n → P.length ≤ q →
    ∀ x ∈ chain (parentOf (shapeP P hd ls)) q, P.length ≤ x
  | 0, _, h, _, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, q, hq, hge, x, hx => by
    have hi : q - P.length < ls.length := by
      cases hpo : parentOf (shapeP P hd ls) q with
      | none => rw [chain_none hpo] at hx; simp at hx
      | some r =>
        simp only [parentOf] at hpo
        cases h' : (shapeP P hd ls)[q]? with
        | none => rw [h'] at hpo; cases hpo
        | some _ => have := lt_of_getElem? h'; rw [shapeP_len] at this; omega
    have hpo := shape_parentOf_new (P := P) (hd := hd) hi
    rw [show P.length + (q - P.length) = q by omega] at hpo
    cases hb : (ls[q - P.length]?).bind (·.1) with
    | none => rw [hb] at hpo; rw [chain_none hpo] at hx; simp at hx
    | some r =>
      rw [hb] at hpo
      have h1 := (hsh (q - P.length) (List.mem_range.2 hi)).1
      rw [hb] at h1; simp only [OptP] at h1
      rw [chain_cons hpo (by omega)] at hx
      rcases List.mem_cons.1 hx with rfl | hx
      · omega
      · exact shape_chain_ge hsh n r (by omega) (by omega) x hx

/-- The footprint of an existing place does not change when a shape is appended: new elements
have new parents (MM-03.3.2; C6). -/
theorem shape_footprint_old (hsh : ShapeOK P.length ls) {q : Nat} (hq : q < P.length) :
    ∀ l, l ∈ footprint (shapeP P hd ls) q ↔ l ∈ footprint P q := by
  have hpar : ∀ j < P.length, parentOf (shapeP P hd ls) j = parentOf P j :=
    fun j hj => shape_parentOf_lt hj
  have hch : ∀ l < P.length, chain (parentOf (shapeP P hd ls)) l = chain (parentOf P) l :=
    fun l hl => chain_congr fun j hj => hpar j (by omega)
  intro l
  simp only [mem_footprint, isLeaf, partOf, shapeP_len]
  constructor
  · rintro ⟨hl, hleaf, -, hpo⟩
    have hln : l < P.length := by
      rcases Nat.lt_or_ge l P.length with h | h
      · exact h
      · rcases hpo with rfl | hpo
        · omega
        · have := shape_chain_ge (hd := hd) hsh (l + 1) l (Nat.lt_succ_self l) h q hpo; omega
    refine ⟨hln, fun r hr => by rw [← hpar r hr]; exact hleaf r (by omega), hln, ?_⟩
    rwa [hch l hln] at hpo
  · rintro ⟨hl, hleaf, -, hpo⟩
    refine ⟨by omega, fun r hr => ?_, by omega, by rwa [hch l hl]⟩
    by_cases hrn : r < P.length
    · rw [hpar r hrn]; exact hleaf r hrn
    · intro he
      have hi : r - P.length < ls.length := by omega
      have hpo' := shape_parentOf_new (P := P) (hd := hd) hi
      rw [show P.length + (r - P.length) = r by omega, he] at hpo'
      have h1 := (hsh (r - P.length) (List.mem_range.2 hi)).1
      rw [← hpo'] at h1; simp only [OptP] at h1; omega

end Shape

section AllocLemmas
variable {s : S3} {pr o : Nat} {ls : List (Option Nat × Option Nat × Nat)}

theorem allocP_len (s : S3) (o : Nat) (ls : List (Option Nat × Option Nat × Nat)) :
    (allocP s o ls).length = s.P.length + ls.length := shapeP_len _ _ _

theorem allocP_lt {q : Nat} (h : q < s.P.length) : (allocP s o ls)[q]? = s.P[q]? := shapeP_lt h

theorem alloc_get {j : Nat} {z : Authority} (h : (allocEff s pr o ls).A[j]? = some z) :
    (j < s.A.length ∧ s.A[j]? = some z) ∨
    (s.A.length ≤ j ∧ ∃ i, (rootIdx ls)[j - s.A.length]? = some i ∧
      z = ⟨.modify, none, footprint (allocP s o ls) (s.P.length + i),
        shapeOwner ls (.place o) i, true⟩) := by
  simp only [allocEff] at h
  by_cases hj : j < s.A.length
  · rw [List.getElem?_append_left hj] at h; exact .inl ⟨hj, h⟩
  · rw [List.getElem?_append_right (by omega), List.getElem?_map] at h
    cases hi : (rootIdx ls)[j - s.A.length]? with
    | none => rw [hi] at h; cases h
    | some i => rw [hi] at h; cases h; exact .inr ⟨by omega, i, rfl, rfl⟩

theorem alloc_lt {j : Nat} (h : j < s.A.length) : (allocEff s pr o ls).A[j]? = s.A[j]? :=
  List.getElem?_append_left h

theorem alloc_ancs_lt {j : Nat} (h : j < s.A.length) : (allocEff s pr o ls).ancs j = s.ancs j :=
  chain_congr fun _ hi => by simp only [S3.org, alloc_lt (Nat.lt_of_le_of_lt hi h)]

theorem alloc_usable_old {q : Nat} (h : s.Usable q) : (allocEff s pr o ls).Usable q := by
  induction h with
  | @frame q f pl hpl hd ho hf =>
    exact .frame (show (allocP s o ls)[q]? = _ by rw [allocP_lt (lt_of_getElem? hpl)]; exact hpl)
      (by simp [allocEff, hd, show ¬ s.P.length ≤ q from Nat.not_le.2 (lt_of_getElem? hpl)])
      ho hf
  | @place q o' pl hpl hd ho _ ih =>
    exact .place (show (allocP s o ls)[q]? = _ by rw [allocP_lt (lt_of_getElem? hpl)]; exact hpl)
      (by simp [allocEff, hd, show ¬ s.P.length ≤ q from Nat.not_le.2 (lt_of_getElem? hpl)])
      ho ih

theorem alloc_usable_back (hwf : WF3 s) {q : Nat} (h : (allocEff s pr o ls).Usable q)
    (hq : q < s.P.length) : s.Usable q := by
  induction h with
  | @frame q f pl hpl hd ho hf =>
    have hpl' : s.P[q]? = some pl := by
      have : (allocP s o ls)[q]? = some pl := hpl; rwa [allocP_lt hq] at this
    exact .frame hpl' (by simpa [allocEff, show ¬ s.P.length ≤ q by omega] using hd) ho hf
  | @place q o' pl hpl hd ho _ ih =>
    have hpl' : s.P[q]? = some pl := by
      have : (allocP s o ls)[q]? = some pl := hpl; rwa [allocP_lt hq] at this
    exact .place hpl' (by simpa [allocEff, show ¬ s.P.length ≤ q by omega] using hd) ho
      (ih (hwf.ownerPlace q pl o' hpl' ho))

/-- New elements are usable after `alloc` (A5; C6): their owners lead to `owner`. -/
theorem alloc_usable_new {k : K} (hst : AllocStatic k s pr o ls) : ∀ n i, i < n → i < ls.length →
    (allocEff s pr o ls).Usable (s.P.length + i)
  | 0, _, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, i, _, hi => by
    have hpl := shapeP_new (P := s.P) (hd := .place o) hi
    have hd : (allocEff s pr o ls).dead (s.P.length + i) = false := by simp [allocEff]
    unfold shapeOwner at hpl
    cases ho : (ls[i]?).bind (·.2.1) with
    | none =>
      rw [ho] at hpl
      exact .place (show (allocP s o ls)[_]? = _ from hpl) hd rfl (alloc_usable_old hst.2.2.1)
    | some o' =>
      rw [ho] at hpl
      have h2 := (hst.2.2.2.2.2.1 i (List.mem_range.2 hi)).2
      rw [ho] at h2; obtain ⟨h₁, h₂⟩ := h2
      have := alloc_usable_new hst n (o' - s.P.length) (by omega) (by omega)
      rw [show s.P.length + (o' - s.P.length) = o' by omega] at this
      exact .place (show (allocP s o ls)[_]? = _ from hpl) hd rfl this

theorem alloc_shapeOwner_live {k : K} (hst : AllocStatic k s pr o ls) {i : Nat}
    (hi : i < ls.length) : HolderLive (allocEff s pr o ls) (shapeOwner ls (.place o) i) := by
  unfold shapeOwner
  cases ho : (ls[i]?).bind (·.2.1) with
  | none => exact alloc_usable_old hst.2.2.1
  | some o' =>
    have h2 := (hst.2.2.2.2.2.1 i (List.mem_range.2 hi)).2
    rw [ho] at h2; simp only [OptP] at h2
    have := alloc_usable_new hst (o' - s.P.length + 1) (o' - s.P.length) (Nat.lt_succ_self _)
      (by omega)
    rwa [show s.P.length + (o' - s.P.length) = o' by omega] at this

end AllocLemmas

/-- `alloc` preserves `RootChain` (B1; C6): old authorities keep their chains and the footprints of
old places are unchanged; each new root authority is the root authority of its element. -/
theorem alloc_rootChain {k : K} {s : S3} {pr o : Nat} {ls : List (Option Nat × Option Nat × Nat)}
    (hwf : WF3 s) (hst : AllocStatic k s pr o ls) : RootChain (allocEff s pr o ls) := by
  have hsh := hst.2.2.2.2.2.1
  intro a y l ha hl hleaf
  rcases alloc_get ha with ⟨ha', hy⟩ | ⟨-, i, hi, rfl⟩
  · have hlt := hwf.fp a y hy l hl
    have hleaf0 : isLeaf s.P l := fun r hr => by
      have := hleaf r (by show r < (allocP s o ls).length; rw [allocP_len]; omega)
      rwa [show parentOf (allocEff s pr o ls).P r = parentOf s.P r from shape_parentOf_lt hr]
        at this
    obtain ⟨x0, z, r, hx0, hz, hzo, ⟨hrl, hrp⟩, ⟨hl', hc⟩, hfz⟩ :=
      hwf.rootChain a y l hy hl hleaf0
    have hx0lt : x0 < s.A.length := by
      rcases hx0 with rfl | hx0
      · exact ha'
      · exact Nat.lt_trans (chain_lt hx0) ha'
    refine ⟨x0, z, r, by rw [alloc_ancs_lt ha']; exact hx0, by rw [alloc_lt hx0lt]; exact hz, hzo,
      ⟨?_, ?_⟩, ⟨?_, ?_⟩, fun l' => ?_⟩
    · show r < (allocP s o ls).length; rw [allocP_len]; omega
    · show parentOf (allocP s o ls) r = none; rw [allocP, shape_parentOf_lt hrl]; exact hrp
    · show l < (allocP s o ls).length; rw [allocP_len]; omega
    · rcases hc with rfl | hc
      · exact .inl rfl
      · right
        show r ∈ chain (parentOf (shapeP s.P (.place o) ls)) l
        rwa [chain_congr (fun j hj => shape_parentOf_lt (Nat.lt_of_le_of_lt hj hl'))]
    · show _ ↔ l' ∈ footprint (shapeP s.P (.place o) ls) r
      rw [shape_footprint_old hsh hrl]; exact hfz l'
  · obtain ⟨hil, hin⟩ := rootIdx_mem hi
    refine ⟨a, _, s.P.length + i, .inl rfl, ha, rfl, ⟨?_, ?_⟩, (mem_footprint.1 hl).2.2,
      fun _ => Iff.rfl⟩
    · show s.P.length + i < (allocP s o ls).length; rw [allocP_len]; omega
    · show parentOf (allocP s o ls) (s.P.length + i) = none
      rw [allocP, shape_parentOf_new hil]; exact hin

/-- `alloc` preserves `RootHeld` (A4; B5; C6): the root of each new element is held by the owner of
the element. -/
theorem alloc_rootHeld {s : S3} {pr o : Nat} {ls : List (Option Nat × Option Nat × Nat)}
    (hwf : WF3 s) (hr : RootHeld s) : RootHeld (allocEff s pr o ls) := by
  intro x z l r hx ho hl hrp hlr
  rcases alloc_get hx with ⟨-, hx'⟩ | ⟨-, i, hi, rfl⟩
  · have hlt := hwf.fp x z hx' l hl
    obtain ⟨-, hc⟩ := hlr
    have hch : chain (parentOf (allocP s o ls)) l = chain (parentOf s.P) l :=
      chain_congr fun j hj => shape_parentOf_lt (Nat.lt_of_le_of_lt hj hlt)
    have hrl : r < s.P.length := by
      rcases hc with rfl | hc
      · exact hlt
      · have : r ∈ chain (parentOf s.P) l := by rw [← hch]; exact hc
        exact Nat.lt_trans (chain_lt this) hlt
    have hrp' : RootPlace s.P r := ⟨hrl, by rw [← shape_parentOf_lt hrl]; exact hrp.2⟩
    have hlr' : partOf s.P l r := ⟨hlt, by
      rcases hc with rfl | hc
      · exact .inl rfl
      · right; rw [← hch]; exact hc⟩
    obtain ⟨pr', hpr, hh⟩ := hr x z l r hx' ho hl hrp' hlr'
    exact ⟨pr', by show (allocP s o ls)[r]? = _; rw [allocP_lt hrl]; exact hpr, hh⟩
  · obtain ⟨hil, hin⟩ := rootIdx_mem hi
    have hroot : RootPlace (allocEff s pr o ls).P (s.P.length + i) :=
      ⟨by show s.P.length + i < (allocP s o ls).length; rw [allocP_len]; omega,
        by show parentOf (allocP s o ls) (s.P.length + i) = none
           rw [allocP, shape_parentOf_new hil]; exact hin⟩
    obtain rfl := rootOf_unique hrp hroot hlr (mem_footprint.1 hl).2.2
    exact ⟨_, shapeP_new hil, rfl⟩

/-- `alloc` preserves `WF3` and `Inv3base` (B5; C6; MM-03.3 §2). -/
theorem alloc_preserves {k : K} {pr ow : Nat} {ls : List (Option Nat × Option Nat × Nat)}
    {s s' : S3} (hwf : WF3 s) (hinv : Inv3base s) (h : AllocStep k pr ow ls s (.ok s')) :
    WF3 s' ∧ Inv3base s' := by
  cases h with
  | ok hst _ =>
  obtain ⟨i1, i2, i3, -⟩ := hinv
  have hsh := hst.2.2.2.2.2.1
  have nodup : (rootIdx ls).Nodup :=
    ((pairwise_lt_range _).sublist List.filter_sublist).imp Nat.ne_of_lt
  have live : ∀ (hd : Holder), HolderLive s hd → HolderLive (allocEff s pr ow ls) hd := by
    intro hd hl; cases hd with
    | frame f => exact hl
    | place p => exact alloc_usable_old hl
  refine ⟨⟨?_, ?_, hwf.ne, hwf.nodup, hwf.frames, ?_, ?_, ?_, ?_,
    alloc_rootChain hwf hst, alloc_rootHeld hwf hwf.rootHeld⟩, ?_, ?_, ?_, i4_always _⟩
  · intro b y a hb ho
    rcases alloc_get hb with ⟨-, hb'⟩ | ⟨-, _, -, rfl⟩
    · exact hwf.origin b y a hb' ho
    · cases ho
  · intro a y hy l hl
    show l < (allocP s ow ls).length
    rw [allocP_len]
    rcases alloc_get hy with ⟨-, hy'⟩ | ⟨-, i, -, rfl⟩
    · have := hwf.fp a y hy' l hl; omega
    · have := (mem_footprint.1 hl).1; rwa [allocP_len] at this
  · intro q pl f hq ho
    rcases shapeP_get hq with ⟨-, hq'⟩ | ⟨-, i, -, -, rfl⟩
    · exact hwf.ownerFrame q pl f hq' ho
    · simp only [shapeOwner] at ho; split at ho <;> cases ho
  · intro q pl o hq ho
    show o < (allocP s ow ls).length
    rw [allocP_len]
    rcases shapeP_get hq with ⟨-, hq'⟩ | ⟨-, i, hi, -, rfl⟩
    · have := hwf.ownerPlace q pl o hq' ho; omega
    · simp only [shapeOwner] at ho; split at ho
      · rename_i o' ho'; cases ho
        have h2 := (hsh i (List.mem_range.2 hi)).2
        rw [ho'] at h2; exact Nat.lt_of_lt_of_le h2.2 (by omega)
      · cases ho; have := hst.2.2.1.lt; omega
  · intro q pl r hq hp
    rcases shapeP_get hq with ⟨hq', hq''⟩ | ⟨hq', i, hi, rfl, rfl⟩
    · obtain ⟨pr', hpr, hlt, ho, hd⟩ := hwf.parts q pl r hq'' hp
      refine ⟨pr', by show (allocP s ow ls)[r]? = _; rw [allocP_lt (by omega)]; exact hpr, hlt, ho,
        ?_⟩
      simp [allocEff, show ¬ s.P.length ≤ r by omega, show ¬ s.P.length ≤ q by omega, hd]
    · have h1 := (hsh i (List.mem_range.2 hi)).1
      simp only at hp; rw [hp] at h1; obtain ⟨hr₁, hr₂, hown⟩ := h1
      have hri : r - s.P.length < ls.length := by omega
      refine ⟨_, by show (allocP s ow ls)[r]? = _
                    rw [show r = s.P.length + (r - s.P.length) by omega, allocP, shapeP_new hri],
        by omega, ?_, by simp [allocEff, show s.P.length ≤ r by omega]⟩
      simp only [shapeOwner, hown]
  · intro a y hy ya
    rcases alloc_get hy with ⟨-, hy'⟩ | ⟨-, i, hi, rfl⟩
    · exact live _ (hwf.poss a y hy' ya)
    · exact alloc_shapeOwner_live hst (rootIdx_mem hi).1
  · intro a b x y p hab ha hb xa ya xp yp hnab hnba
    rcases alloc_get ha with ⟨ha', hx⟩ | ⟨ha', i, hi, rfl⟩ <;>
      rcases alloc_get hb with ⟨hb', hy⟩ | ⟨hb', i', hi', rfl⟩
    · rw [alloc_ancs_lt hb'] at hnab; rw [alloc_ancs_lt ha'] at hnba
      exact i1 a b x y p hab hx hy xa ya xp yp hnab hnba
    · have := hwf.fp a x hx p xp
      have := shape_root_fp_ge yp; omega
    · have := hwf.fp b y hy p yp
      have := shape_root_fp_ge xp; omega
    · have hk : a - s.A.length ≠ b - s.A.length := by omega
      have hii : i ≠ i' := fun e => hk ((nodup.getElem?_inj (lt_of_getElem? hi)).1 (by
        rw [hi, hi', e]))
      exact (shape_roots_disjoint hii (rootIdx_mem hi).2 (rootIdx_mem hi').2 xp yp).elim
  · intro b y a hb ho
    rcases alloc_get hb with ⟨-, hb'⟩ | ⟨-, _, -, rfl⟩
    · obtain ⟨x₁, hx₁, hh⟩ := i2 b y a hb' ho
      exact ⟨x₁, by rw [alloc_lt (lt_of_getElem? hx₁)]; exact hx₁, hh⟩
    · cases ho
  · intro q hq x hx
    by_cases hql : q < s.P.length
    · have hx' : x ∈ s.D q := by simpa [allocEff, show ¬ s.P.length ≤ q by omega] using hx
      obtain ⟨y, hy, ya⟩ := i3 q (alloc_usable_back hwf hq hql) x hx'
      exact ⟨y, by rw [alloc_lt (lt_of_getElem? hy)]; exact hy, ya⟩
    · simp [allocEff, show s.P.length ≤ q by omega] at hx

/-- `alloc_fresh` (B5; C6): the new places and the new authorities have fresh identities. Before
`alloc`, no place is at an index `|P| + i`, no authority covers one, no place has one as parent or
owner; no authority is at an index `|A| + j` or has one as origin. After `alloc`, the new places
are `Uninit`, without anchor, alive, not freed and not pinned. -/
theorem alloc_fresh {k : K} {pr ow : Nat} {ls : List (Option Nat × Option Nat × Nat)}
    {s s' : S3} (hwf : WF3 s) (h : AllocStep k pr ow ls s (.ok s')) :
    (∀ i, s.P[s.P.length + i]? = none) ∧ (∀ j, s.A[s.A.length + j]? = none) ∧
    (∀ (a : Nat) (y : Authority) (i : Nat), s.A[a]? = some y → s.P.length + i ∉ y.footprint) ∧
    (∀ (q : Nat) (pl : Place) (i : Nat), s.P[q]? = some pl →
      pl.parent ≠ some (s.P.length + i) ∧ pl.owner ≠ .place (s.P.length + i)) ∧
    (∀ (b : Nat) (y : Authority) (j : Nat), s.A[b]? = some y →
      y.origin ≠ some (s.A.length + j)) ∧
    s'.P.length = s.P.length + ls.length ∧
    ∀ i, s'.I (s.P.length + i) = .uninit ∧ s'.D (s.P.length + i) = [] ∧
      s'.dead (s.P.length + i) = false ∧ s'.freed (s.P.length + i) = false ∧
      s'.pin (s.P.length + i) = false := by
  cases h with
  | ok _ _ =>
  refine ⟨fun _ => List.getElem?_eq_none (by omega), fun _ => List.getElem?_eq_none (by omega),
    fun a y i hy hl => by have := hwf.fp a y hy _ hl; omega,
    fun q pl i hq => ⟨fun hp => ?_, fun ho => ?_⟩, fun b y j hy ho => ?_, allocP_len s ow ls,
    fun i => by simp [allocEff]⟩
  · obtain ⟨pr', hpr, -⟩ := hwf.parts q pl _ hq hp
    have := lt_of_getElem? hpr; omega
  · have := hwf.ownerPlace q pl _ hq ho; omega
  · have := hwf.origin b y _ hy ho; have := lt_of_getElem? hy; omega

/-- `alloc_owned_root` (B5; C6): each root element of the shape is a usable owned root, owned by
its owning element or by `owner`; its root authority `Modify`, without origin, covers its
footprint and is held by that owner. -/
theorem alloc_owned_root {k : K} {pr ow : Nat} {ls : List (Option Nat × Option Nat × Nat)}
    {s s' : S3} (h : AllocStep k pr ow ls s (.ok s')) :
    ∀ m i, (rootIdx ls)[m]? = some i →
      s'.P[s.P.length + i]? = some ⟨none, shapeOwner ls (.place ow) i, ((ls[i]?).map (·.2.2)).getD 0⟩ ∧
      OwnedRoot s' (s.P.length + i) ∧ s'.Usable (s.P.length + i) ∧
      s'.A[s.A.length + m]? =
        some ⟨.modify, none, footprint s'.P (s.P.length + i), shapeOwner ls (.place ow) i, true⟩ := by
  cases h with
  | ok hst _ =>
  intro m i hm
  obtain ⟨hil, hin⟩ := rootIdx_mem hm
  have hnew : (allocEff s pr ow ls).P[s.P.length + i]? =
      some ⟨none, shapeOwner ls (.place ow) i, ((ls[i]?).map (·.2.2)).getD 0⟩ := by
    have := shapeP_new (P := s.P) (hd := .place ow) hil; rw [hin] at this; exact this
  refine ⟨hnew, ?_, alloc_usable_new hst (i + 1) i (Nat.lt_succ_self i) hil, ?_⟩
  · simp only [OwnedRoot, OptP, hnew, true_and]
    unfold shapeOwner; split <;> rfl
  · show (s.A ++ _)[s.A.length + m]? = _
    rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left, List.getElem?_map, hm]; rfl

/-- An accepted `alloc` creates a root (B5: `ok`, « nouvelle racine »; D2): the shape is not empty,
and its first element has no parent, which would have to be an earlier element (`ShapeOK`). With
`alloc_owned_root` at `m = 0`, the new place `|P|` is a usable owned root with its root authority. -/
theorem alloc_ok_new_root {k : K} {pr ow : Nat} {ls : List (Option Nat × Option Nat × Nat)}
    {s s' : S3} (h : AllocStep k pr ow ls s (.ok s')) : (rootIdx ls)[0]? = some 0 := by
  cases h with
  | ok hst _ =>
  obtain ⟨-, -, -, -, -, hsh, hne⟩ := hst
  cases ls with
  | nil => exact absurd rfl hne
  | cons e rest =>
    have h0 := (hsh 0 (List.mem_range.2 (by simp))).1
    cases hp : e.1 with
    | some r => simp [hp, OptP] at h0; omega
    | none => simp [rootIdx, List.range_succ_eq_map, hp]

/-- `alloc_owned_root` for the shape of one leaf, the `alloc` of pass 3 (B5; C6): the new place is
a usable root, owned by `owner`, whose footprint is itself; its root authority `Modify`, without
origin, covers that footprint and is held by `owner`. -/
theorem alloc_owned_root_leaf {k : K} {pr ow : Nat} {s s' : S3} (hwf : WF3 s)
    (h : AllocStep k pr ow [(none, none, 0)] s (.ok s')) :
    s'.P[s.P.length]? = some ⟨none, .place ow, 0⟩ ∧ OwnedRoot s' s.P.length ∧
    s'.Usable s.P.length ∧ (∀ l, l ∈ footprint s'.P s.P.length ↔ l = s.P.length) ∧
    s'.A[s.A.length]? = some ⟨.modify, none, footprint s'.P s.P.length, .place ow, true⟩ := by
  have h0 := alloc_owned_root h 0 0 rfl
  cases h with
  | ok hst _ =>
  obtain ⟨hnew, hroot, hu, hA⟩ := h0
  refine ⟨hnew, hroot, hu, fun l => ⟨fun hl => ?_, fun e => ?_⟩, hA⟩
  · obtain ⟨hl, -, -, hc | hc⟩ := mem_footprint.1 hl
    · exact hc
    · have := chain_lt hc; have : l < (allocP s ow [(none, none, 0)]).length := hl
      rw [allocP_len] at this; simp at this; omega
  · subst e
    have hlen : s.P.length < (allocEff s pr ow [(none, none, 0)]).P.length := by
      show s.P.length < (allocP s ow [(none, none, 0)]).length; rw [allocP_len]; simp
    refine mem_footprint.2 ⟨hlen, fun r hr he => ?_, hlen, .inl rfl⟩
    have hr' : r < s.P.length + 1 := by
      have : r < (allocP s ow [(none, none, 0)]).length := hr; rw [allocP_len] at this; simpa using this
    rcases Nat.lt_or_ge r s.P.length with hrl | hrl
    · have he' : parentOf s.P r = some s.P.length := by
        rw [← shape_parentOf_lt (hd := .place ow) (ls := [(none, none, 0)]) hrl]; exact he
      simp only [parentOf] at he'
      cases hq : s.P[r]? with
      | none => rw [hq] at he'; cases he'
      | some pl =>
        rw [hq] at he'
        obtain ⟨pr', hpr, -⟩ := hwf.parts r pl _ hq he'
        exact absurd (lt_of_getElem? hpr) (Nat.lt_irrefl _)
    · obtain rfl : r = s.P.length := by omega
      have he' : parentOf (allocP s ow [(none, none, 0)]) (s.P.length + 0) = some s.P.length := he
      rw [allocP, shape_parentOf_new (by simp)] at he'; cases he'

/-! ## Preservation of `AnchorOrder` (B8, C1) -/

theorem effAnchor_mem (s : S3) (x : Nat) : s.effAnchor x = x ∨ s.effAnchor x ∈ s.ancs x :=
  List.mem_cons.1 (List.getLastD_mem_cons (l := s.ancs x) (a := x))

theorem effAnchor_le (s : S3) (x : Nat) : s.effAnchor x ≤ x := by
  rcases effAnchor_mem s x with h | h
  · exact Nat.le_of_eq h
  · exact Nat.le_of_lt (chain_lt h)

/-- The effective anchor of `x` is the element without origin of its chain (C1). -/
theorem effAnchor_eq {s : S3} : ∀ n x, x < n → ∀ r, (r = x ∨ r ∈ s.ancs x) → s.org r = none →
    s.effAnchor x = r
  | 0, _, h, _, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, x, hx, r, hr, hro => by
    rcases hr with rfl | hr
    · simp [S3.effAnchor, S3.ancs, chain_none hro]
    · cases ho : s.org x with
      | none => rw [S3.ancs, chain_none ho] at hr; simp at hr
      | some o =>
        rcases ancs_step ho with ⟨hlt, he⟩ | he
        · have e : s.effAnchor x = s.effAnchor o := by
            simp only [S3.effAnchor, he, List.getLastD_cons]
          rw [e]; rw [he] at hr
          exact effAnchor_eq n o (by omega) r (List.mem_cons.1 hr) hro
        · rw [he] at hr; simp at hr

/-- Under the order of origins of `WF3`, the effective anchor has no origin (C1, B1). -/
theorem effAnchor_root {s : S3} (hw : ∀ (b : Nat) (y : Authority) (a : Nat), s.A[b]? = some y →
    y.origin = some a → a < b) (x : Nat) : s.org (s.effAnchor x) = none := by
  obtain ⟨r, hr, hro⟩ := reanchor_reaches_root hw (x + 1) x (Nat.lt_succ_self x)
  rw [effAnchor_eq (x + 1) x (Nat.lt_succ_self x) r hr hro]; exact hro

theorem effAnchor_congr {s s' : S3} {x : Nat} (h : s'.ancs x = s.ancs x) :
    s'.effAnchor x = s.effAnchor x := by simp only [S3.effAnchor, h]

theorem EffAnchorOK.get {s : S3} {x : Nat} {fd : Option Nat} (h : EffAnchorOK s x fd) :
    ∃ z, s.A[s.effAnchor x]? = some z := by
  unfold EffAnchorOK at h
  cases hz : s.A[s.effAnchor x]? with
  | none => rw [hz] at h; exact h.elim
  | some z => exact ⟨z, rfl⟩

/-- The effective anchor of an `EffAnchorOK` anchor has a frame. -/
theorem EffAnchorOK.frame {s : S3} {x : Nat} {fd : Option Nat} {z : Authority}
    (h : EffAnchorOK s x fd) (hz : s.A[s.effAnchor x]? = some z) :
    ∃ g, s.hframe z.holder = some g := by
  unfold EffAnchorOK at h; rw [hz] at h; simp only [OptP] at h
  cases hg : s.hframe z.holder with
  | none => rw [hg] at h; exact h.elim
  | some g => exact ⟨g, rfl⟩

/-- An `EffAnchorOK` anchor is an authority of `A`. -/
theorem EffAnchorOK.lt {s : S3} {x : Nat} {fd : Option Nat} (h : EffAnchorOK s x fd) :
    x < s.A.length := by
  obtain ⟨z, hz⟩ := h.get
  rcases effAnchor_mem s x with e | e
  · rw [e] at hz; exact lt_of_getElem? hz
  · have : s.org x ≠ none := fun ho => by rw [S3.ancs, chain_none ho] at e; simp at e
    simp only [S3.org] at this
    cases hx : s.A[x]? with
    | none => rw [hx] at this; exact absurd rfl this
    | some _ => exact lt_of_getElem? hx

theorem effAnchorOK_of_same {s s' : S3} {x x' : Nat} {z z' : Authority}
    (hz : s.A[s.effAnchor x]? = some z) (hz' : s'.A[s'.effAnchor x']? = some z')
    (hh : s'.hframe z'.holder = s.hframe z.holder) {fd fd' : Option Nat}
    (hanc : ∀ g f, fd = some f → (ancestor s'.F g f ↔ ancestor s.F g f)) (hfd : fd' = fd) :
    EffAnchorOK s' x' fd' ↔ EffAnchorOK s x fd := by
  rw [hfd]; unfold EffAnchorOK; rw [hz, hz']; simp only [OptP]; rw [hh]
  cases hg : s.hframe z.holder with
  | none => simp
  | some g =>
    cases hf : fd with
    | none => simp
    | some f => simp only; rw [hanc g f hf]

theorem effAnchorOK_congr {s s' : S3} (hA : s'.A = s.A) (hP : s'.P = s.P) (hF : s'.F = s.F)
    (x : Nat) (fd : Option Nat) : EffAnchorOK s' x fd ↔ EffAnchorOK s x fd := by
  have ho : s'.org = s.org := funext fun i => by simp only [S3.org, hA]
  have he : s'.effAnchor x = s.effAnchor x := by unfold S3.effAnchor S3.ancs; rw [ho]
  simp only [EffAnchorOK, he, hA, hF, S3.hframe_congr hP]

/-- `AnchorOrder` carries over to a state with the same places and stack, fewer usable places,
fewer anchors, the same chains of origins, and the same holders for the existing authorities
(B8, C1). -/
theorem AnchorOrder.of {s s' : S3} (ho : AnchorOrder s) (hP : s'.P = s.P) (hF : s'.F = s.F)
    (hu : ∀ q, s'.Usable q → s.Usable q) (hD : ∀ q, s'.Usable q → ∀ x ∈ s'.D q, x ∈ s.D q)
    (hanc : ∀ a, a < s.A.length → s'.ancs a = s.ancs a)
    (hA : ∀ (x : Nat) (y : Authority), s.A[x]? = some y →
      ∃ y', s'.A[x]? = some y' ∧ y'.origin = y.origin ∧ y'.holder = y.holder) :
    AnchorOrder s' := by
  intro q hq x hx
  have hok := ho q (hu q hq) x (hD q hq x hx)
  obtain ⟨z, hz⟩ := hok.get
  have he : s'.effAnchor x = s.effAnchor x := effAnchor_congr (hanc x hok.lt)
  obtain ⟨z', hz', -, e2⟩ := hA _ z hz
  exact (effAnchorOK_of_same hz (by rw [he]; exact hz') (by rw [e2, S3.hframe_congr hP])
    (fun g f _ => by rw [hF]) (S3.pframe_congr hP q)).2 hok

/-- A local anchor, without origin, of a usable place has a frame, the place has a frame on the
stack, and the first is the second or one of its ancestors (B8, C1). -/
theorem AnchorOrder.frames {s : S3} (_hwf : WF3 s) (_h3 : I3 s) (ho : AnchorOrder s) {q x : Nat}
    (hq : s.Usable q) (hx : x ∈ s.D q) {y : Authority} (hy : s.A[x]? = some y)
    (hyo : y.origin = none) :
    ∃ g f, s.hframe y.holder = some g ∧ s.pframe q = some f ∧ f ∈ s.F ∧ ancestor s.F g f := by
  obtain ⟨f, hf, hfF⟩ := hq.frameOf
  have hpf : s.pframe q = some f := pframe_iff.2 hf
  have he : s.effAnchor x = x :=
    effAnchor_eq (x + 1) x (Nat.lt_succ_self x) x (.inl rfl) (by simp [S3.org, hy, hyo])
  have hok := ho q hq x hx
  obtain ⟨g, hg⟩ := hok.frame (by rw [he]; exact hy)
  unfold EffAnchorOK at hok
  rw [he, hy, hpf] at hok; simp only [OptP] at hok; rw [hg] at hok; simp only at hok
  exact ⟨g, f, hg, hpf, hfF, hok⟩

theorem OnlyReleases.fwd {s s₁ : S3} (h : OnlyReleases s s₁) {x : Nat} {y : Authority}
    (hy : s.A[x]? = some y) :
    ∃ y', s₁.A[x]? = some y' ∧ y'.origin = y.origin ∧ y'.holder = y.holder := by
  obtain ⟨y', hy'⟩ : ∃ y', s₁.A[x]? = some y' :=
    ⟨_, List.getElem?_eq_some_iff.2 ⟨by rw [h.1]; exact lt_of_getElem? hy, rfl⟩⟩
  obtain ⟨y₀, hy₀, -, e1, -, e2, -⟩ := h.2 x y' hy'
  rw [hy] at hy₀; cases hy₀
  exact ⟨y', hy', e1, e2⟩

theorem release_releases (s : S3) (a : Nat) : OnlyReleases s (releaseEff s a) := by
  unfold releaseEff
  split
  · rename_i x hx
    refine ⟨by simp, fun j z hz => ?_⟩
    rw [set_get (lt_of_getElem? hx)] at hz
    split at hz
    · subst_vars; cases hz; exact ⟨x, hx, rfl, rfl, rfl, rfl, by simp⟩
    · exact ⟨z, hz, rfl, rfl, rfl, rfl, id⟩
  · exact ⟨rfl, fun j z hz => ⟨z, hz, rfl, rfl, rfl, rfl, id⟩⟩

/-- `derive` preserves `AnchorOrder` (B8, C1; MM-03.3 §3, O1), under `AnchorOrder` alone. -/
theorem derive_preserves_anchorOrder {s s' : S3} {src q : Nat} {m : Mode} (hao : AnchorOrder s)
    (h : DeriveStep src q m s (.ok s')) : AnchorOrder s' := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
  exact hao.of rfl rfl (fun _ hq => hq.of_eqs rfl rfl rfl) (fun _ _ _ hx => hx)
    (fun _ ha => ancs_addAuth_lt ha)
    (fun x y hy => ⟨y, by rw [deriveEff, addAuth_lt (lt_of_getElem? hy)]; exact hy, rfl, rfl⟩)

/-- `split` preserves `AnchorOrder` (B8, C1; MM-03.3 §3, O2), under `AnchorOrder` alone. -/
theorem split_preserves_anchorOrder {k : K} {s s' : S3} {src : Nat} {rs : List (List Nat)}
    (hao : AnchorOrder s) (h : SplitStep k src rs s (.ok s')) : AnchorOrder s' := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
  exact hao.of rfl rfl (fun _ hq => hq.of_eqs rfl rfl rfl) (fun _ _ _ hx => hx)
    (fun a ha => chain_congr fun j hj => by
      simp only [S3.org]; show ((s.A ++ _)[j]?).bind _ = _
      rw [List.getElem?_append_left (by omega)])
    (fun x y hy => ⟨y, by
      show (s.A ++ _)[x]? = _; rw [List.getElem?_append_left (lt_of_getElem? hy)]; exact hy,
      rfl, rfl⟩)

/-- `release` preserves `AnchorOrder` (B8, C1; MM-03.3 §3, O3), under `AnchorOrder` alone. -/
theorem release_preserves_anchorOrder {s s' : S3} {a : Nat} (hao : AnchorOrder s)
    (h : ReleaseStep a s (.ok s')) : AnchorOrder s' := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
  have hr := release_releases s a
  have hP : (releaseEff s a).P = s.P := by unfold releaseEff; split <;> rfl
  have hF : (releaseEff s a).F = s.F := by unfold releaseEff; split <;> rfl
  have hd : (releaseEff s a).dead = s.dead := by unfold releaseEff; split <;> rfl
  have hD : ∀ q, ∀ x ∈ (releaseEff s a).D q, x ∈ s.D q := fun q x hx => by
    cases hy : s.A[a]? with
    | none => unfold releaseEff at hx; rw [hy] at hx; exact hx
    | some y => exact (release_D_mem hy hx).1
  exact hao.of hP hF (fun q hq => (S3.Usable.congr hP hF hd).1 hq)
    (fun q _ x hx => hD q x hx) (fun _ _ => by unfold S3.ancs; rw [hr.org])
    (fun x y hy => hr.fwd hy)

/-- `depend` preserves `AnchorOrder` (B8, C1; MM-03.3 §3, O5), under `AnchorOrder` alone: the new anchor
satisfies the precondition on its effective anchor. -/
theorem depend_preserves_anchorOrder {s s' : S3} {q x : Nat} (hao : AnchorOrder s)
    (h : DependStep q x s (.ok s')) : AnchorOrder s' := by
  obtain ⟨⟨-, -, -, -, hok⟩, rfl⟩ := Guarded.ok_iff.1 h
  intro r hr y hy
  have hr' : s.Usable r := hr.of_eqs rfl rfl rfl
  rw [effAnchorOK_congr (s' := dependEff s q x) (s := s) rfl rfl rfl,
    S3.pframe_congr (s' := dependEff s q x) (s := s) rfl]
  simp only [dependEff] at hy
  split at hy
  · rename_i hrq; subst hrq
    rcases List.mem_append.1 hy with hy | hy
    · exact hao _ hr' y hy
    · simp at hy; subst hy; exact hok
  · exact hao r hr' y hy

/-- `write3`, `writeShared`, `pin` and `unpin` preserve `AnchorOrder` (B8, C1): they change neither
places, stack, anchors nor authorities. -/
theorem write3_preserves_anchorOrder {s : S3} (ls : List Nat) (hao : AnchorOrder s) :
    AnchorOrder (write3Eff s ls) :=
  hao.of rfl rfl (fun _ hq => hq.of_eqs rfl rfl rfl) (fun _ _ _ hx => hx) (fun _ _ => rfl)
    (fun _ y hy => ⟨y, hy, rfl, rfl⟩)

/-- `pin` and `unpin` preserve `AnchorOrder` (B8, C1; A8): they only set the pin state. -/
theorem pinEff_preserves_anchorOrder {s : S3} (p : Nat) (b : Bool) (hao : AnchorOrder s) :
    AnchorOrder (pinEff s p b) :=
  hao.of rfl rfl (fun _ hq => hq.of_eqs rfl rfl rfl) (fun _ _ _ hx => hx) (fun _ _ => rfl)
    (fun _ y hy => ⟨y, hy, rfl, rfl⟩)

/-- `endUse` preserves `AnchorOrder` (B8, C1; A6), under `AnchorOrder` alone. -/
theorem endUse_preserves_anchorOrder {k : K} {s s' : S3} {p : Nat} (hao : AnchorOrder s)
    (h : EndUseStep k p s (.ok s')) : AnchorOrder s' := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
  have hr := (endUseS_releases s p).trans cleanup_releases
  refine hao.of rfl rfl (fun q hq => ?_) (fun q _ x hx => ?_)
    (fun a _ => congrArg (chain · a) hr.org) (fun x y hy => hr.fwd hy)
  · exact S3.Usable.mono (s := s) (s' := endUseEff s p) rfl (fun _ h => h)
      (fun q h => by simp only [endUseEff, cleanup, endUseS, Bool.or_eq_false_iff] at h; exact h.1) hq
  · simp only [endUseEff, cleanup, endUseS] at hx; split at hx
    · simp at hx
    · exact hx

/-- `free` preserves `AnchorOrder` (B8, C1; A6), under `AnchorOrder` alone. -/
theorem free_preserves_anchorOrder {k : K} {s s' : S3} {p auth : Nat} (hao : AnchorOrder s)
    (h : FreeStep k p auth s (.ok s')) : AnchorOrder s' := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
  have hr := (freeS_releases s p).trans cleanup_releases
  refine hao.of rfl rfl (fun q hq => ?_) (fun q _ x hx => ?_)
    (fun a _ => congrArg (chain · a) hr.org) (fun x y hy => hr.fwd hy)
  · exact S3.Usable.mono (s := s) (s' := freeEff s p) rfl (fun _ h => h)
      (fun q h => by simp only [freeEff, cleanup, freeS, Bool.or_eq_false_iff] at h; exact h.1) hq
  · simp only [freeEff, cleanup, freeS] at hx; split at hx
    · simp at hx
    · exact hx

theorem enter_frameOf_old {s : S3} {ps : List Nat} {ls : List (Option Nat × Option Nat × Nat)}
    (hwf : WF3 s) {q f : Nat} (hq : q < s.P.length) :
    FrameOf (enterEff s ps ls) q f ↔ FrameOf s q f := by
  constructor
  · intro h
    revert hq
    induction h with
    | @frame q f pl hpl ho =>
      intro hq
      exact .frame (by have : (enterP s ls)[q]? = some pl := hpl; rwa [enterP_lt hq] at this) ho
    | @place q o f pl hpl ho _ ih =>
      intro hq
      have hpl' : s.P[q]? = some pl := by
        have : (enterP s ls)[q]? = some pl := hpl; rwa [enterP_lt hq] at this
      exact .place hpl' ho (ih (hwf.ownerPlace q pl o hpl' ho))
  · intro h
    clear hq
    induction h with
    | frame hpl ho =>
      exact .frame (show (enterP s ls)[_]? = _ by rw [enterP_lt (lt_of_getElem? hpl)]; exact hpl) ho
    | place hpl ho _ ih =>
      exact .place (show (enterP s ls)[_]? = _ by rw [enterP_lt (lt_of_getElem? hpl)]; exact hpl)
        ho ih

theorem enter_pframe_old {s : S3} {ps : List Nat} {ls : List (Option Nat × Option Nat × Nat)}
    (hwf : WF3 s) {q : Nat} (hq : q < s.P.length) :
    (enterEff s ps ls).pframe q = s.pframe q :=
  Option.ext fun f => by rw [pframe_iff, pframe_iff, enter_frameOf_old hwf hq]

/-- `enterFrame` preserves `AnchorOrder` (B8, C1; MM-03.3 §4, O6), under `WF3`: the frames of old
places do not change, the new frame is younger than all the others, and an effective anchor,
without origin, is never a parameter (A3). -/
theorem enter_preserves_anchorOrder {s s' : S3} {ps : List Nat}
    {ls : List (Option Nat × Option Nat × Nat)} (hwf : WF3 s) (hao : AnchorOrder s)
    (h : EnterStep ps ls s (.ok s')) : AnchorOrder s' := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  intro q hq x hx
  by_cases hlt : q < s.P.length
  · have hq0 := enter_usable_back hwf hq hlt
    have hx0 : x ∈ s.D q := by simpa [enterEff, show ¬ s.P.length ≤ q by omega] using hx
    have hok := hao q hq0 x hx0
    obtain ⟨z, hz⟩ := hok.get
    obtain ⟨g, hg⟩ := hok.frame hz
    have hxl := hok.lt
    have he : (enterEff s ps ls).effAnchor x = s.effAnchor x := effAnchor_congr (enter_ancs_lt hxl)
    have hrl : s.effAnchor x < s.A.length := Nat.lt_of_le_of_lt (effAnchor_le s x) hxl
    have hro : s.org (s.effAnchor x) = none := effAnchor_root hwf.origin x
    have hnp : s.effAnchor x ∉ ps := fun hp => by
      have := hpre.2.1 _ hp; simp only [OptP, hz] at this
      exact this.2.2 (by simpa [S3.org, hz] using hro)
    refine (effAnchorOK_of_same (s' := enterEff s ps ls) (z' := z) hz
      (by rw [he, enter_lt hrl, hz]; simp [hnp]) ?_ ?_ (enter_pframe_old hwf hlt)).2 hok
    · cases hh : z.holder with
      | frame f => rfl
      | place p =>
        rw [hh] at hg
        exact enter_pframe_old hwf (pframe_iff.1 hg).lt
    · intro g f hf
      obtain ⟨f', hf', hfF⟩ := hq0.frameOf
      rw [pframe_iff.2 hf'] at hf; rw [← Option.some.inj hf]
      have hne : (s.nF != f') = true := by
        simpa using fun e => Nat.lt_irrefl _ (e ▸ hwf.frames _ hfF)
      show g ∈ (s.nF :: s.F).dropWhile (· != f') ↔ g ∈ s.F.dropWhile (· != f')
      rw [List.dropWhile_cons]; simp only [hne, ↓reduceIte]
  · simp [enterEff, show s.P.length ≤ q by omega] at hx

theorem alloc_frameOf_old {s : S3} {pr o : Nat} {ls : List (Option Nat × Option Nat × Nat)}
    (hwf : WF3 s) {q f : Nat} (hq : q < s.P.length) :
    FrameOf (allocEff s pr o ls) q f ↔ FrameOf s q f := by
  constructor
  · intro h
    revert hq
    induction h with
    | @frame q f pl hpl ho =>
      intro hq
      exact .frame (by have : (allocP s o ls)[q]? = some pl := hpl; rwa [allocP_lt hq] at this) ho
    | @place q o' f pl hpl ho _ ih =>
      intro hq
      have hpl' : s.P[q]? = some pl := by
        have : (allocP s o ls)[q]? = some pl := hpl; rwa [allocP_lt hq] at this
      exact .place hpl' ho (ih (hwf.ownerPlace q pl o' hpl' ho))
  · intro h
    clear hq
    induction h with
    | frame hpl ho =>
      exact .frame (show (allocP s o ls)[_]? = _ by rw [allocP_lt (lt_of_getElem? hpl)]; exact hpl) ho
    | place hpl ho _ ih =>
      exact .place (show (allocP s o ls)[_]? = _ by rw [allocP_lt (lt_of_getElem? hpl)]; exact hpl)
        ho ih

theorem alloc_pframe_old {s : S3} {pr o : Nat} {ls : List (Option Nat × Option Nat × Nat)}
    (hwf : WF3 s) {q : Nat} (hq : q < s.P.length) :
    (allocEff s pr o ls).pframe q = s.pframe q :=
  Option.ext fun f => by rw [pframe_iff, pframe_iff, alloc_frameOf_old hwf hq]

/-- `alloc` preserves `AnchorOrder` (B8, C1; B5; C6), under `WF3`: the frames of old places do not
change and the new places have no anchor. -/
theorem alloc_preserves_anchorOrder {k : K} {pr ow : Nat}
    {ls : List (Option Nat × Option Nat × Nat)} {s s' : S3} (hwf : WF3 s)
    (hao : AnchorOrder s) (h : AllocStep k pr ow ls s (.ok s')) : AnchorOrder s' := by
  cases h with
  | ok _ _ =>
  intro q hq x hx
  by_cases hql : q < s.P.length
  · have hq0 := alloc_usable_back hwf hq hql
    have hx0 : x ∈ s.D q := by simpa [allocEff, show ¬ s.P.length ≤ q by omega] using hx
    have hok := hao q hq0 x hx0
    obtain ⟨z, hz⟩ := hok.get
    obtain ⟨g, hg⟩ := hok.frame hz
    have hxl := hok.lt
    have he : (allocEff s pr ow ls).effAnchor x = s.effAnchor x :=
      effAnchor_congr (alloc_ancs_lt hxl)
    have hrl : s.effAnchor x < s.A.length := Nat.lt_of_le_of_lt (effAnchor_le s x) hxl
    refine (effAnchorOK_of_same (s' := allocEff s pr ow ls) (z' := z) hz (by
      rw [he, alloc_lt hrl]; exact hz) ?_ (fun _ _ _ => Iff.rfl) (alloc_pframe_old hwf hql)).2 hok
    cases hh : z.holder with
    | frame f => rfl
    | place p =>
      rw [hh] at hg
      exact alloc_pframe_old hwf (pframe_iff.1 hg).lt
  · simp [allocEff, show s.P.length ≤ q by omega] at hx

theorem transfer_D (s : S3) (src dst q : Nat) : (transferEff s src dst).D q =
    if q = dst then s.D dst ++ depsOf s src else if partOf s.P q src then [] else s.D q := rfl

theorem depsOf_sub_movedDeps {s : S3} {src x : Nat} (h : x ∈ depsOf s src) :
    x ∈ movedDeps s src := by
  simp only [depsOf, movedDeps, List.mem_flatMap, List.mem_filter, decide_eq_true_eq] at h ⊢
  obtain ⟨r, ⟨hr, hp⟩, hx⟩ := h
  exact ⟨r, ⟨hr, .inl hp⟩, hx⟩

theorem mem_movedDeps_owned {s : S3} {src q x : Nat} (hq : s.Usable q) (ho : OwnedIn s.P src q)
    (hx : x ∈ s.D q) : x ∈ movedDeps s src := by
  simp only [movedDeps, List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_range]
  exact ⟨q, ⟨hq.lt, .inr ⟨ownedWithin_iff.2 ho, hq⟩⟩, hx⟩

theorem transfer_frameOf_fwd {s : S3} {src dst q f : Nat} (h : FrameOf s q f)
    (hn : ¬ OwnedIn s.P src q) : FrameOf (transferEff s src dst) q f := by
  induction h with
  | @frame q f pl hpl ho =>
    exact .frame (pl := pl) (by rw [transfer_P_get, hpl]; simp [ho, heldIn]) ho
  | @place q o f pl hpl ho hf ih =>
    have h1 : ¬ partOf s.P o src := fun hp => hn (.direct hpl ho hp)
    have h2 : ¬ OwnedIn s.P src o := fun ho' => hn (.step hpl ho ho')
    exact .place (pl := pl) (by rw [transfer_P_get, hpl]; simp [ho, heldIn, h1]) ho (ih h2)

theorem transfer_frameOf_back {s : S3} {src dst q f : Nat} (h : FrameOf (transferEff s src dst) q f) :
    (FrameOf s q f ∧ ¬ OwnedIn s.P src q) ∨
      (OwnedIn s.P src q ∧ FrameOf (transferEff s src dst) dst f) := by
  induction h with
  | @frame q f pl hpl ho =>
    rw [transfer_P_get] at hpl
    cases h' : s.P[q]? with
    | none => rw [h'] at hpl; cases hpl
    | some pl₀ =>
      rw [h'] at hpl; simp only [Option.map_some, Option.some.injEq] at hpl; subst hpl
      split at ho
      · cases ho
      · left; refine ⟨.frame h' ho, fun hn => ?_⟩
        cases hn with
        | direct h1 h2 _ => rw [h'] at h1; cases h1; rw [ho] at h2; cases h2
        | step h1 h2 _ => rw [h'] at h1; cases h1; rw [ho] at h2; cases h2
  | @place q o f pl hpl ho hf ih =>
    rw [transfer_P_get] at hpl
    cases h' : s.P[q]? with
    | none => rw [h'] at hpl; cases hpl
    | some pl₀ =>
      rw [h'] at hpl; simp only [Option.map_some, Option.some.injEq] at hpl; subst hpl
      split at ho
      · rename_i hh
        cases ho
        cases hpo : pl₀.owner with
        | frame g => rw [hpo] at hh; exact hh.elim
        | place r => rw [hpo] at hh; exact .inr ⟨.direct h' hpo hh, hf⟩
      · rename_i hh
        rcases ih with ⟨hf0, hn⟩ | ⟨ho', hd⟩
        · left; refine ⟨.place h' ho hf0, fun hq => ?_⟩
          cases hq with
          | direct h1 h2 h3 =>
            rw [h'] at h1; cases h1; rw [ho] at h2; cases h2; exact hh (by rw [ho]; exact h3)
          | step h1 h2 h3 => rw [h'] at h1; cases h1; rw [ho] at h2; cases h2; exact hn h3
        · exact .inr ⟨.step h' ho ho', hd⟩

/-- The destination of an accepted transfer is not owned by the source: its owner chain would
come back to it (A5). -/
theorem transfer_dst_not_owned {s : S3} {src dst f : Nat} :
    ∀ {q}, FrameOf (transferEff s src dst) q f → OwnedIn s.P src q → ¬ OwnedIn s.P src dst := by
  intro q h
  induction h with
  | @frame q f pl hpl ho =>
    intro hq _
    rw [transfer_P_get] at hpl
    cases h' : s.P[q]? with
    | none => rw [h'] at hpl; cases hpl
    | some pl₀ =>
      rw [h'] at hpl; simp only [Option.map_some, Option.some.injEq] at hpl; subst hpl
      split at ho
      · cases ho
      · cases hq with
        | direct h1 h2 _ => rw [h'] at h1; cases h1; rw [ho] at h2; cases h2
        | step h1 h2 _ => rw [h'] at h1; cases h1; rw [ho] at h2; cases h2
  | @place q o f pl hpl ho hf ih =>
    intro hq hd
    rw [transfer_P_get] at hpl
    cases h' : s.P[q]? with
    | none => rw [h'] at hpl; cases hpl
    | some pl₀ =>
      rw [h'] at hpl; simp only [Option.map_some, Option.some.injEq] at hpl; subst hpl
      split at ho
      · cases ho; exact ih hd hd
      · rename_i hh
        cases hq with
        | direct h1 h2 h3 =>
          rw [h'] at h1; cases h1; rw [ho] at h2; cases h2; exact hh (by rw [ho]; exact h3)
        | step h1 h2 h3 => rw [h'] at h1; cases h1; rw [ho] at h2; cases h2; exact ih h3 hd

theorem transfer_pframe_unmoved {s : S3} {src dst q : Nat} (hn : ¬ OwnedIn s.P src q) :
    (transferEff s src dst).pframe q = s.pframe q :=
  Option.ext fun f => by
    rw [pframe_iff, pframe_iff]
    exact ⟨fun h => (transfer_frameOf_back h).elim (fun h => h.1) (fun h => absurd h.1 hn),
      fun h => transfer_frameOf_fwd h hn⟩

/-- An anchor whose effective anchor does not move with the value keeps its order (B8, C1; A4,
A5). -/
theorem transfer_effAnchorOK_unmoved {s : S3} {src dst x : Nat} {z : Authority}
    (hz : s.A[s.effAnchor x]? = some z) (hm : ¬ AnchorMoves s src (s.effAnchor x))
    (fd : Option Nat) :
    EffAnchorOK (transferEff s src dst) x fd ↔ EffAnchorOK s x fd := by
  have hm' : ¬ HolderMoves s src z.holder := by unfold AnchorMoves at hm; rw [hz] at hm; exact hm
  have hnh : ¬ heldIn s.P src z.holder := by
    cases hh : z.holder with
    | frame g => simp [heldIn]
    | place p => rw [hh] at hm'; exact fun h => hm' (.inl h)
  have he : (transferEff s src dst).effAnchor x = s.effAnchor x :=
    effAnchor_congr (by rw [(transfer_skel s src dst).ancs])
  refine effAnchorOK_of_same (z' := z) hz (by rw [he, transfer_A_get, hz]; simp [hnh]) ?_
    (fun _ _ _ => Iff.rfl) rfl
  cases hh : z.holder with
  | frame g => rfl
  | place p =>
    rw [hh] at hm'
    exact transfer_pframe_unmoved (fun ho => hm' (.inr (ownedWithin_iff.2 ho)))

/-- `transfer` preserves `AnchorOrder` (B8, C1; MM-03.3 §3, O4; MM-03.3.6), under `WF3`: when the
effective anchor or the dependent moves, by the clause B8; otherwise both frames are unchanged. -/
theorem transfer_preserves_anchorOrder {k : K} {s s' : S3} {src dst : Nat} (hwf : WF3 s)
    (hao : AnchorOrder s) (h : TransferStep k src dst s (.ok s')) : AnchorOrder s' := by
  obtain ⟨⟨hsrc, -, -, -, -, -, -, -, -, -, -, -, h8⟩, rfl⟩ := Guarded.ok_iff.1 h
  intro q hq x hx
  by_cases hm : AnchorMoves s src (s.effAnchor x) ∨ q = dst ∨ OwnedWithin s src q
  · exact h8 q (List.mem_range.2 (by have := hq.lt; rwa [transfer_len] at this)) hq x hx hm
  have hm1 : ¬ AnchorMoves s src (s.effAnchor x) := fun e => hm (.inl e)
  have hm2 : q ≠ dst := fun e => hm (.inr (.inl e))
  have hown : ¬ OwnedIn s.P src q := fun e => hm (.inr (.inr (ownedWithin_iff.2 e)))
  have hq0 := transfer_usable_back hwf hsrc hq
  rw [transfer_D] at hx; simp only [hm2, ↓reduceIte] at hx
  split at hx
  · simp at hx
  · have hok := hao q hq0 x hx
    obtain ⟨z, hz⟩ := hok.get
    rw [transfer_pframe_unmoved hown]
    exact (transfer_effAnchorOK_unmoved hz hm1 _).2 hok

/-- `exitFrame` preserves `AnchorOrder` (B8, C1; MM-03.3 §4, O7; A7), under `WF3`: re-anchoring
replaces an anchor by an authority of its chain, which has the same effective anchor, and the
frame of a usable place stays below the popped frame. -/
theorem exit_preserves_anchorOrder {k : K} {s s' : S3} (hwf : WF3 s) (hao : AnchorOrder s)
    (h : ExitStep k s (.ok s')) : AnchorOrder s' := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  unfold ExitPre at hpre
  split at hpre
  · rename_i f F₀ hF
    obtain ⟨-, hR1, h3, -⟩ := hpre
    have e := exitEff_eq hF
    have hP : (exitEff s).P = s.P := by rw [e]
    have hnd := (List.nodup_cons.1 (hF ▸ hwf.nodup)).1
    intro q hq x' hx'
    have hq₁ : ({ s with F := F₀ } : S3).Usable q :=
      (S3.Usable.congr (s := ({ s with F := F₀ } : S3)) hP (by rw [e]) (by rw [e])).1 hq
    have hq₀ : s.Usable q :=
      S3.Usable.mono (s := s) (s' := ({ s with F := F₀ } : S3)) rfl
        (fun g hg => by rw [hF]; exact List.mem_cons_of_mem _ hg) (fun _ h => h) hq₁
    rw [e] at hx'; simp only [List.mem_map] at hx'
    obtain ⟨x, hx, rfl⟩ := hx'
    obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.1 (hR1 q (List.mem_range.2 hq₀.lt) hq₁ x hx)
    rw [hz]; simp only [Option.getD_some]
    have hok := hao q hq₀ x hx
    obtain ⟨r, hr, hro⟩ := reanchor_reaches_root hwf.origin (x + 1) x (Nat.lt_succ_self x)
    have hex : s.effAnchor x = r := effAnchor_eq (x + 1) x (Nat.lt_succ_self x) r hr hro
    have hzx : z = x ∨ z ∈ s.ancs x := List.mem_cons.1 (firstSurv_some hz).1
    have hrz : r = z ∨ r ∈ s.ancs z := by
      rcases hzx with rfl | hzx
      · exact hr
      · rcases hr with rfl | hr
        · rw [S3.ancs, chain_none hro] at hzx; simp at hzx
        · exact ancs_root_after (x + 1) x (Nat.lt_succ_self x) z r hzx hr hro
    obtain ⟨y, hy⟩ := hok.get
    rw [hex] at hy
    have hyo : y.origin = none := by simpa [S3.org, hy] using hro
    have hro' : (exitEff s).org r = none := by
      simp only [S3.org, exit_A_get hF, hy, Option.map_some, Option.bind_some]
      rcases exitG_origin (s := s) (F₀ := F₀) (a := r) (y := y) with e' | ⟨-, hn, -⟩
      · rw [e']; exact hyo
      · exact absurd hyo hn
    have hrz' : r = z ∨ r ∈ (exitEff s).ancs z := hrz.imp id fun hh =>
      exit_root_kept hF h3 (z + 1) z (Nat.lt_succ_self z) r hh hro
    have hez : (exitEff s).effAnchor z = r := effAnchor_eq (z + 1) z (Nat.lt_succ_self z) r hrz' hro'
    refine (effAnchorOK_of_same (s := s) (s' := exitEff s) (x := x) (x' := z)
      (z' := exitG s F₀ r y) (by rw [hex]; exact hy) (by rw [hez, exit_A_get hF, hy]; rfl)
      (by rw [(exitG_same s F₀ r y).2.2, S3.hframe_congr hP]) ?_ (S3.pframe_congr hP q)).2 hok
    intro g f₁ hf
    obtain ⟨f', hf', hfF⟩ := hq₁.frameOf
    rw [pframe_iff.2 ((FrameOf.congr (s := s) (s' := ({ s with F := F₀ } : S3)) rfl).1 hf')] at hf
    rw [← Option.some.inj hf]
    have hne : (f != f') = true := by simpa using fun e => hnd (by rw [e]; exact hfF)
    rw [show (exitEff s).F = F₀ by rw [e]]
    show g ∈ F₀.dropWhile (· != f') ↔ g ∈ s.F.dropWhile (· != f')
    rw [hF, List.dropWhile_cons]; simp only [hne, ↓reduceIte]
  · exact hpre.elim

/-! ## Exercise requires holding (A2, B2) -/

/-- `exercise_requires_hold` (A2), by mode (B2): an authority exercisable at mode `m` is active, its
mode permits `m`, and it is held by the current frame, or held by a place on which the current
frame already has an authority exercisable at `m` with an effective mode permitting `m`. -/
theorem exercise_requires_hold {s : S3} {a : Nat} {m : Mode} (h : s.ExercisableAt a m) :
    ∃ y, s.A[a]? = some y ∧ y.active = true ∧ m.le y.mode ∧
      (y.holder = .frame s.top ∨ ∃ p, y.holder = .place p ∧ HasRight s m p) := by
  cases h with
  | base hy ha hm hf => exact ⟨_, hy, ha, hm, .inl hf⟩
  | @held _ p b _ y hy ha hm hp hb hc =>
    have hlt : b < s.A.length := by
      cases hb with
      | base hy' _ _ _ => exact lt_of_getElem? hy'
      | held hy' _ _ _ _ _ => exact lt_of_getElem? hy'
    exact ⟨y, hy, ha, hm, .inr ⟨p, hp, b, List.mem_range.2 hlt, hb, hc⟩⟩

/-- Under the possession clause of `WF3`, an exercisable authority has a live holder: when it is
held by a place, that place is usable (A4; B2). With `exercise_requires_hold`, this gives the
pass-2 conclusion `s.Usable p`. -/
theorem exercise_requires_hold_live {s : S3} {a : Nat} {m : Mode} (hwf : WF3 s)
    (h : s.ExercisableAt a m) :
    ∃ y, s.A[a]? = some y ∧ y.active = true ∧ m.le y.mode ∧
      (y.holder = .frame s.top ∨ ∃ p, y.holder = .place p ∧ s.Usable p ∧ HasRight s m p) := by
  obtain ⟨y, hy, ya, hm, hh⟩ := exercise_requires_hold h
  refine ⟨y, hy, ya, hm, hh.imp id fun ⟨p, hp, hr⟩ => ⟨p, hp, ?_, hr⟩⟩
  have := hwf.poss a y hy ya; rw [hp] at this; exact this

/-! ## Static storage (D1) -/

/-- Static storage (D1): each element is a local of `enterFrame` (parent, owning element, kind;
C6) with a flag, the initial state of the element when it is a leaf: `true` for a global with an
initialiser (`Init`), `false` otherwise (`Uninit`). The flag of an element that has parts is not
read: its leaves carry their own (MM-03.3.3: a composite may be partly initialised). -/
abbrev Statics := List ((Option Nat × Option Nat × Nat) × Bool)

/-- Initial state (MM-03.3.1; D1) with the static storage `statics`: the base frame 0, which never
exits (O7), and the elements of `statics` laid out as the locals of `enterFrame` (`shapeP`), owned
by frame 0 or by an earlier static. One root authority `Modify` per root element, on its
footprint, held by the owner of the element (A4): frame 0 for a static it owns. Leaves `Init` or
`Uninit` as declared; no anchor; alive, not freed, not pinned. -/
def S3.init (statics : Statics) : S3 :=
  { F := [0]
    nF := 1
    P := shapeP [] (.frame 0) (statics.map (·.1))
    I := fun l => if ((statics[l]?).map (·.2)).getD false then .init else .uninit
    A := (rootIdx (statics.map (·.1))).map fun i =>
      ⟨.modify, none, footprint (shapeP [] (.frame 0) (statics.map (·.1))) i,
        shapeOwner (statics.map (·.1)) (.frame 0) i, true⟩
    D := fun _ => []
    dead := fun _ => false
    freed := fun _ => false
    pin := fun _ => false
    arenas := []
    callParams := fun _ => [] }

section Init
variable {statics : Statics}

theorem init_len (statics : Statics) : (S3.init statics).P.length = statics.length := by
  simp [S3.init, shapeP_len]

theorem init_P_new {i : Nat} (hi : i < statics.length) : (S3.init statics).P[i]? =
    some ⟨((statics.map (·.1))[i]?).bind (·.1), shapeOwner (statics.map (·.1)) (.frame 0) i,
      (((statics.map (·.1))[i]?).map (·.2.2)).getD 0⟩ := by
  have := shapeP_new (P := []) (hd := .frame 0) (ls := statics.map (·.1)) (i := i) (by simpa using hi)
  rw [List.length_nil, Nat.zero_add] at this; exact this

theorem init_P_get {q : Nat} {pl : Place} (h : (S3.init statics).P[q]? = some pl) :
    q < statics.length ∧ pl = ⟨((statics.map (·.1))[q]?).bind (·.1),
      shapeOwner (statics.map (·.1)) (.frame 0) q, (((statics.map (·.1))[q]?).map (·.2.2)).getD 0⟩ := by
  have hq : q < statics.length := by have := lt_of_getElem? h; rwa [init_len] at this
  rw [init_P_new hq] at h; cases h; exact ⟨hq, rfl⟩

theorem init_parentOf {q : Nat} (hq : q < statics.length) :
    parentOf (S3.init statics).P q = ((statics.map (·.1))[q]?).bind (·.1) := by
  simp [parentOf, init_P_new hq]

theorem init_get {j : Nat} {z : Authority} (h : (S3.init statics).A[j]? = some z) :
    ∃ i, (rootIdx (statics.map (·.1)))[j]? = some i ∧
      z = ⟨.modify, none, footprint (S3.init statics).P i,
        shapeOwner (statics.map (·.1)) (.frame 0) i, true⟩ := by
  simp only [S3.init, List.getElem?_map] at h
  cases hi : (rootIdx (statics.map (·.1)))[j]? with
  | none => rw [hi] at h; cases h
  | some i => rw [hi] at h; cases h; exact ⟨i, rfl, rfl⟩

theorem init_fp_lt {i l : Nat} (h : l ∈ footprint (S3.init statics).P i) :
    i < statics.length ∧ l < statics.length := by
  obtain ⟨hl, -, -, hq⟩ := mem_footprint.1 h
  rw [init_len] at hl
  rcases hq with rfl | hq
  · exact ⟨hl, hl⟩
  · exact ⟨Nat.lt_trans (chain_lt hq) hl, hl⟩

/-- The static places are usable in the initial state (A5; D1): their owners lead to frame 0. -/
theorem init_usable (hsh : ShapeOK 0 (statics.map (·.1))) :
    ∀ n i, i < n → i < statics.length → (S3.init statics).Usable i
  | 0, _, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, i, _, hi => by
    have hpl := init_P_new hi
    have hd : (S3.init statics).dead i = false := rfl
    unfold shapeOwner at hpl
    cases ho : ((statics.map (·.1))[i]?).bind (·.2.1) with
    | none =>
      rw [ho] at hpl
      exact .frame hpl hd rfl (List.mem_singleton_self _)
    | some o =>
      rw [ho] at hpl
      have h2 := (hsh i (List.mem_range.2 (by simpa using hi))).2
      rw [ho] at h2; simp only [OptP] at h2
      exact .place hpl hd rfl (init_usable hsh n o (by omega) (by omega))

end Init

/-- `init_wf` (MM-03.3 §2, §10; A1; D1): for every well-formed static storage, the initial state
satisfies `WF3` and `Inv3`. -/
theorem init_wf (statics : Statics) (hsh : ShapeOK 0 (statics.map (·.1))) :
    WF3 (S3.init statics) ∧ Inv3 (S3.init statics) := by
  have nodup : (rootIdx (statics.map (·.1))).Nodup :=
    ((pairwise_lt_range _).sublist List.filter_sublist).imp Nat.ne_of_lt
  have hlen : (statics.map (·.1)).length = statics.length := by simp
  refine ⟨⟨?_, ?_, by simp [S3.init], by simp [S3.init], by simp [S3.init], ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, fun q _ x hx => by simp [S3.init] at hx, i4_always _⟩,
    fun q _ x hx => by simp [S3.init] at hx, ?_⟩
  · intro b y a hb ho
    obtain ⟨i, -, rfl⟩ := init_get hb; cases ho
  · intro a y hy l hl
    obtain ⟨i, -, rfl⟩ := init_get hy
    rw [init_len]; exact (init_fp_lt hl).2
  · intro q pl f hq ho
    obtain ⟨-, rfl⟩ := init_P_get hq
    simp only [shapeOwner] at ho; split at ho
    · cases ho
    · cases ho; exact Nat.zero_lt_one
  · intro q pl o hq ho
    obtain ⟨hql, rfl⟩ := init_P_get hq
    rw [init_len]
    simp only [shapeOwner] at ho; split at ho
    · rename_i o' ho'; cases ho
      have h2 := (hsh q (List.mem_range.2 (by rw [hlen]; exact hql))).2
      rw [ho'] at h2; exact Nat.lt_of_lt_of_le h2.2 (by omega)
    · cases ho
  · intro q pl r hq hp
    obtain ⟨hql, rfl⟩ := init_P_get hq
    have h1 := (hsh q (List.mem_range.2 (by rw [hlen]; exact hql))).1
    simp only at hp; rw [hp] at h1; obtain ⟨-, hr₂, hown⟩ := h1
    refine ⟨_, init_P_new (by omega), by omega, ?_, rfl⟩
    simp only [shapeOwner, hown, Nat.sub_zero]
  · intro a y hy ya
    obtain ⟨i, hi, rfl⟩ := init_get hy
    have hil : i < statics.length := by rw [← hlen]; exact (rootIdx_mem hi).1
    show HolderLive _ (shapeOwner (statics.map (·.1)) (.frame 0) i)
    unfold shapeOwner
    cases ho : ((statics.map (·.1))[i]?).bind (·.2.1) with
    | none => exact List.mem_singleton_self _
    | some o =>
      have h2 := (hsh i (List.mem_range.2 (by rw [hlen]; exact hil))).2
      rw [ho] at h2; simp only [OptP] at h2
      exact init_usable hsh (o + 1) o (Nat.lt_succ_self _) (by omega)
  · intro a y l ha hl hleaf
    obtain ⟨i, hi, rfl⟩ := init_get ha
    obtain ⟨hil, hin⟩ := rootIdx_mem hi
    refine ⟨a, _, i, .inl rfl, ha, rfl, ⟨?_, ?_⟩, (mem_footprint.1 hl).2.2, fun _ => Iff.rfl⟩
    · rw [init_len, ← hlen]; exact hil
    · rw [init_parentOf (by rw [← hlen]; exact hil)]; exact hin
  · intro x z l r hx ho hl hrp hlr
    obtain ⟨i, hi, rfl⟩ := init_get hx
    obtain ⟨hil, hin⟩ := rootIdx_mem hi
    have hil' : i < statics.length := by rw [← hlen]; exact hil
    have hroot : RootPlace (S3.init statics).P i :=
      ⟨by rw [init_len]; exact hil', by rw [init_parentOf hil']; exact hin⟩
    obtain rfl := rootOf_unique hrp hroot hlr (mem_footprint.1 hl).2.2
    exact ⟨_, init_P_new hil', rfl⟩
  · intro a b x y p hab ha hb _ _ xp yp _ _
    obtain ⟨i, hi, rfl⟩ := init_get ha
    obtain ⟨i', hi', rfl⟩ := init_get hb
    have hii : i ≠ i' := fun e => hab ((nodup.getElem?_inj (lt_of_getElem? hi)).1 (by
      rw [hi, hi', e]))
    exact (shape_roots_disjoint (P := []) (hd := .frame 0) hii (rootIdx_mem hi).2
      (rootIdx_mem hi').2 (by rw [List.length_nil, Nat.zero_add]; exact xp)
      (by rw [List.length_nil, Nat.zero_add]; exact yp)).elim
  · intro b y a hb ho
    obtain ⟨i, -, rfl⟩ := init_get hb; cases ho
  · intro j y hy _ q hq l hl _
    obtain ⟨hql, -⟩ := init_fp_lt hl
    exact hq (init_usable hsh (q + 1) q (Nat.lt_succ_self _) hql)

/-! ## Re-anchoring keeps modes and footprints (D4) -/

/-- `exitG_keeps_modes_footprints` (D4; A7; O7): at the exit, a surviving authority is re-anchored,
which changes only its origin; an authority that does not survive is released, which changes only
its activity. Neither changes a mode, a footprint or a holder. Besides the authorities, the exit
changes only the anchors (`D`) and the stack (`F`) (`exitEff`). -/
theorem exitG_keeps_modes_footprints (s : S3) (F₀ : Frames) (a : Nat) (y : Authority) :
    (Survives s F₀ a → ∃ o : Option Nat, exitG s F₀ a y = { y with origin := o }) ∧
      (¬ Survives s F₀ a → exitG s F₀ a y = { y with active := false }) := by
  unfold exitG
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  simp only [h, ↓reduceIte]
  split
  · exact ⟨y.origin, rfl⟩
  · exact ⟨_, rfl⟩

/-- An active `Modify` authority takes the effective right on each of its leaves away from all its
ancestors (MM-03.3.5): their effective mode there is absent. -/
theorem effective_none_of_desc_modify {s : S3} {j z l : Nat} {y : Authority}
    (hy : s.A[j]? = some y) (ya : y.active = true) (hl : l ∈ y.footprint)
    (hm : y.mode = .modify) (hz : z ∈ s.ancs j) : effective s z l = none := by
  have hd : Mode.modify ∈ descModes s z l := mem_descModes.2 ⟨j, y, hy, ya, hl, hz, hm⟩
  unfold effective
  split
  · split
    · unfold effOf
      have hne : descModes s z l ≠ [] := fun e => by rw [e] at hd; cases hd
      simp [hne, hd]
    · rfl
  · rfl

/-- D4: after the exit, the restrictions of a surviving `Modify` authority still bind its
surviving ancestors through I1: it keeps its mode and footprint (`exitG_keeps_modes_footprints`),
they stay its ancestors (A7), and their effective mode on its leaves stays absent. -/
theorem exit_keeps_restrictions {k : K} {s s' : S3} {f : Nat} {F₀ : Frames} (hF : s.F = f :: F₀)
    (h : ExitStep k s (.ok s')) {j z l : Nat} {y : Authority} (hy : s.A[j]? = some y)
    (hm : y.mode = .modify) (hl : l ∈ y.footprint) (hsj : Survives s F₀ j) (hz : z ∈ s.ancs j)
    (hsz : Survives s F₀ z) : effective s' z l = none := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
  have hy' : (exitEff s).A[j]? = some (exitG s F₀ j y) := by rw [exit_A_get hF, hy]; rfl
  exact effective_none_of_desc_modify hy' (exitG_surv hy hsj)
    (by rw [(exitG_same s F₀ j y).2.1]; exact hl) (by rw [(exitG_same s F₀ j y).1]; exact hm)
    (exit_ancs_keep hF (j + 1) j (Nat.lt_succ_self j) z hz hsz)

/-! ## Closure of the exit (MM-03.3 §4, O7; A4; B1) -/

theorem WF3.ownerOf_aux {s : S3} (hw : WF3 s) :
    ∀ n l r, l < n → partOf s.P l r →
      ∃ pl pr, s.P[l]? = some pl ∧ s.P[r]? = some pr ∧ pl.owner = pr.owner
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, l, r, hl, ⟨hlen, hlr⟩ => by
    obtain ⟨pl, hpl⟩ : ∃ pl, s.P[l]? = some pl := ⟨_, List.getElem?_eq_some_iff.2 ⟨hlen, rfl⟩⟩
    rcases hlr with rfl | hc
    · exact ⟨pl, pl, hpl, hpl, rfl⟩
    cases hpo : parentOf s.P l with
    | none => rw [chain_none hpo] at hc; simp at hc
    | some p =>
      have hpar : pl.parent = some p := by simp [parentOf, hpl] at hpo; exact hpo
      obtain ⟨pr, hpr, hlt, ho, -⟩ := hw.parts l pl p hpl hpar
      rw [chain_cons hpo hlt] at hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact ⟨pl, pr, hpl, hpr, ho.symm⟩
      · obtain ⟨pl', pr', hpl', hpr', he⟩ :=
          WF3.ownerOf_aux hw n p r (by omega) ⟨lt_of_getElem? hpr, .inr hc⟩
        rw [hpr] at hpl'; cases hpl'
        exact ⟨pl, pr', hpl, hpr', ho.symm.trans he⟩

/-- A part has the owner of the place it belongs to (A5, `WF3`). -/
theorem WF3.ownerOf {s : S3} (hw : WF3 s) {l r : Nat} (h : partOf s.P l r) :
    ∃ pl pr, s.P[l]? = some pl ∧ s.P[r]? = some pr ∧ pl.owner = pr.owner :=
  hw.ownerOf_aux (l + 1) l r (Nat.lt_succ_self l) h

/-- Under `ExitPre` (MM-03.3 §4, O7; A7), the root of the chain of a surviving authority
survives. -/
theorem exit_root_survives {s : S3} {F₀ : Frames}
    (h3 : ∀ a ∈ List.range s.A.length, Survives s F₀ a → s.org a ≠ none →
      firstSurv s F₀ (s.ancs a) ≠ none) :
    ∀ n a, a < n → Survives s F₀ a → ∀ x0, (x0 = a ∨ x0 ∈ s.ancs a) → s.org x0 = none →
      Survives s F₀ x0
  | 0, _, h, _, _, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, a, ha, hs, x0, hx0, hx0o => by
    rcases hx0 with rfl | hx0
    · exact hs
    have hA : a < s.A.length := by
      unfold Survives OptP at hs; split at hs
      · exact lt_of_getElem? ‹_›
      · exact hs.elim
    have horg : s.org a ≠ none := fun e => by rw [S3.ancs, chain_none e] at hx0; simp at hx0
    cases hz : firstSurv s F₀ (s.ancs a) with
    | none => exact absurd hz (h3 a (List.mem_range.2 hA) hs horg)
    | some z =>
      obtain ⟨hz1, hzs⟩ := firstSurv_some hz
      rcases ancs_root_after (a + 1) a (Nat.lt_succ_self a) z x0 hz1 hx0 hx0o with rfl | hx'
      · exact hzs
      · exact exit_root_survives h3 n z (by have := chain_lt hz1; omega) hzs x0 (.inr hx') hx0o

/-- A place that belongs to the exited frame through ownership is not usable once the frame is
popped (MM-03.3.1; A5). -/
theorem ownedByFrame_not_usable {s : S3} {f : Nat} {F₀ : Frames} (hnd : f ∉ F₀) {q : Nat}
    (h : OwnedByFrame s.P f q) : ¬ ({ s with F := F₀ } : S3).Usable q := by
  induction h with
  | @frame q pl hpl ho =>
    intro hu
    cases hu with
    | frame hpl' _ ho' hf => rw [hpl] at hpl'; cases hpl'; rw [ho] at ho'; cases ho'; exact hnd hf
    | place hpl' _ ho' _ => rw [hpl] at hpl'; cases hpl'; rw [ho] at ho'; cases ho'
  | @place q o pl hpl ho _ ih =>
    intro hu
    cases hu with
    | frame hpl' _ ho' _ => rw [hpl] at hpl'; cases hpl'; rw [ho] at ho'; cases ho'
    | place hpl' _ ho' hU => rw [hpl] at hpl'; cases hpl'; rw [ho] at ho'; cases ho'; exact ih hU

theorem OwnedByFrame.of_owner {P : List Place} {f q l : Nat} {pq pl : Place}
    (h : OwnedByFrame P f q) (hq : P[q]? = some pq) (hl : P[l]? = some pl)
    (ho : pl.owner = pq.owner) : OwnedByFrame P f l := by
  cases h with
  | frame h1 h2 => rw [hq] at h1; cases h1; exact .frame hl (ho.trans h2)
  | place h1 h2 h3 => rw [hq] at h1; cases h1; exact .place hl (ho.trans h2) h3

/-- `exitFrame_no_dangling` (MM-03.3 §4, O7; MM-03.3.1; A4; A5; A7; B1), the closure theorem of the
milestone: after the exit, no active authority covers a leaf of a place of the exited frame, its
locals and the storage they own transitively, whatever authorities transfers and re-anchorings
kept. The chain of origins of an active authority ends at the root authority of the root place of
the leaf (`RootChain`), which survives by `ExitPre`; that root is held by the owner of its place
(`RootHeld`, A4), which belongs to the exited frame and does not survive. Stated under `WF3`
alone: `Inv3` is not used. -/
theorem exitFrame_no_dangling {k : K} {s s' : S3} {f : Nat} {F₀ : Frames} (hwf : WF3 s)
    (hF : s.F = f :: F₀) (h : ExitStep k s (.ok s')) :
    ∀ q, OwnedByFrame s.P f q → ∀ (j : Nat) (y : Authority), s'.A[j]? = some y →
      y.active = true → ∀ l ∈ footprint s.P q, l ∉ y.footprint := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  unfold ExitPre at hpre; rw [hF] at hpre
  obtain ⟨-, -, h3, -⟩ := hpre
  have hnd := (List.nodup_cons.1 (hF ▸ hwf.nodup)).1
  intro q hq j y hy ya l hl hly
  rw [exit_A_get hF] at hy
  obtain ⟨y₀, hy₀, rfl⟩ := Option.map_eq_some_iff.1 hy
  have hs := exitG_active ya
  rw [(exitG_same s F₀ j y₀).2.1] at hly
  obtain ⟨hlP, hleaf, hlq⟩ := mem_footprint.1 hl
  obtain ⟨x0, z, r, hx0, hz, hzo, hr, hlr, hfz⟩ := hwf.rootChain j y₀ l hy₀ hly hleaf
  have hx0o : s.org x0 = none := by simp [S3.org, hz, hzo]
  have hs0 := exit_root_survives h3 (j + 1) j (Nat.lt_succ_self j) hs x0 hx0 hx0o
  have hlz : l ∈ z.footprint := (hfz l).2 (mem_footprint.2 ⟨hlP, hleaf, hlr⟩)
  obtain ⟨pr, hpr, hh⟩ := hwf.rootHeld x0 z l r hz hzo hlz hr hlr
  unfold Survives at hs0; rw [hz] at hs0
  obtain ⟨-, hlive⟩ := hs0
  rw [hh] at hlive
  obtain ⟨pl, pr', hpl, hpr', e1⟩ := hwf.ownerOf hlr
  rw [hpr] at hpr'; cases hpr'
  obtain ⟨pl', pq, hpl', hpq, e2⟩ := hwf.ownerOf hlq
  rw [hpl] at hpl'; cases hpl'
  have hol : OwnedByFrame s.P f r := hq.of_owner hpq hpr (e1.symm.trans e2)
  cases hol with
  | frame h1 h2 => rw [hpr] at h1; cases h1; rw [h2] at hlive; exact hnd hlive
  | place h1 h2 h3' =>
    rw [hpr] at h1; cases h1; rw [h2] at hlive; exact ownedByFrame_not_usable hnd h3' hlive

/-! ## Preservation of `NoDangling` (C2) -/

theorem S3.Usable.dead_false {s : S3} {q : Nat} (h : s.Usable q) : s.dead q = false := by
  cases h <;> assumption

/-- A place that exists, is not dead and has a live owner is usable (A5). -/
theorem S3.Usable.of_owner {s : S3} {q : Nat} {pl : Place} (hpl : s.P[q]? = some pl)
    (hd : s.dead q = false) (h : HolderLive s pl.owner) : s.Usable q := by
  cases ho : pl.owner with
  | frame f => rw [ho] at h; exact .frame hpl hd ho h
  | place o => rw [ho] at h; exact .place hpl hd ho h

theorem WF3.deadOf_aux {s : S3} (hw : WF3 s) :
    ∀ n l r, l < n → partOf s.P l r → s.dead l = s.dead r
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, l, r, hl, ⟨hlen, hlr⟩ => by
    rcases hlr with rfl | hc
    · rfl
    cases hpo : parentOf s.P l with
    | none => rw [chain_none hpo] at hc; simp at hc
    | some p =>
      obtain ⟨pl, hpl⟩ : ∃ pl, s.P[l]? = some pl := ⟨_, List.getElem?_eq_some_iff.2 ⟨hlen, rfl⟩⟩
      have hpar : pl.parent = some p := by simp [parentOf, hpl] at hpo; exact hpo
      obtain ⟨pr, hpr, hlt, -, hd⟩ := hw.parts l pl p hpl hpar
      rw [chain_cons hpo hlt] at hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact hd.symm
      · exact hd.symm.trans (WF3.deadOf_aux hw n p r (by omega) ⟨lt_of_getElem? hpr, .inr hc⟩)

/-- A part has the `dead` flag of the place it belongs to (A5, `WF3`). -/
theorem WF3.deadOf {s : S3} (hw : WF3 s) {l r : Nat} (h : partOf s.P l r) : s.dead l = s.dead r :=
  hw.deadOf_aux (l + 1) l r (Nat.lt_succ_self l) h

/-- A place with a usable part is usable (A5, `WF3`). -/
theorem usable_of_part {s : S3} (hw : WF3 s) {l r : Nat} (h : partOf s.P l r) (hu : s.Usable l) :
    s.Usable r := by
  obtain ⟨pl, pr, hpl, hpr, ho⟩ := hw.ownerOf h
  exact hu.of_same hpl hpr ho.symm (hw.deadOf h).symm

/-- `NoDangling` carries over when no footprint grows, no usable place stops being usable, and
every active authority covers only leaves of an active authority of the previous state (C2). -/
theorem NoDangling.of {s s' : S3} (hnd : NoDangling s)
    (hfp : ∀ q l, l ∈ footprint s'.P q → l ∈ footprint s.P q)
    (hu : ∀ q, s.Usable q → s'.Usable q)
    (hA : ∀ (j : Nat) (z : Authority), s'.A[j]? = some z → z.active = true → ∀ l ∈ z.footprint,
      ∃ (i : Nat) (y : Authority), s.A[i]? = some y ∧ y.active = true ∧ l ∈ y.footprint) :
    NoDangling s' := by
  intro j z hz za q hq l hl hlz
  obtain ⟨i, y, hy, ya, hly⟩ := hA j z hz za l hlz
  exact hnd i y hy ya q (fun h => hq (hu q h)) l (hfp q l hl) hly

/-- `derive` preserves `NoDangling` (C2; MM-03.3 §3, O1): the derived footprint is within the
footprint of the active origin. -/
theorem derive_preserves_noDangling {s s' : S3} {src q : Nat} {m : Mode} (hnd : NoDangling s)
    (h : DeriveStep src q m s (.ok s')) : NoDangling s' := by
  obtain ⟨⟨⟨x, hx, xa⟩, -, -, hsub, -⟩, rfl⟩ := Guarded.ok_iff.1 h
  refine hnd.of (fun _ _ h => h) (fun _ h => h.of_eqs rfl rfl rfl) fun j z hz za => ?_
  rcases addAuth_get hz with ⟨-, hy⟩ | ⟨-, rfl⟩
  · exact fun l hl => ⟨j, z, hy, za, hl⟩
  · exact fun l hl => ⟨src, x, hx, xa, by have := hsub l hl; simp only [S3.afp, hx] at this; exact this⟩

/-- `split` preserves `NoDangling` (C2; MM-03.3 §3, O2): each region is within the footprint of
the active origin. -/
theorem split_preserves_noDangling {k : K} {s s' : S3} {src : Nat} {rs : List (List Nat)}
    (hnd : NoDangling s) (h : SplitStep k src rs s (.ok s')) : NoDangling s' := by
  obtain ⟨⟨⟨x, hx, xa⟩, -, -, hreg, -⟩, rfl⟩ := Guarded.ok_iff.1 h
  refine hnd.of (fun _ _ h => h) (fun _ h => h.of_eqs rfl rfl rfl) fun j z hz za => ?_
  simp only [splitEff] at hz
  by_cases hj : j < s.A.length
  · rw [List.getElem?_append_left hj] at hz; exact fun l hl => ⟨j, z, hz, za, hl⟩
  · rw [List.getElem?_append_right (by omega), List.getElem?_map] at hz
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 hz
    intro l hl
    have := (hreg r (List.mem_of_getElem? hr) l hl).1; simp only [S3.afp, hx] at this
    exact ⟨src, x, hx, xa, this⟩

/-- `release` preserves `NoDangling` (C2; MM-03.3 §3, O3): it activates nothing. -/
theorem release_preserves_noDangling {s s' : S3} {a : Nat} (hnd : NoDangling s)
    (h : ReleaseStep a s (.ok s')) : NoDangling s' := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
  have hP : (releaseEff s a).P = s.P := by unfold releaseEff; split <;> rfl
  have hF : (releaseEff s a).F = s.F := by unfold releaseEff; split <;> rfl
  have hd : (releaseEff s a).dead = s.dead := by unfold releaseEff; split <;> rfl
  refine hnd.of (fun _ _ h => by rw [hP] at h; exact h)
    (fun _ h => (S3.Usable.congr hP hF hd).2 h) fun j z hz za => ?_
  obtain ⟨y, hy, -, -, e, -, ea⟩ := (release_releases s a).2 j z hz
  exact fun l hl => ⟨j, y, hy, ea za, e ▸ hl⟩

/-- `depend` preserves `NoDangling` (C2; MM-03.3 §3, O5): it changes no authority. -/
theorem depend_preserves_noDangling {s s' : S3} {q x : Nat} (hnd : NoDangling s)
    (h : DependStep q x s (.ok s')) : NoDangling s' := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
  exact hnd.of (fun _ _ h => h) (fun _ h => h.of_eqs rfl rfl rfl)
    fun j z hz za _ hl => ⟨j, z, hz, za, hl⟩

/-- `write3`, `writeShared`, `pin` and `unpin` preserve `NoDangling` (C2): they change neither
places, stack, `dead` flags nor authorities. -/
theorem write3_preserves_noDangling {s : S3} (ls : List Nat) (hnd : NoDangling s) :
    NoDangling (write3Eff s ls) :=
  hnd.of (fun _ _ h => h) (fun _ h => h.of_eqs rfl rfl rfl)
    fun j z hz za _ hl => ⟨j, z, hz, za, hl⟩

/-- `pin` and `unpin` preserve `NoDangling` (C2; A8): they only set the pin state. -/
theorem pinEff_preserves_noDangling {s : S3} (p : Nat) (b : Bool) (hnd : NoDangling s) :
    NoDangling (pinEff s p b) :=
  hnd.of (fun _ _ h => h) (fun _ h => h.of_eqs rfl rfl rfl)
    fun j z hz za _ hl => ⟨j, z, hz, za, hl⟩

/-- `transfer` preserves `NoDangling` (C2; MM-03.3 §3, O4): footprints are unchanged, every usable
place stays usable, and authorities only change holder. -/
theorem transfer_preserves_noDangling {k : K} {s s' : S3} {src dst : Nat} (hnd : NoDangling s)
    (h : TransferStep k src dst s (.ok s')) : NoDangling s' := by
  obtain ⟨⟨-, -, -, -, -, -, -, hd', -, -, -, -, -⟩, rfl⟩ := Guarded.ok_iff.1 h
  refine hnd.of (fun q l h => by rw [transfer_footprint] at h; exact h)
    (fun _ h => transfer_usable_fwd hd' h) fun j z hz za => ?_
  rw [transfer_A_get] at hz
  obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hz
  exact fun l hl => ⟨j, y, hy, by split at za <;> exact za, by split at hl <;> exact hl⟩

/-- `enterFrame` preserves `NoDangling` (C2; MM-03.3 §4, O6), under `WF3`: old places keep their
footprints and their usability; a new root authority covers only new locals, which are usable. -/
theorem enter_preserves_noDangling {s s' : S3} {ps : List Nat}
    {ls : List (Option Nat × Option Nat × Nat)} (hwf : WF3 s) (hnd : NoDangling s)
    (h : EnterStep ps ls s (.ok s')) : NoDangling s' := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  intro j z hz za q hq l hl hlz
  obtain ⟨hlP, -, hlq⟩ := mem_footprint.1 hl
  have hql : q ≤ l := by
    rcases hlq.2 with rfl | hc
    · exact Nat.le_refl _
    · exact Nat.le_of_lt (chain_lt hc)
  rcases enter_get hz with ⟨-, y, hy, rfl⟩ | ⟨-, i, -, rfl⟩
  · have hly : l ∈ y.footprint := by split at hlz <;> exact hlz
    have ya : y.active = true := by split at za <;> exact za
    have hqo : q < s.P.length := Nat.lt_of_le_of_lt hql (hwf.fp j y hy l hly)
    exact hnd j y hy ya q (fun hu => hq (enter_usable_old hu)) l
      ((enter_footprint_old hpre hqo l).1 hl) hly
  · have hge : s.P.length ≤ l := enter_root_fp_ge hlz
    by_cases hqo : q < s.P.length
    · have := (mem_footprint.1 ((enter_footprint_old hpre hqo l).1 hl)).1; omega
    · have hlP' : l < (enterP s ls).length := hlP
      rw [enterP_len] at hlP'
      have hu := enter_usable_new (ps := ps) hpre (q - s.P.length + 1) (q - s.P.length)
        (Nat.lt_succ_self _) (by omega)
      rw [show s.P.length + (q - s.P.length) = q by omega] at hu
      exact hq hu

/-- `alloc` preserves `NoDangling` (C2; B5; C6), under `WF3`: old places keep their footprints and
their usability; a new root authority covers only new elements, which are usable. -/
theorem alloc_preserves_noDangling {k : K} {pr ow : Nat}
    {ls : List (Option Nat × Option Nat × Nat)} {s s' : S3} (hwf : WF3 s)
    (hnd : NoDangling s) (h : AllocStep k pr ow ls s (.ok s')) : NoDangling s' := by
  cases h with
  | ok hst _ =>
  intro j z hz za q hq l hl hlz
  obtain ⟨hlP, -, hlq⟩ := mem_footprint.1 hl
  have hql : q ≤ l := by
    rcases hlq.2 with rfl | hc
    · exact Nat.le_refl _
    · exact Nat.le_of_lt (chain_lt hc)
  rcases alloc_get hz with ⟨-, hy⟩ | ⟨-, i, -, rfl⟩
  · have hqo : q < s.P.length := Nat.lt_of_le_of_lt hql (hwf.fp j z hy l hlz)
    exact hnd j z hy za q (fun hu => hq (alloc_usable_old hu)) l
      ((shape_footprint_old hst.2.2.2.2.2.1 hqo l).1 hl) hlz
  · have hge : s.P.length ≤ l := shape_root_fp_ge hlz
    by_cases hqo : q < s.P.length
    · have := (mem_footprint.1 ((shape_footprint_old hst.2.2.2.2.2.1 hqo l).1 hl)).1; omega
    · have hlP' : l < (allocP s ow ls).length := hlP
      rw [allocP_len] at hlP'
      have hu := alloc_usable_new hst (q - s.P.length + 1) (q - s.P.length) (Nat.lt_succ_self _)
        (by omega)
      rw [show s.P.length + (q - s.P.length) = q by omega] at hu
      exact hq hu

/-- A place usable before the exit and not after belongs to the exited frame, directly or through
its owners (MM-03.3.1; A5). -/
theorem exit_owned_of_usable {s : S3} {f : Nat} {F₀ : Frames} (hF : s.F = f :: F₀) {q : Nat}
    (h : s.Usable q) (h' : ¬ ({ s with F := F₀ } : S3).Usable q) : OwnedByFrame s.P f q := by
  induction h with
  | @frame q g pl hpl hd ho hg =>
    rw [hF] at hg
    rcases List.mem_cons.1 hg with rfl | hg
    · exact .frame hpl ho
    · exact absurd (S3.Usable.frame (s := { s with F := F₀ }) hpl hd ho hg) h'
  | @place q o pl hpl hd ho _ ih =>
    exact .place hpl ho (ih fun hu => h' (S3.Usable.place (s := { s with F := F₀ }) hpl hd ho hu))

/-- `exitFrame` preserves `NoDangling` (C2; MM-03.3 §4, O7), under `WF3`: a place that stops being
usable belongs to the exited frame, and `exitFrame_no_dangling` applies to it. -/
theorem exit_preserves_noDangling {k : K} {s s' : S3} (hwf : WF3 s) (hnd : NoDangling s)
    (h : ExitStep k s (.ok s')) : NoDangling s' := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  cases hF : s.F with
  | nil => unfold ExitPre at hpre; rw [hF] at hpre; exact hpre.elim
  | cons f F₀ =>
  have e := exitEff_eq hF
  intro j z hz za q hq l hl hlz
  rw [show (exitEff s).P = s.P by rw [e]] at hl
  have hz' := hz
  rw [exit_A_get hF] at hz'
  obtain ⟨y₀, hy₀, rfl⟩ := Option.map_eq_some_iff.1 hz'
  by_cases hq₀ : s.Usable q
  · have hq₁ : ¬ ({ s with F := F₀ } : S3).Usable q := fun hu =>
      hq ((S3.Usable.congr (s := ({ s with F := F₀ } : S3)) (by rw [e]) (by rw [e])
        (by rw [e])).2 hu)
    exact exitFrame_no_dangling hwf hF h q (exit_owned_of_usable hF hq₀ hq₁) j _ hz za l hl hlz
  · rw [(exitG_same s F₀ j y₀).2.1] at hlz
    exact hnd j y₀ hy₀ (exitG_active' hy₀ za) q hq₀ l hl hlz

/-- `StaticPinnedBottom k s` (C5, F3), obligation on the static pinning `K.Pinned`: every leaf
covered by `K.Pinned` belongs to a place owned directly by the base frame, the last of the stack
(frame 0 on reached states, `reachable_base_owns_statics`). F3 replaces the transitive ownership
of C5 by direct ownership. Dynamic pinning (`pin`, `unpin`) is not concerned. -/
def StaticPinnedBottom (k : K) (s : S3) : Prop :=
  ∀ l, k.Pinned l → ∃ (q : Nat) (pl : Place), l ∈ footprint s.P q ∧ s.P[q]? = some pl ∧
    pl.owner = .frame (s.F.getLastD 0)

/-- A place has at most one owning frame (A5). -/
theorem OwnedByFrame.unique {P : List Place} {f g q : Nat} (h : OwnedByFrame P f q)
    (h' : OwnedByFrame P g q) : f = g := by
  induction h with
  | @frame q pl hpl ho =>
    cases h' with
    | frame hpl' ho' => rw [hpl] at hpl'; cases hpl'; rw [ho] at ho'; cases ho'; rfl
    | place hpl' ho' _ => rw [hpl] at hpl'; cases hpl'; rw [ho] at ho'; cases ho'
  | @place q o pl hpl ho _ ih =>
    cases h' with
    | frame hpl' ho' => rw [hpl] at hpl'; cases hpl'; rw [ho] at ho'; cases ho'
    | place hpl' ho' h'' => rw [hpl] at hpl'; cases hpl'; rw [ho] at ho'; cases ho'; exact ih h''

/-- `static_pinned_never_exits` (C5; F3): under `StaticPinnedBottom`, no frame exit meets a
statically pinned leaf: a place that stops being usable at the exit covers no leaf of
`K.Pinned`. -/
theorem static_pinned_never_exits {k : K} {s : S3} {f : Nat} {F₀ : Frames} (hwf : WF3 s)
    (hsp : StaticPinnedBottom k s) (hF : s.F = f :: F₀) (hne : F₀ ≠ []) :
    ∀ q, s.Usable q → ¬ ({ s with F := F₀ } : S3).Usable q →
      ∀ l ∈ footprint s.P q, ¬ k.Pinned l := by
  intro q hq hq' l hl hpin
  have hof := exit_owned_of_usable hF hq hq'
  obtain ⟨q', pl₀, hl', hq₀, ho₀⟩ := hsp l hpin
  have hob : OwnedByFrame s.P (s.F.getLastD 0) q' := .frame hq₀ ho₀
  obtain ⟨-, -, hlq⟩ := mem_footprint.1 hl
  obtain ⟨-, -, hlq'⟩ := mem_footprint.1 hl'
  obtain ⟨pl, pq, hpl, hpq, e⟩ := hwf.ownerOf hlq
  obtain ⟨pl', pq', hpl', hpq', e'⟩ := hwf.ownerOf hlq'
  rw [hpl] at hpl'; cases hpl'
  have hfb := (hof.of_owner hpq hpl e).unique (hob.of_owner hpq' hpl e')
  obtain ⟨g, F₁, rfl⟩ : ∃ g F₁, F₀ = g :: F₁ := by
    cases F₀ with
    | nil => exact absurd rfl hne
    | cons g F₁ => exact ⟨g, F₁, rfl⟩
  rw [hF, List.getLastD_cons, List.getLastD_cons] at hfb
  have hnd := (List.nodup_cons.1 (hF ▸ hwf.nodup)).1
  exact hnd (by rw [hfb]; exact List.getLastD_mem_cons)

/-- An active authority after `endUse p` (A6): active before, not held within `p`, with a holder
live after `endUseS`. -/
theorem endUse_active {s : S3} {p j : Nat} {z : Authority}
    (hz : (endUseEff s p).A[j]? = some z) (za : z.active = true) :
    s.A[j]? = some z ∧ ¬ heldIn s.P p z.holder ∧ HolderLive (endUseS s p) z.holder := by
  rw [endUseEff, cleanup_get, endUseS_get] at hz
  cases hy : s.A[j]? with
  | none => rw [hy] at hz; cases hz
  | some y =>
    rw [hy] at hz; simp only [Option.map_some, Option.some.injEq] at hz
    by_cases hh : heldIn s.P p y.holder
    · simp only [hh, ↓reduceIte] at hz; subst hz; split at za <;> simp at za
    · simp only [hh, ↓reduceIte] at hz
      split at hz
      · rename_i hl; subst hz; exact ⟨rfl, hh, hl⟩
      · subst hz; simp at za

/-- `endUse` preserves `NoDangling` (C2; A6), under `WF3`: an active authority on a leaf of a place
that stops being usable is derived, and released by `EndUseAccessOK`, or a root, held by the owner
of its root place (`RootChain`, `RootHeld`), which stops being usable too. -/
theorem endUse_preserves_noDangling {k : K} {s s' : S3} {p : Nat} (hwf : WF3 s)
    (hinv : Inv3base s) (hnd : NoDangling s) (h : EndUseStep k p s (.ok s')) : NoDangling s' := by
  have hw' := (endUse_preserves hwf hinv h).1
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  have hU : ∀ r, (endUseEff s p).Usable r ↔ (endUseS s p).Usable r :=
    fun r => S3.Usable.congr (s := endUseS s p) (s' := endUseEff s p) rfl rfl rfl
  intro j z hz za q hq l hl hlz
  obtain ⟨hz₀, hnh, hlive⟩ := endUse_active hz za
  by_cases hq₀ : ¬ s.Usable q
  · exact hnd j z hz₀ za q hq₀ l hl hlz
  replace hq₀ := Decidable.of_not_not hq₀
  obtain ⟨-, hleaf, hlq⟩ := mem_footprint.1 hl
  have hl₀ : s.Usable l := usable_of_partOf hwf (l + 1) l q (Nat.lt_succ_self l) hlq hq₀
  have hl₁ : ¬ (endUseS s p).Usable l := fun hu => hq (usable_of_part hw' hlq ((hU l).2 hu))
  cases hzo : z.origin with
  | some o =>
    have hacc := hpre.2.2.1 j (List.mem_range.2 (lt_of_getElem? hz₀))
    unfold EndUseAccessOK OptP at hacc; rw [hz₀] at hacc
    rcases hacc za (by rw [hzo]; simp) (.inl ⟨l, hlz, .inr ⟨hl₀, hl₁⟩⟩) with e | e
    · exact hnh e
    · exact e hlive
  | none =>
    obtain ⟨-, -, r, -, -, -, hr, hlr, -⟩ := hwf.rootChain j z l hz₀ hlz hleaf
    obtain ⟨pr, hpr, hh⟩ := hwf.rootHeld j z l r hz₀ hzo hlz hr hlr
    have hd : (endUseS s p).dead r = false := by
      simp only [endUseS, hpr, ← hh, (hwf.deadOf hlr).symm, hl₀.dead_false, Bool.false_or,
        decide_eq_false_iff_not]
      exact hnh
    have hr₁ : (endUseS s p).Usable r := S3.Usable.of_owner hpr hd (hh ▸ hlive)
    exact hl₁ ((hU l).1 (usable_of_partOf hw' (l + 1) l r (Nat.lt_succ_self l) hlr ((hU r).2 hr₁)))

/-- An active authority after `free p` (A6): active before, covering no leaf of `p`, not held
within `p`, with a holder live after `freeS`. -/
theorem free_active {s : S3} {p j : Nat} {z : Authority}
    (hz : (freeEff s p).A[j]? = some z) (za : z.active = true) :
    s.A[j]? = some z ∧ ¬ ((∃ l ∈ z.footprint, l ∈ footprint s.P p) ∨ heldIn s.P p z.holder) ∧
      HolderLive (freeS s p) z.holder := by
  rw [freeEff, cleanup_get, freeS_get] at hz
  cases hy : s.A[j]? with
  | none => rw [hy] at hz; cases hz
  | some y =>
    rw [hy] at hz; simp only [Option.map_some, Option.some.injEq] at hz
    by_cases hc : (∃ l ∈ y.footprint, l ∈ footprint s.P p) ∨ heldIn s.P p y.holder
    · simp only [hc, ↓reduceIte] at hz; subst hz; split at za <;> simp at za
    · simp only [hc, ↓reduceIte] at hz
      split at hz
      · rename_i hl; subst hz; exact ⟨rfl, hc, hl⟩
      · subst hz; simp at za

/-- `free` preserves `NoDangling` (C2; A6), under `WF3`: the leaves of `p` are covered by no active
authority (`free_no_dangling`); on a leaf of another place that stops being usable, an active
authority is derived, and released by `FreeAccessOK`, or a root, held by the owner of its root
place (`RootChain`, `RootHeld`), which stops being usable too. -/
theorem free_preserves_noDangling {k : K} {s s' : S3} {p auth : Nat} (hwf : WF3 s)
    (hinv : Inv3base s) (hnd : NoDangling s) (h : FreeStep k p auth s (.ok s')) : NoDangling s' := by
  have hw' := (free_preserves hwf hinv h).1
  have hfd := free_no_dangling hwf hinv h
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  have hU : ∀ r, (freeEff s p).Usable r ↔ (freeS s p).Usable r :=
    fun r => S3.Usable.congr (s := freeS s p) (s' := freeEff s p) rfl rfl rfl
  intro j z hz za q hq l hl hlz
  by_cases hlp : l ∈ footprint s.P p
  · exact (hfd j z hz za).1 l hlz hlp
  obtain ⟨hz₀, hnc, hlive⟩ := free_active hz za
  by_cases hq₀ : ¬ s.Usable q
  · exact hnd j z hz₀ za q hq₀ l hl hlz
  replace hq₀ := Decidable.of_not_not hq₀
  obtain ⟨-, hleaf, hlq⟩ := mem_footprint.1 hl
  have hl₀ : s.Usable l := usable_of_partOf hwf (l + 1) l q (Nat.lt_succ_self l) hlq hq₀
  have hl₁ : ¬ (freeS s p).Usable l := fun hu => hq (usable_of_part hw' hlq ((hU l).2 hu))
  cases hzo : z.origin with
  | some o =>
    have hacc := hpre.2.2.2.2.2.1 j (List.mem_range.2 (lt_of_getElem? hz₀))
    unfold FreeAccessOK OptP at hacc; rw [hz₀] at hacc
    rcases hacc za (by rw [hzo]; simp) (.inl ⟨l, hlz, .inr ⟨hl₀, hl₁⟩⟩) with e | e
    · exact hnc (.inr e)
    · exact e hlive
  | none =>
    obtain ⟨-, -, r, -, -, -, hr, hlr, -⟩ := hwf.rootChain j z l hz₀ hlz hleaf
    obtain ⟨pr, hpr, hh⟩ := hwf.rootHeld j z l r hz₀ hzo hlz hr hlr
    have hrp : ¬ partOf s.P r p := fun hrp => by
      obtain ⟨-, e | hc⟩ := hrp
      · subst e; exact hlp (mem_footprint.2 ⟨(mem_footprint.1 hl).1, hleaf, hlr⟩)
      · rw [chain_none hr.2] at hc; simp at hc
    have hd : (freeS s p).dead r = false := by
      simp only [freeS, (hwf.deadOf hlr).symm, hl₀.dead_false, Bool.false_or,
        decide_eq_false_iff_not]
      exact hrp
    have hr₁ : (freeS s p).Usable r := S3.Usable.of_owner hpr hd (hh ▸ hlive)
    exact hl₁ ((hU l).1 (usable_of_partOf hw' (l + 1) l r (Nat.lt_succ_self l) hlr ((hU r).2 hr₁)))

/-! ## Preservation by `store` (F4) -/

theorem storeEff_eq {s : S3} {a p : Nat} {y : Authority} (hy : s.A[a]? = some y) :
    storeEff s a p = { s with
      A := s.A.set a { y with holder := .place p }
      D := fun q => if q = p then s.D p ++ [a] else s.D q
      I := fun l => if l ∈ footprint s.P p then .init else s.I l } := by
  simp [storeEff, hy]

/-- `store` only changes the holder of `a` among the authorities (F4). -/
theorem store_skel (s : S3) (a p : Nat) : SameSkel s (storeEff s a p) := by
  cases hy : s.A[a]? with
  | none => unfold storeEff; rw [hy]; exact ⟨rfl, fun _ => rfl⟩
  | some y =>
    rw [storeEff_eq hy]
    refine ⟨by simp, fun j => ?_⟩
    show ((s.A.set a { y with holder := .place p })[j]?).map skel = _
    rw [set_get (lt_of_getElem? hy)]; split
    · subst_vars; simp [hy, skel]
    · rfl

theorem store_get {s : S3} {a p : Nat} {y : Authority} (hy : s.A[a]? = some y) (j : Nat) :
    (storeEff s a p).A[j]? = if a = j then some { y with holder := .place p } else s.A[j]? := by
  rw [storeEff_eq hy]; exact set_get (lt_of_getElem? hy)

theorem store_pre_auth {s : S3} {a p : Nat} (h : StorePre s a p) :
    ∃ y, s.A[a]? = some y ∧ y.active = true ∧ y.origin ≠ none ∧ y.holder = .frame s.top := by
  have h1 := h.1; unfold OptP at h1
  split at h1
  · exact ⟨_, ‹_›, h1⟩
  · exact h1.elim

/-- `store` preserves `WF3` and `Inv3base` (F4): it changes the holder of a derived authority to a
usable place, adds an active anchor, and writes leaves. `RootHeld` is untouched: `a` is derived. -/
theorem store_preserves {s s' : S3} {a p : Nat} (hwf : WF3 s) (hinv : Inv3base s)
    (h : StoreStep a p s (.ok s')) : WF3 s' ∧ Inv3base s' := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  obtain ⟨y, hy, ya, ho, -⟩ := store_pre_auth hpre
  have hp := hpre.2.1
  have sk := store_skel s a p
  have e := storeEff_eq (p := p) hy
  have hP : (storeEff s a p).P = s.P := by rw [e]
  have hF : (storeEff s a p).F = s.F := by rw [e]
  have hd : (storeEff s a p).dead = s.dead := by rw [e]
  have hn : (storeEff s a p).nF = s.nF := by rw [e]
  obtain ⟨i1, i2, i3, -⟩ := hinv
  refine ⟨⟨sk.origin hwf.origin, by rw [hP]; exact sk.fp hwf.fp, hF ▸ hwf.ne, hF ▸ hwf.nodup,
    by rw [hF, hn]; exact hwf.frames, by rw [hP, hn]; exact hwf.ownerFrame,
    by rw [hP]; exact hwf.ownerPlace, by rw [hP, hd]; exact hwf.parts, fun j z hz za => ?_,
    sk.rootChain hwf.rootChain (by rw [hP]) (by rw [hP]), ?_⟩, sk.i1 i1, sk.i2 i2,
    fun q hq x hx => ?_, i4_always _⟩
  · rw [store_get hy] at hz; split at hz
    · cases hz; exact (S3.Usable.congr hP hF hd).2 hp
    · rw [HolderLive.congr hP hF hd]; exact hwf.poss j z hz za
  · exact hwf.rootHeld.transport hP fun x z' hx ho' => by
      rw [store_get hy] at hx; split at hx
      · cases hx; exact absurd ho' ho
      · exact ⟨z', hx, ho', rfl, rfl⟩
  · have hq' := (S3.Usable.congr hP hF hd).1 hq
    rw [e] at hx; simp only at hx
    split at hx
    · subst q; rcases List.mem_append.1 hx with hx | hx
      · exact sk.active.2 (i3 _ hq' x hx)
      · rw [List.mem_singleton.1 hx]; exact sk.active.2 ⟨y, hy, ya⟩
    · exact sk.active.2 (i3 q hq' x hx)

/-- `store` keeps the condition `EffAnchorOK` of every anchor (F4; C1): the effective anchor has
no origin (`effAnchor_root`) and `a` has one, so its holder does not change. -/
theorem store_effAnchorOK {s : S3} {a p : Nat} {y : Authority} (hwf : WF3 s)
    (hy : s.A[a]? = some y) (ho : y.origin ≠ none) (x : Nat) (fd : Option Nat) :
    EffAnchorOK (storeEff s a p) x fd ↔ EffAnchorOK s x fd := by
  have sk := store_skel s a p
  have heq : (storeEff s a p).effAnchor x = s.effAnchor x := effAnchor_congr (by rw [sk.ancs])
  have hne : s.effAnchor x ≠ a := fun e => by
    have := effAnchor_root hwf.origin x; rw [e] at this
    simp only [S3.org, hy, Option.bind_some] at this; exact ho this
  have hA : (storeEff s a p).A[s.effAnchor x]? = s.A[s.effAnchor x]? := by
    rw [store_get hy]; simp [Ne.symm hne]
  have hP : (storeEff s a p).P = s.P := by rw [storeEff_eq hy]
  have hF : (storeEff s a p).F = s.F := by rw [storeEff_eq hy]
  unfold EffAnchorOK; rw [heq, hA, hF]
  simp only [S3.hframe_congr hP]

/-- `store` preserves `AnchorOrder` (F4; B8, C1): the added anchor satisfies the precondition on
its effective anchor; the other anchors and frames are unchanged. -/
theorem store_preserves_anchorOrder {s s' : S3} {a p : Nat} (hwf : WF3 s) (hao : AnchorOrder s)
    (h : StoreStep a p s (.ok s')) : AnchorOrder s' := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  obtain ⟨y, hy, -, ho, -⟩ := store_pre_auth hpre
  have e := storeEff_eq (p := p) hy
  have hP : (storeEff s a p).P = s.P := by rw [e]
  have hF : (storeEff s a p).F = s.F := by rw [e]
  have hd : (storeEff s a p).dead = s.dead := by rw [e]
  intro q hq x hx
  have hq' := (S3.Usable.congr hP hF hd).1 hq
  rw [store_effAnchorOK hwf hy ho, S3.pframe_congr hP]
  rw [e] at hx; simp only at hx
  split at hx
  · subst q; rcases List.mem_append.1 hx with hx | hx
    · exact hao _ hq' x hx
    · rw [List.mem_singleton.1 hx]; exact hpre.2.2.2.2
  · exact hao q hq' x hx

/-- `store` preserves `NoDangling` (F4; C2): footprints, activity and usability are unchanged. -/
theorem store_preserves_noDangling {s s' : S3} {a p : Nat} (hnd : NoDangling s)
    (h : StoreStep a p s (.ok s')) : NoDangling s' := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  obtain ⟨y, hy, -⟩ := store_pre_auth hpre
  have e := storeEff_eq (p := p) hy
  have hP : (storeEff s a p).P = s.P := by rw [e]
  have hF : (storeEff s a p).F = s.F := by rw [e]
  have hd : (storeEff s a p).dead = s.dead := by rw [e]
  have sk := store_skel s a p
  exact hnd.of (fun q l hl => by rw [hP] at hl; exact hl)
    (fun q hq => (S3.Usable.congr hP hF hd).2 hq)
    (fun j z hz za l hl => by
      obtain ⟨z₀, hz₀, ez⟩ := sk.get hz; simp [skel] at ez
      exact ⟨j, z₀, hz₀, ez.2.2.2 ▸ za, ez.2.2.1 ▸ hl⟩)

/-- `store_root_rejected` (F4): storing an authority without origin, a root, is rejected. -/
theorem store_root_rejected {s : S3} {a p : Nat} {y : Authority} (hy : s.A[a]? = some y)
    (ho : y.origin = none) : StoreStep a p s .reject :=
  .reject fun h => by
    obtain ⟨y', hy', -, ho', -⟩ := store_pre_auth h
    rw [hy] at hy'; cases hy'; exact ho' ho

theorem mem_of_mem_dropWhile {p : Nat → Bool} : ∀ {l : List Nat} {x : Nat}, x ∈ l.dropWhile p → x ∈ l
  | [], _, h => by simp at h
  | b :: l, x, h => by
    simp only [List.dropWhile_cons] at h
    split at h
    · exact List.mem_cons_of_mem _ (mem_of_mem_dropWhile h)
    · exact h

/-- `store_escape_rejected_at_transfer` (F4; MM-03.3.1: « Un accès temporaire ne peut être
prolongé simplement en le stockant dans un cadre plus ancien »; MM-03.3.6; C1): a value `src`,
one of whose parts (`src` included) is anchored on an authority `a` whose effective anchor does
not move with the value and is of the current frame `f`, such as an authority derived from a
local of `f` and stored into `src` or one of its fields, cannot be transferred to a destination
whose frame, after the transfer, is an older frame `g`: the dependency follows the value
(`depsOf`, MM-03.3.6; MM-03.3 §3, O4) and the clause B8 of `transfer` checks its effective
anchor. An effective anchor that moves with the value, the root of storage the value owns,
travels with it (A5). The theorem speaks of the authorities placed by `store`, which anchors
them; a block issued to `src` is held without being an anchor (pass-6 report, (d) 3). -/
theorem store_escape_rejected_at_transfer {k : K} {s : S3} {src dst a f g : Nat} {F₀ : Frames}
    {z : Authority} (hwf : WF3 s) (hF : s.F = f :: F₀) (ha : a ∈ depsOf s src)
    (hz : s.A[s.effAnchor a]? = some z) (hm : ¬ AnchorMoves s src (s.effAnchor a))
    (hzf : s.hframe z.holder = some f)
    (hg : (transferEff s src dst).pframe dst = some g) (hgF : g ∈ F₀) :
    TransferStep k src dst s .reject := by
  refine .reject fun hpre => ?_
  have hdst : (transferEff s src dst).Usable dst := hpre.2.2.2.2.2.2.2.1
  have hin : a ∈ (transferEff s src dst).D dst := by
    simp only [transferEff, ↓reduceIte]
    exact List.mem_append_right _ ha
  have hok := hpre.2.2.2.2.2.2.2.2.2.2.2.2 dst
    (List.mem_range.2 (by have := hdst.lt; simpa [transferEff] using this)) hdst a hin (.inr (.inl rfl))
  rw [transfer_effAnchorOK_unmoved hz hm, hg] at hok
  unfold EffAnchorOK at hok
  rw [hz] at hok
  simp only [OptP, hzf] at hok
  have hnd := List.nodup_cons.1 (hF ▸ hwf.nodup)
  rw [hF] at hok
  unfold ancestor at hok
  have hfg : f ≠ g := fun e => hnd.1 (e ▸ hgF)
  simp only [List.dropWhile_cons, show (f != g) = true by simp [hfg], ↓reduceIte] at hok
  exact hnd.1 (mem_of_mem_dropWhile hok)

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

/-- The place of the arena value: the holder of `internal` (F1, replacing the owner of the storage
of A10 and D3). -/
def arenaValue (s : S3) (ar : Arena) : Option Nat :=
  match s.A[ar.internal]? with
  | some y =>
    match y.holder with
    | .place v => some v
    | .frame _ => none
  | none => none

/-- Metadata leaves of the arena: the footprint of the arena value (A10). -/
def metaLeaves (s : S3) (ar : Arena) : List Nat :=
  match arenaValue s ar with
  | some v => footprint s.P v
  | none => []

/-- Arena invariant (MM-03.3 §6; A10; D3; F1; F2). Clauses of §6: issued regions within the
administered storage (the footprint of `internal`); two simultaneously valid issued regions
disjoint; available regions disjoint from the still distributed ones; added: available regions
within the storage. Clause of A10: each emission is a `Modify` authority derived from `internal`
on its region. F2: the storage is a place of `P`, owned by anything (a local, a static, an
allocated root, a block): the ownership clause of A10 is removed. F1: `internal` is a `Modify`
authority held by a place, the arena value, and covers exactly the footprint of the storage. -/
def ArenaInv (s : S3) (ar : Arena) : Prop :=
  (∀ l ∈ ar.available, l ∈ s.afp ar.internal) ∧
  (∀ e ∈ ar.issued, ∀ l ∈ e.1, l ∈ s.afp ar.internal) ∧
  ar.issued.Pairwise (fun e e' => s.Active e.2 → s.Active e'.2 → ∀ l ∈ e.1, l ∉ e'.1) ∧
  (∀ e ∈ ar.issued, s.Active e.2 → ∀ l ∈ e.1, l ∉ ar.available) ∧
  (∀ e ∈ ar.issued, ∃ y, s.A[e.2]? = some y ∧ y.origin = some ar.internal ∧
    y.footprint = e.1 ∧ y.mode = .modify) ∧
  ar.storage < s.P.length ∧
  (∃ (y : Authority) (v : Nat), s.A[ar.internal]? = some y ∧ y.mode = .modify ∧
    y.holder = .place v) ∧
  (∀ l, l ∈ s.afp ar.internal ↔ l ∈ footprint s.P ar.storage)

/-- Right to update the metadata of the arena (A10; C6, aligned with `ProviderRight`): exercisable
`Modify` on the arena value, or an authority `via` exercisable at `Observe` (B2) with a present
effective mode on every metadata leaf, all `SharedMutable` (a `writeShared`, A9), with valid
dependencies. -/
def MetaRight (k : K) (s : S3) (ar : Arena) (via : Nat) : Prop :=
  OptP (arenaValue s ar) (fun v => HasRight s .modify v) False ∨
  (s.ExercisableAt via .observe ∧ arenaValue s ar ≠ none ∧
    ∀ l ∈ metaLeaves s ar, effective s via l ≠ none ∧ k.SharedMutable l ∧ DepsValid s l)

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

/-- `arena_issue_preserves_disjointness` (MM-03.3 §6, §10; A10): `issue` preserves `WF3`, `Inv3base`
and the arena invariant. The disjointness of the new region is obtained from the access
discipline (`issue_disjoint_redundant`), not from a precondition. No hypothesis on `K`. -/
theorem arena_issue_preserves_disjointness {k : K} {s s' : S3} {ar ar' : Arena} {via dst : Nat}
    {region : List Nat} (hwf : WF3 s) (hinv : Inv3base s) (hai : ArenaInv s ar)
    (h : IssueStep k ar via region dst s (.ok s' ar')) : WF3 s' ∧ Inv3base s' ∧ ArenaInv s' ar' := by
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
  obtain ⟨c0, c1, c2, c3, c4, c5, ⟨yi, vi, hyi, hmi, hhi⟩, c7⟩ := hai
  have old : ∀ e ∈ ar.issued, e.2 < s.A.length := fun e he => by
    obtain ⟨y, hy, -⟩ := c4 e he; exact lt_of_getElem? hy
  have hi := lt_of_getElem? hyi
  refine ⟨hwf₁.of_eq rfl rfl rfl rfl rfl, ⟨hinv₁.1, hinv₁.2.1, fun q hq y hy =>
    hinv₁.2.2.1 q ((S3.Usable.congr (s' := (issueEff s ar region dst).1)
      (s := s.addAuth ⟨.modify, some ar.internal, region, .place dst, true⟩) rfl rfl rfl).1 hq) y hy,
    i4_always _⟩, ?_⟩
  refine ⟨fun l hl => ?_, fun e he l hl => ?_, ?_, fun e he ha l hl => ?_, fun e he => ?_, c5,
    ⟨yi, vi, by show (s.addAuth _).A[ar.internal]? = _; rw [addAuth_lt hi]; exact hyi,
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

/-- `reset` preserves `WF3` and `Inv3base` (MM-03.3 §6; A10): it only writes the metadata. -/
theorem arena_reset_preserves_wf {k : K} {s s' : S3} {ar ar' : Arena} {via : Nat} (hwf : WF3 s)
    (hinv : Inv3base s) (h : ResetStep k ar via s (.ok (s', ar'))) : WF3 s' ∧ Inv3base s' := by
  obtain ⟨-, e⟩ := Guarded.ok_iff.1 h
  have e1 := congrArg Prod.fst e; simp only [resetEff] at e1; subst e1
  exact ⟨hwf.of_eq rfl rfl rfl rfl rfl, ⟨hinv.1, hinv.2.1, fun q hq y hy =>
    hinv.2.2.1 q ((S3.Usable.congr (s := s)
      (s' := { s with I := fun l => if l ∈ metaLeaves s ar then .init else s.I l })
      rfl rfl rfl).1 hq) y hy, i4_always _⟩⟩

/-- `arena_reuse_safe` (MM-03.3 §6; A10): after `reset`, issuing again, a region already issued
included, preserves `WF3`, `Inv3base` and the arena invariant, and leaves every past emission
inactive: no stale access. -/
theorem arena_reuse_safe {k : K} {s s₁ s₂ : S3} {ar ar₁ ar₂ : Arena} {via via' dst : Nat}
    {region : List Nat} (hwf : WF3 s) (hinv : Inv3base s) (hai : ArenaInv s ar)
    (hr : ResetStep k ar via s (.ok (s₁, ar₁)))
    (hi : IssueStep k ar₁ via' region dst s₁ (.ok s₂ ar₂)) :
    WF3 s₂ ∧ Inv3base s₂ ∧ ArenaInv s₂ ar₂ ∧ ∀ e ∈ ar.issued, ¬ s₂.Active e.2 := by
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

/-- One `ok` transition of a kernel operation (MM-03.3 §3–5; A6–A9; F4). -/
inductive KStep (k : K) : S3 → S3 → Prop where
  | derive {s s' : S3} {src q : Nat} {m : Mode} : DeriveStep src q m s (.ok s') → KStep k s s'
  | split {s s' : S3} {src : Nat} {rs : List (List Nat)} :
      SplitStep k src rs s (.ok s') → KStep k s s'
  | release {s s' : S3} {a : Nat} : ReleaseStep a s (.ok s') → KStep k s s'
  | transfer {s s' : S3} {src dst : Nat} : TransferStep k src dst s (.ok s') → KStep k s s'
  | depend {s s' : S3} {q x : Nat} : DependStep q x s (.ok s') → KStep k s s'
  | enter {s s' : S3} {ps : List Nat} {ls : List (Option Nat × Option Nat × Nat)} :
      EnterStep ps ls s (.ok s') → KStep k s s'
  | exit {s s' : S3} : ExitStep k s (.ok s') → KStep k s s'
  | read {s s' : S3} {a : Nat} {ls : List Nat} : Read3Step a ls s (.ok s') → KStep k s s'
  | write {s s' : S3} {a : Nat} {ls : List Nat} : Write3Step a ls s (.ok s') → KStep k s s'
  | writeShared {s s' : S3} {a : Nat} {ls : List Nat} :
      WriteSharedStep k a ls s (.ok s') → KStep k s s'
  | pin {s s' : S3} {p : Nat} : PinStep p s (.ok s') → KStep k s s'
  | unpin {s s' : S3} {p : Nat} : UnpinStep k p s (.ok s') → KStep k s s'
  | endUse {s s' : S3} {p : Nat} : EndUseStep k p s (.ok s') → KStep k s s'
  | free {s s' : S3} {p auth : Nat} : FreeStep k p auth s (.ok s') → KStep k s s'
  | alloc {s s' : S3} {pr ow : Nat} {ls : List (Option Nat × Option Nat × Nat)} :
      AllocStep k pr ow ls s (.ok s') → KStep k s s'
  | store {s s' : S3} {a p : Nat} : StoreStep a p s (.ok s') → KStep k s s'

/-- Sufficient conditions for the arena invariant to carry over to a new state: existing
authorities keep mode and footprint, only lose activity, keep an origin equal to `internal`; places
are not removed; `internal` stays held by a place (F1). -/
theorem arenaInv_transport {s s' : S3} {ar : Arena} (hai : ArenaInv s ar)
    (hA : ∀ (j : Nat) (y : Authority), s.A[j]? = some y → ∃ y', s'.A[j]? = some y' ∧
      y'.mode = y.mode ∧ y'.footprint = y.footprint ∧ (y'.active = true → y.active = true) ∧
      (y.origin = some ar.internal → y'.origin = some ar.internal))
    (hlen : s.P.length ≤ s'.P.length)
    (hown : ∀ (y y' : Authority) (v : Nat), s.A[ar.internal]? = some y →
      s'.A[ar.internal]? = some y' → y.holder = .place v → ∃ v', y'.holder = .place v')
    (hfoot : ∀ l, l ∈ footprint s'.P ar.storage ↔ l ∈ footprint s.P ar.storage) :
    ArenaInv s' ar := by
  obtain ⟨c0, c1, c2, c3, c4, c5, ⟨yi, vi, hyi, hmi, hhi⟩, c7⟩ := hai
  obtain ⟨yi', hyi', mi, fi, -, -⟩ := hA _ yi hyi
  have hafp : s'.afp ar.internal = s.afp ar.internal := by simp [S3.afp, hyi, hyi', fi]
  have act : ∀ x, s'.Active x → x < s.A.length → s.Active x := fun x ⟨y', hy', ya'⟩ hx => by
    obtain ⟨y, hy⟩ : ∃ y, s.A[x]? = some y := ⟨_, List.getElem?_eq_some_iff.2 ⟨hx, rfl⟩⟩
    obtain ⟨y'', hy'', -, -, ha, -⟩ := hA x y hy
    rw [hy'] at hy''; cases hy''; exact ⟨y, hy, ha ya'⟩
  have old : ∀ e ∈ ar.issued, e.2 < s.A.length := fun e he => by
    obtain ⟨y, hy, -⟩ := c4 e he; exact lt_of_getElem? hy
  obtain ⟨vi', hh'⟩ := hown yi yi' vi hyi hyi' hhi
  refine ⟨fun l hl => hafp ▸ c0 l hl, fun e he l hl => hafp ▸ c1 e he l hl,
    c2.imp_of_mem fun {e e'} he he' h ha ha' => h (act _ ha (old e he)) (act _ ha' (old e' he')),
    fun e he ha => c3 e he (act _ ha (old e he)), fun e he => ?_, Nat.lt_of_lt_of_le c5 hlen,
    ⟨yi', vi', hyi', mi ▸ hmi, hh'⟩, fun l => by rw [hafp, hfoot]; exact c7 l⟩
  obtain ⟨y, hy, ho, hf, hm⟩ := c4 e he
  obtain ⟨y', hy', m', f', -, o'⟩ := hA _ y hy
  exact ⟨y', hy', o' ho, f'.trans hf, m'.trans hm⟩

theorem OwnedRoot.of_P {s s' : S3} {q : Nat} (h : OwnedRoot s q) (hP : s'.P[q]? = s.P[q]?) :
    OwnedRoot s' q := by
  unfold OwnedRoot at h ⊢; rw [hP]; exact h

/-- `arena_inv_preserved` (MM-03.3 §6; A10; D3; F1): every `ok` transition of a kernel operation
preserves the arena invariant of an arena still live afterwards. Liveness after the step is
needed at the exit only: an `internal` that is a block may have an ancestor that survives it, onto
which the exit would re-anchor the blocks issued from it (A7). -/
theorem arena_inv_preserved {k : K} {s s' : S3} {ar : Arena} (hwf : WF3 s) (hinv : Inv3base s)
    (hai : ArenaInv s ar) (h : KStep k s s') (hlive : s'.Active ar.internal) : ArenaInv s' ar := by
  obtain ⟨yi, vi, hyi, -, hhi⟩ := hai.2.2.2.2.2.2.1
  have hi := lt_of_getElem? hyi
  have same : ∀ s₁ : S3, s₁.A = s.A → s₁.P = s.P → ArenaInv s₁ ar := fun s₁ hA hP =>
    arenaInv_transport hai (fun j y hy => ⟨y, by rw [hA]; exact hy, rfl, rfl, id, id⟩)
      (by rw [hP]; exact Nat.le_refl _) (fun y y' v h1 h2 h3 => ⟨v, by
        rw [hA, h1] at h2; cases h2; exact h3⟩) (fun l => by rw [hP])
  have append : ∀ (l : List Authority), ArenaInv { s with A := s.A ++ l } ar := fun l =>
    arenaInv_transport hai (fun j y hy => ⟨y, List.getElem?_append_left (lt_of_getElem? hy) ▸ hy,
      rfl, rfl, id, id⟩) (Nat.le_refl _)
      (fun y y' v h1 h2 h3 => ⟨v, by
        rw [show ({ s with A := s.A ++ l } : S3).A = s.A ++ l from rfl,
          List.getElem?_append_left hi, h1] at h2; cases h2; exact h3⟩) (fun _ => Iff.rfl)
  have releases : ∀ s₁, OnlyReleases s s₁ → s₁.P = s.P → ArenaInv s₁ ar := fun s₁ hr hP =>
    arenaInv_transport hai (fun j y hy => by
      obtain ⟨y', hy'⟩ : ∃ y', s₁.A[j]? = some y' :=
        ⟨_, List.getElem?_eq_some_iff.2 ⟨by rw [hr.1]; exact lt_of_getElem? hy, rfl⟩⟩
      obtain ⟨y₀, hy₀, m, o, f, -, a⟩ := hr.2 j y' hy'
      rw [hy] at hy₀; cases hy₀
      exact ⟨y', hy', m, f, a, fun h => o ▸ h⟩)
      (by rw [hP]; exact Nat.le_refl _)
      (fun y y' v h1 h2 h3 => by
        obtain ⟨y₀, hy₀, -, -, -, hh, -⟩ := hr.2 _ y' h2
        rw [h1] at hy₀; cases hy₀
        exact ⟨v, hh ▸ h3⟩) (fun l => by rw [hP])
  cases h with
  | derive hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact append _
  | split hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact append _
  | release hs =>
    obtain ⟨⟨⟨x, hx, -⟩, -⟩, rfl⟩ := Guarded.ok_iff.1 hs
    exact releases _ (release_releases s _) (by rw [releaseEff_eq hx])
  | transfer hs =>
    rename_i src dst
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
    refine arenaInv_transport hai (fun j y hy =>
      ⟨if heldIn s.P src y.holder then { y with holder := .place dst } else y,
        by rw [transfer_A_get, hy]; rfl, ?_⟩) (by simp [transferEff]) ?_
        (fun l => by rw [transfer_footprint])
    · by_cases hc : heldIn s.P src y.holder <;> simp [hc]
    · intro y y' v h1 h2 h3
      rw [transfer_A_get, h1] at h2; cases h2
      by_cases hc : heldIn s.P src y.holder
      · exact ⟨dst, by simp only [hc, ↓reduceIte]⟩
      · exact ⟨v, by simp only [hc, ↓reduceIte]; exact h3⟩
  | depend hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact same _ rfl rfl
  | read hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact same _ rfl rfl
  | write hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact same _ rfl rfl
  | writeShared hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact same _ rfl rfl
  | pin hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact same _ rfl rfl
  | unpin hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact same _ rfl rfl
  | enter hs =>
    rename_i ps ls
    obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 hs
    have hst := hai.2.2.2.2.2.1
    have hnot : ar.internal ∉ ps := fun hm => by
      have h1 := hpre.2.1 _ hm
      simp only [OptP, hyi] at h1
      obtain ⟨-, hp, -⟩ := h1
      rw [hhi] at hp; cases hp
    refine arenaInv_transport hai (fun j y hy => ⟨_, by rw [enter_lt (lt_of_getElem? hy), hy]; rfl,
      ?_⟩) (by simp [enterEff, enterP_len]) ?_ (enter_footprint_old hpre hst)
    · split <;> simp
    · intro y y' v h1 h2 h3
      rw [enter_lt hi, h1] at h2; simp only [Option.map_some, Option.some.injEq, hnot,
        ↓reduceIte] at h2
      exact ⟨v, h2 ▸ h3⟩
  | exit hs =>
    obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 hs
    unfold ExitPre at hpre
    split at hpre
    · rename_i f F₀ hF
      obtain ⟨-, -, hR2, -⟩ := hpre
      refine arenaInv_transport hai (fun j y hy => ⟨_, by rw [exit_A_get hF, hy]; rfl,
        (exitG_same s F₀ j y).1, (exitG_same s F₀ j y).2.1, exitG_active' hy, fun ho => ?_⟩)
        (by rw [exitEff_eq hF]; exact Nat.le_refl _) ?_ (fun l => by rw [exitEff_eq hF])
      · rcases exitG_origin (s := s) (F₀ := F₀) (a := j) (y := y) with e | ⟨hsv, -, e⟩
        · rw [e, ho]
        · rw [e]
          have hob : s.org j = some ar.internal := by simp [S3.org, hy, ho]
          have hsi : Survives s F₀ ar.internal := by
            obtain ⟨z, hz, za⟩ := hlive
            rw [exit_A_get hF, hyi] at hz; cases hz; exact exitG_active za
          rw [ancs_cons hwf.origin hob]
          simp [firstSurv, hsi]
      · intro y y' v h1 h2 h3
        rw [exit_A_get hF, h1] at h2; cases h2
        exact ⟨v, (exitG_same s F₀ _ y).2.2 ▸ h3⟩
    · exact hpre.elim
  | endUse hs =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
    exact releases _ ((endUseS_releases s _).trans cleanup_releases) rfl
  | free hs =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
    exact releases _ ((freeS_releases s _).trans cleanup_releases) rfl
  | alloc hs =>
    cases hs with
    | ok hsa _ =>
    have hst := hai.2.2.2.2.2.1
    refine arenaInv_transport hai (fun j y hy => ⟨y, by rw [alloc_lt (lt_of_getElem? hy)]; exact hy,
      rfl, rfl, id, id⟩) (by simp [allocEff, allocP_len]) ?_
      (shape_footprint_old hsa.2.2.2.2.2.1 hst)
    intro y y' v h1 h2 h3
    rw [alloc_lt hi, h1] at h2; cases h2
    exact ⟨v, h3⟩
  | store hs =>
    rename_i a p
    obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 hs
    obtain ⟨y, hy, -, -, hfr⟩ := store_pre_auth hpre
    have hne : a ≠ ar.internal := fun e => by subst e; rw [hyi] at hy; cases hy; rw [hhi] at hfr; cases hfr
    have sk := store_skel s a p
    have hP : (storeEff s a p).P = s.P := by rw [storeEff_eq hy]
    refine arenaInv_transport hai (fun j z hz => ?_) (by rw [hP]; exact Nat.le_refl _) ?_
      (fun l => by rw [hP])
    · obtain ⟨z', hz', ez⟩ := sk.get' hz; simp [skel] at ez
      exact ⟨z', hz', ez.1, ez.2.2.1, fun h => ez.2.2.2 ▸ h, fun h => ez.2.1 ▸ h⟩
    · intro y₁ y₁' v h1 h2 h3
      rw [store_get hy] at h2; simp only [hne, ↓reduceIte, h1] at h2; cases h2; exact ⟨v, h3⟩

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
theorem exit_det {k : K}  {s : S3} {o₁ o₂ : Outcome3 S3}
    (h₁ : ExitStep k s o₁) (h₂ : ExitStep k s o₂) : o₁ = o₂ := Guarded.det h₁ h₂

/-- `ok` outcome of `exit` (MM-03.3 §4, O7). -/
theorem exit_ok_iff {k : K}  {s s' : S3} :
    ExitStep k s (.ok s') ↔ ExitPre k s ∧ s' = exitEff s := Guarded.ok_iff

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

/-- `Inv3base` part of `addAuth_preserves`, without `WF3`. -/
theorem addAuth_inv3 {s : S3} (hinv : Inv3base s) {src : Nat} {x : Authority} {m : Mode}
    {fp : List Nat} {hd : Holder} (hx : s.A[src]? = some x)
    (hfp : ∀ p ∈ fp, p ∈ x.footprint) (hal : ∀ p ∈ fp, Allows (effective s src p) m) :
    Inv3base (s.addAuth ⟨m, some src, fp, hd, true⟩) := by
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

/-- `derive` preserves `Inv3base` without `WF3` (MM-03.3 §3, O1; A1). -/
theorem derive_preserves_inv3 {s s' : S3} {src q : Nat} {m : Mode} (hinv : Inv3base s)
    (h : DeriveStep src q m s (.ok s')) : Inv3base s' := by
  obtain ⟨⟨⟨x, hx, -⟩, -, -, hfp, hal⟩, rfl⟩ := Guarded.ok_iff.1 h
  exact addAuth_inv3 hinv hx (fun p hp => by simpa [S3.afp, hx] using hfp p hp) hal

theorem split_aux_inv3 {src : Nat} {x : Authority} : ∀ (rs : List (List Nat)) (s : S3), Inv3base s →
    s.A[src]? = some x →
    (∀ r ∈ rs, ∀ p ∈ r, effective s src p = some .modify ∧ p ∈ x.footprint) →
    rs.Pairwise (fun r r' => ∀ l ∈ r, l ∉ r') → Inv3base (splitEff s src rs)
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

/-- `split` preserves `Inv3base` without `WF3` (MM-03.3 §3, O2; A1), under `DDSound k`
(MM-03.3.8). -/
theorem split_preserves_inv3_underDD {k : K} (hdd : DDSound k) {s s' : S3} {src : Nat}
    {rs : List (List Nat)} (hinv : Inv3base s) (h : SplitStep k src rs s (.ok s')) : Inv3base s' := by
  obtain ⟨⟨⟨x, hx, -⟩, -, h1, h2, h3, -⟩, rfl⟩ := Guarded.ok_iff.1 h
  refine split_aux_inv3 rs s hinv hx (fun r hr p hp => ⟨h1 r hr p hp, ?_⟩)
    (h3.imp fun {r r'} h => h.elim id fun hd => hdd r r' hd)
  simpa [S3.afp, hx] using (h2 r hr p hp).1

/-- `split_preserves_exclusivity` (MM-03.3 §10): `split` preserves I1 under `Inv3base` alone,
conditional on `DDSound k` (MM-03.3.8). -/
theorem split_preserves_exclusivity_underDD {k : K} (hdd : DDSound k) {s s' : S3} {src : Nat}
    {rs : List (List Nat)} (hinv : Inv3base s) (h : SplitStep k src rs s (.ok s')) : I1 s' :=
  (split_preserves_inv3_underDD hdd hinv h).1

/-- `release` preserves `Inv3base` without `WF3` (MM-03.3 §3, O3; A1): the strengthened I1 only
constrains active authorities, which `release` removes. -/
theorem release_preserves_inv3 {s s' : S3} {a : Nat} (hinv : Inv3base s)
    (h : ReleaseStep a s (.ok s')) : Inv3base s' := by
  obtain ⟨⟨⟨x, hx, xa⟩, -, h3, -⟩, rfl⟩ := Guarded.ok_iff.1 h
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
    obtain ⟨hy', hya⟩ := release_D_mem hx hy
    obtain ⟨z, hz, za⟩ := i3 q hq' y hy'
    refine ⟨z, ?_, za⟩
    rw [get]; split
    · subst_vars
      have := h3 q (List.mem_range.2 hq'.lt) hq' hy'
      rw [hx] at this; exact absurd (Option.some.inj this) (hya rfl)
    · exact hz

/-- `depend` preserves `Inv3base` without `WF3` (MM-03.3 §3, O5). -/
theorem depend_preserves_inv3 {s s' : S3} {q x : Nat} (hinv : Inv3base s)
    (h : DependStep q x s (.ok s')) : Inv3base s' := by
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

/-- `write3` preserves `Inv3base` without `WF3` (MM-03.3 §5). -/
theorem write3_preserves_inv3 {s s' : S3} {a : Nat} {ls : List Nat} (hinv : Inv3base s)
    (h : Write3Step a ls s (.ok s')) : Inv3base s' := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
  exact ⟨hinv.1, hinv.2.1, fun q hq x hx =>
    hinv.2.2.1 q ((S3.Usable.congr (s := s) (s' := write3Eff s ls) rfl rfl rfl).1 hq) x hx,
    i4_always _⟩

/-- `issue` preserves `Inv3base` without `WF3` (MM-03.3 §6; A1; A10). -/
theorem issue_preserves_inv3 {k : K} {s s' : S3} {ar ar' : Arena} {via dst : Nat}
    {region : List Nat} (hinv : Inv3base s) (h : IssueStep k ar via region dst s (.ok s' ar')) :
    Inv3base s' := by
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

/-- `issue` preserves `AnchorOrder` (B8, C1; MM-03.3 §6; A10), under `AnchorOrder` alone. -/
theorem issue_preserves_anchorOrder {k : K} {s s' : S3} {ar ar' : Arena} {via dst : Nat}
    {region : List Nat} (hao : AnchorOrder s) (h : IssueStep k ar via region dst s (.ok s' ar')) :
    AnchorOrder s' := by
  cases h with
  | ok _ _ _ =>
  exact hao.of rfl rfl (fun _ hq => hq.of_eqs rfl rfl rfl) (fun _ _ _ hx => hx)
    (fun _ ha => ancs_addAuth_lt ha)
    (fun x y hy => ⟨y, by
      show (s.addAuth _).A[x]? = _; rw [addAuth_lt (lt_of_getElem? hy)]; exact hy, rfl, rfl⟩)

/-- `issue` preserves `NoDangling` (C2; MM-03.3 §6; A10): the block is within the footprint of the
active `internal` (`IssueRight`). -/
theorem issue_preserves_noDangling {k : K} {s s' : S3} {ar ar' : Arena} {via dst : Nat}
    {region : List Nat} (hnd : NoDangling s) (h : IssueStep k ar via region dst s (.ok s' ar')) :
    NoDangling s' := by
  cases h with
  | ok _ _ hright =>
  refine hnd.of (s' := (issueEff s ar region dst).1) (fun _ _ h => h)
    (fun _ h => h.of_eqs rfl rfl rfl) fun j z hz za => ?_
  rcases addAuth_get (s := s) hz with ⟨-, hy⟩ | ⟨-, rfl⟩
  · exact fun l hl => ⟨j, z, hy, za, hl⟩
  · intro l hl
    obtain ⟨x, hx, xa, hlx, -⟩ := effective_some (hright l hl)
    exact ⟨ar.internal, x, hx, xa, hlx⟩

/-- `reset` preserves `NoDangling` (C2; MM-03.3 §6; A10): it only writes the metadata. -/
theorem reset_preserves_noDangling {k : K} {s s' : S3} {ar ar' : Arena} {via : Nat}
    (hnd : NoDangling s) (h : ResetStep k ar via s (.ok (s', ar'))) : NoDangling s' := by
  obtain ⟨-, e⟩ := Guarded.ok_iff.1 h
  have e1 := congrArg Prod.fst e; simp only [resetEff] at e1; subst e1
  exact hnd.of (fun _ _ h => h) (fun _ h => h.of_eqs rfl rfl rfl)
    fun j z hz za _ hl => ⟨j, z, hz, za, hl⟩

/-- `reset` preserves `AnchorOrder` (B8, C1; MM-03.3 §6; A10): it only writes the metadata. -/
theorem reset_preserves_anchorOrder {k : K} {s s' : S3} {ar ar' : Arena} {via : Nat}
    (hao : AnchorOrder s) (h : ResetStep k ar via s (.ok (s', ar'))) : AnchorOrder s' := by
  obtain ⟨-, e⟩ := Guarded.ok_iff.1 h
  have e1 := congrArg Prod.fst e; simp only [resetEff] at e1; subst e1
  exact hao.of rfl rfl (fun _ hq => hq.of_eqs rfl rfl rfl) (fun _ _ _ hx => hx)
    (fun _ _ => rfl) (fun _ y hy => ⟨y, hy, rfl, rfl⟩)

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
it too in `Modify`. I1 fails in its structural form (A1) and in the effective form of the text of
§2 (pass 1). `WF3` (footprints made of existing places) excludes this state. -/
theorem enter_not_inv3_preserving :
    let s : S3 := ⟨[0], 1, [], fun _ => .uninit, [⟨.modify, none, [0], .frame 0, true⟩],
      fun _ => [], fun _ => false, fun _ => false, fun _ => false, [], fun _ => []⟩
    Inv3 s ∧ EnterStep [] [(none, none, 0)] s (.ok (enterEff s [] [(none, none, 0)])) ∧
      ¬ I1 (enterEff s [] [(none, none, 0)]) ∧
      ¬ ∀ a b p m₁ m₂, a ≠ b → effective (enterEff s [] [(none, none, 0)]) a p = some m₁ →
        effective (enterEff s [] [(none, none, 0)]) b p = some m₂ → Compat m₁ m₂ := by
  intro s
  refine ⟨⟨⟨fun a b x y p hab ha hb _ _ _ _ _ _ => ?_, fun b y a hb ho => ?_,
    fun q hq => ?_, i4_always _⟩, fun q hq => absurd hq.lt (by simp [s]),
    fun _ _ _ _ _ _ l hl => by simp [footprint, s] at hl⟩, .ok (by decide),
    fun h => ?_, fun h => ?_⟩
  · have h1 := lt_of_getElem? ha; have h2 := lt_of_getElem? hb
    simp [s] at h1 h2; omega
  · have := lt_of_getElem? hb; simp [s] at this; subst this; simp [s] at hb; subst hb; cases ho
  · have := hq.lt; simp [s] at this
  · have := h 0 1 ⟨.modify, none, [0], .frame 0, true⟩ ⟨.modify, none, [0], .frame 1, true⟩ 0
      (by decide) (by decide) (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide)
    exact absurd this.1 (by decide)
  · exact absurd (h 0 1 0 .modify .modify (by decide) (by decide) (by decide)).1 (by decide)

/-! ## Arenas in the state (D3) -/

/-- The state with the entry `i` of `arenas` replaced by `ar` (D3). -/
def arenaSet (s : S3) (i : Nat) (ar : Arena) : S3 := { s with arenas := s.arenas.set i ar }

/-- Preconditions of `newArena storage internal` (D3, F1, F2), in order. Kept from D3: exercisable
`Modify` on `storage`; `storage` usable. F1: `internal`, named by the caller, is active, `Modify`,
exercisable at `Modify` (B2), and held by a place, the arena value; the footprint of `internal` is
the footprint of `storage`; no live arena already has `internal` as `internal`. F1 removes the
guard by place index of D3 and the kind of `internal`; F2 removes the ownership of the storage
(A10): the storage may be a local, a static, an allocated root or a block. -/
def NewArenaPre (s : S3) (storage internal : Nat) : Prop :=
  HasRight s .modify storage ∧ s.Usable storage ∧
    OptP (s.A[internal]?) (fun y => y.active = true ∧ y.mode = .modify ∧ y.holder.isPlace = true)
      False ∧
    s.ExercisableAt internal .modify ∧
    (∀ l ∈ s.afp internal, l ∈ footprint s.P storage) ∧
    (∀ l ∈ footprint s.P storage, l ∈ s.afp internal) ∧
    (∀ ar ∈ s.arenas, s.Active ar.internal → ar.internal ≠ internal)

instance (s : S3) (storage internal : Nat) : Decidable (NewArenaPre s storage internal) := by
  unfold NewArenaPre; infer_instance

/-- Effect of `newArena storage internal` (D3; F1): a new entry, the whole storage available,
nothing issued. -/
def newArenaEff (s : S3) (storage internal : Nat) : S3 :=
  { s with arenas := s.arenas ++ [⟨storage, internal, s.afp internal, []⟩] }

/-- `newArena storage internal : ok | reject` as a relation (D3; F1). -/
def NewArenaStep (storage internal : Nat) (s : S3) : Outcome3 S3 → Prop :=
  Guarded (NewArenaPre s storage internal) (newArenaEff s storage internal)

/-- `arena.issue` on the entry `i` of the state (MM-03.3 §6; A10; D3): the step `IssueStep` of the
recorded arena, whose new logical state is written back; a missing entry is rejected. An entry
whose `internal` is released is rejected by `IssueStatic`, which asks it active. -/
inductive IssueAt (k : K) (i via : Nat) (region : List Nat) (dst : Nat) (s : S3) :
    AOutcome → Prop where
  | ok {ar : Arena} {s' : S3} {ar' : Arena} : s.arenas[i]? = some ar →
      IssueStep k ar via region dst s (.ok s' ar') → IssueAt k i via region dst s (.ok (arenaSet s' i ar'))
  | fail {ar : Arena} {s' : S3} {ar' : Arena} : s.arenas[i]? = some ar →
      IssueStep k ar via region dst s (.fail s' ar') → IssueAt k i via region dst s (.fail s)
  | reject {ar : Arena} : s.arenas[i]? = some ar → IssueStep k ar via region dst s .reject →
      IssueAt k i via region dst s .reject
  | none : s.arenas[i]? = none → IssueAt k i via region dst s .reject

/-- Preconditions of `arena.reset()` on the entry `i` of the state (MM-03.3 §6; A10; D3): the entry
exists and is live (an entry whose `internal` is released cannot be reset), and `ResetPre`. -/
def ResetAtPre (k : K) (s : S3) (i via : Nat) : Prop :=
  OptP (s.arenas[i]?) (fun ar => s.Active ar.internal ∧ ResetPre k s ar via) False

instance (k : K) [DecidablePred k.SharedMutable] (s : S3) (i via : Nat) :
    Decidable (ResetAtPre k s i via) := by
  unfold ResetAtPre; infer_instance

/-- Effect of `arena.reset()` on the entry `i` (D3): `resetEff`, the new logical state written
back. -/
def resetAtEff (s : S3) (i : Nat) : S3 :=
  match s.arenas[i]? with
  | some ar => arenaSet (resetEff s ar).1 i (resetEff s ar).2
  | none => s

/-- `arena.reset` on the entry `i` of the state as a relation (D3). -/
def ResetAtStep (k : K) (i via : Nat) (s : S3) : Outcome3 S3 → Prop :=
  Guarded (ResetAtPre k s i via) (resetAtEff s i)

/-- Determinism of `newArena` (D3; F1). -/
theorem newArena_det {st i : Nat} {s : S3} {o₁ o₂ : Outcome3 S3} (h₁ : NewArenaStep st i s o₁)
    (h₂ : NewArenaStep st i s o₂) : o₁ = o₂ := Guarded.det h₁ h₂

/-- Determinism of `arena.reset` on an entry of the state (D3). -/
theorem resetAt_det {k : K} {i via : Nat} {s : S3} {o₁ o₂ : Outcome3 S3}
    (h₁ : ResetAtStep k i via s o₁) (h₂ : ResetAtStep k i via s o₂) : o₁ = o₂ := Guarded.det h₁ h₂

/-- Determinism of `arena.issue` on an entry of the state (MM-03.3 §6; A10; D3). -/
theorem issueAt_det {k : K} {i via dst : Nat} {region : List Nat} {s : S3} {o₁ o₂ : AOutcome}
    (h₁ : IssueAt k i via region dst s o₁) (h₂ : IssueAt k i via region dst s o₂) : o₁ = o₂ := by
  have key : ∀ {ar ar' : Arena} {o o' : IOutcome}, s.arenas[i]? = some ar →
      s.arenas[i]? = some ar' → IssueStep k ar via region dst s o →
      IssueStep k ar' via region dst s o' → o = o' := by
    intro ar ar' o o' h h' hs hs'; rw [h] at h'; cases h'; exact issue_det hs hs'
  cases h₁ with
  | ok ha hs => cases h₂ with
    | ok ha' hs' => cases key ha ha' hs hs'; rfl
    | fail ha' hs' => cases key ha ha' hs hs'
    | reject ha' hs' => cases key ha ha' hs hs'
    | none hn => rw [ha] at hn; cases hn
  | fail ha hs => cases h₂ with
    | ok ha' hs' => cases key ha ha' hs hs'
    | fail ha' hs' => rfl
    | reject ha' hs' => cases key ha ha' hs hs'
    | none hn => rw [ha] at hn; cases hn
  | reject ha hs => cases h₂ with
    | ok ha' hs' => cases key ha ha' hs hs'
    | fail ha' hs' => cases key ha ha' hs hs'
    | reject ha' hs' => rfl
    | none hn => rfl
  | none hn => cases h₂ with
    | ok ha' hs' => rw [ha'] at hn; cases hn
    | fail ha' hs' => rw [ha'] at hn; cases hn
    | reject ha' hs' => rfl
    | none hn' => rfl

/-- Arena entries name existing authorities (D3): `newArena` takes `internal` from `A`, which
only grows. -/
def ArenasWF (s : S3) : Prop := ∀ ar ∈ s.arenas, ar.internal < s.A.length

/-- D3: every live arena of the state, one whose `internal` is active, satisfies `ArenaInv`. -/
def ArenasInv (s : S3) : Prop := ∀ ar ∈ s.arenas, s.Active ar.internal → ArenaInv s ar

theorem WF3.arenas {s : S3} (h : WF3 s) (l : List Arena) : WF3 { s with arenas := l } :=
  h.of_eq rfl rfl rfl rfl rfl

theorem Inv3.arenas {s : S3} (h : Inv3 s) (l : List Arena) : Inv3 { s with arenas := l } :=
  ⟨⟨h.base.1, h.base.2.1, fun q hq x hx => h.base.2.2.1 q (hq.of_eqs rfl rfl rfl) x hx,
    i4_always _⟩,
    h.ao.of rfl rfl (fun _ hq => hq.of_eqs rfl rfl rfl) (fun _ _ _ hx => hx) (fun _ _ => rfl)
      (fun _ y hy => ⟨y, hy, rfl, rfl⟩),
    h.nd.of (fun _ _ h => h) (fun _ hq => S3.Usable.of_eqs (s' := s) hq rfl rfl rfl)
      (fun j z hz za _ hl => ⟨j, z, hz, za, hl⟩)⟩
theorem ArenaInv.arenas {s : S3} {ar : Arena} (h : ArenaInv s ar) (l : List Arena) :
    ArenaInv { s with arenas := l } ar := h

/-- A kernel step changes no arena entry (D3). -/
theorem KStep.arenas {k : K} {s s' : S3} (h : KStep k s s') : s'.arenas = s.arenas := by
  cases h with
  | release hs =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; unfold releaseEff; split <;> rfl
  | exit hs =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; unfold exitEff; split <;> rfl
  | alloc hs => cases hs; rfl
  | store hs =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; unfold storeEff; split <;> rfl
  | derive hs | split hs | transfer hs | depend hs | enter hs | read hs | write hs
  | writeShared hs | pin hs | unpin hs | endUse hs | free hs =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; rfl

/-- A kernel step keeps the existing authorities, and activates none of them (MM-03.3 §3–5). -/
theorem KStep.active_back {k : K} {s s' : S3} (h : KStep k s s') :
    s.A.length ≤ s'.A.length ∧ ∀ x, x < s.A.length → s'.Active x → s.Active x := by
  have append : ∀ (l : List Authority), s.A.length ≤ (s.A ++ l).length ∧
      ∀ x, x < s.A.length → ({ s with A := s.A ++ l } : S3).Active x → s.Active x :=
    fun l => ⟨by simp, fun x hx ⟨y, hy, ya⟩ => ⟨y, by
      rw [show ({ s with A := s.A ++ l } : S3).A = s.A ++ l from rfl,
        List.getElem?_append_left hx] at hy; exact hy, ya⟩⟩
  have rel : ∀ s₁ : S3, OnlyReleases s s₁ →
      s.A.length ≤ s₁.A.length ∧ ∀ x, x < s.A.length → s₁.Active x → s.Active x :=
    fun s₁ hr => ⟨Nat.le_of_eq hr.1.symm, fun x _ ⟨y, hy, ya⟩ => by
      obtain ⟨y₀, hy₀, -, -, -, -, a⟩ := hr.2 x y hy; exact ⟨y₀, hy₀, a ya⟩⟩
  have same : ∀ s₁ : S3, s₁.A = s.A →
      s.A.length ≤ s₁.A.length ∧ ∀ x, x < s.A.length → s₁.Active x → s.Active x :=
    fun s₁ hA => ⟨by rw [hA]; exact Nat.le_refl _, fun x _ ⟨y, hy, ya⟩ => ⟨y, by rw [hA] at hy; exact hy, ya⟩⟩
  cases h with
  | derive hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact append _
  | split hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact append _
  | release hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact rel _ (release_releases s _)
  | transfer hs =>
    rename_i src dst
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
    refine ⟨by simp [transferEff], fun x _ ⟨y, hy, ya⟩ => ?_⟩
    rw [transfer_A_get] at hy
    obtain ⟨y₀, hy₀, rfl⟩ := Option.map_eq_some_iff.1 hy
    exact ⟨y₀, hy₀, by split at ya <;> exact ya⟩
  | depend hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact same _ rfl
  | read hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact same _ rfl
  | write hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact same _ rfl
  | writeShared hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact same _ rfl
  | pin hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact same _ rfl
  | unpin hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact same _ rfl
  | enter hs =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
    refine ⟨by simp [enterEff, length_mapI], fun x hx ⟨y, hy, ya⟩ => ?_⟩
    rw [enter_lt hx] at hy
    obtain ⟨y₀, hy₀, rfl⟩ := Option.map_eq_some_iff.1 hy
    exact ⟨y₀, hy₀, by split at ya <;> exact ya⟩
  | exit hs =>
    obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 hs
    unfold ExitPre at hpre
    split at hpre
    · rename_i f F₀ hF
      refine ⟨by rw [exitEff_eq hF]; simp [length_mapI], fun x _ ⟨y, hy, ya⟩ => ?_⟩
      rw [exit_A_get hF] at hy
      obtain ⟨y₀, hy₀, rfl⟩ := Option.map_eq_some_iff.1 hy
      exact ⟨y₀, hy₀, exitG_active' hy₀ ya⟩
    · exact hpre.elim
  | endUse hs =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
    exact rel _ ((endUseS_releases s _).trans cleanup_releases)
  | free hs =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
    exact rel _ ((freeS_releases s _).trans cleanup_releases)
  | alloc hs => cases hs; exact append _
  | store hs =>
    rename_i a p
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
    have sk := store_skel s a p
    exact ⟨Nat.le_of_eq sk.1.symm, fun x _ h => sk.active.1 h⟩

/-- A kernel step preserves the arena invariants of the state (D3): the entries do not change, a
live entry was live before, and `arena_inv_preserved` carries its invariant over. -/
theorem kstep_preserves_arenas {k : K} {s s' : S3} (hwf : WF3 s) (hinv : Inv3base s)
    (hw : ArenasWF s) (hai : ArenasInv s) (h : KStep k s s') : ArenasWF s' ∧ ArenasInv s' := by
  obtain ⟨hlen, hact⟩ := h.active_back
  refine ⟨fun ar har => ?_, fun ar har ha => ?_⟩
  · rw [h.arenas] at har; exact Nat.lt_of_lt_of_le (hw ar har) hlen
  · rw [h.arenas] at har
    exact arena_inv_preserved hwf hinv (hai ar har (hact _ (hw ar har) ha)) h ha

/-- `newArena` preserves `WF3`, `Inv3` and the arena invariants (D3; F1): it only adds an entry,
which satisfies `ArenaInv` by its preconditions. -/
theorem newArena_preserves {s s' : S3} {st i : Nat} (hwf : WF3 s) (hinv : Inv3 s)
    (hw : ArenasWF s) (hai : ArenasInv s) (h : NewArenaStep st i s (.ok s')) :
    WF3 s' ∧ Inv3 s' ∧ ArenasWF s' ∧ ArenasInv s' := by
  obtain ⟨⟨-, hu, hint, -, h1, h2, -⟩, rfl⟩ := Guarded.ok_iff.1 h
  obtain ⟨y, hy⟩ : ∃ y, s.A[i]? = some y := by
    unfold OptP at hint; split at hint
    · exact ⟨_, ‹_›⟩
    · exact hint.elim
  rw [hy] at hint; obtain ⟨-, hm, hpl⟩ := hint
  obtain ⟨v, hv⟩ : ∃ v, y.holder = .place v := by
    cases hh : y.holder with
    | place v => exact ⟨v, rfl⟩
    | frame f => rw [hh] at hpl; cases hpl
  refine ⟨hwf.arenas _, hinv.arenas _, fun ar har => ?_, fun ar har ha => ?_⟩
  · rcases List.mem_append.1 har with har | har
    · exact hw ar har
    · rw [List.mem_singleton.1 har]; exact lt_of_getElem? hy
  · rcases List.mem_append.1 har with har | har
    · exact (hai ar har ha).arenas _
    · rw [List.mem_singleton.1 har]
      exact ⟨fun l hl => hl, fun _ he => (by cases he), List.Pairwise.nil, fun _ he => (by cases he),
        fun _ he => (by cases he), hu.lt, ⟨y, v, hy, hm, hv⟩, fun l => ⟨h1 l, h2 l⟩⟩

/-- The arena invariant of another arena carries over to `issue` (D3): `issue` adds an authority
and writes the metadata, and changes no place. -/
theorem arenaInv_issue {s : S3} {ar ar₂ : Arena} {region : List Nat} {dst : Nat}
    (hai : ArenaInv s ar₂) : ArenaInv (issueEff s ar region dst).1 ar₂ := by
  obtain ⟨yi, vi, hyi, -, hhi⟩ := hai.2.2.2.2.2.2.1
  have hi := lt_of_getElem? hyi
  exact arenaInv_transport hai (fun j y hy => ⟨y, by
      show (s.addAuth _).A[j]? = _; rw [addAuth_lt (lt_of_getElem? hy)]; exact hy,
      rfl, rfl, id, id⟩) (Nat.le_refl _)
    (fun y y' v h1 h2 h3 => ⟨v, by
      have h2' : (s.addAuth _).A[ar₂.internal]? = some y' := h2
      rw [addAuth_lt hi, h1] at h2'; cases h2'; exact h3⟩) (fun _ => Iff.rfl)

/-- `arena.issue` on an entry of the state preserves `WF3`, `Inv3` and the arena invariants
(MM-03.3 §6; A10; D3). -/
theorem issueAt_preserves {k : K} {s s' : S3} {i via dst : Nat} {region : List Nat}
    (hwf : WF3 s) (hinv : Inv3 s) (hw : ArenasWF s) (hai : ArenasInv s)
    (h : IssueAt k i via region dst s (.ok s')) :
    WF3 s' ∧ Inv3 s' ∧ ArenasWF s' ∧ ArenasInv s' := by
  cases h with
  | @ok ar s₁ ar₁ har hst =>
  have hst' := hst
  cases hst with
  | ok hp hav hright =>
  have hlive : s.Active ar.internal := hp.2.1
  have hmem : ar ∈ s.arenas := List.mem_of_getElem? har
  obtain ⟨hwf₁, hinv₁, hai₁⟩ := arena_issue_preserves_disjointness hwf hinv.base (hai ar hmem hlive) hst'
  have hao := issue_preserves_anchorOrder hinv.ao hst'
  have hnd := issue_preserves_noDangling hinv.nd hst'
  have hlen : (issueEff s ar region dst).1.A.length = s.A.length + 1 := by
    simp [issueEff, S3.addAuth]
  refine ⟨hwf₁.arenas _, (show Inv3 (issueEff s ar region dst).1 from ⟨hinv₁, hao, hnd⟩).arenas _,
    fun ar₂ har₂ => ?_, fun ar₂ har₂ ha => ?_⟩
  · show ar₂.internal < (issueEff s ar region dst).1.A.length
    rw [hlen]
    rcases List.mem_or_eq_of_mem_set har₂ with har₂ | rfl
    · have := hw ar₂ har₂; omega
    · have := hw ar hmem; exact Nat.lt_succ_of_lt this
  · rcases List.mem_or_eq_of_mem_set har₂ with har₂ | rfl
    · have hl := hw ar₂ har₂
      have ha' : s.Active ar₂.internal := by
        obtain ⟨y, hy, ya⟩ := ha
        exact ⟨y, by
          have hy' : (s.addAuth _).A[ar₂.internal]? = some y := hy
          rwa [addAuth_lt hl] at hy', ya⟩
      exact (arenaInv_issue (hai ar₂ har₂ ha')).arenas _
    · exact hai₁.arenas _

/-- `arena.reset` on an entry of the state preserves `WF3`, `Inv3` and the arena invariants
(MM-03.3 §6; A10; D3): it only writes the metadata and the logical state of the entry. -/
theorem resetAt_preserves {k : K} {s s' : S3} {i via : Nat}
    (hwf : WF3 s) (hinv : Inv3 s) (hw : ArenasWF s) (hai : ArenasInv s)
    (h : ResetAtStep k i via s (.ok s')) :
    WF3 s' ∧ Inv3 s' ∧ ArenasWF s' ∧ ArenasInv s' := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  unfold ResetAtPre at hpre
  unfold resetAtEff
  cases har : s.arenas[i]? with
  | none => rw [har] at hpre; exact hpre.elim
  | some ar =>
    rw [har] at hpre; obtain ⟨hlive, hrp⟩ := hpre
    have hmem : ar ∈ s.arenas := List.mem_of_getElem? har
    have hst : ResetStep k ar via s (.ok (resetEff s ar)) := Guarded.ok_iff.2 ⟨hrp, rfl⟩
    obtain ⟨hwf₁, hinv₁⟩ := arena_reset_preserves_wf hwf hinv.base hst
    obtain ⟨hai₁, -, -⟩ := arena_reset_preserves (hai ar hmem hlive) hst
    have hao := reset_preserves_anchorOrder hinv.ao hst
    have hnd := reset_preserves_noDangling hinv.nd hst
    refine ⟨hwf₁.arenas _, (show Inv3 (resetEff s ar).1 from ⟨hinv₁, hao, hnd⟩).arenas _,
      fun ar₂ har₂ => ?_, fun ar₂ har₂ ha => ?_⟩
    · rcases List.mem_or_eq_of_mem_set har₂ with har₂ | rfl
      · exact hw ar₂ har₂
      · exact hw ar hmem
    · rcases List.mem_or_eq_of_mem_set har₂ with har₂ | rfl
      · exact hai ar₂ har₂ ha
      · exact hai₁.arenas _

/-- `arena_entry_follows_transfer` (D3; A4; F1): when the arena value, the place that holds
`internal`, is transferred, the entry stays live and satisfies `ArenaInv`, and the destination
becomes its arena value. -/
theorem arena_entry_follows_transfer {k : K} {s s' : S3} {ar : Arena} {v dst : Nat}
    (hwf : WF3 s) (hinv : Inv3base s) (hai : ArenaInv s ar) (hlive : s.Active ar.internal)
    (hv : arenaValue s ar = some v) (h : TransferStep k v dst s (.ok s')) :
    s'.Active ar.internal ∧ ArenaInv s' ar ∧ arenaValue s' ar = some dst := by
  have hk : KStep k s s' := .transfer h
  obtain ⟨⟨hsrc, -⟩, rfl⟩ := Guarded.ok_iff.1 h
  have hlive' : (transferEff s v dst).Active ar.internal := by
    obtain ⟨y, hy, ya⟩ := hlive
    refine ⟨if heldIn s.P v y.holder then { y with holder := .place dst } else y,
      by rw [transfer_A_get, hy]; rfl, ?_⟩
    split <;> exact ya
  refine ⟨hlive', arena_inv_preserved hwf hinv hai hk hlive', ?_⟩
  obtain ⟨y, hy, hhv⟩ : ∃ y, s.A[ar.internal]? = some y ∧ y.holder = .place v := by
    unfold arenaValue at hv
    cases hy : s.A[ar.internal]? with
    | none => rw [hy] at hv; cases hv
    | some y =>
      rw [hy] at hv; simp only at hv
      split at hv
      · rename_i w hw; cases hv; exact ⟨y, rfl, hw⟩
      · cases hv
  have hh : heldIn s.P v y.holder := by rw [hhv]; exact ⟨hsrc.lt, .inl rfl⟩
  unfold arenaValue
  rw [transfer_A_get, hy]
  simp [hh]

/-- `arena_dies_with_internal` (D3; A6; F1): after `endUse` of the arena value, the place that
holds `internal`, `internal` is released: the entry is no longer live. -/
theorem arena_dies_with_internal {k : K} {s s' : S3} {ar : Arena} {v : Nat}
    (hv : arenaValue s ar = some v) (h : EndUseStep k v s (.ok s')) :
    ¬ s'.Active ar.internal := by
  obtain ⟨⟨hu, -⟩, rfl⟩ := Guarded.ok_iff.1 h
  rintro ⟨z, hz, za⟩
  obtain ⟨hz₀, hnh, -⟩ := endUse_active hz za
  apply hnh
  unfold arenaValue at hv
  rw [hz₀] at hv; simp only at hv
  split at hv
  · rename_i w hw; cases hv; rw [hw]; exact ⟨hu.lt, .inl rfl⟩
  · cases hv

/-- A chain contains the chain of each of its elements, for a link to smaller indices. -/
theorem chain_trans {org : Nat → Option Nat} (hlt : ∀ i o, org i = some o → o < i) :
    ∀ n i, i < n → ∀ r, r ∈ chain org i → ∀ o ∈ chain org r, o ∈ chain org i
  | 0, _, h, _, _, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, i, hi, r, hr, o, ho => by
    cases hp : org i with
    | none => rw [chain_none hp] at hr; simp at hr
    | some p =>
      have hpi := hlt i p hp
      rw [chain_cons hp hpi] at hr ⊢
      rcases List.mem_cons.1 hr with rfl | hr
      · exact List.mem_cons_of_mem _ ho
      · exact List.mem_cons_of_mem _ (chain_trans hlt n p (by omega) r hr o ho)

theorem exists_lt_not_of_not_forall {p : Nat → Prop} [DecidablePred p] :
    ∀ n, ¬ (∀ r < n, p r) → ∃ r < n, ¬ p r
  | 0, h => absurd (fun r hr => absurd hr (Nat.not_lt_zero r)) h
  | n + 1, h => by
    by_cases hn : p n
    · obtain ⟨r, hr, hp⟩ := exists_lt_not_of_not_forall n fun h' => h fun r hr => by
        rcases Nat.lt_succ_iff_lt_or_eq.1 hr with hr | rfl
        · exact h' r hr
        · exact hn
      exact ⟨r, by omega, hp⟩
    · exact ⟨n, Nat.lt_succ_self n, hn⟩

/-- Every place of a well-formed state has a leaf (MM-03.3.2): its parts have larger indices
(`WF3`), so the search for a part without part terminates. -/
theorem exists_mem_footprint {s : S3} (hw : WF3 s) :
    ∀ n q, s.P.length - q < n → q < s.P.length → ∃ l, l ∈ footprint s.P q
  | 0, _, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, q, hn, hq => by
    by_cases hleaf : isLeaf s.P q
    · exact ⟨q, mem_footprint.2 ⟨hq, hleaf, hq, .inl rfl⟩⟩
    · obtain ⟨r, hr, hpr⟩ := exists_lt_not_of_not_forall _ hleaf
      have hpr : parentOf s.P r = some q := Decidable.of_not_not hpr
      have hlt : ∀ i o, parentOf s.P i = some o → o < i := fun i o h => by
        simp only [parentOf] at h
        cases hi : s.P[i]? with
        | none => rw [hi] at h; cases h
        | some pl => rw [hi] at h; obtain ⟨-, -, hlt, -⟩ := hw.parts i pl o hi h; exact hlt
      have hqr := hlt r q hpr
      obtain ⟨l, hl⟩ := exists_mem_footprint hw n r (by omega) hr
      obtain ⟨hlP, hleaf', -, hlr⟩ := mem_footprint.1 hl
      refine ⟨l, mem_footprint.2 ⟨hlP, hleaf', hlP, .inr ?_⟩⟩
      have hrq : q ∈ chain (parentOf s.P) r := by rw [chain_cons hpr hqr]; exact List.mem_cons_self ..
      rcases hlr with rfl | hlr
      · exact hrq
      · exact chain_trans hlt (l + 1) l (Nat.lt_succ_self l) r hlr q hrq

/-! ## Reachability (MM-03.3 §10) -/

/-- States reached from the initial state with the static storage `statics` (D1) by `ok`
transitions of the kernel operations, of the arena operations `newArena`, `issue` and `reset`
(D3), and of `store` (F4), for fixed contracts `k` (MM-03.3.8). The static storage is well-formed (`ShapeOK`, C6). -/
inductive Reachable (k : K) (statics : Statics) : S3 → Prop where
  | init : ShapeOK 0 (statics.map (·.1)) → Reachable k statics (S3.init statics)
  | derive {s s' : S3} {src q : Nat} {m : Mode} :
      Reachable k statics s → DeriveStep src q m s (.ok s') → Reachable k statics s'
  | split {s s' : S3} {src : Nat} {rs : List (List Nat)} :
      Reachable k statics s → SplitStep k src rs s (.ok s') → Reachable k statics s'
  | release {s s' : S3} {a : Nat} : Reachable k statics s → ReleaseStep a s (.ok s') → Reachable k statics s'
  | transfer {s s' : S3} {src dst : Nat} :
      Reachable k statics s → TransferStep k src dst s (.ok s') → Reachable k statics s'
  | depend {s s' : S3} {q x : Nat} : Reachable k statics s → DependStep q x s (.ok s') → Reachable k statics s'
  | enter {s s' : S3} {ps : List Nat} {ls : List (Option Nat × Option Nat × Nat)} :
      Reachable k statics s → EnterStep ps ls s (.ok s') → Reachable k statics s'
  | exit {s s' : S3} : Reachable k statics s → ExitStep k s (.ok s') → Reachable k statics s'
  | read {s s' : S3} {a : Nat} {ls : List Nat} :
      Reachable k statics s → Read3Step a ls s (.ok s') → Reachable k statics s'
  | write {s s' : S3} {a : Nat} {ls : List Nat} :
      Reachable k statics s → Write3Step a ls s (.ok s') → Reachable k statics s'
  | writeShared {s s' : S3} {a : Nat} {ls : List Nat} :
      Reachable k statics s → WriteSharedStep k a ls s (.ok s') → Reachable k statics s'
  | pin {s s' : S3} {p : Nat} : Reachable k statics s → PinStep p s (.ok s') → Reachable k statics s'
  | unpin {s s' : S3} {p : Nat} : Reachable k statics s → UnpinStep k p s (.ok s') → Reachable k statics s'
  | endUse {s s' : S3} {p : Nat} : Reachable k statics s → EndUseStep k p s (.ok s') → Reachable k statics s'
  | free {s s' : S3} {p auth : Nat} :
      Reachable k statics s → FreeStep k p auth s (.ok s') → Reachable k statics s'
  | alloc {s s' : S3} {pr ow : Nat} {ls : List (Option Nat × Option Nat × Nat)} :
      Reachable k statics s → AllocStep k pr ow ls s (.ok s') → Reachable k statics s'
  | newArena {s s' : S3} {st i : Nat} :
      Reachable k statics s → NewArenaStep st i s (.ok s') → Reachable k statics s'
  | issue {s s' : S3} {i via dst : Nat} {region : List Nat} :
      Reachable k statics s → IssueAt k i via region dst s (.ok s') → Reachable k statics s'
  | reset {s s' : S3} {i via : Nat} :
      Reachable k statics s → ResetAtStep k i via s (.ok s') → Reachable k statics s'
  | store {s s' : S3} {a p : Nat} :
      Reachable k statics s → StoreStep a p s (.ok s') → Reachable k statics s'

/-- Invariants of the reached states (MM-03.3 §10; B8, C1, C2, D3): `WF3`, `Inv3`, arena entries
naming existing authorities (`ArenasWF`) and `ArenaInv` for every live arena. Under `DDSound k`
(MM-03.3.8), used by `split`. -/
theorem reachable_invariants {k : K} (hdd : DDSound k) {statics : Statics} {s : S3}
    (h : Reachable k statics s) : WF3 s ∧ Inv3 s ∧ ArenasWF s ∧ ArenasInv s := by
  have mk : ∀ {s s' : S3}, KStep k s s' → WF3 s ∧ Inv3 s ∧ ArenasWF s ∧ ArenasInv s →
      WF3 s' ∧ Inv3base s' → AnchorOrder s' → NoDangling s' →
      WF3 s' ∧ Inv3 s' ∧ ArenasWF s' ∧ ArenasInv s' :=
    fun hk ih h a d => ⟨h.1, ⟨h.2, a, d⟩,
      kstep_preserves_arenas ih.1 ih.2.1.base ih.2.2.1 ih.2.2.2 hk⟩
  induction h with
  | init hsh =>
    exact ⟨(init_wf statics hsh).1, (init_wf statics hsh).2, fun _ h => by simp [S3.init] at h,
      fun _ h => by simp [S3.init] at h⟩
  | derive _ hs ih =>
    exact mk (.derive hs) ih (derive_preserves ih.1 ih.2.1.base hs)
      (derive_preserves_anchorOrder ih.2.1.ao hs) (derive_preserves_noDangling ih.2.1.nd hs)
  | split _ hs ih =>
    exact mk (.split hs) ih (split_preserves_underDD hdd ih.1 ih.2.1.base hs)
      (split_preserves_anchorOrder ih.2.1.ao hs) (split_preserves_noDangling ih.2.1.nd hs)
  | release _ hs ih =>
    exact mk (.release hs) ih (release_preserves ih.1 ih.2.1.base hs)
      (release_preserves_anchorOrder ih.2.1.ao hs) (release_preserves_noDangling ih.2.1.nd hs)
  | transfer _ hs ih =>
    exact mk (.transfer hs) ih (transfer_preserves ih.1 ih.2.1.base hs)
      (transfer_preserves_anchorOrder ih.1 ih.2.1.ao hs) (transfer_preserves_noDangling ih.2.1.nd hs)
  | depend _ hs ih =>
    exact mk (.depend hs) ih (depend_preserves ih.1 ih.2.1.base hs)
      (depend_preserves_anchorOrder ih.2.1.ao hs) (depend_preserves_noDangling ih.2.1.nd hs)
  | enter _ hs ih =>
    exact mk (.enter hs) ih (enter_preserves ih.1 ih.2.1.base hs)
      (enter_preserves_anchorOrder ih.1 ih.2.1.ao hs) (enter_preserves_noDangling ih.1 ih.2.1.nd hs)
  | exit _ hs ih =>
    exact mk (.exit hs) ih (exit_preserves ih.1 ih.2.1.base hs)
      (exit_preserves_anchorOrder ih.1 ih.2.1.ao hs) (exit_preserves_noDangling ih.1 ih.2.1.nd hs)
  | read _ hs ih => rw [read3_preserves hs]; exact ih
  | write _ hs ih =>
    have hk := KStep.write (k := k) hs
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
    exact mk hk ih (write3_preserves ih.1 ih.2.1.base hs) (write3_preserves_anchorOrder _ ih.2.1.ao)
      (write3_preserves_noDangling _ ih.2.1.nd)
  | writeShared _ hs ih =>
    have hk := KStep.writeShared hs
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
    exact mk hk ih (writeShared_preserves ih.1 ih.2.1.base hs)
      (write3_preserves_anchorOrder _ ih.2.1.ao) (write3_preserves_noDangling _ ih.2.1.nd)
  | pin _ hs ih =>
    have hk := KStep.pin (k := k) hs
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
    exact mk hk ih (pinEff_preserves ih.1 ih.2.1.base) (pinEff_preserves_anchorOrder _ _ ih.2.1.ao)
      (pinEff_preserves_noDangling _ _ ih.2.1.nd)
  | unpin _ hs ih =>
    have hk := KStep.unpin hs
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
    exact mk hk ih (pinEff_preserves ih.1 ih.2.1.base) (pinEff_preserves_anchorOrder _ _ ih.2.1.ao)
      (pinEff_preserves_noDangling _ _ ih.2.1.nd)
  | endUse _ hs ih =>
    exact mk (.endUse hs) ih (endUse_preserves ih.1 ih.2.1.base hs)
      (endUse_preserves_anchorOrder ih.2.1.ao hs)
      (endUse_preserves_noDangling ih.1 ih.2.1.base ih.2.1.nd hs)
  | free _ hs ih =>
    exact mk (.free hs) ih (free_preserves ih.1 ih.2.1.base hs) (free_preserves_anchorOrder ih.2.1.ao hs)
      (free_preserves_noDangling ih.1 ih.2.1.base ih.2.1.nd hs)
  | alloc _ hs ih =>
    exact mk (.alloc hs) ih (alloc_preserves ih.1 ih.2.1.base hs)
      (alloc_preserves_anchorOrder ih.1 ih.2.1.ao hs) (alloc_preserves_noDangling ih.1 ih.2.1.nd hs)
  | newArena _ hs ih => exact newArena_preserves ih.1 ih.2.1 ih.2.2.1 ih.2.2.2 hs
  | issue _ hs ih => exact issueAt_preserves ih.1 ih.2.1 ih.2.2.1 ih.2.2.2 hs
  | reset _ hs ih => exact resetAt_preserves ih.1 ih.2.1 ih.2.2.1 ih.2.2.2 hs
  | store _ hs ih =>
    exact mk (.store hs) ih (store_preserves ih.1 ih.2.1.base hs)
      (store_preserves_anchorOrder ih.1 ih.2.1.ao hs) (store_preserves_noDangling ih.2.1.nd hs)

/-- `reachable_access_invariant` (MM-03.3 §10; B8, C1, C2, D3): every reached state satisfies `WF3`,
`Inv3`, and `ArenaInv` for every live arena. Conditional on the obligation `DDSound k` of
`DeclaredDisjoint` (MM-03.3.8), used by `split`. -/
theorem reachable_access_invariant_underDD {k : K} (hdd : DDSound k) {statics : Statics} {s : S3}
    (h : Reachable k statics s) :
    WF3 s ∧ Inv3 s ∧ ∀ ar ∈ s.arenas, s.Active ar.internal → ArenaInv s ar :=
  let h' := reachable_invariants hdd h
  ⟨h'.1, h'.2.1, h'.2.2.2⟩

/-- `reachable_no_dangling` (C2; MM-03.3 §10; D3): in every reached state, no active authority
covers a leaf of a place that is not usable. Under `DDSound k` (MM-03.3.8). -/
theorem reachable_no_dangling {k : K} (hdd : DDSound k) {statics : Statics} {s : S3}
    (h : Reachable k statics s) :
    NoDangling s :=
  (reachable_access_invariant_underDD hdd h).2.1.nd

/-- `live_arena_storage_usable` (F2): in every reached state, the storage of a live arena is
usable. A corollary of `NoDangling` (C2): `internal` is active and covers the footprint of the
storage (`ArenaInv`, F1), which has a leaf. Under `DDSound k` (MM-03.3.8). -/
theorem live_arena_storage_usable {k : K} (hdd : DDSound k) {statics : Statics} {s : S3}
    (h : Reachable k statics s) : ∀ ar ∈ s.arenas, s.Active ar.internal → s.Usable ar.storage := by
  obtain ⟨hwf, hinv, hai⟩ := reachable_access_invariant_underDD hdd h
  intro ar har ⟨y, hy, ya⟩
  have hi := hai ar har ⟨y, hy, ya⟩
  obtain ⟨l, hl⟩ := exists_mem_footprint hwf (s.P.length + 1) ar.storage (by omega)
    hi.2.2.2.2.2.1
  have hly : l ∈ y.footprint := by
    have := (hi.2.2.2.2.2.2.2 l).2 hl
    simpa [S3.afp, hy] using this
  exact Decidable.byContradiction fun hu => hinv.nd ar.internal y hy ya ar.storage hu l hl hly

/-- `exitFrame_no_dangling` on reached states (MM-03.3 §4, O7; §10), under `DDSound k`
(MM-03.3.8). -/
theorem exitFrame_no_dangling_reachable {k : K} (hdd : DDSound k) {statics : Statics} {s s' : S3} {f : Nat}
    {F₀ : Frames} (hs : Reachable k statics s) (hF : s.F = f :: F₀) (h : ExitStep k s (.ok s')) :
    ∀ q, OwnedByFrame s.P f q → ∀ (j : Nat) (y : Authority), s'.A[j]? = some y →
      y.active = true → ∀ l ∈ footprint s.P q, l ∉ y.footprint :=
  exitFrame_no_dangling (reachable_access_invariant_underDD hdd hs).1 hF h

/-! ## Test cases (MM-03.3 §11 and the tasks of passes 2 and 3)

Each verdict is obtained by `decide` on the precondition of the operation concerned. States are
built from `S3.init` by the effects of operations. Classification of each case (kernel,
abstraction with `K` instantiated, out of kernel) is given in the report. -/

/-- Test contracts: `SharedMutable`, `Pinned`, `ExternalDone`, `Deallocable` given by lists of
leaves or places, `FreeCompat` by a list of pairs; no declared disjointness; every allocation
satisfiable. -/
def KT (sh pinned done dealloc : List Nat) (compat : List (Nat × Nat)) : K :=
  ⟨fun _ _ => False, (· ∈ sh), (· ∈ pinned), (· ∈ done), (· ∈ dealloc),
    fun p a => (p, a) ∈ compat, fun _ _ _ => True⟩

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
instance : ∀ p ls s, Decidable ((KT sh pinned done dealloc compat).Satisfiable p ls s) :=
  fun _ _ _ => instDecidableTrue
end TestContracts

/-- Empty contracts. -/
abbrev K0 : K := KT [] [] [] [] []

theorem KT_dd (sh pinned done dealloc : List Nat) (compat : List (Nat × Nat)) :
    DDSound (KT sh pinned done dealloc compat) := fun _ _ h => h.elim

/-- Entering frame 1 from the initial frame with locals `ls`. -/
def enter1 (ls : List (Option Nat × Option Nat × Nat)) : S3 := enterEff (S3.init []) [] ls

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
    ⟨_, _, rfl, rfl, rfl⟩,
    fun _ => by rw [show c6a.afp ar6.internal = footprint c6a.P ar6.storage by decide]⟩
example : WF3 c6a ∧ Inv3 c6a :=
  let h := reachable_access_invariant_underDD (KT_dd [] [] [] [] [])
    (show Reachable K0 [] c6a from .enter (.init (by decide)) (.ok (by decide)))
  ⟨h.1, h.2.1⟩

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
example : ExitStep K0 c8e (.ok (exitEff c8e)) := .ok (by decide)
example : (exitEff c8e).D 1 = [0] := by decide

/-! ### Case 9: temporary capture of an access by a non-escaping value (expected: allowed) -/

def c9a : S3 := write3Eff (deriveEff (enter1 [(none, none, 0), (none, none, 0)]) 0 0 .observe) [1]
example : DependStep 1 2 c9a (.ok (dependEff c9a 1 2)) := .ok (by decide)
example : ReleaseStep 2 (dependEff c9a 1 2) .reject := .reject (by decide)

/-! ### Case 10: capture of a local access in an escaping value (expected: reject). Caller: 0
result, parameter 1. Callee: 1 local, 2 value capturing access 4 derived from the local. C1 rejects
the `transfer`: the effective anchor of 4 is the root 2 of the local, held by frame 2, and the
dependent moves to the caller (B8 on the effective anchor). Pass 3 accepted the `transfer` and
rejected the exit; the `ExitStep` fact describes the state pass 3 reached. -/

def c10a : S3 := enterEff (deriveEff (enter1 [(none, none, 0)]) 0 0 .modify) [1]
  [(none, none, 0), (none, none, 0)]
def c10b : S3 := write3Eff (deriveEff c10a 2 1 .observe) [2]
def c10c : S3 := transferEff (dependEff c10b 2 4) 2 0
example : DeriveStep 2 1 .observe c10a (.ok (deriveEff c10a 2 1 .observe)) := .ok (by decide)
example : DependStep 2 4 c10b (.ok (dependEff c10b 2 4)) := .ok (by decide)
example : TransferStep K0 2 0 (dependEff c10b 2 4) .reject := .reject (by decide)
example : ExitStep K0 c10c .reject := .reject (by decide)

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
example : ExitStep K0 (transferEff c16c.1 5 4) (.ok c16d) := .ok (by decide)
example : c16d.Active 6 ∧ (c16d.A[6]?).map (·.holder) = some (.place 4) := by decide
example : ResetStep KA c16c.2 0 c16d .reject := .reject (by decide)
example : EndUseStep KA 4 c16d (.ok (endUseEff c16d 4)) := .ok (by decide)
example : ResetStep KA c16c.2 0 (endUseEff c16d 4) (.ok (resetEff (endUseEff c16d 4) c16c.2)) :=
  .ok (by decide)

/-- `exitFrame_no_dangling` on the exit of case 16 (MM-03.3 §7): `WF3` holds before the exit, from
the reached state `c16b`, the arena invariant, and the preservation by `issue` and `transfer`. -/
example : ∀ q, OwnedByFrame (transferEff c16c.1 5 4).P 2 q → ∀ (j : Nat) (y : Authority),
    c16d.A[j]? = some y → y.active = true →
    ∀ l ∈ footprint (transferEff c16c.1 5 4).P q, l ∉ y.footprint := by
  have r0 : Reachable KA [] c16a := .enter (.init (by decide)) (.ok (by decide))
  have r1 : Reachable KA [] c16b :=
    .enter (.derive (.derive r0 (.ok (by decide))) (.ok (by decide))) (.ok (by decide))
  obtain ⟨hw, ⟨hi, -⟩, -⟩ := reachable_access_invariant_underDD (KT_dd [0] [] [] [] []) r1
  have hai : ArenaInv c16b ar16 :=
    ⟨(by decide), (by decide), (by decide), (by decide), fun _ h => (nomatch h), (by decide),
      ⟨_, _, rfl, rfl, rfl⟩,
      fun _ => by rw [show c16b.afp ar16.internal = footprint c16b.P ar16.storage by decide]⟩
  obtain ⟨hw1, hi1, -⟩ := arena_issue_preserves_disjointness hw hi hai
    (show IssueStep KA ar16 3 [2] 5 c16b (.ok c16c.1 c16c.2) from
      .ok (by decide) (by decide) (by decide))
  obtain ⟨hw2, -⟩ := transfer_preserves hw1 hi1
    (show TransferStep KA 5 4 c16c.1 (.ok (transferEff c16c.1 5 4)) from .ok (by decide))
  exact exitFrame_no_dangling hw2 (show (transferEff c16c.1 5 4).F = 2 :: [1, 0] by decide)
    (show ExitStep KA (transferEff c16c.1 5 4) (.ok c16d) from .ok (by decide))

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
example : ExitStep K0 (transferEff (write3Eff n2a [2]) 2 0) (.ok n2b) := .ok (by decide)
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
example : ExitStep K0 (transferEff (write3Eff (write3Eff n3a [1]) [2]) 1 0) (.ok n3b) := .ok (by decide)
example : Read3Step 3 [2] n3b (.ok n3b) := .ok (by decide)

/-- `endUse(p)` with an active derived authority held elsewhere (expected: reject), and with a
usable dependent anchored on `p` (expected: reject). -/
example : EndUseStep K0 0 (deriveEff c13a 0 0 .observe) .reject := .reject (by decide)
example : EndUseStep K0 0 (dependEff c13a 1 0) .reject := .reject (by decide)

/-- `alloc`, `process`, `free` at the end of the frame (`defer`), then `endUse` (expected:
`ok`); `free` during an active access, without a compatible deallocation authority, or of an
arena block (expected: reject). Frame 1: 0 box value, 1 allocator value; in the middle of the
frame, `alloc` with provider 1 and owner 0 creates the storage 2, owned by 0, with root 2 (B5). -/
abbrev KF : K := KT [] [] [] [2] [(2, 7)]
def n6e : S3 := enter1 [(none, none, 0), (none, none, 0)]
def n6a : S3 := write3Eff (allocEff (write3Eff n6e [1]) 1 0 [(none, none, 0)]) [2]
example : Write3Step 1 [1] n6e (.ok (write3Eff n6e [1])) := .ok (by decide)
example : AllocStep KF 1 0 [(none, none, 0)] (write3Eff n6e [1]) (.ok (allocEff (write3Eff n6e [1]) 1 0 [(none, none, 0)])) :=
  .ok (by decide) (by decide)
example : Write3Step 2 [2] (allocEff (write3Eff n6e [1]) 1 0 [(none, none, 0)]) (.ok n6a) := .ok (by decide)
example : FreeStep KF 2 7 n6a (.ok (freeEff n6a 2)) := .ok (by decide)
example : EndUseStep KF 0 (freeEff n6a 2) (.ok (endUseEff (freeEff n6a 2) 0)) := .ok (by decide)
example : FreeStep KF 2 7 (deriveEff n6a 2 2 .observe) .reject := .reject (by decide)
example : FreeStep KF 2 8 n6a .reject := .reject (by decide)
example : FreeStep (KT [0] [] [] [1] [(2, 7)]) 2 7 c6b.1 .reject := .reject (by decide)

/-- `endUse` of a value whose owned storage was not freed (expected: `ok`, reported as a leak):
the storage is logically dead and not freed. -/
example : EndUseStep KF 0 n6a (.ok (endUseEff n6a 0)) := .ok (by decide)
example : (endUseEff n6a 0).dead 2 = true ∧ (endUseEff n6a 0).freed 2 = false := by decide

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
example : ExitStep K0 n9b (.ok (exitEff n9b)) := .ok (by decide)
example : (exitEff n9b).D 1 = [0] := by decide

/-- Return of a value anchored on a local of the callee through two derivations (expected:
reject). Callee of case 10: 4 derived from the root of the local, 5 derived from 4. C1 rejects the
`transfer`, as in case 10; the `ExitStep` fact describes the state pass 3 reached. -/
def n9c : S3 := deriveEff (deriveEff c10a 2 1 .observe) 4 1 .observe
def n9d : S3 := transferEff (dependEff (write3Eff n9c [2]) 2 5) 2 0
example : TransferStep K0 2 0 (dependEff (write3Eff n9c [2]) 2 5) .reject := .reject (by decide)
example : ExitStep K0 n9d .reject := .reject (by decide)

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
def KDD : K := ⟨fun _ _ => True, fun _ => False, fun _ => False, fun _ => False, fun _ => False,
  fun _ _ => False, fun _ _ _ => False⟩
instance : ∀ r r', Decidable (KDD.DeclaredDisjoint r r') := fun _ _ => instDecidableTrue

/-- Without the obligation `DDSound` (MM-03.3.8), `split` (MM-03.3 §3, O2) accepts two overlapping
regions and breaks I1, both in its structural form (A1) and in the effective form of the text
of §2 (pass 1): the hypothesis of `split_preserves_underDD` is needed. -/
theorem split_unsound_without_DD :
    SplitStep KDD 0 [[1], [1]] c3a (.ok (splitEff c3a 0 [[1], [1]])) ∧
    ¬ I1 (splitEff c3a 0 [[1], [1]]) ∧
    ¬ ∀ a b p m₁ m₂, a ≠ b → effective (splitEff c3a 0 [[1], [1]]) a p = some m₁ →
      effective (splitEff c3a 0 [[1], [1]]) b p = some m₂ → Compat m₁ m₂ := by
  refine ⟨.ok (by decide), fun h => ?_, fun h => ?_⟩
  · have := h 1 2 ⟨.modify, some 0, [1], .frame 1, true⟩ ⟨.modify, some 0, [1], .frame 1, true⟩ 1
      (by decide) (by decide) (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide)
    exact absurd this.1 (by decide)
  · exact absurd (h 1 2 1 .modify .modify (by decide) (by decide) (by decide)).1 (by decide)

/-- `exitFrame` rejects the exit of a frame whose local is pinned (B4; pass 2: accepted); the
local is unpinned first. -/
example : ExitStep K0 (pinEff c13a 0 true) .reject := .reject (by decide)
example : EndUseStep K0 0 (pinEff c13a 0 true) .reject := .reject (by decide)

/-- A callee without parameter cannot release a root held by its caller's frame (B3; C4: a root is
never released) (pass 2: accepted). The caller releases its own derived access. For a root held
by a place of the caller, see `rq1`. -/
example : ReleaseStep 0 (enterEff c13a [] [(none, none, 0)]) .reject := .reject (by decide)
example : ReleaseStep 2 (deriveEff c13a 0 0 .observe)
    (.ok (releaseEff (deriveEff c13a 0 0 .observe) 2)) := .ok (by decide)

/-- Reading the owned storage of a value shared in `Observe` (B2): the root of the storage, a
`Modify` authority held by the value, is exercisable at `Observe`, the mode the read requests
(pass 2: rejected). Writing it is rejected while the value is shared. Frame 1: 0 value, 2 owned
storage. -/
example : Read3Step 2 [2] n6a (.ok n6a) := .ok (by decide)
example : Read3Step 2 [2] (deriveEff n6a 0 0 .observe) (.ok (deriveEff n6a 0 0 .observe)) :=
  .ok (by decide)
example : Write3Step 2 [2] (deriveEff n6a 0 0 .observe) .reject := .reject (by decide)

/-- Witness state of `transfer_not_inv3_preserving` (A1; C2): place 0, the source, has a parent
link to the later place 1, which `chain` ignores, so neither 0 nor 1 is a leaf and the source
covers no leaf; place 1 is a part of place 0 with another owner, a frame not on the stack; place 2
is owned by place 1 and anchored on the released root 1 of frame 1; place 3 is the destination. -/
def xferCex : S3 := ⟨[1, 0], 6, [⟨some 1, .frame 1, 0⟩, ⟨some 0, .frame 5, 0⟩, ⟨none, .place 1, 0⟩,
  ⟨none, .frame 1, 0⟩], fun _ => .uninit,
  [⟨.modify, none, [3], .frame 1, true⟩, ⟨.modify, none, [], .frame 1, false⟩],
  fun q => if q = 2 then [1] else [], fun _ => false, fun _ => false, fun _ => false, [], fun _ => []⟩

/-- `transfer` (MM-03.3 §3, O4; A5) does not preserve `Inv3` without `WF3` (A1; C2): a part with
another owner than its parent (excluded by `WF3`) is not usable while its parent is; a place owned
by that part is not usable either and keeps an invalid anchor. The transfer gives that place to
the destination: it becomes usable with an invalid anchor. -/
theorem transfer_not_inv3_preserving :
    Inv3 xferCex ∧ TransferStep K0 0 3 xferCex (.ok (transferEff xferCex 0 3)) ∧
      ¬ I3 (transferEff xferCex 0 3) := by
  refine ⟨⟨⟨fun a b x y p hab ha hb _ _ xp yp _ _ => ?_, fun b y a hb ho => ?_,
    fun q hq z hz => ?_, i4_always _⟩, fun q hq z hz => ?_, noDangling_iff.2 (by decide)⟩,
    .ok (by decide), fun h => ?_⟩
  · have h1 := lt_of_getElem? ha; have h2 := lt_of_getElem? hb
    simp [xferCex] at h1 h2
    obtain rfl | rfl : a = 0 ∨ a = 1 := by omega
    all_goals obtain rfl | rfl : b = 0 ∨ b = 1 := by omega
    all_goals first | exact absurd rfl hab | (simp [xferCex] at ha hb; subst ha hb; simp at xp yp)
  · have := lt_of_getElem? hb; simp [xferCex] at this
    obtain rfl | rfl : b = 0 ∨ b = 1 := by omega
    all_goals simp [xferCex] at hb; subst hb; cases ho
  · cases Nat.decEq q 2 with
    | isTrue e => subst e; exact absurd hq (by decide)
    | isFalse e => simp [xferCex, e] at hz
  · cases Nat.decEq q 2 with
    | isTrue e => subst e; exact absurd hq (by decide)
    | isFalse e => simp [xferCex, e] at hz
  · exact absurd (h 2 (by decide) 1 (by decide)) (by decide)

/-- The witness of `transfer_not_inv3_preserving` breaks the parts clause of `WF3` and satisfies
all its other clauses, those of B1 and A4 included: the parts clause is the one needed. -/
example : (∀ (b : Nat) (y : Authority) (a : Nat), xferCex.A[b]? = some y → y.origin = some a →
      a < b) ∧
    (∀ (a : Nat) (x : Authority), xferCex.A[a]? = some x → ∀ l ∈ x.footprint,
      l < xferCex.P.length) ∧
    xferCex.F ≠ [] ∧ xferCex.F.Nodup ∧ (∀ f ∈ xferCex.F, f < xferCex.nF) ∧
    (∀ (q : Nat) (pl : Place) (f : Nat), xferCex.P[q]? = some pl → pl.owner = .frame f →
      f < xferCex.nF) ∧
    (∀ (q : Nat) (pl : Place) (o : Nat), xferCex.P[q]? = some pl → pl.owner = .place o →
      o < xferCex.P.length) ∧
    (∀ (a : Nat) (y : Authority), xferCex.A[a]? = some y → y.active = true →
      HolderLive xferCex y.holder) ∧
    RootsDisjoint xferCex.P ∧ RootChain xferCex ∧ RootHeld xferCex ∧
    ¬ (∀ (q : Nat) (pl : Place) (r : Nat), xferCex.P[q]? = some pl → pl.parent = some r →
      ∃ pr : Place, xferCex.P[r]? = some pr ∧ r < q ∧ pr.owner = pl.owner ∧
        xferCex.dead r = xferCex.dead q) := by
  refine ⟨?_, ?_, by decide, by decide, by decide, ?_, ?_, ?_, rootsDisjoint_always _, ?_, ?_, ?_⟩
  · intro b y a hb ho
    have := lt_of_getElem? hb; simp [xferCex] at this
    obtain rfl | rfl : b = 0 ∨ b = 1 := by omega
    all_goals simp [xferCex] at hb; subst hb; cases ho
  · intro a x ha l hl
    have := lt_of_getElem? ha; simp [xferCex] at this
    obtain rfl | rfl : a = 0 ∨ a = 1 := by omega
    all_goals simp [xferCex] at ha; subst ha; simp at hl <;> (subst hl; decide)
  · intro q pl f hq ho
    have := lt_of_getElem? hq; simp [xferCex] at this
    obtain rfl | rfl | rfl | rfl : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 := by omega
    all_goals (simp [xferCex] at hq; subst hq; cases ho; try decide)
  · intro q pl o hq ho
    have := lt_of_getElem? hq; simp [xferCex] at this
    obtain rfl | rfl | rfl | rfl : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 := by omega
    all_goals (simp [xferCex] at hq; subst hq; cases ho; try decide)
  · intro a y ha hy
    have := lt_of_getElem? ha; simp [xferCex] at this
    obtain rfl | rfl : a = 0 ∨ a = 1 := by omega
    all_goals simp [xferCex] at ha; subst ha; first | decide | simp at hy
  · intro a y l ha hl _
    have := lt_of_getElem? ha; simp [xferCex] at this
    obtain rfl | rfl : a = 0 ∨ a = 1 := by omega
    · simp [xferCex] at ha; subst ha; simp at hl; subst hl
      exact ⟨0, _, 3, .inl rfl, rfl, rfl, by decide, by decide, fun l' => by
        rw [show footprint xferCex.P 3 = [3] by decide]⟩
    · simp [xferCex] at ha; subst ha; simp at hl
  · intro x z l r hx _ hl hr hlr
    have := lt_of_getElem? hx; simp [xferCex] at this
    obtain rfl | rfl : x = 0 ∨ x = 1 := by omega
    · simp [xferCex] at hx; subst hx; simp at hl; subst hl
      obtain rfl := rootOf_unique hr (show RootPlace xferCex.P 3 by decide) hlr (by decide)
      exact ⟨_, rfl, rfl⟩
    · simp [xferCex] at hx; subst hx; simp at hl
  · intro h; obtain ⟨pr, hpr, -, ho, -⟩ := h 1 ⟨some 0, .frame 5, 0⟩ 0 rfl rfl
    simp [xferCex] at hpr; subst hpr; simp at ho

/-- The witness of `transfer_not_inv3_preserving` in passes 2 and 3: place 1 is a part of place 0
with another owner, a frame not on the stack; place 2 is owned by place 1 and anchored on the
released root 2 of frame 1 (anchored on a missing authority 5 before C1); place 3 is the
destination. -/
def xferNd : S3 := ⟨[1, 0], 6, [⟨none, .frame 1, 0⟩, ⟨some 0, .frame 5, 0⟩, ⟨none, .place 1, 0⟩,
  ⟨none, .frame 1, 0⟩], fun l => if l = 1 then .init else .uninit,
  [⟨.modify, none, [1], .frame 1, true⟩, ⟨.modify, none, [3], .frame 1, true⟩,
    ⟨.modify, none, [], .frame 1, false⟩],
  fun q => if q = 2 then [2] else [], fun _ => false, fun _ => false, fun _ => false, [], fun _ => []⟩

/-- `transfer` (MM-03.3 §3, O4; A5) does not preserve `Inv3base ∧ AnchorOrder`, the `Inv3` of
pass 3, without `WF3` (A1): the transfer gives place 2 to the destination, where it becomes usable
with an invalid anchor. The state breaks `NoDangling` (C2): the authority on the source covers the
leaf of the part 1, which is not usable. -/
example :
    (Inv3base xferNd ∧ AnchorOrder xferNd) ∧ ¬ NoDangling xferNd ∧
      TransferStep K0 0 3 xferNd (.ok (transferEff xferNd 0 3)) ∧
      ¬ I3 (transferEff xferNd 0 3) := by
  refine ⟨⟨⟨fun a b x y p hab ha hb _ _ xp yp _ _ => ?_, fun b y a hb ho => ?_,
    fun q hq z hz => ?_, i4_always _⟩, fun q hq z hz => ?_⟩,
    fun h => absurd (h 0 _ rfl rfl 1 (by decide) 1 (by decide)) (by decide), .ok (by decide),
    fun h => ?_⟩
  · have h1 := lt_of_getElem? ha; have h2 := lt_of_getElem? hb
    simp [xferNd] at h1 h2
    obtain rfl | rfl | rfl : a = 0 ∨ a = 1 ∨ a = 2 := by omega
    all_goals obtain rfl | rfl | rfl : b = 0 ∨ b = 1 ∨ b = 2 := by omega
    all_goals first | exact absurd rfl hab |
      (simp [xferNd] at ha hb; subst ha hb; simp at xp yp <;> omega)
  · have := lt_of_getElem? hb; simp [xferNd] at this
    obtain rfl | rfl | rfl : b = 0 ∨ b = 1 ∨ b = 2 := by omega
    all_goals simp [xferNd] at hb; subst hb; cases ho
  · cases Nat.decEq q 2 with
    | isTrue e => subst e; exact absurd hq (by decide)
    | isFalse e => simp [xferNd, e] at hz
  · cases Nat.decEq q 2 with
    | isTrue e => subst e; exact absurd hq (by decide)
    | isFalse e => simp [xferNd, e] at hz
  · exact absurd (h 2 (by decide) 2 (by decide)) (by decide)

/-- With a duplicated frame on the stack (excluded by `WF3`), `exitFrame` (MM-03.3 §4, O7; A4)
keeps active an authority held by the exited frame: the hypothesis `s.F.Nodup` of
`exitFrame_releases_all` is needed. -/
theorem exit_duplicate_frame :
    let s : S3 := { enter1 [(none, none, 0)] with F := [1, 1, 0] }
    ExitStep K0 s (.ok (exitEff s)) ∧
      (exitEff s).A[0]? = some ⟨.modify, none, [0], .frame 1, true⟩ := by
  intro s; exact ⟨.ok (by decide), by decide⟩

/-- Adding an authority held by a holder that is not live breaks the possession clause of `WF3`
(A4): the hypothesis `HolderLive s hd` of `addAuth_preserves` is needed. -/
theorem addAuth_needs_live_holder :
    let s : S3 := enter1 [(none, none, 0)]
    WF3 s ∧ Inv3base s ∧ Allows (effective s 0 0) .observe ∧
      ¬ WF3 (s.addAuth ⟨.observe, some 0, [0], .frame 7, true⟩) := by
  intro s
  have h := reachable_access_invariant_underDD (KT_dd [] [] [] [] [])
    (show Reachable K0 [] s from .enter (.init (by decide)) (.ok (by decide)))
  refine ⟨h.1, h.2.1.base, by decide, fun h' => ?_⟩
  exact absurd (h'.poss 1 ⟨.observe, some 0, [0], .frame 7, true⟩ (by decide) rfl) (by decide)

/-- A frame exit leaves owned storage unreleased (A6, leak): the owned storage 2 of the box value
0 stops being usable at `exitFrame` (MM-03.3 §4, O7) without `free`; nothing requires its
release. -/
example : ExitStep K0 n6a (.ok (exitEff n6a)) := .ok (by decide)
example : ¬ (exitEff n6a).Usable 2 ∧ (exitEff n6a).freed 2 = false := by decide

/-- `free` after the end of the owner value is rejected (A6): the owned storage is dead. A
forgotten `free` cannot follow `endUse`. -/
example : FreeStep KF 2 7 (endUseEff n6a 0) .reject := .reject (by decide)

/-- An arena value cannot end while an issued block is live (A6, A10); once its blocks have ended,
it ends, and its storage is dead and not freed (leak). -/
example : EndUseStep KA 0 c6b.1 .reject := .reject (by decide)
example : EndUseStep KA 0 n10a (.ok (endUseEff n10a 0)) := .ok (by decide)
example : (endUseEff n10a 0).dead 1 = true ∧ (endUseEff n10a 0).freed 1 = false := by decide

/-! ### Witnesses of the final review -/

/-- `endUse` and `free` (A6) reject an active access derived from an authority that `cleanup`
releases with its dead holder (MM-03.3 §3, O3.2). Frame 1: 0 value `p`, 1 storage owned by 0 (block
destination), 2 arena value, 3 arena storage owned by 2 with parts 4, 5; the block 4 is held by
place 1, and access 5, held by the frame, is derived from it. -/
abbrev KCG : K := KT [2] [] [] [] []
def cg0 : S3 := enter1 [(none, none, 0), (none, some 0, 0), (none, none, 0), (none, some 2, 0),
  (some 3, some 2, 0), (some 3, some 2, 0)]
def arCG : Arena := ⟨3, 3, [4, 5], []⟩
def cg1 : S3 := deriveEff (issueEff cg0 arCG [4] 1).1 4 4 .observe
example : IssueStep KCG arCG 2 [4] 1 cg0 (.ok (issueEff cg0 arCG [4] 1).1 (issueEff cg0 arCG [4] 1).2) :=
  .ok (by decide) (by decide) (by decide)
example : DeriveStep 4 4 .observe (issueEff cg0 arCG [4] 1).1 (.ok cg1) := .ok (by decide)
example : EndUseStep KCG 0 cg1 .reject := .reject (by decide)

/-- Same shape for `free`: 0 value, 1 owned root (freed), 2 storage owned by 1 (block
destination), 3 arena value, 4 arena storage with parts 5, 6. -/
abbrev KCF : K := KT [3] [] [] [1] [(1, 7)]
def cf0 : S3 := enter1 [(none, none, 0), (none, some 0, 0), (none, some 1, 0), (none, none, 0),
  (none, some 3, 0), (some 4, some 3, 0), (some 4, some 3, 0)]
def arCF : Arena := ⟨4, 4, [5, 6], []⟩
def cf1 : S3 := deriveEff (issueEff cf0 arCF [5] 2).1 5 5 .observe
example : IssueStep KCF arCF 3 [5] 2 cf0 (.ok (issueEff cf0 arCF [5] 2).1 (issueEff cf0 arCF [5] 2).2) :=
  .ok (by decide) (by decide) (by decide)
example : DeriveStep 5 5 .observe (issueEff cf0 arCF [5] 2).1 (.ok cf1) := .ok (by decide)
example : FreeStep KCF 1 7 cf1 .reject := .reject (by decide)

/-- `transfer` (MM-03.3 §3, O4.6; MM-03.3.6; A5) checks non-escape for the anchors of the owned
storage, whose frame changes with the value. Caller frame 1: 0 result, parameter 1. Callee
frame 2: 1 value, 2 storage owned by 1 and anchored on the root 4 of the callee local 3. -/
def od0 : S3 := enterEff (deriveEff (enter1 [(none, none, 0)]) 0 0 .modify) [1]
  [(none, none, 0), (none, some 1, 0), (none, none, 0)]
def od1 : S3 := dependEff (write3Eff od0 [1]) 2 4
example : DependStep 2 4 (write3Eff od0 [1]) (.ok od1) := .ok (by decide)
example : TransferStep K0 1 0 od1 .reject := .reject (by decide)

/-- Non-escape is read after the transfer (B7; MM-03.3 §3, O4.6): a value anchored on the root 3 of
its own owned storage, held by the value, is returned (pass 2: rejected); so is the same value
anchored on an access 5 derived from that root, and after the exit its anchor is the root 3, held
by the caller's place 0. Callee frame 2: 1 value, 2 storage owned by 1, 3 local. -/
def ne0 : S3 := write3Eff (write3Eff od0 [1]) [2]
example : TransferStep K0 1 0 (dependEff ne0 1 3) (.ok (transferEff (dependEff ne0 1 3) 1 0)) :=
  .ok (by decide)
def ne1 : S3 := dependEff (deriveEff ne0 3 2 .observe) 1 5
example : TransferStep K0 1 0 ne1 (.ok (transferEff ne1 1 0)) := .ok (by decide)
example : ExitStep K0 (transferEff ne1 1 0) (.ok (exitEff (transferEff ne1 1 0))) := .ok (by decide)
example : (exitEff (transferEff ne1 1 0)).D 0 = [3] ∧
    ((exitEff (transferEff ne1 1 0)).A[3]?).map (·.holder) = some (.place 0) := by decide

/-- The anchors of a containing value stay with it when a part is transferred (MM-03.3 §3, O4;
MM-03.3.6). Frame 1: 0 value with parts 1 and 2, 3 local, 4 destination; access 3 observes the
local; the value at 0 depends on it. After the part 1 is moved to 4 and the value at 0 ends, the
access is released while the moved value is still readable. -/
def pt0 : S3 := enter1 [(none, none, 0), (some 0, none, 0), (some 0, none, 0), (none, none, 0),
  (none, none, 0)]
def pt1 : S3 := dependEff (deriveEff (write3Eff (write3Eff pt0 [1, 2]) [3]) 1 3 .observe) 0 3
def pt2 : S3 := transferEff pt1 1 4
example : TransferStep K0 1 4 pt1 (.ok pt2) := .ok (by decide)
example : pt2.D 4 = [] ∧ pt2.D 0 = [3] := by decide
example : ReleaseStep 3 pt2 .reject := .reject (by decide)
example : EndUseStep K0 0 pt2 (.ok (endUseEff pt2 0)) := .ok (by decide)
example : ReleaseStep 3 (endUseEff pt2 0) (.ok (releaseEff (endUseEff pt2 0) 3)) := .ok (by decide)
example : Read3Step 2 [4] (releaseEff (endUseEff pt2 0) 3) (.ok (releaseEff (endUseEff pt2 0) 3)) :=
  .ok (by decide)

/-- `free` of an owned root that owns storage itself leaves that storage dead and not freed (A6,
leak), and it can no longer be freed. Frame 1: 0 value, 1 storage owned by 0, 2 storage owned by
1. Freeing 2 first, then 1, leaves no leak. -/
abbrev KFL : K := KT [] [] [] [1, 2] [(1, 7), (2, 7)]
def fl0 : S3 := write3Eff (write3Eff (enter1 [(none, none, 0), (none, some 0, 0), (none, some 1, 0)])
  [1]) [2]
example : FreeStep KFL 1 7 fl0 (.ok (freeEff fl0 1)) := .ok (by decide)
example : ¬ (freeEff fl0 1).Usable 2 ∧ (freeEff fl0 1).freed 2 = false ∧ OwnedRoot (freeEff fl0 1) 2 :=
  by decide
example : FreeStep KFL 2 7 (freeEff fl0 1) .reject := .reject (by decide)
example : FreeStep KFL 2 7 fl0 (.ok (freeEff fl0 2)) := .ok (by decide)
example : FreeStep KFL 1 7 (freeEff fl0 2) (.ok (freeEff (freeEff fl0 2) 1)) := .ok (by decide)

/-- The pass-1 statement `canWrite3_iff` is false on the pass-2 definitions: in a reached state,
so under I1, the caller's root has effective `Modify` and valid dependencies on leaf 0, yet
`canWrite3` fails because the root is not exercisable from the callee (A2). -/
example : ¬ (∀ {s : S3}, I1 s → ∀ {a : Nat} {ls : List Nat},
    canWrite3 s a ls ↔ ∀ p ∈ ls, effective s a p = some .modify ∧ DepsValid s p) := by
  intro h
  have hr : Reachable K0 [] (enterEff c13a [] [(none, none, 0)]) :=
    .enter (ps := []) (ls := [(none, none, 0)]) (.write (a := 0) (ls := [0])
      (.enter (ps := []) (ls := [(none, none, 0), (none, none, 0)]) (.init (by decide)) (.ok (by decide)))
      (.ok (by decide))) (.ok (by decide))
  have hi := (reachable_access_invariant_underDD (KT_dd [] [] [] [] []) hr).2.1.base.1
  exact absurd ((h hi (a := 0) (ls := [0])).2 (by decide)) (by decide)

/-- The pass-1 statement `SameSkel.inv3` is false on the pass-2 model: without equal `dead` flags
(A6), a place dead in `sk0` is usable in `sk1` with an anchor that does not exist. -/
def sk0 : S3 := ⟨[0], 1, [⟨none, .frame 0, 0⟩], fun _ => .uninit, [],
  fun q => if q = 0 then [5] else [], fun _ => true, fun _ => false, fun _ => false, [], fun _ => []⟩
def sk1 : S3 := { sk0 with dead := fun _ => false }
example : SameSkel sk0 sk1 ∧ sk1.P = sk0.P ∧ sk1.F = sk0.F ∧ Inv3base sk0 ∧
    (∀ q, sk0.Usable q → ∀ x ∈ sk1.D q, sk0.Active x) ∧ ¬ Inv3base sk1 := by
  refine ⟨⟨rfl, fun _ => rfl⟩, rfl, rfl, ⟨?_, ?_, ?_, i4_always _⟩, ?_, ?_⟩
  · intro a b x y p _ hx; simp [sk0] at hx
  · intro b y a hy; simp [sk0] at hy
  · intro q hq; cases hq <;> simp_all [sk0]
  · intro q hq; cases hq <;> simp_all [sk0]
  · intro ⟨_, _, h3, _⟩
    exact absurd (h3 0 (by decide) 5 (by simp [sk1, sk0])) (by decide)

/-- Without the arena invariant, a live entry of `issued` does not block `reset` (A10): here the
entry names the root 0 of the arena value, which does not derive from `internal`. -/
def arBad : Arena := ⟨1, 1, [2, 3], [([2], 0)]⟩
example : ([2], 0) ∈ arBad.issued ∧ c6a.Active 0 ∧
    ResetStep KA arBad 0 c6a (.ok (resetEff c6a arBad)) := ⟨by decide, by decide, .ok (by decide)⟩

/-- An anchor of a dead owned place does not block a return (A5; MM-03.3.6): the value 1 of
`od1` ends, its storage 2 dies with the anchor 4, the value receives a fresh content and is
returned. -/
example : EndUseStep K0 1 od1 (.ok (endUseEff od1 1)) := .ok (by decide)
example : ¬ (write3Eff (endUseEff od1 1) [1]).Usable 2 ∧ (write3Eff (endUseEff od1 1) [1]).D 2 = [4] ∧
    TransferStep K0 1 0 (write3Eff (endUseEff od1 1) [1])
      (.ok (transferEff (write3Eff (endUseEff od1 1) [1]) 1 0)) := ⟨by decide, by decide, .ok (by decide)⟩

/-- A transfer that would move an anchor held within the value to a younger frame while a place
that depends on it stays in an older frame is rejected (B8; MM-03.3.6; A4). Frame 1: 0 value,
1 storage owned by 0, 2 storage owned by 1, 3 local depending on the root 2 of storage 2. Frame 2
receives `Modify` on 0 and tries to move the value into its local 4: the dependent of frame 1 would
be anchored on an authority held in frame 2 (pass 2: `transfer` accepted, `exitFrame` rejected). -/
def ma0 : S3 := dependEff (write3Eff (enter1 [(none, none, 0), (none, some 0, 0), (none, some 1, 0),
  (none, none, 0)]) [1]) 3 2
def ma1 : S3 := enterEff (deriveEff ma0 0 0 .modify) [4] [(none, none, 0)]
example : NoEscape ma1 2 (ma1.pframe 3) := by decide
example : TransferStep K0 1 4 ma1 .reject := .reject (by decide)
example : AnchorMoves ma1 1 2 ∧ (transferEff ma1 1 4).Usable 3 ∧ 2 ∈ (transferEff ma1 1 4).D 3 ∧
    ¬ NoEscape (transferEff ma1 1 4) 2 ((transferEff ma1 1 4).pframe 3) := by decide

/-! ### Closure of the exit (O7; B1) -/

/-- Witness state of `exitFrame_no_dangling_needs_rootHeld`: frame 1, called by frame 0, owns the
place 0, whose root authority 0 is held by frame 0. -/
def nd0 : S3 := ⟨[1, 0], 2, [⟨none, .frame 1, 0⟩], fun _ => .uninit,
  [⟨.modify, none, [0], .frame 0, true⟩], fun _ => [], fun _ => false, fun _ => false,
  fun _ => false, [], fun _ => []⟩

/-- The clause `RootHeld` of `WF3` (A4) is needed by `exitFrame_no_dangling` (MM-03.3 §4, O7): this
state satisfies every other clause of `WF3`, and `Inv3`, but the root authority 0 of the local 0
of frame 1 is held by frame 0, not by the owner of its place. The exit of frame 1 is accepted, and
the authority 0 stays active on the leaf of the local of the exited frame. -/
theorem exitFrame_no_dangling_needs_rootHeld :
    (∀ (b : Nat) (y : Authority) (a : Nat), nd0.A[b]? = some y → y.origin = some a → a < b) ∧
    (∀ (a : Nat) (x : Authority), nd0.A[a]? = some x → ∀ l ∈ x.footprint, l < nd0.P.length) ∧
    nd0.F ≠ [] ∧ nd0.F.Nodup ∧ (∀ f ∈ nd0.F, f < nd0.nF) ∧
    (∀ (q : Nat) (pl : Place) (f : Nat), nd0.P[q]? = some pl → pl.owner = .frame f →
      f < nd0.nF) ∧
    (∀ (q : Nat) (pl : Place) (o : Nat), nd0.P[q]? = some pl → pl.owner = .place o →
      o < nd0.P.length) ∧
    (∀ (q : Nat) (pl : Place) (r : Nat), nd0.P[q]? = some pl → pl.parent = some r →
      ∃ pr : Place, nd0.P[r]? = some pr ∧ r < q ∧ pr.owner = pl.owner ∧ nd0.dead r = nd0.dead q) ∧
    (∀ (a : Nat) (y : Authority), nd0.A[a]? = some y → y.active = true →
      HolderLive nd0 y.holder) ∧
    RootsDisjoint nd0.P ∧ RootChain nd0 ∧ ¬ RootHeld nd0 ∧ Inv3 nd0 ∧
    ExitStep K0 nd0 (.ok (exitEff nd0)) ∧ OwnedByFrame nd0.P 1 0 ∧
    (exitEff nd0).A[0]? = some ⟨.modify, none, [0], .frame 0, true⟩ ∧ 0 ∈ footprint nd0.P 0 := by
  have hA : ∀ {b : Nat} {y : Authority}, nd0.A[b]? = some y →
      b = 0 ∧ y = ⟨.modify, none, [0], .frame 0, true⟩ := by
    intro b y h
    have := lt_of_getElem? h; simp [nd0] at this; subst this; simp [nd0] at h; exact ⟨rfl, h.symm⟩
  have hP : ∀ {q : Nat} {pl : Place}, nd0.P[q]? = some pl → q = 0 ∧ pl = ⟨none, .frame 1, 0⟩ := by
    intro q pl h
    have := lt_of_getElem? h; simp [nd0] at this; subst this; simp [nd0] at h; exact ⟨rfl, h.symm⟩
  refine ⟨fun b y a hb ho => ?_, fun a x ha l hl => ?_, by decide, by decide, by decide,
    fun q pl f hq ho => ?_, fun q pl o hq ho => ?_, fun q pl r hq hp => ?_, fun a y ha ya => ?_,
    rootsDisjoint_always _, fun a y l ha hl _ => ?_, fun h => ?_,
    ⟨⟨fun a b x y p hab ha hb _ _ _ _ _ _ => ?_, fun b y a hb ho => ?_,
      fun q _ x hx => by simp [nd0] at hx, i4_always _⟩, fun q _ x hx => by simp [nd0] at hx,
      noDangling_iff.2 (by decide)⟩,
    .ok (by decide), .frame (pl := ⟨none, .frame 1, 0⟩) rfl rfl, by decide, by decide⟩
  · obtain ⟨-, rfl⟩ := hA hb; cases ho
  · obtain ⟨-, rfl⟩ := hA ha; simp at hl; subst hl; decide
  · obtain ⟨-, rfl⟩ := hP hq; cases ho; decide
  · obtain ⟨-, rfl⟩ := hP hq; cases ho
  · obtain ⟨-, rfl⟩ := hP hq; cases hp
  · obtain ⟨-, rfl⟩ := hA ha; decide
  · obtain ⟨rfl, rfl⟩ := hA ha; simp at hl; subst hl
    exact ⟨0, _, 0, .inl rfl, rfl, rfl, by decide, by decide, fun l' => by
      rw [show footprint nd0.P 0 = [0] by decide]⟩
  · obtain ⟨pr, hpr, hh⟩ := h 0 _ 0 0 rfl rfl (by decide) (by decide) (by decide)
    obtain ⟨-, rfl⟩ := hP hpr; cases hh
  · obtain ⟨rfl, -⟩ := hA ha; obtain ⟨rfl, -⟩ := hA hb; exact absurd rfl hab
  · obtain ⟨-, rfl⟩ := hA hb; cases ho

/-! ### `AnchorOrder` and the exit (B8, C1) -/

/-- A chain of three frames. Frame 1: local 0 with root 0; access 1 (`Modify` on 0) is passed to
frame 2. Frame 2: local 1 with root 2; access 3 observes 1, access 4 (`Modify` on 0) derives from 1;
both are passed to frame 3. Frame 3 derives 5 from 3 and makes the local 0 of frame 1 depend on
it. -/
def ao0 : S3 := enterEff (deriveEff (enter1 [(none, none, 0)]) 0 0 .modify) [1] [(none, none, 0)]
def ao1 : S3 := enterEff (deriveEff (deriveEff ao0 2 1 .observe) 1 0 .modify) [3, 4] []
def ao2 : S3 := dependEff (deriveEff ao1 3 1 .observe) 0 5

/-- The pass-3 counterexample to the preservation of `AnchorOrder` by `exitFrame` is excluded at
`depend` (C1): the effective anchor of 5 is the root 2, held by frame 2, younger than frame 1 of
place 0. The state `ao2` it built satisfies `WF3` and `Inv3base` but violates `AnchorOrder`, so
neither it nor its exit is reached any more; from it, the exit of frame 3 still replaces 5 by 2 and
the exit of frame 2 is still rejected. -/
theorem ao2_rejected_at_depend :
    Reachable K0 [] (deriveEff ao1 3 1 .observe) ∧
      (deriveEff ao1 3 1 .observe).effAnchor 5 = 2 ∧
      DependStep 0 5 (deriveEff ao1 3 1 .observe) .reject ∧ ¬ AnchorOrder ao2 ∧
      WF3 ao2 ∧ Inv3base ao2 ∧ ¬ Reachable K0 [] ao2 ∧
      ExitStep K0 ao2 (.ok (exitEff ao2)) ∧ ¬ AnchorOrder (exitEff ao2) ∧
      ¬ Reachable K0 [] (exitEff ao2) ∧
      (exitEff ao2).D 0 = [2] ∧ ExitStep K0 (exitEff ao2) .reject := by
  have r0 : Reachable K0 [] (enter1 [(none, none, 0)]) := .enter (.init (by decide)) (.ok (by decide))
  have r1 : Reachable K0 [] ao0 :=
    .enter (.derive r0 (.ok (by decide))) (.ok (by decide))
  have r2 : Reachable K0 [] ao1 :=
    .enter (.derive (.derive r1 (.ok (by decide))) (.ok (by decide))) (.ok (by decide))
  have r3 : Reachable K0 [] (deriveEff ao1 3 1 .observe) := .derive r2 (.ok (by decide))
  obtain ⟨hw, hi, -⟩ := reachable_access_invariant_underDD (KT_dd [] [] [] [] []) r3
  have hao : ¬ AnchorOrder ao2 := fun h => absurd (h 0 (by decide) 5 (by decide)) (by decide)
  have hao' : ¬ AnchorOrder (exitEff ao2) :=
    fun h => absurd (h 0 (by decide) 2 (by decide)) (by decide)
  have unr : ∀ {t : S3}, ¬ AnchorOrder t → ¬ Reachable K0 [] t := fun h hr =>
    h (reachable_access_invariant_underDD (KT_dd [] [] [] [] []) hr).2.1.ao
  have h3 : ∀ q ∈ List.range ao2.P.length, ao2.Usable q → ∀ x ∈ ao2.D q, ao2.Active x := by
    decide
  exact ⟨r3, by decide, .reject (by decide), hao, hw.of_eq rfl rfl rfl rfl rfl,
    ⟨hi.base.1, hi.base.2.1, fun q hq x hx => h3 q (List.mem_range.2 hq.lt) hq x hx, i4_always _⟩,
    unr hao, .ok (by decide), hao', unr hao', by decide, .reject (by decide)⟩

/-! ## New cases of pass 3 -/

/-- A local pinned at the exit (expected: reject, B4); unpinned under `ExternalDone`, the exit is
accepted. -/
abbrev KD0 : K := KT [] [] [0] [] []
example : ExitStep KD0 (pinEff c13a 0 true) .reject := .reject (by decide)
example : UnpinStep KD0 0 (pinEff c13a 0 true) (.ok (pinEff (pinEff c13a 0 true) 0 false)) :=
  .ok (by decide)
example : ExitStep KD0 (pinEff (pinEff c13a 0 true) 0 false)
    (.ok (exitEff (pinEff (pinEff c13a 0 true) 0 false))) := .ok (by decide)

/-- `release` by the callee of a root of the caller (expected: reject, B3; C4). -/
example : ReleaseStep 0 (enterEff c13a [] [(none, none, 0)]) .reject := .reject (by decide)

/-- `depend` on a place of the caller without right (expected: reject, B3): in the callee of case 8,
place 0 of the caller is only observed through parameter 2. With the `Modify` parameter 3 on
place 1, `depend` is accepted. -/
example : DependStep 0 2 c8c .reject := .reject (by decide)
example : DependStep 1 3 c8c (.ok (dependEff c8c 1 3)) := .ok (by decide)

/-- A value anchored on the root of its own storage, returned to the caller (expected: `ok`, B7):
the anchor moves with the value; after the exit, the caller's place 0 is anchored on the root 3,
held by place 0. -/
example : TransferStep K0 1 0 (dependEff ne0 1 3) (.ok (transferEff (dependEff ne0 1 3) 1 0)) :=
  .ok (by decide)
example : ExitStep K0 (transferEff (dependEff ne0 1 3) 1 0)
    (.ok (exitEff (transferEff (dependEff ne0 1 3) 1 0))) := .ok (by decide)
example : (exitEff (transferEff (dependEff ne0 1 3) 1 0)).D 0 = [3] ∧
    ((exitEff (transferEff (dependEff ne0 1 3) 1 0)).A[3]?).map (·.holder) = some (.place 0) := by
  decide

/-- A `transfer` that takes an anchor to a frame younger than a dependent (expected: reject at the
`transfer`, B8). -/
example : TransferStep K0 1 4 ma1 .reject := .reject (by decide)

/-- `alloc` in the middle of a frame, provider distinct from the owner, then `free` (expected:
`ok`, B5): case n6 above. `alloc` not satisfiable (expected: `fail`, state unchanged); `alloc` by a
callee without right on the provider of the caller (expected: reject). -/
def KNS : K := { KT [] [] [] [] [] with Satisfiable := fun _ _ _ => False }
instance : DecidablePred KNS.SharedMutable := fun l => inferInstanceAs (Decidable (l ∈ ([] : List Nat)))
instance : ∀ p ls s, Decidable (KNS.Satisfiable p ls s) := fun _ _ _ => instDecidableFalse
example : AllocStep KNS 1 0 [(none, none, 0)] (write3Eff n6e [1]) (.fail (write3Eff n6e [1])) :=
  .fail (by decide) (by decide)
example : AllocStep KF 1 2 [(none, none, 0)] (enterEff (write3Eff n6e [1]) [] [(none, none, 0)]) .reject :=
  .reject (by decide)

/-- `free` of a pinned leaf (expected: reject, B6); `unpin` under `ExternalDone`, then `free`
(expected: `ok`). -/
abbrev KFP : K := KT [] [] [2] [2] [(2, 7)]
example : PinStep 2 n6a (.ok (pinEff n6a 2 true)) := .ok (by decide)
example : FreeStep KFP 2 7 (pinEff n6a 2 true) .reject := .reject (by decide)
example : UnpinStep KFP 2 (pinEff n6a 2 true) (.ok (pinEff (pinEff n6a 2 true) 2 false)) :=
  .ok (by decide)
example : FreeStep KFP 2 7 (pinEff (pinEff n6a 2 true) 2 false)
    (.ok (freeEff (pinEff (pinEff n6a 2 true) 2 false) 2)) := .ok (by decide)

/-! ## Witnesses of the questions of pass 3 -/

/-- `alloc` (B5) does not preserve `Inv3` alone (A1): in a state satisfying `Inv3` where an
authority covers a leaf that does not exist yet, the root authority of the new place covers it too
in `Modify`. I1 fails. `WF3` (footprints made of existing places) excludes this state. The
provider 0 is `Init` (C6). -/
theorem alloc_not_inv3_preserving :
    let s : S3 := ⟨[0], 1, [⟨none, .frame 0, 0⟩], fun _ => .init,
      [⟨.modify, none, [0], .frame 0, true⟩, ⟨.modify, none, [1], .frame 0, true⟩],
      fun _ => [], fun _ => false, fun _ => false, fun _ => false, [], fun _ => []⟩
    Inv3 s ∧ AllocStep K0 0 0 [(none, none, 0)] s (.ok (allocEff s 0 0 [(none, none, 0)])) ∧
      ¬ I1 (allocEff s 0 0 [(none, none, 0)]) := by
  intro s
  have hA : ∀ {b : Nat} {y : Authority}, s.A[b]? = some y →
      (b = 0 ∧ y = ⟨.modify, none, [0], .frame 0, true⟩) ∨
      (b = 1 ∧ y = ⟨.modify, none, [1], .frame 0, true⟩) := by
    intro b y h
    have := lt_of_getElem? h; simp [s] at this
    obtain rfl | rfl : b = 0 ∨ b = 1 := by omega
    · simp [s] at h; exact .inl ⟨rfl, h.symm⟩
    · simp [s] at h; exact .inr ⟨rfl, h.symm⟩
  refine ⟨⟨⟨fun a b x y p hab ha hb _ _ xp yp _ _ => ?_, fun b y a hb ho => ?_,
    fun q _ x hx => by simp [s] at hx, i4_always _⟩, fun q _ x hx => by simp [s] at hx,
    noDangling_iff.2 (by decide)⟩, .ok (by decide) (by decide), fun h => ?_⟩
  · rcases hA ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hA hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals first | exact absurd rfl hab | (simp at xp yp; omega)
  · rcases hA hb with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> cases ho
  · have := h 1 2 ⟨.modify, none, [1], .frame 0, true⟩
      ⟨.modify, none, footprint (allocP s 0 [(none, none, 0)]) 1, .place 0, true⟩ 1
      (by decide) (by decide) (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide)
    exact absurd this.1 (by decide)

/-- Scope of B8 (C1): on the return of case 8, place 1 of frame 1 depends on parameter 2, held by
the younger frame 2; its effective anchor, the root 0, is held by frame 1, and `AnchorOrder`
holds. -/
example : TransferStep K0 2 1 c8d (.ok c8e) ∧ c8e.Usable 1 ∧ 2 ∈ c8e.D 1 ∧
    (c8e.A[2]?).map (·.holder) = some (.frame 2) ∧ c8e.pframe 1 = some 1 ∧
    ¬ ancestor c8e.F 2 1 ∧ c8e.effAnchor 2 = 0 ∧
    (c8e.A[0]?).map (·.holder) = some (.frame 1) ∧ AnchorOrder c8e :=
  ⟨.ok (by decide), by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    anchorOrder_iff.2 (by decide)⟩

/-- Mode requested by `release` (pass-3 report, (e) 8): B3 accepted an authority exercisable by
the current frame, at some mode. A callee that only observes the caller's value 0 released the
`Modify` root 1 of the storage owned by 0; after the return, the caller could neither write nor
free its storage. C4 rejects that `release`: authority 1 has no origin. The facts on
`releaseEff rq1 1` describe the state pass 3 reached. Frame 1: 0 value, 1 storage owned by 0. -/
abbrev KR : K := KT [] [] [] [1] [(1, 7)]
def rq0 : S3 := write3Eff (write3Eff (enter1 [(none, none, 0), (none, some 0, 0)]) [0]) [1]
def rq1 : S3 := enterEff (deriveEff rq0 0 0 .observe) [2] []
example : rq1.ExercisableAt 1 .observe ∧ ¬ rq1.ExercisableAt 1 .modify ∧ ¬ HasRight rq1 .modify 0 ∧
    ReleaseStep 1 rq1 .reject := ⟨by decide, by decide, by decide, .reject (by decide)⟩
example : ExitStep K0 (releaseEff rq1 1) (.ok (exitEff (releaseEff rq1 1))) := .ok (by decide)
example : Write3Step 1 [1] rq0 (.ok (write3Eff rq0 [1])) := .ok (by decide)
example : FreeStep KR 1 7 rq0 (.ok (freeEff rq0 1)) := .ok (by decide)
example : Write3Step 1 [1] (exitEff (releaseEff rq1 1)) .reject := .reject (by decide)
example : FreeStep KR 1 7 (exitEff (releaseEff rq1 1)) .reject := .reject (by decide)
example : (exitEff (releaseEff rq1 1)).Usable 1 := by decide

/-- Initialisation of the allocator (pass-3 report, (e) 6): B5 did not require it. C6 requires the
leaves of the provider `Init`: `alloc` rejects a provider whose value was moved out, or never
initialised. Frame 1: 0 owner, 1 allocator value, 2 another local. -/
def mv0 : S3 := enter1 [(none, none, 0), (none, none, 0), (none, none, 0)]
def mv1 : S3 := transferEff (write3Eff mv0 [1]) 1 2
example : TransferStep K0 1 2 (write3Eff mv0 [1]) (.ok mv1) := .ok (by decide)
example : mv1.I 1 = .moved ∧ Read3Step 1 [1] mv1 .reject := ⟨by decide, .reject (by decide)⟩
example : AllocStep K0 1 0 [(none, none, 0)] mv1 .reject := .reject (by decide)
example : AllocStep K0 1 0 [(none, none, 0)] mv0 .reject := .reject (by decide)

/-- `endUse` and the end of external obligations (pass-3 report, (e) 9): A8 let `endUse` end a
pinned leaf under `ExternalDone`, while B6 reserves the end of external obligations to `unpin`.
The storage 2 of `n6a`, pinned, is rejected by `free`; C5 now rejects the end of its owner too.
The facts on `endUseEff (pinEff n6a 2 true) 0` describe the state pass 3 reached: the storage
died with its pin set, and the exit accepted it. -/
abbrev KE : K := KT [] [] [2] [2] [(2, 7)]
example : FreeStep KE 2 7 (pinEff n6a 2 true) .reject := .reject (by decide)
example : EndUseStep KE 0 (pinEff n6a 2 true) .reject := .reject (by decide)
example : (endUseEff (pinEff n6a 2 true) 0).pin 2 = true ∧
    (endUseEff (pinEff n6a 2 true) 0).dead 2 = true := by decide
example : ExitStep KE (endUseEff (pinEff n6a 2 true) 0)
    (.ok (exitEff (endUseEff (pinEff n6a 2 true) 0))) := .ok (by decide)

/-! ## New cases of pass 4 -/

/-- `release` of a root (expected: reject, C4): the local 0 of frame 1 is held by the current
frame, which pass 3 accepted (B3); C4 rejects every authority without origin. -/
example : ReleaseStep 0 c13a .reject := .reject (by decide)

/-- `release` by the current frame of a derived authority held by one of its places, with
exercisable `Modify` on that place (expected: `ok`, C4): the block 4 of case 6, derived from
`internal` and held by place 4, on which frame 1 holds the root 2. -/
example : (c6b.1.A[4]?).map (fun y => (y.origin, y.holder)) = some (some 1, .place 4) ∧
    HasRight c6b.1 .modify 4 := by decide
example : ReleaseStep 4 c6b.1 (.ok (releaseEff c6b.1 4)) := .ok (by decide)

/-- `endUse` of a pinned storage under `ExternalDone` without `unpin` (expected: reject, C5); after
`unpin`, `endUse` is accepted. The storage 2 of `n6a`, allocated and owned by 0, is pinned. -/
example : EndUseStep KE 2 (pinEff n6a 2 true) .reject := .reject (by decide)
example : UnpinStep KE 2 (pinEff n6a 2 true) (.ok (pinEff (pinEff n6a 2 true) 2 false)) :=
  .ok (by decide)
example : EndUseStep KE 2 (pinEff (pinEff n6a 2 true) 2 false)
    (.ok (endUseEff (pinEff (pinEff n6a 2 true) 2 false) 2)) := .ok (by decide)

/-- `alloc` with a provider `Moved` or `Uninit` (expected: reject, C6): `mv1` and `mv0` above. -/
example : AllocStep K0 1 0 [(none, none, 0)] mv1 .reject ∧
    AllocStep K0 1 0 [(none, none, 0)] mv0 .reject := ⟨.reject (by decide), .reject (by decide)⟩

/-- `alloc` of a shape with two fields, then `split` of the two fields and two writes (expected:
`ok`, C6). Frame 1: 0 owner, 1 allocator value. The shape: a root 2 with parts 3 and 4; its root
authority 2, held by place 0, covers both. -/
def sh2 : List (Option Nat × Option Nat × Nat) :=
  [(none, none, 0), (some 2, none, 0), (some 2, none, 0)]
def al2 : S3 := allocEff (write3Eff n6e [1]) 1 0 sh2
example : AllocStep K0 1 0 sh2 (write3Eff n6e [1]) (.ok al2) := .ok (by decide) trivial
example : (al2.A[2]?).map (fun y => (y.footprint, y.holder)) = some ([3, 4], .place 0) := by decide
example : SplitStep K0 2 [[3], [4]] al2 (.ok (splitEff al2 2 [[3], [4]])) := .ok (by decide)
example : Write3Step 3 [3] (splitEff al2 2 [[3], [4]])
    (.ok (write3Eff (splitEff al2 2 [[3], [4]]) [3])) := .ok (by decide)
example : Write3Step 4 [4] (write3Eff (splitEff al2 2 [[3], [4]]) [3])
    (.ok (write3Eff (write3Eff (splitEff al2 2 [[3], [4]]) [3]) [4])) := .ok (by decide)

/-- An arena whose storage comes from `alloc`, two emissions (expected: `ok`, `ok`; C6). Frame 1:
0 arena value, 1 allocator value, 2 and 3 block destinations. The storage 4, with leaves 5 and 6,
is allocated and owned by 0; its root authority 4 is `internal`. The metadata right is
exercisable `Modify` on the arena value 0 (`MetaRight`, C6), without `SharedMutable`. -/
def aaE : S3 := enter1 [(none, none, 0), (none, none, 0), (none, none, 0), (none, none, 0)]
def aa0 : S3 := allocEff (write3Eff aaE [1]) 1 0 [(none, none, 0), (some 4, none, 0), (some 4, none, 0)]
example : Write3Step 1 [1] aaE (.ok (write3Eff aaE [1])) := .ok (by decide)
example : AllocStep K0 1 0 [(none, none, 0), (some 4, none, 0), (some 4, none, 0)]
    (write3Eff aaE [1]) (.ok aa0) := .ok (by decide) trivial
def aar : Arena := ⟨4, 4, [5, 6], []⟩
def aa1 : S3 × Arena := issueEff aa0 aar [5] 2
def aa2 : S3 × Arena := issueEff aa1.1 aa1.2 [6] 3
example : IssueStep K0 aar 0 [5] 2 aa0 (.ok aa1.1 aa1.2) := .ok (by decide) (by decide) (by decide)
example : IssueStep K0 aa1.2 0 [6] 3 aa1.1 (.ok aa2.1 aa2.2) :=
  .ok (by decide) (by decide) (by decide)

/-- The same `alloc` twice, `Satisfiable` true then false depending on the state (expected: `ok`
then `fail`; C9). The allocator contract has a capacity of three places. -/
def KCap : K :=
  { KT [] [] [] [] [] with Satisfiable := fun _ ls s => s.P.length + ls.length ≤ 3 }
instance : DecidablePred KCap.SharedMutable :=
  fun l => inferInstanceAs (Decidable (l ∈ ([] : List Nat)))
instance : ∀ p ls s, Decidable (KCap.Satisfiable p ls s) := fun _ _ _ => Nat.decLe _ _
example : AllocStep KCap 1 0 [(none, none, 0)] (write3Eff n6e [1])
    (.ok (allocEff (write3Eff n6e [1]) 1 0 [(none, none, 0)])) := .ok (by decide) (by decide)
example : AllocStep KCap 1 0 [(none, none, 0)]
    (allocEff (write3Eff n6e [1]) 1 0 [(none, none, 0)])
    (.fail (allocEff (write3Eff n6e [1]) 1 0 [(none, none, 0)])) := .fail (by decide) (by decide)

/-- `alloc`, then a read of an `Uninit` leaf (expected: reject), a write (`ok`) and a read
(`ok`): the storage 2 of `n6a` before its write. -/
example : Read3Step 2 [2] (allocEff (write3Eff n6e [1]) 1 0 [(none, none, 0)]) .reject :=
  .reject (by decide)
example : Write3Step 2 [2] (allocEff (write3Eff n6e [1]) 1 0 [(none, none, 0)]) (.ok n6a) :=
  .ok (by decide)
example : Read3Step 2 [2] n6a (.ok n6a) := .ok (by decide)

/-- `transfer` of a local, source `Moved`, then a write into the source (`ok`) and a read
(`ok`): `mv1` above, where the value of local 1 went to 2. -/
example : Write3Step 1 [1] mv1 (.ok (write3Eff mv1 [1])) := .ok (by decide)
example : Read3Step 1 [1] (write3Eff mv1 [1]) (.ok (write3Eff mv1 [1])) := .ok (by decide)

/-- `transfer` of a part, the parent partly `Moved`, then a read of the other part (`ok`) and a
rewrite of the moved part (`ok`): in `c11a`, the part 1 of 0 goes to 3. -/
def tp1 : S3 := transferEff c11a 1 3
example : TransferStep K0 1 3 c11a (.ok tp1) := .ok (by decide)
example : tp1.I 1 = .moved ∧ tp1.I 2 = .init := by decide
example : Read3Step 0 [2] tp1 (.ok tp1) := .ok (by decide)
example : Write3Step 0 [1] tp1 (.ok (write3Eff tp1 [1])) := .ok (by decide)

/-- `endUse` of a local, then a write and a read in that local (expected: `ok`, `ok`; C8): the
local stays usable, its leaves `Uninit`. -/
example : EndUseStep K0 0 c13a (.ok (endUseEff c13a 0)) := .ok (by decide)
example : (endUseEff c13a 0).Usable 0 ∧ (endUseEff c13a 0).I 0 = .uninit := by decide
example : Write3Step 0 [0] (endUseEff c13a 0) (.ok (write3Eff (endUseEff c13a 0) [0])) :=
  .ok (by decide)
example : Read3Step 0 [0] (write3Eff (endUseEff c13a 0) [0])
    (.ok (write3Eff (endUseEff c13a 0) [0])) := .ok (by decide)

/-! ## Witnesses of the questions of pass 4 -/

/-- On every reached state (MM-03.3.1; D1), the base frame is 0 and stays at the bottom of the
stack, `nF` is positive, the static places keep their indices, and frame 0 owns directly exactly
the static elements without owning element: `enterFrame` gives its locals the new frame or a place
as owner (A5), `alloc` and `transfer` only give places, and the exit never pops the last frame
(O7). The places frame 0 owns transitively (`OwnedByFrame`) are those and the storage they own. -/
theorem reachable_base_owns_statics {k : K} {statics : Statics} {s : S3}
    (h : Reachable k statics s) :
    s.F.getLast? = some 0 ∧ 0 < s.nF ∧ statics.length ≤ s.P.length ∧
      ∀ (q : Nat) (pl : Place), s.P[q]? = some pl →
        (pl.owner = .frame 0 ↔
          q < statics.length ∧ ((statics.map (·.1))[q]?).bind (·.2.1) = none) := by
  induction h with
  | init hsh =>
    refine ⟨rfl, Nat.zero_lt_one, Nat.le_of_eq (init_len statics).symm, fun q pl hq => ?_⟩
    obtain ⟨hql, rfl⟩ := init_P_get hq
    simp only [shapeOwner]
    split
    · rename_i o ho
      exact ⟨fun e => (by cases e), fun ⟨_, h⟩ => (by rw [ho] at h; cases h)⟩
    · rename_i ho
      exact ⟨fun _ => ⟨hql, ho⟩, fun _ => rfl⟩
  | derive _ h ih =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; exact ih
  | split _ h ih =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; exact ih
  | @release s s' a _ h ih =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
    unfold releaseEff; split <;> exact ih
  | @transfer s s' src dst _ h ih =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
    refine ⟨ih.1, ih.2.1, by rw [transfer_len]; exact ih.2.2.1, fun q pl hq => ?_⟩
    rw [transfer_P_get] at hq
    obtain ⟨pl₀, h₀, rfl⟩ := Option.map_eq_some_iff.1 hq
    have e := ih.2.2.2 q pl₀ h₀
    split
    · rename_i hh
      have hp : pl₀.owner ≠ .frame 0 := fun e' => by rw [e'] at hh; exact hh
      simp only [reduceCtorEq, false_iff]
      exact fun h' => hp (e.2 h')
    · exact e
  | depend _ h ih =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; exact ih
  | @enter s s' ps ls _ h ih =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
    obtain ⟨h1, h2, h3, h4⟩ := ih
    refine ⟨?_, by simp [enterEff], ?_, fun q pl hq => ?_⟩
    · show (s.nF :: s.F).getLast? = some 0
      cases hF : s.F with
      | nil => rw [hF] at h1; cases h1
      | cons a l => rw [hF] at h1; rw [List.getLast?_cons_cons]; exact h1
    · show statics.length ≤ (enterP s ls).length
      rw [enterP_len]; omega
    · rcases enterP_get (show (enterP s ls)[q]? = some pl from hq) with ⟨-, hq'⟩ | ⟨hge, i, -, -, rfl⟩
      · exact h4 q pl hq'
      · have : ¬ q < statics.length := by omega
        simp only [this, false_and, iff_false]
        simp only [localOwner]; split
        · simp
        · intro e; injection e with e; omega
  | @exit s s' _ h ih =>
    obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
    unfold exitEff
    unfold ExitPre at hpre
    split
    · rename_i f F₀ hF
      rw [hF] at hpre
      obtain ⟨hne, -⟩ := hpre
      refine ⟨?_, ih.2.1, ih.2.2⟩
      have := ih.1; rw [hF] at this
      cases F₀ with
      | nil => exact absurd rfl hne
      | cons g F₁ => rw [List.getLast?_cons_cons] at this; exact this
    · exact ih
  | read _ h ih =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; exact ih
  | write _ h ih =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; exact ih
  | writeShared _ h ih =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; exact ih
  | pin _ h ih =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; exact ih
  | unpin _ h ih =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; exact ih
  | endUse _ h ih =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; exact ih
  | free _ h ih =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; exact ih
  | @alloc s s' pr ow ls _ h ih =>
    cases h with
    | ok _ _ =>
      obtain ⟨h1, h2, h3, h4⟩ := ih
      refine ⟨h1, h2, ?_, fun q pl hq => ?_⟩
      · show statics.length ≤ (allocP s ow ls).length
        rw [allocP_len]; omega
      · rcases shapeP_get (show (shapeP s.P (.place ow) ls)[q]? = some pl from hq) with
          ⟨-, hq'⟩ | ⟨hge, i, -, -, rfl⟩
        · exact h4 q pl hq'
        · have : ¬ q < statics.length := by omega
          simp only [this, false_and, iff_false]
          simp only [shapeOwner]; split <;> simp
  | newArena _ h ih =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; exact ih
  | issue _ h ih => cases h with
    | ok _ hst => cases hst; exact ih
  | reset _ h ih =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; unfold resetAtEff; split <;> exact ih
  | store _ h ih =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; unfold storeEff; split <;> exact ih

/-- A static leaf pinned by `K.Pinned` (C5; D1), as a memory-mapped register would be: the
contract `KPS` pins the leaf 0 of the static storage `stPin`, one global with an initialiser. -/
abbrev KPS : K := KT [] [0] [] [] []
def stPin : Statics := [((none, none, 0), true)]
def sp1 : S3 := enterEff (S3.init stPin) [] [(none, none, 0)]

/-- `static_pinned_never_exits` has content on a reached state (C5; D1; F3): `K.Pinned` is not
empty, `StaticPinnedBottom` holds since frame 0 owns the pinned global directly, and the exit of
frame 1 kills its local, which covers no pinned leaf. -/
theorem staticPinned_reached :
    Reachable KPS stPin sp1 ∧ KPS.Pinned 0 ∧ StaticPinnedBottom KPS sp1 ∧
      ExitStep KPS sp1 (.ok (exitEff sp1)) ∧
      ∀ q, sp1.Usable q → ¬ ({ sp1 with F := [0] } : S3).Usable q →
        ∀ l ∈ footprint sp1.P q, ¬ KPS.Pinned l := by
  have hr : Reachable KPS stPin sp1 := .enter (.init (by decide)) (.ok (by decide))
  have hsp : StaticPinnedBottom KPS sp1 := by
    intro l hl
    have : l = 0 := List.mem_singleton.1 hl
    subst this
    exact ⟨0, ⟨none, .frame 0, 0⟩, by decide, by decide, rfl⟩
  exact ⟨hr, List.mem_singleton_self _, hsp, .ok (by decide),
    static_pinned_never_exits (reachable_access_invariant_underDD (KT_dd [] [0] [] [] []) hr).1 hsp
      (show sp1.F = 1 :: [0] from rfl) (by decide)⟩

/-- Reading the base frame of C5 as the first frame entered does not help: in `c13a`, the local 0
belongs to frame 1, the first frame entered, and stops being usable when frame 1 exits. -/
example : c13a.F = [1, 0] ∧ c13a.Usable 0 ∧ ¬ ({ c13a with F := [0] } : S3).Usable 0 ∧
    0 ∈ footprint c13a.P 0 ∧ OwnedByFrame c13a.P 1 0 :=
  ⟨rfl, by decide, by decide, by decide, .frame (pl := ⟨none, .frame 1, 0⟩) rfl rfl⟩

/-- `alloc` of the empty shape (pass-4 question (e) 2): pass 4 accepted it, with no new place and
no new authority, the state `allocEff (write3Eff n6e [1]) 1 0 []` below. D2 rejects it. -/
example : AllocStep K0 1 0 [] (write3Eff n6e [1]) .reject := .reject (by decide)
example : (allocEff (write3Eff n6e [1]) 1 0 []).P = (write3Eff n6e [1]).P ∧
    (allocEff (write3Eff n6e [1]) 1 0 []).A = (write3Eff n6e [1]).A := by decide

/-! ## New cases of pass 5 -/

/-! ### Static storage (D1) -/

/-- Two globals: 0 with an initialiser (`Init`), 1 without (`Uninit`), owned by frame 0, each with
a root held by frame 0 (D1). -/
def stG : Statics := [((none, none, 0), true), ((none, none, 0), false)]
def g0 : S3 := S3.init stG

/-- A global `Init` read by frame 0 (expected: `ok`); a global `Uninit` read (expected: reject),
written then read (expected: `ok`, `ok`). -/
example : Read3Step 0 [0] g0 (.ok g0) := .ok (by decide)
example : Read3Step 1 [1] g0 .reject := .reject (by decide)
example : Write3Step 1 [1] g0 (.ok (write3Eff g0 [1])) := .ok (by decide)
example : Read3Step 1 [1] (write3Eff g0 [1]) (.ok (write3Eff g0 [1])) := .ok (by decide)

/-- A global written by a callee without parameter (expected: reject): the root of the global is
held by frame 0, which the callee does not exercise (A2). With a `Modify` parameter derived by the
caller (A3), the write is accepted. -/
example : EnterStep [] [] g0 (.ok (enterEff g0 [] [])) := .ok (by decide)
example : Write3Step 0 [0] (enterEff g0 [] []) .reject := .reject (by decide)
def g3 : S3 := enterEff (deriveEff g0 0 0 .modify) [2] []
example : DeriveStep 0 0 .modify g0 (.ok (deriveEff g0 0 0 .modify)) := .ok (by decide)
example : EnterStep [2] [] (deriveEff g0 0 0 .modify) (.ok g3) := .ok (by decide)
example : Write3Step 2 [0] g3 (.ok (write3Eff g3 [0])) := .ok (by decide)
example : Reachable K0 stG g3 :=
  .enter (.derive (.init (by decide)) (.ok (by decide))) (.ok (by decide))

/-- A memory-mapped register as a pinned static (D1): the global 0 is pinned by `K.Pinned`
(`KPS`). The test checks the access discipline only: `transfer` and `endUse` are rejected, reads
and writes allowed by the discipline are accepted. The semantics of a hardware access, read side
effects and external modifications, is outside the kernel and not represented. -/
def mm0 : S3 := S3.init stG
example : TransferStep KPS 0 1 mm0 .reject := .reject (by decide)
example : EndUseStep KPS 0 mm0 .reject := .reject (by decide)
example : Read3Step 0 [0] mm0 (.ok mm0) := .ok (by decide)
example : Write3Step 0 [0] mm0 (.ok (write3Eff mm0 [0])) := .ok (by decide)
example : StaticPinnedBottom KPS mm0 := fun l hl => by
  have : l = 0 := List.mem_singleton.1 hl
  subst this
  exact ⟨0, ⟨none, .frame 0, 0⟩, by decide, by decide, rfl⟩

/-! ### `alloc` of the empty shape (D2) -/

/-- `alloc []` (expected: reject); `alloc` of a shape of one leaf (expected: `ok`), D2. -/
example : AllocStep K0 1 0 [] (write3Eff n6e [1]) .reject := .reject (by decide)
example : AllocStep K0 1 0 [(none, none, 0)] (write3Eff n6e [1])
    (.ok (allocEff (write3Eff n6e [1]) 1 0 [(none, none, 0)])) := .ok (by decide) trivial

/-! ### Cases 16 and n4 as executions of `Reachable` (D3) -/

/-- Case 16 and n4 from the initial state, the arena introduced by `alloc` and `newArena`.
Frame 1: 0 arena value, 1 allocator value, 2 buffer destination. `alloc` gives the storage 3, with
parts 4 and 5, owned by 0, of root authority 3; `newArena 3` registers the arena (entry 0,
`internal` 3). The call passes 4, which observes the arena value, and 5, which modifies the
buffer; the callee local 6 receives the block 7 on the region `[4]`, then is returned to 2. -/
def a0 : S3 := enter1 [(none, none, 0), (none, none, 0), (none, none, 0)]
def a1 : S3 := write3Eff a0 [1]
def a2 : S3 := allocEff a1 1 0 [(none, none, 0), (some 3, none, 0), (some 3, none, 0)]
def a3 : S3 := newArenaEff a2 3 3
def a6 : S3 := enterEff (deriveEff (deriveEff a3 0 0 .observe) 2 2 .modify) [4, 5] [(none, none, 0)]
def ar7 : Arena := ⟨3, 3, [4, 5], []⟩
def a7 : S3 := arenaSet (issueEff a6 ar7 [4] 6).1 0 (issueEff a6 ar7 [4] 6).2
def a8 : S3 := transferEff a7 6 2
def a9 : S3 := exitEff a8
def a10 : S3 := endUseEff a9 2
def a11 : S3 := resetAtEff a10 0

example : Write3Step 1 [1] a0 (.ok a1) := .ok (by decide)
example : AllocStep KA 1 0 [(none, none, 0), (some 3, none, 0), (some 3, none, 0)] a1 (.ok a2) :=
  .ok (by decide) trivial
example : NewArenaStep 3 3 a2 (.ok a3) := .ok (by decide)
example : a3.arenas = [ar7] := by decide
example : DeriveStep 0 0 .observe a3 (.ok (deriveEff a3 0 0 .observe)) := .ok (by decide)
example : DeriveStep 2 2 .modify (deriveEff a3 0 0 .observe)
    (.ok (deriveEff (deriveEff a3 0 0 .observe) 2 2 .modify)) := .ok (by decide)
example : EnterStep [4, 5] [(none, none, 0)] (deriveEff (deriveEff a3 0 0 .observe) 2 2 .modify)
    (.ok a6) := .ok (by decide)
example : IssueAt KA 0 4 [4] 6 a6 (.ok a7) := .ok (ar := ar7) (by decide) (.ok (by decide) (by decide) (by decide))
example : TransferStep KA 6 2 a7 (.ok a8) := .ok (by decide)
example : ExitStep KA a8 (.ok a9) := .ok (by decide)
example : ResetAtStep KA 0 0 a9 .reject := .reject (by decide)
example : EndUseStep KA 2 a9 (.ok a10) := .ok (by decide)
example : ResetAtStep KA 0 0 a10 (.ok a11) := .ok (by decide)

/-- The run of case 16 and n4 is an execution of `Reachable` from `S3.init []`, and the list of
arenas is not empty from `newArena` on. -/
theorem case16_reachable :
    Reachable KA [] a11 ∧ a3.arenas ≠ [] ∧ a6.arenas ≠ [] ∧ a7.arenas ≠ [] ∧ a8.arenas ≠ [] ∧
      a9.arenas ≠ [] ∧ a10.arenas ≠ [] ∧ a11.arenas ≠ [] := by
  have r0 : Reachable KA [] a0 := .enter (.init (by decide)) (.ok (by decide))
  have r1 : Reachable KA [] a1 := .write r0 (show Write3Step 1 [1] a0 (.ok a1) from .ok (by decide))
  have r2 : Reachable KA [] a2 := .alloc r1
    (show AllocStep KA 1 0 [(none, none, 0), (some 3, none, 0), (some 3, none, 0)] a1 (.ok a2) from
      .ok (by decide) trivial)
  have r3 : Reachable KA [] a3 := .newArena r2 (show NewArenaStep 3 3 a2 (.ok a3) from .ok (by decide))
  have r4 : Reachable KA [] (deriveEff a3 0 0 .observe) :=
    .derive r3 (show DeriveStep 0 0 .observe a3 (.ok _) from .ok (by decide))
  have r5 : Reachable KA [] (deriveEff (deriveEff a3 0 0 .observe) 2 2 .modify) :=
    .derive r4 (show DeriveStep 2 2 .modify (deriveEff a3 0 0 .observe) (.ok _) from .ok (by decide))
  have r6 : Reachable KA [] a6 := .enter r5
    (show EnterStep [4, 5] [(none, none, 0)] _ (.ok a6) from .ok (by decide))
  have r7 : Reachable KA [] a7 := .issue r6
    (show IssueAt KA 0 4 [4] 6 a6 (.ok a7) from
      .ok (ar := ar7) (by decide) (.ok (by decide) (by decide) (by decide)))
  have r8 : Reachable KA [] a8 := .transfer r7 (show TransferStep KA 6 2 a7 (.ok a8) from .ok (by decide))
  have r9 : Reachable KA [] a9 := .exit r8 (show ExitStep KA a8 (.ok a9) from .ok (by decide))
  have r10 : Reachable KA [] a10 := .endUse r9 (show EndUseStep KA 2 a9 (.ok a10) from .ok (by decide))
  exact ⟨.reset r10 (show ResetAtStep KA 0 0 a10 (.ok a11) from .ok (by decide)), by decide,
    by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- Return of a value holding a derived `Modify` access to a part of a container of the caller:
the buffer 2 of case 16 holds the block 7, derived from `internal` on the part 4 of the storage 3.
After the return, a write of the caller on the whole container (expected: reject), on the other
part 5 (expected: `ok`). A value holds a derived access as a block issued to it or, since F4, as
an authority stored into it by `store`; `derive` and `split` give the current frame as holder.
Case 16 is modelled here by an issued block. -/
example : (a9.A[7]?).map (fun y => (y.origin, y.holder, y.footprint, y.mode, y.active)) =
    some (some 3, .place 2, [4], .modify, true) := by decide
example : Write3Step 3 [4, 5] a9 .reject := .reject (by decide)
example : Write3Step 3 [5] a9 (.ok (write3Eff a9 [5])) := .ok (by decide)

/-! ### The arena value transferred or ended (D3) -/

/-- Frame 1: 0 arena value, 1 allocator value, 2 new owner, 3 block destination; `alloc` gives
the storage 4, with parts 5 and 6, owned by 0. After the transfer of the arena value to 2, the new
owner issues a block (expected: `ok`), with `Modify` on the arena value as metadata right (C6).
After `endUse` of the arena value, `issue` is rejected: its `internal` is released. -/
def b0 : S3 := enter1 [(none, none, 0), (none, none, 0), (none, none, 0), (none, none, 0)]
def b1 : S3 := write3Eff (write3Eff b0 [1]) [0]
def b2 : S3 := allocEff b1 1 0 [(none, none, 0), (some 4, none, 0), (some 4, none, 0)]
def b3 : S3 := newArenaEff b2 4 4
def b4 : S3 := transferEff b3 0 2
def arB : Arena := ⟨4, 4, [5, 6], []⟩
example : Write3Step 1 [1] b0 (.ok (write3Eff b0 [1])) := .ok (by decide)
example : Write3Step 0 [0] (write3Eff b0 [1]) (.ok b1) := .ok (by decide)
example : AllocStep K0 1 0 [(none, none, 0), (some 4, none, 0), (some 4, none, 0)] b1 (.ok b2) :=
  .ok (by decide) trivial
example : NewArenaStep 4 4 b2 (.ok b3) := .ok (by decide)
example : b3.arenas = [arB] ∧ arenaValue b3 arB = some 0 := by decide
example : TransferStep K0 0 2 b3 (.ok b4) := .ok (by decide)
example : b4.arenas = [arB] ∧ arenaValue b4 arB = some 2 ∧ b4.Active 4 := by decide
example : IssueAt K0 0 2 [5] 3 b4
    (.ok (arenaSet (issueEff b4 arB [5] 3).1 0 (issueEff b4 arB [5] 3).2)) :=
  .ok (by decide) (.ok (by decide) (by decide) (by decide))
example : EndUseStep K0 2 b4 (.ok (endUseEff b4 2)) := .ok (by decide)
example : ¬ (endUseEff b4 2).Active 4 := by decide
example : IssueAt K0 0 2 [5] 3 (endUseEff b4 2) .reject :=
  .reject (ar := arB) (by decide) (.reject (by decide))

/-! ### Nested arena (D3) -/

/-- An arena nested in a block of another arena, with the block issued to the parent arena value
itself, the only form that D3 realised (pass-5 report, (d) 2); still legal under F1, where the
arena value is the holder of `internal`. The form of pass 6, with a child arena value distinct
from the parent's, is among the new cases of pass 6. Frame 1: 0 arena value, 1 allocator value; storage 2 with parts 3 and 4, of root
authority 2; the parent issues the block 3 on `[3]` to 0; `newArena 3` registers the child, of
`internal` 3, derived from
the parent's `internal` 2. The `reset` of the parent is rejected while the child lives; after the
release of the child's `internal`, the child is dead and the `reset` of the parent is accepted. -/
def nA0 : S3 := enter1 [(none, none, 0), (none, none, 0)]
def nA2 : S3 := allocEff (write3Eff nA0 [1]) 1 0 [(none, none, 0), (some 2, none, 0), (some 2, none, 0)]
def nA3 : S3 := newArenaEff nA2 2 2
def arP : Arena := ⟨2, 2, [3, 4], []⟩
def nA4 : S3 := arenaSet (issueEff nA3 arP [3] 0).1 0 (issueEff nA3 arP [3] 0).2
def nA5 : S3 := newArenaEff nA4 3 3
example : NewArenaStep 2 2 nA2 (.ok nA3) := .ok (by decide)
example : nA3.arenas = [arP] := by decide
example : IssueAt K0 0 0 [3] 0 nA3 (.ok nA4) :=
  .ok (ar := arP) (by decide) (.ok (by decide) (by decide) (by decide))
example : NewArenaStep 3 3 nA4 (.ok nA5) := .ok (by decide)
example : nA5.arenas.map (fun ar => (ar.storage, ar.internal)) = [(2, 2), (3, 3)] ∧
    (nA5.A[3]?).map (·.origin) = some (some 2) := by decide
example : ResetAtStep K0 0 0 nA5 .reject := .reject (by decide)
example : ReleaseStep 3 nA5 (.ok (releaseEff nA5 3)) := .ok (by decide)
example : IssueAt K0 1 0 [3] 4 nA5
    (.ok (arenaSet (issueEff nA5 ⟨3, 3, [3], []⟩ [3] 4).1 1 (issueEff nA5 ⟨3, 3, [3], []⟩ [3] 4).2)) :=
  .ok (by decide) (.ok (by decide) (by decide) (by decide))
example : IssueAt K0 1 0 [3] 4 (releaseEff nA5 3) .reject :=
  .reject (ar := ⟨3, 3, [3], []⟩) (by decide) (.reject (by decide))
example : (releaseEff nA5 3).arenas = nA5.arenas ∧ ¬ (releaseEff nA5 3).Active 3 := by decide
example : ResetAtStep K0 0 0 (releaseEff nA5 3) (.ok (resetAtEff (releaseEff nA5 3) 0)) :=
  .ok (by decide)
theorem nested_reachable : Reachable K0 [] (resetAtEff (releaseEff nA5 3) 0) := by
  have r0 : Reachable K0 [] nA0 := .enter (.init (by decide)) (.ok (by decide))
  have r1 : Reachable K0 [] (write3Eff nA0 [1]) :=
    .write r0 (show Write3Step 1 [1] nA0 (.ok _) from .ok (by decide))
  have r2 : Reachable K0 [] nA2 := .alloc r1
    (show AllocStep K0 1 0 [(none, none, 0), (some 2, none, 0), (some 2, none, 0)] _ (.ok nA2) from
      .ok (by decide) trivial)
  have r3 : Reachable K0 [] nA3 := .newArena r2 (show NewArenaStep 2 2 nA2 (.ok nA3) from .ok (by decide))
  have r4 : Reachable K0 [] nA4 := .issue r3 (show IssueAt K0 0 0 [3] 0 nA3 (.ok nA4) from
    .ok (ar := arP) (by decide) (.ok (by decide) (by decide) (by decide)))
  have r5 : Reachable K0 [] nA5 := .newArena r4 (show NewArenaStep 3 3 nA4 (.ok nA5) from .ok (by decide))
  have r6 : Reachable K0 [] (releaseEff nA5 3) :=
    .release r5 (show ReleaseStep 3 nA5 (.ok _) from .ok (by decide))
  exact .reset r6 (show ResetAtStep K0 0 0 (releaseEff nA5 3) (.ok _) from .ok (by decide))

/-- In this form, parent and child have the same arena value 0, the holder of both `internal`
(F1), so the `endUse` of the child's value releases both (`arena_dies_with_internal`), and the
`reset` of the parent is then rejected (pass-5 report, (d) 2). -/
example : nA5.arenas.map (arenaValue nA5) = [some 0, some 0] ∧
    EndUseStep K0 0 nA5 (.ok (endUseEff nA5 0)) ∧
    ¬ (endUseEff nA5 0).Active 2 ∧ ¬ (endUseEff nA5 0).Active 3 ∧
    ResetAtStep K0 0 0 (endUseEff nA5 0) .reject :=
  ⟨by decide, .ok (by decide), by decide, by decide, .reject (by decide)⟩

/-! ### Dependency without access -/

/-- Return of a value that only depends (`D`) on a part of a container, without access. Frame 1:
container 0 with parts 1 and 2, result 3; the call passes the authorities 2, which observes the
part 1, and 3, which modifies the result; the callee value 4 depends on 2 and is returned to 3.
After the return, 3 is anchored on the root 0 of the container (A7) and no active authority on the
part 1 is held by 3: the dependency gives no access. A read of the part 1 through the root 1 of
3 is rejected; it was rejected before the call too, since that root never covered the part. -/
def dd0 : S3 := write3Eff (enter1 [(none, none, 0), (some 0, none, 0), (some 0, none, 0),
  (none, none, 0)]) [1, 2]
def dd1 : S3 := enterEff (deriveEff (deriveEff dd0 0 1 .observe) 1 3 .modify) [2, 3]
  [(none, none, 0)]
def dd2 : S3 := dependEff (write3Eff dd1 [4]) 4 2
def dd3 : S3 := exitEff (transferEff dd2 4 3)
example : EnterStep [2, 3] [(none, none, 0)] (deriveEff (deriveEff dd0 0 1 .observe) 1 3 .modify)
    (.ok dd1) := .ok (by decide)
example : DependStep 4 2 (write3Eff dd1 [4]) (.ok dd2) := .ok (by decide)
example : TransferStep K0 4 3 dd2 (.ok (transferEff dd2 4 3)) := .ok (by decide)
example : ExitStep K0 (transferEff dd2 4 3) (.ok dd3) := .ok (by decide)
example : dd3.D 3 = [0] ∧ ∀ j ∈ List.range dd3.A.length, dd3.Active j → 1 ∈ dd3.afp j →
    OptP (dd3.A[j]?) (fun y => y.holder ≠ .place 3) True := by decide
example : Read3Step 1 [1] dd3 .reject := .reject (by decide)


/-! ## Witnesses of the questions of pass 5 -/

/-- A nested arena on a storage of a single part (pass-5 report, (c) 10): the root of the parent
and the block cover the same leaves. Under F1 the caller names `internal`: the root 3 is
rejected, being the `internal` of a live arena, and the block 4 is accepted. Frame 1: 0 arena value, 1 allocator value, 2 block destination; storage 3 with a
single part 4; the parent issues the block 4 on `[4]` to 0. -/
def x0 : S3 := enter1 [(none, none, 0), (none, none, 0), (none, none, 0)]
def x2 : S3 := allocEff (write3Eff x0 [1]) 1 0 [(none, none, 0), (some 3, none, 0)]
def arX : Arena := ⟨3, 3, [4], []⟩
def x3 : S3 := newArenaEff x2 3 3
def x4 : S3 := arenaSet (issueEff x3 arX [4] 0).1 0 (issueEff x3 arX [4] 0).2
def x5 : S3 := newArenaEff x4 4 4
example : footprint x2.P 3 = [4] ∧ footprint x2.P 4 = [4] := by decide
example : NewArenaStep 3 3 x2 (.ok x3) ∧ x3.arenas = [arX] := ⟨.ok (by decide), by decide⟩
example : IssueAt K0 0 0 [4] 0 x3 (.ok x4) :=
  .ok (ar := arX) (by decide) (.ok (by decide) (by decide) (by decide))
example : NewArenaStep 4 3 x4 .reject := .reject (by decide)
example : NewArenaStep 4 4 x4 (.ok x5) ∧
    x5.arenas.map (fun ar => (ar.storage, ar.internal)) = [(3, 3), (4, 4)] :=
  ⟨.ok (by decide), by decide⟩
example : IssueAt K0 1 0 [4] 2 x5
    (.ok (arenaSet (issueEff x5 ⟨4, 4, [4], []⟩ [4] 2).1 1 (issueEff x5 ⟨4, 4, [4], []⟩ [4] 2).2)) :=
  .ok (by decide) (.ok (by decide) (by decide) (by decide))
example : ResetAtStep K0 0 0 x5 .reject := .reject (by decide)

/-- `x2` (pass-5 report, (e) 6; F1): without any arena, the storage 4 is the single part of the
root 3, which is active, `Modify`, without origin, held by the place 0 and covers exactly `[4]`.
Pass 5 rejected `newArena 4` (kind of `IsInternalFor`); F1, which removes that kind, accepts
`newArena 4 3`, with the root 3 as `internal` (expected: `ok`). A second arena with the same root
as `internal`, here on the root place 3, is rejected (expected: reject). -/
example : Reachable K0 [] x2 ∧ HasRight x2 .modify 4 ∧ x2.Usable 4 ∧ x2.arenas = [] ∧
    (x2.A[3]?).map (fun y => (y.origin, y.holder, y.footprint, y.mode, y.active)) =
      some (none, .place 0, [4], .modify, true) ∧
    (x2.P[4]?).map (·.owner) = some (.place 0) ∧ footprint x2.P 4 = [4] ∧
    NewArenaStep 4 3 x2 (.ok (newArenaEff x2 4 3)) ∧
    NewArenaStep 3 3 (newArenaEff x2 4 3) .reject :=
  ⟨.alloc (.write (.enter (.init (by decide)) (.ok (by decide)))
      (show Write3Step 1 [1] x0 (.ok _) from .ok (by decide)))
    (show AllocStep K0 1 0 [(none, none, 0), (some 3, none, 0)] _ (.ok x2) from .ok (by decide) trivial),
   by decide, by decide, by decide, by decide, by decide, by decide, .ok (by decide),
   .reject (by decide)⟩

/-- Two places that share a leaf have the same owner (A5, `WF3`). -/
theorem shared_leaf_same_owner {s : S3} (hw : WF3 s) {q₁ q₂ l : Nat}
    (h₁ : l ∈ footprint s.P q₁) (h₂ : l ∈ footprint s.P q₂) :
    (s.P[q₁]?).map (·.owner) = (s.P[q₂]?).map (·.owner) := by
  obtain ⟨pl, pr, hl, hr, he⟩ := hw.ownerOf (mem_footprint.1 h₁).2.2
  obtain ⟨pl', pr', hl', hr', he'⟩ := hw.ownerOf (mem_footprint.1 h₂).2.2
  rw [hl] at hl'; cases hl'
  rw [hr, hr']; simp [← he, he']

/-- A static owned by another static, a legal behaviour (F3: the owning element stays allowed;
pass-5 report, (c) 2 and (e) 1): a callee holding a derived
`Modify` parameter on static 0 exercises the root of static 1, held by 0 (A2), and transfers 1 to
its local 3; after the exit, static 2, owned by 1, belongs to frame 1, which has exited: frame 0
no longer owns it and it is not usable. With statics without owning element, the callee could
not transfer any static. -/
def stO : Statics := [((none, none, 0), true), ((none, some 0, 0), true), ((none, some 1, 0), true)]
def o3 : S3 := transferEff (enterEff (deriveEff (S3.init stO) 0 0 .modify) [3] [(none, none, 0)]) 1 3
theorem static_not_owned_by_frame0 :
    Reachable K0 stO (exitEff o3) ∧ (exitEff o3).F = [0] ∧ 2 < stO.length ∧
      ¬ OwnedByFrame (exitEff o3).P 0 2 ∧ ¬ (exitEff o3).Usable 2 := by
  refine ⟨.exit (.transfer (.enter (.derive (.init (by decide)) (.ok (by decide))) (.ok (by decide)))
    (.ok (by decide))) (.ok (by decide)), by decide, by decide, fun h => ?_, by decide⟩
  have h1 : OwnedByFrame (exitEff o3).P 1 2 :=
    .place (pl := ⟨none, .place 3, 0⟩) (by decide) rfl
      (.frame (pl := ⟨none, .frame 1, 0⟩) (by decide) rfl)
  exact absurd (h.unique h1) (by decide)

/-- Under F3, `StaticPinnedBottom` asks direct ownership by frame 0: it excludes the initial state
of `stO` where the pinned leaf 2 belongs to the static 2, owned by the static 1 (pass-5 report,
(c) 2). Pass 5 proved the obligation true there and false on the reached state `o3`
(`staticPinnedBottom_not_invariant`, retired). The exit of `o3` is still rejected by the pin
(B4). -/
abbrev KP2 : K := KT [] [2] [] [] []
theorem staticPinnedBottom_excludes_owned_static :
    ¬ StaticPinnedBottom KP2 (S3.init stO) ∧ Reachable KP2 stO o3 ∧ ExitStep KP2 o3 .reject := by
  refine ⟨fun h => ?_, .transfer (.enter (.derive (.init (by decide)) (.ok (by decide)))
    (.ok (by decide))) (.ok (by decide)), .reject (by decide)⟩
  obtain ⟨q, pl, hq, hpl, ho⟩ := h 2 (List.mem_singleton_self _)
  have hlt : q < 3 := lt_of_getElem? hpl
  have key : ∀ q < 3, 2 ∈ footprint (S3.init stO).P q →
      ((S3.init stO).P[q]?).map (·.owner) ≠ some (.frame ((S3.init stO).F.getLastD 0)) := by decide
  exact key q hlt hq (by rw [hpl]; simp [ho])

/-- Why `newArena` asked, in pass 5, a storage owned by a place (pass-5 report, (c) 9 and (e) 4),
and why F1 asks `internal` held by a place. The part 1 of a local of frame 1 is administered by
the authority 1, derived by frame 1 on it and held by frame 1. `enterFrame` may pass it as a
parameter (A3), which changes its holder to frame 2. F1 rejects `newArena 1 1`: the authority 1
is held by a frame, not by a place. -/
def ow0 : S3 := deriveEff (enter1 [(none, none, 0), (some 0, none, 0), (some 0, none, 0)]) 0 1 .modify
example : HasRight ow0 .modify 1 ∧ ow0.Usable 1 ∧ ((ow0.A[1]?).map (·.holder) = some (.frame 1)) ∧
    NewArenaStep 1 1 ow0 .reject := ⟨by decide, by decide, by decide, .reject (by decide)⟩
example : EnterStep [1] [] ow0 (.ok (enterEff ow0 [1] [])) ∧ (enterEff ow0 [1] []).Active 1 ∧
    ((enterEff ow0 [1] []).A[1]?).map (·.holder) = some (.frame 2) ∧
    ((enterEff ow0 [1] []).P[1]?).map (·.owner) = some (.frame 1) :=
  ⟨.ok (by decide), by decide, by decide, by decide⟩

/-! ## Protection of the parameters of a call (F6) -/

/-- `call_protects_params_safe` as stated by F6, transitive form, as a predicate on a state: for a
stack `G ++ f :: F₀`, the current frame being `f` or a frame called by `f` transitively, every
authority exercisable by the current frame (A2, B2) that covers a leaf of the footprint of a
`Modify` authority of `callParams f` is that authority or one of its descendants, whether the
parameter is active or not. It concerns safe accesses only: neither raw pointers nor suspension
are represented. -/
def CallProtects (s : S3) : Prop :=
  ∀ (G : Frames) (f : Nat) (F₀ : Frames), s.F = G ++ f :: F₀ →
    ∀ p ∈ s.callParams f, ∀ y : Authority, s.A[p]? = some y → y.mode = .modify →
      ∀ (b : Nat) (m : Mode), s.ExercisableAt b m → ∀ l ∈ y.footprint, l ∈ s.afp b →
        b = p ∨ p ∈ s.ancs b

/-- The direct form of `CallProtects` (F6): the current frame is `f`. -/
def CallProtectsDirect (s : S3) : Prop :=
  ∀ (f : Nat) (F₀ : Frames), s.F = f :: F₀ →
    ∀ p ∈ s.callParams f, ∀ y : Authority, s.A[p]? = some y → y.mode = .modify →
      ∀ (b : Nat) (m : Mode), s.ExercisableAt b m → ∀ l ∈ y.footprint, l ∈ s.afp b →
        b = p ∨ p ∈ s.ancs b

theorem CallProtects.direct {s : S3} (h : CallProtects s) : CallProtectsDirect s :=
  fun f F₀ hF => h [] f F₀ hF

theorem S3.ExercisableAt.lt {s : S3} {b : Nat} {m : Mode} (h : s.ExercisableAt b m) :
    b < s.A.length := by
  cases h <;> exact lt_of_getElem? ‹_›

/-- The condition of `CallProtects` for one parameter `p`, read on the authorities of `A` and on
both modes: decidable form. -/
def ParamProtected (s : S3) (p : Nat) : Prop :=
  (s.A[p]?).map (·.mode) = some .modify →
    ∀ b ∈ List.range s.A.length, (s.ExercisableAt b .observe ∨ s.ExercisableAt b .modify) →
      ∀ l ∈ s.afp p, l ∈ s.afp b → b = p ∨ p ∈ s.ancs b

instance (s : S3) (p : Nat) : Decidable (ParamProtected s p) := by
  unfold ParamProtected; infer_instance

/-- `CallProtects` holds when every parameter of every frame of the stack is protected
(`ParamProtected`): a decidable sufficient condition, used on concrete states. -/
theorem callProtects_of_check {s : S3}
    (hchk : ∀ f ∈ s.F, ∀ p ∈ s.callParams f, ParamProtected s p) : CallProtects s := by
  intro G f F₀ hF p hp y hy hm b m hex l hl hlb
  have hf : f ∈ s.F := by rw [hF]; exact List.mem_append_right _ (List.mem_cons_self ..)
  exact hchk f hf p hp (by rw [hy]; simp [hm]) b (List.mem_range.2 hex.lt)
    (by cases m with | observe => exact .inl hex | modify => exact .inr hex) l
    (by simp only [S3.afp, hy]; exact hl) hlb

/-- The part of F6 that holds without hypothesis on the call (MM-03.3.5; I1): while an active
`Modify` authority `p` covers a leaf `l`, every authority with a present effective mode on `l` is
`p` or one of its descendants. It says nothing once `p` is released, nor of authorities that are
exercisable without an effective mode on `l`. -/
theorem call_params_effective_protected {s : S3} (h1 : I1 s) {p b l : Nat} {y : Authority}
    (hp : s.A[p]? = some y) (ya : y.active = true) (hm : y.mode = .modify) (hl : l ∈ y.footprint)
    (hb : effective s b l ≠ none) : b = p ∨ p ∈ s.ancs b := by
  by_cases e : b = p
  · exact .inl e
  by_cases hpb : p ∈ s.ancs b
  · exact .inr hpb
  cases he : effective s b l with
  | none => exact absurd he hb
  | some mb =>
    obtain ⟨x, hx, xa, xl, ex⟩ := effective_some he
    by_cases hbp : b ∈ s.ancs p
    · have hd : Mode.modify ∈ descModes s b l := mem_descModes.2 ⟨p, y, hp, ya, hl, hbp, hm⟩
      rcases effOf_cases ex with ⟨h0, -⟩ | ⟨-, hn, -⟩
      · simp [h0] at hd
      · exact absurd hd hn
    · have := (h1 b p x y l e hx hp xa ya xl hl hbp hpb).2
      rw [hm] at this; cases this

/-- F6 is not provable as stated: a counterexample on a reached state, where the caller passes an
authority and one of its descendants. Frame 1: local 0, of root 0; the caller derives 1, `Modify`
on 0, then 2, `Modify` on 0 from 1, and calls with `[1, 2]`. In frame 2, the parameter 1 is
exercisable, covers the leaf 0 of the parameter 2, and is its ancestor, not a descendant. After
the callee releases 2, it writes the leaf 0 through 1. -/
def cp0 : S3 := deriveEff (deriveEff (enter1 [(none, none, 0)]) 0 0 .modify) 1 0 .modify
def cp1 : S3 := enterEff cp0 [1, 2] []
theorem call_protects_params_safe_fails_param :
    Reachable K0 [] cp1 ∧ ¬ CallProtects cp1 ∧
      ReleaseStep 2 cp1 (.ok (releaseEff cp1 2)) ∧ ¬ CallProtects (releaseEff cp1 2) ∧
      Write3Step 1 [0] (releaseEff cp1 2) (.ok (write3Eff (releaseEff cp1 2) [0])) := by
  have hr : Reachable K0 [] cp1 := .enter (.derive (.derive (.enter (.init (by decide))
    (.ok (by decide))) (.ok (by decide))) (.ok (by decide))) (.ok (by decide))
  have key : ∀ s : S3, s.F = [2, 1, 0] → s.callParams 2 = [1, 2] → s.ExercisableAt 1 .modify →
      (s.A[2]?).map (fun y => (y.mode, y.footprint)) = some (.modify, [0]) → s.afp 1 = [0] →
      s.ancs 1 = [0] → ¬ CallProtects s := by
    intro s hF hc hex h2 h1 ha h
    obtain ⟨y, hy, e⟩ := Option.map_eq_some_iff.1 h2
    simp only [Prod.mk.injEq] at e
    have := h.direct 2 [1, 0] hF 2 (by rw [hc]; decide) y hy e.1 1 .modify hex 0 (by rw [e.2]; decide)
      (by rw [h1]; decide)
    rw [ha] at this; simp at this
  exact ⟨hr, key _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    .ok (by decide), key _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    .ok (by decide)⟩

/-- F6 is not provable as stated: a counterexample on a reached state, through owned storage
(A5; A2, held authorities). Frame 1: value 0, of root 0 held by frame 1, which owns the storage
1, of root 1 held by the place 0. The caller derives 2, `Modify` on 1 from the root 1, and 3,
`Modify` on 0, and calls with `[2, 3]`. In frame 2, the root 1, held by the place 0 on which the
parameter 3 has effective `Modify`, is exercisable and covers the leaf 1 of the parameter 2, of
which it is the origin. After the callee releases 2, it writes the leaf 1 through the root 1. -/
def co0 : S3 :=
  deriveEff (deriveEff (enter1 [(none, none, 0), (none, some 0, 0)]) 1 1 .modify) 0 0 .modify
def co1 : S3 := enterEff co0 [2, 3] []
theorem call_protects_params_safe_fails_owned :
    Reachable K0 [] co1 ∧ ¬ CallProtects co1 ∧
      ReleaseStep 2 co1 (.ok (releaseEff co1 2)) ∧ ¬ CallProtects (releaseEff co1 2) ∧
      Write3Step 1 [1] (releaseEff co1 2) (.ok (write3Eff (releaseEff co1 2) [1])) := by
  have hr : Reachable K0 [] co1 := .enter (.derive (.derive (.enter (.init (by decide))
    (.ok (by decide))) (.ok (by decide))) (.ok (by decide))) (.ok (by decide))
  have key : ∀ s : S3, s.F = [2, 1, 0] → s.callParams 2 = [2, 3] → s.ExercisableAt 1 .modify →
      (s.A[2]?).map (fun y => (y.mode, y.footprint)) = some (.modify, [1]) → s.afp 1 = [1] →
      s.ancs 1 = [] → ¬ CallProtects s := by
    intro s hF hc hex h2 h1 ha h
    obtain ⟨y, hy, e⟩ := Option.map_eq_some_iff.1 h2
    simp only [Prod.mk.injEq] at e
    have := h.direct 2 [1, 0] hF 2 (by rw [hc]; decide) y hy e.1 1 .modify hex 1 (by rw [e.2]; decide)
      (by rw [h1]; decide)
    rw [ha] at this; simp at this
  exact ⟨hr, key _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    .ok (by decide), key _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    .ok (by decide)⟩

/-! ## New cases of pass 6 -/

/-! ### Nested arena with a child value (F1) -/

/-- An arena nested in a block issued to a value distinct from the parent arena value (F1: the
child arena value is the holder of its `internal`, the block). Frame 1: 0 parent arena value,
1 allocator value, 2 child arena value; storage 3 with parts 4 and 5, owned by 0, of root 3; the
parent issues the block 4 on `[4]` to 2; `newArena 4 4` registers the child on the part 4. The
`reset` of the parent is rejected while the child lives (expected: reject); after the `endUse` of
the child value, which releases the block, it is accepted (expected: `ok`). -/
def na0 : S3 := enter1 [(none, none, 0), (none, none, 0), (none, none, 0)]
def na1 : S3 :=
  allocEff (write3Eff na0 [1]) 1 0 [(none, none, 0), (some 3, none, 0), (some 3, none, 0)]
def na2 : S3 := newArenaEff na1 3 3
def arNa : Arena := ⟨3, 3, [4, 5], []⟩
def na3 : S3 := arenaSet (issueEff na2 arNa [4] 2).1 0 (issueEff na2 arNa [4] 2).2
def na4 : S3 := newArenaEff na3 4 4
example : NewArenaStep 3 3 na1 (.ok na2) := .ok (by decide)
example : IssueAt K0 0 0 [4] 2 na2 (.ok na3) :=
  .ok (ar := arNa) (by decide) (.ok (by decide) (by decide) (by decide))
example : NewArenaStep 4 4 na3 (.ok na4) := .ok (by decide)
example : na4.arenas.map (arenaValue na4) = [some 0, some 2] := by decide
example : ResetAtStep K0 0 0 na4 .reject := .reject (by decide)
example : EndUseStep K0 2 na4 (.ok (endUseEff na4 2)) := .ok (by decide)
example : ¬ (endUseEff na4 2).Active 4 := by decide
example : ResetAtStep K0 0 0 (endUseEff na4 2) (.ok (resetAtEff (endUseEff na4 2) 0)) :=
  .ok (by decide)

/-! ### Arena on a local buffer (F1, F2, F4) -/

/-- An arena whose storage is a local buffer of the callee, administered by a derived authority
stored into the arena value. Frame 1: 0 result; it derives 1, `Modify` on 0, and calls. Frame 2:
1 arena value, 2 buffer with parts 3 and 4, 5 and 6 block destinations, 7 another local. The
callee derives 7, `Modify` on 2, stores it into 1, registers `newArena 2 7`, and issues `[3]` and
`[4]` (expected: `ok` for each). The transfer of the arena value to the caller's result is
rejected at the `transfer` (expected: reject): the stored authority is an anchor of the arena
value whose effective anchor, the root of the buffer, is held by frame 2 (C1, B8). The transfer
to another local of frame 2 is accepted (expected: `ok`). -/
def lb0 : S3 := enterEff (deriveEff (enter1 [(none, none, 0)]) 0 0 .modify) [1]
  [(none, none, 0), (none, none, 0), (some 2, none, 0), (some 2, none, 0), (none, none, 0),
   (none, none, 0), (none, none, 0)]
def lb1 : S3 := deriveEff lb0 3 2 .modify
def lb2 : S3 := storeEff lb1 7 1
def lb3 : S3 := newArenaEff lb2 2 7
def arLb : Arena := ⟨2, 7, [3, 4], []⟩
def lb4 : S3 := arenaSet (issueEff lb3 arLb [3] 5).1 0 (issueEff lb3 arLb [3] 5).2
def arLb' : Arena := ⟨2, 7, [4], [([3], 8)]⟩
def lb5 : S3 := arenaSet (issueEff lb4 arLb' [4] 6).1 0 (issueEff lb4 arLb' [4] 6).2
example : DeriveStep 3 2 .modify lb0 (.ok lb1) := .ok (by decide)
example : StoreStep 7 1 lb1 (.ok lb2) := .ok (by decide)
example : NewArenaStep 2 7 lb2 (.ok lb3) := .ok (by decide)
example : lb3.arenas = [arLb] ∧ arenaValue lb3 arLb = some 1 := by decide
example : IssueAt K0 0 1 [3] 5 lb3 (.ok lb4) :=
  .ok (ar := arLb) (by decide) (.ok (by decide) (by decide) (by decide))
example : lb4.arenas = [arLb'] := by decide
example : IssueAt K0 0 1 [4] 6 lb4 (.ok lb5) :=
  .ok (ar := arLb') (by decide) (.ok (by decide) (by decide) (by decide))
example : TransferStep K0 1 0 lb5 .reject := .reject (by decide)
example : TransferStep K0 1 7 lb5 (.ok (transferEff lb5 1 7)) := .ok (by decide)

/-- A value that holds a block derived from a local buffer, without being anchored on it, is not
stopped at the `transfer` (pass-6 report, (d) and (e)): the block 8 is held by the local 5 of
frame 2, derived from `internal` 7, of effective anchor the root 3 of the buffer, held by frame 2;
`issue` does not add it to the anchors of 5 (A10). The transfer of 5 to the caller's result 0 is
accepted, and the block is then held by a place of frame 1; the exit of frame 2 is rejected
(O7, A7: the block survives and its ancestors do not). -/
example : (lb5.A[8]?).map (fun y => (y.origin, y.holder, y.footprint)) = some (some 7, .place 5, [3]) ∧
    lb5.D 5 = [] := by decide
example : TransferStep K0 5 0 lb5 (.ok (transferEff lb5 5 0)) := .ok (by decide)
example : ((transferEff lb5 5 0).A[8]?).map (·.holder) = some (.place 0) ∧
    (transferEff lb5 5 0).pframe 0 = some 1 := by decide
example : ExitStep K0 (transferEff lb5 5 0) .reject := .reject (by decide)
theorem lb5_reachable : Reachable K0 [] lb5 ∧ Reachable K0 [] (transferEff lb5 5 0) := by
  have r0 : Reachable K0 [] lb0 := .enter (.derive (.enter (.init (by decide)) (.ok (by decide)))
    (.ok (by decide))) (.ok (by decide))
  have r3 : Reachable K0 [] lb3 := .newArena (.store (.derive r0
    (show DeriveStep 3 2 .modify lb0 (.ok lb1) from .ok (by decide)))
    (show StoreStep 7 1 lb1 (.ok lb2) from .ok (by decide)))
    (show NewArenaStep 2 7 lb2 (.ok lb3) from .ok (by decide))
  have r5 : Reachable K0 [] lb5 := .issue (.issue r3 (show IssueAt K0 0 1 [3] 5 lb3 (.ok lb4) from
    .ok (ar := arLb) (by decide) (.ok (by decide) (by decide) (by decide))))
    (show IssueAt K0 0 1 [4] 6 lb4 (.ok lb5) from
      .ok (ar := arLb') (by decide) (.ok (by decide) (by decide) (by decide)))
  exact ⟨r5, .transfer r5 (show TransferStep K0 5 0 lb5 (.ok _) from .ok (by decide))⟩

/-! ### Arena on an allocation owned by its value, returned (F1) -/

/-- Frame 1: 0 result; it derives 1, `Modify` on 0, and calls. Frame 2: 1 arena value,
2 allocator value; `alloc 2 1` gives the storage 3 with the part 4, owned by 1, of root 4 held by
1; `newArena 3 4`. The arena value is transferred to the caller's result and the callee exits
(expected: `ok`, `ok`): the arena stays live, with the caller's result as arena value. -/
def ra0 : S3 := enterEff (deriveEff (enter1 [(none, none, 0)]) 0 0 .modify) [1]
  [(none, none, 0), (none, none, 0)]
def ra1 : S3 := allocEff (write3Eff (write3Eff ra0 [2]) [1]) 2 1 [(none, none, 0), (some 3, none, 0)]
def ra2 : S3 := newArenaEff ra1 3 4
example : AllocStep K0 2 1 [(none, none, 0), (some 3, none, 0)] (write3Eff (write3Eff ra0 [2]) [1])
    (.ok ra1) := .ok (by decide) trivial
example : NewArenaStep 3 4 ra1 (.ok ra2) := .ok (by decide)
example : TransferStep K0 1 0 ra2 (.ok (transferEff ra2 1 0)) := .ok (by decide)
example : ExitStep K0 (transferEff ra2 1 0) (.ok (exitEff (transferEff ra2 1 0))) := .ok (by decide)
example : (exitEff (transferEff ra2 1 0)).Active 4 ∧
    (exitEff (transferEff ra2 1 0)).arenas.map (arenaValue (exitEff (transferEff ra2 1 0))) =
      [some 0] := by decide

/-! ### A view stored in a structure (F4) -/

/-- Frame 1: 0 result; it derives 1, `Modify` on 0, and calls. Frame 2: 1 array, 2 structure,
3 another structure. The callee writes the array, derives 5, an `Observe` view on it, and stores
it into the structure 2 (expected: `ok`). The transfer of the structure to the caller's result
is rejected at the `transfer` (expected: reject; `store_escape_rejected_at_transfer`); to the
other local 3, accepted (expected: `ok`). -/
def vw0 : S3 := enterEff (deriveEff (enter1 [(none, none, 0)]) 0 0 .modify) [1]
  [(none, none, 0), (none, none, 0), (none, none, 0)]
def vw1 : S3 := write3Eff vw0 [1]
def vw2 : S3 := deriveEff vw1 2 1 .observe
def vw3 : S3 := storeEff vw2 5 2
example : DeriveStep 2 1 .observe vw1 (.ok vw2) := .ok (by decide)
example : StoreStep 5 2 vw2 (.ok vw3) := .ok (by decide)
example : TransferStep K0 2 0 vw3 .reject := .reject (by decide)
example : TransferStep K0 2 3 vw3 (.ok (transferEff vw3 2 3)) := .ok (by decide)
/-- The same rejection, obtained from `store_escape_rejected_at_transfer` on the reached state
`vw3`: the effective anchor of 5 is the root 2 of the array, held by frame 2, and the result 0 is
of frame 1. -/
theorem vw3_escape_rejected : Reachable K0 [] vw3 ∧ TransferStep K0 2 0 vw3 .reject := by
  have r : Reachable K0 [] vw3 := .store (.derive (.write (.enter (.derive (.enter (.init (by decide))
    (.ok (by decide))) (.ok (by decide))) (.ok (by decide))) (show Write3Step 2 [1] vw0 (.ok vw1) from
      .ok (by decide))) (show DeriveStep 2 1 .observe vw1 (.ok vw2) from .ok (by decide)))
    (show StoreStep 5 2 vw2 (.ok vw3) from .ok (by decide))
  refine ⟨r, store_escape_rejected_at_transfer (a := 5) (f := 2) (g := 1) (F₀ := [1, 0])
    (z := ⟨.modify, none, [1], .frame 2, true⟩)
    (reachable_access_invariant_underDD (KT_dd [] [] [] [] []) r).1 (by decide) (by decide)
    (by decide) (by decide) rfl (by decide) (by decide)⟩

/-- A view stored into a field of a structure (F4; MM-03.3.6): frame 2 has 1 array, 2 structure
with the field 3, 4 another local. The view 5 on the array is stored into the field 3 (expected:
`ok`); it is an anchor of the field, not of the structure. The transfer of the structure to the
caller's result is rejected (expected: reject), the dependency of the field following the value
(`depsOf`); to the other local 4, accepted (expected: `ok`). -/
def fw0 : S3 := enterEff (deriveEff (enter1 [(none, none, 0)]) 0 0 .modify) [1]
  [(none, none, 0), (none, none, 0), (some 2, none, 0), (none, none, 0)]
def fw1 : S3 := write3Eff fw0 [1]
def fw2 : S3 := deriveEff fw1 2 1 .observe
def fw3 : S3 := storeEff fw2 5 3
example : DeriveStep 2 1 .observe fw1 (.ok fw2) := .ok (by decide)
example : StoreStep 5 3 fw2 (.ok fw3) := .ok (by decide)
example : 5 ∉ fw3.D 2 ∧ 5 ∈ fw3.D 3 := by decide
example : TransferStep K0 2 0 fw3 .reject := .reject (by decide)
example : TransferStep K0 2 4 fw3 (.ok (transferEff fw3 2 4)) := .ok (by decide)
theorem fw3_escape_rejected : Reachable K0 [] fw3 ∧ TransferStep K0 2 0 fw3 .reject := by
  have r : Reachable K0 [] fw3 := .store (.derive (.write (.enter (.derive (.enter (.init (by decide))
    (.ok (by decide))) (.ok (by decide))) (.ok (by decide))) (show Write3Step 2 [1] fw0 (.ok fw1) from
      .ok (by decide))) (show DeriveStep 2 1 .observe fw1 (.ok fw2) from .ok (by decide)))
    (show StoreStep 5 3 fw2 (.ok fw3) from .ok (by decide))
  refine ⟨r, store_escape_rejected_at_transfer (a := 5) (f := 2) (g := 1) (F₀ := [1, 0])
    (z := ⟨.modify, none, [1], .frame 2, true⟩)
    (reachable_access_invariant_underDD (KT_dd [] [] [] [] []) r).1 (by decide) (by decide)
    (by decide) (by decide) rfl (by decide) (by decide)⟩

/-- A view on a local owned by another local (F4; A5): frame 2 has 1 a value, 2 a local owned by
1, of root 3 held by the place 1, 3 a structure, 4 another local. The view 6 on 2 is stored into
3. Its effective anchor, the root 3, is held by a place of frame 2 that does not move with the
structure: the transfer of the structure to the caller's result is rejected
(`store_escape_rejected_at_transfer`), to the other local 4 accepted (expected: reject; `ok`). -/
def hw0 : S3 := enterEff (deriveEff (enter1 [(none, none, 0)]) 0 0 .modify) [1]
  [(none, none, 0), (none, some 1, 0), (none, none, 0), (none, none, 0)]
def hw1 : S3 := write3Eff hw0 [2]
def hw2 : S3 := deriveEff hw1 3 2 .observe
def hw3 : S3 := storeEff hw2 6 3
example : (hw3.A[hw3.effAnchor 6]?).map (·.holder) = some (.place 1) := by decide
example : TransferStep K0 3 4 hw3 (.ok (transferEff hw3 3 4)) := .ok (by decide)
theorem hw3_escape_rejected : Reachable K0 [] hw3 ∧ TransferStep K0 3 0 hw3 .reject := by
  have r : Reachable K0 [] hw3 := .store (.derive (.write (.enter (.derive (.enter (.init (by decide))
    (.ok (by decide))) (.ok (by decide))) (.ok (by decide))) (show Write3Step 3 [2] hw0 (.ok hw1) from
      .ok (by decide))) (show DeriveStep 3 2 .observe hw1 (.ok hw2) from .ok (by decide)))
    (show StoreStep 6 3 hw2 (.ok hw3) from .ok (by decide))
  refine ⟨r, store_escape_rejected_at_transfer (a := 6) (f := 2) (g := 1) (F₀ := [1, 0])
    (z := ⟨.modify, none, [2], .place 1, true⟩)
    (reachable_access_invariant_underDD (KT_dd [] [] [] [] []) r).1 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)⟩

/-! ### A second arena on the same root (F1) -/

/-- The case `x2` (`newArena 4 3` accepted, a second arena with the root 3 as `internal`
rejected) is in the witnesses of pass 5. F1 guards by `internal` only: once the frame derives
4, `Modify` on the root place 3, from the root 3 and stores it into the place 2, a second arena
on the root place 3 with `internal` 4 is accepted while the first lives (pass-6 report, (e)). -/
def y1 : S3 := deriveEff (newArenaEff x2 4 3) 3 3 .modify
def y3 : S3 := storeEff y1 4 2
example : DeriveStep 3 3 .modify (newArenaEff x2 4 3) (.ok y1) := .ok (by decide)
example : StoreStep 4 2 y1 (.ok y3) := .ok (by decide)
example : y3.Active 3 ∧ NewArenaStep 3 4 y3 (.ok (newArenaEff y3 3 4)) := ⟨by decide, .ok (by decide)⟩
/-- In the state of the case `x2`, before that derivation, every second arena on the root place 3
or its part 4 is rejected, whatever its `internal` (an index beyond `A` fails `NewArenaPre`). -/
example : ∀ st ∈ [3, 4], ∀ i ∈ List.range (newArenaEff x2 4 3).A.length,
    ¬ NewArenaPre (newArenaEff x2 4 3) st i := by decide

/-! ### `store` of a root (F4) -/

/-- Frame 1: locals 0 and 1, of roots 0 and 1. Storing the root 0 into 1 is rejected (expected:
reject; `store_root_rejected`); storing a `Modify` derived from it is accepted (expected: `ok`). -/
def sr0 : S3 := enter1 [(none, none, 0), (none, none, 0)]
example : StoreStep 0 1 sr0 .reject :=
  store_root_rejected (y := ⟨.modify, none, [0], .frame 1, true⟩) (by decide) rfl
example : StoreStep 2 1 (deriveEff sr0 0 0 .modify) (.ok (storeEff (deriveEff sr0 0 0 .modify) 2 1)) :=
  .ok (by decide)

/-! ### `store`, then the end of the value that holds the origin (F4; A6) -/

/-- Frame 1: 0 value, 1 storage owned by 0, of root 1 held by 0, 2 another local. The frame
derives 3, `Modify` on 1, and stores it into 2. The `endUse` of 0, which releases the root 1, is
rejected (expected: reject): 3 descends from it and is held by 2 (A6; MM-03.3 §3, O3.2). After
the `release` of 3 (expected: `ok`; F4: 3 leaves the anchors of 2), the same `endUse` is accepted
(expected: `ok`). -/
def se0 : S3 := enter1 [(none, none, 0), (none, some 0, 0), (none, none, 0)]
def se1 : S3 := deriveEff se0 1 1 .modify
def se2 : S3 := storeEff se1 3 2
example : DeriveStep 1 1 .modify se0 (.ok se1) := .ok (by decide)
example : StoreStep 3 2 se1 (.ok se2) := .ok (by decide)
example : se2.D 2 = [3] := by decide
example : EndUseStep K0 0 se2 .reject := .reject (by decide)
example : ReleaseStep 3 se2 (.ok (releaseEff se2 3)) := .ok (by decide)
example : (releaseEff se2 3).D 2 = [] := by decide
example : EndUseStep K0 0 (releaseEff se2 3) (.ok (endUseEff (releaseEff se2 3) 0)) :=
  .ok (by decide)

/-! ### `transfer(x, x.f)` (F5) -/

/-- Frame 1: 0 value `x` with the field 1, 2 a local `tmp`; the field is written. `transfer(x,
x.f)` is rejected (expected: reject): the footprints overlap (F5), and the destination is
initialised. Twin: `transfer(x.f, tmp)` then `transfer(tmp, x)` (expected: `ok`, `ok`). -/
def tx0 : S3 := write3Eff (enter1 [(none, none, 0), (some 0, none, 0), (none, none, 0)]) [1]
example : TransferStep K0 0 1 tx0 .reject := .reject (by decide)
example : overlap tx0.P 0 1 ∧ tx0.I 1 = .init := by decide
example : TransferStep K0 1 2 tx0 (.ok (transferEff tx0 1 2)) := .ok (by decide)
example : TransferStep K0 2 0 (transferEff tx0 1 2) (.ok (transferEff (transferEff tx0 1 2) 2 0)) :=
  .ok (by decide)

/-! ### Non-vacuity of F6 -/

/-- Frame 1: local 0, of root 0; it derives 1, `Modify` on 0, and calls with `[1]`. In frame 2,
the root 0 of the caller covers the footprint of the parameter and is not exercisable by the
callee; `CallProtects` holds. After the callee releases the parameter (expected: `ok`), a write
or a read through the root and a derivation from it are rejected (expected: reject), and
`CallProtects` still holds. Two nested calls: frame 2 derives 2 from 1 and calls with `[2]`; in
frame 3 neither 0 nor 1 is exercisable; after releasing 2, a write through 1 or 0 is rejected;
`CallProtects` holds in its transitive form. Positive twins: the callee writes and reads through
the parameter; after the release and the exit, the caller writes and derives through its root;
in the nested case, frame 2 writes through 1 after the exit of frame 3, and frame 1 through 0
after the exit of frame 2. In `pw0` the leaf is initialised before the call, so the rejected read
through the root after the release fails on exercise alone, and is accepted after the exit. -/
def pv0 : S3 := enterEff (deriveEff (enter1 [(none, none, 0)]) 0 0 .modify) [1] []
def pv1 : S3 := enterEff (deriveEff pv0 1 0 .modify) [2] []
example : pv0.callParams 2 = [1] ∧ pv0.afp 0 = pv0.afp 1 ∧ ¬ pv0.ExercisableAt 0 .modify ∧
    ¬ pv0.ExercisableAt 0 .observe := by decide
example : CallProtects pv0 := callProtects_of_check (by decide)
example : ReleaseStep 1 pv0 (.ok (releaseEff pv0 1)) := .ok (by decide)
example : Write3Step 0 [0] (releaseEff pv0 1) .reject := .reject (by decide)
example : Read3Step 0 [0] (releaseEff pv0 1) .reject := .reject (by decide)
example : DeriveStep 0 0 .modify (releaseEff pv0 1) .reject := .reject (by decide)
example : CallProtects (releaseEff pv0 1) := callProtects_of_check (by decide)
example : EnterStep [2] [] (deriveEff pv0 1 0 .modify) (.ok pv1) := .ok (by decide)
example : pv1.F = [3, 2, 1, 0] ∧ ¬ pv1.ExercisableAt 0 .observe ∧ ¬ pv1.ExercisableAt 1 .observe :=
  by decide
example : CallProtects pv1 := callProtects_of_check (by decide)
example : ReleaseStep 2 pv1 (.ok (releaseEff pv1 2)) := .ok (by decide)
example : Write3Step 1 [0] (releaseEff pv1 2) .reject := .reject (by decide)
example : Write3Step 0 [0] (releaseEff pv1 2) .reject := .reject (by decide)
example : CallProtects (releaseEff pv1 2) := callProtects_of_check (by decide)
example : Write3Step 1 [0] pv0 (.ok (write3Eff pv0 [0])) := .ok (by decide)
example : Read3Step 1 [0] (write3Eff pv0 [0]) (.ok (write3Eff pv0 [0])) := .ok (by decide)
example : ExitStep K0 (releaseEff pv0 1) (.ok (exitEff (releaseEff pv0 1))) := .ok (by decide)
example : Write3Step 0 [0] (exitEff (releaseEff pv0 1))
    (.ok (write3Eff (exitEff (releaseEff pv0 1)) [0])) := .ok (by decide)
example : DeriveStep 0 0 .modify (exitEff (releaseEff pv0 1))
    (.ok (deriveEff (exitEff (releaseEff pv0 1)) 0 0 .modify)) := .ok (by decide)
example : Write3Step 2 [0] pv1 (.ok (write3Eff pv1 [0])) := .ok (by decide)
example : ExitStep K0 (releaseEff pv1 2) (.ok (exitEff (releaseEff pv1 2))) := .ok (by decide)
example : Write3Step 1 [0] (exitEff (releaseEff pv1 2))
    (.ok (write3Eff (exitEff (releaseEff pv1 2)) [0])) := .ok (by decide)
example : Write3Step 0 [0] (exitEff (releaseEff (exitEff (releaseEff pv1 2)) 1))
    (.ok (write3Eff (exitEff (releaseEff (exitEff (releaseEff pv1 2)) 1)) [0])) := .ok (by decide)
def pw0 : S3 := enterEff (deriveEff (write3Eff (enter1 [(none, none, 0)]) [0]) 0 0 .modify) [1] []
example : CallProtects pw0 := callProtects_of_check (by decide)
example : Read3Step 1 [0] pw0 (.ok pw0) := .ok (by decide)
example : ReleaseStep 1 pw0 (.ok (releaseEff pw0 1)) := .ok (by decide)
example : (releaseEff pw0 1).I 0 = .init ∧ ¬ (releaseEff pw0 1).ExercisableAt 0 .observe := by decide
example : Read3Step 0 [0] (releaseEff pw0 1) .reject := .reject (by decide)
example : ExitStep K0 (releaseEff pw0 1) (.ok (exitEff (releaseEff pw0 1))) := .ok (by decide)
example : Read3Step 0 [0] (exitEff (releaseEff pw0 1)) (.ok (exitEff (releaseEff pw0 1))) :=
  .ok (by decide)

/-! ### Progress (F7) -/

/-- F7 (a), cycle on whole nodes. Frame 1: 0 arena value, 1 allocator value, 2 and 3 node
values; storage 4 with the nodes 5 (A) and 6 (B), owned by 0, of root 4; `newArena 4 4`; the
blocks 5 on `[5]` and 6 on `[6]` are issued to 2 and 3. The frame derives 7, `Modify` on B from
the block 6, and stores it into A; then derives 8, `Modify` on A from the block 5, and stores it
into B. Expected: the second `store` rejected. Obtained: accepted. In `fa7`, before it, the block
6 has lost its effective `Modify` on B to 7, but 7, held by A, is exercisable through 8, held by
the frame, which has effective `Modify` on A (B2): `HasRight` on B holds, and no clause of
`StorePre` fails. In `fa8`, neither 7 nor 8 is exercisable, and `release` of 7 or 8, `endUse` of
2 or 3 and `reset` are rejected; the `endUse` and `reset` rejections already hold before the
second store, where 8 could still be released first. The exit of frame 1 releases both; so does
the end of the arena value before the exit (`progress_cycle_freed_before_exit`). Whether a
sequence frees 7 or 8 while keeping the arena live is open (F7: no conclusion of impossibility
without proof). Each state is reached from `S3.init []`; the list of arenas is non-empty from `fa2` on. -/
def fa0 : S3 := enter1 [(none, none, 0), (none, none, 0), (none, none, 0), (none, none, 0)]
def fa1 : S3 :=
  allocEff (write3Eff fa0 [1]) 1 0 [(none, none, 0), (some 4, none, 0), (some 4, none, 0)]
def fa2 : S3 := newArenaEff fa1 4 4
def arFa : Arena := ⟨4, 4, [5, 6], []⟩
def fa3 : S3 := arenaSet (issueEff fa2 arFa [5] 2).1 0 (issueEff fa2 arFa [5] 2).2
def arFa' : Arena := ⟨4, 4, [6], [([5], 5)]⟩
def fa4 : S3 := arenaSet (issueEff fa3 arFa' [6] 3).1 0 (issueEff fa3 arFa' [6] 3).2
def fa5 : S3 := deriveEff fa4 6 6 .modify
def fa6 : S3 := storeEff fa5 7 5
def fa7 : S3 := deriveEff fa6 5 5 .modify
def fa8 : S3 := storeEff fa7 8 6
theorem progress_cycle_whole_nodes :
    Reachable K0 [] fa8 ∧ fa8.arenas ≠ [] ∧ StoreStep 7 5 fa5 (.ok fa6) ∧
      StoreStep 8 6 fa7 (.ok fa8) ∧ effective fa7 6 6 = none ∧ fa7.ExercisableAt 7 .modify ∧
      HasRight fa7 .modify 6 ∧
      ¬ fa8.ExercisableAt 7 .observe ∧ ¬ fa8.ExercisableAt 8 .observe ∧
      ReleaseStep 7 fa8 .reject ∧ ReleaseStep 8 fa8 .reject ∧ EndUseStep K0 2 fa8 .reject ∧
      EndUseStep K0 3 fa8 .reject ∧ ResetAtStep K0 0 0 fa8 .reject ∧
      Reachable K0 [] (exitEff fa8) ∧ ¬ (exitEff fa8).Active 7 ∧ ¬ (exitEff fa8).Active 8 := by
  have r0 : Reachable K0 [] fa0 := .enter (.init (by decide)) (.ok (by decide))
  have r1 : Reachable K0 [] fa1 := .alloc (.write r0 (show Write3Step 1 [1] fa0 (.ok _) from
    .ok (by decide))) (show AllocStep K0 1 0 [(none, none, 0), (some 4, none, 0), (some 4, none, 0)]
      _ (.ok fa1) from .ok (by decide) trivial)
  have r2 : Reachable K0 [] fa2 := .newArena r1 (show NewArenaStep 4 4 fa1 (.ok fa2) from .ok (by decide))
  have r3 : Reachable K0 [] fa3 := .issue r2 (show IssueAt K0 0 0 [5] 2 fa2 (.ok fa3) from
    .ok (ar := arFa) (by decide) (.ok (by decide) (by decide) (by decide)))
  have r4 : Reachable K0 [] fa4 := .issue r3 (show IssueAt K0 0 0 [6] 3 fa3 (.ok fa4) from
    .ok (ar := arFa') (by decide) (.ok (by decide) (by decide) (by decide)))
  have r5 : Reachable K0 [] fa5 := .derive r4 (show DeriveStep 6 6 .modify fa4 (.ok fa5) from
    .ok (by decide))
  have s6 : StoreStep 7 5 fa5 (.ok fa6) := .ok (by decide)
  have r7 : Reachable K0 [] fa7 := .derive (.store r5 s6) (show DeriveStep 5 5 .modify fa6 (.ok fa7) from
    .ok (by decide))
  have s8 : StoreStep 8 6 fa7 (.ok fa8) := .ok (by decide)
  have r8 : Reachable K0 [] fa8 := .store r7 s8
  have hx : ExitStep K0 fa8 (.ok (exitEff fa8)) := .ok (by decide)
  exact ⟨r8, by decide, s6, s8, by decide, by decide, by decide, by decide, by decide,
    .reject (by decide), .reject (by decide), .reject (by decide), .reject (by decide),
    .reject (by decide), .exit r8 hx, by decide, by decide⟩

/-- Before the second store of F7 (a), in `fa7`: `release 8` is accepted, while `endUse` of 2 and
3 and `reset` are already rejected. -/
example : ReleaseStep 8 fa7 (.ok (releaseEff fa7 8)) := .ok (by decide)
example : EndUseStep K0 2 fa7 .reject ∧ EndUseStep K0 3 fa7 .reject ∧ ResetAtStep K0 0 0 fa7 .reject :=
  ⟨.reject (by decide), .reject (by decide), .reject (by decide)⟩

/-- F7 (a): the cycle is undone before the exit of frame 1, at the cost of the arena. In `fa8`,
`endUse 0` of the arena value is rejected (the node values hold live blocks). The frame
allocates two places 7 and 8 owned by 0, transfers the node values 2 and 3 into them (A5: the
blocks are then held within the storage of 0), and ends 0: the storage 4, its parts and the
places 7 and 8 die, and 7 and 8, the stored authorities, are released (A6). Frame 1 is still the
current frame; the arena is dead and cannot be reset. -/
def fc1 : S3 := allocEff fa8 1 0 [(none, none, 0), (none, none, 0)]
def fc4 : S3 := endUseEff (transferEff (transferEff fc1 2 7) 3 8) 0
theorem progress_cycle_freed_before_exit :
    EndUseStep K0 0 fa8 .reject ∧ Reachable K0 [] fc4 ∧ fc4.F = [1, 0] ∧ ¬ fc4.Active 7 ∧
      ¬ fc4.Active 8 ∧ ¬ fc4.Active 4 ∧ ResetAtStep K0 0 0 fc4 .reject :=
  ⟨.reject (by decide), .endUse (.transfer (.transfer (.alloc progress_cycle_whole_nodes.1
    (.ok (by decide) trivial)) (.ok (by decide))) (.ok (by decide))) (.ok (by decide)), by decide,
    by decide, by decide, by decide, .reject (by decide)⟩
example : (fc1.P[7]?).map (·.owner) = some (.place 0) ∧ (fc1.P[8]?).map (·.owner) = some (.place 0) :=
  by decide
example : ((transferEff (transferEff fc1 2 7) 3 8).A[5]?).map (·.holder) = some (.place 7) ∧
    ((transferEff (transferEff fc1 2 7) 3 8).A[6]?).map (·.holder) = some (.place 8) := by decide
example : ¬ fc4.Usable 4 ∧ ¬ fc4.Usable 5 ∧ ¬ fc4.Usable 6 ∧ ¬ fc4.Usable 7 ∧ ¬ fc4.Usable 8 := by decide

/-- F7 (b), cycle on disjoint fields. Same frame; storage 4 with the nodes 5 (A, fields 6 `data`
and 7 `link`) and 8 (B, fields 9 `data` and 10 `link`); blocks 5 on `[6, 7]` and 6 on `[9, 10]`
issued to 2 and 3. The frame derives 7, `Modify` on `B.data` from the block 6, and stores it into
`A.link`; then 8, `Modify` on `A.data` from the block 5, stored into `B.link` (expected and
obtained: `ok`). Teardown: `release` of 7 and 8 (F4: each leaves the anchors of its holder),
`endUse` of the node values 2 and 3, which releases the blocks, then `reset` of the arena
(expected and obtained: `ok` at each step). Each state is reached from `S3.init []`. -/
def fb1 : S3 := allocEff (write3Eff fa0 [1]) 1 0 [(none, none, 0), (some 4, none, 0),
  (some 5, none, 0), (some 5, none, 0), (some 4, none, 0), (some 8, none, 0), (some 8, none, 0)]
def fb2 : S3 := newArenaEff fb1 4 4
def arFb : Arena := ⟨4, 4, [6, 7, 9, 10], []⟩
def fb3 : S3 := arenaSet (issueEff fb2 arFb [6, 7] 2).1 0 (issueEff fb2 arFb [6, 7] 2).2
def arFb' : Arena := ⟨4, 4, [9, 10], [([6, 7], 5)]⟩
def fb4 : S3 := arenaSet (issueEff fb3 arFb' [9, 10] 3).1 0 (issueEff fb3 arFb' [9, 10] 3).2
def fb5 : S3 := deriveEff fb4 6 9 .modify
def fb6 : S3 := storeEff fb5 7 7
def fb7 : S3 := deriveEff fb6 5 6 .modify
def fb8 : S3 := storeEff fb7 8 10
def fb9 : S3 := releaseEff (releaseEff fb8 7) 8
def fb10 : S3 := endUseEff (endUseEff fb9 2) 3
theorem progress_cycle_disjoint_fields :
    Reachable K0 [] (resetAtEff fb10 0) ∧ fb8.arenas ≠ [] ∧ fb10.arenas ≠ [] ∧
      StoreStep 7 7 fb5 (.ok fb6) ∧ StoreStep 8 10 fb7 (.ok fb8) ∧
      ReleaseStep 7 fb8 (.ok (releaseEff fb8 7)) ∧ ReleaseStep 8 (releaseEff fb8 7) (.ok fb9) ∧
      EndUseStep K0 2 fb9 (.ok (endUseEff fb9 2)) ∧ EndUseStep K0 3 (endUseEff fb9 2) (.ok fb10) ∧
      ResetAtStep K0 0 0 fb10 (.ok (resetAtEff fb10 0)) := by
  have r0 : Reachable K0 [] fa0 := .enter (.init (by decide)) (.ok (by decide))
  have r1 : Reachable K0 [] fb1 := .alloc (.write r0 (show Write3Step 1 [1] fa0 (.ok _) from
    .ok (by decide))) (show AllocStep K0 1 0 [(none, none, 0), (some 4, none, 0), (some 5, none, 0),
      (some 5, none, 0), (some 4, none, 0), (some 8, none, 0), (some 8, none, 0)] _ (.ok fb1) from
      .ok (by decide) trivial)
  have r2 : Reachable K0 [] fb2 := .newArena r1 (show NewArenaStep 4 4 fb1 (.ok fb2) from .ok (by decide))
  have r3 : Reachable K0 [] fb3 := .issue r2 (show IssueAt K0 0 0 [6, 7] 2 fb2 (.ok fb3) from
    .ok (ar := arFb) (by decide) (.ok (by decide) (by decide) (by decide)))
  have r4 : Reachable K0 [] fb4 := .issue r3 (show IssueAt K0 0 0 [9, 10] 3 fb3 (.ok fb4) from
    .ok (ar := arFb') (by decide) (.ok (by decide) (by decide) (by decide)))
  have r5 : Reachable K0 [] fb5 := .derive r4 (show DeriveStep 6 9 .modify fb4 (.ok fb5) from
    .ok (by decide))
  have s6 : StoreStep 7 7 fb5 (.ok fb6) := .ok (by decide)
  have r7 : Reachable K0 [] fb7 := .derive (.store r5 s6) (show DeriveStep 5 6 .modify fb6 (.ok fb7) from
    .ok (by decide))
  have s8 : StoreStep 8 10 fb7 (.ok fb8) := .ok (by decide)
  have l1 : ReleaseStep 7 fb8 (.ok (releaseEff fb8 7)) := .ok (by decide)
  have l2 : ReleaseStep 8 (releaseEff fb8 7) (.ok fb9) := .ok (by decide)
  have e1 : EndUseStep K0 2 fb9 (.ok (endUseEff fb9 2)) := .ok (by decide)
  have e2 : EndUseStep K0 3 (endUseEff fb9 2) (.ok fb10) := .ok (by decide)
  have z : ResetAtStep K0 0 0 fb10 (.ok (resetAtEff fb10 0)) := .ok (by decide)
  exact ⟨.reset (.endUse (.endUse (.release (.release (.store r7 s8) l1) l2) e1) e2) z,
    by decide, by decide, s6, s8, l1, l2, e1, e2, z⟩

end Ern.MM03
