import Ern.MemoryModel.Access.Invariants

/-!
# Access kernel: shared lemmas

Lemmas shared by the preservation proofs of the kernel operations of
`specs/ERN_Memory_Model_Specification_v0.md` §60–§75: origin and parent chains (§40, §42),
footprints and frames of places (§40), effective modes (§43) and their exclusivity under `I1`
(§50), additions of authorities (§42, §60, §61), states with the same authorities up to holders
(§63), consequences of `WF3` (§49), usability (§40), root places (§40, §49.6, §49.7), the shape of
`transfer` (§63), and `NoOrphan` from `WF3` (§54).
-/

namespace Ern.MemoryModel.Access

/-! ## Chains (§40, §42, §49) -/

/-- A chain from an element without link is empty (§40 parents, §42 origins). -/
theorem chainF_none {org : Nat → Option Nat} {i : Nat} (h : org i = none) :
    ∀ k, chainF org k i = []
  | 0 => rfl
  | _ + 1 => by simp [chainF, h]

/-- Any fuel at least the start index gives the same chain (§40, §42; acyclicity, §49). -/
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

/-- The chain of an element without link is empty (§40, §42). -/
theorem chain_none {org : Nat → Option Nat} {i : Nat} (h : org i = none) : chain org i = [] :=
  chainF_none h i

/-- The chain of `i` is its link followed by the chain of the link (§40, §42). -/
theorem chain_cons {org : Nat → Option Nat} {i o : Nat} (h : org i = some o) (hlt : o < i) :
    chain org i = o :: chain org o := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  simp only [chain, chainF, h, hlt, ↓reduceIte]
  rw [chainF_fuel org k o o (by omega) (Nat.le_refl o)]

/-- Elements of a chain are below its start (§49, acyclic chains). -/
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

/-- Every element of a chain is below its start (§49, acyclic chains). -/
theorem chain_lt {org : Nat → Option Nat} {i j : Nat} (h : j ∈ chain org i) : j < i :=
  chainF_lt i i j h

/-- A chain within fuel `k` has at most `k` elements (§49, finite chains). -/
theorem chainF_length {org : Nat → Option Nat} : ∀ k i, (chainF org k i).length ≤ k
  | 0, _ => by simp [chainF]
  | k + 1, i => by
    simp only [chainF]; split
    · split
      · simp only [List.length_cons]; have := chainF_length (org := org) k ‹_›; omega
      · simp
    · simp

/-- A chain from `i` has at most `i` elements (§49, finite chains). -/
theorem chain_length (org : Nat → Option Nat) (i : Nat) : (chain org i).length ≤ i :=
  chainF_length i i

/-- A chain depends only on the links at or below its start (§40, §42). -/
theorem chainF_congr {org org' : Nat → Option Nat} :
    ∀ k i, (∀ j ≤ i, org j = org' j) → chainF org k i = chainF org' k i
  | 0, _, _ => rfl
  | k + 1, i, h => by
    simp only [chainF]; rw [h i (Nat.le_refl i)]; split
    · split
      · rw [chainF_congr k _ fun j hj => h j (by omega)]
      · rfl
    · rfl

/-- A chain depends only on the links at or below its start (§40, §42). -/
theorem chain_congr {org org' : Nat → Option Nat} {i : Nat} (h : ∀ j ≤ i, org j = org' j) :
    chain org i = chain org' i := chainF_congr i i h

/-- Two elements without link of one chain are equal (§40 root places, §49.5 root
authorities). -/
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

/-- A chain contains the chain of each of its elements, for links to smaller indices (§40, §42,
§49). -/
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

/-! ## Footprints and frames of places (§40) -/

/-- Membership in `footprint(q)` (§40): an existing leaf that is a part of `q`. -/
theorem mem_footprint {P : List Place} {q l : Nat} :
    l ∈ footprint P q ↔ l < P.length ∧ isLeaf P l ∧ partOf P l q := by
  simp [footprint, List.mem_filter, List.mem_range]

/-- Footprints depend only on the number of places and on structural parents (§40). -/
theorem footprint_congr {P P' : List Place} (hlen : P'.length = P.length)
    (hpar : parentOf P' = parentOf P) (q : Nat) : footprint P' q = footprint P q := by
  unfold footprint; rw [hlen]; congr 1; funext l
  exact decide_eq_decide.2 (by simp only [isLeaf, partOf, hpar, hlen])

/-- The frame of a place is unique (§40, `placeFrame`). -/
theorem FrameOf.det {s : S3} {q f f' : Nat} (h : FrameOf s q f) (h' : FrameOf s q f') :
    f = f' := by
  induction h generalizing f' with
  | frame hpl ho => cases h' with
    | frame hpl' ho' => rw [hpl] at hpl'; cases hpl'; rw [ho] at ho'; cases ho'; rfl
    | place hpl' ho' _ => rw [hpl] at hpl'; cases hpl'; rw [ho] at ho'; cases ho'
  | place hpl ho _ ih => cases h' with
    | frame hpl' ho' => rw [hpl] at hpl'; cases hpl'; rw [ho] at ho'; cases ho'
    | place hpl' ho' hf' => rw [hpl] at hpl'; cases hpl'; rw [ho] at ho'; cases ho'; exact ih hf'

/-- A usable place has a frame of the stack (§40, items 2–3). -/
theorem S3.Usable.frameOf {s : S3} {q : Nat} (h : s.Usable q) : ∃ f, FrameOf s q f ∧ f ∈ s.F := by
  induction h with
  | frame hpl _ ho hf => exact ⟨_, .frame hpl ho, hf⟩
  | place hpl _ ho _ ih => obtain ⟨f, hf, hm⟩ := ih; exact ⟨f, .place hpl ho hf, hm⟩

/-- The frame of a place depends only on the places (§40, `placeFrame`). -/
theorem FrameOf.congr {s s' : S3} (hP : s'.P = s.P) {q f : Nat} :
    FrameOf s' q f ↔ FrameOf s q f :=
  ⟨fun h => by induction h with
    | frame hpl ho => exact .frame (hP ▸ hpl) ho
    | place hpl ho _ ih => exact .place (hP ▸ hpl) ho ih,
   fun h => by induction h with
    | frame hpl ho => exact .frame (hP ▸ hpl) ho
    | place hpl ho _ ih => exact .place (hP ▸ hpl) ho ih⟩

/-- `placeFrame` depends only on the places (§40). -/
theorem S3.pframe_congr {s s' : S3} (hP : s'.P = s.P) (q : Nat) : s'.pframe q = s.pframe q :=
  Option.ext fun f => by rw [pframe_iff, pframe_iff, FrameOf.congr hP]

/-- The frame of a holder depends only on the places (§44). -/
theorem S3.hframe_congr {s s' : S3} (hP : s'.P = s.P) (h : Holder) :
    s'.hframe h = s.hframe h := by
  cases h with
  | frame f => rfl
  | place p => exact S3.pframe_congr hP p

/-- Places with the same owner have the same frame (§40, `placeFrame`). -/
theorem pframe_eq_of_owner {s : S3} {q r : Nat} {pq pr : Place} (hq : s.P[q]? = some pq)
    (hr : s.P[r]? = some pr) (h : pr.owner = pq.owner) : s.pframe r = s.pframe q := by
  simp only [S3.pframe, pframeF, hq, hr, h]

/-! ## Indexed maps (§72, §73) -/

/-- `mapI` preserves the length (effects of §72 and §73). -/
theorem length_mapI {α β : Type} (f : Nat → α → β) :
    ∀ (i : Nat) (l : List α), (mapI f i l).length = l.length
  | _, [] => rfl
  | i, _ :: l => by simp [mapI, length_mapI f (i + 1) l]

/-- Element `j` of `mapI f i l` is `f (i + j)` applied to element `j` of `l` (effects of §72 and
§73). -/
theorem getElem?_mapI {α β : Type} (f : Nat → α → β) :
    ∀ (i : Nat) (l : List α) (j : Nat), (mapI f i l)[j]? = (l[j]?).map (f (i + j))
  | _, [], _ => rfl
  | i, a :: l, 0 => by simp [mapI]
  | i, a :: l, j + 1 => by
    simp only [mapI, List.getElem?_cons_succ, getElem?_mapI f (i + 1) l j]
    congr 2; omega

/-! ## Guarded transitions (§58) -/

/-- A guarded transition has one outcome (§58). -/
theorem Guarded.det {σ : Type} {Pre : Prop} {eff : σ} {o₁ o₂ : Outcome3 σ}
    (h₁ : Guarded Pre eff o₁) (h₂ : Guarded Pre eff o₂) : o₁ = o₂ := by
  cases h₁ <;> cases h₂ <;> first | rfl | contradiction

/-- The `ok` outcome of a guarded transition: the preconditions hold and the state is the effect
(§58). -/
theorem Guarded.ok_iff {σ : Type} {Pre : Prop} {eff s' : σ} :
    Guarded Pre eff (.ok s') ↔ Pre ∧ s' = eff :=
  ⟨fun h => by cases h; exact ⟨‹_›, rfl⟩, fun ⟨h, e⟩ => e ▸ .ok h⟩

/-- The `reject` outcome of a guarded transition: the preconditions fail (§58). -/
theorem Guarded.reject_iff {σ : Type} {Pre : Prop} {eff : σ} :
    Guarded Pre eff .reject ↔ ¬ Pre :=
  ⟨fun h => by cases h; assumption, fun h => .reject h⟩

/-! ## Effective modes (§43) -/

/-- Cases 2 and 4 of §43: a present effective mode is the own mode when no active descendant
covers the leaf, `Observe` when only `Observe` descendants do. -/
theorem effOf_cases {m m' : Mode} {ds : List Mode} (h : effOf m ds = some m') :
    (ds = [] ∧ m' = m) ∨ (ds ≠ [] ∧ Mode.modify ∉ ds ∧ m' = .observe) := by
  unfold effOf at h
  by_cases h0 : ds = []
  · simp [h0] at h; exact .inl ⟨h0, h.symm⟩
  · by_cases h1 : Mode.modify ∈ ds
    · simp [h0, h1] at h
    · simp [h0, h1] at h; exact .inr ⟨h0, h1, h.symm⟩

/-- A mode other than `Modify` is `Observe` (§42). -/
theorem mode_eq_observe {m : Mode} (h : m ≠ .modify) : m = .observe := by cases m <;> simp_all

/-- Membership in `descModes` (§43): the mode of an active descendant covering the leaf. -/
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

/-- A present effective mode (§43, case 1): the authority is active and covers the leaf. -/
theorem effective_some {s : S3} {a p : Nat} {m : Mode} (h : effective s a p = some m) :
    ∃ x, s.A[a]? = some x ∧ x.active = true ∧ p ∈ x.footprint ∧
      effOf x.mode (descModes s a p) = some m := by
  unfold effective at h
  split at h
  · rename_i x hx; split at h
    · rename_i hc; exact ⟨x, hx, hc.1, hc.2, h⟩
    · cases h
  · cases h

/-- The effective mode of an active authority covering the leaf (§43, cases 2–4). -/
theorem effective_eq {s : S3} {a p : Nat} {x : Authority} (hx : s.A[a]? = some x)
    (ha : x.active = true) (hp : p ∈ x.footprint) :
    effective s a p = effOf x.mode (descModes s a p) := by
  simp [effective, hx, ha, hp]

/-- The mode order is reflexive (§43). -/
theorem Mode.le_refl (m : Mode) : m.le m := by cases m <;> simp [Mode.le]

/-- The effective mode does not exceed the own mode (§43). -/
theorem effective_le {s : S3} {a p : Nat} {m : Mode} {x : Authority} (hx : s.A[a]? = some x)
    (h : effective s a p = some m) : m.le x.mode := by
  obtain ⟨x', hx', -, -, he⟩ := effective_some h
  rw [hx] at hx'; cases hx'
  rcases effOf_cases he with ⟨-, rfl⟩ | ⟨-, -, rfl⟩
  · exact Mode.le_refl _
  · simp [Mode.le]

/-- The mode order is transitive (§43). -/
theorem Mode.le_trans {a b c : Mode} (h₁ : a.le b) (h₂ : b.le c) : a.le c := by
  cases a <;> cases b <;> cases c <;> simp_all [Mode.le]

/-- Only `Observe` is below `Observe` (§43). -/
theorem Mode.le_observe {m : Mode} (h : m.le .observe) : m = .observe := by
  cases m <;> simp_all [Mode.le]

/-- A mode permitted by a present effective mode (§43): below the own mode when no active
descendant covers the leaf, `Observe` when no `Modify` descendant does. -/
theorem allows_effOf {m m' : Mode} {ds : List Mode} (h : Allows (effOf m ds) m') :
    (ds = [] ∧ m'.le m) ∨ (Mode.modify ∉ ds ∧ m' = .observe) := by
  unfold Allows OptP at h
  split at h
  · rename_i e he
    rcases effOf_cases he with ⟨h0, rfl⟩ | ⟨-, hn, rfl⟩
    · exact .inl ⟨h0, h⟩
    · exact .inr ⟨hn, Mode.le_observe h⟩
  · exact h.elim

/-! ## Consequences of `I1` (§50) -/

/-- Under `I1`, two distinct authorities with present effective modes on a leaf have compatible
effective modes, `Observe`/`Observe` (§50, second paragraph). -/
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

/-- `effective_exclusive` (§50): under `I1`, an authority with effective `Modify` on a leaf is the
only one with a present effective mode there. -/
theorem effective_exclusive {s : S3} (h : I1 s) {a b p : Nat} (hab : a ≠ b)
    (ha : effective s a p = some .modify) : effective s b p = none := by
  cases hb : effective s b p with
  | none => rfl
  | some m => exact absurd (effective_compat h a b p _ _ hab ha hb).1 (by simp)

/-- Compatibility of effective modes is symmetric (§50). -/
theorem Compat.symm {m₁ m₂ : Mode} (h : Compat m₁ m₂) : Compat m₂ m₁ := ⟨h.2, h.1⟩

/-- `I4` holds in every state (§53, first sentence): a read requires `Init` on every leaf read
(§66.1). -/
theorem i4_always (s : S3) : I4 s := fun _ _ l hl hm h => by rw [h.init l hl] at hm; cases hm

/-! ## Additions of authorities (§42, §60, §61) -/

/-- A list whose members are none is empty (§43, §63.2). -/
theorem nil_of_forall_not_mem {α : Type} : ∀ {l : List α}, (∀ a, a ∉ l) → l = []
  | [], _ => rfl
  | a :: _, h => absurd (List.mem_cons_self ..) (h a)

/-- `filterMap` depends only on the values of the function on the list (§43, `descModes`). -/
theorem filterMap_congr' {α β : Type} {f g : α → Option β} :
    ∀ {l : List α}, (∀ a ∈ l, f a = g a) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.filterMap_cons, h a (List.mem_cons_self ..),
      filterMap_congr' fun b hb => h b (List.mem_cons_of_mem a hb)]

/-- The authorities after an addition: the former ones, and the new one at the fresh identity
(§42, fresh identities). -/
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

/-- An addition keeps the former authorities (§42). -/
theorem addAuth_lt {s : S3} {y₀ : Authority} {j : Nat} (h : j < s.A.length) :
    (s.addAuth y₀).A[j]? = s.A[j]? := List.getElem?_append_left h

/-- The added authority has the fresh identity `|A|` (§42). -/
theorem addAuth_self (s : S3) (y₀ : Authority) : (s.addAuth y₀).A[s.A.length]? = some y₀ := by
  simp [S3.addAuth]

/-- An addition keeps the origin chains of the former authorities (§42). -/
theorem ancs_addAuth_lt {s : S3} {y₀ : Authority} {j : Nat} (h : j < s.A.length) :
    (s.addAuth y₀).ancs j = s.ancs j :=
  chain_congr fun i hi => by simp only [S3.org, addAuth_lt (Nat.lt_of_le_of_lt hi h)]

/-- The origin chain of an authority added with origin `src` is `src` followed by the chain of
`src` (§42, §60). -/
theorem ancs_addAuth_self {s : S3} {y₀ : Authority} {src : Nat} (ho : y₀.origin = some src)
    (hs : src < s.A.length) : (s.addAuth y₀).ancs s.A.length = src :: s.ancs src := by
  unfold S3.ancs
  rw [chain_cons (by simp [S3.org, addAuth_self, ho]) hs]
  exact congrArg _ (ancs_addAuth_lt hs)

/-- An addition keeps active authorities active (§42). -/
theorem active_addAuth {s : S3} {y₀ : Authority} {x : Nat} (h : s.Active x) :
    (s.addAuth y₀).Active x := by
  obtain ⟨y, hy, ha⟩ := h; exact ⟨y, by rw [addAuth_lt (lt_of_getElem? hy)]; exact hy, ha⟩

/-- The covering descendants after an addition: the former ones, and the new authority when it
is an active descendant covering the leaf (§43). -/
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

/-- An addition leaves the effective mode of a former authority unchanged on a leaf the new
authority does not cover (§43). -/
theorem effective_addAuth_notin {s : S3} {y₀ : Authority} {a p : Nat} (ha : a < s.A.length)
    (hp : p ∉ y₀.footprint) : effective (s.addAuth y₀) a p = effective s a p := by
  unfold effective; rw [addAuth_lt ha, descModes_addAuth]; simp [hp]

/-- Under `I1`, an authority derived from `src` with a mode permitted on leaf `p`, and an active
authority covering `p` outside the origin chain of the new one, are both `Observe` (§50, §60.3). -/
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

/-- `split` adds its authorities one region at a time (§61, `ok` effect). -/
theorem splitEff_cons (s : S3) (src : Nat) (r : List Nat) (rs : List (List Nat)) :
    splitEff s src (r :: rs) =
      splitEff (s.addAuth ⟨.modify, some src, r, .frame s.top, true⟩) src rs := by
  simp [splitEff, S3.addAuth, S3.top]

/-! ## Same authorities up to holders (§42, §63) -/

/-- Skeleton of an authority (§42): every field but its holder. -/
def skel (z : Authority) : Mode × Option Nat × List Nat × Bool :=
  (z.mode, z.origin, z.footprint, z.active)

/-- `s'` has the authorities of `s` up to their holders (§42; §63: a transfer creates and
duplicates no authority). -/
def SameSkel (s s' : S3) : Prop :=
  s'.A.length = s.A.length ∧ ∀ j : Nat, (s'.A[j]?).map skel = (s.A[j]?).map skel

/-- An authority of `s'` has a counterpart in `s` with the same skeleton (§42). -/
theorem SameSkel.get {s s' : S3} (h : SameSkel s s') {j : Nat} {y' : Authority}
    (hj : s'.A[j]? = some y') : ∃ y, s.A[j]? = some y ∧ skel y' = skel y := by
  have := h.2 j; rw [hj] at this
  cases hy : s.A[j]? with
  | none => rw [hy] at this; cases this
  | some y => rw [hy] at this; exact ⟨y, rfl, Option.some.inj this⟩

/-- An authority of `s` has a counterpart in `s'` with the same skeleton (§42). -/
theorem SameSkel.get' {s s' : S3} (h : SameSkel s s') {j : Nat} {y : Authority}
    (hj : s.A[j]? = some y) : ∃ y', s'.A[j]? = some y' ∧ skel y' = skel y := by
  have := h.2 j; rw [hj] at this
  cases hy : s'.A[j]? with
  | none => rw [hy] at this; cases this
  | some y' => rw [hy] at this; exact ⟨y', rfl, Option.some.inj this⟩

/-- Same skeletons give the same origin links (§42). -/
theorem SameSkel.org {s s' : S3} (h : SameSkel s s') : s'.org = s.org := by
  funext j
  cases hy : s.A[j]? with
  | none =>
    cases hy' : s'.A[j]? with
    | none => simp [S3.org, hy, hy']
    | some y' => obtain ⟨y, h1, -⟩ := h.get hy'; rw [hy] at h1; cases h1
  | some y => obtain ⟨y', hy', e⟩ := h.get' hy; simp [skel] at e; simp [S3.org, hy, hy', e.2.1]

/-- Same skeletons give the same origin chains (§42). -/
theorem SameSkel.ancs {s s' : S3} (h : SameSkel s s') : s'.ancs = s.ancs := by
  funext j; simp [S3.ancs, h.org]

/-- Same skeletons give the same active authorities (§42). -/
theorem SameSkel.active {s s' : S3} (h : SameSkel s s') {x : Nat} :
    s'.Active x ↔ s.Active x := by
  constructor
  · rintro ⟨y', hy', ha⟩; obtain ⟨y, hy, he⟩ := h.get hy'
    exact ⟨y, hy, by simp [skel] at he; rw [← he.2.2.2]; exact ha⟩
  · rintro ⟨y, hy, ha⟩; obtain ⟨y', hy', he⟩ := h.get' hy
    exact ⟨y', hy', by simp [skel] at he; rw [he.2.2.2]; exact ha⟩

/-- Same skeletons give the same covering descendants (§43). -/
theorem SameSkel.descModes {s s' : S3} (h : SameSkel s s') (a p : Nat) :
    descModes s' a p = descModes s a p := by
  unfold Access.descModes; rw [h.1, h.ancs]
  refine filterMap_congr' fun j _ => ?_
  cases hy : s.A[j]? with
  | none => have := h.2 j; rw [hy] at this; cases hy' : s'.A[j]? <;> simp_all
  | some y =>
    obtain ⟨y', hy', he⟩ := h.get' hy
    simp [skel] at he; simp [hy', he]

/-- Same skeletons give the same effective modes (§43). -/
theorem SameSkel.effective {s s' : S3} (h : SameSkel s s') (a p : Nat) :
    effective s' a p = effective s a p := by
  unfold Access.effective; rw [h.descModes]
  cases hy : s.A[a]? with
  | none => have := h.2 a; rw [hy] at this; cases hy' : s'.A[a]? <;> simp_all
  | some y =>
    obtain ⟨y', hy', he⟩ := h.get' hy
    simp [skel] at he; simp [hy', he]

/-- `I1` depends only on the skeletons (§50). -/
theorem SameSkel.i1 {s s' : S3} (h : SameSkel s s') (h1 : I1 s) : I1 s' := by
  intro a b x' y' p hab ha hb xa ya xp yp hnab hnba
  obtain ⟨x, hx, ex⟩ := h.get ha; obtain ⟨y, hy, ey⟩ := h.get hb
  simp [skel] at ex ey; rw [h.ancs] at hnab hnba
  rw [ex.1, ey.1]
  exact h1 a b x y p hab hx hy (ex.2.2.2 ▸ xa) (ey.2.2.2 ▸ ya) (ex.2.2.1 ▸ xp) (ey.2.2.1 ▸ yp)
    hnab hnba

/-- `I2` depends only on the skeletons (§51). -/
theorem SameSkel.i2 {s s' : S3} (h : SameSkel s s') (h2 : I2 s) : I2 s' := by
  intro b y a hb ho
  obtain ⟨y₀, hy₀, e⟩ := h.get hb; simp [skel] at e
  obtain ⟨x₀, hx₀, hm, hh⟩ := h2 b y₀ a hy₀ (e.2.1 ▸ ho)
  obtain ⟨x', hx', e'⟩ := h.get' hx₀; simp [skel] at e'
  exact ⟨x', hx', by rw [e.1, e'.1]; exact hm,
    fun p hp => by rw [e'.2.2.1]; exact hh p (e.2.2.1 ▸ hp)⟩

/-- The origin clause of `WF3` depends only on the skeletons (§49.5). -/
theorem SameSkel.origins {s s' : S3} (h : SameSkel s s')
    (hw : ∀ (b : Nat) (y : Authority) (a : Nat), s.A[b]? = some y → y.origin = some a → a < b) :
    ∀ (b : Nat) (y : Authority) (a : Nat), s'.A[b]? = some y → y.origin = some a → a < b := by
  intro b y a hb ho
  obtain ⟨y₀, hy₀, e⟩ := h.get hb; simp [skel] at e
  exact hw b y₀ a hy₀ (e.2.1 ▸ ho)

/-- A property of every footprint member depends only on the skeletons (§49.4). -/
theorem SameSkel.footprints {s s' : S3} (h : SameSkel s s') {Q : Nat → Prop}
    (hw : ∀ (a : Nat) (x : Authority), s.A[a]? = some x → ∀ l ∈ x.footprint, Q l) :
    ∀ (a : Nat) (x : Authority), s'.A[a]? = some x → ∀ l ∈ x.footprint, Q l := by
  intro a x hx l hl
  obtain ⟨x₀, hx₀, e⟩ := h.get hx; simp [skel] at e
  exact hw a x₀ hx₀ l (e.2.2.1 ▸ hl)

/-! ## `release` (§62) -/

/-- Element `j` after setting element `a` (§62, §65 effects). -/
theorem set_get {l : List Authority} {a j : Nat} {x' : Authority} (ha : a < l.length) :
    (l.set a x')[j]? = if a = j then some x' else l[j]? := by
  rw [List.getElem?_set]; split <;> simp_all

/-- The effect of `release` on an existing authority (§62, `ok` effect). -/
theorem releaseEff_eq {s : S3} {a : Nat} {x : Authority} (hx : s.A[a]? = some x) :
    releaseEff s a = { s with
      A := s.A.set a { x with active := false }
      D := fun q => if x.holder = .place q then (s.D q).filter (· != a) else s.D q } := by
  simp [releaseEff, hx]

/-- The anchors after a release: those before, without `a` at the place holding it (§62, `ok`
effect). -/
theorem release_D_mem {s : S3} {a q y : Nat} {x : Authority} (hx : s.A[a]? = some x)
    (hy : y ∈ (releaseEff s a).D q) : y ∈ s.D q ∧ (y = a → x.holder ≠ .place q) := by
  rw [releaseEff_eq hx] at hy; simp only at hy
  split at hy
  · rename_i hh
    obtain ⟨hy, hne⟩ := List.mem_filter.1 hy
    exact ⟨hy, fun e => by subst e; simp at hne⟩
  · exact ⟨hy, fun _ => ‹_›⟩

/-- A release keeps the origin links (§62). -/
theorem release_org {s : S3} {a : Nat} {x : Authority} (hx : s.A[a]? = some x) :
    (releaseEff s a).org = s.org := by
  funext j; rw [releaseEff_eq hx]
  simp only [S3.org, set_get (lt_of_getElem? hx)]
  split
  · subst_vars; simp [hx]
  · rfl

/-- A release keeps the origin chains (§62). -/
theorem release_ancs {s : S3} {a : Nat} {x : Authority} (hx : s.A[a]? = some x) :
    (releaseEff s a).ancs = s.ancs := by
  funext j; simp only [S3.ancs, release_org hx]

/-! ## Consequences of `WF3` (§49) -/

/-- A part has the owner of every place it belongs to (§40, §49.2). -/
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
      obtain ⟨pr, hpr, hlt, ho, -⟩ := hw.places l pl p hpl hpar
      rw [chain_cons hpo hlt] at hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact ⟨pl, pr, hpl, hpr, ho.symm⟩
      · obtain ⟨pl', pr', hpl', hpr', he⟩ :=
          WF3.ownerOf_aux hw n p r (by omega) ⟨lt_of_getElem? hpr, .inr hc⟩
        rw [hpr] at hpl'; cases hpl'
        exact ⟨pl, pr', hpl, hpr', ho.symm.trans he⟩

/-- A part has the owner of every place it belongs to (§40, §49.2). -/
theorem WF3.ownerOf {s : S3} (hw : WF3 s) {l r : Nat} (h : partOf s.P l r) :
    ∃ pl pr, s.P[l]? = some pl ∧ s.P[r]? = some pr ∧ pl.owner = pr.owner :=
  hw.ownerOf_aux (l + 1) l r (Nat.lt_succ_self l) h

/-- A part has the death marker of every place it belongs to (§40, §49.2). -/
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
      obtain ⟨pr, hpr, hlt, -, hd⟩ := hw.places l pl p hpl hpar
      rw [chain_cons hpo hlt] at hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact hd.symm
      · exact hd.symm.trans (WF3.deadOf_aux hw n p r (by omega) ⟨lt_of_getElem? hpr, .inr hc⟩)

/-- A part has the death marker of every place it belongs to (§40, §49.2). -/
theorem WF3.deadOf {s : S3} (hw : WF3 s) {l r : Nat} (h : partOf s.P l r) :
    s.dead l = s.dead r :=
  hw.deadOf_aux (l + 1) l r (Nat.lt_succ_self l) h

/-- A structural parent exists and precedes its child (§49.2). -/
theorem WF3.parent_lt {s : S3} (hw : WF3 s) {i o : Nat} (h : parentOf s.P i = some o) :
    o < i ∧ o < s.P.length := by
  simp only [parentOf] at h
  cases hp : s.P[i]? with
  | none => rw [hp] at h; cases h
  | some pl =>
    rw [hp] at h
    obtain ⟨pr, hpr, hlt, -⟩ := hw.places i pl o hp h
    exact ⟨hlt, lt_of_getElem? hpr⟩

/-- The current frame of a nonempty stack belongs to it (§39, §49.1). -/
theorem top_mem {s : S3} (h : s.F ≠ []) : s.top ∈ s.F := by
  unfold S3.top; cases hF : s.F with
  | nil => exact absurd hF h
  | cons f F => simp

/-! ## Usability (§40) -/

/-- Usability depends only on places, stack and death markers: a smaller stack and more dead
places give fewer usable places (§40). -/
theorem S3.Usable.mono {s s' : S3} (hP : s'.P = s.P) (hF : ∀ f ∈ s'.F, f ∈ s.F)
    (hd : ∀ q, s'.dead q = false → s.dead q = false) {q : Nat} (h : s'.Usable q) :
    s.Usable q := by
  induction h with
  | frame hpl hdq ho hf => exact .frame (by rw [← hP]; exact hpl) (hd _ hdq) ho (hF _ hf)
  | place hpl hdq ho _ ih => exact .place (by rw [← hP]; exact hpl) (hd _ hdq) ho ih

/-- Usability depends only on places, stack and death markers (§40). -/
theorem S3.Usable.congr {s s' : S3} (hP : s'.P = s.P) (hF : s'.F = s.F) (hd : s'.dead = s.dead)
    {q : Nat} : s'.Usable q ↔ s.Usable q :=
  ⟨S3.Usable.mono hP (fun f h => hF ▸ h) (fun q h => hd ▸ h),
   S3.Usable.mono hP.symm (fun f h => hF ▸ h) (fun q h => by rw [hd]; exact h)⟩

/-- Usability carries over between states with the same places, stack and death markers
(§40). -/
theorem S3.Usable.of_eqs {s s' : S3} {q : Nat} (h : s'.Usable q) (hP : s'.P = s.P)
    (hF : s'.F = s.F) (hd : s'.dead = s.dead) : s.Usable q :=
  S3.Usable.mono hP (fun _ h => hF ▸ h) (fun _ h => hd ▸ h) h

/-- Liveness of a holder depends only on places, stack and death markers (§49.8). -/
theorem HolderLive.congr {s s' : S3} (hP : s'.P = s.P) (hF : s'.F = s.F) (hd : s'.dead = s.dead)
    (h : Holder) : HolderLive s' h ↔ HolderLive s h := by
  cases h with
  | frame f => simp [HolderLive, hF]
  | place p => exact S3.Usable.congr hP hF hd

/-- A place with the owner and the death marker of a usable place is usable (§40). -/
theorem S3.Usable.of_same {s : S3} {q r : Nat} {pl pr : Place} (h : s.Usable q)
    (hq : s.P[q]? = some pl) (hr : s.P[r]? = some pr) (ho : pr.owner = pl.owner)
    (hd : s.dead r = s.dead q) : s.Usable r := by
  cases h with
  | frame hpl hdq hof hf =>
    rw [hq] at hpl; cases hpl; exact .frame hr (by rw [hd]; exact hdq) (by rw [ho]; exact hof) hf
  | place hpl hdq hof hu =>
    rw [hq] at hpl; cases hpl; exact .place hr (by rw [hd]; exact hdq) (by rw [ho]; exact hof) hu

/-- A part of a usable place is usable (§40: parts share owner and death marker; §49.2). -/
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
      obtain ⟨pr, hpr, hlt, ho, hd⟩ := hw.places r pl p hpl hpar
      rw [chain_cons hpo hlt] at hc
      have hup : s.Usable p := by
        rcases List.mem_cons.1 hc with rfl | hc
        · exact hu
        · exact usable_of_partOf hw n p q (by omega) ⟨lt_of_getElem? hpr, .inr hc⟩ hu
      exact hup.of_same hpr hpl ho.symm hd.symm

/-- The place containing a usable part is usable (§40: parts share owner and death marker;
§49.2). -/
theorem usable_of_part {s : S3} (hw : WF3 s) {l r : Nat} (h : partOf s.P l r)
    (hu : s.Usable l) : s.Usable r := by
  obtain ⟨pl, pr, hpl, hpr, ho⟩ := hw.ownerOf h
  exact hu.of_same hpl hpr ho.symm (hw.deadOf h).symm

/-! ## Root places (§40, §49.6, §49.7) -/

/-- A place belongs to at most one root place (§40). -/
theorem rootOf_unique {P : List Place} {l r r' : Nat} (hr : RootPlace P r)
    (hr' : RootPlace P r') (h : partOf P l r) (h' : partOf P l r') : r = r' := by
  obtain ⟨-, hr⟩ := hr; obtain ⟨-, hr'⟩ := hr'
  obtain ⟨-, h | h⟩ := h <;> obtain ⟨-, h' | h'⟩ := h'
  · exact h.symm.trans h'
  · subst h; rw [chain_none hr] at h'; simp at h'
  · subst h'; rw [chain_none hr'] at h; simp at h
  · exact chainF_root _ _ _ _ h hr h' hr'

/-- Every place of a well-formed state is a part of a root place (§40, §49.2). -/
theorem exists_rootPlace {s : S3} (hw : WF3 s) : ∀ n q, q < n → q < s.P.length →
    ∃ r, RootPlace s.P r ∧ partOf s.P q r
  | 0, _, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, q, hqn, hq => by
    cases hp : parentOf s.P q with
    | none => exact ⟨q, ⟨hq, hp⟩, hq, .inl rfl⟩
    | some o =>
      obtain ⟨hlt, hol⟩ := hw.parent_lt hp
      obtain ⟨r, hr, -, hor⟩ := exists_rootPlace hw n o (by omega) hol
      refine ⟨r, hr, hq, .inr ?_⟩
      rw [chain_cons hp hlt]
      rcases hor with rfl | hor
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ hor

/-- The footprint of a part is within the footprint of the whole (§40, §49.2). -/
theorem footprint_sub {s : S3} (hw : WF3 s) {q r : Nat} (h : partOf s.P q r) {l : Nat}
    (hl : l ∈ footprint s.P q) : l ∈ footprint s.P r := by
  obtain ⟨hlP, hleaf, -, hlq⟩ := mem_footprint.1 hl
  refine mem_footprint.2 ⟨hlP, hleaf, hlP, ?_⟩
  obtain ⟨-, hqr⟩ := h
  rcases hlq with rfl | hlq
  · exact hqr
  · rcases hqr with rfl | hqr
    · exact .inr hlq
    · exact .inr (chain_trans (fun i o h => (hw.parent_lt h).1) (l + 1) l (Nat.lt_succ_self l) q
        hlq r hqr)

/-- A decidable property failing somewhere below `n` has a witness below `n` (§40, search for a
leaf). -/
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

/-- Every place of a well-formed state has a leaf in its footprint (§40, §49.2: parts follow
their parent, so the search for a part without part terminates). -/
theorem exists_mem_footprint {s : S3} (hw : WF3 s) :
    ∀ n q, s.P.length - q < n → q < s.P.length → ∃ l, l ∈ footprint s.P q
  | 0, _, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, q, hn, hq => by
    by_cases hleaf : isLeaf s.P q
    · exact ⟨q, mem_footprint.2 ⟨hq, hleaf, hq, .inl rfl⟩⟩
    · obtain ⟨r, hr, hpr⟩ := exists_lt_not_of_not_forall _ hleaf
      have hpr : parentOf s.P r = some q := Decidable.of_not_not hpr
      have hlt : ∀ i o, parentOf s.P i = some o → o < i := fun i o h => (hw.parent_lt h).1
      have hqr := hlt r q hpr
      obtain ⟨l, hl⟩ := exists_mem_footprint hw n r (by omega) hr
      obtain ⟨hlP, hleaf', -, hlr⟩ := mem_footprint.1 hl
      refine ⟨l, mem_footprint.2 ⟨hlP, hleaf', hlP, .inr ?_⟩⟩
      have hrq : q ∈ chain (parentOf s.P) r := by
        rw [chain_cons hpr hqr]; exact List.mem_cons_self ..
      rcases hlr with rfl | hlr
      · exact hrq
      · exact chain_trans hlt (l + 1) l (Nat.lt_succ_self l) r hlr q hrq

/-- `RootHeld` (§49.7) carries over to a state with the same places and no more usable places,
which keeps every active root authority of `s` unchanged. -/
theorem RootHeld.transport {s s' : S3} (h : RootHeld s) (hP : s'.P = s.P)
    (hU : ∀ r, s'.Usable r → s.Usable r)
    (hA : ∀ (i : Nat) (z : Authority), s.A[i]? = some z → z.active = true → z.origin = none →
      s'.A[i]? = some z) : RootHeld s' := by
  intro r hr hu
  rw [hP] at hr
  obtain ⟨i, z, pr, hz, za, zo, zm, hpr, hh, hf⟩ := h r hr (hU r hu)
  exact ⟨i, z, pr, hA i z hz za zo, za, zo, zm, by rw [hP]; exact hpr, hh, by rw [hP]; exact hf⟩

/-- `RootHeldConv` (§40, §49.7) carries over to a state with the same places whose root
authorities are root authorities of `s` with the same footprint and holder. -/
theorem RootHeldConv.transport {s s' : S3} (h : RootHeldConv s) (hP : s'.P = s.P)
    (hA : ∀ (x : Nat) (z' : Authority), s'.A[x]? = some z' → z'.origin = none →
      ∃ z, s.A[x]? = some z ∧ z.origin = none ∧ z'.footprint = z.footprint ∧
        z'.holder = z.holder) : RootHeldConv s' := by
  intro x z' l r hx ho hl hr hlr
  obtain ⟨z, hz, hzo, hf, hh⟩ := hA x z' hx ho
  rw [hP] at hr hlr
  obtain ⟨pr, hpr, hpr'⟩ := h x z l r hz hzo (hf ▸ hl) hr hlr
  exact ⟨pr, by rw [hP]; exact hpr, hh.trans hpr'⟩

/-- An active authority with no origin is held by the owner of the root place of every leaf it
covers (the converse of `RootHeld` restricted to active authorities), from `WF3` (§49.4, §49.7),
`I1` (§50) and `NoDangling` (§54): the root place is usable, so its root `Modify` authority
(§49.7) covers the leaf, and two distinct active authorities with no origin covering a common leaf
are unrelated by derivation, so by `I1` that root authority would be `Observe`. -/
theorem rootHeldConv_active {s : S3} (hw : WF3 s) (h1 : I1 s) (hnd : NoDangling s) :
    ∀ (x : Nat) (z : Authority) (l r : Nat), s.A[x]? = some z → z.active = true →
      z.origin = none → l ∈ z.footprint → RootPlace s.P r → partOf s.P l r →
      ∃ pr, s.P[r]? = some pr ∧ z.holder = pr.owner := by
  intro x z l r hz za zo hl hr hlr
  obtain ⟨hlP, hleaf⟩ := hw.footprints x z hz l hl
  have hlfr : l ∈ footprint s.P r := mem_footprint.2 ⟨hlP, hleaf, hlr⟩
  have hur : s.Usable r := Decidable.byContradiction fun hu => hnd x z hz za r hu l hlfr hl
  obtain ⟨i, z', pr, hz', za', zo', zm', hpr, hh', hfp'⟩ := hw.rootHeld r hr hur
  by_cases hix : i = x
  · subst hix; rw [hz] at hz'; cases hz'; exact ⟨pr, hpr, hh'⟩
  · have hancs : ∀ j w, s.A[j]? = some w → w.origin = none → s.ancs j = [] :=
      fun j w hj hw0 => by
        have : s.org j = none := by simp [S3.org, hj, hw0]
        simp [S3.ancs, chain_none this]
    have := (h1 i x z' z l hix hz' hz za' za ((hfp' l).2 hlfr) hl
      (by rw [hancs x z hz zo]; simp) (by rw [hancs i z' hz' zo']; simp)).1
    rw [zm'] at this; cases this

/-- `RootChain` (§49.6) carries over to a state with the same tree of places, the same origin
chains, the same footprints, and the same root authorities. -/
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

/-- `RootChain` (§49.6) depends only on the skeletons and the tree of places. -/
theorem SameSkel.rootChain {s s' : S3} (h : SameSkel s s') (hc : RootChain s)
    (hlen : s'.P.length = s.P.length) (hpar : parentOf s'.P = parentOf s.P) : RootChain s' :=
  hc.transport hlen hpar (fun a => by rw [h.ancs])
    (fun a y' ha => by obtain ⟨y, hy, e⟩ := h.get ha; simp [skel] at e; exact ⟨y, hy, e.2.2.1⟩)
    (fun x z hz hzo => by
      obtain ⟨z', hz', e⟩ := h.get' hz; simp [skel] at e
      exact ⟨z', hz', e.2.1.trans hzo, e.2.2.1⟩)

/-! ## Additions of authorities and `WF3` (§49, §50, §51, §60, §61) -/

/-- An addition keeps the places (§42). -/
theorem addAuth_P (s : S3) (y : Authority) : (s.addAuth y).P = s.P := rfl
/-- An addition keeps the stack (§42). -/
theorem addAuth_F (s : S3) (y : Authority) : (s.addAuth y).F = s.F := rfl
/-- An addition keeps the death markers (§42). -/
theorem addAuth_dead (s : S3) (y : Authority) : (s.addAuth y).dead = s.dead := rfl

/-- Adding an authority derived from `src`, within its footprint, preserves `RootChain`
(§49.6). -/
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

/-- Adding an active authority derived from `src` whose mode is permitted by the effective mode
of `src` on each leaf of its footprint preserves `I1` (§50, §60.2, §60.3). -/
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

/-- Adding an active authority derived from `src`, with a mode not above the mode of `src`, a
footprint within the footprint of `src`, a mode permitted by the effective mode of `src` on each
leaf, and a live holder, preserves `WF3` (§49) and `I1`–`I4` (§50–§53). Shared by `derive` (§60)
and `split` (§61). -/
theorem addAuth_preserves {s : S3} (hwf : WF3 s) (hinv : Inv3base s) {src : Nat} {x : Authority}
    {m : Mode} {fp : List Nat} {hd : Holder} (hx : s.A[src]? = some x) (hm : m.le x.mode)
    (hfp : ∀ p ∈ fp, p ∈ x.footprint) (hal : ∀ p ∈ fp, Allows (effective s src p) m)
    (hl : HolderLive s hd) :
    WF3 (s.addAuth ⟨m, some src, fp, hd, true⟩) ∧
      Inv3base (s.addAuth ⟨m, some src, fp, hd, true⟩) := by
  obtain ⟨i1, i2, i3, -⟩ := hinv
  have hs := lt_of_getElem? hx
  have live := HolderLive.congr (addAuth_P s ⟨m, some src, fp, hd, true⟩) rfl rfl
  have usable := fun q => S3.Usable.congr (q := q) (addAuth_P s ⟨m, some src, fp, hd, true⟩) rfl rfl
  refine ⟨⟨hwf.frames, hwf.places, ⟨hwf.owners.1, hwf.owners.2.1, fun q hq => ?_⟩, ?_, ?_,
    rootChain_addAuth hwf.rootChain hx rfl hfp,
    hwf.rootHeld.transport rfl (fun r => (usable r).1)
      (fun i z hz _ _ => by rw [addAuth_lt (lt_of_getElem? hz)]; exact hz), ?_⟩,
    addAuth_I1 i1 hx hal, ?_, fun q hq y hy => active_addAuth (i3 q ((usable q).1 hq) y hy),
    i4_always _⟩
  · obtain ⟨f, hf, hfF⟩ := hwf.owners.2.2 q ((usable q).1 hq)
    exact ⟨f, (FrameOf.congr (addAuth_P s _)).2 hf, hfF⟩
  · intro a y hy l hl'
    rcases addAuth_get hy with ⟨-, hy'⟩ | ⟨-, rfl⟩
    · exact hwf.footprints a y hy' l hl'
    · exact hwf.footprints src x hx l (hfp l hl')
  · intro b y a hb ho
    rcases addAuth_get hb with ⟨-, hb''⟩ | ⟨rfl, rfl⟩
    · exact hwf.origins b y a hb'' ho
    · cases ho; exact hs
  · intro a y hy ya
    rcases addAuth_get hy with ⟨-, hy'⟩ | ⟨-, rfl⟩
    · exact (live _).2 (hwf.holders a y hy' ya)
    · exact (live _).2 hl
  · intro b y a hb ho
    rcases addAuth_get hb with ⟨-, hb''⟩ | ⟨rfl, rfl⟩
    · obtain ⟨x₁, hx₁, h⟩ := i2 b y a hb'' ho
      exact ⟨x₁, by rw [addAuth_lt (lt_of_getElem? hx₁)]; exact hx₁, h⟩
    · cases ho
      exact ⟨x, by rw [addAuth_lt hs]; exact hx, hm, hfp⟩

/-! ## Shape of `transfer` (§63) -/

/-- Places after a transfer: owners within `src` move to the corresponding part of `dst` (§63,
`ok` effect). -/
theorem transfer_P_get (s : S3) (src dst q : Nat) :
    (transferEff s src dst).P[q]? = (s.P[q]?).map fun pl =>
      if heldIn s.P src pl.owner then { pl with owner := mvTo s.P src dst pl.owner } else pl := by
  simp [transferEff]

/-- Authorities after a transfer: holders within `src` move to the corresponding part of `dst`
(§63, `ok` effect). -/
theorem transfer_A_get (s : S3) (src dst j : Nat) :
    (transferEff s src dst).A[j]? = (s.A[j]?).map fun y =>
      if heldIn s.P src y.holder then { y with holder := mvTo s.P src dst y.holder } else y := by
  simp [transferEff]

/-- A transfer keeps the number of places (§63). -/
theorem transfer_len (s : S3) (src dst : Nat) :
    (transferEff s src dst).P.length = s.P.length := by simp [transferEff]

/-- A transfer keeps the structural parents (§63). -/
theorem transfer_parentOf (s : S3) (src dst : Nat) :
    parentOf (transferEff s src dst).P = parentOf s.P := by
  funext i; simp only [parentOf, transfer_P_get]
  cases s.P[i]? with
  | none => rfl
  | some pl => simp only [Option.map_some, Option.bind_some]; split <;> rfl

/-- A transfer keeps the footprints (§63). -/
theorem transfer_footprint (s : S3) (src dst q : Nat) :
    footprint (transferEff s src dst).P q = footprint s.P q :=
  footprint_congr (transfer_len s src dst) (transfer_parentOf s src dst) q

/-- A transfer keeps the structural parts (§63). -/
theorem transfer_partOf (s : S3) (src dst r q : Nat) :
    partOf (transferEff s src dst).P r q ↔ partOf s.P r q := by
  simp only [partOf, transfer_parentOf, transfer_len]

/-- Membership in the children of a place (§63.2). -/
theorem mem_kids {P : List Place} {x r : Nat} :
    r ∈ kids P x ↔ r < P.length ∧ parentOf P r = some x := by
  simp [kids, List.mem_filter, List.mem_range]

/-- A place has no children exactly when it is a leaf (§40, §63.2). -/
theorem kids_nil_iff {P : List Place} {l : Nat} : kids P l = [] ↔ isLeaf P l := by
  constructor
  · intro h r hr hp
    have : r ∈ kids P l := mem_kids.2 ⟨hr, hp⟩
    rw [h] at this; simp at this
  · intro h
    exact nil_of_forall_not_mem fun r hr => by
      obtain ⟨hr, hp⟩ := mem_kids.1 hr; exact h r hr hp

/-- Any fuel at least the index gives the same `corr` (§63.2). -/
theorem corrF_fuel (P : List Place) (src dst : Nat) :
    ∀ n m r, r ≤ n → r ≤ m → corrF P src dst n r = corrF P src dst m r
  | 0, 0, _, _, _ => rfl
  | 0, m + 1, r, h, _ => by
    obtain rfl : r = 0 := by omega
    simp only [corrF]; split
    · rfl
    · split
      · split
        · omega
        · rfl
      · rfl
  | n + 1, 0, r, _, h => by
    obtain rfl : r = 0 := by omega
    simp only [corrF]; split
    · rfl
    · split
      · split
        · omega
        · rfl
      · rfl
  | n + 1, m + 1, r, h₁, h₂ => by
    simp only [corrF]; split
    · rfl
    · split
      · split
        · rw [corrF_fuel P src dst n m _ (by omega) (by omega)]
        · rfl
      · rfl

/-- `corr(src) = dst` (§63.2). -/
theorem corr_src (P : List Place) (src dst : Nat) : corr P src dst src = some dst := by
  unfold corr; cases src <;> simp [corrF]

/-- `corr(r)` for a part other than `src`: the child at the position of `r` among the children
of its parent, under the place corresponding to that parent (§63.2). -/
theorem corr_step {P : List Place} {src dst r p : Nat} (hr : r ≠ src)
    (hp : parentOf P r = some p) (hlt : p < r) :
    corr P src dst r = (corr P src dst p).bind fun p' => (kids P p')[posIn r (kids P p)]? := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  unfold corr
  simp only [corrF, hr, ↓reduceIte, hp, hlt]
  rw [corrF_fuel P src dst n p _ (by omega) (Nat.le_refl p)]

/-- An element found at an index belongs to the list (§63.2). -/
theorem getElem?_mem {l : List Nat} {i x : Nat} (h : l[i]? = some x) : x ∈ l :=
  List.mem_of_getElem? h

/-- The place corresponding to a part of `src` is a part of `dst` (§63.2). -/
theorem corr_partOf {s : S3} (hw : WF3 s) {src dst : Nat} (hd : dst < s.P.length) :
    ∀ n r r', r < n → corr s.P src dst r = some r' → partOf s.P r' dst
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, r, r', hr, h => by
    by_cases e : r = src
    · subst e; rw [corr_src] at h; cases h; exact ⟨hd, .inl rfl⟩
    cases hp : parentOf s.P r with
    | none =>
      unfold corr at h
      cases r with
      | zero => simp [corrF, e] at h
      | succ m => simp [corrF, e, hp] at h
    | some p =>
      have hlt := (hw.parent_lt hp).1
      rw [corr_step e hp hlt] at h
      cases hc : corr s.P src dst p with
      | none => rw [hc] at h; cases h
      | some p' =>
        rw [hc] at h; simp only [Option.bind_some] at h
        have ih := corr_partOf hw hd n p p' (by omega) hc
        obtain ⟨hr'l, hr'p⟩ := mem_kids.1 (getElem?_mem h)
        have hlt' := (hw.parent_lt hr'p).1
        refine ⟨hr'l, .inr ?_⟩
        rw [chain_cons hr'p hlt']
        rcases ih.2 with rfl | hc'
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ hc'

/-- A holder within `src` moves to a part of `dst` (§63, `ok` effect). -/
theorem mvTo_part {s : S3} (hw : WF3 s) {src dst : Nat} (hd : dst < s.P.length) {h : Holder}
    (hh : heldIn s.P src h) : ∃ r', mvTo s.P src dst h = .place r' ∧ partOf s.P r' dst := by
  cases h with
  | frame f => exact hh.elim
  | place r =>
    cases hc : corr s.P src dst r with
    | none => exact ⟨dst, by simp [mvTo, hc], hd, .inl rfl⟩
    | some r' =>
      exact ⟨r', by simp [mvTo, hc], corr_partOf hw hd (r + 1) r r' (Nat.lt_succ_self r) hc⟩

/-- A holder within `src` moves to a place (§63, `ok` effect). -/
theorem mvTo_place {P : List Place} {src dst : Nat} {h : Holder} (hh : heldIn P src h) :
    ∃ r', mvTo P src dst h = .place r' := by
  cases h with
  | frame _ => exact hh.elim
  | place r => exact ⟨_, rfl⟩

/-- After a transfer, a part of `dst` has the owner of `dst` (§40, §49.2, §63). -/
theorem transfer_owner_part {s : S3} (hw : WF3 s) {src dst r' : Nat} (hr' : partOf s.P r' dst) :
    ∃ pd pr, (transferEff s src dst).P[dst]? = some pd ∧
      (transferEff s src dst).P[r']? = some pr ∧ pr.owner = pd.owner := by
  obtain ⟨pl, pd, hpl, hpd, ho⟩ := hw.ownerOf hr'
  refine ⟨_, _, by rw [transfer_P_get, hpd]; rfl, by rw [transfer_P_get, hpl]; rfl, ?_⟩
  show (if heldIn s.P src pl.owner then _ else pl).owner =
    (if heldIn s.P src pd.owner then _ else pd).owner
  rw [ho]; split
  · rfl
  · exact ho

/-- After a transfer, a part of `dst` is usable when `dst` is (§40, §63). -/
theorem transfer_usable_part {s : S3} (hw : WF3 s) {src dst r' : Nat} (hr' : partOf s.P r' dst)
    (hd' : (transferEff s src dst).Usable dst) : (transferEff s src dst).Usable r' := by
  obtain ⟨pd, pr, hpd, hpr, ho⟩ := transfer_owner_part (src := src) hw hr'
  exact hd'.of_same hpd hpr ho (by show s.dead r' = s.dead dst; exact hw.deadOf hr')

/-- After a transfer, a part of `dst` has the frame of `dst` (§40, §63). -/
theorem transfer_pframe_part {s : S3} (hw : WF3 s) {src dst r' : Nat} (hr' : partOf s.P r' dst) :
    (transferEff s src dst).pframe r' = (transferEff s src dst).pframe dst := by
  obtain ⟨pd, pr, hpd, hpr, ho⟩ := transfer_owner_part (src := src) hw hr'
  exact pframe_eq_of_owner hpd hpr ho

/-- A transfer creates and duplicates no authority: it changes holders only (§63, §53). -/
theorem transfer_skel (s : S3) (src dst : Nat) : SameSkel s (transferEff s src dst) := by
  refine ⟨by simp [transferEff], fun j => ?_⟩
  rw [transfer_A_get]
  cases s.A[j]? with
  | none => rfl
  | some y => simp only [Option.map_some]; split <;> rfl

/-- A place usable after a transfer of a usable `src` was usable before (§40, §63). -/
theorem transfer_usable_back {s : S3} {src dst : Nat} (hwf : WF3 s) (hsrc : s.Usable src)
    {q : Nat} (h : (transferEff s src dst).Usable q) : s.Usable q := by
  induction h with
  | @frame q f pl hpl hd ho hf =>
    rw [transfer_P_get] at hpl
    cases h' : s.P[q]? with
    | none => rw [h'] at hpl; cases hpl
    | some pl =>
      rw [h'] at hpl; simp only [Option.map_some, Option.some.injEq] at hpl; subst hpl
      split at ho
      · rename_i hh
        obtain ⟨r', e⟩ := mvTo_place (dst := dst) hh
        simp [e] at ho
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

/-- A place usable before a transfer stays usable when `dst` is usable after it (§40, §63: places
owned by a part of `src` become owned by a part of `dst`). -/
theorem transfer_usable_fwd {s : S3} {src dst : Nat} (hw : WF3 s)
    (hd' : (transferEff s src dst).Usable dst) {q : Nat} (h : s.Usable q) :
    (transferEff s src dst).Usable q := by
  have hdl : dst < s.P.length := by have := hd'.lt; rwa [transfer_len] at this
  induction h with
  | @frame q f pl hpl hd ho hf =>
    exact .frame (by rw [transfer_P_get, hpl]; rfl) hd (by simp [ho, heldIn]) hf
  | @place q o pl hpl hd ho _ ih =>
    by_cases hh : heldIn s.P src (.place o)
    · obtain ⟨r', e, hr'⟩ := mvTo_part hw hdl hh
      exact .place (by rw [transfer_P_get, hpl]; rfl) hd (by simp [ho, hh, e])
        (transfer_usable_part hw hr' hd')
    · exact .place (by rw [transfer_P_get, hpl]; rfl) hd (by simp [ho, hh]) ih

/-! ## `NoOrphan` from `WF3` (§54) -/

/-- Membership in a `dropWhile` (§54, chains without repetition). -/
theorem mem_of_mem_dropWhile {p : Nat → Bool} : ∀ {l : List Nat} {x : Nat},
    x ∈ l.dropWhile p → x ∈ l
  | [], _, h => by simp at h
  | b :: l, x, h => by
    simp only [List.dropWhile_cons] at h
    split at h
    · exact List.mem_cons_of_mem _ (mem_of_mem_dropWhile h)
    · exact h

/-- `Linked` on a cons (§54). -/
theorem linked_cons {R : Nat → Nat → Prop} {a : Nat} {l : List Nat} :
    Linked R (a :: l) ↔ (∀ b, l.head? = some b → R a b) ∧ Linked R l := by
  cases l with
  | nil => simp [Linked]
  | cons b l => simp [Linked]

/-- A suffix of a linked list is linked (§54). -/
theorem linked_dropWhile {R : Nat → Nat → Prop} {p : Nat → Bool} :
    ∀ {l : List Nat}, Linked R l → Linked R (l.dropWhile p)
  | [], h => h
  | b :: l, h => by
    simp only [List.dropWhile_cons]
    split
    · exact linked_dropWhile (linked_cons.1 h).2
    · exact h

/-- The last element of a cons with a nonempty tail is the last element of the tail (§54). -/
theorem getLast?_cons_ne {a : Nat} : ∀ {l : List Nat}, l ≠ [] → (a :: l).getLast? = l.getLast?
  | [], h => absurd rfl h
  | _ :: _, _ => by simp [List.getLast?_cons_cons]

/-- The last element of `l ++ [x]` is `x` (§54). -/
theorem getLast?_append_single {x : Nat} : ∀ (l : List Nat), (l ++ [x]).getLast? = some x
  | [] => rfl
  | a :: l => by
    rw [List.cons_append, getLast?_cons_ne (by simp)]; exact getLast?_append_single l

/-- A nonempty `dropWhile` keeps the last element (§54). -/
theorem getLast?_dropWhile {p : Nat → Bool} : ∀ {l : List Nat}, l.dropWhile p ≠ [] →
    (l.dropWhile p).getLast? = l.getLast?
  | [], h => absurd rfl h
  | b :: l, h => by
    simp only [List.dropWhile_cons] at h ⊢
    split at h
    · rename_i hb; simp only [hb, ↓reduceIte]
      have hl : l ≠ [] := fun e => by subst e; exact h rfl
      rw [getLast?_dropWhile h, getLast?_cons_ne hl]
    · rename_i hb; simp only [hb]; rfl

/-- `dropWhile` does not lengthen a list (§54). -/
theorem length_dropWhile_le {p : Nat → Bool} : ∀ (l : List Nat),
    (l.dropWhile p).length ≤ l.length
  | [] => Nat.le_refl _
  | b :: l => by
    simp only [List.dropWhile_cons]
    split
    · exact Nat.le_trans (length_dropWhile_le l) (Nat.le_succ _)
    · exact Nat.le_refl _

/-- Dropping up to a member stops at that member (§54). -/
theorem dropWhile_ne_of_mem {a : Nat} : ∀ {l : List Nat}, a ∈ l →
    ∃ t, l.dropWhile (· != a) = a :: t
  | b :: l, h => by
    simp only [List.dropWhile_cons]
    by_cases e : b = a
    · subst e; simp
    · have : (b != a) = true := by simp [e]
      simp only [this, ↓reduceIte]
      exact dropWhile_ne_of_mem (by rcases List.mem_cons.1 h with h | h
                                    · exact absurd h.symm e
                                    · exact h)

/-- Removes the loops of a walk (§54, non-repeating chains): the first element is kept, and an
element that occurs again later cuts the walk to its later occurrence. `n` is a fuel, at least the
length. -/
def dropLoops : Nat → List Nat → List Nat
  | 0, l => l
  | _ + 1, [] => []
  | n + 1, a :: c => if a ∈ c then dropLoops n (c.dropWhile (· != a)) else a :: dropLoops n c

/-- `dropLoops` keeps only elements of the walk (§54). -/
theorem mem_dropLoops : ∀ (n : Nat) {l : List Nat} {x : Nat}, x ∈ dropLoops n l → x ∈ l
  | 0, _, _, h => h
  | _ + 1, [], _, h => h
  | n + 1, a :: c, x, h => by
    simp only [dropLoops] at h
    split at h
    · exact List.mem_cons_of_mem _ (mem_of_mem_dropWhile (mem_dropLoops n h))
    · rcases List.mem_cons.1 h with rfl | h
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (mem_dropLoops n h)

/-- `dropLoops` keeps the first element (§54). -/
theorem dropLoops_head : ∀ (n : Nat) (l : List Nat), (dropLoops n l).head? = l.head?
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | n + 1, a :: c => by
    simp only [dropLoops]
    split
    · rename_i hac
      obtain ⟨t, ht⟩ := dropWhile_ne_of_mem hac
      rw [ht, dropLoops_head n]; rfl
    · rfl

/-- `dropLoops` of a nonempty walk is nonempty (§54). -/
theorem dropLoops_ne_nil {n : Nat} {l : List Nat} (h : l ≠ []) : dropLoops n l ≠ [] := by
  intro e
  have := dropLoops_head n l
  rw [e] at this
  cases l with
  | nil => exact h rfl
  | cons _ _ => cases this

/-- `dropLoops` keeps the last element (§54). -/
theorem dropLoops_getLast : ∀ (n : Nat) (l : List Nat), (dropLoops n l).getLast? = l.getLast?
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | n + 1, a :: c => by
    simp only [dropLoops]
    split
    · rename_i hac
      have hc : c ≠ [] := fun e => by subst e; simp at hac
      obtain ⟨t, ht⟩ := dropWhile_ne_of_mem hac
      rw [dropLoops_getLast n, getLast?_dropWhile (by rw [ht]; simp), getLast?_cons_ne hc]
    · by_cases hc : c = []
      · subst hc; cases n <;> rfl
      · rw [getLast?_cons_ne (dropLoops_ne_nil hc), getLast?_cons_ne hc, dropLoops_getLast n]

/-- With enough fuel, `dropLoops` gives a walk without repetition (§54). -/
theorem dropLoops_nodup : ∀ (n : Nat) (l : List Nat), l.length ≤ n → (dropLoops n l).Nodup
  | 0, [], _ => List.nodup_nil
  | 0, _ :: _, h => absurd h (by simp)
  | _ + 1, [], _ => List.nodup_nil
  | n + 1, a :: c, h => by
    simp only [dropLoops]
    split
    · rename_i hac
      exact dropLoops_nodup n _ (Nat.le_trans (length_dropWhile_le c) (by simpa using h))
    · rename_i hac
      exact List.nodup_cons.2 ⟨fun hm => hac (mem_dropLoops n hm),
        dropLoops_nodup n c (by simpa using h)⟩

/-- `dropLoops` keeps a walk linked (§54). -/
theorem dropLoops_linked {R : Nat → Nat → Prop} : ∀ (n : Nat) {l : List Nat}, Linked R l →
    Linked R (dropLoops n l)
  | 0, _, h => h
  | _ + 1, [], h => h
  | n + 1, a :: c, h => by
    simp only [dropLoops]
    split
    · exact dropLoops_linked n (linked_dropWhile (linked_cons.1 h).2)
    · refine linked_cons.2 ⟨fun b hb => ?_, dropLoops_linked n (linked_cons.1 h).2⟩
      rw [dropLoops_head] at hb
      exact (linked_cons.1 h).1 b hb

/-- Extending a linked walk ending at `i` by `x` with `R i x` keeps it linked (§54). -/
theorem linked_append {R : Nat → Nat → Prop} {i x : Nat} (hr : R i x) :
    ∀ {l : List Nat}, Linked R l → l.getLast? = some i → Linked R (l ++ [x])
  | [], _, h => by cases h
  | [b], _, h => by
    simp only [List.getLast?_singleton, Option.some.injEq] at h
    subst h; exact ⟨hr, trivial⟩
  | b :: c :: l, hl, h => by
    have := linked_append hr (l := c :: l) hl.2
      (by rw [← getLast?_cons_ne (a := b) (by simp)]; exact h)
    exact ⟨hl.1, this⟩

/-- The root authority of the root place of a usable place `q` (§49.7) is active, covers the
footprint of `q`, and is held by the owner of `q` (§40, §54). -/
theorem rootHeld_cover {s : S3} (hw : WF3 s) {q : Nat} {pl : Place}
    (hpl : s.P[q]? = some pl) (hq : s.Usable q) :
    ∃ (i : Nat) (z : Authority), s.A[i]? = some z ∧ z.active = true ∧ z.holder = pl.owner ∧
      ∀ l ∈ footprint s.P q, l ∈ z.footprint := by
  obtain ⟨r, hrp, hqr⟩ := exists_rootPlace hw (q + 1) q (Nat.lt_succ_self q) (lt_of_getElem? hpl)
  obtain ⟨i, z, pr, hz, za, -, -, hpr, hzh, hzf⟩ := hw.rootHeld r hrp (usable_of_part hw hqr hq)
  obtain ⟨pl', pr', hpl', hpr', he⟩ := hw.ownerOf hqr
  rw [hpl] at hpl'; cases hpl'; rw [hpr] at hpr'; cases hpr'
  exact ⟨i, z, hz, za, by rw [hzh, he], fun l hl => (hzf l).2 (footprint_sub hw hqr hl)⟩

/-- An active authority covering every leaf of the place holding `x` is a link to `x` (§54). -/
theorem coversHolder_of {s : S3} {i x : Nat} {z y : Authority} {q : Nat} (hz : s.A[i]? = some z)
    (za : z.active = true) (hx : s.A[x]? = some y) (hh : y.holder = .place q)
    (hc : ∀ l ∈ footprint s.P q, l ∈ z.footprint) : CoversHolder s i x := by
  simp only [CoversHolder, OptP, hx, hh]
  exact ⟨⟨z, hz, za⟩, fun l hl => by simp only [S3.afp, hz]; exact hc l hl⟩

/-- Under `WF3`, an active authority held by a usable place is linked to a frame of the stack by
a walk of authorities, possibly with repetitions: the root authorities along the ownership chain
of its holder (§49.7, §54). -/
theorem chain_to_frame {s : S3} (hw : WF3 s) {q : Nat} (hq : s.Usable q) :
    ∀ (x : Nat) (y : Authority), s.A[x]? = some y → y.active = true → y.holder = .place q →
      ∃ (a₀ : Nat) (z : Authority) (f : Nat) (c : List Nat), s.A[a₀]? = some z ∧
        z.active = true ∧ z.holder = .frame f ∧ f ∈ s.F ∧ (a₀ :: c).getLast? = some x ∧
        Linked (CoversHolder s) (a₀ :: c) := by
  induction hq with
  | @frame q f pl hpl hd ho hf =>
    intro x y hx ya hh
    obtain ⟨i, z, hz, za, hzh, hzf⟩ := rootHeld_cover hw hpl (.frame hpl hd ho hf)
    exact ⟨i, z, f, [x], hz, za, by rw [hzh, ho], hf, rfl,
      ⟨coversHolder_of hz za hx hh hzf, trivial⟩⟩
  | @place q o pl hpl hd ho hu ih =>
    intro x y hx ya hh
    obtain ⟨i, z, hz, za, hzh, hzf⟩ := rootHeld_cover hw hpl (.place hpl hd ho hu)
    obtain ⟨a₀, z₀, f, c, h0, h0a, h0h, hf, hlast, hlink⟩ := ih i z hz za (by rw [hzh, ho])
    refine ⟨a₀, z₀, f, c ++ [x], h0, h0a, h0h, hf, ?_, ?_⟩
    · rw [← List.cons_append]; exact getLast?_append_single _
    · rw [← List.cons_append]; exact linked_append (coversHolder_of hz za hx hh hzf) hlink hlast

/-- `NoOrphan` (§54) holds in every state satisfying `WF3` (§49): the holder of an active
authority held by a place is usable (§49.8), the root authorities along its ownership chain
(§49.7) link it to a frame of the stack, and the loops of that walk can be removed. -/
theorem noOrphan_of_wf3 {s : S3} (hw : WF3 s) : NoOrphan s := by
  intro x y q hx ya hh
  have hq : s.Usable q := by have := hw.holders x y hx ya; rw [hh] at this; exact this
  obtain ⟨a₀, z, f, c, hz, za, hzh, hf, hlast, hlink⟩ := chain_to_frame hw hq x y hx ya hh
  have hhd := dropLoops_head (c.length + 1) (a₀ :: c)
  obtain ⟨t, ht⟩ : ∃ t, dropLoops (c.length + 1) (a₀ :: c) = a₀ :: t := by
    cases e : dropLoops (c.length + 1) (a₀ :: c) with
    | nil => exact absurd e (dropLoops_ne_nil (by simp))
    | cons b t => rw [e] at hhd; cases hhd; exact ⟨t, rfl⟩
  refine ⟨a₀, z, f, t, hz, za, hzh, hf, ?_, ?_, ?_⟩
  · rw [← ht]; exact dropLoops_nodup _ _ (Nat.le_refl _)
  · rw [← ht, dropLoops_getLast]; exact hlast
  · rw [← ht]; exact dropLoops_linked _ hlink

end Ern.MemoryModel.Access
