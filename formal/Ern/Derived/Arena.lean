import Ern.MM03.Horrors

/-!
# Derivability of the arena operations (derivability pass 0.1, question 1)

The hypothesis of the brief: with `MetaRight` restricted to exercisable `Modify` on the arena value
(its `writeShared` branch removed), `issue` (O18) and `reset` (O19) of the candidate Spec 1 (§77,
§78) are realised by the kernel operations O1–O16 and the abstraction metadata (`available`,
`issued`, the registry), and no safety property depends on the registration and the guard of
`newArena` (O17.4, §56). The kernel (`Ern.MM03`) is unchanged; the restricted operations are
defined here from the text of the candidate Spec 1.

* `issue`: the restricted `issue` (`IssueR`) against `split` of `internal` on the region (O2, one
  region: a `Modify` derivation on a list of leaves) or `derive` of `internal` on a place (O1), then
  `store` (O8) into the destination. `issue_as_kernel_split` and `issue_as_kernel` give both
  directions with the same arrival state, and name the two clauses on which the operation and the
  sequence differ: `store` asks the destination still exercisable in the arrival state (O8.5), the
  restricted `issue` does not (`ce_g2`); `issue` asks the destination not `Init` (O18.2), `store`
  does not (O8.2, `ce_init`).
* `reset`: the restricted `reset` (`ResetPreR`) against `derive` of `internal` on the storage, then
  `release` of the derived authority (`reset_as_kernel`). The sequence does not give the third
  clause of `reset`, nor the second for an active derivation of empty footprint (`ce_reset_anchor`,
  `ce_reset_empty`).
* `writeShared`: `ce_writeShared`, the kernel `issue` and `reset` accepted through the `writeShared`
  branch of `MetaRight` where the sequences are rejected.
* `newArena`: `newArena_as_library`.
-/

namespace Ern.Derived.Arena

open Ern.MM03 Ern.HandlePool Ern.MM03.Horrors

/-! ## Restricted metadata right -/

/-- `MetaRight` restricted to its first branch (brief, question 1; candidate Spec 1 §77.1, §78.1):
exercisable `Modify` on the arena value, the holder of `internal` (§46). The `writeShared` branch
of §78.1 is removed. -/
def MetaRightM (s : S3) (ar : Arena) : Prop :=
  OptP (arenaValue s ar) (fun v => HasRight s .modify v) False

instance (s : S3) (ar : Arena) : Decidable (MetaRightM s ar) := by
  unfold MetaRightM; infer_instance

/-- The restricted right implies the kernel `MetaRight` (its first disjunct), for any contracts and
any `via`. -/
theorem metaRightM_metaRight {k : K} {s : S3} {ar : Arena} {via : Nat} (h : MetaRightM s ar) :
    MetaRight k s ar via := .inl h

/-! ## Restricted `issue` (candidate Spec 1 §77) -/

/-- Static preconditions of the restricted `issue` (candidate Spec 1 §77, clauses 1 and 2, with
`MetaRightM`): clause 1, restricted metadata right and `internal` active; clause 2, the region
within the administered storage, the destination a usable leaf, under exercisable `Modify`, not
`Init`, holding no active authority, and not in the region ("Prévention locale de l'auto-blocage",
§88). The static restrictions of clause 3 are those of the kernel (`IssueStatic`,
`issueStaticR_iff`); its `AnchorOrder` check is on the arrival state (`ArrivalR`). -/
def IssueStaticR (s : S3) (ar : Arena) (region : List Nat) (dst : Nat) : Prop :=
  MetaRightM s ar ∧ s.Active ar.internal ∧ (∀ l ∈ region, l ∈ s.afp ar.internal) ∧
  s.Usable dst ∧ HasRight s .modify dst ∧ (∀ l ∈ footprint s.P dst, s.I l ≠ .init) ∧
  isLeaf s.P dst ∧
  (∀ j ∈ List.range s.A.length, OptP (s.A[j]?) (fun z => z.active = true → z.holder ≠ .place dst)
    True) ∧
  dst ∉ region

instance (s : S3) (ar : Arena) (region : List Nat) (dst : Nat) :
    Decidable (IssueStaticR s ar region dst) := by
  unfold IssueStaticR; infer_instance

/-- The static preconditions of the restricted `issue` are those of the kernel `issue`
(`IssueStatic`) with the restricted right and the destination outside the region. -/
theorem issueStaticR_iff {k : K} {via : Nat} {s : S3} {ar : Arena} {region : List Nat}
    {dst : Nat} : IssueStaticR s ar region dst ↔
      MetaRightM s ar ∧ IssueStatic k s ar via region dst ∧ dst ∉ region := by
  unfold IssueStaticR IssueStatic
  exact ⟨fun ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ => ⟨h0, ⟨.inl h0, h1, h2, h3, h4, h5, h6, h7⟩, h8⟩,
    fun ⟨h0, ⟨_, h1, h2, h3, h4, h5, h6, h7⟩, h8⟩ => ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩⟩

/-- Effect of the restricted `issue` (candidate Spec 1 §77, effect): the effect of the kernel
(`issueEff`: the block, held by the destination, which alone becomes `Init`; the region leaves
`available` and joins `issued`), and the destination "reçoit l'ancre correspondante": the block is
added to `D dst`, which the kernel `issueEff` does not do. -/
def issueEffR (s : S3) (ar : Arena) (region : List Nat) (dst : Nat) : S3 × Arena :=
  ({ (issueEff s ar region dst).1 with
      D := fun q => if q = dst then s.D dst ++ [s.A.length] else s.D q },
   (issueEff s ar region dst).2)

/-- Checks of the restricted `issue` on the simulated arrival state (candidate Spec 1 §77.3 and
§77.6): `AnchorOrder` for the new anchor of the destination, and `AnchorOrderHeld`. -/
def ArrivalR (s : S3) (ar : Arena) (region : List Nat) (dst : Nat) : Prop :=
  EffAnchorOK (issueEffR s ar region dst).1 s.A.length ((issueEffR s ar region dst).1.pframe dst) ∧
  AnchorOrderHeld (issueEffR s ar region dst).1

instance (s : S3) (ar : Arena) (region : List Nat) (dst : Nat) :
    Decidable (ArrivalR s ar region dst) := by
  unfold ArrivalR; infer_instance

/-- The restricted `issue` as a relation (candidate Spec 1 §77; §58): `reject` when a static
precondition fails; `fail`, the state unchanged, when the region is not available (§77.4);
`reject` when `internal` lacks effective `Modify` on the region (§77.5) or an arrival check fails
(§77.3, §77.6); `ok` otherwise. The disjointness of §77.5 from the active emissions is not
restated: it follows from the effective right (`issue_disjoint_redundant`, A11). -/
inductive IssueR (ar : Arena) (region : List Nat) (dst : Nat) (s : S3) : IOutcome → Prop where
  | ok : IssueStaticR s ar region dst → Avail ar region → IssueRight s ar region →
      ArrivalR s ar region dst →
      IssueR ar region dst s (.ok (issueEffR s ar region dst).1 (issueEffR s ar region dst).2)
  | fail : IssueStaticR s ar region dst → ¬ Avail ar region → IssueR ar region dst s (.fail s ar)
  | reject : ¬ IssueStaticR s ar region dst → IssueR ar region dst s .reject
  | noRight : IssueStaticR s ar region dst → Avail ar region → ¬ IssueRight s ar region →
      IssueR ar region dst s .reject
  | noAnchor : IssueStaticR s ar region dst → Avail ar region → IssueRight s ar region →
      ¬ ArrivalR s ar region dst → IssueR ar region dst s .reject

/-- Determinism of the restricted `issue`. -/
theorem issueR_det {ar : Arena} {region : List Nat} {dst : Nat} {s : S3} {o₁ o₂ : IOutcome}
    (h₁ : IssueR ar region dst s o₁) (h₂ : IssueR ar region dst s o₂) : o₁ = o₂ := by
  cases h₁ <;> cases h₂ <;> first | rfl | contradiction

/-- Totality of the restricted `issue`: every state has an outcome. -/
theorem issueR_total (ar : Arena) (region : List Nat) (dst : Nat) (s : S3) :
    ∃ o, IssueR ar region dst s o := by
  by_cases h1 : IssueStaticR s ar region dst
  · by_cases h2 : Avail ar region
    · by_cases h3 : IssueRight s ar region
      · by_cases h4 : ArrivalR s ar region dst
        · exact ⟨_, .ok h1 h2 h3 h4⟩
        · exact ⟨_, .noAnchor h1 h2 h3 h4⟩
      · exact ⟨_, .noRight h1 h2 h3⟩
    · exact ⟨_, .fail h1 h2⟩
  · exact ⟨_, .reject h1⟩

/-- `ok` outcome of the restricted `issue`. -/
theorem issueR_ok_iff {ar ar' : Arena} {region : List Nat} {dst : Nat} {s s' : S3} :
    IssueR ar region dst s (.ok s' ar') ↔ IssueStaticR s ar region dst ∧ Avail ar region ∧
      IssueRight s ar region ∧ ArrivalR s ar region dst ∧ (s', ar') = issueEffR s ar region dst := by
  constructor
  · intro h; cases h with
    | ok h1 h2 h3 h4 => exact ⟨h1, h2, h3, h4, rfl⟩
  · rintro ⟨h1, h2, h3, h4, e⟩
    have e1 := congrArg Prod.fst e; have e2 := congrArg Prod.snd e
    simp only at e1 e2; subst e1 e2; exact .ok h1 h2 h3 h4

/-- `fail` outcome of the restricted `issue` (§77.4): the static preconditions hold and the region
is not available in the metadata. -/
theorem issueR_fail_iff {ar ar' : Arena} {region : List Nat} {dst : Nat} {s s' : S3} :
    IssueR ar region dst s (.fail s' ar') ↔
      IssueStaticR s ar region dst ∧ ¬ Avail ar region ∧ s' = s ∧ ar' = ar := by
  constructor
  · intro h; cases h with
    | fail h1 h2 => exact ⟨h1, h2, rfl, rfl⟩
  · rintro ⟨h1, h2, rfl, rfl⟩; exact .fail h1 h2

/-- `reject` outcome of the restricted `issue`: neither `ok` nor `fail`. -/
theorem issueR_reject_iff {ar : Arena} {region : List Nat} {dst : Nat} {s : S3} :
    IssueR ar region dst s .reject ↔
      (∀ s' ar', ¬ IssueR ar region dst s (.ok s' ar')) ∧
      (∀ s' ar', ¬ IssueR ar region dst s (.fail s' ar')) := by
  constructor
  · intro h
    exact ⟨fun _ _ h' => (by cases issueR_det h h'), fun _ _ h' => (by cases issueR_det h h')⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨o, ho⟩ := issueR_total ar region dst s
    cases o with
    | ok s' ar' => exact absurd ho (h1 s' ar')
    | fail s' ar' => exact absurd ho (h2 s' ar')
    | reject => exact ho

/-! ## The kernel sequence for `issue` -/

/-- The authority that `split` of `internal` on `[region]` (O2), or `derive` of `internal` at
`Modify` on a place of footprint `region` (O1), adds to the state: `Modify`, origin `internal`,
held by the current frame. -/
def blockOf (s : S3) (ar : Arena) (region : List Nat) : Authority :=
  ⟨.modify, some ar.internal, region, .frame s.top, true⟩

theorem splitEff_one (s : S3) (ar : Arena) (region : List Nat) :
    splitEff s ar.internal [region] = s.addAuth (blockOf s ar region) := rfl

theorem deriveEff_eq (s : S3) (ar : Arena) (q : Nat) :
    deriveEff s ar.internal q .modify = s.addAuth (blockOf s ar (footprint s.P q)) := rfl

/-- Arrival state (brief, question 1, "le même état d'arrivée sur la partie noyau"): the kernel
part of the arrival state of the restricted `issue` is the arrival state of the sequence, the
derived block stored into the destination (O8). -/
theorem issueEffR_eq (s : S3) (ar : Arena) (region : List Nat) (dst : Nat) :
    (issueEffR s ar region dst).1 =
      storeEff (s.addAuth (blockOf s ar region)) s.A.length dst := by
  rw [storeEff_eq (addAuth_self _ _)]
  simp [issueEffR, issueEff, S3.addAuth, blockOf, List.set_append_right]

/-! ## Transport lemmas -/

theorem allows_modify_iff {e : Option Mode} : Allows e .modify ↔ e = some .modify := by
  cases e with
  | none => simp [Allows, OptP]
  | some m => cases m <;> simp [Allows, OptP, Mode.le]

theorem allows_some_modify (m : Mode) : Allows (some .modify) m := by
  cases m <;> simp [Allows, OptP, Mode.le]

/-- An exercise at `Modify` is an exercise at every mode (§43: `Observe ≤ Modify`). -/
theorem exercisable_of_modify {s : S3} {a : Nat} {m : Mode} (h : s.ExercisableAt a .modify) :
    s.ExercisableAt a m := by
  generalize hm : Mode.modify = m' at h
  induction h with
  | base hy ha hle hf =>
    subst hm
    exact .base hy ha (.inr (hle.resolve_left (by decide))) hf
  | held hy ha hle hp _ hc ih =>
    subst hm
    exact .held hy ha (.inr (hle.resolve_left (by decide))) hp (ih rfl)
      fun l hl => by rw [allows_modify_iff.1 (hc l hl)]; exact allows_some_modify m

theorem ExercisableAt.lt {s : S3} {a : Nat} {m : Mode} (h : s.ExercisableAt a m) :
    a < s.A.length := by
  cases h <;> exact lt_of_getElem? ‹_›

/-- A permitted effective mode comes from an existing authority covering the leaf. -/
theorem mem_of_allows {s : S3} {a l : Nat} {m : Mode} (h : Allows (effective s a l) m) :
    ∃ x, s.A[a]? = some x ∧ l ∈ x.footprint := by
  unfold effective at h
  cases hx : s.A[a]? with
  | none => rw [hx] at h; exact h.elim
  | some x =>
    rw [hx] at h; simp only at h
    split at h
    · exact ⟨x, rfl, ‹_ ∧ _›.2⟩
    · exact h.elim

theorem allows_effOf_append {m m' : Mode} {ds e : List Mode} (h : Allows (effOf m (ds ++ e)) m') :
    Allows (effOf m ds) m' := by
  by_cases h0 : ds ++ e = []
  · rw [(List.append_eq_nil_iff.1 h0).1]; simpa [effOf, h0] using h
  · by_cases h1 : Mode.modify ∈ ds ++ e
    · simp [effOf, h0, h1, Allows, OptP] at h
    · have hm' : m' = .observe := by
        cases m' with
        | observe => rfl
        | modify => simp [effOf, h0, h1, Allows, OptP, Mode.le] at h
      subst hm'
      have h1' : Mode.modify ∉ ds := fun h' => h1 (List.mem_append_left _ h')
      by_cases hd : ds = []
      · simp [effOf, hd, Allows, OptP, Mode.le]
      · simp [effOf, hd, h1', Allows, OptP, Mode.le]

/-- Adding an authority only takes effective modes away from the existing ones (§43, case 3). -/
theorem allows_addAuth_back {s : S3} {y₀ : Authority} {b l : Nat} {m : Mode} (hb : b < s.A.length)
    (h : Allows (effective (s.addAuth y₀) b l) m) : Allows (effective s b l) m := by
  unfold effective at h ⊢
  rw [addAuth_lt hb, descModes_addAuth] at h
  cases hx : s.A[b]? with
  | none => rw [hx] at h; exact h
  | some x =>
    rw [hx] at h; simp only at h ⊢
    split at h
    · rename_i hc; simp only [hc, and_self, ite_true]; exact allows_effOf_append h
    · exact h.elim

/-- Exercise in the state where the block `y₀` is added, for an authority that existed before,
comes from an exercise before: a link through the block is replaced by a link through `src`, which
is exercisable at `Modify` and has effective `Modify` on every leaf of the block. -/
theorem exercisable_addAuth_back {s : S3} {y₀ : Authority} {src : Nat}
    (hsrc : s.ExercisableAt src .modify)
    (hfp : ∀ l ∈ y₀.footprint, effective s src l = some .modify) {a : Nat} {m : Mode}
    (h : (s.addAuth y₀).ExercisableAt a m) : a < s.A.length → s.ExercisableAt a m := by
  induction h with
  | base hy ha hle hf =>
    intro hlt
    rw [addAuth_lt hlt] at hy
    exact .base hy ha hle hf
  | @held a' p b m' y hy ha hle hp hb hc ih =>
    intro hlt
    rw [addAuth_lt hlt] at hy
    by_cases hbl : b < s.A.length
    · exact .held hy ha hle hp (ih hbl) fun l hl => allows_addAuth_back hbl (hc l hl)
    · have hbe : b = s.A.length := by
        have := hb.lt; simp [S3.addAuth] at this; omega
      subst hbe
      refine .held hy ha hle hp (exercisable_of_modify hsrc) fun l hl => ?_
      obtain ⟨x, hx, hlx⟩ := mem_of_allows (hc l hl)
      rw [addAuth_self] at hx; cases hx
      rw [hfp l hlx]; exact allows_some_modify m'

/-- `HasRight` in the state where the block `y₀` is added, on a place none of whose leaves the block
covers, comes from `HasRight` before. -/
theorem hasRight_addAuth_back {s : S3} {y₀ : Authority} {src p : Nat} {m : Mode}
    (hsrc : s.ExercisableAt src .modify)
    (hfp : ∀ l ∈ y₀.footprint, effective s src l = some .modify)
    (hout : ∀ l ∈ footprint s.P p, l ∉ y₀.footprint) (h : HasRight (s.addAuth y₀) m p) :
    HasRight s m p := by
  obtain ⟨a, -, ha, hall⟩ := h
  by_cases hlt : a < s.A.length
  · exact ⟨a, List.mem_range.2 hlt, exercisable_addAuth_back hsrc hfp ha hlt,
      fun l hl => allows_addAuth_back hlt (hall l hl)⟩
  · have hae : a = s.A.length := by
      have := ha.lt; simp [S3.addAuth] at this; omega
    subst hae
    refine ⟨src, List.mem_range.2 hsrc.lt, exercisable_of_modify hsrc, fun l hl => ?_⟩
    obtain ⟨x, hx, hlx⟩ := mem_of_allows (hall l hl)
    rw [addAuth_self] at hx; cases hx
    exact absurd hlx (hout l hl)

/-- Exercise after `store` (O8) comes from an exercise before: `store` only moves the stored
authority from the current frame to a place, and keeps every effective mode (`store_skel`). -/
theorem exercisable_store_back {s : S3} {a p : Nat} {y : Authority} (hy : s.A[a]? = some y)
    (hh : y.holder = .frame s.top) {b : Nat} {m : Mode} (h : (storeEff s a p).ExercisableAt b m) :
    s.ExercisableAt b m := by
  have hA : (storeEff s a p).A = s.A.set a { y with holder := .place p } := by
    rw [storeEff_eq hy]
  have hF : (storeEff s a p).F = s.F := by rw [storeEff_eq hy]
  have hP : (storeEff s a p).P = s.P := by rw [storeEff_eq hy]
  have he := (store_skel s a p).effective
  have hal := lt_of_getElem? hy
  induction h with
  | @base b m z hz za hle hf =>
    have hne : a ≠ b := by
      rintro rfl
      rw [hA, List.getElem?_set_self hal] at hz; cases hz
      simp at hf
    rw [hA, List.getElem?_set_ne hne] at hz
    exact .base hz za hle (by rw [hf]; simp only [S3.top, hF])
  | @held b q c m z hz za hle hq _ hc ih =>
    by_cases hba : a = b
    · subst hba
      rw [hA, List.getElem?_set_self hal] at hz; cases hz
      exact .base hy za hle hh
    · rw [hA, List.getElem?_set_ne hba] at hz
      exact .held hz za hle hq ih fun l hl => by rw [← he]; exact hc l (by rw [hP]; exact hl)

/-- `HasRight` after `store` comes from `HasRight` before. -/
theorem hasRight_store_back {s : S3} {a p q : Nat} {y : Authority} {m : Mode}
    (hy : s.A[a]? = some y) (hh : y.holder = .frame s.top) (h : HasRight (storeEff s a p) m q) :
    HasRight s m q := by
  obtain ⟨b, -, hb, hall⟩ := h
  have hP : (storeEff s a p).P = s.P := by rw [storeEff_eq hy]
  have hb' := exercisable_store_back hy hh hb
  exact ⟨b, List.mem_range.2 hb'.lt, hb', fun l hl => by
    rw [← (store_skel s a p).effective]; exact hall l (by rw [hP]; exact hl)⟩

/-- A place of the strict ancestors of `i` is the parent of some place. -/
theorem mem_chainF_parent {org : Nat → Option Nat} :
    ∀ k i x, x ∈ chainF org k i → ∃ j, org j = some x
  | 0, _, _, h => by simp [chainF] at h
  | k + 1, i, x, h => by
    simp only [chainF] at h
    cases ho : org i with
    | none => rw [ho] at h; simp at h
    | some o =>
      rw [ho] at h; simp only at h
      split at h
      · rcases List.mem_cons.1 h with rfl | h
        · exact ⟨i, ho⟩
        · exact mem_chainF_parent k o x h
      · simp at h

/-- A leaf is a strict ancestor of no place (§42, `isLeaf`). -/
theorem not_mem_chain_of_leaf {P : List Place} {d x : Nat} (hd : isLeaf P d) :
    d ∉ chain (parentOf P) x := by
  intro h
  obtain ⟨j, hj⟩ := mem_chainF_parent _ _ _ h
  have hjl : j < P.length := by
    unfold parentOf at hj
    cases hp : P[j]? with
    | none => rw [hp] at hj; simp at hj
    | some _ => exact lt_of_getElem? hp
  exact hd j hjl hj

/-- The footprint of a leaf is the leaf itself. -/
theorem mem_footprint_leaf {P : List Place} {d l : Nat} (hd : isLeaf P d) (hlt : d < P.length) :
    l ∈ footprint P d ↔ l = d := by
  constructor
  · intro hl
    obtain ⟨-, -, -, h⟩ := mem_footprint.1 hl
    exact h.resolve_right (not_mem_chain_of_leaf hd)
  · rintro rfl; exact mem_footprint.2 ⟨hlt, hd, hlt, .inl rfl⟩

/-- `NoDangling` (§54): a place containing a leaf covered by an active authority is usable. -/
theorem usable_of_covered {s : S3} (hnd : NoDangling s) {j q l : Nat} {y : Authority}
    (hy : s.A[j]? = some y) (ya : y.active = true) (hly : l ∈ y.footprint)
    (hl : l ∈ footprint s.P q) : s.Usable q :=
  Decidable.byContradiction fun hu => hnd j y hy ya q hu l hl hly

/-- A usable place owned, transitively, by the leaf `dst` makes `dst` hold an active authority: the
root authority of its root place, held by the owner of that place (`RootLive`, §54). -/
theorem ownedIn_holds {s : S3} (hw : WF3 s) (hr : RootLive s) {dst : Nat} (hd : isLeaf s.P dst)
    {q : Nat} (h : OwnedIn s.P dst q) (hu : s.Usable q) :
    ∃ (j : Nat) (z : Authority), s.A[j]? = some z ∧ z.active = true ∧ z.holder = .place dst := by
  induction h with
  | @direct q o pl hq ho hpo =>
    have hod : o = dst := hpo.2.resolve_right (not_mem_chain_of_leaf hd)
    subst hod
    obtain ⟨r, hrp, hqr⟩ := exists_rootPlace hw (q + 1) q (Nat.lt_succ_self q) hu.lt
    obtain ⟨pl', pr, hpl', hpr, hown⟩ := hw.ownerOf hqr
    rw [hq] at hpl'; cases hpl'
    have hdead : s.dead r = false := by rw [← hw.deadOf hqr]; cases hu <;> assumption
    have hou : s.Usable o := by
      cases hu with
      | frame hq' _ ho' _ => rw [hq] at hq'; cases hq'; rw [ho] at ho'; cases ho'
      | place hq' _ ho' hu' => rw [hq] at hq'; cases hq'; rw [ho] at ho'; cases ho'; exact hu'
    have hur : s.Usable r := .place hpr hdead (by rw [← hown, ho]) hou
    obtain ⟨i, z, pr', hz, za, -, hpr', hzh, -⟩ := hr r hrp hur
    rw [hpr] at hpr'; cases hpr'
    exact ⟨i, z, hz, za, by rw [hzh, ← hown, ho]⟩
  | @step q o pl hq ho _ ih =>
    apply ih
    cases hu with
    | frame hq' _ ho' _ => rw [hq] at hq'; cases hq'; rw [ho] at ho'; cases ho'
    | place hq' _ ho' hu' => rw [hq] at hq'; cases hq'; rw [ho] at ho'; cases ho'; exact hu'

/-- An active `Modify` descendant of `a` covering `p` takes the effective `Modify` of `a` on `p`
away (§43, case 3). -/
theorem effective_ne_modify_of_desc {s : S3} {a j p : Nat} {y : Authority} (hy : s.A[j]? = some y)
    (ya : y.active = true) (hp : p ∈ y.footprint) (hj : a ∈ s.ancs j) (hm : y.mode = .modify) :
    effective s a p ≠ some .modify := by
  intro he
  obtain ⟨x, -, -, -, hx⟩ := effective_some he
  have hmem : Mode.modify ∈ descModes s a p := mem_descModes.2 ⟨j, y, hy, ya, hp, hj, hm⟩
  rcases effOf_cases hx with ⟨h0, -⟩ | ⟨-, h1, -⟩
  · rw [h0] at hmem; simp at hmem
  · exact h1 hmem

/-- The restricted right is exactly the exercise of `internal` at `Modify` (§43), the first
precondition of `derive` and `split` on `internal` (O1.1, O2.1): `internal` is a `Modify` authority
held by the arena value (`ArenaInv`, §55). -/
theorem metaRightM_iff {s : S3} {ar : Arena} (hai : ArenaInv s ar) (hact : s.Active ar.internal) :
    MetaRightM s ar ↔ s.ExercisableAt ar.internal .modify := by
  obtain ⟨y, v, hy, hm, hv⟩ := hai.2.2.2.2.2.2.1
  have hav : arenaValue s ar = some v := by simp [arenaValue, hy, hv]
  obtain ⟨y', hy', ya⟩ := hact
  rw [hy] at hy'; cases hy'
  unfold MetaRightM; rw [hav]; simp only [OptP]
  constructor
  · rintro ⟨b, -, hb, hall⟩
    exact .held hy ya (.inr hm) hv hb hall
  · intro h
    cases h with
    | base hy₂ _ _ hf => rw [hy] at hy₂; cases hy₂; rw [hv] at hf; cases hf
    | held hy₂ _ _ hp hb hc =>
      rw [hy] at hy₂; cases hy₂; rw [hv] at hp; cases hp
      exact ⟨_, List.mem_range.2 hb.lt, hb, hc⟩

/-- The effective anchor of an authority with an origin is strictly older than it. -/
theorem effAnchor_lt {s : S3} {x o : Nat} (ho : s.org x = some o) (hlt : o < x) :
    s.effAnchor x < x := by
  unfold S3.effAnchor S3.ancs
  rw [chain_cons ho hlt]
  exact chain_lt (by rw [chain_cons ho hlt, List.getLastD_cons]; exact List.getLastD_mem_cons)

/-- `store` changes no `EffAnchorOK` whose effective anchor is not the stored authority. -/
theorem effAnchorOK_store {s : S3} {a p x : Nat} {y : Authority} (hy : s.A[a]? = some y)
    (hne : s.effAnchor x ≠ a) (fd : Option Nat) :
    EffAnchorOK (storeEff s a p) x fd ↔ EffAnchorOK s x fd := by
  have he : (storeEff s a p).effAnchor x = s.effAnchor x := by
    unfold S3.effAnchor; rw [(store_skel s a p).ancs]
  have hP : (storeEff s a p).P = s.P := by rw [storeEff_eq hy]
  have hF : (storeEff s a p).F = s.F := by rw [storeEff_eq hy]
  have hA : (storeEff s a p).A[s.effAnchor x]? = s.A[s.effAnchor x]? := by
    rw [storeEff_eq hy]; exact List.getElem?_set_ne (Ne.symm hne)
  unfold EffAnchorOK
  rw [he, hA, hF]
  simp only [S3.hframe_congr hP]

/-! ## `issue` as `split` (or `derive`) then `store` -/

section IssueAsKernel

variable {k : K} (hdd : DDSound k) {statics : Statics} {s : S3} (hr : Reachable k statics s)
  {ar : Arena} (har : ar ∈ s.arenas) {region : List Nat} {dst : Nat}
include hdd hr har

/-- Direction `issue` → sequence (brief, question 1): an `ok` of the restricted `issue` whose
destination is still exercisable at `Modify` in the arrival state is the `ok` of `split` of
`internal` on the region, then of `store` of the block into the destination, with the same
arrival state. The extra hypothesis is clause 5 of `store` (O8.5, `store_keeps_target_reachable`),
which the restricted `issue` does not check: `ce_g2` shows it is needed. Clause 3 of `store` on the
storage owned by the destination (O8.3) follows from clause 2 of `issue` (no active authority held
by the destination) in reached states (`ownedIn_holds`). -/
theorem issue_to_seq {s' : S3} {ar' : Arena} (h : IssueR ar region dst s (.ok s' ar'))
    (hg2 : HasRight s' .modify dst) :
    SplitStep k ar.internal [region] s (.ok (s.addAuth (blockOf s ar region))) ∧
      StoreStep s.A.length dst (s.addAuth (blockOf s ar region)) (.ok s') := by
  obtain ⟨hwf, hinv, -, hais⟩ := reachable_invariants hdd hr
  have hrl := reachable_rootLive hdd hr
  obtain ⟨hst, -, hright, harr, he⟩ := issueR_ok_iff.1 h
  have hs' : s' = storeEff (s.addAuth (blockOf s ar region)) s.A.length dst := by
    rw [← issueEffR_eq]; exact congrArg Prod.fst he
  subst hs'
  obtain ⟨hm, hact, hreg, hud, -, -, hleaf, hnoh, hnot⟩ := hst
  have hai := hais ar har hact
  have hex := (metaRightM_iff hai hact).1 hm
  obtain ⟨yi, hyi, yia⟩ := hact
  refine ⟨.ok ⟨⟨yi, hyi, yia⟩, hex, ?_, ?_, List.pairwise_singleton _ _, ?_⟩, .ok ?_⟩
  · intro r hr' p hp; rw [List.mem_singleton.1 hr'] at hp; exact hright p hp
  · intro r hr' p hp; rw [List.mem_singleton.1 hr'] at hp
    exact ⟨hreg p hp, by rw [hright p hp]; simp⟩
  · intro r hr' p hp j _ hd
    rw [List.mem_singleton.1 hr'] at hp
    unfold DistribExcl at hd
    cases hj : s.A[j]? with
    | none => rw [hj] at hd; exact hd
    | some y =>
      rw [hj] at hd; obtain ⟨ya, hanc, hpy, hmy⟩ := hd
      exact effective_ne_modify_of_desc hj ya hpy hanc hmy (hright p hp)
  · -- `StorePre` on the state after `split`
    have hy₀ : (s.addAuth (blockOf s ar region)).A[s.A.length]? = some (blockOf s ar region) :=
      addAuth_self _ _
    have hdl : dst < s.P.length := hud.lt
    have hfd : ∀ l, l ∈ footprint s.P dst ↔ l = dst := fun l => mem_footprint_leaf hleaf hdl
    have hu₁ : (s.addAuth (blockOf s ar region)).Usable dst :=
      (S3.Usable.congr (s := s) (s' := s.addAuth (blockOf s ar region)) rfl rfl rfl).2 hud
    have hne : (s.addAuth (blockOf s ar region)).effAnchor s.A.length ≠ s.A.length := by
      have := effAnchor_lt (s := s.addAuth (blockOf s ar region)) (x := s.A.length)
        (o := ar.internal) (by simp only [S3.org, hy₀]; rfl) (lt_of_getElem? hyi)
      omega
    refine ⟨by simp [OptP, blockOf, S3.top, S3.addAuth], hu₁, ?_, ?_, ?_, hleaf, ?_, ?_, ?_⟩
    · exact hasRight_store_back hy₀ rfl hg2
    · intro l hl
      have hlr : l ∈ region := by simp only [S3.afp, hy₀] at hl; exact hl
      refine ⟨fun hld => hnot (by rw [(hfd l).1 hld] at hlr; exact hlr), fun q _ hown hlq => ?_⟩
      have hreg' : l ∈ yi.footprint := by simpa [S3.afp, hyi] using hreg l hlr
      have huq := usable_of_covered hinv.nd hyi yia hreg' hlq
      obtain ⟨j, z, hz, za, hzh⟩ := ownedIn_holds hwf hrl hleaf hown huq
      have := hnoh j (List.mem_range.2 (lt_of_getElem? hz))
      rw [hz] at this; exact this za hzh
    · rw [← effAnchorOK_store (p := dst) hy₀ hne]
      have h1 := harr.1
      rw [issueEffR_eq] at h1
      have hP : (storeEff (s.addAuth (blockOf s ar region)) s.A.length dst).P =
          (s.addAuth (blockOf s ar region)).P := by rw [storeEff_eq hy₀]
      rwa [S3.pframe_congr hP] at h1
    · intro j hj
      by_cases hjl : j < s.A.length
      · rw [addAuth_lt hjl]
        exact hnoh j (List.mem_range.2 hjl)
      · have : j = s.A.length := by
          have := List.mem_range.1 hj; simp [S3.addAuth] at this; omega
        subst this; rw [hy₀]; simp [OptP, blockOf]
    · exact hg2
    · have h2 := harr.2; rw [issueEffR_eq] at h2; exact h2

/-- Direction sequence → `issue` (brief, question 1): an `ok` of `split` of `internal` on the
region, then of `store` of the block into the destination, on an available region whose destination
is not `Init`, is the `ok` of the restricted `issue`, with the same arrival state. The hypothesis on
`Init` is clause 2 of `issue` (§77.2), which `store` does not check (O8.2): `ce_init` shows it is
needed. The availability is the metadata of the arena: when it fails, `issue` fails (§77.4). -/
theorem seq_to_issue {s₁ s₂ : S3} (hsp : SplitStep k ar.internal [region] s (.ok s₁))
    (hst : StoreStep s.A.length dst s₁ (.ok s₂)) (hav : Avail ar region)
    (hni : ∀ l ∈ footprint s.P dst, s.I l ≠ .init) :
    s₁ = s.addAuth (blockOf s ar region) ∧
      IssueR ar region dst s (.ok s₂ (issueEffR s ar region dst).2) := by
  obtain ⟨-, -, -, hais⟩ := reachable_invariants hdd hr
  obtain ⟨⟨hact, hex, hright, hreg, -, -⟩, rfl⟩ := Guarded.ok_iff.1 hsp
  obtain ⟨⟨-, hu₁, hrd₁, hcov, -, hleaf, hnoh₁, -, haoh⟩, rfl⟩ := Guarded.ok_iff.1 hst
  rw [splitEff_one] at hu₁ hrd₁ hcov hleaf hnoh₁ haoh ⊢
  refine ⟨rfl, ?_⟩
  have hy₀ : (s.addAuth (blockOf s ar region)).A[s.A.length]? = some (blockOf s ar region) :=
    addAuth_self _ _
  have hud : s.Usable dst :=
    (S3.Usable.congr (s := s) (s' := s.addAuth (blockOf s ar region)) rfl rfl rfl).1 hu₁
  have hfd : ∀ l, l ∈ footprint s.P dst ↔ l = dst := fun l => mem_footprint_leaf hleaf hud.lt
  have hnot : dst ∉ region := by
    intro hd
    have := (hcov dst (by simp only [S3.afp, hy₀]; exact hd)).1
    exact this ((hfd dst).2 rfl)
  have hright' : IssueRight s ar region := fun l hl => hright region (List.mem_singleton_self _) l hl
  have hai := hais ar har hact
  have harr' := issueEffR_eq s ar region dst
  have hstat : IssueStaticR s ar region dst := by
    refine ⟨(metaRightM_iff hai hact).2 hex, hact,
      fun l hl => (hreg region (List.mem_singleton_self _) l hl).1, hud, ?_, hni, hleaf, ?_, hnot⟩
    · exact hasRight_addAuth_back hex (fun l hl => hright' l hl)
        (fun l hl hlr => hnot (by rw [(hfd l).1 hl] at hlr; exact hlr)) hrd₁
    · intro j hj
      have hjl := List.mem_range.1 hj
      have := hnoh₁ j (List.mem_range.2 (by simp only [S3.addAuth, List.length_append]; omega))
      rwa [addAuth_lt hjl] at this
  have harr : ArrivalR s ar region dst := by
    refine ⟨?_, by rw [harr']; exact haoh⟩
    rw [harr']
    have hP : (storeEff (s.addAuth (blockOf s ar region)) s.A.length dst).P = s.P := by
      rw [storeEff_eq hy₀]; rfl
    refine haoh dst ((S3.Usable.congr hP (by rw [storeEff_eq hy₀]; rfl)
      (by rw [storeEff_eq hy₀]; rfl)).2 hud) s.A.length { blockOf s ar region with holder := .place dst }
      (by rw [storeEff_eq hy₀]; exact List.getElem?_set_self (by simp [S3.addAuth])) rfl rfl
  have hok := IssueR.ok hstat hav hright' harr
  rwa [harr'] at hok

/-- `issue_as_kernel` for a region (brief, question 1), in reached states: the restricted `issue`
is `ok` with a destination still exercisable at `Modify` iff the region is available, the
destination is not `Init`, and `split` of `internal` on the region then `store` of the block into
the destination are `ok`; the arrival state of the kernel part is the same, and the metadata is that
of the restricted `issue`. `fail` is `issueR_fail_iff`, `reject` is `issueR_reject_iff`. -/
theorem issue_as_kernel_split {s' : S3} {ar' : Arena} :
    (IssueR ar region dst s (.ok s' ar') ∧ HasRight s' .modify dst) ↔
      Avail ar region ∧ (∀ l ∈ footprint s.P dst, s.I l ≠ .init) ∧
      SplitStep k ar.internal [region] s (.ok (s.addAuth (blockOf s ar region))) ∧
      StoreStep s.A.length dst (s.addAuth (blockOf s ar region)) (.ok s') ∧
      ar' = (issueEffR s ar region dst).2 := by
  constructor
  · rintro ⟨h, hg2⟩
    obtain ⟨hsp, hst⟩ := issue_to_seq hdd hr har h hg2
    obtain ⟨hstat, hav, -, -, he⟩ := issueR_ok_iff.1 h
    exact ⟨hav, hstat.2.2.2.2.2.1, hsp, hst, congrArg Prod.snd he⟩
  · rintro ⟨hav, hni, hsp, hst, rfl⟩
    obtain ⟨-, h⟩ := seq_to_issue hdd hr har hsp hst hav hni
    exact ⟨h, (Guarded.ok_iff.1 hst).1.2.2.2.2.2.2.2.1 |> fun h' => by
      rw [(Guarded.ok_iff.1 hst).2]; exact h'⟩

omit har in
/-- On a place `q` with a leaf, `derive` of `internal` at `Modify` (O1) is `split` of `internal` on
the footprint of `q` (O2, one region), with the same effect: the usability of `q` asked by
`derive` follows from `NoDangling`, `internal` being active and covering the footprint. -/
theorem derive_iff_split {q : Nat} (hq : q < s.P.length) {s₁ : S3} :
    DeriveStep ar.internal q .modify s (.ok s₁) ↔
      SplitStep k ar.internal [footprint s.P q] s (.ok s₁) := by
  obtain ⟨hwf, hinv, -, -⟩ := reachable_invariants hdd hr
  constructor
  · intro h
    obtain ⟨⟨hact, hex, -, hsub, hal⟩, rfl⟩ := Guarded.ok_iff.1 h
    have hm : ∀ p ∈ footprint s.P q, effective s ar.internal p = some .modify :=
      fun p hp => allows_modify_iff.1 (hal p hp)
    refine .ok ⟨hact, hex, ?_, ?_, List.pairwise_singleton _ _, ?_⟩
    · intro r hr' p hp; rw [List.mem_singleton.1 hr'] at hp; exact hm p hp
    · intro r hr' p hp; rw [List.mem_singleton.1 hr'] at hp
      exact ⟨hsub p hp, by rw [hm p hp]; simp⟩
    · intro r hr' p hp j _ hd
      rw [List.mem_singleton.1 hr'] at hp
      unfold DistribExcl at hd
      cases hj : s.A[j]? with
      | none => rw [hj] at hd; exact hd
      | some y =>
        rw [hj] at hd; obtain ⟨ya, hanc, hpy, hmy⟩ := hd
        exact effective_ne_modify_of_desc hj ya hpy hanc hmy (hm p hp)
  · intro h
    obtain ⟨⟨hact, hex, hright, hreg, -, -⟩, rfl⟩ := Guarded.ok_iff.1 h
    obtain ⟨l, hl⟩ := exists_mem_footprint hwf (s.P.length - q + 1) q (by omega) hq
    obtain ⟨yi, hyi, yia⟩ := hact
    have hli : l ∈ yi.footprint := by
      have := (hreg _ (List.mem_singleton_self _) l hl).1; simpa [S3.afp, hyi] using this
    refine .ok ⟨⟨yi, hyi, yia⟩, hex, usable_of_covered hinv.nd hyi yia hli hl,
      fun p hp => (hreg _ (List.mem_singleton_self _) p hp).1,
      fun p hp => by rw [hright _ (List.mem_singleton_self _) p hp]; exact allows_some_modify _⟩

/-- `issue_as_kernel` (brief, question 1), with `derive` (O1) of `internal` at `Modify` on a place
`q`, the region being the footprint of `q`. Same statement as `issue_as_kernel_split`. A region that
is not the footprint of a place, the empty region included (`exists_mem_footprint`), is out of reach
of the kernel `derive`, which takes a place; `split` on one region covers it. -/
theorem issue_as_kernel {q : Nat} (hq : q < s.P.length) {s' : S3} {ar' : Arena} :
    (IssueR ar (footprint s.P q) dst s (.ok s' ar') ∧ HasRight s' .modify dst) ↔
      Avail ar (footprint s.P q) ∧ (∀ l ∈ footprint s.P dst, s.I l ≠ .init) ∧
      DeriveStep ar.internal q .modify s (.ok (deriveEff s ar.internal q .modify)) ∧
      StoreStep s.A.length dst (deriveEff s ar.internal q .modify) (.ok s') ∧
      ar' = (issueEffR s ar (footprint s.P q) dst).2 := by
  rw [issue_as_kernel_split hdd hr har, derive_iff_split hdd hr hq, deriveEff_eq]

end IssueAsKernel

/-! ## Restricted `reset` (candidate Spec 1 §78) -/

/-- Preconditions of the restricted `reset` (candidate Spec 1 §78, with `MetaRightM`), as the
clauses of the kernel `ResetPre`: 1 restricted metadata right (§78.1); 2 no active authority
derived from `internal` (§78.2); 3 no usable place with an anchor in the subtree of origins of
`internal`, `internal` itself included, as the kernel reads §78.3. Transitive dependencies through
contained values are covered since every usable part is a usable place. -/
def ResetPreR (s : S3) (ar : Arena) : Prop :=
  MetaRightM s ar ∧
  (∀ j ∈ List.range s.A.length, ar.internal ∈ s.ancs j → ¬ s.Active j) ∧
  (∀ q ∈ List.range s.P.length, s.Usable q → ∀ x ∈ s.D q, x ≠ ar.internal ∧ ar.internal ∉ s.ancs x)

instance (s : S3) (ar : Arena) : Decidable (ResetPreR s ar) := by
  unfold ResetPreR; infer_instance

/-- The restricted `reset` is the kernel `ResetPre` with the restricted right. -/
theorem resetPreR_iff {k : K} {via : Nat} {s : S3} {ar : Arena} :
    ResetPreR s ar ↔ MetaRightM s ar ∧ ResetPre k s ar via :=
  ⟨fun ⟨h0, h1, h2⟩ => ⟨h0, .inl h0, h1, h2⟩, fun ⟨h0, ⟨_, h1, h2⟩⟩ => ⟨h0, h1, h2⟩⟩

/-- The footprint of an authority derived, transitively, from `a` lies in the footprint of `a`
(I2, §42: "La création de droits dérivés n'accroît ni la portée"). -/
theorem afp_of_ancs {s : S3} (hwf : WF3 s) (h2 : I2 s) {a : Nat} :
    ∀ n j, j < n → a ∈ s.ancs j → ∀ l ∈ s.afp j, l ∈ s.afp a
  | 0, _, h, _, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, j, hj, ha, l, hl => by
    cases hy : s.A[j]? with
    | none => simp [S3.afp, hy] at hl
    | some y =>
      have hly : l ∈ y.footprint := by simpa [S3.afp, hy] using hl
      cases ho : y.origin with
      | none =>
        have : s.org j = none := by simp [S3.org, hy, ho]
        rw [S3.ancs, chain_none this] at ha; simp at ha
      | some o =>
        have hoj := hwf.origin j y o hy ho
        obtain ⟨x, hx, hfx⟩ := h2 j y o hy ho
        have hlo : l ∈ s.afp o := by simp only [S3.afp, hx]; exact (hfx l hly).1
        have horg : s.org j = some o := by simp [S3.org, hy, ho]
        rw [S3.ancs, chain_cons horg hoj] at ha
        rcases List.mem_cons.1 ha with rfl | ha
        · exact hlo
        · exact afp_of_ancs hwf h2 n o (by omega) ha l hlo

/-- The release of the authority derived on the whole storage leaves the kernel state unchanged
but for that authority, present and inactive: the arrival state of the sequence, against the kernel
state unchanged by `reset` (`resetEff`). -/
theorem reset_seq_arrival (s : S3) (ar : Arena) :
    releaseEff (deriveEff s ar.internal ar.storage .modify) s.A.length =
      { s with A := s.A ++ [{ blockOf s ar (footprint s.P ar.storage) with active := false }] } := by
  rw [deriveEff_eq]
  unfold releaseEff
  rw [addAuth_self]
  simp [S3.addAuth, blockOf, List.set_append_right]

section ResetAsKernel

variable {k : K} (hdd : DDSound k) {statics : Statics} {s : S3} (hr : Reachable k statics s)
  {ar : Arena} (har : ar ∈ s.arenas) (hact : s.Active ar.internal)
include hdd hr har hact

/-- Direction `reset` → sequence (brief, question 1): the restricted `reset` of a live arena gives
the `ok` of `derive` of `internal` at `Modify` on the storage (O1), then of `release` of the derived
authority (O3). -/
theorem reset_to_seq (h : ResetPreR s ar) :
    DeriveStep ar.internal ar.storage .modify s (.ok (deriveEff s ar.internal ar.storage .modify)) ∧
      ReleaseStep s.A.length (deriveEff s ar.internal ar.storage .modify)
        (.ok (releaseEff (deriveEff s ar.internal ar.storage .modify) s.A.length)) := by
  obtain ⟨-, hinv, -, hais⟩ := reachable_invariants hdd hr
  have hai := hais ar har hact
  obtain ⟨hm, h2, -⟩ := h
  obtain ⟨yi, hyi, yia⟩ := hact
  refine ⟨.ok ⟨⟨yi, hyi, yia⟩, (metaRightM_iff hai ⟨yi, hyi, yia⟩).1 hm,
    live_arena_storage_usable hdd hr ar har ⟨yi, hyi, yia⟩, fun l hl => (hai.2.2.2.2.2.2.2 l).2 hl,
    fun l hl => ?_⟩, .ok ?_⟩
  · have hli : l ∈ yi.footprint := by
      have := (hai.2.2.2.2.2.2.2 l).2 hl; simpa [S3.afp, hyi] using this
    have hd : descModes s ar.internal l = [] := by
      apply nil_of_forall_not_mem; intro e he
      obtain ⟨j, y, hy, ya, -, hj, -⟩ := mem_descModes.1 he
      exact h2 j (List.mem_range.2 (lt_of_getElem? hy)) hj ⟨y, hy, ya⟩
    obtain ⟨-, -, -, -, -, -, ⟨y', v, hy', hmy, -⟩, -⟩ := hai
    rw [hyi] at hy'; cases hy'
    unfold effective; rw [hyi]; simp [yia, hli, hd, effOf, hmy, Allows, OptP, Mode.le]
  · have hy₀ := addAuth_self s (blockOf s ar (footprint s.P ar.storage))
    rw [deriveEff_eq]
    refine ⟨⟨_, hy₀, rfl⟩, fun j hj hn => ?_, fun q _ hq hx => ?_, ?_⟩
    · have := chain_lt hn
      have := List.mem_range.1 hj; simp [S3.addAuth] at this; omega
    · have hq' : s.Usable q := (S3.Usable.congr (s := s)
        (s' := s.addAuth (blockOf s ar (footprint s.P ar.storage))) rfl rfl rfl).1 hq
      obtain ⟨z, hz, -⟩ := hinv.base.2.2.1 q hq' _ hx
      have := lt_of_getElem? hz; omega
    · rw [hy₀]; exact ⟨by simp [blockOf], rfl⟩

/-- Direction sequence → `reset` (brief, question 1): the `ok` of `derive` of `internal` on the
storage, then of `release` of the derived authority, gives the restricted `reset`, provided that no
active authority derived from `internal` has an empty footprint and that no usable place has
`internal` itself as anchor. Clause 2 of `reset` (§78.2) comes from clause 2 of `derive` (O1.2,
effective `Modify` on the whole storage) for derivations that cover a leaf; clause 3 (§78.3) comes
from clause 2 and I3 for strict derivations, not from the preconditions of `release`, which, for a
fresh authority, check nothing on other anchors (O3.3). `ce_reset_empty` and `ce_reset_anchor` show
that both hypotheses are needed. -/
theorem seq_to_reset {s₁ s₂ : S3} (hd : DeriveStep ar.internal ar.storage .modify s (.ok s₁))
    (_hrl : ReleaseStep s.A.length s₁ (.ok s₂))
    (hemp : ∀ j ∈ List.range s.A.length, ar.internal ∈ s.ancs j → s.Active j → s.afp j ≠ [])
    (hanc : ∀ q, s.Usable q → ar.internal ∉ s.D q) : ResetPreR s ar := by
  obtain ⟨hwf, hinv, -, hais⟩ := reachable_invariants hdd hr
  have hai := hais ar har hact
  obtain ⟨⟨-, hex, -, -, hal⟩, -⟩ := Guarded.ok_iff.1 hd
  have h2 : ∀ j ∈ List.range s.A.length, ar.internal ∈ s.ancs j → ¬ s.Active j := by
    intro j hj ha hja
    obtain ⟨l, hl⟩ := List.exists_mem_of_ne_nil _ (hemp j hj ha hja)
    have hli := afp_of_ancs hwf hinv.base.2.1 (j + 1) j (Nat.lt_succ_self j) ha l hl
    have hls : l ∈ footprint s.P ar.storage := (hai.2.2.2.2.2.2.2 l).1 hli
    obtain ⟨y, hy, ya⟩ := hja
    have hly : l ∈ y.footprint := by simpa [S3.afp, hy] using hl
    have he := allows_modify_iff.1 (hal l hls)
    obtain ⟨x, -, -, -, hx⟩ := effective_some he
    have hmem : y.mode ∈ descModes s ar.internal l := mem_descModes.2 ⟨j, y, hy, ya, hly, ha, rfl⟩
    rcases effOf_cases hx with ⟨h0, -⟩ | ⟨-, -, h1⟩
    · rw [h0] at hmem; simp at hmem
    · cases h1
  refine ⟨(metaRightM_iff hai hact).2 hex, h2, fun q _ hq x hx => ⟨fun he => hanc q hq (he ▸ hx),
    fun hxa => ?_⟩⟩
  obtain ⟨z, hz, za⟩ := hinv.base.2.2.1 q hq x hx
  exact h2 x (List.mem_range.2 (lt_of_getElem? hz)) hxa ⟨z, hz, za⟩

/-- `reset_as_kernel` (brief, question 1), in reached states, for a live arena: the restricted
`reset` holds iff `derive` of `internal` at `Modify` on the storage then `release` of the derived
authority are `ok`, no active authority derived from `internal` has an empty footprint, and no
usable place has `internal` as anchor. The kernel part of the arrival states differs by the released
authority alone (`reset_seq_arrival`). -/
theorem reset_as_kernel :
    ResetPreR s ar ↔
      DeriveStep ar.internal ar.storage .modify s (.ok (deriveEff s ar.internal ar.storage .modify)) ∧
      ReleaseStep s.A.length (deriveEff s ar.internal ar.storage .modify)
        (.ok (releaseEff (deriveEff s ar.internal ar.storage .modify) s.A.length)) ∧
      (∀ j ∈ List.range s.A.length, ar.internal ∈ s.ancs j → s.Active j → s.afp j ≠ []) ∧
      (∀ q, s.Usable q → ar.internal ∉ s.D q) := by
  constructor
  · intro h
    obtain ⟨hd, hrl⟩ := reset_to_seq hdd hr har hact h
    exact ⟨hd, hrl, fun j hj ha hja => absurd hja (h.2.1 j hj ha), fun q hq hx =>
      (h.2.2 q (List.mem_range.2 hq.lt) hq _ hx).1 rfl⟩
  · rintro ⟨hd, hrl, hemp, hanc⟩
    exact seq_to_reset hdd hr har hact hd hrl hemp hanc

omit har hact in
/-- Under the strict reading of §78.3 (the subtree of origins of `internal` without `internal`),
the clause follows from §78.2 and I3 in reached states. -/
theorem reset_clause3_strict (h2 : ∀ j ∈ List.range s.A.length, ar.internal ∈ s.ancs j → ¬ s.Active j) :
    ∀ q, s.Usable q → ∀ x ∈ s.D q, ar.internal ∉ s.ancs x := by
  obtain ⟨-, hinv, -, -⟩ := reachable_invariants hdd hr
  intro q hq x hx hxa
  obtain ⟨z, hz, za⟩ := hinv.base.2.2.1 q hq x hx
  exact h2 x (List.mem_range.2 (lt_of_getElem? hz)) hxa ⟨z, hz, za⟩

end ResetAsKernel

/-! ## `newArena` as a library operation (O17, §56) -/

/-- `newArena` changes no component of the kernel (O17, effect: "Aucun emplacement, droit d'accès
ou état `Init` n'est fabriqué par l'inscription"): it only appends a registry entry. -/
theorem newArena_kernel_noop (s : S3) (st i : Nat) :
    newArenaEff s st i = { s with arenas := s.arenas ++ [⟨st, i, s.afp i, []⟩] } := rfl

/-- The preconditions of `newArena` without the guard of §56 (O17.4): every other clause of the
kernel `NewArenaPre`. -/
def NewArenaPreNG (s : S3) (storage internal : Nat) : Prop :=
  HasRight s .modify storage ∧ s.Usable storage ∧
    OptP (s.A[internal]?) (fun y => y.active = true ∧ y.mode = .modify ∧ y.holder.isPlace = true)
      False ∧
    s.ExercisableAt internal .modify ∧
    (∀ l ∈ s.afp internal, l ∈ footprint s.P storage) ∧
    (∀ l ∈ footprint s.P storage, l ∈ s.afp internal) ∧
    OptP (s.A[internal]?) (fun y => LeavesInit s y.holder) True

instance (s : S3) (storage internal : Nat) : Decidable (NewArenaPreNG s storage internal) := by
  unfold NewArenaPreNG; infer_instance

/-- The kernel `NewArenaPre` is `NewArenaPreNG` and the guard of §56 on the arena registry. -/
theorem newArenaPre_iff {s : S3} {st i : Nat} : NewArenaPre s st i ↔
    NewArenaPreNG s st i ∧ ∀ ar ∈ s.arenas, s.Active ar.internal → ar.internal ≠ i :=
  ⟨fun ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ => ⟨⟨h0, h1, h2, h3, h4, h5, h7⟩, h6⟩,
    fun ⟨⟨h0, h1, h2, h3, h4, h5, h7⟩, h6⟩ => ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩⟩

/-- The invariants of §57 and the auxiliary `RootLive`: `WF3`, `Inv3`, `ArenasWF`, `ArenasInv`,
`AnchorOrderHeld` and `RootLive` (which gives `NoOrphan`, `noOrphan_of_rootLive`). -/
def Inv57 (s : S3) : Prop :=
  WF3 s ∧ Inv3 s ∧ ArenasWF s ∧ ArenasInv s ∧ AnchorOrderHeld s ∧ RootLive s

/-- Every step of `Reachable` preserves `Inv57` (MM-03.3 §10): the case analysis of
`reachable_invariants`, `reachable_anchorOrderHeld` and `reachable_rootLive`, on a state that
satisfies the invariants rather than a reached one. -/
theorem step_inv57 {k : K} (hdd : DDSound k) {s s' : S3} (ih : Inv57 s) (h : Step k s s') :
    Inv57 s' := by
  obtain ⟨hwf, hinv, haw, hai, hao, hrl⟩ := ih
  have i4 : WF3 s ∧ Inv3 s ∧ ArenasWF s ∧ ArenasInv s := ⟨hwf, hinv, haw, hai⟩
  have mk : ∀ {s' : S3}, KStep k s s' → WF3 s' ∧ Inv3base s' → AnchorOrder s' → NoDangling s' →
      WF3 s' ∧ Inv3 s' ∧ ArenasWF s' ∧ ArenasInv s' :=
    fun hk h a d => ⟨h.1, ⟨h.2, a, d⟩, kstep_preserves_arenas hwf hinv.base haw hai hk⟩
  cases h with
  | kernel hk =>
    cases hk with
    | derive hs =>
      obtain ⟨a, b, c, d⟩ := mk (.derive hs) (derive_preserves hwf hinv.base hs)
        (derive_preserves_anchorOrder hinv.ao hs) (derive_preserves_noDangling hinv.nd hs)
      refine ⟨a, b, c, d, derive_preserves_anchorOrderHeld hao hs, ?_⟩
      obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact hrl.of_append rfl rfl rfl _ rfl
    | split hs =>
      obtain ⟨a, b, c, d⟩ := mk (.split hs) (split_preserves_underDD hdd hwf hinv.base hs)
        (split_preserves_anchorOrder hinv.ao hs) (split_preserves_noDangling hinv.nd hs)
      refine ⟨a, b, c, d, split_preserves_anchorOrderHeld hao hs, ?_⟩
      obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact hrl.of_append rfl rfl rfl _ rfl
    | release hs =>
      obtain ⟨a, b, c, d⟩ := mk (.release hs) (release_preserves hwf hinv.base hs)
        (release_preserves_anchorOrder hinv.ao hs) (release_preserves_noDangling hinv.nd hs)
      exact ⟨a, b, c, d, release_preserves_anchorOrderHeld hao hs, release_rootLive hrl hs⟩
    | transfer hs =>
      obtain ⟨a, b, c, d⟩ := mk (.transfer hs) (transfer_preserves hwf hinv.base hs)
        (transfer_preserves_anchorOrder hwf hinv.ao hs) (transfer_preserves_noDangling hwf hinv.nd hs)
      obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 hs
      exact ⟨a, b, c, d, hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.1, transfer_rootLive hwf hpre.1 hrl⟩
    | depend hs =>
      obtain ⟨a, b, c, d⟩ := mk (.depend hs) (depend_preserves hwf hinv.base hs)
        (depend_preserves_anchorOrder hinv.ao hs) (depend_preserves_noDangling hinv.nd hs)
      obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
      exact ⟨a, b, c, d, sameA_preserves_anchorOrderHeld hao rfl rfl rfl rfl,
        hrl.of_sameA rfl rfl rfl rfl⟩
    | enter hs =>
      obtain ⟨a, b, c, d⟩ := mk (.enter hs) (enter_preserves hwf hinv.base hs)
        (enter_preserves_anchorOrder hwf hinv.ao hs) (enter_preserves_noDangling hwf hinv.nd hs)
      have hrl' := enter_rootLive hwf hrl hs
      obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 hs
      exact ⟨a, b, c, d, hpre.2.2, hrl'⟩
    | exit hs =>
      obtain ⟨a, b, c, d⟩ := mk (.exit hs) (exit_preserves hwf hinv.base hs)
        (exit_preserves_anchorOrder hwf hinv.ao hs) (exit_preserves_noDangling hwf hinv.nd hs)
      have hrl' := exit_rootLive hrl hs
      obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 hs
      refine ⟨a, b, c, d, ?_, hrl'⟩
      unfold ExitPre at hpre; split at hpre
      · exact hpre.2.2.2.2
      · exact hpre.elim
    | read hs =>
      rw [read3_preserves hs]; exact ⟨hwf, hinv, haw, hai, hao, hrl⟩
    | write hs =>
      have hk := KStep.write (k := k) hs
      obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
      obtain ⟨a, b, c, d⟩ := mk hk (write3_preserves hwf hinv.base hs)
        (write3_preserves_anchorOrder _ hinv.ao) (write3_preserves_noDangling _ hinv.nd)
      exact ⟨a, b, c, d, sameA_preserves_anchorOrderHeld hao rfl rfl rfl rfl,
        hrl.of_sameA rfl rfl rfl rfl⟩
    | writeShared hs =>
      have hk := KStep.writeShared hs
      obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
      obtain ⟨a, b, c, d⟩ := mk hk (writeShared_preserves hwf hinv.base hs)
        (write3_preserves_anchorOrder _ hinv.ao) (write3_preserves_noDangling _ hinv.nd)
      exact ⟨a, b, c, d, sameA_preserves_anchorOrderHeld hao rfl rfl rfl rfl,
        hrl.of_sameA rfl rfl rfl rfl⟩
    | pin hs =>
      have hk := KStep.pin (k := k) hs
      obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
      obtain ⟨a, b, c, d⟩ := mk hk (pinEff_preserves hwf hinv.base)
        (pinEff_preserves_anchorOrder _ _ hinv.ao) (pinEff_preserves_noDangling _ _ hinv.nd)
      exact ⟨a, b, c, d, sameA_preserves_anchorOrderHeld hao rfl rfl rfl rfl,
        hrl.of_sameA rfl rfl rfl rfl⟩
    | unpin hs =>
      have hk := KStep.unpin hs
      obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
      obtain ⟨a, b, c, d⟩ := mk hk (pinEff_preserves hwf hinv.base)
        (pinEff_preserves_anchorOrder _ _ hinv.ao) (pinEff_preserves_noDangling _ _ hinv.nd)
      exact ⟨a, b, c, d, sameA_preserves_anchorOrderHeld hao rfl rfl rfl rfl,
        hrl.of_sameA rfl rfl rfl rfl⟩
    | endUse hs =>
      obtain ⟨a, b, c, d⟩ := mk (.endUse hs) (endUse_preserves hwf hinv.base hs)
        (endUse_preserves_anchorOrder hinv.ao hs)
        (endUse_preserves_noDangling hwf hinv.base hinv.nd hs)
      exact ⟨a, b, c, d, endUse_preserves_anchorOrderHeld hao hs, endUse_rootLive hrl hs⟩
    | free hs =>
      obtain ⟨a, b, c, d⟩ := mk (.free hs) (free_preserves hwf hinv.base hs)
        (free_preserves_anchorOrder hinv.ao hs) (free_preserves_noDangling hwf hinv.base hinv.nd hs)
      exact ⟨a, b, c, d, free_preserves_anchorOrderHeld hao hs, free_rootLive hrl hs⟩
    | alloc hs =>
      obtain ⟨a, b, c, d⟩ := mk (.alloc hs) (alloc_preserves hwf hinv.base hs)
        (alloc_preserves_anchorOrder hwf hinv.ao hs) (alloc_preserves_noDangling hwf hinv.nd hs)
      exact ⟨a, b, c, d, alloc_preserves_anchorOrderHeld hwf hao hs, alloc_rootLive hwf hrl hs⟩
    | store hs =>
      obtain ⟨a, b, c, d⟩ := mk (.store hs) (store_preserves hwf hinv.base hs)
        (store_preserves_anchorOrder hwf hinv.ao hs) (store_preserves_noDangling hinv.nd hs)
      have hrl' := store_rootLive hrl hs
      obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 hs
      exact ⟨a, b, c, d, hpre.2.2.2.2.2.2.2.2, hrl'⟩
  | newArena hs =>
    obtain ⟨a, b, c, d⟩ := newArena_preserves hwf hinv haw hai hs
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
    exact ⟨a, b, c, d, sameA_preserves_anchorOrderHeld hao rfl rfl rfl rfl,
      hrl.of_sameA rfl rfl rfl rfl⟩
  | issue hs =>
    obtain ⟨a, b, c, d⟩ := issueAt_preserves hwf hinv haw hai hs
    cases hs with
    | ok _ hst =>
      cases hst with
      | ok _ _ _ h4 =>
        exact ⟨a, b, c, d, sameA_preserves_anchorOrderHeld h4 rfl rfl rfl rfl,
          hrl.of_append rfl rfl rfl _ rfl⟩
  | reset hs =>
    obtain ⟨a, b, c, d⟩ := resetAt_preserves hwf hinv haw hai hs
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
    refine ⟨a, b, c, d, ?_, ?_⟩
    · unfold resetAtEff; split
      · exact sameA_preserves_anchorOrderHeld hao rfl rfl rfl rfl
      · exact hao
    · unfold resetAtEff; split
      · exact hrl.of_sameA rfl rfl rfl rfl
      · exact hrl

/-- `newArena` without the guard of §56 preserves `Inv57`: the proof of `newArena_preserves` does not
use the guard. -/
theorem newArenaNG_inv57 {s : S3} {st i : Nat} (ih : Inv57 s) (h : NewArenaPreNG s st i) :
    Inv57 (newArenaEff s st i) := by
  obtain ⟨hwf, hinv, hw, hai, hao, hrl⟩ := ih
  obtain ⟨-, hu, hint, -, h1, h2, -⟩ := h
  obtain ⟨y, hy⟩ : ∃ y, s.A[i]? = some y := by
    unfold OptP at hint; split at hint
    · exact ⟨_, ‹_›⟩
    · exact hint.elim
  rw [hy] at hint; obtain ⟨-, hm, hpl⟩ := hint
  obtain ⟨v, hv⟩ : ∃ v, y.holder = .place v := by
    cases hh : y.holder with
    | place v => exact ⟨v, rfl⟩
    | frame f => rw [hh] at hpl; cases hpl
  refine ⟨hwf.arenas _, hinv.arenas _, fun ar har => ?_, fun ar har ha => ?_,
    sameA_preserves_anchorOrderHeld hao rfl rfl rfl rfl, hrl.of_sameA rfl rfl rfl rfl⟩
  · rcases List.mem_append.1 har with har | har
    · exact hw ar har
    · rw [List.mem_singleton.1 har]; exact lt_of_getElem? hy
  · rcases List.mem_append.1 har with har | har
    · exact (hai ar har ha).arenas _
    · rw [List.mem_singleton.1 har]
      exact ⟨fun l hl => hl, fun _ he => (by cases he), List.Pairwise.nil, fun _ he => (by cases he),
        fun _ he => (by cases he), hu.lt, ⟨y, v, hy, hm, hv⟩, fun l => ⟨h1 l, h2 l⟩⟩

/-- States reached with `newArena` also allowed without the guard of §56 (O17.4): the steps of
`Reachable` and the unguarded registration. -/
inductive ReachableNG (k : K) (statics : Statics) : S3 → Prop where
  | init : ShapeOK 0 (statics.map (·.1)) → ReachableNG k statics (S3.init statics)
  | step {s s' : S3} : ReachableNG k statics s → Step k s s' → ReachableNG k statics s'
  | newArenaNG {s : S3} {st i : Nat} : ReachableNG k statics s → NewArenaPreNG s st i →
      ReachableNG k statics (newArenaEff s st i)

/-- Every reached state is reached without the guard. -/
theorem reachableNG_of_reachable {k : K} {statics : Statics} {s : S3}
    (h : Reachable k statics s) : ReachableNG k statics s := by
  induction h with
  | init hsh => exact .init hsh
  | derive _ hs ih => exact .step ih (.kernel (.derive hs))
  | split _ hs ih => exact .step ih (.kernel (.split hs))
  | release _ hs ih => exact .step ih (.kernel (.release hs))
  | transfer _ hs ih => exact .step ih (.kernel (.transfer hs))
  | depend _ hs ih => exact .step ih (.kernel (.depend hs))
  | enter _ hs ih => exact .step ih (.kernel (.enter hs))
  | exit _ hs ih => exact .step ih (.kernel (.exit hs))
  | read _ hs ih => exact .step ih (.kernel (.read hs))
  | write _ hs ih => exact .step ih (.kernel (.write hs))
  | writeShared _ hs ih => exact .step ih (.kernel (.writeShared hs))
  | pin _ hs ih => exact .step ih (.kernel (.pin hs))
  | unpin _ hs ih => exact .step ih (.kernel (.unpin hs))
  | endUse _ hs ih => exact .step ih (.kernel (.endUse hs))
  | free _ hs ih => exact .step ih (.kernel (.free hs))
  | alloc _ hs ih => exact .step ih (.kernel (.alloc hs))
  | newArena _ hs ih => exact .step ih (.newArena hs)
  | issue _ hs ih => exact .step ih (.issue hs)
  | reset _ hs ih => exact .step ih (.reset hs)
  | store _ hs ih => exact .step ih (.kernel (.store hs))

/-- `newArena_as_library` (brief, question 1; O17.4, §56): registration is a metadata operation with
no kernel step (`newArena_kernel_noop`), and no safety property of §57 depends on its guard: in
every state reached with the unguarded registration, `WF3`, `Inv3` (I1 to I4, `AnchorOrder`,
`NoDangling`), `AnchorOrderHeld`, `NoOrphan` and `ArenaInv` of every live entry hold. Under
`DDSound k`. -/
theorem newArena_as_library {k : K} (hdd : DDSound k) {statics : Statics} {s : S3}
    (h : ReachableNG k statics s) :
    WF3 s ∧ Inv3 s ∧ AnchorOrderHeld s ∧ NoOrphan s ∧
      ∀ ar ∈ s.arenas, s.Active ar.internal → ArenaInv s ar := by
  have key : Inv57 s := by
    induction h with
    | init hsh =>
      have hr : Reachable k statics (S3.init statics) := .init hsh
      obtain ⟨a, b, c, d⟩ := reachable_invariants hdd hr
      exact ⟨a, b, c, d, reachable_anchorOrderHeld hdd hr, reachable_rootLive hdd hr⟩
    | step _ hs ih => exact step_inv57 hdd ih hs
    | newArenaNG _ hp ih => exact newArenaNG_inv57 ih hp
  obtain ⟨hwf, hinv, -, hai, hao, hrl⟩ := key
  exact ⟨hwf, hinv, hao, noOrphan_of_rootLive hwf hrl, hai⟩

/-- I1 rejects a second emission of a leaf through a second administration of the same `internal`
(brief, question 1): an active `Modify` block derived from `internal` covering a leaf of the region
takes the effective right of `internal` away, so neither the kernel `issue` nor the restricted
`issue` of any entry with this `internal` is `ok`, and `split` of `internal` on the region is
rejected. -/
theorem issue_blocked_by_block {k : K} {s : S3} {ar : Arena} {region : List Nat} {j l : Nat}
    {y : Authority} (hy : s.A[j]? = some y) (ya : y.active = true) (hj : ar.internal ∈ s.ancs j)
    (hm : y.mode = .modify) (hly : l ∈ y.footprint) (hl : l ∈ region) :
    ¬ IssueRight s ar region ∧ ¬ SplitPre k s ar.internal [region] :=
  ⟨fun h => effective_ne_modify_of_desc hy ya hly hj hm (h l hl),
   fun h => effective_ne_modify_of_desc hy ya hly hj hm (h.2.2.1 region (List.mem_singleton_self _) l hl)⟩

/-! ## Counterexamples on reached states

Runs from `S3.init []` with the test contracts `K0` (no `SharedMutable` leaf) or `KA` (leaf 0
`SharedMutable`); every verdict by `decide`. -/

/-- Reachability of a run whose steps are all `ok`, under `K0`. -/
theorem reach_run {os : List Op} (h : (prun K0 (PS.init []) os).isSome = true) :
    Reachable K0 [] (run K0 [] os).s :=
  pReach_reachable (KT_dd _ _ _ _ _) (run_reach (by decide) h)

/-- Common prefix: frame 1 with the leaves 0 (arena value), 1 (storage), 2 and 3 (destinations), of
root authorities 0 to 3; `internal` 4 derived from 1 at `Modify` and stored into 0; `newArena 1 4`. -/
def opsArena : List Op :=
  [.enter [] [lf, lf, lf, lf], .derive 1 1 .modify, .store 4 0, .newArena 1 4]

/-- The entry registered by `opsArena`. -/
def arD : Arena := ⟨1, 4, [1], []⟩

/-- **G2** (brief: "la clause G2 de `store` … n'introduit aucun rejet que `issue` n'a pas"): the
authority 5, derived from the root of the destination 2, is stored into the storage leaf 1, so that
2 is exercisable at `Modify` only through 5, hence through `internal` on 1. The restricted `issue` of
`[1]` into 2 is `ok`, and so is the kernel `issue`; in the arrival state the block on 1, held by 2,
and 5, held by 1, block each other, and 2 is no longer exercisable at `Modify`. `split` is `ok`, and
`store` of the block into 2 is rejected by its clause 5 (O8.5). An indirect cycle, which §88 allows
("des blocages indirects compatibles avec la sûreté peuvent subsister"). -/
def opsG2 : List Op := opsArena ++ [.derive 2 2 .modify, .store 5 1]

theorem ce_g2 :
    Reachable K0 [] (run K0 [] opsG2).s ∧ (run K0 [] opsG2).s.arenas = [arD] ∧
    IssueR arD [1] 2 (run K0 [] opsG2).s
      (.ok (issueEffR (run K0 [] opsG2).s arD [1] 2).1 (issueEffR (run K0 [] opsG2).s arD [1] 2).2) ∧
    IssueAt K0 0 0 [1] 2 (run K0 [] opsG2).s
      (.ok (arenaSet (issueEff (run K0 [] opsG2).s arD [1] 2).1 0
        (issueEff (run K0 [] opsG2).s arD [1] 2).2)) ∧
    ¬ HasRight (issueEffR (run K0 [] opsG2).s arD [1] 2).1 .modify 2 ∧
    SplitStep K0 4 [[1]] (run K0 [] opsG2).s
      (.ok ((run K0 [] opsG2).s.addAuth (blockOf (run K0 [] opsG2).s arD [1]))) ∧
    StoreStep (run K0 [] opsG2).s.A.length 2
      ((run K0 [] opsG2).s.addAuth (blockOf (run K0 [] opsG2).s arD [1])) .reject :=
  ⟨reach_run (by decide), by decide, .ok (by decide) (by decide) (by decide) (by decide),
    .ok (ar := arD) (by decide) (.ok (by decide) (by decide) (by decide) (by decide)), by decide,
    .ok (by decide), .reject (by decide)⟩

/-- **Init** (sequence accepting more than `issue`): the destination 2 is written (`write3`) before
the emission. The restricted `issue` of `[1]` into 2 is rejected by clause 2 (§77.2, "non `Init`");
`split` then `store` of the block into 2 are `ok` (O8.2: "Le fait que ses données soient déjà `Init`
n'interdit pas à lui seul l'opération"). -/
def opsInit : List Op := opsArena ++ [.write 2 [2]]

theorem ce_init :
    Reachable K0 [] (run K0 [] opsInit).s ∧ (run K0 [] opsInit).s.arenas = [arD] ∧
    IssueR arD [1] 2 (run K0 [] opsInit).s .reject ∧
    SplitStep K0 4 [[1]] (run K0 [] opsInit).s
      (.ok ((run K0 [] opsInit).s.addAuth (blockOf (run K0 [] opsInit).s arD [1]))) ∧
    StoreStep (run K0 [] opsInit).s.A.length 2
      ((run K0 [] opsInit).s.addAuth (blockOf (run K0 [] opsInit).s arD [1]))
      (.ok (storeEff ((run K0 [] opsInit).s.addAuth (blockOf (run K0 [] opsInit).s arD [1]))
        (run K0 [] opsInit).s.A.length 2)) :=
  ⟨reach_run (by decide), by decide, .reject (by decide), .ok (by decide), .ok (by decide)⟩

/-- The entry of `opsAvail` once `[1]` is issued (block 5) and the block released. -/
def arDu : Arena := ⟨1, 4, [], [([1], 5)]⟩

/-- **Availability** (the role of the metadata, §77.4): after the emission of `[1]` into 2 and the
release of the block, `internal` has its effective `Modify` on 1 again but the region is still
issued. The restricted `issue` of `[1]` into 3 fails; `split` then `store` into 3 are `ok`. -/
def opsAvail : List Op := opsArena ++ [.issue 0 0 [1] 2, .release 5]

theorem ce_avail :
    Reachable K0 [] (run K0 [] opsAvail).s ∧ (run K0 [] opsAvail).s.arenas = [arDu] ∧
    IssueR arDu [1] 3 (run K0 [] opsAvail).s (.fail (run K0 [] opsAvail).s arDu) ∧
    SplitStep K0 4 [[1]] (run K0 [] opsAvail).s
      (.ok ((run K0 [] opsAvail).s.addAuth (blockOf (run K0 [] opsAvail).s arDu [1]))) ∧
    StoreStep (run K0 [] opsAvail).s.A.length 3
      ((run K0 [] opsAvail).s.addAuth (blockOf (run K0 [] opsAvail).s arDu [1]))
      (.ok (storeEff ((run K0 [] opsAvail).s.addAuth (blockOf (run K0 [] opsAvail).s arDu [1]))
        (run K0 [] opsAvail).s.A.length 3)) :=
  ⟨reach_run (by decide), by decide, .fail (by decide) (by decide), .ok (by decide),
    .ok (by decide)⟩

/-- **Empty region**: the restricted `issue` of the empty region is `ok`; no place has an empty
footprint (`exists_mem_footprint`), so `derive` (O1), which takes a place, cannot produce the block,
while `split` on one region can (`issue_as_kernel_split`). -/
theorem ce_empty_region :
    IssueR arD [] 2 (run K0 [] opsArena).s
      (.ok (issueEffR (run K0 [] opsArena).s arD [] 2).1 (issueEffR (run K0 [] opsArena).s arD [] 2).2) ∧
    ∀ q < (run K0 [] opsArena).s.P.length, footprint (run K0 [] opsArena).s.P q ≠ [] := by
  refine ⟨.ok (by decide) (by decide) (by decide) (by decide), fun q hq he => ?_⟩
  have hw := (reachable_invariants (KT_dd _ _ _ _ _) (reach_run (os := opsArena) (by decide))).1
  obtain ⟨l, hl⟩ := exists_mem_footprint hw ((run K0 [] opsArena).s.P.length - q + 1) q (by omega) hq
  rw [he] at hl; simp at hl

/-- **`internal` stored into the arena value** (`reset`): `internal` 4 was placed into the arena
value 0 by `store` (O8), which adds it to `D 0`. The restricted `reset` and the kernel `reset` are
rejected by their clause 3 (§78.3, the kernel reading `internal` within its subtree of origins) for
as long as 0 is usable; `derive` of `internal` on the storage then `release` are `ok`. -/
theorem ce_reset_anchor :
    Reachable K0 [] (run K0 [] opsArena).s ∧ (run K0 [] opsArena).s.arenas = [arD] ∧
    4 ∈ (run K0 [] opsArena).s.D 0 ∧
    ¬ ResetPreR (run K0 [] opsArena).s arD ∧ ResetAtStep K0 0 0 (run K0 [] opsArena).s .reject ∧
    DeriveStep 4 1 .modify (run K0 [] opsArena).s
      (.ok (deriveEff (run K0 [] opsArena).s 4 1 .modify)) ∧
    ReleaseStep (run K0 [] opsArena).s.A.length (deriveEff (run K0 [] opsArena).s 4 1 .modify)
      (.ok (releaseEff (deriveEff (run K0 [] opsArena).s 4 1 .modify) (run K0 [] opsArena).s.A.length)) :=
  ⟨reach_run (by decide), by decide, by decide, by decide, .reject (by decide), .ok (by decide),
    .ok (by decide)⟩

/-- An arena value that holds `internal` through `store` blocks the restricted `reset` while it is
usable. -/
theorem reset_blocked_by_stored_internal {s : S3} {ar : Arena} {v : Nat} (hv : s.Usable v)
    (hx : ar.internal ∈ s.D v) : ¬ ResetPreR s ar :=
  fun h => (h.2.2 v (List.mem_range.2 hv.lt) hv _ hx).1 rfl

/-- Prefix with an allocated storage: frame 1 with the leaves 0 (arena value), 1 (allocator
value), 2 and 3 (destinations); `alloc` of the storage 4, of parts 5 and 6, owned by 0, of root
authority 4 held by 0; `newArena 4 4`. `internal` is a root, in no `D`. -/
def opsAlloc : List Op :=
  [.enter [] [lf, lf, lf, lf], .write 1 [1],
    .alloc 1 0 [(none, none, 0), (some 4, none, 0), (some 4, none, 0)], .write 0 [0], .newArena 4 4]

/-- The entry registered by `opsAlloc`. -/
def arL : Arena := ⟨4, 4, [5, 6], []⟩

/-- **Empty derivation** (`reset`): `split` of `internal` on the empty region creates an active
derivation of empty footprint. The restricted `reset` and the kernel `reset` are rejected by their
clause 2 (§78.2); `derive` of `internal` on the storage then `release` are `ok`. -/
def opsEmpty : List Op := opsAlloc ++ [.split 4 [[]]]

theorem ce_reset_empty :
    Reachable K0 [] (run K0 [] opsEmpty).s ∧ (run K0 [] opsEmpty).s.arenas = [arL] ∧
    ¬ ResetPreR (run K0 [] opsEmpty).s arL ∧ ResetAtStep K0 0 0 (run K0 [] opsEmpty).s .reject ∧
    DeriveStep 4 4 .modify (run K0 [] opsEmpty).s
      (.ok (deriveEff (run K0 [] opsEmpty).s 4 4 .modify)) ∧
    ReleaseStep (run K0 [] opsEmpty).s.A.length (deriveEff (run K0 [] opsEmpty).s 4 4 .modify)
      (.ok (releaseEff (deriveEff (run K0 [] opsEmpty).s 4 4 .modify) (run K0 [] opsEmpty).s.A.length)) :=
  ⟨reach_run (by decide), by decide, by decide, .reject (by decide), .ok (by decide),
    .ok (by decide)⟩

/-- Without such a derivation, the same arena is reset by both: the restricted `reset` holds. -/
theorem reset_alloc_ok : ResetPreR (run K0 [] opsAlloc).s arL := by decide

/-- The state `a6` of case 16 (`Ern.MM03`) is reached. -/
theorem a6_reachable : Reachable KA [] a6 := by
  have r0 : Reachable KA [] a0 := .enter (.init (by decide)) (.ok (by decide))
  have r1 : Reachable KA [] a1 := .write r0 (show Write3Step 1 [1] a0 (.ok a1) from .ok (by decide))
  have r2 : Reachable KA [] a2 := .alloc r1
    (show AllocStep KA 1 0 [(none, none, 0), (some 3, none, 0), (some 3, none, 0)] a1 (.ok a2) from
      .ok (by decide) trivial)
  have r3 : Reachable KA [] a3 := .newArena (.write r2 (show Write3Step 0 [0] a2 (.ok a2w) from
    .ok (by decide))) (show NewArenaStep 3 3 a2w (.ok a3) from .ok (by decide))
  have r4 : Reachable KA [] (deriveEff a3 0 0 .observe) :=
    .derive r3 (show DeriveStep 0 0 .observe a3 (.ok _) from .ok (by decide))
  have r5 : Reachable KA [] (deriveEff (deriveEff a3 0 0 .observe) 2 2 .modify) :=
    .derive r4 (show DeriveStep 2 2 .modify (deriveEff a3 0 0 .observe) (.ok _) from .ok (by decide))
  exact .enter r5 (show EnterStep [4, 5] [(none, none, 0)] _ (.ok a6) from .ok (by decide))

/-- **`writeShared` branch** (brief, question 1, counterexample to keep): in `a6`, case 16 of the
kernel, the callee frame has only the `Observe` authority 4 on the arena value 0, whose leaf is
`SharedMutable` under `KA`, and no block is issued. The kernel `issue` of `[4]` into 6 and the kernel
`reset` are `ok` through the `writeShared` branch of `MetaRight`; `internal` 3 is exercisable at no
`Modify` (`MetaRightM` fails), so `derive` of `internal` on the region (place 4) or on the storage
(place 3), and `split` on the region, are rejected; the restricted operations are rejected too. -/
theorem ce_writeShared :
    Reachable KA [] a6 ∧ a6.arenas = [ar7] ∧ ar7.issued = [] ∧
    IssueAt KA 0 4 [4] 6 a6 (.ok a7) ∧ ResetAtStep KA 0 4 a6 (.ok (resetAtEff a6 0)) ∧
    ¬ MetaRightM a6 ar7 ∧
    DeriveStep 3 4 .modify a6 .reject ∧ SplitStep KA 3 [[4]] a6 .reject ∧
    DeriveStep 3 3 .modify a6 .reject ∧
    IssueR ar7 [4] 6 a6 .reject ∧ ¬ ResetPreR a6 ar7 :=
  ⟨a6_reachable, by decide, rfl,
    .ok (ar := ar7) (by decide) (.ok (by decide) (by decide) (by decide) (by decide)),
    .ok (by decide), by decide, .reject (by decide), .reject (by decide), .reject (by decide),
    .reject (by decide), by decide⟩

/-- **Two administrations** (`newArena_as_library`): the unguarded registration of `internal` 4 a
second time (`NewArenaPreNG` holds, the kernel guard rejects); the emission of `[5]` through entry 0
is `ok`; the emission of `[5]` through entry 1, whose metadata still has 5 available, is rejected by
the effective right (§77.5), as is `split` of `internal` on `[5]`: the kernel (I1) rejects the double
emission, and the metadata of entry 1 no longer separates `fail` from `reject`. -/
def sTwo : S3 := newArenaEff (run K0 [] opsAlloc).s 4 4

def sTwoIssued : S3 := arenaSet (issueEff sTwo arL [5] 2).1 0 (issueEff sTwo arL [5] 2).2

theorem ce_two_admins :
    NewArenaPreNG (run K0 [] opsAlloc).s 4 4 ∧ NewArenaStep 4 4 (run K0 [] opsAlloc).s .reject ∧
    ReachableNG K0 [] sTwoIssued ∧ sTwoIssued.arenas.map (·.available) = [[6], [5, 6]] ∧
    IssueAt K0 1 0 [5] 3 sTwoIssued .reject ∧ IssueStatic K0 sTwoIssued arL 0 [5] 3 ∧
    Avail arL [5] ∧ SplitStep K0 4 [[5]] sTwoIssued .reject := by
  have h1 : NewArenaPreNG (run K0 [] opsAlloc).s 4 4 := by decide
  have hr : ReachableNG K0 [] sTwo :=
    .newArenaNG (reachableNG_of_reachable (reach_run (by decide))) h1
  refine ⟨h1, .reject (by decide), .step hr (.issue (via := 0) (.ok (ar := arL) (by decide)
    (.ok (by decide) (by decide) (by decide) (by decide)))), by decide,
    .reject (ar := arL) (by decide) (.noRight (by decide) (by decide) (by decide)), by decide,
    by decide, .reject (by decide)⟩

/-- **Inexact metadata with the guard**: in a reached state, a frame that can exercise `internal`
derives from it directly (`derive` of 4 on 5 at `Observe`); the region `[5]` is available in the
metadata and its emission is rejected by the effective right. The guard does not make the metadata
exact either. -/
def opsObs : List Op := opsAlloc ++ [.derive 4 5 .observe]

theorem ce_avail_reject :
    Reachable K0 [] (run K0 [] opsObs).s ∧ (run K0 [] opsObs).s.arenas = [arL] ∧
    IssueAt K0 0 0 [5] 2 (run K0 [] opsObs).s .reject ∧ IssueStatic K0 (run K0 [] opsObs).s arL 0 [5] 2 ∧
    Avail arL [5] :=
  ⟨reach_run (by decide), by decide,
    .reject (ar := arL) (by decide) (.noRight (by decide) (by decide) (by decide)), by decide, by decide⟩

end Ern.Derived.Arena
