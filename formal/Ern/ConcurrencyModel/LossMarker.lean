import Ern.ConcurrencyModel.LocalLoss

/-!
# Theorem 12d, 12e: existence and position of the loss marker (C42–C46)

Theorem 12 of `formal/DESIGN.md`, Milestone 4, target theorems, on the authority machine:

* 12d (C45, L2; C46): for `i < j`, distinct contexts `c'` and `c`, a leaf `l` and a mode `m` with
  `cap(σ j, c, l)` at least `m` and `cap(σ i, c', l)` incompatible with `m`, there is a first step
  `r ≥ i` after which `cap(·, c', l)` is compatible with `m`; it is unique, `i ≤ r < j`, and step
  `r` is a step of `c'` (`loss_marker_modify`; under the `Confined` criterion with the premise of
  C35 and C51 item 2(c), `loss_marker_confined`);
* 12e: the corollary for two access steps of 11e (`access_pair_marker`), with the variant of C42:
  a `read3` on an `Atomic` leaf that satisfies the rule of 11f uses `Modify` (`UsesModify`).

Step `r` is the position of the loss marker in the abstract trace (C45). Where the marker lies
among the physical events of a compound step is not stated (C45, last paragraph; `OB-C19`,
`OB-C20`).

The execution is an `EncapsulatedTrace` with named states (`EncapRun`): `σ 0` is the first state
and `σ (i + 1)` the state after step `i`. Fragment: `DDSound` (Spec 1 §80), well-formed statics
(§47), `σ 0` the initial state of Spec 1 §47.
-/

namespace Ern.ConcurrencyModel

open Ern.MemoryModel Ern.MemoryModel.Access

variable {pm : ProviderMeta}

/-! ## Executions with named states -/

/-- An `EncapsulatedTrace` (C51.1) with named states: step `i` of `lbls` goes from `σ i` to `σ (i +
1)` and satisfies `EncapStep`. Exported obligation `OB-C08` (C22), stated part
(`ExportedObligations`): a property of the executions of the safe abstraction; it does not establish
that the safe interfaces and the library produce only such executions. The obligation is exported
and remains open. -/
def EncapRun (pm : ProviderMeta) (ks : KShared) (L : MutexLayout)
    (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) : Prop :=
  ∀ i (h : i < lbls.length),
    EncapStep pm ks L (σ i) lbls[i] (σ (i + 1)) ∧ LStep ks L lbls[i] (σ i) (σ (i + 1))

/-- Appending a step to an `EncapsulatedTrace` (C51.1). -/
theorem EncapsulatedTrace.snoc {ks : KShared} {L : MutexLayout}
    {st st₁ st₂ : SC × SyncReg × ArenaReg} {lbls : List Label} {lbl : Label}
    (h : EncapsulatedTrace pm ks L st lbls st₁) (he : EncapStep pm ks L st₁ lbl st₂)
    (hs : LStep ks L lbl st₁ st₂) : EncapsulatedTrace pm ks L st (lbls ++ [lbl]) st₂ := by
  induction h with
  | nil => exact .cons he hs .nil
  | cons he' hs' _ ih => exact .cons he' hs' (ih he hs)

/-- Every `EncapsulatedTrace` has named states. -/
theorem encapRun_of_trace {ks : KShared} {L : MutexLayout} {st st' : SC × SyncReg × ArenaReg}
    {lbls : List Label} (h : EncapsulatedTrace pm ks L st lbls st') :
    ∃ σ, σ 0 = st ∧ EncapRun pm ks L σ lbls ∧ σ lbls.length = st' := by
  induction h with
  | @nil st => exact ⟨fun _ => st, rfl, fun i h => absurd h (Nat.not_lt_zero _), rfl⟩
  | @cons st st₁ st₂ lbl lbls he hs _ ih =>
    obtain ⟨σ, h0, hr, hn⟩ := ih
    refine ⟨fun i => match i with | 0 => st | i + 1 => σ i, rfl, fun i hi => ?_, hn⟩
    cases i with
    | zero => exact ⟨by rw [← h0] at he; exact he, by show LStep _ _ lbl st (σ 0); rw [h0]; exact hs⟩
    | succ i => exact hr i (by simpa using hi)

/-- Every state of an `EncapRun` is reached by an `EncapsulatedTrace` from its first state. -/
theorem encapRun_reach {ks : KShared} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg}
    {lbls : List Label} (hr : EncapRun pm ks L σ lbls) :
    ∀ k, k ≤ lbls.length → ∃ pre, EncapsulatedTrace pm ks L (σ 0) pre (σ k)
  | 0, _ => ⟨[], .nil⟩
  | k + 1, hk => by
    obtain ⟨pre, hpre⟩ := encapRun_reach hr k (by omega)
    obtain ⟨he, hs⟩ := hr k (by omega)
    exact ⟨pre ++ [lbls[k]], hpre.snoc he hs⟩

/-! ## The first compatible state -/

/-- The first index after `i` where a decidable property holds, when one exists within `n`
steps. -/
theorem exists_first_aux {P : Nat → Prop} [DecidablePred P] {i : Nat} (hi : ¬ P i) :
    ∀ n, (∃ k, i < k ∧ k ≤ i + n ∧ P k) →
      ∃ r, i ≤ r ∧ P (r + 1) ∧ ∀ k, i ≤ k → k ≤ r → ¬ P k
  | 0, ⟨k, h1, h2, _⟩ => absurd h2 (by omega)
  | n + 1, ⟨k, h1, h2, h3⟩ => by
    by_cases hex : ∃ k, i < k ∧ k ≤ i + n ∧ P k
    · exact exists_first_aux hi n hex
    · have hk : k = i + n + 1 := by
        refine Decidable.byContradiction fun hne => hex ⟨k, h1, by omega, h3⟩
      subst hk
      refine ⟨i + n, by omega, h3, fun k' hk1 hk2 hp => ?_⟩
      rcases Nat.lt_or_ge i k' with h | h
      · exact hex ⟨k', h, hk2, hp⟩
      · have : k' = i := by omega
        subst this; exact hi hp

/-- Between a state where a decidable property fails and a later one where it holds, there is a
first step after which it holds, and it precedes the later state. -/
theorem exists_first {P : Nat → Prop} [DecidablePred P] {i j : Nat} (hij : i < j) (hi : ¬ P i)
    (hj : P j) : ∃ r, i ≤ r ∧ r < j ∧ P (r + 1) ∧ ∀ k, i ≤ k → k ≤ r → ¬ P k := by
  obtain ⟨r, h1, h2, h3⟩ := exists_first_aux hi (j - i) ⟨j, hij, by omega, hj⟩
  refine ⟨r, h1, ?_, h2, h3⟩
  exact Decidable.byContradiction fun hn => h3 j (Nat.le_of_lt hij) (by omega) hj

/-! ## 12d: the loss marker (C45, L2; C46) -/

/-- Step `r` is the first step at or after `i` at the end of which the capability of `c'` on `l`
is compatible with the mode `m` under the incompatibility criterion `Inc` (C43, C45: "the loss
marker that ends the period containing `e1` during which `cap(·,c′,l)` is incompatible with the
capability used by `e2`"): `cap(·, c', l)` is incompatible with `m` from state `i` to state `r`,
and compatible in state `r + 1`. -/
def FirstCompatible (Inc : Option Mode → Mode → Prop) (σ : Nat → SC × SyncReg × ArenaReg)
    (i c' l : Nat) (m : Mode) (r : Nat) : Prop :=
  i ≤ r ∧ ¬ Inc (cap (σ (r + 1)).1 (σ (r + 1)).2.1 c' l) m ∧
    ∀ k, i ≤ k → k ≤ r → Inc (cap (σ k).1 (σ k).2.1 c' l) m

/-- The first compatible step is unique. -/
theorem FirstCompatible.unique {Inc : Option Mode → Mode → Prop}
    {σ : Nat → SC × SyncReg × ArenaReg} {i c' l : Nat} {m : Mode} {r r' : Nat}
    (h : FirstCompatible Inc σ i c' l m r) (h' : FirstCompatible Inc σ i c' l m r') : r' = r := by
  rcases Nat.lt_trichotomy r r' with hlt | heq | hgt
  · exact absurd (h'.2.2 (r + 1) (by have := h.1; omega) hlt) h.2.1
  · exact heq.symm
  · exact absurd (h.2.2 (r' + 1) (by have := h'.1; omega) hgt) h'.2.1

/-- Under the `Modify` criterion of C43, passing from a capability incompatible with `m` to one
compatible with it is a strict decrease. -/
theorem rank_drop_modify {v v' : Option Mode} {m : Mode} (h : IncompatModify v m)
    (h' : ¬ IncompatModify v' m) : capRank v' < capRank v := by
  cases v with
  | none => exact h.elim
  | some v =>
    cases v' with
    | none => cases v <;> simp [capRank]
    | some v' =>
      cases v <;> cases v' <;> cases m <;> simp_all [IncompatModify, capRank]

/-- Under the `Confined` criterion of C43, passing from a capability incompatible with `m` to one
compatible with it is a strict decrease. -/
theorem rank_drop_confined {v v' : Option Mode} {m : Mode} (h : IncompatConfined v m)
    (h' : ¬ IncompatConfined v' m) : capRank v' < capRank v := by
  have : v' = none := Decidable.byContradiction h'
  subst this
  cases v with
  | none => exact absurd rfl h
  | some v => cases v <;> simp [capRank]

/-- The loss marker for an incompatibility criterion `Inc` under which passing from incompatible
to compatible is a strict decrease of `cap` (C45, L1 and L2): if `cap(σ i, c', l)` is incompatible
with `m` and `cap(σ j, c', l)` is compatible with it, `i < j`, the first step at or after `i` at the
end of which `cap(·, c', l)` is compatible with `m` exists, is unique, precedes `j`, and is a step of
`c'` (L1, `local_loss`). -/
theorem loss_marker_of {Inc : Option Mode → Mode → Prop} [∀ v m, Decidable (Inc v m)]
    (hdrop : ∀ {v v' : Option Mode} {m : Mode}, Inc v m → ¬ Inc v' m → capRank v' < capRank v)
    {ks : KShared} {L : MutexLayout} {statics : Statics} {σ : Nat → SC × SyncReg × ArenaReg}
    {lbls : List Label} (hdd : DDSound ks.toK) (hst : StaticsOK statics)
    (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], [])) (hr : EncapRun pm ks L σ lbls)
    {i j c' l : Nat} {m : Mode} (hij : i < j) (hj : j ≤ lbls.length)
    (hi : Inc (cap (σ i).1 (σ i).2.1 c' l) m) (hjc : ¬ Inc (cap (σ j).1 (σ j).2.1 c' l) m) :
    ∃ r, FirstCompatible Inc σ i c' l m r ∧ (∀ r', FirstCompatible Inc σ i c' l m r' → r' = r) ∧
      r < j ∧ ∃ hr : r < lbls.length, lbls[r].requester = c' := by
  obtain ⟨r, h1, h2, h3, h4⟩ := exists_first (P := fun k => ¬ Inc (cap (σ k).1 (σ k).2.1 c' l) m)
    hij (fun h => h hi) hjc
  have hfc : FirstCompatible Inc σ i c' l m r :=
    ⟨h1, h3, fun k hk1 hk2 => Decidable.byContradiction (h4 k hk1 hk2)⟩
  have hrl : r < lbls.length := by omega
  refine ⟨r, hfc, fun r' h' => hfc.unique h', h2, hrl, ?_⟩
  obtain ⟨pre, hpre⟩ := encapRun_reach hr r (Nat.le_of_lt hrl)
  rw [h0] at hpre
  obtain ⟨he, hs⟩ := hr r hrl
  exact local_loss hdd hst hpre he hs c' l (hdrop (hfc.2.2 r h1 (Nat.le_refl _)) h3)

/-- **Theorem 12d**, `Modify` criterion (C45, L2: "a step of `c′` that reduces `cap(·,c′,l)` below
incompatibility with the capability used by `e2` lies at or after the step emitting `e1` and
before the step emitting `e2` in the abstract trace; that step carries the loss marker"; C46):
for `i < j`, distinct contexts `c'` and `c`, a leaf `l` and a mode `m` with `cap(σ j, c, l)` at
least `m` and `cap(σ i, c', l)` incompatible with `m` (C43, `Modify` criterion), there is a first
step `r ≥ i` at the end of which `cap(·, c', l)` is compatible with `m`; it is unique;
`i ≤ r < j`; and step `r` is a step of `c'`. Compatibility at `j` is L2 (`cap_l2`). -/
theorem loss_marker_modify {ks : KShared} {L : MutexLayout} {statics : Statics}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} (hdd : DDSound ks.toK)
    (hst : StaticsOK statics) (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], []))
    (hr : EncapRun pm ks L σ lbls) {i j c c' l : Nat} {m : Mode} (hij : i < j)
    (hj : j ≤ lbls.length) (hcc : c ≠ c') (hm : Allows (cap (σ j).1 (σ j).2.1 c l) m)
    (hi : IncompatModify (cap (σ i).1 (σ i).2.1 c' l) m) :
    ∃ r, FirstCompatible IncompatModify σ i c' l m r ∧
      (∀ r', FirstCompatible IncompatModify σ i c' l m r' → r' = r) ∧
      r < j ∧ ∃ hr : r < lbls.length, lbls[r].requester = c' := by
  refine loss_marker_of (Inc := IncompatModify) rank_drop_modify hdd hst h0 hr hij hj hi ?_
  obtain ⟨pre, hpre⟩ := encapRun_reach hr j hj
  rw [h0] at hpre
  intro hinc
  cases hcj : cap (σ j).1 (σ j).2.1 c l with
  | none => rw [hcj] at hm; exact hm
  | some m' =>
    have hl2 := cap_l2 hdd hst hpre hcc hcj
    cases hc' : cap (σ j).1 (σ j).2.1 c' l with
    | none => rw [hc'] at hinc; exact hinc
    | some v =>
      rw [hc'] at hinc hl2
      apply hl2
      rcases hinc with h | h
      · exact .inl h
      · subst h; rw [hcj] at hm
        rcases hm with h' | h'
        · cases h'
        · exact .inr h'

/-- **Theorem 12d**, `Confined` criterion (C43: "for `Confined`, any two present capabilities are
incompatible"; C45, L2: "for `Confined` storage, that no state gives two distinct contexts a
present capability on the same leaf is a premise of the safe-storage contract (C35; C51, item
2(c))"): under that premise for `l` on every state of the execution, the conclusion of
`loss_marker_modify` holds for the `Confined` criterion. -/
theorem loss_marker_confined {ks : KShared} {L : MutexLayout} {statics : Statics}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} (hdd : DDSound ks.toK)
    (hst : StaticsOK statics) (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], []))
    (hr : EncapRun pm ks L σ lbls) {i j c c' l : Nat} {m : Mode}
    (hconf : ∀ k, k ≤ lbls.length → ∀ d d', d ≠ d' → cap (σ k).1 (σ k).2.1 d l ≠ none →
      cap (σ k).1 (σ k).2.1 d' l = none)
    (hij : i < j) (hj : j ≤ lbls.length) (hcc : c ≠ c')
    (hm : Allows (cap (σ j).1 (σ j).2.1 c l) m)
    (hi : IncompatConfined (cap (σ i).1 (σ i).2.1 c' l) m) :
    ∃ r, FirstCompatible IncompatConfined σ i c' l m r ∧
      (∀ r', FirstCompatible IncompatConfined σ i c' l m r' → r' = r) ∧
      r < j ∧ ∃ hr : r < lbls.length, lbls[r].requester = c' :=
  loss_marker_of (Inc := IncompatConfined) rank_drop_confined hdd hst h0 hr hij hj hi
    fun hinc => hinc (hconf j hj c c' hcc (allows_present hm))

/-! ## 12e: pairs of accesses (C42, C44) -/

/-- An exercise in `Modify` from the current frame of `c` whose authority is also exercised in
`Observe` without a live `guarded` authority (C22.6) is itself guard-free, under `I1` (Spec 1
§50) and `WF3` (§49): along the holder chain, the authority exercised in `Modify` on each holding
place is the only one with a present effective mode there. -/
theorem exerFree_modify {s : SC} {reg : SyncReg} {c : Nat} (hI : I1 s.flat) (hw : WF3 s.flat) :
    ∀ {a : Nat} {m : Mode}, (s.view c).ExercisableAt a m → m = .modify →
      ExerFree s reg c a .observe → ExerFree s reg c a .modify := by
  have hv : ∀ d, (s.view d).A = s.A := fun _ => rfl
  intro a m hx
  induction hx with
  | @base a m y hy ha hm hf =>
    intro hmm hfree
    subst hmm
    rw [hv] at hy
    have hng : NotGuarded s reg a := by
      cases hfree with
      | base hg => exact hg
      | held hg => exact hg
    exact .base hng hy ha hm hf
  | @held a p b m y hy ha hm hp _ hc ih =>
    intro hmm hfree
    subst hmm
    rw [hv] at hy
    cases hfree with
    | base _ hy' _ _ hf' =>
      rw [hy] at hy'; cases hy'; rw [hp] at hf'; cases hf'
    | @held _ p' b' _ y' hng hy' _ _ hp' hb' hc' =>
      rw [hy] at hy'; cases hy'
      rw [hp] at hp'; cases hp'
      have hu : s.flat.Usable p := by
        have := hw.holders a y hy ha; rw [hp] at this; exact this
      obtain ⟨l, hl⟩ := exists_mem_footprint hw (s.flat.P.length - p + 1) p (by omega) hu.lt
      have hbl : effective s.flat b l = some .modify := allows_modify (hc l hl)
      have hbb : b' = b := Decidable.byContradiction fun hne =>
        allows_present (hc' l hl) (effective_exclusive hI (Ne.symm hne) hbl)
      subst hbb
      exact .held hng hy ha hm hp (ih rfl hb') hc

/-- The access `x` of the step `lbl` from `st` uses `Modify` (C44, C42): its required mode is
`Modify`, or it is a `read3` of an `Atomic` leaf that satisfies the rule of C42 (11f), which
"requires an effective and exercisable `Modify` capability for that leaf". -/
def UsesModify (ks : KShared) (st : SC × SyncReg × ArenaReg) (lbl : Label) (x : LeafAccess) :
    Prop :=
  x.mode = .modify ∨
    (AtomicLeaf ks x.leaf ∧ (∃ c a ls, lbl = .kernel c (.read a ls)) ∧
      AtomicOrdinaryOK ks st.1 lbl)

/-- An access that uses `Modify` is covered by a `Modify` capability of the executing context
(C43, C42), on a state satisfying the invariants of theorem 2. -/
theorem cap_of_usesModify {ks : KShared} {L : MutexLayout} {R : CtlOrders} {lbl : Label}
    {st st' : SC × SyncReg × ArenaReg} {acc : List LeafAccess} {x : LeafAccess}
    (hk : KInvCA st.1) (he : EncapStep pm ks L st lbl st') (h : LStep ks L lbl st st')
    (hc : classify ks L R st lbl = some acc) (hx : x ∈ acc) (hu : UsesModify ks st lbl x) :
    Allows (cap st.1 st.2.1 lbl.requester x.leaf) .modify := by
  have hF : FramesC st.1 := hk.1.1.1
  rcases hu with hm | ⟨hat, ⟨c, a, ls, rfl⟩, hrule⟩
  · rw [← hm]; exact cap_covers hF he h hc x hx
  · simp only [classify, Option.some.injEq] at hc; subst hc
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
    obtain ⟨hxm, hel⟩ := hrule l hl hat
    have hfree : ExerFree st.1 st.2.1 c a .observe := he.2.2
    have hmod := exerFree_modify (reg := st.2.1) hk.1.2.1.1.1 hk.1.1.2 hxm rfl hfree
    exact cap_covers_of hF hmod (by rw [hel]; exact Or.inr rfl)

/-- **Theorem 12e** (C44, C45, C46; corollary of 12a and 12d): for two access steps `i < j` of
11e on the same leaf `l`, of distinct contexts, at least one of which uses `Modify`
(`UsesModify`: its required mode is `Modify`, or, the variant of C42, it is a `read3` of an
`Atomic` leaf that satisfies the rule of 11f), there is a mode `m` used by the later access, with
which the capability of the earlier context at `i` is incompatible (C43, `Modify` criterion), and
the loss marker exists with the position of 12d: the first step `r ≥ i` at the end of which that
capability is compatible with `m`, unique, with `i ≤ r < j`, is a step of the earlier context. -/
theorem access_pair_marker {ks : KShared} {L : MutexLayout} {R : CtlOrders} {statics : Statics}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} (hdd : DDSound ks.toK)
    (hst : StaticsOK statics) (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], []))
    (hr : EncapRun pm ks L σ lbls) {i j l : Nat} (hij : i < j) (hj : j < lbls.length)
    {acc acc' : List LeafAccess} {x y : LeafAccess}
    (hci : classify ks L R (σ i) lbls[i] = some acc) (hx : x ∈ acc) (hxl : x.leaf = l)
    (hcj : classify ks L R (σ j) lbls[j] = some acc') (hy : y ∈ acc') (hyl : y.leaf = l)
    (hcc : lbls[j].requester ≠ lbls[i].requester)
    (hmod : UsesModify ks (σ i) lbls[i] x ∨ UsesModify ks (σ j) lbls[j] y) :
    ∃ m, Allows (cap (σ j).1 (σ j).2.1 lbls[j].requester l) m ∧
      IncompatModify (cap (σ i).1 (σ i).2.1 lbls[i].requester l) m ∧
      ∃ r, FirstCompatible IncompatModify σ i lbls[i].requester l m r ∧
        (∀ r', FirstCompatible IncompatModify σ i lbls[i].requester l m r' → r' = r) ∧
        r < j ∧ ∃ hr : r < lbls.length, lbls[r].requester = lbls[i].requester := by
  have hi' : i < lbls.length := by omega
  have reach : ∀ k, k ≤ lbls.length → KInvCA (σ k).1 := fun k hk => by
    obtain ⟨pre, hpre⟩ := encapRun_reach hr k hk
    rw [h0] at hpre
    exact (encapsulated_inv hdd hst hpre).1
  obtain ⟨hei, hsi⟩ := hr i hi'
  obtain ⟨hej, hsj⟩ := hr j hj
  have capi : Allows (cap (σ i).1 (σ i).2.1 lbls[i].requester l) x.mode := by
    rw [← hxl]; exact cap_covers (reach i (by omega)).1.1.1 hei hsi hci x hx
  have capj : Allows (cap (σ j).1 (σ j).2.1 lbls[j].requester l) y.mode := by
    rw [← hyl]; exact cap_covers (reach j (by omega)).1.1.1 hej hsj hcj y hy
  have key : ∃ m, Allows (cap (σ j).1 (σ j).2.1 lbls[j].requester l) m ∧
      IncompatModify (cap (σ i).1 (σ i).2.1 lbls[i].requester l) m := by
    rcases hmod with hm | hm
    · have hmi := cap_of_usesModify (reach i (by omega)) hei hsi hci hx hm
      rw [hxl] at hmi
      refine ⟨y.mode, capj, ?_⟩
      rw [allows_modify hmi]; exact .inl rfl
    · have hmj := cap_of_usesModify (reach j (by omega)) hej hsj hcj hy hm
      rw [hyl] at hmj
      refine ⟨.modify, hmj, ?_⟩
      cases hv : cap (σ i).1 (σ i).2.1 lbls[i].requester l with
      | none => rw [hv] at capi; exact capi.elim
      | some v => exact .inr rfl
  obtain ⟨m, hmj, hinc⟩ := key
  exact ⟨m, hmj, hinc, loss_marker_modify hdd hst h0 hr hij (Nat.le_of_lt hj) hcc hmj hinc⟩

end Ern.ConcurrencyModel
