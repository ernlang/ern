import Ern.Concurrency.Encap5
import Ern.Concurrency.Reachable

/-!
# L1 and L2 on `cap5` (WC5 C45, `OB-C17`, `OB-C18`)

Statements of the brief of milestone 4, task 4, on the states reached by an `EncapsulatedTrace5`
from an initial state: `cap5_sound`, `cap5_compat` (L2, state form), `cap5_drop_own` (L1) and
`handoff_loss_exists` (L2, trace form). Each statement is a `Prop` here; the theorems establish or
refute them (`Corpus/GuardedChain.lean` for the counterexamples).
-/

namespace Ern.Concurrency

open Ern.MemoryModel.Access

/-! ## Statements -/

/-- Order of capability values (WC5 C43): `none < Observe < Modify`. -/
def capRank : Option Mode → Nat
  | none => 0
  | some .observe => 1
  | some .modify => 2

/-- Step `lbl` is an access by context `d` to leaf `l` requiring mode `m`: `read3` and
`writeShared` require `Observe` (Spec 1 §66.2, §68.2), `write3` requires `Modify` (§67.1). -/
def Label.Access : Label → Nat → Nat → Mode → Prop
  | .kernel c (.read _ ls), d, l, m => c = d ∧ l ∈ ls ∧ m = .observe
  | .kernel c (.write _ ls), d, l, m => c = d ∧ l ∈ ls ∧ m = .modify
  | .kernel c (.writeShared _ ls), d, l, m => c = d ∧ l ∈ ls ∧ m = .observe
  | _, _, _, _ => False

/-- An `EncapsulatedTrace5` with named states: `σ 0` is the first state, `σ (i + 1)` the state
after step `i`. -/
def Run5 (k : K) (L : MutexLayout) (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) :
    Prop :=
  ∀ i (h : i < lbls.length),
    Encap5 L ((σ i).1, (σ i).2.1) lbls[i] ∧ LStep k L lbls[i] (σ i) (σ (i + 1))

/-- Every `EncapsulatedTrace5` has named states. -/
theorem run5_of_trace {k : K} {L : MutexLayout} {st st' : SC × SyncReg × ArenaReg}
    {lbls : List Label} (h : EncapsulatedTrace5 k L st lbls st') :
    ∃ σ, σ 0 = st ∧ Run5 k L σ lbls ∧ σ lbls.length = st' := by
  induction h with
  | @nil st => exact ⟨fun _ => st, rfl, fun i h => absurd h (Nat.not_lt_zero _), rfl⟩
  | @cons st st₁ st₂ lbl lbls he hs _ ih =>
    obtain ⟨σ, h0, hr, hn⟩ := ih
    refine ⟨fun i => match i with | 0 => st | i + 1 => σ i, rfl, fun i hi => ?_, hn⟩
    cases i with
    | zero => exact ⟨he, by show LStep k L lbl st (σ 0); rw [h0]; exact hs⟩
    | succ i => exact hr i (by simpa using hi)

/-- `cap5_sound` (brief of milestone 4, task 4): as `cap_sound`, for the access steps admitted by
`Encap5` from the states reached by an `EncapsulatedTrace5` from an initial state (Spec 1 §47). -/
def Cap5Sound (k : K) (L : MutexLayout) : Prop :=
  ∀ (statics : Statics) (lbls : List Label) (st : SC × SyncReg × ArenaReg) (c a : Nat)
    (ls : List Nat) (s' : SC), StaticsOK statics →
    EncapsulatedTrace5 k L (SC.ofS3 (S3.init statics), [], []) lbls st →
    (Encap5 L (st.1, st.2.1) (.kernel c (.read a ls)) → opStepC k (.read a ls) c st.1 (.ok s') →
      ∀ l ∈ ls, Allows (cap5 st.1 st.2.1 c l) .observe) ∧
    (Encap5 L (st.1, st.2.1) (.kernel c (.write a ls)) → opStepC k (.write a ls) c st.1 (.ok s') →
      ∀ l ∈ ls, Allows (cap5 st.1 st.2.1 c l) .modify) ∧
    (Encap5 L (st.1, st.2.1) (.kernel c (.writeShared a ls)) →
      opStepC k (.writeShared a ls) c st.1 (.ok s') →
      ∀ l ∈ ls, Allows (cap5 st.1 st.2.1 c l) .observe)

/-- `cap5_drop_own` (L1, WC5 C45, `OB-C17`; brief of milestone 4, task 4): from a state reached by
an `EncapsulatedTrace5` from an initial state, a step admitted by `Encap5` that strictly lowers
`cap5` of context `c` on leaf `l` is a step of `c`. -/
def Cap5DropOwn (k : K) (L : MutexLayout) : Prop :=
  ∀ (statics : Statics) (lbls : List Label) (st st' : SC × SyncReg × ArenaReg) (lbl : Label)
    (c l : Nat), StaticsOK statics →
    EncapsulatedTrace5 k L (SC.ofS3 (S3.init statics), [], []) lbls st →
    Encap5 L (st.1, st.2.1) lbl → LStep k L lbl st st' →
    capRank (cap5 st'.1 st'.2.1 c l) < capRank (cap5 st.1 st.2.1 c l) → lbl.ctx = c

/-- `handoff_loss_exists` (L2, trace form, WC5 C45, `OB-C18`; brief of milestone 4, task 4): on an
`EncapsulatedTrace5` from an initial state, if context `c'` accesses `l` at step `i` and a context
`c ≠ c'` accesses `l` at step `j > i`, at least one of the two requiring `Modify`, then some step
`k'` with `i < k' < j` is a step of `c'` that strictly lowers `cap5` of `c'` on `l`. -/
def HandoffLossExists (k : K) (L : MutexLayout) : Prop :=
  ∀ (statics : Statics) (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label),
    StaticsOK statics → σ 0 = (SC.ofS3 (S3.init statics), [], []) → Run5 k L σ lbls →
    ∀ (i j c c' l : Nat) (m m' : Mode) (hi : i < j) (hj : j < lbls.length), c ≠ c' →
      lbls[i].Access c' l m → lbls[j].Access c l m' → (m = .modify ∨ m' = .modify) →
      ∃ k', ∃ hk : k' < lbls.length, i < k' ∧ k' < j ∧ lbls[k'].ctx = c' ∧
        capRank (cap5 (σ (k' + 1)).1 (σ (k' + 1)).2.1 c' l) <
          capRank (cap5 (σ k').1 (σ k').2.1 c' l)

/-! ## L2, state form -/

/-- A place of `P` has a leaf in its footprint when parents precede their children (Spec 1 §40,
§49.2). -/
theorem footprint_ne {P : List Place} (hP : ∀ q o, parentOf P q = some o → o < q) :
    ∀ n q, P.length - q ≤ n → q < P.length → ∃ l, l ∈ footprint P q := by
  intro n
  induction n with
  | zero => intro q hn hq; exact absurd hn (by omega)
  | succ n ih =>
    intro q hn hq
    by_cases hex : ∃ r ∈ List.range P.length, parentOf P r = some q
    · obtain ⟨r, hr, hpr⟩ := hex
      have hr := List.mem_range.1 hr
      have hqr := hP r q hpr
      obtain ⟨l, hlr⟩ := ih r (by omega) hr
      obtain ⟨hl1, hl2⟩ := List.mem_filter.1 hlr
      obtain ⟨hleaf, hlt, hpart⟩ := of_decide_eq_true hl2
      refine ⟨l, List.mem_filter.2 ⟨hl1, decide_eq_true ⟨hleaf, hlt, Or.inr ?_⟩⟩⟩
      have hc : chain (parentOf P) r = q :: chain (parentOf P) q := chain_cons hpr hqr
      rcases hpart with rfl | hrc
      · rw [hc]; exact List.mem_cons_self ..
      · exact chain_trans hP (l + 1) l (by omega) r hrc q (by rw [hc]; exact List.mem_cons_self ..)
    · have hl : isLeaf P q := fun r hr hpr => hex ⟨r, List.mem_range.2 hr, hpr⟩
      exact ⟨q, List.mem_filter.2 ⟨List.mem_range.2 hq, decide_eq_true ⟨hl, hq, Or.inl rfl⟩⟩⟩

/-- An effective mode `Modify` (Spec 1 §43, case 2): the authority exists, is active, covers the
leaf, has own mode `Modify` and no active descendant covers the leaf. -/
theorem eff_modify {t : S3} {x l : Nat} (h : effective t x l = some .modify) :
    ∃ y, t.A[x]? = some y ∧ y.active = true ∧ l ∈ y.footprint ∧ y.mode = .modify ∧
      descModes t x l = [] := by
  unfold effective at h
  split at h
  · rename_i y hy
    split at h
    · rename_i hc
      unfold effOf at h
      split at h
      · rename_i hd; exact ⟨y, hy, hc.1, hc.2, Option.some.inj h, hd⟩
      · split at h <;> simp at h
    · simp at h
  · simp at h

/-- A present effective mode (Spec 1 §43, cases 2 and 4): the authority exists, is active, covers
the leaf, and no active descendant of mode `Modify` covers the leaf. -/
theorem eff_present {t : S3} {y l : Nat} (h : effective t y l ≠ none) :
    ∃ z, t.A[y]? = some z ∧ z.active = true ∧ l ∈ z.footprint ∧ Mode.modify ∉ descModes t y l := by
  unfold effective at h
  split at h
  · rename_i z hz
    split at h
    · rename_i hc
      unfold effOf at h
      exact ⟨z, hz, hc.1, hc.2, fun hm => h (by split <;> simp_all)⟩
    · exact absurd rfl h
  · exact absurd rfl h

/-- An active descendant covering a leaf contributes its mode (Spec 1 §43). -/
theorem mem_descModes {t : S3} {a j l : Nat} {w : Authority} (hw : t.A[j]? = some w)
    (ha : w.active = true) (hl : l ∈ w.footprint) (hj : a ∈ t.ancs j) :
    w.mode ∈ descModes t a l := by
  unfold descModes
  refine List.mem_filterMap.2 ⟨j, List.mem_range.2 (lt_of_getElem? hw), ?_⟩
  rw [hw]; simp [ha, hl, hj]

/-- Two distinct authorities, one with effective `Modify` on a leaf, the other with a present
effective mode on it, contradict `I1` (Spec 1 §43, §50). -/
theorem auth_compat {t : S3} (hI : I1 t) {x y l : Nat} (hxy : x ≠ y)
    (hx : effective t x l = some .modify) (hy : effective t y l ≠ none) : False := by
  obtain ⟨xa, hxa, hxact, hxl, hxm, hxd⟩ := eff_modify hx
  obtain ⟨ya, hya, hyact, hyl, hyd⟩ := eff_present hy
  by_cases h1 : x ∈ t.ancs y
  · have := mem_descModes hya hyact hyl h1
    rw [hxd] at this; simp at this
  · by_cases h2 : y ∈ t.ancs x
    · exact hyd (hxm ▸ mem_descModes hxa hxact hxl h2)
    · have := (hI x y xa ya l hxy hxa hya hxact hyact hxl hyl h1 h2).1
      rw [hxm] at this; cases this

/-- `Allows e Modify` is `e = some Modify` (Spec 1 §43). -/
theorem allows_modify {e : Option Mode} (h : Allows e .modify) : e = some .modify := by
  cases e with
  | none => exact h.elim
  | some e =>
    rcases h with h | h
    · cases h
    · rw [h]

/-- A mode allowed is present (Spec 1 §43). -/
theorem allows_present {e : Option Mode} {m : Mode} (h : Allows e m) : e ≠ none := by
  cases e with
  | none => exact h.elim
  | some _ => exact Option.some_ne_none _

/-- L2 on attributions (WC5 C43, C45): under the frame uniqueness of WC4 C3, `I1` (Spec 1 §50) and
`WF3` (Spec 1 §49), no authority attributable to `c` in mode `Modify` with effective `Modify` on a
leaf coexists with an authority attributable to another context `c'` with an effective mode
permitting its mode on the same leaf. -/
theorem attr_compat {s : SC} (hnd : s.frames.Nodup) (hI : I1 s.flat) (hw : WF3 s.flat)
    {c c' : Nat} (hcc : c ≠ c') {x : Nat} {m₀ : Mode} (hx : Attr s c x m₀) (hm₀ : m₀ = .modify) :
    ∀ y l m, effective s.flat x l = some .modify → Attr s c' y m →
      Allows (effective s.flat y l) m → False := by
  have hP : ∀ q o, parentOf s.P q = some o → o < q := fun q o h => by
    unfold parentOf at h
    cases hq : s.P[q]? with
    | none => rw [hq] at h; cases h
    | some pl =>
      rw [hq] at h
      obtain ⟨_, _, hlt, _⟩ := hw.places q pl o hq h
      exact hlt
  induction hx with
  | @base a m y f hy ha hm hf hin =>
    intro y' l m' hel hy' hal
    by_cases hxy : a = y'
    · subst hxy
      cases hy' with
      | base hy2 _ _ hf2 hin2 =>
        rw [hy] at hy2; cases hy2; rw [hf] at hf2; cases hf2
        exact hcc (ReparentAux.stk_unique hnd hin hin2)
      | held hy2 _ _ hp2 =>
        rw [hy] at hy2; cases hy2; rw [hf] at hp2; cases hp2
    · exact auth_compat hI hxy hel (allows_present hal)
  | @held a p b m y hy ha hm hp hb hc ih =>
    intro y' l m' hel hy' hal
    by_cases hxy : a = y'
    · subst hxy
      cases hy' with
      | base hy2 _ _ hf2 =>
        rw [hy] at hy2; cases hy2; rw [hp] at hf2; cases hf2
      | held hy2 _ _ hp2 hb2 hc2 =>
        rw [hy] at hy2; cases hy2; rw [hp] at hp2; cases hp2
        have hu : s.flat.Usable p := by
          have := hw.holders a _ hy ha; rw [hp] at this; exact this
        obtain ⟨l', hl'⟩ := footprint_ne hP _ p (Nat.le_refl _) hu.lt
        exact ih hm₀ _ l' _ (allows_modify (hm₀ ▸ hc l' hl')) hb2 (hc2 l' hl')
    · exact auth_compat hI hxy hel (allows_present hal)

/-- `Attr5` is an `Attr` (brief of milestone 4, task 3; WC5 C43). -/
theorem Attr5.attr {s : SC} {reg : SyncReg} {c x : Nat} {m : Mode} (h : Attr5 s reg c x m) :
    Attr s c x m := by
  induction h with
  | base _ hy ha hm hf hin => exact .base hy ha hm hf hin
  | held _ hy ha hm hp _ hc ih => exact .held hy ha hm hp ih hc

/-- `cap5` at `Modify` rests on an authority attributable in `Modify` with effective `Modify`. -/
theorem cap5_modify {s : SC} {reg : SyncReg} {c l : Nat} (h : cap5 s reg c l = some .modify) :
    CapAt5 s reg c l .modify := by
  unfold cap5 at h
  split at h
  · assumption
  · split at h <;> simp at h

/-- A present `cap5` rests on an attributable authority with a sufficient effective mode. -/
theorem cap5_present {s : SC} {reg : SyncReg} {c l : Nat} (h : cap5 s reg c l ≠ none) :
    ∃ m, CapAt5 s reg c l m := by
  unfold cap5 at h
  split at h
  · exact ⟨_, ‹_›⟩
  · split at h
    · exact ⟨_, ‹_›⟩
    · exact absurd rfl h

/-- L2, state form, on one state (WC5 C45): under the frame uniqueness of WC4 C3, `I1` and `WF3`,
for `c ≠ c'`, never `cap5 c l = Modify` with `cap5 c' l ≠ none`. -/
theorem cap5_compat_state {s : SC} {reg : SyncReg} (hnd : s.frames.Nodup) (hI : I1 s.flat)
    (hw : WF3 s.flat) {c c' l : Nat} (hcc : c ≠ c') (hm : cap5 s reg c l = some .modify) :
    cap5 s reg c' l = none := by
  cases hc' : cap5 s reg c' l with
  | none => rfl
  | some m' =>
    exfalso
    obtain ⟨x, -, hx, hex⟩ := cap5_modify hm
    obtain ⟨m, y, -, hy, hey⟩ := cap5_present (by rw [hc']; exact Option.some_ne_none _)
    exact attr_compat hnd hI hw hcc hx.attr rfl y l m (allows_modify hex) hy.attr hey

/-- `cap5_compat` (L2, state form, WC5 C45, `OB-C18`; brief of milestone 4, task 4): on the states
reached by an `EncapsulatedTrace5` from an initial state (Spec 1 §47), under `DDSound` (Spec 1 §80),
for `c ≠ c'`, never `cap5 c l = Modify` with `cap5 c' l ≠ none`. -/
theorem cap5_compat {k : K} {L : MutexLayout} {statics : Statics} {lbls : List Label}
    {st : SC × SyncReg × ArenaReg} (hdd : DDSound k) (hst : StaticsOK statics)
    (h : EncapsulatedTrace5 k L (SC.ofS3 (S3.init statics), [], []) lbls st) {c c' l : Nat}
    (hcc : c ≠ c') (hm : cap5 st.1 st.2.1 c l = some .modify) : cap5 st.1 st.2.1 c' l = none := by
  obtain ⟨⟨hF, hw⟩, ⟨⟨hI, -⟩, -⟩, -⟩ := (encapsulated_inv hdd hst (encapsulatedTrace5_imp h)).1
  exact cap5_compat_state hF.nodup hI hw hcc hm

/-! ## L1: per-label lemmas -/

/-- Transport of `Attr5` (brief of milestone 4, task 3) from `s` to `s'` for context `c`: the
frames of `c` stay live, the footprints of existing places are unchanged, and every authority
attributable to `c` keeps its activity, own mode and holder, stays outside the live `guarded` set,
and keeps an effective mode permitting the mode in which it is attributable (Spec 1 §43; WC5
C43). -/
theorem attr5_transport {s s' : SC} {reg reg' : SyncReg} {c : Nat} (hw : WF3 s.flat)
    (hstk : ∀ f ∈ s.stk c, f ∈ s'.stk c)
    (hfp : ∀ p, p < s.P.length → footprint s'.P p = footprint s.P p)
    (hA : ∀ u m y, Attr5 s reg c u m → s.A[u]? = some y → ∃ y', s'.A[u]? = some y' ∧
      y'.active = y.active ∧ y'.mode = y.mode ∧ y'.holder = y.holder)
    (hng : ∀ u m, Attr5 s reg c u m → NotGuarded s' reg' u)
    (heff : ∀ u m l, Attr5 s reg c u m → Allows (effective s.flat u l) m →
      Allows (effective s'.flat u l) m)
    {u : Nat} {m : Mode} (h : Attr5 s reg c u m) : Attr5 s' reg' c u m := by
  induction h with
  | @base a m y f hg hy ha hm hf hin =>
    obtain ⟨y', hy', ha', hm', hf'⟩ := hA a m y (.base hg hy ha hm hf hin) hy
    exact .base (hng a m (.base hg hy ha hm hf hin)) hy' (ha'.trans ha) (hm' ▸ hm) (hf'.trans hf)
      (hstk f hin)
  | @held a p b m y hg hy ha hm hp hb hc ih =>
    have hab : Attr5 s reg c a m := .held hg hy ha hm hp hb hc
    obtain ⟨y', hy', ha', hm', hp'⟩ := hA a m y hab hy
    have hu : s.flat.Usable p := by
      have := hw.holders a _ hy ha; rw [hp] at this; exact this
    refine .held (hng a m hab) hy' (ha'.trans ha) (hm' ▸ hm) (hp'.trans hp) ih fun l hl => ?_
    rw [hfp p hu.lt] at hl
    exact heff b m l hb (hc l hl)

/-- `cap5` does not decrease when every `CapAt5` of `c` on `l` is kept (brief of milestone 4,
task 3; WC5 C43). -/
theorem cap5_rank_mono {s s' : SC} {reg reg' : SyncReg} {c l : Nat}
    (h : ∀ m, CapAt5 s reg c l m → CapAt5 s' reg' c l m) :
    capRank (cap5 s reg c l) ≤ capRank (cap5 s' reg' c l) := by
  unfold cap5
  by_cases h1 : CapAt5 s reg c l .modify
  · simp only [h1, h .modify h1, ↓reduceIte, Nat.le_refl]
  · by_cases h2 : CapAt5 s reg c l .observe
    · have h2' := h .observe h2
      simp only [h1, h2, h2', ↓reduceIte]
      split <;> simp [capRank]
    · simp only [h1, h2, ↓reduceIte, capRank]; exact Nat.zero_le _

/-- `cap5` of `c` does not decrease under the hypotheses of `attr5_transport`. -/
theorem cap5_transport {s s' : SC} {reg reg' : SyncReg} {c : Nat} (hw : WF3 s.flat)
    (hstk : ∀ f ∈ s.stk c, f ∈ s'.stk c)
    (hfp : ∀ p, p < s.P.length → footprint s'.P p = footprint s.P p)
    (hA : ∀ u m y, Attr5 s reg c u m → s.A[u]? = some y → ∃ y', s'.A[u]? = some y' ∧
      y'.active = y.active ∧ y'.mode = y.mode ∧ y'.holder = y.holder)
    (hng : ∀ u m, Attr5 s reg c u m → NotGuarded s' reg' u)
    (heff : ∀ u m l, Attr5 s reg c u m → Allows (effective s.flat u l) m →
      Allows (effective s'.flat u l) m) (l : Nat) :
    capRank (cap5 s reg c l) ≤ capRank (cap5 s' reg' c l) := by
  refine cap5_rank_mono fun m ⟨x, hx, ha, he⟩ => ⟨x, ?_, attr5_transport hw hstk hfp hA hng heff ha,
    heff x m l ha he⟩
  have hlt := List.mem_range.1 hx
  obtain ⟨y, hy⟩ : ∃ y, s.A[x]? = some y := ⟨_, List.getElem?_eq_getElem hlt⟩
  obtain ⟨y', hy', -⟩ := hA x m y ha hy
  exact List.mem_range.2 (lt_of_getElem? hy')

/-- `effective` reads only the authorities (Spec 1 §43). -/
theorem effective_of_A {t t' : S3} (h : t.A = t'.A) (a p : Nat) :
    effective t a p = effective t' a p := by
  have ho : t.org = t'.org := by funext i; unfold S3.org; rw [h]
  unfold effective descModes S3.ancs; rw [h, ho]

/-- Same kernel components `A`, `P` and contexts, and registries with the same `guarded`
identities: `cap5` does not decrease. -/
theorem cap5_same {s s' : SC} {reg reg' : SyncReg} (hw : WF3 s.flat) (hA : s'.A = s.A)
    (hP : s'.P = s.P) (hC : s'.C = s.C) (hreg : ∀ e' ∈ reg', ∃ e ∈ reg, e.guarded = e'.guarded)
    (c l : Nat) : capRank (cap5 s reg c l) ≤ capRank (cap5 s' reg' c l) := by
  have hAf : s'.flat.A = s.flat.A := hA
  refine cap5_transport hw (fun f hf => by unfold SC.stk at hf ⊢; rw [hC]; exact hf)
    (fun p _ => by rw [hP]) (fun u m y _ hy => ⟨y, by rw [hA]; exact hy, rfl, rfl, rfl⟩)
    (fun u m h e he hl => ?_) (fun u m l _ h => by rw [effective_of_A hAf]; exact h) l
  obtain ⟨e₀, he₀, hg⟩ := hreg e he
  have hng : NotGuarded s reg u := by
    cases h with
    | base hg' => exact hg'
    | held hg' => exact hg'
  have hl' : e₀.Live s := by
    show s.flat.Active e₀.guarded
    obtain ⟨y, hy, hya⟩ : s'.flat.Active e.guarded := hl
    exact ⟨y, by rw [hg]; rw [← hAf]; exact hy, hya⟩
  exact hg ▸ hng e₀ he₀ hl'

/-- Labels whose `ok` effect changes neither the authorities, the places, the contexts nor the
`guarded` identities of the registry: `read3`, `write3`, `writeShared` (Spec 1 §66–§68: initialization
states only), `depend` (§64: anchors only), `pin`, `unpin` (§74, §75: pinning obligations only),
`join` (WC4 C8: no change), `resetLock` (WC4 C18: the grant record only), `newArena` (Spec 1
§76: the arena registry only). -/
def Label.Inert : Label → Prop
  | .kernel _ (.read _ _) | .kernel _ (.write _ _) | .kernel _ (.writeShared _ _)
  | .kernel _ (.depend _ _) | .kernel _ (.pin _) | .kernel _ (.unpin _) | .join _ _
  | .resetLock _ _ | .newArena _ _ _ => True
  | _ => False

/-- The `ok` effect of an inert label (Spec 1 §64, §66–§68, §74–§76; WC4 C8, C18). -/
theorem inert_effect {k : K} {L : MutexLayout} {lbl : Label} {st st' : SC × SyncReg × ArenaReg}
    (hi : lbl.Inert) (h : LStep k L lbl st st') :
    st'.1.A = st.1.A ∧ st'.1.P = st.1.P ∧ st'.1.C = st.1.C ∧
      ∀ e' ∈ st'.2.1, ∃ e ∈ st.2.1, e.guarded = e'.guarded := by
  have same : ∀ (reg : SyncReg), ∀ e' ∈ reg, ∃ e ∈ reg, e.guarded = e'.guarded :=
    fun _ e' he' => ⟨e', he', rfl⟩
  cases h with
  | @kernel s s' reg ar c op hk =>
    cases op <;> simp only [Label.Inert] at hi
    · obtain ⟨-, hR⟩ := hk
      cases hR; exact ⟨rfl, rfl, rfl, same reg⟩
    · obtain ⟨-, o, hR, ho⟩ := hk
      cases hR with
      | ok => cases ho; exact ⟨rfl, rfl, rfl, same reg⟩
      | reject => cases ho
    · obtain ⟨-, o, hR, ho⟩ := hk
      cases hR with
      | ok => cases ho; exact ⟨rfl, rfl, rfl, same reg⟩
      | reject => cases ho
    · obtain ⟨-, o, hR, ho⟩ := hk
      cases hR with
      | ok => cases ho; exact ⟨rfl, rfl, rfl, same reg⟩
      | reject => cases ho
    · obtain ⟨-, o, hR, ho⟩ := hk
      cases hR with
      | ok => cases ho; exact ⟨rfl, rfl, rfl, same reg⟩
      | reject => cases ho
    · obtain ⟨-, o, hR, ho⟩ := hk
      cases hR with
      | ok => cases ho; exact ⟨rfl, rfl, rfl, same reg⟩
      | reject => cases ho
  | join hj =>
    cases hj; exact ⟨rfl, rfl, rfl, same _⟩
  | @resetLock s reg ar c i st₁ hr =>
    obtain ⟨-, e, he, -, -, -, rfl⟩ := hr
    refine ⟨rfl, rfl, rfl, fun e' he' => ?_⟩
    rcases List.mem_or_eq_of_mem_set he' with h | h
    · exact ⟨e', h, rfl⟩
    · exact ⟨e, List.mem_of_getElem? he, by rw [h]⟩
  | newArena hn =>
    obtain ⟨-, hR⟩ := hn
    cases hR; exact ⟨rfl, rfl, rfl, same _⟩
  | _ => simp only [Label.Inert] at hi

/-- L1 (`cap5_drop_own`, WC5 C45) for the inert labels: from a state reached by an
`EncapsulatedTrace` from an initial state (Spec 1 §47), under `DDSound` (Spec 1 §80), an inert
step lowers no `cap5`, so the implication of `Cap5DropOwn` holds for it. -/
theorem cap5_drop_own_inert {k : K} {L : MutexLayout} {statics : Statics} {lbls : List Label}
    {st st' : SC × SyncReg × ArenaReg} {lbl : Label} (hdd : DDSound k) (hst : StaticsOK statics)
    (htr : EncapsulatedTrace5 k L (SC.ofS3 (S3.init statics), [], []) lbls st) (hi : lbl.Inert)
    (h : LStep k L lbl st st') (c l : Nat)
    (hd : capRank (cap5 st'.1 st'.2.1 c l) < capRank (cap5 st.1 st.2.1 c l)) : lbl.ctx = c := by
  obtain ⟨⟨-, hw⟩, -⟩ := (encapsulated_inv hdd hst (encapsulatedTrace5_imp htr)).1
  obtain ⟨hA, hP, hC, hreg⟩ := inert_effect hi h
  exact absurd hd (Nat.not_lt.2 (cap5_same hw hA hP hC hreg c l))

/-- An exercisable authority's own mode permits the requested mode (Spec 1 §43). -/
theorem exer_mode {t : S3} {a : Nat} {m : Mode} {y : Authority} (h : t.ExercisableAt a m)
    (hy : t.A[a]? = some y) : m.le y.mode := by
  cases h with
  | base hy' _ hm => rw [hy] at hy'; cases hy'; exact hm
  | held hy' _ hm => rw [hy] at hy'; cases hy'; exact hm

/-- Adding an `Observe` descendant keeps an effective `Observe` (Spec 1 §43, case 4). -/
theorem allows_effOf_obs {o : Mode} {ds : List Mode} (h : Allows (effOf o ds) .observe) :
    Allows (effOf o (ds ++ [.observe])) .observe := by
  have hn : Mode.modify ∉ ds := by
    rcases allows_effOf h with ⟨h0, -⟩ | ⟨hn, -⟩
    · rw [h0]; simp
    · exact hn
  unfold effOf
  simp only [List.append_eq_nil_iff, List.cons_ne_self, and_false, ↓reduceIte, List.mem_append,
    List.mem_singleton, reduceCtorEq, or_false, hn]
  exact Or.inl rfl

/-- `derive` by context `c'` (Spec 1 §60) keeps, for every other context `c`, the effective mode of
an authority attributable to `c` (WC5 C43): the new authority lowers only the effective modes of
its source and of the source's ancestors on its region, which `attr_compat` and `I1` exclude for
`c` (Spec 1 §43, §50, §60.1, §60.2). -/
theorem derive_eff_keep {s : SC} (hnd : s.frames.Nodup) (hI : I1 s.flat) (hw : WF3 s.flat)
    {c c' src : Nat} {region : List Nat} {md : Mode} (hcc : c ≠ c') (hne : s.stk c' ≠ [])
    (hp : DerivePre (s.view c') src region md) {u : Nat} {m : Mode} (hu : Attr s c u m)
    {l : Nat} (hal : Allows (effective s.flat u l) m) :
    Allows (effective (s.flat.addAuth ⟨md, some src, region, .frame (s.view c').top, true⟩) u l)
      m := by
  have hvA : ∀ a l, effective (s.view c') a l = effective s.flat a l :=
    fun a l => effective_of_A rfl a l
  have hulen : u < s.A.length := by
    cases hu with
    | base hy => exact lt_of_getElem? hy
    | held hy => exact lt_of_getElem? hy
  by_cases hl : l ∈ region
  · obtain ⟨x, hx, hxa⟩ := hp.active
    have hxl : l ∈ x.footprint := by
      have := hp.within l hl; unfold S3.afp at this; rw [hx] at this; exact this
    have hsl : src < s.A.length := lt_of_getElem? hx
    obtain ⟨z, hz, hza, hzl, -⟩ := eff_present (allows_present hal)
    have hz' : (s.flat.addAuth ⟨md, some src, region, .frame (s.view c').top, true⟩).A[u]? =
        some z := by rw [addAuth_lt hulen]; exact hz
    rw [effective_eq hz' hza hzl, descModes_addAuth,
      ancs_addAuth_self (s := s.flat) (rfl : (⟨md, some src, region, .frame (s.view c').top, true⟩ :
        Authority).origin = some src) hsl]
    rw [effective_eq hz hza hzl] at hal
    by_cases hus : u ∈ src :: s.flat.ancs src
    · simp only [hl, hus, and_self, ↓reduceIte]
      have hcomp : ∀ m₁, Attr s c u .modify → effective s.flat u l = some .modify →
          Attr s c' src m₁ → Allows (effective s.flat src l) m₁ → False :=
        fun m₁ h1 h2 h3 h4 => attr_compat hnd hI hw hcc h1 rfl src l m₁ h2 h3 h4
      have hc'src : Attr s c' src md := attr_of_exercisable hne hp.exercisable
      have hmod : Allows (effective s.flat src l) md := (hvA src l) ▸ hp.modeOK l hl
      have hxm : md.le x.mode := exer_mode hp.exercisable hx
      rcases List.mem_cons.1 hus with rfl | hanc
      · -- `u` is the source
        cases md with
        | modify =>
          exact (attr_compat hnd hI hw (Ne.symm hcc) hc'src rfl _ l m
            (allows_modify hmod) hu (by rw [effective_eq hz hza hzl]; exact hal)).elim
        | observe =>
          cases m with
          | observe => exact allows_effOf_obs hal
          | modify =>
            exact (hcomp _ hu (by rw [effective_eq hz hza hzl]; exact allows_modify hal) hc'src
              hmod).elim
      · -- `u` is a strict ancestor of the source
        have hin : x.mode ∈ descModes s.flat u l := mem_descModes hx hxa hxl hanc
        have hne' : descModes s.flat u l ≠ [] := List.ne_nil_of_mem hin
        cases md with
        | modify =>
          have : x.mode = .modify := by rcases hxm with h | h; cases h; exact h
          rw [this] at hin
          rcases allows_effOf hal with ⟨h0, -⟩ | ⟨hn, -⟩
          · exact absurd h0 hne'
          · exact absurd hin hn
        | observe =>
          cases m with
          | observe => exact allows_effOf_obs hal
          | modify =>
            rcases allows_effOf hal with ⟨h0, -⟩ | ⟨-, h⟩
            · exact absurd h0 hne'
            · cases h
    · simp only [hus, and_false, ↓reduceIte, List.append_nil]; exact hal
  · rw [effective_addAuth_notin hulen hl]; exact hal

/-- L1 (`cap5_drop_own`, WC5 C45) for `derive` (Spec 1 §60): from a state reached by an
`EncapsulatedTrace5` from an initial state (Spec 1 §47), under `DDSound` (Spec 1 §80), a `derive`
step that strictly lowers `cap5` of `c` is a step of `c`. -/
theorem cap5_drop_own_derive {k : K} {L : MutexLayout} {statics : Statics} {lbls : List Label}
    {st st' : SC × SyncReg × ArenaReg} {c' src : Nat} {region : List Nat} {mo : Mode}
    (hdd : DDSound k) (hst : StaticsOK statics)
    (htr : EncapsulatedTrace5 k L (SC.ofS3 (S3.init statics), [], []) lbls st)
    (h : LStep k L (.kernel c' (.derive src region mo)) st st') (c l : Nat)
    (hd : capRank (cap5 st'.1 st'.2.1 c l) < capRank (cap5 st.1 st.2.1 c l)) :
    (Label.kernel c' (.derive src region mo)).ctx = c := by
  obtain ⟨⟨hF, hw⟩, ⟨⟨hI, -⟩, -⟩, -⟩ := (encapsulated_inv hdd hst (encapsulatedTrace5_imp htr)).1
  refine Decidable.byContradiction fun hcc => ?_
  have hcc : c ≠ c' := fun e => hcc (e ▸ rfl)
  cases h with
  | @kernel s s' reg ar _ _ hk =>
    obtain ⟨hlive, o, hR, ho⟩ := hk
    cases hR with
    | reject => cases ho
    | ok hp =>
      cases ho
      have hne := hF.nonempty c' hlive
      refine absurd hd (Nat.not_lt.2 (cap5_transport (s' := s.set (deriveEff (s.view c') src region mo))
        (reg' := reg) hw (fun f hf => hf) (fun p _ => rfl)
        (fun u m y hu hy => ⟨y, ?_, rfl, rfl, rfl⟩) (fun u m hu e he hl => ?_)
        (fun u m l hu hal => ?_) l))
      · have hlt : u < s.A.length := lt_of_getElem? hy
        show (deriveEff (s.view c') src region mo).A[u]? = some y
        rw [deriveEff, addAuth_lt hlt]; exact hy
      · have hng : NotGuarded s reg u := by
          cases hu with
          | base hg => exact hg
          | held hg => exact hg
        have hlt : u < s.A.length := by
          cases hu with
          | base _ hy => exact lt_of_getElem? hy
          | held _ hy => exact lt_of_getElem? hy
        obtain ⟨y, hy, hya⟩ := hl
        by_cases hg : e.guarded < s.A.length
        · refine hng e he ⟨y, ?_, hya⟩
          have : (deriveEff (s.view c') src region mo).A[e.guarded]? = some y := hy
          rwa [deriveEff, addAuth_lt hg] at this
        · exact fun h => hg (h ▸ hlt)
      · have := derive_eff_keep hF.nodup hI hw hcc hne hp hu.attr hal
        rw [effective_of_A (t := (s.set (deriveEff (s.view c') src region mo)).flat)
          (t' := s.flat.addAuth ⟨mo, some src, region, .frame (s.view c').top, true⟩) rfl]
        exact this

end Ern.Concurrency
