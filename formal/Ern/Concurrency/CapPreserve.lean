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

end Ern.Concurrency
