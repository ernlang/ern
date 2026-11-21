import Ern.ConcurrencyModel.Capability
import Ern.ConcurrencyModel.SpawnValuePreserve

/-!
# Theorem 12c: L1, local loss (C43, C45)

Theorem 12 of `formal/DESIGN.md`, Milestone 4, target theorems: L1 (C45: "On an `EncapsulatedTrace`
(C51), a strict reduction of `cap(·,c′,l)` occurs only at a step of `c′` itself"; `OB-C17`), for
every label, the atomic step cases included (C39, "Authority-machine operation coverage"). One
lemma per label; the assembly is `local_loss`.

The proofs use the unrestricted contextual attribution of C43 (`UnrestrictedAttr`: the holder
chains of Spec 1 §43 read from a frame of the stack, through `guarded` authorities included),
which C43 distinguishes from `cap` and which is not the quantity of L1: it serves to show that an
authority exercised by the executing context is attributable to no other context.
-/

namespace Ern.ConcurrencyModel

open Ern.MemoryModel Ern.MemoryModel.Access

variable {pm : ProviderMeta}

/-! ## Unrestricted attribution (C43) -/

/-- `x` is attributable to context `c` in mode `m` without the `guarded` exclusion (C43:
"Unrestricted contextual capability is distinct from this guarded-chain-excluding `cap`"): the
holder chains of Spec 1 §43 read from a frame of the stack of `c` (reading 8). -/
inductive UnrestrictedAttr (s : SC) (c : Nat) : Nat → Mode → Prop where
  | base {a : Nat} {m : Mode} {y : Authority} {f : Nat} : s.A[a]? = some y → y.active = true →
      m.le y.mode → y.holder = .frame f → f ∈ s.stk c → UnrestrictedAttr s c a m
  | held {a p b : Nat} {m : Mode} {y : Authority} : s.A[a]? = some y → y.active = true →
      m.le y.mode → y.holder = .place p → UnrestrictedAttr s c b m →
      (∀ l ∈ footprint s.P p, Allows (effective s.flat b l) m) → UnrestrictedAttr s c a m

/-- What the current frame of a live context with a nonempty stack exercises (Spec 1 §43 on its
view, C2) is attributable to it without the `guarded` exclusion (C43). -/
theorem attr_of_exercisable {s : SC} {c a : Nat} {m : Mode} (hne : s.stk c ≠ [])
    (h : (s.view c).ExercisableAt a m) : UnrestrictedAttr s c a m := by
  have htop : (s.view c).top ∈ s.stk c := by
    obtain ⟨f, r, hfr⟩ := List.exists_cons_of_ne_nil hne
    rw [SC.view_top hfr, hfr]; exact List.mem_cons_self ..
  induction h with
  | base hy ha hm hf => exact .base hy ha hm hf htop
  | held hy ha hm hp _ hc ih => exact .held hy ha hm hp ih hc

/-- A guarded-chain-excluding attribution is an unrestricted one (C43). -/
theorem CapAttr.unrestricted {s : SC} {reg : SyncReg} {c x : Nat} {m : Mode}
    (h : CapAttr s reg c x m) : UnrestrictedAttr s c x m := by
  induction h with
  | base _ hy ha hm hf hin => exact .base hy ha hm hf hin
  | held _ hy ha hm hp _ hc ih => exact .held hy ha hm hp ih hc

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

/-- Unrestricted attribution on attributions (C43, C45): under the frame uniqueness of C3, `I1`
(Spec 1 §50) and `WF3` (Spec 1 §49), an authority attributable to `c` in mode `Modify` with
effective `Modify` on a leaf does not coexist with an authority attributable to another context
`c'` with an effective mode permitting its mode on the same leaf. -/
theorem attr_compat {s : SC} (hnd : s.frames.Nodup) (hI : I1 s.flat) (hw : WF3 s.flat)
    {c c' : Nat} (hcc : c ≠ c') {x : Nat} {m₀ : Mode} (hx : UnrestrictedAttr s c x m₀)
    (hm₀ : m₀ = .modify) :
    ∀ y l m, effective s.flat x l = some .modify → UnrestrictedAttr s c' y m →
      Allows (effective s.flat y l) m → False := by
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
    · exact allows_present hal (effective_exclusive hI hxy hel)
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
        obtain ⟨l', hl'⟩ := exists_mem_footprint hw (s.flat.P.length - p + 1) p (by omega) hu.lt
        exact ih hm₀ _ l' _ (allows_modify (hm₀ ▸ hc l' hl')) hb2 (hc2 l' hl')
    · exact allows_present hal (effective_exclusive hI hxy hel)

/-! ## L1: per-label lemmas -/

/-- Transport of `CapAttr` from `s` to `s'` for context `c`: the
frames of `c` stay live, the footprints of existing places are unchanged, and every authority
attributable to `c` keeps its activity, own mode and holder, stays outside the live `guarded` set,
and keeps an effective mode permitting the mode in which it is attributable (Spec 1 §43;
C43). -/
theorem capAttr_transport {s s' : SC} {reg reg' : SyncReg} {c : Nat} (hw : WF3 s.flat)
    (hstk : ∀ f ∈ s.stk c, f ∈ s'.stk c)
    (hfp : ∀ p, p < s.P.length → footprint s'.P p = footprint s.P p)
    (hA : ∀ u m y, CapAttr s reg c u m → s.A[u]? = some y → ∃ y', s'.A[u]? = some y' ∧
      y'.active = y.active ∧ y'.mode = y.mode ∧ y'.holder = y.holder)
    (hng : ∀ u m, CapAttr s reg c u m → NotGuarded s' reg' u)
    (heff : ∀ u m l, CapAttr s reg c u m → Allows (effective s.flat u l) m →
      Allows (effective s'.flat u l) m)
    {u : Nat} {m : Mode} (h : CapAttr s reg c u m) : CapAttr s' reg' c u m := by
  induction h with
  | @base a m y f hg hy ha hm hf hin =>
    obtain ⟨y', hy', ha', hm', hf'⟩ := hA a m y (.base hg hy ha hm hf hin) hy
    exact .base (hng a m (.base hg hy ha hm hf hin)) hy' (ha'.trans ha) (hm' ▸ hm) (hf'.trans hf)
      (hstk f hin)
  | @held a p b m y hg hy ha hm hp hb hc ih =>
    have hab : CapAttr s reg c a m := .held hg hy ha hm hp hb hc
    obtain ⟨y', hy', ha', hm', hp'⟩ := hA a m y hab hy
    have hu : s.flat.Usable p := by
      have := hw.holders a _ hy ha; rw [hp] at this; exact this
    refine .held (hng a m hab) hy' (ha'.trans ha) (hm' ▸ hm) (hp'.trans hp) ih fun l hl => ?_
    rw [hfp p hu.lt] at hl
    exact heff b m l hb (hc l hl)

/-- `cap` does not decrease when every `CapAt` of `c` on `l` is kept (C43). -/
theorem cap_rank_mono {s s' : SC} {reg reg' : SyncReg} {c l : Nat}
    (h : ∀ m, CapAt s reg c l m → CapAt s' reg' c l m) :
    capRank (cap s reg c l) ≤ capRank (cap s' reg' c l) := by
  unfold cap
  by_cases h1 : CapAt s reg c l .modify
  · simp only [h1, h .modify h1, ↓reduceIte, Nat.le_refl]
  · by_cases h2 : CapAt s reg c l .observe
    · have h2' := h .observe h2
      simp only [h1, h2, h2', ↓reduceIte]
      split <;> simp [capRank]
    · simp only [h1, h2, ↓reduceIte, capRank]; exact Nat.zero_le _

/-- `cap` of `c` does not decrease under the hypotheses of `capAttr_transport`. -/
theorem cap_transport {s s' : SC} {reg reg' : SyncReg} {c : Nat} (hw : WF3 s.flat)
    (hstk : ∀ f ∈ s.stk c, f ∈ s'.stk c)
    (hfp : ∀ p, p < s.P.length → footprint s'.P p = footprint s.P p)
    (hA : ∀ u m y, CapAttr s reg c u m → s.A[u]? = some y → ∃ y', s'.A[u]? = some y' ∧
      y'.active = y.active ∧ y'.mode = y.mode ∧ y'.holder = y.holder)
    (hng : ∀ u m, CapAttr s reg c u m → NotGuarded s' reg' u)
    (heff : ∀ u m l, CapAttr s reg c u m → Allows (effective s.flat u l) m →
      Allows (effective s'.flat u l) m) (l : Nat) :
    capRank (cap s reg c l) ≤ capRank (cap s' reg' c l) := by
  refine cap_rank_mono fun m ⟨x, hx, ha, he⟩ => ⟨x, ?_, capAttr_transport hw hstk hfp hA hng heff ha,
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
identities: `cap` does not decrease. -/
theorem cap_same {s s' : SC} {reg reg' : SyncReg} (hw : WF3 s.flat) (hA : s'.A = s.A)
    (hP : s'.P = s.P) (hC : s'.C = s.C) (hreg : ∀ e' ∈ reg', ∃ e ∈ reg, e.guarded = e'.guarded)
    (c l : Nat) : capRank (cap s reg c l) ≤ capRank (cap s' reg' c l) := by
  have hAf : s'.flat.A = s.flat.A := hA
  refine cap_transport hw (fun f hf => by unfold SC.stk at hf ⊢; rw [hC]; exact hf)
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
`guarded` identities of the registry: `read3`, `write3`, `writeShared` (Spec 1 §66–§68:
initialization states only), `depend` (§64: anchors only), `pin`, `unpin` (§74, §75: pinning
obligations only), `join` (C8: no change), `resetLock` (C18: the grant record only), `newArena`
(Spec 1 §76: the arena registry only), and the atomic step cases (C37: no change; C39: the O11
effect, or no change for a failed compare-and-exchange). -/
def Label.Inert : Label → Prop
  | .kernel _ (.read _ _) | .kernel _ (.write _ _) | .kernel _ (.writeShared _ _)
  | .kernel _ (.depend _ _) | .kernel _ (.pin _) | .kernel _ (.unpin _) | .join _ _
  | .resetLock _ _ | .newArena _ _ _ | .readShared _ _ _ _ _ | .writeShared _ _ _ _ _
  | .cas _ _ _ _ _ _ => True
  | _ => False

/-- The `ok` effect of an inert label (Spec 1 §64, §66–§68, §74–§76; C8, C18). -/
theorem inert_effect {ks : KShared} {L : MutexLayout} {lbl : Label} {st st' : SC × SyncReg × ArenaReg}
    (hi : lbl.Inert) (h : LStep ks L lbl st st') :
    st'.1.A = st.1.A ∧ st'.1.P = st.1.P ∧ st'.1.C = st.1.C ∧
      ∀ e' ∈ st'.2.1, ∃ e ∈ st.2.1, e.guarded = e'.guarded := by
  have same : ∀ (reg : SyncReg), ∀ e' ∈ reg, ∃ e ∈ reg, e.guarded = e'.guarded :=
    fun _ e' he' => ⟨e', he', rfl⟩
  cases h with
  | @kernel s s' reg ar c op hk =>
    cases op <;> simp only [Label.Inert] at hi
    · have hR := hk
      cases hR; exact ⟨rfl, rfl, rfl, same reg⟩
    · obtain ⟨o, hR, ho⟩ := hk
      cases hR with
      | ok => cases ho; exact ⟨rfl, rfl, rfl, same reg⟩
      | reject => cases ho
    · obtain ⟨o, hR, ho⟩ := hk
      cases hR with
      | ok => cases ho; exact ⟨rfl, rfl, rfl, same reg⟩
      | reject => cases ho
    · obtain ⟨o, hR, ho⟩ := hk
      cases hR with
      | ok => cases ho; exact ⟨rfl, rfl, rfl, same reg⟩
      | reject => cases ho
    · obtain ⟨o, hR, ho⟩ := hk
      cases hR with
      | ok => cases ho; exact ⟨rfl, rfl, rfl, same reg⟩
      | reject => cases ho
    · obtain ⟨o, hR, ho⟩ := hk
      cases hR with
      | ok => cases ho; exact ⟨rfl, rfl, rfl, same reg⟩
      | reject => cases ho
  | join hj =>
    cases hj; exact ⟨rfl, rfl, rfl, same _⟩
  | @resetLock s reg ar c i st₁ hr =>
    obtain ⟨e, he, -, -, -, -, rfl⟩ := hr
    refine ⟨rfl, rfl, rfl, fun e' he' => ?_⟩
    rcases List.mem_or_eq_of_mem_set he' with h | h
    · exact ⟨e', h, rfl⟩
    · exact ⟨e, List.mem_of_getElem? he, by rw [h]⟩
  | newArena hn =>
    have hR := hn
    cases hR; exact ⟨rfl, rfl, rfl, same _⟩
  | readShared => exact ⟨rfl, rfl, rfl, same _⟩
  | writeShared hw =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hw; exact ⟨rfl, rfl, rfl, same _⟩
  | cas hc =>
    rcases cas_ok_cases hc with hk | rfl
    · obtain ⟨o, hR, ho⟩ := hk
      cases hR with
      | ok => cases ho; exact ⟨rfl, rfl, rfl, same _⟩
      | reject => cases ho
    · exact ⟨rfl, rfl, rfl, same _⟩
  | _ => simp only [Label.Inert] at hi

/-- L1 (`local_loss`, C45) for the inert labels: from a state reached by an
`EncapsulatedTrace` from an initial state (Spec 1 §47), under `DDSound` (Spec 1 §80), an inert
step lowers no `cap`, so the implication of `local_loss` holds for it. -/
theorem local_loss_inert {ks : KShared} {L : MutexLayout} {statics : Statics} {lbls : List Label}
    {st st' : SC × SyncReg × ArenaReg} {lbl : Label} (hdd : DDSound ks.toK) (hst : StaticsOK statics)
    (htr : EncapsulatedTrace pm ks L (SC.ofS3 (S3.init statics), [], []) lbls st) (hi : lbl.Inert)
    (h : LStep ks L lbl st st') (c l : Nat)
    (hd : capRank (cap st'.1 st'.2.1 c l) < capRank (cap st.1 st.2.1 c l)) : lbl.requester = c := by
  obtain ⟨⟨-, hw⟩, -⟩ := (encapsulated_inv hdd hst htr).1.1
  obtain ⟨hA, hP, hC, hreg⟩ := inert_effect hi h
  exact absurd hd (Nat.not_lt.2 (cap_same hw hA hP hC hreg c l))

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
an authority attributable to `c` (C43): the new authority lowers only the effective modes of
its source and of the source's ancestors on its region, which `attr_compat` and `I1` exclude for
`c` (Spec 1 §43, §50, §60.1, §60.2). -/
theorem derive_eff_keep {s : SC} (hnd : s.frames.Nodup) (hI : I1 s.flat) (hw : WF3 s.flat)
    {c c' src : Nat} {region : List Nat} {md : Mode} (hcc : c ≠ c') (hne : s.stk c' ≠ [])
    (hp : DerivePre (s.view c') src region md) {u : Nat} {m : Mode} (hu : UnrestrictedAttr s c u m)
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
      have hcomp : ∀ m₁, UnrestrictedAttr s c u .modify → effective s.flat u l = some .modify →
          UnrestrictedAttr s c' src m₁ → Allows (effective s.flat src l) m₁ → False :=
        fun m₁ h1 h2 h3 h4 => attr_compat hnd hI hw hcc h1 rfl src l m₁ h2 h3 h4
      have hc'src : UnrestrictedAttr s c' src md := attr_of_exercisable hne hp.exercisable
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

/-- L1 (`local_loss`, C45) for `derive` (Spec 1 §60): from a state reached by an
`EncapsulatedTrace` from an initial state (Spec 1 §47), under `DDSound` (Spec 1 §80), a `derive`
step that strictly lowers `cap` of `c` is a step of `c`. -/
theorem local_loss_derive {ks : KShared} {L : MutexLayout} {statics : Statics} {lbls : List Label}
    {st st' : SC × SyncReg × ArenaReg} {c' src : Nat} {region : List Nat} {mo : Mode}
    (hdd : DDSound ks.toK) (hst : StaticsOK statics)
    (htr : EncapsulatedTrace pm ks L (SC.ofS3 (S3.init statics), [], []) lbls st)
    (h : LStep ks L (.kernel c' (.derive src region mo)) st st') (c l : Nat)
    (hd : capRank (cap st'.1 st'.2.1 c l) < capRank (cap st.1 st.2.1 c l)) :
    (Label.kernel c' (.derive src region mo)).requester = c := by
  obtain ⟨⟨hF, hw⟩, ⟨⟨hI, -⟩, -⟩, -⟩ := (encapsulated_inv hdd hst htr).1.1
  refine Decidable.byContradiction fun hctx => ?_
  have hcc : c ≠ c' := fun e => hctx (e ▸ rfl)
  cases h with
  | @kernel s s' reg ar _ _ hk =>
    have hlive := opStepC_live hk
    obtain ⟨o, hR, ho⟩ := hk
    cases hR with
    | reject => cases ho
    | ok hp =>
      cases ho
      have hne := hF.nonempty c' hlive
      refine absurd hd (Nat.not_lt.2 (cap_transport
        (s' := s.set (deriveEff (s.view c') src region mo)) (reg' := reg) hw (fun f hf => hf)
        (fun p _ => rfl)
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
      · have := derive_eff_keep hF.nodup hI hw hcc hne hp hu.unrestricted hal
        rw [effective_of_A (t := (s.set (deriveEff (s.view c') src region mo)).flat)
          (t' := s.flat.addAuth ⟨mo, some src, region, .frame (s.view c').top, true⟩) rfl]
        exact this

/-- The current frame of a context with a nonempty stack is in its stack (C2). -/
theorem view_top_mem {s : SC} {c : Nat} (hne : s.stk c ≠ []) : (s.view c).top ∈ s.stk c := by
  obtain ⟨f, r, hfr⟩ := List.exists_cons_of_ne_nil hne
  rw [SC.view_top hfr, hfr]; exact List.mem_cons_self ..

/-- An authority held by a frame of another context is not attributable to `c` (C3: frame
identities are globally unique; C43). -/
theorem not_attr_frame {s : SC} (hnd : s.frames.Nodup) {c c' a f : Nat} {m : Mode} {y : Authority}
    (hcc : c ≠ c') (hy : s.A[a]? = some y) (hf : y.holder = .frame f) (hin : f ∈ s.stk c')
    (h : UnrestrictedAttr s c a m) : False := by
  cases h with
  | base hy' _ _ hf' hin' =>
    rw [hy] at hy'; cases hy'; rw [hf] at hf'; cases hf'
    exact hcc (ReparentAux.stk_unique hnd hin' hin)
  | held hy' _ _ hp' => rw [hy] at hy'; cases hy'; rw [hf] at hp'; cases hp'

/-- An authority held by a place on which another context exercises `Modify` with effective
`Modify` (Spec 1 §43, `HasRight`) is not attributable to `c` (C43, C45; `attr_compat`). -/
theorem not_attr_place {s : SC} (hnd : s.frames.Nodup) (hI : I1 s.flat) (hw : WF3 s.flat)
    {c c' a q g : Nat} {m : Mode} {y : Authority} (hcc : c ≠ c') (hy : s.A[a]? = some y)
    (hp : y.holder = .place q) (hg : UnrestrictedAttr s c' g .modify)
    (hge : ∀ l ∈ footprint s.P q, Allows (effective s.flat g l) .modify) (h : UnrestrictedAttr s c a m) :
    False := by
  have hP : ∀ q o, parentOf s.P q = some o → o < q := fun q o h => by
    unfold parentOf at h
    cases hq : s.P[q]? with
    | none => rw [hq] at h; cases h
    | some pl =>
      rw [hq] at h
      obtain ⟨_, _, hlt, _⟩ := hw.places q pl o hq h
      exact hlt
  cases h with
  | base hy' _ _ hf' => rw [hy] at hy'; cases hy'; rw [hp] at hf'; cases hf'
  | held hy' ha _ hp' hb hc =>
    rw [hy] at hy'; cases hy'; rw [hp] at hp'; cases hp'
    have hu : s.flat.Usable q := by
      have := hw.holders a _ hy ha; rw [hp] at this; exact this
    obtain ⟨l, hl⟩ := footprint_ne hP _ q (Nat.le_refl _) hu.lt
    exact attr_compat hnd hI hw (Ne.symm hcc) hg rfl _ l m (allows_modify (hge l hl)) hb (hc l hl)

/-- `store` keeps the skeletons of the authorities (Spec 1 §65, `ok` effect: only the holder
changes). -/
theorem store_skel (t : S3) (a p : Nat) : SameSkel t (storeEff t a p) := by
  unfold storeEff
  split
  · rename_i y hy
    refine ⟨List.length_set .., fun j => ?_⟩
    by_cases hj : j = a
    · subst hj; rw [List.getElem?_set_self (lt_of_getElem? hy), hy]; rfl
    · rw [List.getElem?_set_ne (Ne.symm hj)]
  · exact ⟨rfl, fun _ => rfl⟩

/-- `store` keeps the places (Spec 1 §65, `ok` effect). -/
theorem storeEff_P (t : S3) (a p : Nat) : (storeEff t a p).P = t.P := by
  unfold storeEff; split <;> rfl

/-- Liveness of the entries depends only on activity (C12). -/
theorem notGuarded_of_skel {s s' : SC} {reg reg' : SyncReg} (hs : SameSkel s.flat s'.flat)
    (hreg : ∀ e' ∈ reg', ∃ e ∈ reg, e.guarded = e'.guarded) {u : Nat} (h : NotGuarded s reg u) :
    NotGuarded s' reg' u := fun e' he' hl => by
  obtain ⟨e, he, hg⟩ := hreg e' he'
  refine hg ▸ h e he ?_
  show s.flat.Active e.guarded
  rw [hg]
  obtain ⟨y', hy', hya⟩ := hl
  obtain ⟨y, hy, hsk⟩ := hs.get hy'
  exact ⟨y, hy, by simp [skel] at hsk; rw [← hsk.2.2.2]; exact hya⟩

/-- L1 (`local_loss`, C45) for `store` (Spec 1 §65): the stored authority is held by the
current frame of the actor (§65.1), so it is attributable to no other context; the skeletons are
kept. Under `DDSound` (Spec 1 §80), from a state reached by an `EncapsulatedTrace` from an initial
state (Spec 1 §47). -/
theorem local_loss_store {ks : KShared} {L : MutexLayout} {statics : Statics} {lbls : List Label}
    {st st' : SC × SyncReg × ArenaReg} {c' a p : Nat} (hdd : DDSound ks.toK) (hst : StaticsOK statics)
    (htr : EncapsulatedTrace pm ks L (SC.ofS3 (S3.init statics), [], []) lbls st)
    (h : LStep ks L (.kernel c' (.store a p)) st st') (c l : Nat)
    (hd : capRank (cap st'.1 st'.2.1 c l) < capRank (cap st.1 st.2.1 c l)) :
    (Label.kernel c' (.store a p)).requester = c := by
  obtain ⟨⟨hF, hw⟩, -⟩ := (encapsulated_inv hdd hst htr).1.1
  refine Decidable.byContradiction fun hctx => ?_
  have hcc : c ≠ c' := fun e => hctx (e ▸ rfl)
  cases h with
  | @kernel s s' reg ar _ _ hk =>
    have hlive := opStepC_live hk
    have hR := hk
    cases hR with
    | ok hp =>
      have hne := hF.nonempty c' hlive
      have hsk : SameSkel s.flat (storeEffC s c' a p).flat := store_skel (s.view c') a p
      have hfa : ∀ u m, CapAttr s reg c u m → u ≠ a := fun u m hu hua => by
        subst hua
        have hd := hp.derivedHeld
        unfold OptP at hd
        split at hd
        · rename_i y hy
          exact not_attr_frame (c := c) (c' := c') hF.nodup hcc hy hd.2.2 (view_top_mem hne) hu.unrestricted
        · exact hd.elim
      refine absurd hd (Nat.not_lt.2 (cap_transport (s' := storeEffC s c' a p) (reg' := reg) hw
        (fun f hf => hf)
        (fun q _ => by rw [show (storeEffC s c' a p).P = s.P from storeEff_P _ a p])
        (fun u m y hu hy => ⟨y, ?_, rfl, rfl, rfl⟩)
        (fun u m hu => notGuarded_of_skel hsk (fun e he => ⟨e, he, rfl⟩) hu.notGuarded)
        (fun u m l _ hal => by rw [hsk.effective]; exact hal) l))
      show (storeEff (s.view c') a p).A[u]? = some y
      unfold storeEff
      split
      · rw [List.getElem?_set_ne (Ne.symm (hfa u m hu))]; exact hy
      · exact hy

/-- L1 (`local_loss`, C45) for `transfer` (Spec 1 §63): the authorities whose holder
changes are held by parts of the source, over which the actor exercises `Modify` with effective
`Modify` (§63.1), so they are attributable to no other context (`attr_compat`); the skeletons and
the footprints are kept (§63, `ok` effect). Under `DDSound` (Spec 1 §80), from a state reached by
an `EncapsulatedTrace` from an initial state (Spec 1 §47). -/
theorem local_loss_transfer {ks : KShared} {L : MutexLayout} {statics : Statics} {lbls : List Label}
    {st st' : SC × SyncReg × ArenaReg} {c' src dst : Nat} (hdd : DDSound ks.toK)
    (hst : StaticsOK statics)
    (htr : EncapsulatedTrace pm ks L (SC.ofS3 (S3.init statics), [], []) lbls st)
    (h : LStep ks L (.kernel c' (.transfer src dst)) st st') (c l : Nat)
    (hd : capRank (cap st'.1 st'.2.1 c l) < capRank (cap st.1 st.2.1 c l)) :
    (Label.kernel c' (.transfer src dst)).requester = c := by
  obtain ⟨⟨hF, hw⟩, ⟨⟨hI, -⟩, -⟩, -⟩ := (encapsulated_inv hdd hst htr).1.1
  refine Decidable.byContradiction fun hctx => ?_
  have hcc : c ≠ c' := fun e => hctx (e ▸ rfl)
  cases h with
  | @kernel s s' reg ar _ _ hk =>
    have hlive := opStepC_live hk
    have hR := hk
    cases hR with
    | ok hp =>
      have hne := hF.nonempty c' hlive
      have hsk : SameSkel s.flat (transferEffC s c' src dst).flat :=
        transfer_skel (s.view c') src dst
      obtain ⟨g, -, hgx, hge⟩ := hp.srcRight
      have hg : UnrestrictedAttr s c' g .modify := attr_of_exercisable hne hgx
      have hge' : ∀ l ∈ footprint s.P src, Allows (effective s.flat g l) .modify :=
        fun l hl => by rw [← effective_of_A (t := s.view c') (t' := s.flat) rfl]; exact hge l hl
      have hkeep : ∀ u m y, CapAttr s reg c u m → s.A[u]? = some y → ¬ heldIn s.P src y.holder :=
        fun u m y hu hy hh => by
          cases hh' : y.holder with
          | frame f => rw [hh'] at hh; exact hh
          | place q =>
            rw [hh'] at hh
            exact not_attr_place hF.nodup hI hw hcc hy hh' hg
              (fun l hl => hge' l (footprint_sub hw hh hl)) hu.unrestricted
      refine absurd hd (Nat.not_lt.2 (cap_transport (s' := transferEffC s c' src dst) (reg' := reg)
        hw (fun f hf => hf) (fun p _ => transfer_footprint (s.view c') src dst p)
        (fun u m y hu hy => ⟨y, ?_, rfl, rfl, rfl⟩)
        (fun u m hu => notGuarded_of_skel hsk (fun e he => ⟨e, he, rfl⟩) hu.notGuarded)
        (fun u m l _ hal => by rw [hsk.effective]; exact hal) l))
      show (transferEff (s.view c') src dst).A[u]? = some y
      unfold transferEff
      simp only [List.getElem?_map]
      rw [show (s.view c').A[u]? = some y from hy]
      have hk : ¬ heldIn (s.view c').P src y.holder := hkeep u m y hu hy
      simp [hk]

/-- `NotGuarded` after the addition of one authority (Spec 1 §42: a fresh identity): an entry live
afterwards was live before, or its `guarded` is the fresh identity (C12). -/
theorem notGuarded_addAuth {s s' : SC} {reg reg' : SyncReg} {y₀ : Authority}
    (hA : s'.A = s.A ++ [y₀]) (hreg : ∀ e' ∈ reg', ∃ e ∈ reg, e.guarded = e'.guarded) {u : Nat}
    (hu : u < s.A.length) (h : NotGuarded s reg u) : NotGuarded s' reg' u := fun e' he' hl => by
  obtain ⟨e, he, hg⟩ := hreg e' he'
  obtain ⟨y, hy, hya⟩ := hl
  by_cases hlt : e'.guarded < s.A.length
  · refine hg ▸ h e he ⟨y, ?_, hya⟩
    rw [hg]
    have : s'.A[e'.guarded]? = some y := hy
    rwa [hA, List.getElem?_append_left hlt] at this
  · exact fun h => hlt (h ▸ hu)

/-- Adding a `Modify` descendant of an active `Modify` authority `g` over leaves of `g` keeps the
effective mode of every other authority (Spec 1 §43): the ancestors of `g` already have no
effective mode on those leaves. -/
theorem addModify_keep {t : S3} {g u l : Nat} {x : Authority} {region : List Nat} {m : Mode}
    {hd : Holder} (hx : t.A[g]? = some x) (hxa : x.active = true) (hxm : x.mode = .modify)
    (hreg : ∀ l ∈ region, l ∈ x.footprint) (hulen : u < t.A.length) (hug : u ≠ g)
    (hal : Allows (effective t u l) m) :
    Allows (effective (t.addAuth ⟨.modify, some g, region, hd, true⟩) u l) m := by
  by_cases hl : l ∈ region
  · obtain ⟨z, hz, hza, hzl, -⟩ := eff_present (allows_present hal)
    have hz' : (t.addAuth ⟨.modify, some g, region, hd, true⟩).A[u]? = some z := by
      rw [addAuth_lt hulen]; exact hz
    rw [effective_eq hz' hza hzl, descModes_addAuth,
      ancs_addAuth_self (rfl : (⟨.modify, some g, region, hd, true⟩ : Authority).origin = some g)
        (lt_of_getElem? hx)]
    rw [effective_eq hz hza hzl] at hal
    by_cases hus : u ∈ g :: t.ancs g
    · have hanc : u ∈ t.ancs g := by
        rcases List.mem_cons.1 hus with h | h
        · exact absurd h hug
        · exact h
      have hin : x.mode ∈ descModes t u l := mem_descModes hx hxa (hreg l hl) hanc
      rw [hxm] at hin
      rcases allows_effOf hal with ⟨h0, -⟩ | ⟨hn, -⟩
      · rw [h0] at hin; simp at hin
      · exact absurd hin hn
    · simp only [hus, and_false, ↓reduceIte, List.append_nil]; exact hal
  · rw [effective_addAuth_notin hulen hl]; exact hal

/-- L1 (`local_loss`, C45) for `acquire` (C16): the grant is a `Modify` descendant of
the live `guarded`, which `CapAttr` attributes to no context, and the ancestors of `guarded`, of mode
`Modify` (C15.1), have no effective mode on the protected leaves. Under `DDSound` (Spec 1 §80), from
a state reached by an `EncapsulatedTrace` from an initial state (Spec 1 §47). -/
theorem local_loss_acquire {ks : KShared} {L : MutexLayout} {statics : Statics} {lbls : List Label}
    {st st' : SC × SyncReg × ArenaReg} {c' i : Nat} (hdd : DDSound ks.toK) (hst : StaticsOK statics)
    (htr : EncapsulatedTrace pm ks L (SC.ofS3 (S3.init statics), [], []) lbls st)
    (h : LStep ks L (.acquire c' i) st st') (c l : Nat)
    (hd : capRank (cap st'.1 st'.2.1 c l) < capRank (cap st.1 st.2.1 c l)) :
    (Label.acquire c' i).requester = c := by
  obtain ⟨⟨-, hw⟩, -⟩ := (encapsulated_inv hdd hst htr).1.1
  refine Decidable.byContradiction fun hctx => ?_
  cases h with
  | @acquire s reg ar _ _ st₁ ha =>
    obtain ⟨e, hei, hauth, hpre, rfl⟩ := ha
    have he : e ∈ reg := List.mem_of_getElem? hei
    have hreg : ∀ e' ∈ reg.set i { e with grant := some s.A.length }, ∃ e₀ ∈ reg,
        e₀.guarded = e'.guarded := fun e' he' => by
      rcases List.mem_or_eq_of_mem_set he' with h | h
      · exact ⟨e', h, rfl⟩
      · exact ⟨e, he, by rw [h]⟩
    obtain ⟨x, hx, hxa⟩ := hpre.active
    have hxm : x.mode = .modify := by
      have := hpre.mode; unfold OptP at this; rw [show (s.view c').A[e.guarded]? = some x from hx]
        at this
      rcases this with h | h
      · cases h
      · exact h
    have hlen : ∀ u m, CapAttr s reg c u m → u < s.A.length := fun u m hu => by
      cases hu with
      | base _ hy => exact lt_of_getElem? hy
      | held _ hy => exact lt_of_getElem? hy
    refine absurd hd (Nat.not_lt.2 (cap_transport (s' := deriveSyncEff s c' e.guarded)
      (reg' := reg.set i { e with grant := some s.A.length }) hw (fun f hf => hf) (fun p _ => rfl)
      (fun u m y hu hy => ⟨y, ?_, rfl, rfl, rfl⟩)
      (fun u m hu => notGuarded_addAuth rfl hreg (hlen u m hu) hu.notGuarded)
      (fun u m l hu hal => ?_) l))
    · show (deriveEff (s.view c') e.guarded ((s.view c').afp e.guarded) .modify).A[u]? = some y
      rw [deriveEff, addAuth_lt (hlen u m hu)]; exact hy
    · have hug : u ≠ e.guarded := fun h' => hu.notGuarded e he hauth.1 h'
      have hafp : (s.view c').afp e.guarded = x.footprint := by
        unfold S3.afp; rw [show (s.view c').A[e.guarded]? = some x from hx]
      have := addModify_keep (t := s.flat) (hd := .frame (s.view c').top)
        (region := (s.view c').afp e.guarded) hx hxa hxm (fun l hl => hafp ▸ hl) (hlen u m hu) hug
        hal
      rw [effective_of_A (t := (deriveSyncEff s c' e.guarded).flat)
        (t' := s.flat.addAuth ⟨.modify, some e.guarded, (s.view c').afp e.guarded,
          .frame (s.view c').top, true⟩) rfl]
      exact this

/-- L1 for the raw `deriveSync` (C15): an `EncapStep` admits no such `ok` step, since
`SyncAuthorized` of the library holds only for the `guarded` of a live entry (C14, `libKC_sound`)
and C22.2 excludes it. -/
theorem local_loss_deriveSync {ks : KShared} {L : MutexLayout} {st st' : SC × SyncReg × ArenaReg}
    {c' g : Nat} (he : EncapStep pm ks L st (.deriveSync c' g) st')
    (h : LStep ks L (.deriveSync c' g) st st') (c : Nat) : (Label.deriveSync c' g).requester = c := by
  exfalso
  cases h with
  | @deriveSync s s' reg ar _ _ hs =>
    have hrs : ∀ e ∈ reg, e.Live s → g ≠ e.guarded := he.1
    have hR := hs
    cases hR with
    | ok hp =>
      obtain ⟨e, hmem, hg, hl⟩ := libKC_sound ks L reg s _ _ hp.authorized
      exact hrs e hmem hl hg.symm

/-- Fewer covering descendants keep an allowed mode (Spec 1 §43). -/
theorem allows_effOf_sub {o m : Mode} {ds ds' : List Mode} (hs : ∀ x ∈ ds', x ∈ ds)
    (h : Allows (effOf o ds) m) : Allows (effOf o ds') m := by
  rcases allows_effOf h with ⟨h0, hm⟩ | ⟨hn, rfl⟩
  · have : ds' = [] := by
      cases ds' with
      | nil => rfl
      | cons x _ => have := hs x (List.mem_cons_self ..); rw [h0] at this; simp at this
    rw [this]; unfold effOf; simp only [↓reduceIte]; exact hm
  · unfold effOf
    split
    · rcases o with _ | _ <;> exact Or.inl rfl
    · have hn' : Mode.modify ∉ ds' := fun h => hn (hs _ h)
      simp only [hn', ↓reduceIte]; exact Or.inl rfl

/-- `release` keeps the origins (Spec 1 §62, `ok` effect: only the activity changes). -/
theorem release_org (t : S3) (a : Nat) : (releaseEff t a).org = t.org := by
  funext i
  unfold releaseEff
  split
  · rename_i x hx
    unfold S3.org
    by_cases hi : i = a
    · subst hi; rw [List.getElem?_set_self (lt_of_getElem? hx), hx]; rfl
    · rw [List.getElem?_set_ne (Ne.symm hi)]
  · rfl

/-- `release` of `a` keeps the effective mode allowed to any other authority (Spec 1 §43, §62:
the released authority stops covering, so effective modes can only rise). -/
theorem release_eff_mono {t : S3} {a u l : Nat} {m : Mode} (hua : u ≠ a)
    (h : Allows (effective t u l) m) : Allows (effective (releaseEff t a) u l) m := by
  obtain ⟨z, hz, hza, hzl, -⟩ := eff_present (allows_present h)
  have hA : ∀ j, j ≠ a → (releaseEff t a).A[j]? = t.A[j]? := fun j hj => by
    unfold releaseEff; split
    · exact List.getElem?_set_ne (Ne.symm hj)
    · rfl
  have hz' : (releaseEff t a).A[u]? = some z := by rw [hA u hua]; exact hz
  rw [effective_eq hz hza hzl] at h
  rw [effective_eq hz' hza hzl]
  refine allows_effOf_sub (fun md hmd => ?_) h
  obtain ⟨j, y, hy, hya, hyl, hj, rfl⟩ := Ern.MemoryModel.Access.mem_descModes.1 hmd
  have hja : j ≠ a := fun hja => by
    subst hja
    unfold releaseEff at hy
    split at hy
    · rename_i x hx
      rw [List.getElem?_set_self (lt_of_getElem? hx)] at hy; cases hy; simp at hya
    · rename_i hx; rw [hx] at hy; cases hy
  have hanc : u ∈ t.ancs j := by
    have : (releaseEff t a).ancs j = t.ancs j := by unfold S3.ancs; rw [release_org]
    rwa [this] at hj
  exact Ern.MemoryModel.Access.mem_descModes.2
    ⟨j, y, by rw [← hA j hja]; exact hy, hya, hyl, hanc, rfl⟩

/-- `release` of `a` by context `c'` (Spec 1 §62) does not lower `cap` of another context `c`:
`a` is held by the current frame of `c'` or by a place on which `c'` exercises `Modify` (§62.2),
so it is attributable to no other context (`not_attr_frame`, `not_attr_place`). -/
theorem release_cap_mono {s : SC} {reg reg' : SyncReg} (hF : FramesC s) (hI : I1 s.flat)
    (hw : WF3 s.flat) {c c' a : Nat} (hcc : c ≠ c') (hlive : s.Live c')
    (hp : ReleasePre (s.view c') a) (hreg : ∀ e' ∈ reg', ∃ e ∈ reg, e.guarded = e'.guarded)
    (l : Nat) :
    capRank (cap s reg c l) ≤ capRank (cap (s.set (releaseEff (s.view c') a)) reg' c l) := by
  have hne := hF.nonempty c' hlive
  have hfa : ∀ u m, CapAttr s reg c u m → u ≠ a := fun u m hu hua => by
    subst hua
    have hh := hp.holderRight
    unfold OptP at hh
    split at hh
    · rename_i y hy
      cases hyh : y.holder with
      | frame f =>
        rw [hyh] at hh
        exact not_attr_frame (c := c) (c' := c') hF.nodup hcc hy hyh (hh ▸ view_top_mem hne) hu.unrestricted
      | place q =>
        rw [hyh] at hh
        obtain ⟨g, -, hgx, hge⟩ := hh
        exact not_attr_place hF.nodup hI hw hcc hy hyh (attr_of_exercisable hne hgx)
          (fun l hl => by rw [← effective_of_A (t := s.view c') (t' := s.flat) rfl]; exact hge l hl)
          hu.unrestricted
    · exact hh.elim
  have hA : ∀ j, j ≠ a → (releaseEff (s.view c') a).A[j]? = s.A[j]? := fun j hj => by
    unfold releaseEff; split
    · exact List.getElem?_set_ne (Ne.symm hj)
    · rfl
  refine cap_transport (s' := s.set (releaseEff (s.view c') a)) (reg' := reg') hw (fun f hf => hf)
    (fun q _ => by
      show footprint (releaseEff (s.view c') a).P q = _; unfold releaseEff; split <;> rfl)
    (fun u m y hu hy => ⟨y, by rw [show (s.set _).A[u]? = _ from hA u (hfa u m hu)]; exact hy, rfl,
      rfl, rfl⟩) (fun u m hu e' he' hl => ?_) (fun u m l hu hal => ?_) l
  · obtain ⟨e, he, hg⟩ := hreg e' he'
    refine hg ▸ hu.notGuarded e he ?_
    obtain ⟨y, hy, hya⟩ := hl
    show s.flat.Active e.guarded
    rw [hg]
    by_cases hga : e'.guarded = a
    · have : (releaseEff (s.view c') a).A[e'.guarded]? = some y := hy
      rw [hga] at this
      unfold releaseEff at this
      split at this
      · rename_i x hx
        rw [List.getElem?_set_self (lt_of_getElem? hx)] at this; cases this; simp at hya
      · rename_i hx; rw [hx] at this; cases this
    · have h2 : (releaseEff (s.view c') a).A[e'.guarded]? = some y := hy
      rw [hA _ hga] at h2
      exact ⟨y, h2, hya⟩
  · have := release_eff_mono (t := s.view c') (hfa u m hu)
      (by rw [effective_of_A (t := s.view c') (t' := s.flat) rfl]; exact hal)
    rwa [effective_of_A (t := releaseEff (s.view c') a)
      (t' := (s.set (releaseEff (s.view c') a)).flat) rfl] at this

/-- L1 (`local_loss`, C45) for `release` (Spec 1 §62). Under `DDSound` (Spec 1 §80), from a
state reached by an `EncapsulatedTrace` from an initial state (Spec 1 §47). -/
theorem local_loss_release {ks : KShared} {L : MutexLayout} {statics : Statics} {lbls : List Label}
    {st st' : SC × SyncReg × ArenaReg} {c' a : Nat} (hdd : DDSound ks.toK) (hst : StaticsOK statics)
    (htr : EncapsulatedTrace pm ks L (SC.ofS3 (S3.init statics), [], []) lbls st)
    (h : LStep ks L (.kernel c' (.release a)) st st') (c l : Nat)
    (hd : capRank (cap st'.1 st'.2.1 c l) < capRank (cap st.1 st.2.1 c l)) :
    (Label.kernel c' (.release a)).requester = c := by
  obtain ⟨⟨hF, hw⟩, ⟨⟨hI, -⟩, -⟩, -⟩ := (encapsulated_inv hdd hst htr).1.1
  refine Decidable.byContradiction fun hctx => ?_
  have hcc : c ≠ c' := fun e => hctx (e ▸ rfl)
  cases h with
  | @kernel s s' reg ar _ _ hk =>
    have hlive := opStepC_live hk
    obtain ⟨o, hR, ho⟩ := hk
    cases hR with
    | reject => cases ho
    | ok hp =>
      cases ho
      exact absurd hd (Nat.not_lt.2 (release_cap_mono hF hI hw hcc hlive hp
        (fun e he => ⟨e, he, rfl⟩) l))

/-- L1 (`local_loss`, C45) for `unlock` (C17): the grant is released by O3 (C17.2,
C17.3) and the registry keeps its `guarded` identities. Under `DDSound` (Spec 1 §80), from a state
reached by an `EncapsulatedTrace` from an initial state (Spec 1 §47). -/
theorem local_loss_unlock {ks : KShared} {L : MutexLayout} {statics : Statics} {lbls : List Label}
    {st st' : SC × SyncReg × ArenaReg} {c' i : Nat} (hdd : DDSound ks.toK) (hst : StaticsOK statics)
    (htr : EncapsulatedTrace pm ks L (SC.ofS3 (S3.init statics), [], []) lbls st)
    (h : LStep ks L (.unlock c' i) st st') (c l : Nat)
    (hd : capRank (cap st'.1 st'.2.1 c l) < capRank (cap st.1 st.2.1 c l)) :
    (Label.unlock c' i).requester = c := by
  obtain ⟨⟨hF, hw⟩, ⟨⟨hI, -⟩, -⟩, -⟩ := (encapsulated_inv hdd hst htr).1.1
  refine Decidable.byContradiction fun hctx => ?_
  have hcc : c ≠ c' := fun e => hctx (e ▸ rfl)
  cases h with
  | @unlock s reg ar _ _ st₁ hu =>
    have hlive : s.Live c' := lstep_live (LStep.unlock (ks := ks) (ar := ar) hu)
    obtain ⟨e, g, hei, -, -, hp, -, -, rfl⟩ := hu
    have he : e ∈ reg := List.mem_of_getElem? hei
    exact absurd hd (Nat.not_lt.2 (release_cap_mono hF hI hw hcc hlive hp (fun e' he' => by
      rcases List.mem_or_eq_of_mem_set he' with h | h
      · exact ⟨e', h, rfl⟩
      · exact ⟨e, he, by rw [h]⟩) l))

/-- One authority attributable in `Modify` to `c'` and attributable to another context `c`
contradicts `attr_compat` (C43, C45), whatever its footprint. -/
theorem attr_excl {s : SC} (hnd : s.frames.Nodup) (hI : I1 s.flat) (hw : WF3 s.flat)
    {c c' x : Nat} {m : Mode} (hcc : c ≠ c') (hx' : UnrestrictedAttr s c' x .modify) (hx : UnrestrictedAttr s c x m) :
    False := by
  cases hx' with
  | base hy _ _ hf hin => exact not_attr_frame hnd hcc hy hf hin hx
  | held hy ha _ hp hb hc =>
    exact not_attr_place hnd hI hw hcc hy hp hb (fun l hl => hc l hl) hx

/-- L1 (`local_loss`, C45) for `newMutex` (C13): the new `guarded` ceases to be
attributable, and it is attributable to no context but the actor, which exercises `Modify` over it
(C13.2; `attr_excl`); the kernel state is unchanged. Under `DDSound` (Spec 1 §80), from a state
reached by an `EncapsulatedTrace` from an initial state (Spec 1 §47). -/
theorem local_loss_newMutex {ks : KShared} {L : MutexLayout} {statics : Statics} {lbls : List Label}
    {st st' : SC × SyncReg × ArenaReg} {c' g : Nat} (hdd : DDSound ks.toK) (hst : StaticsOK statics)
    (htr : EncapsulatedTrace pm ks L (SC.ofS3 (S3.init statics), [], []) lbls st)
    (h : LStep ks L (.newMutex c' g) st st') (c l : Nat)
    (hd : capRank (cap st'.1 st'.2.1 c l) < capRank (cap st.1 st.2.1 c l)) :
    (Label.newMutex c' g).requester = c := by
  obtain ⟨⟨hF, hw⟩, ⟨⟨hI, -⟩, -⟩, -⟩ := (encapsulated_inv hdd hst htr).1.1
  refine Decidable.byContradiction fun hctx => ?_
  have hcc : c ≠ c' := fun e => hctx (e ▸ rfl)
  cases h with
  | @newMutex s reg ar _ _ st₁ hn =>
    obtain ⟨hp, rfl⟩ := hn
    have hlive : s.Live c' := SC.live_of_exercisable hp.exercisable
    have hg : UnrestrictedAttr s c' g .modify := attr_of_exercisable (hF.nonempty c' hlive) hp.exercisable
    refine absurd hd (Nat.not_lt.2 (cap_transport (s' := s) (reg' := reg ++ [⟨g, none⟩]) hw
      (fun f hf => hf) (fun p _ => rfl) (fun u m y _ hy => ⟨y, hy, rfl, rfl, rfl⟩)
      (fun u m hu e he hl => ?_) (fun u m l _ hal => hal) l))
    rcases List.mem_append.1 he with he | he
    · exact hu.notGuarded e he hl
    · rw [List.mem_singleton.1 he]
      exact fun hug => attr_excl hF.nodup hI hw hcc hg (hug ▸ hu.unrestricted)

/-! ## Transport restricted to useful authorities -/

/-- An authority attributable in mode `m` contributes somewhere: its effective mode permits `m`
on some leaf (Spec 1 §43; C43). -/
def Useful (s : SC) (u : Nat) (m : Mode) : Prop := ∃ l, Allows (effective s.flat u l) m

/-- Parents precede their children (Spec 1 §49.2). -/
theorem parents_lt {t : S3} (hw : WF3 t) : ∀ q o, parentOf t.P q = some o → o < q := fun q o h => by
  unfold parentOf at h
  cases hq : t.P[q]? with
  | none => rw [hq] at h; cases h
  | some pl =>
    rw [hq] at h
    obtain ⟨_, _, hlt, _⟩ := hw.places q pl o hq h
    exact hlt

/-- Transport of `CapAttr` from `s` to `s'` for context `c`, for the useful authorities only
(C43): the frames of `c` stay live, the footprints of existing places do not grow, and every useful authority attributable to `c` keeps its activity, own mode and
holder, stays outside the live `guarded` set, and keeps an effective mode permitting the mode in
which it is attributable. -/
theorem capAttr_transport_u {s s' : SC} {reg reg' : SyncReg} {c : Nat} (hw : WF3 s.flat)
    (hstk : ∀ f ∈ s.stk c, f ∈ s'.stk c)
    (hfp : ∀ p, p < s.P.length → ∀ l ∈ footprint s'.P p, l ∈ footprint s.P p)
    (hA : ∀ u m y, CapAttr s reg c u m → Useful s u m → s.A[u]? = some y → ∃ y', s'.A[u]? = some y' ∧
      y'.active = y.active ∧ y'.mode = y.mode ∧ y'.holder = y.holder)
    (hng : ∀ u m, CapAttr s reg c u m → Useful s u m → NotGuarded s' reg' u)
    (heff : ∀ u m l, CapAttr s reg c u m → Allows (effective s.flat u l) m →
      Allows (effective s'.flat u l) m)
    {u : Nat} {m : Mode} (h : CapAttr s reg c u m) (hu : Useful s u m) : CapAttr s' reg' c u m := by
  have hP := parents_lt hw
  induction h with
  | @base a m y f hg hy ha hm hf hin =>
    have hab : CapAttr s reg c a m := .base hg hy ha hm hf hin
    obtain ⟨y', hy', ha', hm', hf'⟩ := hA a m y hab hu hy
    exact .base (hng a m hab hu) hy' (ha'.trans ha) (hm' ▸ hm) (hf'.trans hf) (hstk f hin)
  | @held a p b m y hg hy ha hm hp hb hc ih =>
    have hab : CapAttr s reg c a m := .held hg hy ha hm hp hb hc
    obtain ⟨y', hy', ha', hm', hp'⟩ := hA a m y hab hu hy
    have hup : s.flat.Usable p := by
      have := hw.holders a _ hy ha; rw [hp] at this; exact this
    obtain ⟨l₀, hl₀⟩ := footprint_ne hP _ p (Nat.le_refl _) hup.lt
    refine .held (hng a m hab hu) hy' (ha'.trans ha) (hm' ▸ hm) (hp'.trans hp)
      (ih ⟨l₀, hc l₀ hl₀⟩) fun l hl => heff b m l hb (hc l (hfp p hup.lt l hl))

/-- `cap` of `c` does not decrease under the hypotheses of `capAttr_transport_u`. -/
theorem cap_transport_u {s s' : SC} {reg reg' : SyncReg} {c : Nat} (hw : WF3 s.flat)
    (hstk : ∀ f ∈ s.stk c, f ∈ s'.stk c)
    (hfp : ∀ p, p < s.P.length → ∀ l ∈ footprint s'.P p, l ∈ footprint s.P p)
    (hA : ∀ u m y, CapAttr s reg c u m → Useful s u m → s.A[u]? = some y → ∃ y', s'.A[u]? = some y' ∧
      y'.active = y.active ∧ y'.mode = y.mode ∧ y'.holder = y.holder)
    (hng : ∀ u m, CapAttr s reg c u m → Useful s u m → NotGuarded s' reg' u)
    (heff : ∀ u m l, CapAttr s reg c u m → Allows (effective s.flat u l) m →
      Allows (effective s'.flat u l) m) (l : Nat) :
    capRank (cap s reg c l) ≤ capRank (cap s' reg' c l) := by
  refine cap_rank_mono fun m ⟨x, hx, ha, he⟩ =>
    ⟨x, ?_, capAttr_transport_u hw hstk hfp hA hng heff ha ⟨l, he⟩, heff x m l ha he⟩
  have hlt := List.mem_range.1 hx
  obtain ⟨y, hy⟩ : ∃ y, s.A[x]? = some y := ⟨_, List.getElem?_eq_getElem hlt⟩
  obtain ⟨y', hy', -⟩ := hA x m y ha ⟨l, he⟩ hy
  exact List.mem_range.2 (lt_of_getElem? hy')

/-- A context without frames has no `cap` (C43: attribution ends at a live frame). -/
theorem cap_nil {s : SC} {reg : SyncReg} {c l : Nat} (h : s.stk c = []) :
    cap s reg c l = none := by
  have hno : ∀ u m, ¬ CapAttr s reg c u m := fun u m hu => by
    induction hu with
    | base _ _ _ _ _ hin => rw [h] at hin; simp at hin
    | held _ _ _ _ _ _ _ ih => exact ih
  unfold cap
  have h1 : ¬ CapAt s reg c l .modify := fun ⟨x, _, hx, _⟩ => hno x _ hx
  have h2 : ¬ CapAt s reg c l .observe := fun ⟨x, _, hx, _⟩ => hno x _ hx
  simp only [h1, h2, ↓reduceIte]

/-- Fewer covering descendants keep an allowed mode (Spec 1 §43): if every active descendant of
`u` covering `l` in `t'` was an active descendant of `u` covering `l` in `t`, with the same mode,
and `u` keeps its activity, mode and footprint, an effective mode allowed in `t` is allowed in
`t'`. -/
theorem eff_keep_sub {t t' : S3} {u l : Nat} {m : Mode}
    (hu : ∀ z, t.A[u]? = some z → ∃ z', t'.A[u]? = some z' ∧ z'.active = z.active ∧
      z'.mode = z.mode ∧ z'.footprint = z.footprint)
    (hd : ∀ j y, t'.A[j]? = some y → y.active = true → l ∈ y.footprint → u ∈ t'.ancs j →
      ∃ y₀, t.A[j]? = some y₀ ∧ y₀.active = true ∧ l ∈ y₀.footprint ∧ u ∈ t.ancs j ∧
        y₀.mode = y.mode)
    (h : Allows (effective t u l) m) : Allows (effective t' u l) m := by
  obtain ⟨z, hz, hza, hzl, -⟩ := eff_present (allows_present h)
  obtain ⟨z', hz', ha', hm', hf'⟩ := hu z hz
  rw [effective_eq hz hza hzl] at h
  rw [effective_eq hz' (ha'.trans hza) (hf' ▸ hzl), hm']
  refine allows_effOf_sub (fun md hmd => ?_) h
  obtain ⟨j, y, hy, hya, hyl, hj, rfl⟩ := Ern.MemoryModel.Access.mem_descModes.1 hmd
  obtain ⟨y₀, hy₀, h1, h2, h3, h4⟩ := hd j y hy hya hyl hj
  exact Ern.MemoryModel.Access.mem_descModes.2 ⟨j, y₀, hy₀, h1, h2, h3, h4⟩

/-- An active `Modify` authority covering `l` below `u` leaves `u` no effective mode on `l`
(Spec 1 §43, case 3). -/
theorem no_eff_below_modify {t : S3} {src u l : Nat} {x : Authority} {m : Mode}
    (hx : t.A[src]? = some x) (hxa : x.active = true) (hxm : x.mode = .modify)
    (hxl : l ∈ x.footprint) (hanc : u ∈ t.ancs src) (h : Allows (effective t u l) m) : False := by
  obtain ⟨z, hz, hza, hzl, -⟩ := eff_present (allows_present h)
  rw [effective_eq hz hza hzl] at h
  have hin : x.mode ∈ descModes t u l := mem_descModes hx hxa hxl hanc
  rw [hxm] at hin
  rcases allows_effOf h with ⟨h0, -⟩ | ⟨hn, -⟩
  · rw [h0] at hin; simp at hin
  · exact hn hin

/-- `NotGuarded` when the former authorities keep their activity (C12): an entry live
afterwards was live before, or its `guarded` is a fresh identity. -/
theorem notGuarded_prefix {s s' : SC} {reg : SyncReg}
    (hact : ∀ j < s.A.length, ∀ y', s'.A[j]? = some y' → y'.active = true → s.flat.Active j)
    {u : Nat} (hu : u < s.A.length) (h : NotGuarded s reg u) : NotGuarded s' reg u :=
  fun e he hl => by
    obtain ⟨y', hy', hya⟩ := hl
    by_cases hlt : e.guarded < s.A.length
    · exact h e he (hact _ hlt y' hy' hya)
    · exact fun h' => hlt (h' ▸ hu)

/-- An attributable authority exists (C43). -/
theorem CapAttr.lt {s : SC} {reg : SyncReg} {c u : Nat} {m : Mode} (h : CapAttr s reg c u m) :
    u < s.A.length := by
  cases h with
  | base _ hy => exact lt_of_getElem? hy
  | held _ hy => exact lt_of_getElem? hy

/-- Origin chains of the former authorities are kept when their origins are (Spec 1 §42). -/
theorem ancs_prefix {t t' : S3} (hold : ∀ i < t.A.length, t'.org i = t.org i) {j : Nat}
    (hj : j < t.A.length) : t'.ancs j = t.ancs j :=
  chain_congr fun i hi => hold i (Nat.lt_of_le_of_lt hi hj)

/-! ## `split` (Spec 1 §61) -/

/-- The authorities after `split` (Spec 1 §61, `ok` effect): the former ones, then one `Modify`
descendant of `src` per region. -/
theorem split_get {t : S3} {src : Nat} {rs : List (List Nat)} {j : Nat} {y : Authority}
    (h : (splitEff t src rs).A[j]? = some y) :
    (j < t.A.length ∧ t.A[j]? = some y) ∨
    (t.A.length ≤ j ∧ ∃ r ∈ rs, y = ⟨.modify, some src, r, .frame t.top, true⟩) := by
  simp only [splitEff] at h
  by_cases hj : j < t.A.length
  · rw [List.getElem?_append_left hj] at h; exact .inl ⟨hj, h⟩
  · rw [List.getElem?_append_right (by omega), List.getElem?_map] at h
    cases hr : rs[j - t.A.length]? with
    | none => rw [hr] at h; cases h
    | some r =>
      rw [hr] at h; cases h
      exact .inr ⟨by omega, r, List.mem_of_getElem? hr, rfl⟩

/-- `split` by context `c'` (Spec 1 §61) does not lower `cap` of another context `c`: the new
authorities are `Modify` descendants of the source over leaves where the source has effective
`Modify` (§61.1), which excludes, for `c`, the source (`attr_compat`) and its ancestors (Spec 1
§43, case 3). -/
theorem split_cap_mono {k : K} {s : SC} {reg : SyncReg} (hF : FramesC s) (hI : I1 s.flat)
    (hw : WF3 s.flat) {c c' src : Nat} {rs : List (List Nat)} (hcc : c ≠ c') (hlive : s.Live c')
    (hp : SplitPre k (s.view c') src rs) (l : Nat) :
    capRank (cap s reg c l) ≤ capRank (cap (s.set (splitEff (s.view c') src rs)) reg c l) := by
  have hne := hF.nonempty c' hlive
  have hvA : ∀ a l, effective (s.view c') a l = effective s.flat a l :=
    fun a l => effective_of_A rfl a l
  have hc'src : UnrestrictedAttr s c' src .modify := attr_of_exercisable hne hp.exercisable
  obtain ⟨x, hx, hxa⟩ := hp.active
  have hxm : x.mode = .modify := by
    rcases exer_mode hp.exercisable hx with h | h
    · cases h
    · exact h
  have hsl : src < s.A.length := lt_of_getElem? hx
  have hpre : ∀ j < s.A.length, (splitEff (s.view c') src rs).A[j]? = s.A[j]? :=
    fun j hj => List.getElem?_append_left hj
  have horg : ∀ i < (s.view c').A.length, (splitEff (s.view c') src rs).org i = (s.view c').org i :=
    fun i hi => by unfold S3.org; rw [hpre i hi]; rfl
  refine cap_transport_u (s' := s.set (splitEff (s.view c') src rs)) (reg' := reg) hw
    (fun f hf => hf) (fun p _ l hl => hl)
    (fun u m y hu _ hy => ⟨y, (by show (splitEff (s.view c') src rs).A[u]? = _
                                  rw [hpre u hu.lt]; exact hy), rfl, rfl, rfl⟩)
    (fun u m hu _ => notGuarded_prefix (fun j hj y' hy' hya => ⟨y', by
        have : (splitEff (s.view c') src rs).A[j]? = some y' := hy'
        rwa [hpre j hj] at this, hya⟩) hu.lt hu.notGuarded)
    (fun u m l hu hal => ?_) l
  show Allows (effective (splitEff (s.view c') src rs) u l) m
  rw [← hvA] at hal
  refine eff_keep_sub (fun z hz => ⟨z, by rw [hpre u hu.lt]; exact hz, rfl, rfl, rfl⟩)
    (fun j y hy hya hyl hj => ?_) hal
  rcases split_get hy with ⟨hjl, hy'⟩ | ⟨hjl, r, hr, rfl⟩
  · exact ⟨y, hy', hya, hyl, by rwa [ancs_prefix horg hjl] at hj, rfl⟩
  · exfalso
    have horg' : (splitEff (s.view c') src rs).org j = some src := by
      unfold S3.org; rw [hy]; rfl
    have hanc : (splitEff (s.view c') src rs).ancs j = src :: (s.view c').ancs src := by
      unfold S3.ancs
      rw [chain_cons horg' (by have : (s.view c').A.length = s.A.length := rfl; omega)]
      exact congrArg _ (ancs_prefix horg hsl)
    rw [hanc] at hj
    have hmod : effective s.flat src l = some .modify := by rw [← hvA]; exact hp.modifyOn r hr l hyl
    rcases List.mem_cons.1 hj with rfl | hanc'
    · exact attr_compat hF.nodup hI hw (Ne.symm hcc) hc'src rfl _ l m hmod hu.unrestricted
        (by rw [← hvA]; exact hal)
    · have hxl : l ∈ x.footprint := by
        have := (hp.within r hr l hyl).1; unfold S3.afp at this; rw [hx] at this; exact this
      exact no_eff_below_modify hx hxa hxm hxl hanc' hal

/-! ## `alloc` (Spec 1 §71) -/

/-- `alloc` by context `c'` (Spec 1 §71) does not lower `cap` of another context: the new root
authority has no origin, so it is a descendant of nothing, and the footprints of the former places
are kept (§71, `ok` effect). -/
theorem alloc_cap_mono {k : K} {s : SC} {reg : SyncReg} (hw : WF3 s.flat) {c c' pr ow : Nat}
    {ls : LocalShape} (hst : AllocStatic k (s.view c') pr ow ls) (l : Nat) :
    capRank (cap s reg c l) ≤ capRank (cap (s.set (allocEff (s.view c') ow ls)) reg c l) := by
  have hvA : ∀ a l, effective (s.view c') a l = effective s.flat a l :=
    fun a l => effective_of_A rfl a l
  have hpre : ∀ j < s.A.length, (allocEff (s.view c') ow ls).A[j]? = s.A[j]? :=
    fun j hj => Alloc.A_lt hj
  refine cap_transport_u (s' := s.set (allocEff (s.view c') ow ls)) (reg' := reg) hw
    (fun f hf => hf)
    (fun p hp l hl => (Alloc.footprint_old (s := s.view c') hst.shapeOK hp l).1 hl)
    (fun u m y hu _ hy => ⟨y, (by show (allocEff (s.view c') ow ls).A[u]? = _
                                  rw [hpre u hu.lt]; exact hy), rfl, rfl, rfl⟩)
    (fun u m hu _ => notGuarded_prefix (fun j hj y' hy' hya => ⟨y', by
        have : (allocEff (s.view c') ow ls).A[j]? = some y' := hy'
        rwa [hpre j hj] at this, hya⟩) hu.lt hu.notGuarded)
    (fun u m l hu hal => ?_) l
  show Allows (effective (allocEff (s.view c') ow ls) u l) m
  rw [← hvA] at hal
  refine eff_keep_sub (fun z hz => ⟨z, by rw [hpre u hu.lt]; exact hz, rfl, rfl, rfl⟩)
    (fun j y hy hya hyl hj => ?_) hal
  rw [Alloc.ancs_eq hst] at hj
  rcases Alloc.allocA_get hst hy with ⟨-, hy'⟩ | ⟨rfl, rfl⟩
  · exact ⟨y, hy', hya, hyl, hj, rfl⟩
  · exfalso
    have : (s.view c').org (s.view c').A.length = none := by
      unfold S3.org; rw [List.getElem?_eq_none (Nat.le_refl _)]; rfl
    rw [S3.ancs, chain_none this] at hj; simp at hj

/-! ## `enterFrame` and `spawn` (Spec 1 §72; C4) -/

/-- The kernel effect of `enterFrame` executed by `c'` (Spec 1 §72), read from another context `c`
holding none of the parameters: `cap` of `c` does not decrease when the stack of `c` and the
registry are kept. The parameters are held by the current frame of `c'` (§72.1), the new root
authorities have no origin, and the footprints of the former places are kept (§72, `ok`
effect). -/
theorem enter_cap_mono {s s' : SC} {reg : SyncReg} (hF : FramesC s) (hw : WF3 s.flat)
    {c c' : Nat} {ps : List Nat} {ls : LocalShape} (hcc : c ≠ c') (hne : s.stk c' ≠ [])
    (hparams : ∀ a ∈ ps, OptP ((s.view c').A[a]?) (fun y => y.active = true ∧
      y.holder = .frame (s.view c').top ∧ y.origin ≠ none) False)
    (hsh : ShapeOK s.P.length ls.toShape)
    (hk : s'.A = (enterEff (s.view c') ps ls).A ∧ s'.P = (enterEff (s.view c') ps ls).P)
    (hstk : ∀ f ∈ s.stk c, f ∈ s'.stk c) (l : Nat) :
    capRank (cap s reg c l) ≤ capRank (cap s' reg c l) := by
  have hvA : ∀ a l, effective (s.view c') a l = effective s.flat a l :=
    fun a l => effective_of_A rfl a l
  have hnp : ∀ u m, CapAttr s reg c u m → u ∉ ps := fun u m hu hup => by
    have hpu := hparams u hup
    unfold OptP at hpu
    split at hpu
    · rename_i y hy
      exact not_attr_frame (c := c) (c' := c') hF.nodup hcc hy hpu.2.1 (view_top_mem hne) hu.unrestricted
    · exact hpu.elim
  have hpre : ∀ u m, CapAttr s reg c u m → s'.A[u]? = s.A[u]? := fun u m hu => by
    rw [hk.1, Frames.enter_lt (s := s.view c') hu.lt]
    show Option.map _ (s.A[u]?) = _
    simp [hnp u m hu]
  have hact : ∀ j < s.A.length, ∀ y', s'.A[j]? = some y' → y'.active = true → s.flat.Active j :=
    fun j hj y' hy' hya => by
      rw [hk.1] at hy'
      rcases Frames.enter_get hy' with ⟨-, y, hy, rfl⟩ | ⟨hjl, -⟩
      · refine ⟨y, hy, ?_⟩
        split at hya
        · exact hya
        · exact hya
      · exact absurd hj (Nat.not_lt.2 hjl)
  have heq : ∀ a l, effective s'.flat a l = effective (enterEff (s.view c') ps ls) a l :=
    fun a l => effective_of_A hk.1 a l
  refine cap_transport_u (s' := s') (reg' := reg) hw hstk
    (fun p hp l hl => by
      rw [show s'.P = _ from hk.2] at hl
      exact (Frames.enter_footprint_old (s := s.view c') hsh hp l).1 hl)
    (fun u m y hu _ hy => ⟨y, by rw [hpre u m hu]; exact hy, rfl, rfl, rfl⟩)
    (fun u m hu _ => notGuarded_prefix hact hu.lt hu.notGuarded)
    (fun u m l hu hal => ?_) l
  rw [heq]
  rw [← hvA] at hal
  refine eff_keep_sub (fun z hz => ⟨z, by rw [← hk.1, hpre u m hu]; exact hz, rfl, rfl, rfl⟩)
    (fun j y hy hya hyl hj => ?_) hal
  rcases Frames.enter_get hy with ⟨hjl, y₀, hy₀, rfl⟩ | ⟨hjl, i, -, rfl⟩
  · refine ⟨y₀, hy₀, ?_, ?_, by rwa [Frames.enter_ancs_lt hjl] at hj, ?_⟩ <;>
      split at hya <;> first | exact hya | (split at hyl <;> exact hyl) | (split <;> rfl)
  · exfalso
    have : (enterEff (s.view c') ps ls).org j = none := by unfold S3.org; rw [hy]; rfl
    rw [S3.ancs, chain_none this] at hj; simp at hj

/-! ## State-level forms of `derive`, `store` and `transfer` -/

/-- `derive` by context `c'` (Spec 1 §60) does not lower `cap` of another context (state form of
`local_loss_derive`). -/
theorem derive_cap_mono {s : SC} {reg : SyncReg} (hF : FramesC s) (hI : I1 s.flat)
    (hw : WF3 s.flat) {c c' src : Nat} {region : List Nat} {md : Mode} (hcc : c ≠ c')
    (hlive : s.Live c') (hp : DerivePre (s.view c') src region md) (l : Nat) :
    capRank (cap s reg c l) ≤
      capRank (cap (s.set (deriveEff (s.view c') src region md)) reg c l) := by
  have hne := hF.nonempty c' hlive
  have hpre : ∀ j < s.A.length, (deriveEff (s.view c') src region md).A[j]? = s.A[j]? :=
    fun j hj => addAuth_lt (s := s.view c') hj
  refine cap_transport_u (s' := s.set (deriveEff (s.view c') src region md)) (reg' := reg) hw
    (fun f hf => hf) (fun p _ l hl => hl)
    (fun u m y hu _ hy => ⟨y, (by show (deriveEff (s.view c') src region md).A[u]? = _
                                  rw [hpre u hu.lt]; exact hy), rfl, rfl, rfl⟩)
    (fun u m hu _ => notGuarded_prefix (fun j hj y' hy' hya => ⟨y', by
        have : (deriveEff (s.view c') src region md).A[j]? = some y' := hy'
        rwa [hpre j hj] at this, hya⟩) hu.lt hu.notGuarded)
    (fun u m l hu hal => ?_) l
  have := derive_eff_keep hF.nodup hI hw hcc hne hp hu.unrestricted hal
  rw [effective_of_A (t := (s.set (deriveEff (s.view c') src region md)).flat)
    (t' := s.flat.addAuth ⟨md, some src, region, .frame (s.view c').top, true⟩) rfl]
  exact this

/-- `store` by context `c'` (Spec 1 §65) does not lower `cap` of another context (state form of
`local_loss_store`). -/
theorem store_cap_mono {s : SC} {reg : SyncReg} (hF : FramesC s) (hw : WF3 s.flat)
    {c c' a p : Nat} (hcc : c ≠ c') (hlive : s.Live c') (hp : StorePreC s c' a p) (l : Nat) :
    capRank (cap s reg c l) ≤ capRank (cap (storeEffC s c' a p) reg c l) := by
  have hne := hF.nonempty c' hlive
  have hsk : SameSkel s.flat (storeEffC s c' a p).flat := store_skel (s.view c') a p
  have hfa : ∀ u m, CapAttr s reg c u m → u ≠ a := fun u m hu hua => by
    subst hua
    have hd := hp.derivedHeld
    unfold OptP at hd
    split at hd
    · rename_i y hy
      exact not_attr_frame (c := c) (c' := c') hF.nodup hcc hy hd.2.2 (view_top_mem hne) hu.unrestricted
    · exact hd.elim
  refine cap_transport_u (s' := storeEffC s c' a p) (reg' := reg) hw (fun f hf => hf)
    (fun q _ l hl => by rwa [show (storeEffC s c' a p).P = s.P from storeEff_P _ a p] at hl)
    (fun u m y hu _ hy => ⟨y, ?_, rfl, rfl, rfl⟩)
    (fun u m hu _ => notGuarded_of_skel hsk (fun e he => ⟨e, he, rfl⟩) hu.notGuarded)
    (fun u m l _ hal => by rw [hsk.effective]; exact hal) l
  show (storeEff (s.view c') a p).A[u]? = some y
  unfold storeEff
  split
  · rw [List.getElem?_set_ne (Ne.symm (hfa u m hu))]; exact hy
  · exact hy

/-- `transfer` by context `c'` (Spec 1 §63) does not lower `cap` of another context (state form of
`local_loss_transfer`). -/
theorem transfer_cap_mono {k : K} {s : SC} {reg : SyncReg} (hF : FramesC s) (hI : I1 s.flat)
    (hw : WF3 s.flat) {c c' src dst : Nat} (hcc : c ≠ c') (hlive : s.Live c')
    (hp : TransferPreC k s c' src dst) (l : Nat) :
    capRank (cap s reg c l) ≤ capRank (cap (transferEffC s c' src dst) reg c l) := by
  have hne := hF.nonempty c' hlive
  have hsk : SameSkel s.flat (transferEffC s c' src dst).flat :=
    transfer_skel (s.view c') src dst
  obtain ⟨g, -, hgx, hge⟩ := hp.srcRight
  have hg : UnrestrictedAttr s c' g .modify := attr_of_exercisable hne hgx
  have hge' : ∀ l ∈ footprint s.P src, Allows (effective s.flat g l) .modify :=
    fun l hl => by rw [← effective_of_A (t := s.view c') (t' := s.flat) rfl]; exact hge l hl
  have hkeep : ∀ u m y, CapAttr s reg c u m → s.A[u]? = some y → ¬ heldIn s.P src y.holder :=
    fun u m y hu hy hh => by
      cases hh' : y.holder with
      | frame f => rw [hh'] at hh; exact hh
      | place q =>
        rw [hh'] at hh
        exact not_attr_place hF.nodup hI hw hcc hy hh' hg
          (fun l hl => hge' l (footprint_sub hw hh hl)) hu.unrestricted
  refine cap_transport_u (s' := transferEffC s c' src dst) (reg' := reg) hw (fun f hf => hf)
    (fun p _ l hl => by
      have hl' : l ∈ footprint (transferEff (s.view c') src dst).P p := hl
      rwa [transfer_footprint] at hl')
    (fun u m y hu _ hy => ⟨y, ?_, rfl, rfl, rfl⟩)
    (fun u m hu _ => notGuarded_of_skel hsk (fun e he => ⟨e, he, rfl⟩) hu.notGuarded)
    (fun u m l _ hal => by rw [hsk.effective]; exact hal) l
  show (transferEff (s.view c') src dst).A[u]? = some y
  unfold transferEff
  simp only [List.getElem?_map]
  rw [show (s.view c').A[u]? = some y from hy]
  have hk : ¬ heldIn (s.view c').P src y.holder := hkeep u m y hu hy
  simp [hk]

/-! ## Trace-level lemmas -/

/-- The frame structure, `WF3` and `I1` of a state satisfying `KInvCA` (C20; Spec 1 §49,
§50). -/
theorem KInvCA.parts {s : SC} (hk : KInvCA s) : FramesC s ∧ WF3 s.flat ∧ I1 s.flat :=
  ⟨hk.1.1.1, hk.1.1.2, hk.1.2.1.1.1⟩

/-- L1 (`local_loss`, C45) for `split` (Spec 1 §61). Under `DDSound` (Spec 1 §80), from a
state reached by an `EncapsulatedTrace` from an initial state (Spec 1 §47). -/
theorem local_loss_split {ks : KShared} {L : MutexLayout} {statics : Statics} {lbls : List Label}
    {st st' : SC × SyncReg × ArenaReg} {c' src : Nat} {rs : List (List Nat)} (hdd : DDSound ks.toK)
    (hst : StaticsOK statics)
    (htr : EncapsulatedTrace pm ks L (SC.ofS3 (S3.init statics), [], []) lbls st)
    (h : LStep ks L (.kernel c' (.split src rs)) st st') (c l : Nat)
    (hd : capRank (cap st'.1 st'.2.1 c l) < capRank (cap st.1 st.2.1 c l)) :
    (Label.kernel c' (.split src rs)).requester = c := by
  obtain ⟨hF, hw, hI⟩ := ((encapsulated_inv hdd hst htr).1).parts
  refine Decidable.byContradiction fun hctx => ?_
  have hcc : c ≠ c' := fun e => hctx (e ▸ rfl)
  cases h with
  | @kernel s s' reg ar _ _ hk =>
    have hlive := opStepC_live hk
    obtain ⟨o, hR, ho⟩ := hk
    cases hR with
    | reject => cases ho
    | ok hp =>
      cases ho
      exact absurd hd (Nat.not_lt.2 (split_cap_mono hF hI hw hcc hlive hp l))

/-- L1 (`local_loss`, C45) for `alloc` (Spec 1 §71). Under `DDSound` (Spec 1 §80), from a
state reached by an `EncapsulatedTrace` from an initial state (Spec 1 §47). -/
theorem local_loss_alloc {ks : KShared} {L : MutexLayout} {statics : Statics} {lbls : List Label}
    {st st' : SC × SyncReg × ArenaReg} {c' pr ow : Nat} {ls : LocalShape} (hdd : DDSound ks.toK)
    (hst : StaticsOK statics)
    (htr : EncapsulatedTrace pm ks L (SC.ofS3 (S3.init statics), [], []) lbls st)
    (h : LStep ks L (.kernel c' (.alloc pr ow ls)) st st') (c l : Nat)
    (hd : capRank (cap st'.1 st'.2.1 c l) < capRank (cap st.1 st.2.1 c l)) :
    (Label.kernel c' (.alloc pr ow ls)).requester = c := by
  obtain ⟨-, hw, -⟩ := ((encapsulated_inv hdd hst htr).1).parts
  exfalso
  cases h with
  | @kernel s s' reg ar _ _ hk =>
    obtain ⟨o, hR, ho⟩ := hk
    cases hR with
    | ok hsa _ => cases ho; exact absurd hd (Nat.not_lt.2 (alloc_cap_mono hw hsa l))
    | fail => cases ho
    | reject => cases ho

/-- L1 (`local_loss`, C45) for `enterFrame` (Spec 1 §72). Under `DDSound` (Spec 1 §80),
from a state reached by an `EncapsulatedTrace` from an initial state (Spec 1 §47). -/
theorem local_loss_enter {ks : KShared} {L : MutexLayout} {statics : Statics} {lbls : List Label}
    {st st' : SC × SyncReg × ArenaReg} {c' : Nat} {ps : List Nat} {ls : LocalShape}
    (hdd : DDSound ks.toK) (hst : StaticsOK statics)
    (htr : EncapsulatedTrace pm ks L (SC.ofS3 (S3.init statics), [], []) lbls st)
    (h : LStep ks L (.kernel c' (.enter ps ls)) st st') (c l : Nat)
    (hd : capRank (cap st'.1 st'.2.1 c l) < capRank (cap st.1 st.2.1 c l)) :
    (Label.kernel c' (.enter ps ls)).requester = c := by
  obtain ⟨hF, hw, -⟩ := ((encapsulated_inv hdd hst htr).1).parts
  refine Decidable.byContradiction fun hctx => ?_
  have hcc : c ≠ c' := fun e => hctx (e ▸ rfl)
  cases h with
  | @kernel s s' reg ar _ _ hk =>
    have hR := hk
    cases hR with
    | ok hp =>
      have hstk : ∀ f ∈ s.stk c, f ∈ (enterEffC s c' ps ls).stk c := fun f hf => by
        simp only [PreservationAux.enter_stk hp.callerLive c, hcc, ↓reduceIte]; exact hf
      exact absurd hd (Nat.not_lt.2 (enter_cap_mono hF hw hcc hp.callerLive hp.params hp.localsOK
        ⟨rfl, rfl⟩ hstk l))

/-- L1 (`local_loss`, C45) for `spawn` (C4): the parameters go to the initial frame of
the new context, which had no `cap` before the step. Under `DDSound` (Spec 1 §80), from a state
reached by an `EncapsulatedTrace` from an initial state (Spec 1 §47). -/
theorem local_loss_spawn {ks : KShared} {L : MutexLayout} {statics : Statics} {lbls : List Label}
    {st st' : SC × SyncReg × ArenaReg} {c' : Nat} {ps : List Nat} {ls : LocalShape}
    (hdd : DDSound ks.toK) (hst : StaticsOK statics)
    (htr : EncapsulatedTrace pm ks L (SC.ofS3 (S3.init statics), [], []) lbls st)
    (h : LStep ks L (.spawn c' ps ls) st st') (c l : Nat)
    (hd : capRank (cap st'.1 st'.2.1 c l) < capRank (cap st.1 st.2.1 c l)) :
    (Label.spawn c' ps ls).requester = c := by
  obtain ⟨hF, hw, -⟩ := ((encapsulated_inv hdd hst htr).1).parts
  refine Decidable.byContradiction fun hctx => ?_
  have hcc : c ≠ c' := fun e => hctx (e ▸ rfl)
  cases h with
  | @spawn s s' reg ar _ _ _ hs =>
    have hR := hs
    cases hR with
    | ok hp =>
      by_cases hcl : c < s.C.length
      · have hstk : (spawnEff s c' ps ls).stk c = s.stk c := by
          unfold SC.stk
          rw [show (spawnEff s c' ps ls).C[c]? = s.C[c]? from List.getElem?_append_left hcl]
        exact absurd hd (Nat.not_lt.2 (enter_cap_mono hF hw hcc hp.creatorLive hp.params
          hp.localsOK ⟨rfl, rfl⟩ (fun f hf => by rw [hstk]; exact hf) l))
      · have hnil : s.stk c = [] := by
          unfold SC.stk; rw [List.getElem?_eq_none (Nat.le_of_not_lt hcl)]
        have h0 := cap_nil (reg := reg) (l := l) hnil
        rw [show cap (s, reg, ar).1 (s, reg, ar).2.1 c l = none from h0] at hd
        exact absurd hd (Nat.not_lt_zero _)

/-- L1 (`local_loss`, C45) for `issue` (Spec 1 §77, Part XIV: `split` then `store`, both by
the actor; C2): each phase lowers no `cap` of another context, the invariants holding after
the `split` (theorem 2, `opStepC_preservesC`). Under `DDSound` (Spec 1 §80), from a state reached by an
`EncapsulatedTrace` from an initial state (Spec 1 §47). -/
theorem local_loss_issue {ks : KShared} {L : MutexLayout} {statics : Statics} {lbls : List Label}
    {st st' : SC × SyncReg × ArenaReg} {c' i dst : Nat} {region : List Nat} (hdd : DDSound ks.toK)
    (hst : StaticsOK statics)
    (htr : EncapsulatedTrace pm ks L (SC.ofS3 (S3.init statics), [], []) lbls st)
    (h : LStep ks L (.issue c' i region dst) st st') (c l : Nat)
    (hd : capRank (cap st'.1 st'.2.1 c l) < capRank (cap st.1 st.2.1 c l)) :
    (Label.issue c' i region dst).requester = c := by
  have hk := (encapsulated_inv hdd hst htr).1
  refine Decidable.byContradiction fun hctx => ?_
  have hcc : c ≠ c' := fun e => hctx (e ▸ rfl)
  cases h with
  | @issue s reg ar _ _ _ _ st₁ hi =>
    cases hi with
    | @ok E s₁ s₂ _ _ _ h₁ h₂ =>
      obtain ⟨hF, hw, hI⟩ := hk.parts
      have hk₁ := opStepC_preservesC hdd hk (by intro h; cases h) h₁
      obtain ⟨hF₁, hw₁, -⟩ := hk₁.parts
      have hlive := opStepC_live h₁
      obtain ⟨o, hR, ho⟩ := h₁
      cases hR with
      | reject => cases ho
      | ok hp =>
        cases ho
        have hlive₁ := opStepC_live h₂
        have hR₂ := h₂
        cases hR₂ with
        | ok hp₂ =>
          exact absurd hd (Nat.not_lt.2 (Nat.le_trans (split_cap_mono hF hI hw hcc hlive hp l)
            (store_cap_mono hF₁ hw₁ hcc hlive₁ hp₂ l)))

/-- L1 (`local_loss`, C45) for `reset` (Spec 1 §78, Part XIV: `derive` of `internal` then
`release`, on the view of the actor; C2): each phase lowers no `cap` of another context, the
invariants holding after the `derive` (theorem 2). Under `DDSound` (Spec 1 §80), from a state reached by
an `EncapsulatedTrace` from an initial state (Spec 1 §47). -/
theorem local_loss_reset {ks : KShared} {L : MutexLayout} {statics : Statics} {lbls : List Label}
    {st st' : SC × SyncReg × ArenaReg} {c' i : Nat} (hdd : DDSound ks.toK) (hst : StaticsOK statics)
    (htr : EncapsulatedTrace pm ks L (SC.ofS3 (S3.init statics), [], []) lbls st)
    (h : LStep ks L (.reset c' i) st st') (c l : Nat)
    (hd : capRank (cap st'.1 st'.2.1 c l) < capRank (cap st.1 st.2.1 c l)) :
    (Label.reset c' i).requester = c := by
  have hk := (encapsulated_inv hdd hst htr).1
  refine Decidable.byContradiction fun hctx => ?_
  have hcc : c ≠ c' := fun e => hctx (e ▸ rfl)
  cases h with
  | @reset s reg ar _ _ st₁ hr =>
    have hlive : s.Live c' := lstep_live (LStep.reset (ks := ks) (L := L) (reg := reg) hr)
    obtain ⟨o₃, hD, ho⟩ := hr
    cases hD with
    | @ok E s₁ s₂ _ hd₁ hr₂ _ =>
      cases ho
      obtain ⟨hF, hw, hI⟩ := hk.parts
      cases hd₁ with
      | ok hp₁ =>
        have hmid : opStepC ks.toK (.derive E.internal (footprint (s.view c').P E.storage) .modify) c' s
            (.ok (s.set (deriveEff (s.view c') E.internal (footprint (s.view c').P E.storage)
              .modify))) := ⟨_, .ok hp₁, rfl⟩
        have hk₁ := opStepC_preservesC hdd hk (by intro h; cases h) hmid
        obtain ⟨hF₁, hw₁, hI₁⟩ := hk₁.parts
        have hv : (s.set (deriveEff (s.view c') E.internal (footprint (s.view c').P E.storage)
            .modify)).view c' =
            deriveEff (s.view c') E.internal (footprint (s.view c').P E.storage) .modify :=
          SC.view_set hlive rfl
        cases hr₂ with
        | ok hp₂ =>
          have h2 := release_cap_mono (reg := reg) (reg' := reg) hF₁ hI₁ hw₁ hcc hlive
            (by rw [hv]; exact hp₂) (fun e he => ⟨e, he, rfl⟩) l
          rw [hv] at h2
          exact absurd hd (Nat.not_lt.2 (Nat.le_trans (derive_cap_mono hF hI hw hcc hlive hp₁ l)
            h2))
    | _ => cases ho

/-! ## `exitFrame` and `terminate` (Spec 1 §73; C6, C7) -/

/-- After the exit, the origin chain of an authority keeps only former ancestors (Spec 1 §73 `ok`
effect, third item: reanchoring to the first surviving ancestor). -/
theorem exit_ancs_sub {t : S3}
    (ho : ∀ (b : Nat) (y : Authority) (a : Nat), t.A[b]? = some y → y.origin = some a → a < b) :
    ∀ n x, x < n → ∀ w ∈ (exitEff t).ancs x, w ∈ t.ancs x
  | 0, _, h, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, x, hx, w, hw => by
    have hlt : ∀ i o, t.org i = some o → o < i := fun i o h => by
      unfold S3.org at h
      cases hy : t.A[i]? with
      | none => rw [hy] at h; cases h
      | some y => rw [hy] at h; exact ho i y o hy h
    cases hy : t.A[x]? with
    | none =>
      have : (exitEff t).org x = none := by simp [S3.org, Frames.exit_A_get, hy]
      rw [S3.ancs, chain_none this] at hw; simp at hw
    | some y =>
      have e' : (exitEff t).org x = (exitG t t.F.tail x y).origin := by
        simp [S3.org, Frames.exit_A_get, hy]
      rcases Frames.exitG_origin (s := t) (F₀ := t.F.tail) (a := x) (y := y) with e | ⟨-, -, e⟩
      · rw [e] at e'
        cases hoy : y.origin with
        | none => rw [hoy] at e'; rw [S3.ancs, chain_none e'] at hw; simp at hw
        | some o =>
          rw [hoy] at e'
          have hox := ho x y o hy hoy
          have hob : t.org x = some o := by simp [S3.org, hy, hoy]
          rw [S3.ancs, chain_cons e' hox] at hw
          rw [S3.ancs, chain_cons hob hox]
          rcases List.mem_cons.1 hw with rfl | hw
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (exit_ancs_sub ho n o (by omega) w hw)
      · rw [e] at e'
        cases hz : firstSurv t t.F.tail (t.ancs x) with
        | none => rw [hz] at e'; rw [S3.ancs, chain_none e'] at hw; simp at hw
        | some z =>
          rw [hz] at e'
          have hzx : z ∈ t.ancs x := (Frames.firstSurv_some hz).1
          have hzlt := chain_lt hzx
          rw [S3.ancs, chain_cons e' hzlt] at hw
          rcases List.mem_cons.1 hw with rfl | hw
          · exact hzx
          · exact chain_trans hlt (x + 1) x (Nat.lt_succ_self x) z hzx w
              (exit_ancs_sub ho n z (by omega) w hw)

/-- A live frame other than the top frame of `c` is in the tail of the stack of the view of `c`
(C2). -/
theorem mem_view_tail {s : SC} {c y : Nat} (hne : s.stk c ≠ []) (hy : y ∈ s.frames)
    (hyt : y ≠ (s.stk c).headD 0) : y ∈ (s.view c).F.tail := by
  obtain ⟨f, r, hfr⟩ := List.exists_cons_of_ne_nil hne
  rw [SC.view_F_live (SC.live_of_stk hne)]
  rw [hfr] at hyt ⊢
  simp only [List.headD_cons] at hyt
  simp only [List.cons_append, List.tail_cons, List.mem_append, List.mem_filter,
    decide_eq_true_eq]
  by_cases hin : y ∈ f :: r
  · rcases List.mem_cons.1 hin with rfl | h
    · exact absurd rfl hyt
    · exact .inl h
  · exact .inr ⟨hy, hin⟩

/-- The top frame of `c` after a pop is the head of its stack (C6). -/
theorem ReparentAux.Pop.f_eq {s s' : SC} {c f p : Nat} (h : ReparentAux.Pop s s' c f p) :
    f = (s.stk c).headD 0 := by
  have := h.head
  cases e : s.stk c with
  | nil => rw [e] at this; cases this
  | cons a l => rw [e] at this; cases this; rfl

/-- Every useful authority attributable to another context survives the exit of the top frame of
`c'` (Spec 1 §73, `Survives`): frame-held ones are held by a frame of their own context, and
place-held ones by a place that stays usable, by `NoDangling` after the step (Spec 1 §54, §57;
theorem 2). -/
theorem exit_survives {s s' : SC} {reg : SyncReg} (hF : FramesC s) (hw : WF3 s.flat)
    {c c' f p : Nat} (hcc : c ≠ c') (hne : s.stk c' ≠ []) (hpop : ReparentAux.Pop s s' c' f p)
    (hA' : s'.A = (exitEff (s.view c')).A) (hP' : s'.P = s.P) (hd' : s'.dead = s.dead)
    (hND : NoDangling s'.flat) {u : Nat} {m : Mode} (h : CapAttr s reg c u m) (hu : Useful s u m) :
    Survives (s.view c') (s.view c').F.tail u := by
  have hP := parents_lt hw
  have hf := hpop.f_eq
  have hfc' : f ∈ s.stk c' := by rw [hpop.stk_c]; exact List.mem_cons_self ..
  induction h with
  | @base a m y f₀ hg hy ha hm hfr hin =>
    show OptP ((s.view c').A[a]?) _ False
    rw [show (s.view c').A[a]? = some y from hy]
    refine ⟨ha, ?_⟩
    rw [hfr]
    refine mem_view_tail hne (SC.mem_frames_of hin) fun he => hcc ?_
    exact ReparentAux.stk_unique hF.nodup hin (he ▸ hf ▸ hfc')
  | @held a q b m y hg hy ha hm hp hb hc ih =>
    have hup : s.flat.Usable q := by
      have := hw.holders a _ hy ha; rw [hp] at this; exact this
    obtain ⟨l₀, hl₀⟩ := footprint_ne hP _ q (Nat.le_refl _) hup.lt
    have hsb := ih ⟨l₀, hc l₀ hl₀⟩
    obtain ⟨zb, hzb, -, hzl, -⟩ := eff_present (allows_present (hc l₀ hl₀))
    have hu' : s'.flat.Usable q := by
      refine Decidable.byContradiction fun hnu => ?_
      have hb' : s'.flat.A[b]? = some (exitG (s.view c') (s.view c').F.tail b zb) := by
        show s'.A[b]? = _
        rw [hA', Frames.exit_A_get, show (s.view c').A[b]? = some zb from hzb]; rfl
      have hact := Frames.exitG_surv (s := s.view c') (show (s.view c').A[b]? = some zb from hzb)
        hsb
      have := hND b _ hb' hact q hnu l₀ (by show l₀ ∈ footprint s'.P q; rw [hP']; exact hl₀)
      rw [(Frames.exitG_same _ _ _ _).2.1] at this
      exact this hzl
    have hut : ({ s.view c' with F := (s.view c').F.tail } : S3).Usable q := by
      refine S3.Usable.mono (s := { s.view c' with F := (s.view c').F.tail }) (s' := s'.flat)
        (show s'.flat.P = ({ s.view c' with F := (s.view c').F.tail } : S3).P from hP')
        (fun f' hf' => ?_)
        (fun q hq => by rwa [show s'.flat.dead = s.dead from hd'] at hq) hu'
      obtain ⟨hf1, hf2⟩ := (hpop.mem_frames hF.nodup).1 hf'
      exact mem_view_tail hne hf1 (hf ▸ hf2)
    show OptP ((s.view c').A[a]?) _ False
    rw [show (s.view c').A[a]? = some y from hy]
    refine ⟨ha, ?_⟩
    rw [hp]; exact hut

/-- The exit of the top frame of `c'` (Spec 1 §73; C6, C7), read from another context `c`:
`cap` of `c` does not decrease. The useful authorities of `c` survive (`exit_survives`);
reanchoring only shortens origin chains (`exit_ancs_sub`), so effective modes can only rise. -/
theorem exit_cap_mono {s s' : SC} {reg : SyncReg} (hF : FramesC s) (hw : WF3 s.flat)
    {c c' f p : Nat} (hcc : c ≠ c') (hne : s.stk c' ≠ []) (hpop : ReparentAux.Pop s s' c' f p)
    (hA' : s'.A = (exitEff (s.view c')).A) (hP' : s'.P = s.P) (hd' : s'.dead = s.dead)
    (hND : NoDangling s'.flat) (l : Nat) :
    capRank (cap s reg c l) ≤ capRank (cap s' reg c l) := by
  have ho : ∀ (b : Nat) (y : Authority) (a : Nat), (s.view c').A[b]? = some y →
      y.origin = some a → a < b :=
    fun b y a hy hoy => hw.origins b y a hy hoy
  have hget : ∀ u y, s.A[u]? = some y →
      s'.A[u]? = some (exitG (s.view c') (s.view c').F.tail u y) := fun u y hy => by
    rw [hA', Frames.exit_A_get, show (s.view c').A[u]? = some y from hy]; rfl
  have hsurv : ∀ u m y, CapAttr s reg c u m → Useful s u m → s.A[u]? = some y →
      (exitG (s.view c') (s.view c').F.tail u y).active = true := fun u m y hu hus hy =>
    Frames.exitG_surv (s := s.view c') hy (exit_survives hF hw hcc hne hpop hA' hP' hd' hND hu hus)
  have hyact : ∀ u m y, CapAttr s reg c u m → s.A[u]? = some y → y.active = true :=
    fun u m y hu hy => by
      cases hu with
      | base _ hy' ha => rw [hy] at hy'; cases hy'; exact ha
      | held _ hy' ha => rw [hy] at hy'; cases hy'; exact ha
  refine cap_transport_u (s' := s') (reg' := reg) hw
    (fun f' hf' => by rw [hpop.stk c]; simp only [hcc, ↓reduceIte]; exact hf')
    (fun q _ l hl => by rwa [hP'] at hl)
    (fun u m y hu hus hy => ⟨_, hget u y hy, by rw [hsurv u m y hu hus hy, hyact u m y hu hy],
      (Frames.exitG_same _ _ _ _).1, (Frames.exitG_same _ _ _ _).2.2⟩)
    (fun u m hu _ e he hl => ?_) (fun u m l hu hal => ?_) l
  · obtain ⟨y', hy', hya⟩ := hl
    have hy'' : (exitEff (s.view c')).A[e.guarded]? = some y' := by rw [← hA']; exact hy'
    obtain ⟨y₀, hy₀, rfl⟩ := Frames.exit_get hy''
    exact hu.notGuarded e he ⟨y₀, hy₀, Frames.exitG_active' (s := s.view c') hy₀ hya⟩
  · rw [effective_of_A (t := s'.flat) (t' := exitEff (s.view c')) hA']
    rw [← effective_of_A (t := s.view c') (t' := s.flat) rfl] at hal
    refine eff_keep_sub (fun z hz => ⟨_, by rw [← hA']; exact hget u z hz, ?_,
      (Frames.exitG_same _ _ _ _).1, (Frames.exitG_same _ _ _ _).2.1⟩)
      (fun j y hy hya hyl hj => ?_) hal
    · have hus : Useful s u m :=
        ⟨l, by rw [← effective_of_A (t := s.view c') (t' := s.flat) rfl]; exact hal⟩
      rw [hsurv u m z hu hus hz, hyact u m z hu hz]
    · obtain ⟨y₀, hy₀, rfl⟩ := Frames.exit_get hy
      refine ⟨y₀, hy₀, Frames.exitG_active' (s := s.view c') hy₀ hya, ?_, ?_,
        (Frames.exitG_same _ _ _ _).1.symm⟩
      · rw [(Frames.exitG_same _ _ _ _).2.1] at hyl; exact hyl
      · exact exit_ancs_sub ho (j + 1) j (Nat.lt_succ_self j) u hj

/-- L1 (`local_loss`, C45) for `exitFrame` (Spec 1 §73; C6). Under `DDSound` (Spec 1
§80), from a state reached by an `EncapsulatedTrace` from an initial state (Spec 1 §47). -/
theorem local_loss_exit {ks : KShared} {L : MutexLayout} {statics : Statics} {lbls : List Label}
    {st st' : SC × SyncReg × ArenaReg} {c' : Nat} (hdd : DDSound ks.toK) (hst : StaticsOK statics)
    (htr : EncapsulatedTrace pm ks L (SC.ofS3 (S3.init statics), [], []) lbls st)
    (h : LStep ks L (.kernel c' .exit) st st') (c l : Nat)
    (hd : capRank (cap st'.1 st'.2.1 c l) < capRank (cap st.1 st.2.1 c l)) :
    (Label.kernel c' .exit).requester = c := by
  have hk := (encapsulated_inv hdd hst htr).1
  have hk' := lstep_kInvCA hdd h hk
  refine Decidable.byContradiction fun hctx => ?_
  have hcc : c ≠ c' := fun e => hctx (e ▸ rfl)
  cases h with
  | @kernel s s' reg ar _ _ hs =>
    obtain ⟨hF, hw, -⟩ := hk.parts
    have hlive := opStepC_live hs
    have hR := hs
    cases hR with
    | ok hp =>
      exact absurd hd (Nat.not_lt.2 (exit_cap_mono hF hw hcc (hF.nonempty c' hlive)
        (exitEffC_pop hF.nodup hp.hasCaller) rfl rfl rfl hk'.1.2.1.2.2 l))

/-- L1 (`local_loss`, C45) for `terminate` (C7): the initial frame of the actor is
popped as by `exitFrame` (Spec 1 §73). Under `DDSound` (Spec 1 §80), from a state reached by an
`EncapsulatedTrace` from an initial state (Spec 1 §47). -/
theorem local_loss_terminate {ks : KShared} {L : MutexLayout} {statics : Statics} {lbls : List Label}
    {st st' : SC × SyncReg × ArenaReg} {c' : Nat} (hdd : DDSound ks.toK) (hst : StaticsOK statics)
    (htr : EncapsulatedTrace pm ks L (SC.ofS3 (S3.init statics), [], []) lbls st)
    (h : LStep ks L (.terminate c') st st') (c l : Nat)
    (hd : capRank (cap st'.1 st'.2.1 c l) < capRank (cap st.1 st.2.1 c l)) :
    (Label.terminate c').requester = c := by
  have hk := (encapsulated_inv hdd hst htr).1
  have hk' := lstep_kInvCA hdd h hk
  refine Decidable.byContradiction fun hctx => ?_
  have hcc : c ≠ c' := fun e => hctx (e ▸ rfl)
  cases h with
  | @terminate s s' reg ar _ ht =>
    obtain ⟨hF, hw, -⟩ := hk.parts
    have hlive := termStep_live ht
    have hR := ht
    cases hR with
    | ok hp =>
      have hpar : s.ctxParent c' ≠ none := fun he => by
        have := hp.hasParent; rw [he] at this; exact this
      exact absurd hd (Nat.not_lt.2 (exit_cap_mono hF hw hcc (hF.nonempty c' hlive)
        (termEffC_pop hF.nodup hp.initialOnly hpar) rfl rfl rfl hk'.1.2.1.2.2 l))

/-! ## Steps that only release authorities: `endUse`, `free` (Spec 1 §69, §70) -/

/-- A live frame is in the stack of the view of any context (C2). -/
theorem mem_view_F {s : SC} {c y : Nat} (hy : y ∈ s.frames) : y ∈ (s.view c).F := by
  by_cases hl : s.Live c
  · exact (SC.mem_view_F hl).2 hy
  · simp only [SC.view, hl, ite_false]; exact List.mem_cons_of_mem _ hy

/-- An attributable authority is active (C43). -/
theorem CapAttr.active {s : SC} {reg : SyncReg} {c u : Nat} {m : Mode} {y : Authority}
    (h : CapAttr s reg c u m) (hy : s.A[u]? = some y) : y.active = true := by
  cases h with
  | base _ hy' ha => rw [hy] at hy'; cases hy'; exact ha
  | held _ hy' ha => rw [hy] at hy'; cases hy'; exact ha

/-- A step that only releases authorities (`OnlyReleases`, Spec 1 §69, §70) and keeps the places
and the frames of `c` does not lower `cap` of `c` when every useful authority attributable to
`c` stays active: effective modes can only rise. -/
theorem releases_cap_mono {s s' : SC} {reg : SyncReg} (hw : WF3 s.flat) {c : Nat}
    (hr : EndFree.OnlyReleases s.flat s'.flat) (hstk : ∀ f ∈ s.stk c, f ∈ s'.stk c)
    (hP : s'.P = s.P)
    (hkeep : ∀ u m, CapAttr s reg c u m → Useful s u m → s'.flat.Active u) (l : Nat) :
    capRank (cap s reg c l) ≤ capRank (cap s' reg c l) := by
  have hact : ∀ u m z, CapAttr s reg c u m → Useful s u m → s'.A[u]? = some z → z.active = true :=
    fun u m z hu hus hz => by
      obtain ⟨z', hz', hza⟩ := hkeep u m hu hus
      have : s'.A[u]? = some z' := hz'
      rw [hz] at this; cases this; exact hza
  refine cap_transport_u (s' := s') (reg' := reg) hw hstk (fun q _ l hl => by rwa [hP] at hl)
    (fun u m y hu hus hy => ?_) (fun u m hu _ e he hl => ?_) (fun u m l hu hal => ?_) l
  · obtain ⟨z, hz, hm, -, -, hh⟩ := hr.get' (show s.flat.A[u]? = some y from hy)
    exact ⟨z, hz, by rw [hact u m z hu hus hz, hu.active hy], hm, hh⟩
  · obtain ⟨y', hy', hya⟩ := hl
    obtain ⟨y, hy, -, -, -, -, ha⟩ := hr.2 e.guarded y' hy'
    exact hu.notGuarded e he ⟨y, hy, ha hya⟩
  · refine eff_keep_sub (t := s.flat) (t' := s'.flat) (fun z hz => ?_) (fun j y hy hya hyl hj => ?_)
      hal
    · obtain ⟨z', hz', hm, -, hf, -⟩ := hr.get' hz
      exact ⟨z', hz', by rw [hact u m z' hu ⟨l, hal⟩ hz', hu.active hz], hm, hf⟩
    · obtain ⟨y₀, hy₀, hm, -, hf, -, ha⟩ := hr.2 j y hy
      exact ⟨y₀, hy₀, ha hya, hf ▸ hyl, by rwa [hr.ancs] at hj, hm.symm⟩

/-- `endUse` by context `c'` (Spec 1 §69) keeps active every useful authority attributable to
another context: it is held neither within the place, over which `c'` exercises `Modify`
(§69.1; `not_attr_place`), nor by a place that dies, by `NoDangling` after the step (Spec 1 §54,
§57; theorem 2). -/
theorem endUse_keeps {k : K} {s s' : SC} {reg : SyncReg} (hF : FramesC s) (hI : I1 s.flat)
    (hw : WF3 s.flat) {c c' p : Nat} (hcc : c ≠ c') (hne : s.stk c' ≠ [])
    (hp : EndUsePre k (s.view c') p) (hs' : s' = s.set (endUseEff (s.view c') p))
    (hND : NoDangling s'.flat) {u : Nat} {m : Mode} (h : CapAttr s reg c u m) (hu : Useful s u m) :
    ∀ y, s.A[u]? = some y → s'.A[u]? = some y := by
  have hP := parents_lt hw
  obtain ⟨g, -, hgx, hge⟩ := hp.right
  have hg : UnrestrictedAttr s c' g .modify := attr_of_exercisable hne hgx
  have hge' : ∀ l ∈ footprint s.P p, Allows (effective s.flat g l) .modify :=
    fun l hl => by rw [← effective_of_A (t := s.view c') (t' := s.flat) rfl]; exact hge l hl
  have hget : ∀ (a : Nat) (y : Authority), s.A[a]? = some y → ¬ heldIn s.P p y.holder →
      HolderLive (endUseS (s.view c') p) y.holder → s'.A[a]? = some y := fun a y hy hnh hl => by
    subst hs'
    show (cleanup (endUseS (s.view c') p)).A[a]? = some y
    rw [EndFree.cleanup_get, EndFree.endUseS_get,
      show (s.view c').A[a]? = some y from hy]
    simp only [Option.map_some, show ¬ heldIn (s.view c').P p y.holder from hnh, ↓reduceIte]
    simp only [show HolderLive (endUseS (s.view c') p) y.holder from hl, ↓reduceIte]
  induction h with
  | @base a m y f₀ hg' hy ha hm hfr hin =>
    intro y' hy'
    rw [hy] at hy'; cases hy'
    refine hget a y hy (by rw [hfr]; exact id) ?_
    rw [hfr]
    exact mem_view_F (SC.mem_frames_of hin)
  | @held a q b m y hg' hy ha hm hp' hb hc ih =>
    intro y' hy'
    rw [hy] at hy'; cases hy'
    have hup : s.flat.Usable q := by
      have := hw.holders a _ hy ha; rw [hp'] at this; exact this
    obtain ⟨l₀, hl₀⟩ := footprint_ne hP _ q (Nat.le_refl _) hup.lt
    obtain ⟨zb, hzb, -, hzl, -⟩ := eff_present (allows_present (hc l₀ hl₀))
    have hbk := ih ⟨l₀, hc l₀ hl₀⟩ zb hzb
    refine hget a y hy (fun hh => ?_) ?_
    · rw [hp'] at hh
      exact not_attr_place hF.nodup hI hw hcc hy hp' hg
        (fun l hl => hge' l (footprint_sub hw hh hl)) (.held hy ha hm hp' hb.unrestricted hc)
    · rw [hp']
      refine Decidable.byContradiction fun hnu => ?_
      have hnu' : ¬ s'.flat.Usable q := fun hu' => hnu (by
        refine S3.Usable.mono (s := endUseS (s.view c') p) (s' := s'.flat)
          (by rw [hs']; rfl) (fun f hf => ?_) (fun q hq => by rw [hs'] at hq; exact hq) hu'
        exact mem_view_F (s := s) (c := c') (by rw [hs'] at hf; exact hf))
      have hza : zb.active = true := hb.active hzb
      exact hND b zb hbk hza q hnu' l₀ (by rw [hs']; exact hl₀) hzl

/-- L1 (`local_loss`, C45) for `endUse` (Spec 1 §69). Under `DDSound` (Spec 1 §80), from a
state reached by an `EncapsulatedTrace` from an initial state (Spec 1 §47). -/
theorem local_loss_endUse {ks : KShared} {L : MutexLayout} {statics : Statics} {lbls : List Label}
    {st st' : SC × SyncReg × ArenaReg} {c' p : Nat} (hdd : DDSound ks.toK) (hst : StaticsOK statics)
    (htr : EncapsulatedTrace pm ks L (SC.ofS3 (S3.init statics), [], []) lbls st)
    (h : LStep ks L (.kernel c' (.endUse p)) st st') (c l : Nat)
    (hd : capRank (cap st'.1 st'.2.1 c l) < capRank (cap st.1 st.2.1 c l)) :
    (Label.kernel c' (.endUse p)).requester = c := by
  have hk := (encapsulated_inv hdd hst htr).1
  have hk' := lstep_kInvCA hdd h hk
  refine Decidable.byContradiction fun hctx => ?_
  have hcc : c ≠ c' := fun e => hctx (e ▸ rfl)
  cases h with
  | @kernel s s' reg ar _ _ hs =>
    obtain ⟨hF, hw, hI⟩ := hk.parts
    have hlive := opStepC_live hs
    obtain ⟨o, hR, ho⟩ := hs
    cases hR with
    | reject => cases ho
    | ok hp =>
      cases ho
      have hr : EndFree.OnlyReleases s.flat (s.set (endUseEff (s.view c') p)).flat :=
        (EndFree.endUseS_releases (s.view c') p).trans (EndFree.cleanup_releases _)
      refine absurd hd (Nat.not_lt.2 (releases_cap_mono (s' := s.set (endUseEff (s.view c') p))
        (reg := reg) hw hr (fun f hf => hf) rfl
        (fun u m hu hus => ?_) l))
      obtain ⟨y, hy⟩ : ∃ y, s.A[u]? = some y := ⟨_, List.getElem?_eq_getElem hu.lt⟩
      exact ⟨y, endUse_keeps hF hI hw hcc (hF.nonempty c' hlive) hp rfl hk'.1.2.1.2.2 hu hus y hy,
        hu.active hy⟩

/-- Transitive ownership through `p` goes up the structure (Spec 1 §40, §49.2: parts share their
parent's owner). -/
theorem ownedIn_up {t : S3} (hw : WF3 t) {p : Nat} :
    ∀ n l, l < n → ∀ r, partOf t.P l r → OwnedIn t.P p l → OwnedIn t.P p r
  | 0, _, h, _, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, l, hl, r, ⟨hlP, hlr⟩, ho => by
    rcases hlr with rfl | hc
    · exact ho
    · cases hq : t.P[l]? with
      | none => simp [List.getElem?_eq_getElem hlP] at hq
      | some pl =>
        cases hpo : pl.parent with
        | none =>
          have : parentOf t.P l = none := by simp [parentOf, hq, hpo]
          rw [chain_none this] at hc; simp at hc
        | some o =>
          obtain ⟨pr, hpr, hol, -, -⟩ := hw.places l pl o hq hpo
          have hpar : parentOf t.P l = some o := by simp [parentOf, hq, hpo]
          rw [chain_cons hpar hol] at hc
          have hoo : OwnedIn t.P p o := (EndFree.ownedIn_parent hw hq hpo).2 ho
          rcases List.mem_cons.1 hc with rfl | hc
          · exact hoo
          · exact ownedIn_up hw n o (by omega) r ⟨lt_of_getElem? hpr, .inr hc⟩ hoo

/-- An authority on the origin chain above an authority `g` that has effective `Modify` on every
leaf of a root place `p` has an effective mode on no leaf (Spec 1 §43, §49.6): its leaves are
leaves of `p`, which `g` covers in `Modify`. -/
theorem above_root_ground {t : S3} (hw : WF3 t) {p g u l : Nat} {m : Mode} (hp : RootPlace t.P p)
    (hg : ∀ l ∈ footprint t.P p, Allows (effective t g l) .modify) (hu : u ∈ t.ancs g)
    (h : Allows (effective t u l) m) : False := by
  have hlt : ∀ i o, t.org i = some o → o < i := fun i o h => by
    simp only [S3.org] at h
    cases hi : t.A[i]? with
    | none => rw [hi] at h; cases h
    | some y => rw [hi] at h; exact hw.origins i y o hi h
  obtain ⟨z, hz, -, hzl, -⟩ := eff_present (allows_present h)
  obtain ⟨-, hleaf⟩ := hw.footprints u z hz l hzl
  obtain ⟨xu, wu, ru, hxu, hwu, wuo, hru, hlru, hwuf⟩ := hw.rootChain u z l hz hzl hleaf
  obtain ⟨lp, hlp⟩ := exists_mem_footprint hw (t.P.length - p + 1) p (by omega) hp.1
  obtain ⟨yg, hyg, -, hlpg, -, -⟩ := eff_modify (allows_modify (hg lp hlp))
  have hlpleaf := (mem_footprint.1 hlp).2.1
  obtain ⟨xg, wg, rg, hxg, hwg, wgo, hrg, hlprg, hwgf⟩ := hw.rootChain g yg lp hyg hlpg hlpleaf
  have hxu' : xu = g ∨ xu ∈ t.ancs g := by
    rcases hxu with rfl | hxu
    · exact .inr hu
    · exact .inr (chain_trans hlt (g + 1) g (Nat.lt_succ_self g) u hu xu hxu)
  have e : xu = xg := EndFree.chain_root_unique hlt (g + 1) g (Nat.lt_succ_self g) xu xg hxu' hxg
    (by simp [S3.org, hwu, wuo]) (by simp [S3.org, hwg, wgo])
  subst e
  rw [hwu] at hwg; cases hwg
  obtain rfl : rg = p := rootOf_unique hrg hp hlprg (mem_footprint.1 hlp).2.2
  have hlp' : l ∈ footprint t.P rg :=
    (hwgf l).1 ((hwuf l).2 (mem_footprint.2 ⟨(mem_footprint.1 (footprint_sub hw hlru
      (mem_footprint.2 ⟨by have := (mem_footprint.1 hlp).1; exact (hw.footprints u z hz l hzl).1,
        hleaf, ⟨(hw.footprints u z hz l hzl).1, .inl rfl⟩⟩))).1, hleaf, hlru⟩))
  obtain ⟨yg', hyg', hyga, hlg, hgm, -⟩ := eff_modify (allows_modify (hg l hlp'))
  exact no_eff_below_modify hyg' hyga hgm hlg hu h

/-- `free` by context `c'` (Spec 1 §70) keeps every useful authority attributable to another
context: it is held neither within the released place nor by a place that dies (as for `endUse`),
and it covers no leaf of the released unit: it is not the grounding authority of `c'`
(`attr_excl`), not above it (`above_root_ground`), and otherwise §70.3 (`FreeAccessOK`) or, for a
root authority, its holder (`rootHeldConv_active`) and `I1` exclude it. -/
theorem free_keeps {k : K} {s s' : SC} {reg : SyncReg} (hF : FramesC s) (hI : I1 s.flat)
    (hw : WF3 s.flat) (hND0 : NoDangling s.flat) {c c' p auth : Nat} (hcc : c ≠ c')
    (hne : s.stk c' ≠ []) (hp : FreePre k (s.view c') p auth)
    (hs' : s' = s.set (freeEff (s.view c') p)) (hND : NoDangling s'.flat) {u : Nat} {m : Mode}
    (h : CapAttr s reg c u m) (hu : Useful s u m) : ∀ y, s.A[u]? = some y → s'.A[u]? = some y := by
  have hP := parents_lt hw
  have hlt : ∀ i o, s.flat.org i = some o → o < i := fun i o h => by
    simp only [S3.org] at h
    cases hi : s.flat.A[i]? with
    | none => rw [hi] at h; cases h
    | some y => rw [hi] at h; exact hw.origins i y o hi h
  have hvA : ∀ a l, effective (s.view c') a l = effective s.flat a l :=
    fun a l => effective_of_A rfl a l
  have hroot : RootPlace s.P p := EndFree.rootPlace_of_ownedRoot hp.ownedRoot
  obtain ⟨g, -, ⟨-, hgx, hge⟩, hall⟩ := hp.access
  have hg : UnrestrictedAttr s c' g .modify := attr_of_exercisable hne hgx
  have hge' : ∀ l ∈ footprint s.P p, Allows (effective s.flat g l) .modify :=
    fun l hl => by rw [← hvA]; exact hge l hl
  have hget : ∀ (a : Nat) (y : Authority), s.A[a]? = some y →
      ¬ ((∃ l ∈ y.footprint, FreedPlace s.P p l) ∨ heldIn s.P p y.holder) →
      HolderLive (freeS (s.view c') p) y.holder → s'.A[a]? = some y := fun a y hy hn hl => by
    subst hs'
    show (cleanup (freeS (s.view c') p)).A[a]? = some y
    rw [EndFree.cleanup_get, EndFree.freeS_get, show (s.view c').A[a]? = some y from hy]
    simp only [Option.map_some, show ¬ ((∃ l ∈ y.footprint, FreedPlace (s.view c').P p l) ∨
      heldIn (s.view c').P p y.holder) from hn, ↓reduceIte]
    simp only [show HolderLive (freeS (s.view c') p) y.holder from hl, ↓reduceIte]
  have hfreeDead : ∀ q, FreedPlace s.P p q → ¬ (freeS (s.view c') p).Usable q := fun q hq hu => by
    have := EndFree.dead_false hu
    simp [freeS, show FreedPlace (s.view c').P p q from hq] at this
  -- the covering condition, given the two holder conditions
  have hcov : ∀ (a : Nat) (y : Authority) (m : Mode), CapAttr s reg c a m → Useful s a m →
      s.A[a]? = some y → ¬ heldIn s.P p y.holder → HolderLive (freeS (s.view c') p) y.holder →
      ¬ ∃ l ∈ y.footprint, FreedPlace s.P p l := fun a y m ha has hy hnh hl ⟨l₀, hl₀, hfr⟩ => by
    obtain ⟨l₁, hl₁⟩ := has
    have hya : y.active = true := ha.active hy
    by_cases hag : a = g
    · subst hag; exact attr_excl hF.nodup hI hw hcc hg ha.unrestricted
    by_cases hanc : a ∈ s.flat.ancs g
    · exact above_root_ground hw hroot hge' hanc hl₁
    have hleaf := (hw.footprints a y hy l₀ hl₀)
    cases hyo : y.origin with
    | some o =>
      have hok := (hall a (List.mem_range.2 (lt_of_getElem? hy))).resolve_left (by
        rintro (h | h)
        · exact hag h
        · exact hanc h)
      unfold FreeAccessOK OptP at hok
      rw [show (s.view c').A[a]? = some y from hy] at hok
      have hfl : FreedLeaf (s.view c') p l₀ := by
        rcases hfr with hpart | hown
        · exact .inl (mem_footprint.2 ⟨hleaf.1, hleaf.2, hpart⟩)
        · refine .inr ⟨hleaf.2, ?_, hfreeDead l₀ (.inr hown)⟩
          have hus : s.flat.Usable l₀ := Decidable.byContradiction fun hnu =>
            hND0 a y hy hya l₀ hnu l₀ (mem_footprint.2 ⟨hleaf.1, hleaf.2, hleaf.1, .inl rfl⟩) hl₀
          exact S3.Usable.mono (s := s.view c') (s' := s.flat) rfl
            (fun f hf => mem_view_F hf) (fun q h => h) hus
      rcases hok hya (by rw [hyo]; simp) ⟨l₀, hl₀, hfl⟩ with h | h
      · exact hnh h
      · exact h hl
    | none =>
      obtain ⟨r, hr, hl₀r⟩ := exists_rootPlace hw (l₀ + 1) l₀ (Nat.lt_succ_self _) hleaf.1
      obtain ⟨pr, hpr, hho⟩ := rootHeldConv_active hw hI hND0 a y l₀ r hy hya hyo hl₀ hr hl₀r
      rcases hfr with hpart | hown
      · obtain rfl : r = p := rootOf_unique hr hroot hl₀r hpart
        obtain ⟨xa, wa, ra, hxa, hwa, wao, hra, hl₀ra, hwaf⟩ :=
          hw.rootChain a y l₀ hy hl₀ hleaf.2
        have horg : s.flat.org a = none := by
          show (s.A[a]?).bind (·.origin) = none
          rw [hy]; exact hyo
        have hxa' : xa = a := by
          rcases hxa with h | h
          · exact h
          · rw [S3.ancs, chain_none horg] at h; simp at h
        rw [hxa'] at hwa
        have hwa' : wa = y := by
          have h2 : s.flat.A[a]? = some y := hy
          rw [h2] at hwa; cases hwa; rfl
        rw [hwa'] at hwaf
        obtain rfl : ra = r := rootOf_unique hra hroot hl₀ra hpart
        obtain ⟨lp, hlp⟩ := exists_mem_footprint hw (s.flat.P.length - ra + 1) ra (by omega) hroot.1
        obtain ⟨yg, hyg, hyga, hlpg, hgm, -⟩ := eff_modify (allows_modify (hge' lp hlp))
        have hga : g ∉ s.flat.ancs a := by rw [S3.ancs, chain_none horg]; simp
        have := (hI a g y yg lp hag hy hyg hya hyga ((hwaf lp).2 hlp) hlpg hanc hga).2
        rw [hgm] at this; cases this
      · have hor : OwnedIn s.P p r := ownedIn_up hw (l₀ + 1) l₀ (Nat.lt_succ_self _) r hl₀r hown
        have hpr' : s.P[r]? = some pr := hpr
        cases hor with
        | direct hq ho hpo =>
          rw [hpr'] at hq; cases hq
          exact hnh (by rw [hho, ho]; exact hpo)
        | step hq ho hown' =>
          rw [hpr'] at hq; cases hq
          rw [hho, ho] at hl
          exact hfreeDead _ (.inr hown') hl
  induction h with
  | @base a m y f₀ hg' hy ha hm hfr hin =>
    intro y' hy'
    rw [hy] at hy'; cases hy'
    have hab : CapAttr s reg c a m := .base hg' hy ha hm hfr hin
    have hnh : ¬ heldIn s.P p y.holder := by rw [hfr]; exact id
    have hl : HolderLive (freeS (s.view c') p) y.holder := by
      rw [hfr]; exact mem_view_F (SC.mem_frames_of hin)
    exact hget a y hy (fun h => h.elim (hcov a y m hab hu hy hnh hl) hnh) hl
  | @held a q b m y hg' hy ha hm hp' hb hc ih =>
    intro y' hy'
    rw [hy] at hy'; cases hy'
    have hab : CapAttr s reg c a m := .held hg' hy ha hm hp' hb hc
    have hup : s.flat.Usable q := by
      have := hw.holders a _ hy ha; rw [hp'] at this; exact this
    obtain ⟨l₀, hl₀⟩ := footprint_ne hP _ q (Nat.le_refl _) hup.lt
    obtain ⟨zb, hzb, -, hzl, -⟩ := eff_present (allows_present (hc l₀ hl₀))
    have hbk := ih ⟨l₀, hc l₀ hl₀⟩ zb hzb
    have hnh : ¬ heldIn s.P p y.holder := fun hh => by
      rw [hp'] at hh
      exact not_attr_place hF.nodup hI hw hcc hy hp' hg
        (fun l hl => hge' l (footprint_sub hw hh hl)) hab.unrestricted
    have hl : HolderLive (freeS (s.view c') p) y.holder := by
      rw [hp']
      refine Decidable.byContradiction fun hnu => ?_
      have hnu' : ¬ s'.flat.Usable q := fun hu' => hnu (by
        refine S3.Usable.mono (s := freeS (s.view c') p) (s' := s'.flat)
          (by rw [hs']; rfl) (fun f hf => ?_) (fun q hq => by rw [hs'] at hq; exact hq) hu'
        exact mem_view_F (s := s) (c := c') (by rw [hs'] at hf; exact hf))
      exact hND b zb hbk (hb.active hzb) q hnu' l₀ (by rw [hs']; exact hl₀) hzl
    exact hget a y hy (fun h => h.elim (hcov a y m hab hu hy hnh hl) hnh) hl

/-- L1 (`local_loss`, C45) for `free` (Spec 1 §70). Under `DDSound` (Spec 1 §80), from a
state reached by an `EncapsulatedTrace` from an initial state (Spec 1 §47). -/
theorem local_loss_free {ks : KShared} {L : MutexLayout} {statics : Statics} {lbls : List Label}
    {st st' : SC × SyncReg × ArenaReg} {c' p auth : Nat} (hdd : DDSound ks.toK)
    (hst : StaticsOK statics)
    (htr : EncapsulatedTrace pm ks L (SC.ofS3 (S3.init statics), [], []) lbls st)
    (h : LStep ks L (.kernel c' (.free p auth)) st st') (c l : Nat)
    (hd : capRank (cap st'.1 st'.2.1 c l) < capRank (cap st.1 st.2.1 c l)) :
    (Label.kernel c' (.free p auth)).requester = c := by
  have hk := (encapsulated_inv hdd hst htr).1
  have hk' := lstep_kInvCA hdd h hk
  refine Decidable.byContradiction fun hctx => ?_
  have hcc : c ≠ c' := fun e => hctx (e ▸ rfl)
  cases h with
  | @kernel s s' reg ar _ _ hs =>
    obtain ⟨hF, hw, hI⟩ := hk.parts
    have hlive := opStepC_live hs
    obtain ⟨o, hR, ho⟩ := hs
    cases hR with
    | reject => cases ho
    | ok hp =>
      cases ho
      have hr : EndFree.OnlyReleases s.flat (s.set (freeEff (s.view c') p)).flat :=
        (EndFree.freeS_releases (s.view c') p).trans (EndFree.cleanup_releases _)
      refine absurd hd (Nat.not_lt.2 (releases_cap_mono (s' := s.set (freeEff (s.view c') p))
        (reg := reg) hw hr (fun f hf => hf) rfl (fun u m hu hus => ?_) l))
      obtain ⟨y, hy⟩ : ∃ y, s.A[u]? = some y := ⟨_, List.getElem?_eq_getElem hu.lt⟩
      exact ⟨y, free_keeps hF hI hw hk.1.2.1.2.2 hcc (hF.nonempty c' hlive) hp rfl
        hk'.1.2.1.2.2 hu hus y hy, hu.active hy⟩

/-! ## `spawnVal` (C4, C5) -/

open TransferPreserveAux in
/-- The yield of C5.3 changes only holders (Spec 1 §42). -/
theorem yield_skel (t : SC) (ps : List Nat) (f : Nat) : SameSkel t.flat (yieldEff t ps f).flat := by
  refine ⟨length_mapI _ 0 t.A, fun j => ?_⟩
  show ((mapI (yieldF ps f) 0 t.A)[j]?).map skel = (t.A[j]?).map skel
  rw [getElem?_mapI]
  cases t.A[j]? with
  | none => rfl
  | some y => simp only [Option.map_some, yieldF]; split <;> rfl

open TransferPreserveAux in
/-- An authority exercisable by `c'` before the yield (Spec 1 §43, C2) is attributable after
the yield to `c'` or to the context `d` whose stack holds the yield frame `f` (C43): the
yielded parameters are frame-held and move from the current frame of `c'` to `f`. -/
theorem attr_yield {t : SC} {ps : List Nat} {f c' d g : Nat} {m : Mode} (hne : t.stk c' ≠ [])
    (hf : f ∈ t.stk d) (hp : ∀ a ∈ ps, ∀ y, t.A[a]? = some y → ∃ g, y.holder = .frame g)
    (h : (t.view c').ExercisableAt g m) :
    UnrestrictedAttr (yieldEff t ps f) c' g m ∨ UnrestrictedAttr (yieldEff t ps f) d g m := by
  have hget : ∀ a y, t.A[a]? = some y → (yieldEff t ps f).A[a]? = some (yieldF ps f a y) :=
    fun a y hy => by
      show (mapI (yieldF ps f) 0 t.A)[a]? = _
      rw [getElem?_mapI, hy]; simp
  induction h with
  | @base a m y hy ha hm hfr =>
    by_cases hap : a ∈ ps
    · refine .inr (.base (hget a y hy) (by unfold yieldF; split <;> exact ha)
        (by unfold yieldF; split <;> exact hm) ?_ hf)
      simp [yieldF, hap]
    · refine .inl (.base (hget a y hy) (by unfold yieldF; split <;> exact ha)
        (by unfold yieldF; split <;> exact hm) ?_ (view_top_mem (s := t) hne))
      simp [yieldF, hap, hfr]
  | @held a q b m y hy ha hm hq _ hc ih =>
    have hap : a ∉ ps := fun hap => by
      obtain ⟨g, hg⟩ := hp a hap y hy
      rw [hq] at hg; cases hg
    have hy' : (yieldEff t ps f).A[a]? = some y := by rw [hget a y hy]; simp [yieldF, hap]
    have hc' : ∀ l ∈ footprint (yieldEff t ps f).P q,
        Allows (effective (yieldEff t ps f).flat b l) m := fun l hl => by
      rw [(yield_skel t ps f).effective, ← effective_of_A (t := t.view c') (t' := t.flat) rfl]
      exact hc l hl
    rcases ih with ih | ih
    · exact .inl (.held hy' ha hm hq ih hc')
    · exact .inr (.held hy' ha hm hq ih hc')

/-- A transfer (Spec 1 §63 effect) whose source is covered in `Modify` by an authority
attributable in `Modify` to a context `d ≠ c` does not lower `cap` of `c` (as
`transfer_cap_mono`, with the grounding authority given). -/
theorem transfer_cap_mono_g {s : SC} {reg : SyncReg} (hF : FramesC s) (hI : I1 s.flat)
    (hw : WF3 s.flat) {c d c' g src dst : Nat} (hcd : c ≠ d) (hg : UnrestrictedAttr s d g .modify)
    (hge : ∀ l ∈ footprint s.P src, Allows (effective s.flat g l) .modify) (l : Nat) :
    capRank (cap s reg c l) ≤ capRank (cap (transferEffC s c' src dst) reg c l) := by
  have hsk : SameSkel s.flat (transferEffC s c' src dst).flat :=
    transfer_skel (s.view c') src dst
  have hkeep : ∀ u m y, CapAttr s reg c u m → s.A[u]? = some y → ¬ heldIn s.P src y.holder :=
    fun u m y hu hy hh => by
      cases hh' : y.holder with
      | frame f => rw [hh'] at hh; exact hh
      | place q =>
        rw [hh'] at hh
        exact not_attr_place hF.nodup hI hw hcd hy hh' hg
          (fun l hl => hge l (footprint_sub hw hh hl)) hu.unrestricted
  refine cap_transport_u (s' := transferEffC s c' src dst) (reg' := reg) hw (fun f hf => hf)
    (fun p _ l hl => by
      have hl' : l ∈ footprint (transferEff (s.view c') src dst).P p := hl
      rwa [transfer_footprint] at hl')
    (fun u m y hu _ hy => ⟨y, ?_, rfl, rfl, rfl⟩)
    (fun u m hu _ => notGuarded_of_skel hsk (fun e he => ⟨e, he, rfl⟩) hu.notGuarded)
    (fun u m l _ hal => by rw [hsk.effective]; exact hal) l
  show (transferEff (s.view c') src dst).A[u]? = some y
  unfold transferEff
  simp only [List.getElem?_map]
  rw [show (s.view c').A[u]? = some y from hy]
  have hk : ¬ heldIn (s.view c').P src y.holder := hkeep u m y hu hy
  simp [hk]

open TransferPreserveAux in
/-- The transfer phases of the by-value composite (C5.2), read on the states where the
parameters are already yielded (`yield_transfers`): no phase lowers `cap` of a context `c` other
than the creator `c'` and the new context `d`. `KBase` holds at each phase, as in
`transfers_base`. -/
theorem transfers_cap_mono {k : K} {fin : S3} {reg : SyncReg} {c c' d f : Nat} {ps : List Nat}
    (hcc : c ≠ c') (hcd : c ≠ d) (l : Nat) :
    ∀ (t : SC) (vs : List (Nat × Nat)), ValTransfersPre k fin c' t vs →
      KBase (yieldEff t ps f) → (∀ v ∈ vs, FrameOwned t.P v.2) →
      (∀ a ∈ ps, ∀ y, t.A[a]? = some y → ∃ g, y.holder = .frame g) → t.stk c' ≠ [] →
      f ∈ t.stk d →
      capRank (cap (yieldEff t ps f) reg c l) ≤
        capRank (cap (yieldEff (transfersEff c' t vs) ps f) reg c l)
  | _, [], _, _, _, _, _, _ => Nat.le_refl _
  | t, v :: vs, ⟨hpre, hrest⟩, hk, hown, hp, hne, hf => by
    simp only [transfersEff]
    have hcl : t.Live c' := SC.live_of_hasRight hpre.srcRight
    have hu : ∀ q, ((yieldEff t ps f).view c').Usable q ↔ (t.view c').Usable q := fun q =>
      S3.Usable.congr (s' := (yieldEff t ps f).view c') (s := t.view c') rfl
        (by rw [yield_view hcl]) rfl
    have hdeps : ∀ x ∈ movedDeps ((yieldEff t ps f).view c') v.1,
        ((yieldEff t ps f).view c').Active x := by
      intro x hx
      have hmd : movedDeps ((yieldEff t ps f).view c') v.1 = movedDeps (t.view c') v.1 := by
        rw [yield_view hcl]; rfl
      rw [hmd] at hx
      exact (yield_active (v := t.view c') (ps := ps) (f := f)).2 (hpre.depsValid x hx)
    have hown₀ : FrameOwned ((yieldEff t ps f).view c').P v.2 := hown v (List.mem_cons_self ..)
    have hk₁ := transfer_base hk hcl ((hu _).2 hpre.srcUsable) ((hu _).2 hpre.dstUsable) hdeps
      hpre.sameShape hpre.disjoint
      (transfer_usable_frameOwned ((hu _).2 hpre.dstUsable) hown₀)
    obtain ⟨hF, hw, hI, -⟩ := hk
    have hstep : capRank (cap (yieldEff t ps f) reg c l) ≤
        capRank (cap (transferEffC (yieldEff t ps f) c' v.1 v.2) reg c l) := by
      obtain ⟨g, -, hgx, hge⟩ := hpre.srcRight
      have hge' : ∀ l ∈ footprint (yieldEff t ps f).P v.1,
          Allows (effective (yieldEff t ps f).flat g l) .modify := fun l hl => by
        rw [(yield_skel t ps f).effective, ← effective_of_A (t := t.view c') (t' := t.flat) rfl]
        exact hge l hl
      rcases attr_yield hne hf hp hgx with hg | hg
      · exact transfer_cap_mono_g hF hI hw hcc hg hge' l
      · exact transfer_cap_mono_g hF hI hw hcd hg hge' l
    rw [yield_transfer hp] at hk₁ hstep
    refine Nat.le_trans hstep (transfers_cap_mono hcc hcd l (transferEffC t c' v.1 v.2) vs hrest
      hk₁ (fun w hw => ?_) (fun a ha y hy => ?_) hne hf)
    · exact transfer_frameOwned (hown w (List.mem_cons_of_mem _ hw))
    · obtain ⟨y₀, hy₀, e⟩ := transfer_frame_held hy
      obtain ⟨g, hg⟩ := hp a ha y₀ hy₀
      exact ⟨g, by rw [e ⟨g, hg⟩, hg]⟩

open TransferPreserveAux in
/-- L1 (`local_loss`, C45) for `spawnVal` (C4, C5): the composite is `spawn` with the
parameters followed by the transfer phases (`create_yield`, `yield_transfers`); the new context
had no `cap` before the step. Under `DDSound` (Spec 1 §80), from a state reached by an
`EncapsulatedTrace` from an initial state (Spec 1 §47). -/
theorem local_loss_spawnVal {ks : KShared} {L : MutexLayout} {statics : Statics} {lbls : List Label}
    {st st' : SC × SyncReg × ArenaReg} {c' : Nat} {ps : List Nat} {ls : LocalShape}
    {vs : List (Nat × Nat)} (hdd : DDSound ks.toK) (hst : StaticsOK statics)
    (htr : EncapsulatedTrace pm ks L (SC.ofS3 (S3.init statics), [], []) lbls st)
    (h : LStep ks L (.spawnVal c' ps ls vs) st st') (c l : Nat)
    (hd : capRank (cap st'.1 st'.2.1 c l) < capRank (cap st.1 st.2.1 c l)) :
    (Label.spawnVal c' ps ls vs).requester = c := by
  have hk := (encapsulated_inv hdd hst htr).1
  refine Decidable.byContradiction fun hctx => ?_
  have hcc : c ≠ c' := fun e => hctx (e ▸ rfl)
  cases h with
  | @spawnVal s s' reg ar _ _ _ _ hs =>
    obtain ⟨hF, hw, -⟩ := hk.parts
    have hR := hs
    cases hR with
    | ok hpre =>
      by_cases hcl : c < s.C.length
      · have hlt : ∀ a ∈ ps, a < s.A.length := fun a ha => by
          have := hpre.params a ha
          unfold OptP at this; split at this
          · exact lt_of_getElem? ‹_›
          · exact this.elim
        have hframe : ∀ a ∈ ps, ∀ y, (spawnCreate s c' ls).A[a]? = some y →
            ∃ g, y.holder = .frame g := by
          intro a ha y hy
          have hp := hpre.params a ha
          have hy' : (spawnCreate s c' ls).A[a]? = s.A[a]? := by
            show (mapI _ 0 s.A ++ _)[a]? = _
            rw [List.getElem?_append_left (by rw [length_mapI]; exact hlt a ha), getElem?_mapI]
            cases s.A[a]? <;> simp
          rw [hy'] at hy
          have hy₂ : (s.view c').A[a]? = some y := hy
          rw [hy₂] at hp
          exact ⟨_, hp.2.1⟩
        have hb₀ : KBase (yieldEff (spawnCreate s c' ls) ps s.nF) := by
          rw [create_yield hlt]
          exact spawn_base hk hpre.creatorLive hpre.params hpre.localsOK
        have hstkc : ∀ (ps' : List Nat), (spawnEff s c' ps' ls).stk c = s.stk c := fun ps' => by
          unfold SC.stk
          rw [show (spawnEff s c' ps' ls).C[c]? = s.C[c]? from List.getElem?_append_left hcl]
        have hstk' : (spawnCreate s c' ls).stk c' ≠ [] := by
          rw [show spawnCreate s c' ls = spawnEff s c' [] ls from rfl]
          by_cases hc'l : c' < s.C.length
          · unfold SC.stk
            rw [show (spawnEff s c' [] ls).C[c']? = s.C[c']? from
              List.getElem?_append_left hc'l]
            exact hpre.creatorLive
          · exfalso; apply hpre.creatorLive
            unfold SC.stk; rw [List.getElem?_eq_none (Nat.le_of_not_lt hc'l)]
        have hnF : s.nF ∈ (spawnCreate s c' ls).stk s.C.length := by
          have hC : (spawnCreate s c' ls).C[s.C.length]? =
              some ⟨[s.nF], Life.live, (s.stk c').head?⟩ := by
            show (s.C ++ [_])[s.C.length]? = _
            simp
          unfold SC.stk; rw [hC]; simp
        have h1 : capRank (cap s reg c l) ≤ capRank (cap (spawnEff s c' ps ls) reg c l) :=
          enter_cap_mono hF hw hcc hpre.creatorLive hpre.params hpre.localsOK ⟨rfl, rfl⟩
            (fun f hf => by rw [hstkc]; exact hf) l
        have h2 := transfers_cap_mono (reg := reg) (k := ks.toK)
          (fin := (spawnValEff s c' ps ls vs).flat) (f := s.nF) (ps := ps) hcc
          (Nat.ne_of_lt hcl) l (spawnCreate s c' ls) vs hpre.transfers hb₀
          (fun v hv => by
            have := spawn_frameOwned (ps := []) (c := c') (hpre.freshDst v hv)
            exact this) hframe hstk' hnF
        rw [create_yield hlt] at h2
        exact absurd hd (Nat.not_lt.2 (Nat.le_trans h1 h2))
      · have hnil : s.stk c = [] := by
          unfold SC.stk; rw [List.getElem?_eq_none (Nat.le_of_not_lt hcl)]
        rw [show cap (s, reg, ar).1 (s, reg, ar).2.1 c l = none from cap_nil hnil] at hd
        exact absurd hd (Nat.not_lt_zero _)


/-! ## L1 -/

/-- **Theorem 12c**, L1 (C45: "On an `EncapsulatedTrace` (C51), a strict reduction of
`cap(·,c′,l)` occurs only at a step of `c′` itself"; `OB-C17`): under `DDSound` (Spec 1 §80) and
well-formed statics (§47), from any state reached by an `EncapsulatedTrace` from the initial state
of Spec 1 §47, a step of the trace (`EncapStep`, C51.1) that strictly lowers `cap` of a context `c`
on a leaf is a step of `c`. Every label, the atomic step cases included (C39, "Authority-machine
operation coverage"); one lemma per label. -/
theorem local_loss {ks : KShared} {L : MutexLayout} {statics : Statics} {lbls : List Label}
    {st st' : SC × SyncReg × ArenaReg} {lbl : Label} (hdd : DDSound ks.toK)
    (hst : StaticsOK statics)
    (htr : EncapsulatedTrace pm ks L (SC.ofS3 (S3.init statics), [], []) lbls st)
    (he : EncapStep pm ks L st lbl st') (h : LStep ks L lbl st st') (c l : Nat)
    (hd : capRank (cap st'.1 st'.2.1 c l) < capRank (cap st.1 st.2.1 c l)) :
    lbl.requester = c := by
  cases lbl with
  | kernel c' op =>
    cases op with
    | derive => exact local_loss_derive hdd hst htr h c l hd
    | split => exact local_loss_split hdd hst htr h c l hd
    | release => exact local_loss_release hdd hst htr h c l hd
    | transfer => exact local_loss_transfer hdd hst htr h c l hd
    | depend => exact local_loss_inert (h := h) hdd hst htr (by exact trivial) c l hd
    | enter => exact local_loss_enter hdd hst htr h c l hd
    | exit => exact local_loss_exit hdd hst htr h c l hd
    | read => exact local_loss_inert (h := h) hdd hst htr (by exact trivial) c l hd
    | write => exact local_loss_inert (h := h) hdd hst htr (by exact trivial) c l hd
    | writeShared => exact local_loss_inert (h := h) hdd hst htr (by exact trivial) c l hd
    | pin => exact local_loss_inert (h := h) hdd hst htr (by exact trivial) c l hd
    | unpin => exact local_loss_inert (h := h) hdd hst htr (by exact trivial) c l hd
    | endUse => exact local_loss_endUse hdd hst htr h c l hd
    | free => exact local_loss_free hdd hst htr h c l hd
    | alloc => exact local_loss_alloc hdd hst htr h c l hd
    | store => exact local_loss_store hdd hst htr h c l hd
  | spawn => exact local_loss_spawn hdd hst htr h c l hd
  | terminate => exact local_loss_terminate hdd hst htr h c l hd
  | join => exact local_loss_inert (h := h) hdd hst htr (by exact trivial) c l hd
  | deriveSync => exact local_loss_deriveSync he h c
  | newMutex => exact local_loss_newMutex hdd hst htr h c l hd
  | acquire => exact local_loss_acquire hdd hst htr h c l hd
  | unlock => exact local_loss_unlock hdd hst htr h c l hd
  | resetLock => exact local_loss_inert (h := h) hdd hst htr (by exact trivial) c l hd
  | spawnVal => exact local_loss_spawnVal hdd hst htr h c l hd
  | newArena => exact local_loss_inert (h := h) hdd hst htr (by exact trivial) c l hd
  | issue => exact local_loss_issue hdd hst htr h c l hd
  | reset => exact local_loss_reset hdd hst htr h c l hd
  | readShared => exact local_loss_inert (h := h) hdd hst htr (by exact trivial) c l hd
  | writeShared => exact local_loss_inert (h := h) hdd hst htr (by exact trivial) c l hd
  | cas => exact local_loss_inert (h := h) hdd hst htr (by exact trivial) c l hd

end Ern.ConcurrencyModel
