import Ern.Concurrency.FullEncap.SpawnValCap
import Ern.Concurrency.FullEncap.Dying

/-!
# Last acquire and protected data

Brief of milestone 4, slice 3, complement, task 5 (`corpus-spec2-m3.md` v14 §2 terdecies,
"Dernière prise", "Donnée protégée, en trois cas"). On a `RunFull` from the initial state:

* without a grant, the covering descendants of a live entry are empty (`GrantDiscipline`, WC5.2
  C22, established on the reached states by `trace_inv`);
* with a grant `g`, every covering descendant is `g` or was created after the last `acquire` of
  the entry by a step of case 2 of the closure (`last_acquire`);
* every step touching a protected leaf of an entry live before and after it falls in one of three
  cases, read on the grant before the step (`three_cases`): no grant, impossible; an active grant,
  a capacity from `g` or a descendant of `g`; an inactive grant, a capacity from the covering
  descendants;
* the fact "Donnée protégée" of §2 duodecies, v14 wording (`protected_cap_run`).

The provenance results do not order accesses: W-AG has a race on the strict graph
(`W_AG_strict`), and W-AG-J is ordered by `terminate` and `join` (WC5.2 C46).
-/

set_option autoImplicit false

namespace Ern.Concurrency.FullEncap

open Ern.MemoryModel Ern.MemoryModel.Access Ern.Concurrency Ern.Concurrency.MutexReal
open SyncPreserveAux SyncInitAux TransferPreserveAux

/-! ## Capacities and their provenance -/

/-- `Allows` is antitone in the requested mode (Spec 1 §43). -/
theorem allows_mono {e : Option Mode} {m m' : Mode} (h : Allows e m') (hm : m.le m') :
    Allows e m := by
  cases e with
  | none => exact h.elim
  | some x =>
    show m.le x
    have h' : m'.le x := h
    rcases hm with rfl | rfl
    · exact Or.inl rfl
    · rcases h' with h1 | h1
      · cases h1
      · exact Or.inr h1

/-- The mode order is transitive (Spec 1 §43). -/
theorem Mode.le_trans' {m m' m'' : Mode} (h : m.le m') (h' : m'.le m'') : m.le m'' := by
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · rcases h' with h' | h'
    · cases h'
    · exact Or.inr h'

/-- `Attr5` is antitone in the requested mode (WC5.2 C43). -/
theorem attr5_mono {s : SC} {reg : SyncReg} {c x : Nat} {m m' : Mode} (h : Attr5 s reg c x m')
    (hm : m.le m') : Attr5 s reg c x m := by
  induction h with
  | base hg hy ha hm' hf hin => exact .base hg hy ha (Mode.le_trans' hm hm') hf hin
  | held hg hy ha hm' hp _ hc ih =>
    exact .held hg hy ha (Mode.le_trans' hm hm') hp (ih hm) fun l hl => allows_mono (hc l hl) hm

/-- A capacity is attained by an attributable authority (WC5.2 C43, `cap5`). -/
theorem cap5_attained {s : SC} {reg : SyncReg} {c l : Nat} {m : Mode}
    (h : Allows (cap5 s reg c l) m) : ∃ x ∈ List.range s.A.length,
      Attr5 s reg c x m ∧ Allows (effective s.flat x l) m := by
  by_cases h1 : CapAt5 s reg c l .modify
  · obtain ⟨x, hx, ha, he⟩ := h1
    have hm : m.le .modify := Or.inr rfl
    exact ⟨x, hx, attr5_mono ha hm, allows_mono he hm⟩
  · by_cases h2 : CapAt5 s reg c l .observe
    · simp only [cap5, h1, h2, ↓reduceIte] at h
      have hm : m = .observe := by
        rcases (h : m.le .observe) with h | h
        · exact h
        · cases h
      subst hm
      exact h2
    · simp only [cap5, h1, h2, ↓reduceIte] at h; exact h.elim

/-- The capacity of `c` on `l` in mode `m`, attained by an authority attributable to `c` without
a live `guarded` (WC5.2 C43) that belongs to `S` (brief of the complement, "Capacité de provenance
donnée"). -/
def ProvCap (st : SC × SyncReg × ArenaReg) (S : Nat → Prop) (c l : Nat) (m : Mode) : Prop :=
  ∃ x ∈ List.range st.1.A.length, S x ∧ Attr5 st.1 st.2.1 c x m ∧
    Allows (effective st.1.flat x l) m

/-- `CapReq` (slice 3, task 4) with every capacity attained from `S`; for the by-value `spawn`,
`Modify` on the leaves of the sources (task 4 of the complement). -/
def CapFrom (k : K) (st : SC × SyncReg × ArenaReg) (S : Nat → Prop) : Label → Nat → Prop
  | .kernel c (.read _ _), l | .kernel c (.writeShared _ _), l => ProvCap st S c l .observe
  | .kernel c (.write _ _), l | .kernel c (.store _ _), l | .kernel c (.transfer _ _), l =>
      ProvCap st S c l .modify
  | .kernel c (.endUse p), l | .kernel c (.free p _), l =>
      l ∈ footprint st.1.P p → ProvCap st S c l .modify
  | .kernel c (.alloc pr ow _), l =>
      (l ∈ footprint st.1.P pr → ProvCap st S c l .observe ∧
        (ProvCap st S c l .modify ∨ k.SharedMutable l)) ∧
      (l = ow → ProvCap st S c l .modify)
  | .issue c _ _ _, l | .newMutex c _, l => ProvCap st S c l .modify
  | .acquire c _, l | .unlock c _, l | .resetLock c _, l => ProvCap st S c l .observe
  | .spawnVal c _ _ vs, l => (∃ v ∈ vs, l ∈ footprint st.1.P v.1) → ProvCap st S c l .modify
  | _, _ => True

/-- A capacity whose every attaining authority is in `S` is a capacity of provenance `S`. -/
theorem prov_of {st : SC × SyncReg × ArenaReg} {S : Nat → Prop} {c l : Nat} {m : Mode}
    (hS : ∀ x m, Attr5 st.1 st.2.1 c x m → Allows (effective st.1.flat x l) m → S x)
    (h : Allows (cap5 st.1 st.2.1 c l) m) : ProvCap st S c l m := by
  obtain ⟨x, hx, ha, he⟩ := cap5_attained h
  exact ⟨x, hx, hS x m ha he, ha, he⟩

/-- A capacity of provenance `S` is an attributable authority with a present effective mode. -/
theorem some_of_prov {st : SC × SyncReg × ArenaReg} {S : Nat → Prop} {c l : Nat} {m : Mode}
    (h : ProvCap st S c l m) : ∃ x m', Attr5 st.1 st.2.1 c x m' ∧
      Allows (effective st.1.flat x l) m' :=
  let ⟨x, _, _, ha, he⟩ := h; ⟨x, m, ha, he⟩

/-- Brief of the complement, task 5, step form: a step touching a leaf `l` that does not die
(task 3), with the required capacity of slice 3 (`CapReq`) and, for the by-value `spawn`, the
capacity on the sources before the step (task 4), is made with the required capacity of
provenance `S`, as soon as every attributable authority with a present effective mode on `l` is
in `S`; and some attributable authority has a present effective mode on `l`. -/
theorem capFrom_step {k : K} {L : MutexLayout} {st st' : SC × SyncReg × ArenaReg} {lbl : Label}
    {l : Nat} {S : Nat → Prop} (hs : LStep k L lbl st st')
    (hS : ∀ c x m, Attr5 st.1 st.2.1 c x m → Allows (effective st.1.flat x l) m → S x)
    (hlt : l < st.1.P.length) (hcap : CapReq k st lbl l) (hnd : ¬ Dying st.1 st'.1 l)
    (hsv : ∀ c ps ls vs, lbl = .spawnVal c ps ls vs → ∀ v ∈ vs, l ∈ footprint st.1.P v.1 →
      ∃ x ∈ List.range st.1.A.length, Attr5 st.1 st.2.1 c x .modify ∧
        Allows (effective st.1.flat x l) .modify)
    (ht : TouchesF L st lbl l) :
    CapFrom k st S lbl l ∧ ∃ x m, Attr5 st.1 st.2.1 lbl.ctx x m ∧
      Allows (effective st.1.flat x l) m := by
  cases hs with
  | @kernel s s' reg ar c op hk =>
    cases op with
    | read a ls =>
      have h := prov_of (hS c) hcap; exact ⟨h, some_of_prov h⟩
    | writeShared a ls =>
      have h := prov_of (hS c) hcap; exact ⟨h, some_of_prov h⟩
    | write a ls =>
      have h := prov_of (hS c) hcap; exact ⟨h, some_of_prov h⟩
    | store a p =>
      have h := prov_of (hS c) hcap; exact ⟨h, some_of_prov h⟩
    | transfer src dst =>
      have h := prov_of (hS c) hcap; exact ⟨h, some_of_prov h⟩
    | endUse p =>
      rcases ht with hp | hd
      · have h := prov_of (hS c) (hcap hp)
        exact ⟨fun _ => h, some_of_prov h⟩
      · obtain ⟨t, hR, rfl⟩ := viewStep_ok hk
        obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hR
        exact (hnd hd).elim
    | free p au =>
      obtain ⟨t, hR, rfl⟩ := viewStep_ok hk
      obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hR
      exact (hnd ht).elim
    | exit =>
      obtain ⟨-, hg⟩ := hk
      obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hg
      exact (hnd ht).elim
    | enter ps ls => exact absurd hlt (Nat.not_lt.2 ht)
    | alloc pr ow ls =>
      obtain ⟨hpr, how⟩ := hcap
      refine ⟨⟨fun hl => ?_, fun hl => prov_of (hS c) (how hl)⟩, ?_⟩
      · obtain ⟨h1, h2⟩ := hpr hl
        exact ⟨prov_of (hS c) h1, h2.imp (prov_of (hS c)) id⟩
      · rcases ht with hl | hl | hl
        · exact some_of_prov (prov_of (S := S) (hS c) (hpr hl).1)
        · exact some_of_prov (prov_of (S := S) (hS c) (how hl))
        · exact absurd hlt (Nat.not_lt.2 hl)
    | _ => exact ht.elim
  | @spawn s s' reg ar c ps ls h => exact absurd hlt (Nat.not_lt.2 ht)
  | @terminate s s' reg ar c h =>
    obtain ⟨-, hg⟩ := h
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hg
    exact (hnd ht).elim
  | @spawnVal s s' reg ar c ps ls vs h =>
    rcases ht with hl | ⟨v, hv, hl⟩
    · exact absurd hlt (Nat.not_lt.2 hl)
    · obtain ⟨x, hx, ha, he⟩ := hsv c ps ls vs rfl v hv hl
      exact ⟨fun _ => ⟨x, hx, hS c x _ ha he, ha, he⟩, x, _, ha, he⟩
  | @newMutex s reg ar c g st₁ h =>
    have h := prov_of (hS c) hcap; exact ⟨h, some_of_prov h⟩
  | @acquire s reg ar c i st₁ h =>
    have h := prov_of (hS c) hcap; exact ⟨h, some_of_prov h⟩
  | @unlock s reg ar c i st₁ h =>
    have h := prov_of (hS c) hcap; exact ⟨h, some_of_prov h⟩
  | @resetLock s reg ar c i st₁ h =>
    have h := prov_of (hS c) hcap; exact ⟨h, some_of_prov h⟩
  | @issue s reg ar c i region dst st₁ h =>
    have h := prov_of (hS c) hcap; exact ⟨h, some_of_prov h⟩
  | _ => exact ht.elim

/-! ## An attributable authority on a protected leaf descends from `guarded` -/

/-- Brief of the complement, task 5: under I1 (Spec 1 §50) and WC5.2 C21 item 1 (the `guarded` of
a live entry is active, of own mode `Modify`), an authority that is not a live `guarded` and has a
present effective mode on a leaf of `footprint(guarded)` is a covering descendant of `guarded`:
an ancestor of `guarded` has no effective mode there (Spec 1 §43.3), and an unrelated one would
contradict I1. -/
theorem cov_of_attr {L : MutexLayout} {s : SC} {reg : SyncReg} {e : SyncEntry}
    (hi1 : I1 s.flat) (hinv : SyncInv L s reg) (he : e ∈ reg) (hl : e.Live s) {x l : Nat}
    (hng : NotGuarded s reg x) (hfp : l ∈ s.flat.afp e.guarded)
    (hex : effective s.flat x l ≠ none) : CoveringDesc s e.guarded x := by
  have hg := hinv.guarded e he hl
  obtain ⟨yg, hyg, ya⟩ := hl
  have hyg' : s.A[e.guarded]? = some yg := hyg
  rw [hyg'] at hg
  obtain ⟨hgm, -⟩ := hg
  obtain ⟨z, hz, za, hlz, hnm⟩ := eff_present hex
  have hxg : x ≠ e.guarded := hng e he ⟨yg, hyg, ya⟩
  have hlg : l ∈ yg.footprint := by rw [afp_of hyg'] at hfp; exact hfp
  by_cases h1 : x ∈ s.flat.ancs e.guarded
  · have hmem := mem_descModes (t := s.flat) hyg ya hlg h1
    rw [hgm] at hmem
    exact absurd hmem hnm
  · by_cases h2 : e.guarded ∈ s.flat.ancs x
    · exact ⟨h2, ⟨z, hz, za⟩, l, by rw [afp_of hz]; exact hlz, hfp⟩
    · have := hi1 x e.guarded z yg l hxg hz hyg za ya hlz hlg h1 h2
      rw [hgm] at this; cases this.2

/-! ## The three cases -/

/-- Brief of the complement, task 5, "Trois cas": on a `RunFull` from the initial state, under
`DDSound`, for every step of a context `c`, every entry `e` live before and after it and every
leaf `l` of `footprint(e.guarded)` in the final footprint of the step, the grant being read before
the step:
* `grant = none`: no such step exists;
* `grant = some g` with `g` active: `c` has the required capacity (`CapFrom`) attained by `g` or a
  descendant of `g`;
* `grant = some g` with `g` inactive: `c` has the required capacity attained by a covering
  descendant of `e`.
Invariants used: I1 and WC5.2 C21 item 1 (`cov_of_attr`), C21 item 5 (`GrantSubtree`), C22
(`GrantDiscipline`); tasks 3 (`protected_not_dying_run`) and 4 (`spawnVal_cap_pre`) and the
capacity of slice 3 (`capacity_run`). -/
theorem three_cases {k : K} {L : MutexLayout} {statics : Statics}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} (hdd : DDSound k)
    (hstat : StaticsOK statics) (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], []))
    (h : RunFull k L σ lbls) {i : Nat} (hi : i < lbls.length) {e : SyncEntry}
    (he : e ∈ (σ i).2.1) (hl : e.Live (σ i).1) (hl' : e.Live (σ (i + 1)).1) {l : Nat}
    (hfp : l ∈ (σ i).1.flat.afp e.guarded) (ht : TouchesF L (σ i) lbls[i] l) :
    (e.grant = none → False) ∧
    (∀ g, e.grant = some g → (σ i).1.flat.Active g →
      CapFrom k (σ i) (fun x => x = g ∨ g ∈ (σ i).1.flat.ancs x) lbls[i] l) ∧
    (∀ g, e.grant = some g → ¬ (σ i).1.flat.Active g →
      CapFrom k (σ i) (CoveringDesc (σ i).1 e.guarded) lbls[i] l) := by
  obtain ⟨hk, hlib⟩ := runFull_inv hdd hstat h0 h (Nat.le_of_lt hi)
  have hinv := hlib.1.1
  have hi1 := hk.parts.2.2
  have hw := hk.parts.2.1
  obtain ⟨yg, hyg, ya⟩ := hl
  have hfpg : l ∈ yg.footprint := by rw [afp_of hyg] at hfp; exact hfp
  obtain ⟨hlt, hleaf⟩ := hw.footprints e.guarded yg hyg l hfpg
  have hcap := capacity_run hdd hstat h0 h hi hleaf hlt ht
  have hnd := protected_not_dying_run hdd hstat h0 h hi ⟨yg, hyg, ya⟩ hl' hfp
  have hsv : ∀ c ps ls vs, lbls[i] = .spawnVal c ps ls vs → ∀ v ∈ vs,
      l ∈ footprint (σ i).1.P v.1 → ∃ x ∈ List.range (σ i).1.A.length,
        Attr5 (σ i).1 (σ i).2.1 c x .modify ∧ Allows (effective (σ i).1.flat x l) .modify :=
    fun c ps ls vs hlb v hv hlv => (spawnVal_cap_pre hdd hstat h0 h hi hlb v hv l hlv).1
  have hcov : ∀ c x m, Attr5 (σ i).1 (σ i).2.1 c x m →
      Allows (effective (σ i).1.flat x l) m → CoveringDesc (σ i).1 e.guarded x :=
    fun c x m ha hex => cov_of_attr hi1 hinv he ⟨yg, hyg, ya⟩ ha.notGuarded hfp
      (ne_none_of_allows hex)
  obtain ⟨hcf, x, m, hax, hex⟩ := capFrom_step (h i hi).2 hcov hlt hcap hnd hsv ht
  refine ⟨fun hn => ?_, fun g hg ha => ?_, fun g hg _ => hcf⟩
  · exact hlib.1.2 e he ⟨yg, hyg, ya⟩ hn _ (List.mem_range.2 (Attr5.lt hax)) (hcov _ x m hax hex)
  · refine (capFrom_step (S := fun x => x = g ∨ g ∈ (σ i).1.flat.ancs x) (h i hi).2
      (fun c x m hax hex => ?_) hlt hcap hnd hsv ht).1
    exact hinv.grantSubtree e he ⟨yg, hyg, ya⟩ g hg ha x (hcov c x m hax hex)

/-- Brief of the complement, task 5, the fact "Donnée protégée" of §2 duodecies (v14 wording), for
the 28 kinds: on a `RunFull` from the initial state, under `DDSound`, no step touches a leaf
protected by an entry live before and after it without its context holding a capacity on that
leaf outside any chain through a live `guarded` (`cap5`, WC5.2 C43). -/
theorem protected_cap_run {k : K} {L : MutexLayout} {statics : Statics}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} (hdd : DDSound k)
    (hstat : StaticsOK statics) (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], []))
    (h : RunFull k L σ lbls) {i : Nat} (hi : i < lbls.length) {e : SyncEntry}
    (hl : e.Live (σ i).1) (hl' : e.Live (σ (i + 1)).1) {l : Nat}
    (hfp : l ∈ (σ i).1.flat.afp e.guarded) (ht : TouchesF L (σ i) lbls[i] l) :
    cap5 (σ i).1 (σ i).2.1 lbls[i].ctx l ≠ none := by
  obtain ⟨hk, hlib⟩ := runFull_inv hdd hstat h0 h (Nat.le_of_lt hi)
  obtain ⟨yg, hyg, ya⟩ := hl
  have hfpg : l ∈ yg.footprint := by rw [afp_of hyg] at hfp; exact hfp
  obtain ⟨hlt, hleaf⟩ := hk.parts.2.1.footprints e.guarded yg hyg l hfpg
  obtain ⟨-, x, m, hax, hex⟩ := capFrom_step (S := fun _ => True) (h i hi).2
    (fun _ _ _ _ _ => trivial) hlt (capacity_run hdd hstat h0 h hi hleaf hlt ht)
    (protected_not_dying_run hdd hstat h0 h hi ⟨yg, hyg, ya⟩ hl' hfp)
    (fun c ps ls vs hlb v hv hlv => (spawnVal_cap_pre hdd hstat h0 h hi hlb v hv l hlv).1) ht
  exact ne_none_of_allows (cap5_of hax hex)

/-- Brief of the complement, task 5, "Ensemble vide sans grant": on a `RunFull` from the initial
state, under `DDSound`, at every index where an entry is live with `grant = none`, its covering
descendants are empty (`GrantDiscipline`, WC5.2 C22, on the reached states by `runFull_inv`). -/
theorem empty_without_grant {k : K} {L : MutexLayout} {statics : Statics}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} (hdd : DDSound k)
    (hstat : StaticsOK statics) (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], []))
    (h : RunFull k L σ lbls) {n : Nat} (hn : n ≤ lbls.length) {e : SyncEntry}
    (he : e ∈ (σ n).2.1) (hl : e.Live (σ n).1) (hg : e.grant = none) :
    NoCoveringDesc (σ n).1 e.guarded :=
  (runFull_inv hdd hstat h0 h hn).2.1.2 e he hl hg

/-! ## Last acquire -/

/-- How a step changes the entry at index `i` of the registry (WC5.2 C12, C13, C16–C18 effects):
it is unchanged and the step is no `acquire` of `i`; or it has no grant; or the step is an
`acquire` of `i` that records the fresh identity `|A|` in an entry without grant. -/
theorem reg_step {k : K} {L : MutexLayout} {lbl : Label} {st st' : SC × SyncReg × ArenaReg}
    (hs : LStep k L lbl st st') {i : Nat} {e' : SyncEntry} (he' : st'.2.1[i]? = some e') :
    (st.2.1[i]? = some e' ∧ ∀ c, lbl ≠ .acquire c i) ∨ e'.grant = none ∨
    (∃ c e, lbl = .acquire c i ∧ st.2.1[i]? = some e ∧ e.grant = none ∧
      e' = { e with grant := some st.1.A.length }) := by
  cases hs with
  | @newMutex s reg ar c g st₁ hn =>
    obtain ⟨-, -, rfl⟩ := hn
    by_cases hi : i < reg.length
    · refine .inl ⟨?_, fun c' h => by cases h⟩
      have : (reg ++ [⟨g, none⟩])[i]? = reg[i]? := List.getElem?_append_left hi
      rw [← this]; exact he'
    · refine .inr (.inl ?_)
      have h1 : (reg ++ [(⟨g, none⟩ : SyncEntry)])[i]? = some e' := he'
      rw [List.getElem?_append_right (Nat.le_of_not_lt hi)] at h1
      have h2 := List.mem_of_getElem? h1
      rw [List.mem_singleton] at h2
      rw [h2]
  | @acquire s reg ar c i₀ st₁ ha =>
    obtain ⟨-, e₀, hi₀, ⟨-, hn, -⟩, -, rfl⟩ := ha
    have h1 : (reg.set i₀ { e₀ with grant := some s.A.length })[i]? = some e' := he'
    by_cases e : i₀ = i
    · subst e
      rw [List.getElem?_set_self (lt_of_getElem? hi₀)] at h1
      cases h1
      exact .inr (.inr ⟨c, e₀, rfl, hi₀, hn, rfl⟩)
    · rw [List.getElem?_set_ne e] at h1
      exact .inl ⟨h1, fun c' h => by cases h; exact e rfl⟩
  | @unlock s reg ar c i₀ st₁ hu =>
    obtain ⟨-, e₀, g₀, hi₀, -, -, -, -, rfl⟩ := hu
    have h1 : (reg.set i₀ { e₀ with grant := none })[i]? = some e' := he'
    by_cases e : i₀ = i
    · subst e
      rw [List.getElem?_set_self (lt_of_getElem? hi₀)] at h1
      cases h1; exact .inr (.inl rfl)
    · rw [List.getElem?_set_ne e] at h1
      exact .inl ⟨h1, fun c' h => by cases h⟩
  | @resetLock s reg ar c i₀ st₁ hr =>
    obtain ⟨-, e₀, hi₀, -, -, -, rfl⟩ := hr
    have h1 : (reg.set i₀ { e₀ with grant := none })[i]? = some e' := he'
    by_cases e : i₀ = i
    · subst e
      rw [List.getElem?_set_self (lt_of_getElem? hi₀)] at h1
      cases h1; exact .inr (.inl rfl)
    · rw [List.getElem?_set_ne e] at h1
      exact .inl ⟨h1, fun c' h => by cases h⟩
  | kernel => exact .inl ⟨he', fun c' h => by cases h⟩
  | spawn => exact .inl ⟨he', fun c' h => by cases h⟩
  | terminate => exact .inl ⟨he', fun c' h => by cases h⟩
  | join => exact .inl ⟨he', fun c' h => by cases h⟩
  | deriveSync => exact .inl ⟨he', fun c' h => by cases h⟩
  | spawnVal => exact .inl ⟨he', fun c' h => by cases h⟩
  | newArena => exact .inl ⟨he', fun c' h => by cases h⟩
  | issue => exact .inl ⟨he', fun c' h => by cases h⟩
  | reset => exact .inl ⟨he', fun c' h => by cases h⟩

/-- Brief of the complement, task 5, "Dernière prise": on a `RunFull` from the initial state,
under `DDSound`, at every index `n` where the entry at index `i` of the registry is live with
`grant = some g`, there is a last successful `acquire` of `i` before `n`, at index `k`, which
recorded `g` (the fresh identity `|A|` of WC5.2 C16), and every covering descendant of the entry
is `g` or was created by a step `k'` with `k < k' < n` of case 2 of the closure (created from a
covering descendant of the state before that step). No history of origins is kept in the state:
the induction runs on the indices of the run. -/
theorem last_acquire {k : K} {L : MutexLayout} {statics : Statics}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} (hdd : DDSound k)
    (hstat : StaticsOK statics) (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], []))
    (h : RunFull k L σ lbls) :
    ∀ n, n ≤ lbls.length → ∀ i e, (σ n).2.1[i]? = some e → e.Live (σ n).1 → ∀ g,
      e.grant = some g → ∃ kk, kk < n ∧ (∃ c, lbls[kk]? = some (.acquire c i)) ∧
        (∀ k', kk < k' → k' < n → ∀ c, lbls[k']? ≠ some (.acquire c i)) ∧
        g = (σ kk).1.A.length ∧
        ∀ j, CoveringDesc (σ n).1 e.guarded j → j = g ∨ ∃ k', kk < k' ∧ k' < n ∧
          (σ k').1.A.length ≤ j ∧ j < (σ (k' + 1)).1.A.length ∧
          ∃ o, (σ (k' + 1)).1.flat.org j = some o ∧ CoveringDesc (σ k').1 e.guarded o
  | 0, _, i, e, he, _, _, _ => by rw [h0] at he; cases he
  | n + 1, hn, i, e, he, hl, g, hg => by
    have hn' : n < lbls.length := hn
    obtain ⟨hk, hlib⟩ := runFull_inv hdd hstat h0 h (Nat.le_of_lt hn')
    have hinv := hlib.1.1
    have hs := (h n hn').2
    obtain ⟨hsk, -⟩ := shape_step hk hlib.2.1 (h n hn').1.1.1.1.1 hs
    have hcl := closure_run hdd hstat h0 h hn'
    have hlbl : lbls[n]? = some lbls[n] := List.getElem?_eq_getElem hn'
    rcases reg_step hs he with ⟨he₀, hna⟩ | hgn | ⟨c, e₀, hacq, he₀, hn₀, rfl⟩
    · have hb := hinv.regBound e (List.mem_of_getElem? he₀)
      have hl₀ : e.Live (σ n).1 := hsk.active hb hl
      obtain ⟨kk, hkk, hacq, hlast, hgk, hcov⟩ :=
        last_acquire hdd hstat h0 h n (Nat.le_of_lt hn') i e he₀ hl₀ g hg
      refine ⟨kk, by omega, hacq, fun k' h1 h2 c => ?_, hgk, fun j hj => ?_⟩
      · by_cases hk' : k' < n
        · exact hlast k' h1 hk' c
        · have : k' = n := by omega
          subst this
          rw [hlbl]; intro heq
          exact hna c (Option.some.inj heq)
      · rcases hcl e (List.mem_of_getElem? he₀) hl₀ hl j
          (List.mem_range.2 (active_lt hj.2.1)) hj with h1 | ⟨h1, o, ho, h2⟩ | h3
        · rcases hcov j h1 with h | ⟨k', a1, a2, a3⟩
          · exact .inl h
          · exact .inr ⟨k', a1, by omega, a3⟩
        · exact .inr ⟨n, hkk, Nat.lt_succ_self n, h1, active_lt hj.2.1, o, ho, h2⟩
        · exfalso
          revert h3
          unfold GrantOf
          split
          · rename_i c' i'' heq
            intro h3
            have hne : i'' ≠ i := fun hh => hna c' (by rw [heq, hh])
            revert h3
            cases hx : (σ n).2.1[i'']? with
            | none => exact id
            | some x =>
              rintro ⟨hgx, -⟩
              have hlx : x.Live (σ n).1 := by unfold SyncEntry.Live; rw [hgx]; exact hl₀
              exact hne (hinv.unique i'' i x e hx he₀ hlx hl₀ hgx)
          · exact id
    · rw [hgn] at hg; cases hg
    · have hb := hinv.regBound e₀ (List.mem_of_getElem? he₀)
      have hl₁ : e₀.Live (σ (n + 1)).1 := hl
      have hl₀ : e₀.Live (σ n).1 := hsk.active hb hl₁
      have hg' : g = (σ n).1.A.length := by
        simp only [Option.some.injEq] at hg; exact hg.symm
      refine ⟨n, Nat.lt_succ_self n, ⟨c, by rw [hlbl, hacq]⟩, fun k' h1 h2 => absurd h2 (by omega),
        hg', fun j hj => ?_⟩
      have hdisc := hlib.1.2 e₀ (List.mem_of_getElem? he₀) hl₀ hn₀
      rcases hcl e₀ (List.mem_of_getElem? he₀) hl₀ hl₁ j
        (List.mem_range.2 (active_lt hj.2.1)) hj with h1 | ⟨-, o, -, h2⟩ | h3
      · exact absurd h1 (hdisc j (List.mem_range.2 (active_lt h1.2.1)))
      · exact absurd h2 (hdisc o (List.mem_range.2 (active_lt h2.2.1)))
      · refine .inl ?_
        revert h3
        rw [hacq]
        show OptP _ _ False → _
        cases (σ n).2.1[i]? with
        | none => exact False.elim
        | some x => exact fun h3 => h3.2.trans hg'.symm

end Ern.Concurrency.FullEncap
