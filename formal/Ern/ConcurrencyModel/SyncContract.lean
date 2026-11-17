import Ern.ConcurrencyModel.Reachable

/-!
# Theorem 4: the synchronization contract and the exclusivity of grants (C14, C15, C21, C22,
C25; `OB-C15`)

Theorem 4 of `formal/DESIGN.md`, Milestone 4, target theorems:

* under `ConcurrentWF`, the Spec 1 invariants, `SyncInv` and `GrantDiscipline` (the hypotheses C14
  lists), the three authorization facts of C14 imply the other prerequisites of `deriveSync`
  (`realizability`); `SyncAuthorized` is defined by those facts only (`LibSyncAuthorized`);
* on states reached by a trace satisfying the restrictions of C23, `SyncInv` and
  `GrantDiscipline` hold (`synchronization_reached`); the form for `EncapsulatedTrace` (C51.1),
  which implies those restrictions, is `synchronization_encapsulated` in `Inventory`;
* exclusivity: while the recorded grant is active, every active descendant of `guarded` covering a
  protected leaf is that grant or one of its descendants (C21.5); with `grant = none`, there is none
  (C22); two distinct full grants of the same `guarded` cannot coexist (`grants_exclusive`).
-/

namespace Ern.ConcurrencyModel

open Ern.MemoryModel.Access

/-! ## Exclusivity of grants (Spec 1 §50; C15, C21) -/

/-- An ancestor of an authority whose origin is `g` is `g` or below `g` (Spec 1 §42, §49.5). -/
theorem ancs_le_origin {t : S3} (hw : WF3 t) {b g : Nat} {y : Authority} (hy : t.A[b]? = some y)
    (hyo : y.origin = some g) {x : Nat} (hx : x ∈ t.ancs b) : x ≤ g := by
  have hgb : g < b := hw.origins b y g hy hyo
  have horg : t.org b = some g := by simp [S3.org, hy, hyo]
  rw [S3.ancs, chain_cons horg hgb] at hx
  rcases List.mem_cons.1 hx with rfl | hx
  · exact Nat.le_refl _
  · exact Nat.le_of_lt (chain_lt hx)

/-- Theorem 4, exclusivity (Spec 1 §50, I1; C15, C21.2): two distinct active authorities of own mode
`Modify` whose origin is the same `guarded` and whose footprint is `footprint(guarded)`, nonempty,
cannot coexist. Fragment: states satisfying `WF3` and `I1` on the globally live frames. -/
theorem grants_exclusive {s : SC} (hw : WF3 s.flat) (h1 : I1 s.flat) {g a b : Nat}
    {x y : Authority} (hab : a ≠ b) (hx : s.A[a]? = some x) (hy : s.A[b]? = some y)
    (xa : x.active = true) (ya : y.active = true) (xm : x.mode = .modify)
    (xo : x.origin = some g) (yo : y.origin = some g)
    (xf : ∀ l, l ∈ x.footprint ↔ l ∈ s.flat.afp g) (yf : ∀ l, l ∈ y.footprint ↔ l ∈ s.flat.afp g)
    {l : Nat} (hl : l ∈ s.flat.afp g) : False := by
  have hga : g < a := hw.origins a x g hx xo
  have hgb : g < b := hw.origins b y g hy yo
  have hna : a ∉ s.flat.ancs b := fun h => by have := ancs_le_origin hw hy yo h; omega
  have hnb : b ∉ s.flat.ancs a := fun h => by have := ancs_le_origin hw hx xo h; omega
  have := h1 a b x y l hab hx hy xa ya ((xf l).2 hl) ((yf l).2 hl) hna hnb
  rw [xm] at this; cases this.1

/-! ## Soundness of the synchronization contract (C14, C15, C25; `OB-C15`) -/

/-- **Theorem 4**, soundness of the synchronization contract (C14, C15, C25; `OB-C15`): under `SyncInv` and `GrantDiscipline`, and the kernel invariant
re-indexed (`KInvC`: `FramesC`, `WF3`, `I1` and `I2` are used), the library instantiation of
`SyncAuthorized` (the facts C14.1–C14.3 only) on the registry, for the current frame of the
requesting context, entails that no active descendant of `guarded` covers a protected leaf and all the
preconditions of `deriveSync` on that registry, in particular the own mode (C15.1), I1 for the
full-footprint grant (§60.3) and the validity of the origin chain (§60.1). Fragment: states
satisfying `KInvC`. -/
theorem realizability {ks : KShared} {L : MutexLayout} {reg : SyncReg} {ar : ArenaReg} {s : SC}
    {c g : Nat}
    (hk : KInvC s) (hsi : SyncInv L s reg ar) (hgd : GrantDiscipline s reg)
    (ha : LibSyncAuthorized L reg s g (s.view c).top) :
    NoCoveringDesc s g ∧ DeriveSyncPre (libKC ks L) reg s c g := by
  -- C14.3, C2: a context that is not live has no controller-access right.
  have hl : s.Live c := Decidable.byContradiction fun h => SC.dead_not_libSyncAuthorized h ha
  obtain ⟨⟨hfr, hw⟩, ⟨⟨h1, h2, -, -⟩, -, -⟩, -, -⟩ := hk
  have hc : s.stk c ≠ [] := hfr.nonempty c hl
  obtain ⟨e, he, rfl, hl, hn, hcr⟩ := ha
  have hnc := hgd e he hl hn
  obtain ⟨y, hy, ya⟩ := hl
  have hy' : s.A[e.guarded]? = some y := hy
  have hym : y.mode = .modify := by
    have := hsi.guarded e he ⟨y, hy, ya⟩; simp only [OptP, hy'] at this; exact this.1
  have hfp : s.flat.afp e.guarded = y.footprint := by simp [S3.afp, hy]
  have hafp : ∀ {j : Nat} {z : Authority}, s.A[j]? = some z → s.flat.afp j = z.footprint :=
    fun hz => by simp [S3.afp, SC.flat, hz]
  have hmo : OptP (s.A[e.guarded]?) (fun y => Mode.modify.le y.mode) False := by
    rw [hy', OptP, hym]; exact Mode.le_refl _
  refine ⟨hnc, ⟨y, hy, ya⟩, hmo,
    ⟨e, he, rfl, ⟨y, hy, ya⟩, hn, hcr⟩, ?_, ?_, fun l h => h, ?_, ?_, ?_⟩
  · exact I2.ancs_active h2 ⟨y, hy, ya⟩
  · intro l hl'
    have hl'' : l ∈ y.footprint := by rw [← hfp]; exact hl'
    exact hw.footprints _ y hy l hl''
  · intro l hl'
    have hl'' : l ∈ y.footprint := by rw [← hfp]; exact hl'
    have hd : descModes s.flat e.guarded l = [] := by
      apply nil_of_forall_not_mem
      intro m hm
      obtain ⟨j, z, hz, za, hlz, hanc, -⟩ := mem_descModes.1 hm
      exact hnc j (List.mem_range.2 (lt_of_getElem? hz))
        ⟨hanc, ⟨z, hz, za⟩, l, by rw [hafp hz]; exact hlz, hl'⟩
    change Allows (effective s.flat e.guarded l) .modify
    rw [effective_eq hy ya hl'', hd, hym]
    simp [effOf, Allows, OptP, Mode.le]
  · intro b _
    unfold OptP; split
    · rename_i z hz
      intro za hnb hcov
      exfalso
      obtain ⟨l, hl', hlz⟩ := hcov
      have hb : b ≠ e.guarded := fun h => hnb (h ▸ List.mem_cons_self ..)
      have hnanc : b ∉ s.flat.ancs e.guarded := fun h => hnb (List.mem_cons_of_mem _ h)
      by_cases hdesc : e.guarded ∈ s.flat.ancs b
      · exact hnc b (List.mem_range.2 (lt_of_getElem? hz)) ⟨hdesc, ⟨z, hz, za⟩, l,
          by rw [hafp hz]; exact hlz, hl'⟩
      · have hl'' : l ∈ y.footprint := by rw [← hfp]; exact hl'
        have := h1 e.guarded b y z l (Ne.symm hb) hy hz ya za hl'' hlz hdesc hnanc
        rw [hym] at this; cases this.1
    · trivial
  · obtain ⟨f, rest, hf⟩ := List.exists_cons_of_ne_nil hc
    rw [SC.view_top hf]
    exact SC.mem_frames_of (by rw [hf]; exact List.mem_cons_self ..)


/-- **Theorem 4** (C21, C22, C23): every state reached from the initial state of Spec 1 §47 by a
trace satisfying the restrictions of C23 (C22.1–C22.3, C22.5) satisfies `SyncInv` and
`GrantDiscipline`, and the exclusivity of C21.5 and C22: for every live entry, while its recorded
grant `g` is active, every active descendant of `guarded` covering a protected leaf is `g` or a
descendant of `g`; with `grant = none`, no active descendant of `guarded` covers a protected leaf.
Under `DDSound` (Spec 1 §80) and well-formed statics (Spec 1 §47). -/
theorem synchronization_reached {ks : KShared} {L : MutexLayout} {statics : Statics}
    {lbls : List Label} {st' : SC × SyncReg × ArenaReg} (hdd : DDSound ks.toK)
    (hst : StaticsOK statics) (h : RestrictedTrace ks L (SC.ofS3 (S3.init statics), [], []) lbls st') :
    SyncInv L st'.1 st'.2.1 st'.2.2 ∧ GrantDiscipline st'.1 st'.2.1 ∧
      (∀ e ∈ st'.2.1, e.Live st'.1 → ∀ g, e.grant = some g → st'.1.flat.Active g →
        ∀ j, CoveringDesc st'.1 e.guarded j → j = g ∨ g ∈ st'.1.flat.ancs j) ∧
      (∀ e ∈ st'.2.1, e.Live st'.1 → e.grant = none → NoCoveringDesc st'.1 e.guarded) := by
  obtain ⟨-, hsi, hgd, -⟩ := restricted_inv hdd hst h
  exact ⟨hsi, hgd, hsi.grantSubtree, hgd⟩

end Ern.ConcurrencyModel
