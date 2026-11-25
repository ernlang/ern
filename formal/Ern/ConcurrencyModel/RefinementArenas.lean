import Ern.ConcurrencyModel.RefinementAuthority
import Ern.ConcurrencyModel.RefinementState

/-!
# Theorem 9, arenas: issued bytes and no use after a `reset` (Spec 1 §82.7, §78, §86)

The results of `Ern.MemoryModel.RefinementArena` on the arenas, at the grain of abstract steps, for
the arena operations executed by any context (C2, C19):

* `issue_keeps_bytesC`: the raw operations of an `ok` `issue` modify no byte of the issued region
  (Spec 1 §86, as `RefinementArena.issue_keeps_bytes`);
* `reset_no_useC`, `reset_no_use_issuedC`, `reached_reset_no_use_issued`: after a legal `reset`,
  along every continuation of the run, no step of any context uses an authority derived from
  `internal` that covered the administered storage, nor a block issued before the `reset` on a
  nonempty region (Spec 1 §82.7, §78, §86, as `RefinementArena.reset_no_access` and
  `RefinementArena.reset_no_access_issued`).

"Uses" is in the sense of `usesOf`. Limit of these statements, as of theorem 9e: they are about the
authorities that the modelled steps use. They do not discharge the obligation of C50 on the
physical accesses after invalidation: those of the realizations that are not modelled, the
controller of the mutex included, stay exported (`OB-C05`, `OB-C12`, `OB-C20`).
-/

namespace Ern.ConcurrencyModel

open Ern.MemoryModel Ern.MemoryModel.Access Ern.MemoryModel.Refinement ArenaAux

/-! ## The bytes of an issued region (Spec 1 §86) -/

/-- A write through the access to leaf `p` leaves the bytes of the range of leaf `l` unchanged
when the two ranges are in different allocations or disjoint (Spec 1 §16 ¶3, §9 ¶3): the proof of
the private lemma of `RefinementArena` used by `issue_keeps_bytes`. -/
theorem bytesOf_write_apart {s2 : Machine.State} {L : Layout} {p l : Nat}
    {w : Nat → UInt8 × Option Nat}
    (hd : (L p).alloc ≠ (L l).alloc ∨
      Machine.RangeDisjoint (L p).off (L p).len (L l).off (L l).len)
    {n : Nat} (hn : n < (L l).len) :
    bytesOf (s2.write (leafAcc s2 L .write p) w) L l n = bytesOf s2 L l n := by
  by_cases e : (L l).alloc = (L p).alloc
  · cases ha : s2.allocs (L l).alloc with
    | none =>
      have he : (s2.write (leafAcc s2 L .write p) w).allocs (L l).alloc = none := by
        rw [write_allocs, ha]; split <;> rfl
      simp only [bytesOf, he, ha]
    | some a =>
      have hpa : s2.allocs (L p).alloc = some a := e ▸ ha
      have he : (s2.write (leafAcc s2 L .write p) w).allocs (L l).alloc =
          some (a.write (L p).off (L p).len w) := by
        rw [e, write_allocs, leafAcc_of hpa]
        simp only [↓reduceIte, hpa, Option.map_some, Nat.add_sub_cancel_left]
      have hout : ¬ ((L p).off ≤ (L l).off + n ∧ (L l).off + n < (L p).off + (L p).len) :=
        fun ⟨h1, h2⟩ => hd.elim (fun h => h e.symm)
          fun h => h _ h1 h2 (Nat.le_add_right _ _) (Nat.add_lt_add_left hn _)
      simp only [bytesOf, he, ha, Machine.Alloc.write_bytes_out a w hout]
  · have he : (s2.write (leafAcc s2 L .write p) w).allocs (L l).alloc = s2.allocs (L l).alloc := by
      rw [write_allocs]; exact ite_eq_right e
    simp only [bytesOf, he]

/-- **Theorem 9**, the bytes of an issued region (Spec 1 §86, §77, Part XIV, §82.7; C2, C19), for an
`issue` executed by any context `c`, at the grain of abstract steps: the raw operations of an `ok`
`issue` (one write of the range of the destination, `rawOps_issue`) modify no byte of the issued
region, so a reissued leaf keeps its bytes. The destination is a leaf that is not in the region
(§77.2); under the layout interface (Spec 1 §82.1, §23, part of `ReprC`), the range of every leaf of
the region is in another allocation or disjoint from it. Hypotheses: `ReprC` and the step, as
`RefinementArena.issue_keeps_bytes`; no invariant hypothesis. Fragment: every state related by
`ReprC`, every context. -/
theorem issue_keeps_bytesC {Ty : Type} {ks : KShared} {ML : MutexLayout} {π : Params Ty}
    {w : WriteRepr} {c i : Nat} {region : List Nat} {dst : Nat}
    {st st' : SC × SyncReg × ArenaReg} {m : Machine.State} (hR : ReprC π.L π.rtok st.1 m)
    (h : LStep ks ML (.issue c i region dst) st st') :
    ∀ l ∈ region, ∀ n < (π.L l).len,
      bytesOf (run m (rawOps π w (.issue c i region dst) st m)) π.L l n = bytesOf m π.L l n := by
  cases h with
  | @issue s reg ar _ _ _ _ st₂ h =>
    obtain ⟨E, s₁, hE, hsta, -, hsp, -⟩ := issueStepC_ok h
    have hc : s.Live c := opStepC_live hsp
    have hRv := (reprC_view hc).1 hR
    intro l hl n hn
    rw [rawOps_issue π w (st := (s, reg, ar)) hE]
    simp only [storeOps, writeOps, List.map_cons, List.map_nil, run, opEff]
    obtain ⟨hlP, hlf, -⟩ := mem_footprint.1 (hsta.regionIn l hl)
    have hne : dst ≠ l := fun e => hsta.dstNotIn (e ▸ hl)
    refine bytesOf_write_apart ?_ hn
    by_cases e : (π.L dst).alloc = (π.L l).alloc
    · exact .inr (hRv.layout.disjoint dst l hsta.dstUsable.lt hlP hsta.dstLeaf hlf hne e)
    · exact .inl e

/-! ## No use of an invalidated authority after a `reset` (Spec 1 §82.7, §78, §86) -/

/-- The `reset` of entry `i` executed by `c` (Spec 1 §78, Part XIV; C2) leaves inactive every
authority derived from `internal` that covers a leaf of the administered storage:
`Arena.reset_ends_covering` on the view of `c`, written back. -/
theorem resetC_ends_covering {s : SC} {ar : ArenaReg} {c i : Nat} {st' : SC × ArenaReg}
    {E : Arena.ArenaEntry} (hE : ar[i]? = some E) (hr : ResetStepC s ar c i (.ok st')) {j : Nat}
    (hj : E.internal ∈ s.flat.ancs j)
    (hc : ∃ l ∈ s.flat.afp j, l ∈ footprint s.P E.storage) : ¬ st'.1.flat.Active j := by
  obtain ⟨o₃, hR, ho⟩ := hr
  cases o₃ with
  | reject => cases ho
  | fail => cases ho
  | ok L' =>
    cases ho
    exact Arena.reset_ends_covering (L := ⟨s.view c, ar⟩) hE hR hj hc

/-- **Theorem 9**, no use after a `reset` (Spec 1 §82.7, §78, §86, §42, §58; C2, C19, C50), for the
authorities that the modelled steps use: after a legal `reset` of entry `i` executed by any context
`c`, along every continuation of the run, no step of any context uses (`usesOf`) an authority
derived from `internal` that covered a leaf of the administered storage before the `reset`, as
`RefinementArena.reset_no_access`. The authority may already be inactive before the `reset`.
Fragment: every state, every continuation, every label.

The statement is limited to the authorities that the modelled steps use (`usesOf`). It does not
discharge the obligation of C50 on the physical accesses after invalidation: those of the
realizations that are not modelled, the controller of the mutex included, stay exported
(`OB-C05`, `OB-C12`, `OB-C20`). -/
theorem reset_no_useC {ks : KShared} {ML : MutexLayout} {c i : Nat} {E : Arena.ArenaEntry}
    {st st₁ st₂ : SC × SyncReg × ArenaReg} {t : List (Label × (SC × SyncReg × ArenaReg))}
    (hE : st.2.2[i]? = some E) (hr : LStep ks ML (.reset c i) st st₁)
    (hp : LTrace ks ML st₁ t st₂) {j : Nat} (hj : E.internal ∈ st.1.flat.ancs j)
    (hc : ∃ l ∈ st.1.flat.afp j, l ∈ footprint st.1.P E.storage) :
    ∀ q ∈ t, ∀ u ∈ usesOf q.1 q.2, u.1 ≠ j := by
  have hjL : j < st.1.A.length := by
    obtain ⟨l, hl, -⟩ := hc
    cases hlj : st.1.flat.A[j]? with
    | none => simp [S3.afp, hlj] at hl
    | some _ => exact lt_of_getElem? hlj
  have hd : ¬ st₁.1.flat.Active j := by
    cases hr with
    | @reset s reg ar _ _ st' h => exact resetC_ends_covering hE h hj hc
  exact ltrace_unused ((lstep_keep hr).1.lt hjL) hd hp (Arena.akeep_of_eq rfl)

/-- **Theorem 9**, no use of an issued block after a `reset` (Spec 1 §82.7, §78, §86; C2, C19,
C50), for the authorities that the modelled steps use: for a live entry satisfying `EntryInv`
(Spec 1 §55, with the shape of the issued blocks), after a legal `reset` executed by any context
`c`, along every continuation of the run, no step of any context uses (`usesOf`) a block issued
before the `reset` on a nonempty region, as `RefinementArena.reset_no_access_issued`. On the states
reached from the initial state, `EntryInv` holds (`reached_reset_no_use_issued`). Fragment: every
state, every continuation, every label.

The statement is limited to the authorities that the modelled steps use (`usesOf`). It does not
discharge the obligation of C50 on the physical accesses after invalidation: those of the
realizations that are not modelled, the controller of the mutex included, stay exported
(`OB-C05`, `OB-C12`, `OB-C20`). -/
theorem reset_no_use_issuedC {ks : KShared} {ML : MutexLayout} {c i : Nat} {E : Arena.ArenaEntry}
    {st st₁ st₂ : SC × SyncReg × ArenaReg} {t : List (Label × (SC × SyncReg × ArenaReg))}
    (hE : st.2.2[i]? = some E) (hinv : Arena.EntryInv st.1.flat E)
    (hr : LStep ks ML (.reset c i) st st₁) (hp : LTrace ks ML st₁ t st₂) :
    ∀ e ∈ E.issued, e.1 ≠ [] → ∀ q ∈ t, ∀ u ∈ usesOf q.1 q.2, u.1 ≠ e.2 := by
  intro e he hne
  obtain ⟨y, hy, ho, hlt, hf, -⟩ := hinv.2 e he
  have hj : E.internal ∈ st.1.flat.ancs e.2 := by
    unfold S3.ancs
    rw [chain_cons (by simp [S3.org, hy, ho]) hlt]
    exact List.mem_cons_self ..
  obtain ⟨l, hl⟩ := List.exists_mem_of_ne_nil _ hne
  exact reset_no_useC hE hr hp hj ⟨l, by simp [S3.afp, hy, hf, hl], hinv.1.issuedIn e he l hl⟩

/-- The arena invariant (`ArenaInvC`, Spec 1 §55; C19) along every run, from a state satisfying
`KInvCA` and `ArenaInvC`, under `DDSound` (Spec 1 §80): `lstep_arenaInv` at each step, with no
trace restriction. -/
theorem lrun_arenaInvC {ks : KShared} {ML : MutexLayout} {st st' : SC × SyncReg × ArenaReg}
    {lbls : List Label} (hdd : DDSound ks.toK) (h : LRun ks ML st lbls st') (hk : KInvCA st.1)
    (ha : ArenaInvC st.1 st.2.2) : ArenaInvC st'.1 st'.2.2 := by
  induction h with
  | nil => exact ha
  | cons hs _ ih =>
    have hk' := lstep_kInvCA hdd hs hk
    exact ih hk' (lstep_arenaInv hs hk.1.1.2 hk'.1.2.1.2.2 ha)

/-- **Theorem 9**, no use of an issued block after a `reset` on the reached states (Spec 1 §82.7,
§78, §86, §55; C2, C19, C50), for the authorities that the modelled steps use: under `DDSound(K)`
(Spec 1 §80) and well-formed statics (Spec 1 §47), on every state reached from the initial state
of Spec 1 §47 by a run of labelled steps (no trace restriction), after a legal `reset` of entry `i`
executed by any context `c`, along every continuation, no step of any context uses (`usesOf`) a
block issued before the `reset` on a nonempty region, as
`RefinementArena.reset_no_access_issued_reachable`. The invariant of the entry is not a
hypothesis: the entry is live (the internal `derive` exercises `internal`, Spec 1 §60.1) and the
reached states satisfy `ArenaInvC` (`lrun_arenaInvC`). Fragment: every reached state, every
continuation, every label.

The statement is limited to the authorities that the modelled steps use (`usesOf`). It does not
discharge the obligation of C50 on the physical accesses after invalidation: those of the
realizations that are not modelled, the controller of the mutex included, stay exported
(`OB-C05`, `OB-C12`, `OB-C20`). -/
theorem reached_reset_no_use_issued {ks : KShared} {ML : MutexLayout} {statics : Statics}
    {lbls : List Label} {c i : Nat} {E : Arena.ArenaEntry}
    {st st₁ st₂ : SC × SyncReg × ArenaReg} {t : List (Label × (SC × SyncReg × ArenaReg))}
    (hdd : DDSound ks.toK) (hst : StaticsOK statics)
    (hL : LRun ks ML (SC.ofS3 (S3.init statics), [], []) lbls st) (hE : st.2.2[i]? = some E)
    (hr : LStep ks ML (.reset c i) st st₁) (hp : LTrace ks ML st₁ t st₂) :
    ∀ e ∈ E.issued, e.1 ≠ [] → ∀ q ∈ t, ∀ u ∈ usesOf q.1 q.2, u.1 ≠ e.2 := by
  obtain ⟨hk₀, -, ha₀⟩ := init_inv (k := ks.toK) hdd hst ML
  have ha := lrun_arenaInvC hdd hL hk₀ ha₀
  have hlive : st.1.flat.Active E.internal := by
    cases hr with
    | @reset s reg ar _ _ st' h =>
      obtain ⟨E', s₁, hE', hd, -⟩ := resetStepC_ok (k := ks.toK) h
      rw [hE] at hE'; cases hE'
      exact kernel_uses_active (op := .derive E.internal (footprint s.P E.storage) .modify) hd rfl
  exact reset_no_use_issuedC hE ((ha E (List.mem_of_getElem? hE)).2 hlive) hr hp

end Ern.ConcurrencyModel
