import Ern.ConcurrencyModel.RefinementState

/-!
# Theorem 9, pinning: the move half (Spec 1 §82.6, §63.5, §74, §87)

Spec 1 §82.6 asks for the compatibility of permitted moves and of pinned-address restrictions. The
address half is `reached_pinned_address_stable`. The move half, as
`Refinement.transfer_pinned_not_moved` and `Refinement.transfer_reads_unpinned`, at the grain of
abstract steps:

* for a `transfer` executed by any context (C2): `transfer_pinned_not_movedC`,
  `transfer_reads_unpinnedC`;
* for each transfer of the by-value composite, in the state where its phase starts (C5.2):
  `spawnVal_pinned_not_moved`, `spawnVal_reads_unpinned`.

A leaf is pinned when an active dynamic pinning obligation covers it (Spec 1 §74) or `K.Pinned`
pins it. The proofs read §63.5 (`TransferPreC.notPinned`, `ValTransferPre.notPinned`) and the
effect of O4 only.
-/

namespace Ern.ConcurrencyModel

open Ern.MemoryModel Ern.MemoryModel.Access Ern.MemoryModel.Refinement

/-- The move half of Spec 1 §82.6 on the effect of O4 executed on the view of `c` (§63.5, §74,
§87, §35 ¶2): from the clause §63.5 of the source, a leaf pinned in `t` (covered by an active
dynamic pinning obligation, or pinned by `K.Pinned`) is not an in-place leaf of the source, and its
initialization state does not become `Moved`. The proof of
`Refinement.transfer_pinned_not_moved`, which reads §63.5 only. -/
theorem transferC_pinned_not_moved {k : K} {t : SC} {c src dst l : Nat}
    (hnp : ∀ l ∈ footprint (t.view c).P src, ¬ k.Pinned l ∧ (t.view c).pin l = false)
    (hpin : (∃ (o : Nat) (ob : PinOb), t.pins[o]? = some ob ∧ ob.active = true ∧
      l ∈ ob.leaves) ∨ k.Pinned l) :
    l ∉ footprint t.P src ∧ ((transferEffC t c src dst).I l = .moved → t.I l = .moved) := by
  have hns : l ∉ footprint t.P src := fun hl => by
    obtain ⟨h1, h2⟩ := hnp l hl
    rcases hpin with hp | hp
    · rw [S3.pin_iff.2 hp] at h2; cases h2
    · exact h1 hp
  refine ⟨hns, fun hm => ?_⟩
  change (transferEff (t.view c) src dst).I l = .moved at hm
  simp only [transferEff] at hm
  by_cases hd : l ∈ footprint (t.view c).P dst
  · simp [hd] at hm
  · have hns' : l ∉ footprint (t.view c).P src := hns
    have h' : (t.view c).I l = .moved := by simpa [hd, hns'] using hm
    exact h'

/-- The move half of Spec 1 §82.6 on the raw operations of O4 executed on the view of `c` (§63.5,
§74, §87, §82.3): every raw read of `transferOps` is the access, in the memory state `m` where they
start, to the range of an in-place leaf of the source that no active dynamic pinning obligation
covers and that `K.Pinned` does not pin. The proof of `Refinement.transfer_reads_unpinned`, which
reads §63.5 only. -/
theorem transferC_reads_unpinned {Ty : Type} {k : K} {π : Params Ty} {t : SC} {c src dst : Nat}
    {m : Machine.State}
    (hnp : ∀ l ∈ footprint (t.view c).P src, ¬ k.Pinned l ∧ (t.view c).pin l = false)
    {ac : Machine.Access} {ty : Ty}
    (hr : Machine.Op.read ac ty ∈ transferOps π.L π.ty m (t.view c) src dst) :
    ∃ l ∈ footprint t.P src,
      ((∀ (o : Nat) (ob : PinOb), t.pins[o]? = some ob → ob.active = true → l ∉ ob.leaves) ∧
        ¬ k.Pinned l) ∧
      ac = leafAcc m π.L .read l := by
  obtain ⟨⟨l, l'⟩, hq, rfl⟩ := copyOps_read π.L π.ty m _ hr
  obtain ⟨hl, -⟩ := mem_transferPairs.1 hq
  obtain ⟨h1, h2⟩ := hnp l hl
  refine ⟨l, hl, ⟨fun o ob ho ha hlo => ?_, h1⟩, rfl⟩
  have : (t.view c).pin l = true := S3.pin_iff.2 ⟨o, ob, ho, ha, hlo⟩
  rw [this] at h2; cases h2

/-- **Theorem 9**, move half of pinning (Spec 1 §82.6, §63.5, §74, §87; C2), for a `transfer`
executed by any context `c`, at the grain of abstract steps: a leaf pinned in the state before the
step (covered by an active dynamic pinning obligation, or pinned by `K.Pinned`) is not an in-place
leaf of the source, the leaves that the step moves, and its initialization state does not become
`Moved`. Fragment: every state, every context. -/
theorem transfer_pinned_not_movedC {ks : KShared} {ML : MutexLayout} {c src dst l : Nat}
    {st st' : SC × SyncReg × ArenaReg} (h : LStep ks ML (.kernel c (.transfer src dst)) st st')
    (hpin : (∃ (o : Nat) (ob : PinOb), st.1.pins[o]? = some ob ∧ ob.active = true ∧
      l ∈ ob.leaves) ∨ ks.toK.Pinned l) :
    l ∉ footprint st.1.P src ∧ (st'.1.I l = .moved → st.1.I l = .moved) := by
  cases h with
  | kernel h =>
    obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
    exact transferC_pinned_not_moved hpre.notPinned hpin

/-- **Theorem 9**, move half of pinning on the raw operations (Spec 1 §82.6, §63.5, §74, §87,
§82.3; C2), for a `transfer` executed by any context `c`, at the grain of abstract steps: every
raw read among the raw operations of the step (`rawOps`), by which a value is copied into the
destination, is the access, in the memory state `m` before the step, to the range of an in-place
leaf of the source that no active dynamic pinning obligation covers and that `K.Pinned` does not
pin. Fragment: every state, every context, every memory state. -/
theorem transfer_reads_unpinnedC {Ty : Type} {ks : KShared} {ML : MutexLayout} {π : Params Ty}
    {w : WriteRepr} {c src dst : Nat} {st st' : SC × SyncReg × ArenaReg} {m : Machine.State}
    (h : LStep ks ML (.kernel c (.transfer src dst)) st st') {ac : Machine.Access} {ty : Ty}
    (hr : Machine.Op.read ac ty ∈ rawOps π w (.kernel c (.transfer src dst)) st m) :
    ∃ l ∈ footprint st.1.P src,
      ((∀ (o : Nat) (ob : PinOb), st.1.pins[o]? = some ob → ob.active = true →
          l ∉ ob.leaves) ∧ ¬ ks.toK.Pinned l) ∧
      ac = leafAcc m π.L .read l := by
  cases h with
  | kernel h =>
    exact transferC_reads_unpinned (Guarded.ok_iff.1 h).1.notPinned hr

/-! ## The transfer phases of the by-value composite (C5.2) -/

/-- The transfer phases of the by-value composite executed by `c` from the state `t` (C5.2): each
by-value argument `(src, dst)` in its declared order, with the state where its phase starts, the
state produced by the earlier transfers. -/
def valStarts (c : Nat) : SC → List (Nat × Nat) → List (SC × Nat × Nat)
  | _, [] => []
  | t, v :: vs => (t, v.1, v.2) :: valStarts c (transferEffC t c v.1 v.2) vs

/-- The transfer phases of the by-value composite executed by `c` from the state `t` and the memory
state `m` (C5.2; `valOps`): each by-value argument `(src, dst)` in its declared order, with the
state where its phase starts and the memory state where its raw operations start, those produced
by the earlier transfers and their raw operations. -/
def valPhases {Ty : Type} (π : Params Ty) (c : Nat) :
    SC → List (Nat × Nat) → Machine.State → List (SC × Machine.State × Nat × Nat)
  | _, [], _ => []
  | t, v :: vs, m => (t, m, v.1, v.2) :: valPhases π c (transferEffC t c v.1 v.2) vs
      (run m (transferOps π.L π.ty m (t.view c) v.1 v.2))

/-- The phases with their memory states are the phases of `valStarts` (C5.2). -/
theorem valPhases_starts {Ty : Type} (π : Params Ty) (c : Nat) :
    ∀ (t : SC) (vs : List (Nat × Nat)) (m : Machine.State),
      ∀ ph ∈ valPhases π c t vs m, (ph.1, ph.2.2) ∈ valStarts c t vs
  | _, [], _ => fun _ h => nomatch h
  | t, v :: vs, m => fun ph hph => by
    rcases List.mem_cons.1 hph with rfl | hph
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (valPhases_starts π c _ vs _ ph hph)

/-- The creations of new root places read nothing (Spec 1 §9 ¶11, §72). -/
theorem allocOps_noRead {Ty : Type} (pl : Placement) (g : Nat → Geom) (rtok : Nat → Nat)
    (n : Nat) : ∀ (s : Machine.State) (is : List Nat) {ac : Machine.Access} {ty : Ty},
      Machine.Op.read ac ty ∉ allocOps pl g rtok n s is
  | _, [], _, _, h => nomatch h
  | _, _ :: is, _, _, h => by
    rcases List.mem_cons.1 h with h | h
    · cases h
    · exact allocOps_noRead pl g rtok n _ is h

/-- Every transfer phase satisfies §63.5 at its start (C5.2, C5 item 4). -/
theorem valStarts_notPinned {k : K} {fin : S3} {c : Nat} :
    ∀ (t : SC) (vs : List (Nat × Nat)), ValTransfersPre k fin c t vs →
      ∀ ph ∈ valStarts c t vs, ∀ l ∈ footprint (ph.1.view c).P ph.2.1,
        ¬ k.Pinned l ∧ (ph.1.view c).pin l = false
  | _, [], _ => fun _ h => nomatch h
  | t, v :: vs, ⟨hp, hrest⟩ => fun ph hph => by
    rcases List.mem_cons.1 hph with rfl | hph
    · exact hp.notPinned
    · exact valStarts_notPinned _ vs hrest ph hph

/-- The raw reads of the transfer phases (C5.2; `valOps`): every raw read is one of `transferOps`
of some phase, in the memory state where that phase starts. -/
theorem valOps_read {Ty : Type} (π : Params Ty) (c : Nat) :
    ∀ (t : SC) (vs : List (Nat × Nat)) (m : Machine.State) {ac : Machine.Access} {ty : Ty},
      Machine.Op.read ac ty ∈ valOps π c t vs m →
        ∃ ph ∈ valPhases π c t vs m,
          Machine.Op.read ac ty ∈ transferOps π.L π.ty ph.2.1 (ph.1.view c) ph.2.2.1 ph.2.2.2
  | _, [], _, _, _, h => nomatch h
  | t, v :: vs, m, _, _, h => by
    simp only [valOps] at h
    rcases List.mem_append.1 h with h | h
    · exact ⟨_, List.mem_cons_self .., h⟩
    · obtain ⟨ph, hph, hr⟩ := valOps_read π c _ vs _ h
      exact ⟨ph, List.mem_cons_of_mem _ hph, hr⟩

/-- **Theorem 9**, move half of pinning (Spec 1 §82.6, §63.5, §74, §87; C5.2, C5 item 4), for each
transfer of the by-value composite executed by any context `c`, in the state where its phase starts
(`valStarts`, from `spawnCreate`, then the earlier transfers), at the grain of abstract steps: a leaf
pinned in that state is not an in-place leaf of the source of the phase, and its initialization
state does not become `Moved` by the transfer of the phase. Fragment: every state, every
context. -/
theorem spawnVal_pinned_not_moved {ks : KShared} {ML : MutexLayout} {c : Nat} {ps : List Nat}
    {ls : LocalShape} {vs : List (Nat × Nat)} {st st' : SC × SyncReg × ArenaReg}
    (h : LStep ks ML (.spawnVal c ps ls vs) st st') :
    ∀ ph ∈ valStarts c (spawnCreate st.1 c ls) vs, ∀ l,
      ((∃ (o : Nat) (ob : PinOb), ph.1.pins[o]? = some ob ∧ ob.active = true ∧
        l ∈ ob.leaves) ∨ ks.toK.Pinned l) →
      l ∉ footprint ph.1.P ph.2.1 ∧
        ((transferEffC ph.1 c ph.2.1 ph.2.2).I l = .moved → ph.1.I l = .moved) := by
  cases h with
  | spawnVal h =>
    obtain ⟨hpre, -⟩ := Guarded.ok_iff.1 h
    intro ph hph l hpin
    exact transferC_pinned_not_moved (valStarts_notPinned _ vs hpre.transfers ph hph) hpin

/-- **Theorem 9**, move half of pinning on the raw operations (Spec 1 §82.6, §63.5, §74, §87,
§82.3; C5.2, C5 item 4), for the by-value composite executed by any context `c`, at the grain of
abstract steps: every raw read among the raw operations of the step (`rawOps`) belongs to the
transfer of some phase (`valPhases`), and is the access, in the memory state where that phase
starts, to the range of an in-place leaf of its source that, in the state where the phase starts,
no active dynamic pinning obligation covers and that `K.Pinned` does not pin. The creations of the
first phase read nothing. Fragment: every state, every context, every memory state. -/
theorem spawnVal_reads_unpinned {Ty : Type} {ks : KShared} {ML : MutexLayout} {π : Params Ty}
    {w : WriteRepr} {c : Nat} {ps : List Nat} {ls : LocalShape} {vs : List (Nat × Nat)}
    {st st' : SC × SyncReg × ArenaReg} {m : Machine.State}
    (h : LStep ks ML (.spawnVal c ps ls vs) st st') {ac : Machine.Access} {ty : Ty}
    (hr : Machine.Op.read ac ty ∈ rawOps π w (.spawnVal c ps ls vs) st m) :
    ∃ ph ∈ valPhases π c (spawnCreate st.1 c ls) vs
        (run m (allocOps (Ty := Ty) π.pl π.geom π.rtok (st.1.view c).P.length m
          (rootIdx ls.toShape))),
      ∃ l ∈ footprint ph.1.P ph.2.2.1,
        ((∀ (o : Nat) (ob : PinOb), ph.1.pins[o]? = some ob → ob.active = true →
            l ∉ ob.leaves) ∧ ¬ ks.toK.Pinned l) ∧
        ac = leafAcc ph.2.1 π.L .read l := by
  cases h with
  | spawnVal h =>
    obtain ⟨hpre, -⟩ := Guarded.ok_iff.1 h
    simp only [rawOps] at hr
    rcases List.mem_append.1 hr with hr | hr
    · exact absurd hr (allocOps_noRead _ _ _ _ _ _)
    · obtain ⟨ph, hph, hr'⟩ := valOps_read π c _ vs _ hr
      exact ⟨ph, hph, transferC_reads_unpinned
        (valStarts_notPinned _ vs hpre.transfers _ (valPhases_starts π c _ vs _ ph hph)) hr'⟩

end Ern.ConcurrencyModel
