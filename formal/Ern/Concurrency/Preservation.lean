import Ern.Concurrency.Conservativity
import Ern.Concurrency.Sync

/-!
# Preservation of the re-indexed kernel invariant (WC3 C20, C23)

Theorem 2 of the exploratory pass, except `exitFrameC` and `terminate`: the kernel invariant of
Spec 1 §57 re-indexed (`KInvC`), with the auxiliaries of Spec 1 `reachable_inv` (`KAux`,
`HeldAnchored`) read on the flat state, is preserved by the inherited operations O1–O16 other than
O7 executed by a context (Spec 1 §60–§72, §74, §75; WC3 C2), by `spawn` (WC3 C4), `join` (WC3 C8)
and `deriveSync` (WC3 C15).

The clauses of Spec 1 that read the stack only through membership are obtained from the Spec 1
lemmas on the view of the executing context; the anchor orders are proved on `ancestorC`.
Helper lemmas live in `Ern.Concurrency.PreservationAux`.
-/

namespace Ern.Concurrency

open Ern.MemoryModel.Access

/-- The inductive invariant of theorem 2 (WC3 C20, C23): `KInvC` (Spec 1 §57 re-indexed) with the
auxiliaries `KAux` and `HeldAnchored` of Spec 1 `reachable_inv`, read on the flat state. -/
def KInvCA (s : SC) : Prop := KInvC s ∧ KAux s.flat ∧ HeldAnchored s.flat

namespace PreservationAux

/-! ## Membership transport (WC3 C2) -/

/-- `HeldAnchored` reads the stack only through membership (Spec 1 §44, §40). -/
theorem heldAnchored_mem_congr {t : S3} {F' : Frames} (h : HeldAnchored t)
    (hF : ∀ f, f ∈ F' ↔ f ∈ t.F) : HeldAnchored { t with F := F' } :=
  fun x y q hy ya ho hh hq => h x y q hy ya ho hh ((usable_mem_congr hF).1 hq)

/-- The kernel facts of Spec 1 on the view of a context, from the re-indexed invariant (WC3
C2). -/
theorem view_facts {s : SC} (hk : KInvCA s) (c : Nat) :
    WF3 (s.view c) ∧ Inv3base (s.view c) ∧ NoDangling (s.view c) ∧ RootHeldConv (s.view c) ∧
      HeldAnchored (s.view c) := by
  obtain ⟨⟨⟨hfr, hw⟩, ⟨⟨h1, h2, h3, -⟩, -, hnd⟩, -, -⟩, hc, hh⟩ := hk
  have hF : ∀ f, f ∈ (s.view c).F ↔ f ∈ s.flat.F := fun f => SC.mem_view_F
  exact ⟨SC.wf3_view hfr hw, ⟨h1, h2, i3_mem_congr h3 hF, i4_always _⟩,
    noDangling_mem_congr hnd hF, hc, heldAnchored_mem_congr hh hF⟩

/-- The flat state of `s'` is `t` with the globally live frames of `s'` (WC3 C2); the kernel
facts of Spec 1 on `t` carry to the flat state of `s'` when `t` lists the same frames. -/
theorem flat_facts {s' : SC} {t : S3} (hflat : s'.flat = { t with F := s'.frames })
    (hmem : ∀ f, f ∈ t.F ↔ f ∈ s'.frames) (hnd : s'.frames.Nodup) (hne : s'.frames ≠ [])
    (hw : WF3 t) (hb : Inv3base t) (hd : NoDangling t) (hc : RootHeldConv t)
    (hh : HeldAnchored t) :
    WF3 s'.flat ∧ I1 s'.flat ∧ I2 s'.flat ∧ I3 s'.flat ∧ NoDangling s'.flat ∧ KAux s'.flat ∧
      HeldAnchored s'.flat := by
  have hF : ∀ f, f ∈ s'.frames ↔ f ∈ t.F := fun f => (hmem f).symm
  rw [hflat]
  exact ⟨wf3_mem_congr hw hF hnd hne, hb.1, hb.2.1, i3_mem_congr hb.2.2.1 hF,
    noDangling_mem_congr hd hF, hc, heldAnchored_mem_congr hh hF⟩

/-- Assembly of the re-indexed invariant (WC3 C20; Spec 1 §54: `NoOrphan` follows from `WF3`). -/
theorem kInvCA_of {s : SC} (hfr : FramesC s)
    (hf : WF3 s.flat ∧ I1 s.flat ∧ I2 s.flat ∧ I3 s.flat ∧ NoDangling s.flat ∧ KAux s.flat ∧
      HeldAnchored s.flat) (hao : AnchorOrderC s) (haoh : AnchorOrderHeldC s) : KInvCA s :=
  ⟨⟨⟨hfr, hf.1⟩, ⟨⟨hf.2.1, hf.2.2.1, hf.2.2.2.1, fun _ => i4_always _⟩, hao, hf.2.2.2.2.1⟩,
    haoh, noOrphan_of_wf3 hf.1⟩, hf.2.2.2.2.2.1, hf.2.2.2.2.2.2⟩

/-- The live frames of a nonempty frame structure are nonempty (WC3 C3). -/
theorem frames_ne {s : SC} (hfr : FramesC s) : s.frames ≠ [] := by
  intro he
  have h0 := hfr.initial
  unfold OptP at h0; split at h0
  · rename_i x hx
    have hs := hfr.nonempty 0 (by simp [SC.Live, hx, OptP, h0.1])
    obtain ⟨f, hf⟩ := List.exists_mem_of_ne_nil _ hs
    have := SC.mem_frames_of hf; rw [he] at this; simp at this
  · exact h0.elim

/-! ## Effective anchors on the extended ancestry (Spec 1 §44; WC3 C3) -/

/-- `EffAnchorOKC` carries over between states whose effective anchors have the same holder frame
and whose extended ancestry contains the former on the target frame (Spec 1 §44, mirroring
`Frames.effAnchorOK_of_same`). -/
theorem effAnchorOKC_of_same {s s' : SC} {x x' : Nat} {z z' : Authority}
    (hz : s.A[s.flat.effAnchor x]? = some z) (hz' : s'.A[s'.flat.effAnchor x']? = some z')
    (hh : s'.flat.hframe z'.holder = s.flat.hframe z.holder) {fd : Option Nat}
    (hanc : ∀ g f, fd = some f → s.ancestorC g f → s'.ancestorC g f)
    (h : EffAnchorOKC s x fd) : EffAnchorOKC s' x' fd := by
  unfold EffAnchorOKC at h ⊢
  have hz₁ : s.flat.A[s.flat.effAnchor x]? = some z := hz
  have hz₁' : s'.flat.A[s'.flat.effAnchor x']? = some z' := hz'
  rw [show s.A = s.flat.A from rfl, hz₁] at h
  rw [show s'.A = s'.flat.A from rfl, hz₁']
  simp only [OptP] at h ⊢
  rw [hh]
  revert h
  cases s.flat.hframe z.holder with
  | none => exact id
  | some g =>
    cases hf : fd with
    | none => exact id
    | some f => exact hanc g f hf

/-- The authority at the effective anchor of an `EffAnchorOKC` authority exists (Spec 1 §44). -/
theorem effAnchorOKC_get {s : SC} {x : Nat} {fd : Option Nat} (h : EffAnchorOKC s x fd) :
    ∃ z, s.A[s.flat.effAnchor x]? = some z := by
  unfold EffAnchorOKC at h
  cases e : s.A[s.flat.effAnchor x]? with
  | none => rw [e] at h; exact h.elim
  | some z => exact ⟨z, rfl⟩

/-! ## Operations that keep places and only add frame-held authorities, release, or drop
anchors (Spec 1 §60–§62, §66–§70, §74, §75) -/

/-- Skeleton of a step on the view of a context that keeps places, keeps the origin and the
holder of existing authorities, only deactivates them, adds only frame-held authorities, shrinks
usability and anchors (Spec 1 §60–§62, §66–§70, §74, §75 `ok` effects). -/
structure SkelV (s : SC) (t : S3) : Prop where
  P : t.P = s.P
  len : s.A.length ≤ t.A.length
  old : ∀ x y', t.A[x]? = some y' → x < s.A.length → ∃ y, s.A[x]? = some y ∧
    y'.origin = y.origin ∧ y'.holder = y.holder ∧ (y'.active = true → y.active = true)
  new : ∀ x y', t.A[x]? = some y' → s.A.length ≤ x → ∃ f, y'.holder = .frame f
  usable : ∀ q, t.Usable q → s.flat.Usable q
  D : ∀ q, t.Usable q → ∀ x ∈ t.D q, x ∈ s.D q

/-- Under `SkelV`, the origin links below `|A|` are unchanged (Spec 1 §42). -/
theorem SkelV.org {s : SC} {t : S3} (h : SkelV s t) {j : Nat} (hj : j < s.A.length) :
    t.org j = s.flat.org j := by
  obtain ⟨y, hy⟩ : ∃ y, s.A[j]? = some y := ⟨_, List.getElem?_eq_getElem hj⟩
  obtain ⟨y', hy'⟩ : ∃ y', t.A[j]? = some y' :=
    ⟨_, List.getElem?_eq_getElem (Nat.lt_of_lt_of_le hj h.len)⟩
  obtain ⟨y₀, hy₀, ho, -⟩ := h.old j y' hy' hj
  rw [hy] at hy₀; cases hy₀
  simp [S3.org, hy', SC.flat, hy, ho]

/-- Under `SkelV`, effective anchors below `|A|` are unchanged (Spec 1 §44). -/
theorem SkelV.effAnchor {s : SC} {t : S3} (h : SkelV s t) {x : Nat} (hx : x < s.A.length) :
    t.effAnchor x = s.flat.effAnchor x := by
  have : t.ancs x = s.flat.ancs x :=
    chain_congr fun j hj => h.org (Nat.lt_of_le_of_lt hj hx)
  simp only [S3.effAnchor, this]

/-- Under `SkelV`, `EffAnchorOKC` of an authority below `|A|` carries to the written-back state
(Spec 1 §44; WC3 C2). -/
theorem SkelV.effAnchorOKC {s : SC} {t : S3} (h : SkelV s t) {x : Nat} (hx : x < s.A.length)
    {fd : Option Nat} (hok : EffAnchorOKC s x fd) : EffAnchorOKC (s.set t) x fd := by
  obtain ⟨z, hz⟩ := effAnchorOKC_get hok
  have he : (s.set t).flat.effAnchor x = s.flat.effAnchor x := h.effAnchor hx
  have hel : s.flat.effAnchor x < s.A.length := Nat.lt_of_le_of_lt (Frames.effAnchor_le _ x) hx
  obtain ⟨z', hz'⟩ : ∃ z', t.A[s.flat.effAnchor x]? = some z' :=
    ⟨_, List.getElem?_eq_getElem (Nat.lt_of_lt_of_le hel h.len)⟩
  obtain ⟨z₀, hz₀, -, hzh, -⟩ := h.old _ z' hz' hel
  rw [hz] at hz₀; cases hz₀
  refine effAnchorOKC_of_same (s' := s.set t) (z' := z') hz
    (by show t.A[(s.set t).flat.effAnchor x]? = _; rw [he]; exact hz')
    ?_ (fun g f _ hg => hg) hok
  rw [hzh]; exact S3.hframe_congr h.P _

/-- Usability in the written-back state is usability in `t` (WC3 C2). -/
theorem set_usable {s : SC} {t : S3} (hmem : ∀ f, f ∈ t.F ↔ f ∈ s.frames) {q : Nat} :
    (s.set t).flat.Usable q ↔ t.Usable q :=
  usable_mem_congr (t := t) (F' := s.frames) fun f => (hmem f).symm

/-- `AnchorOrderC` after a `SkelV` step (Spec 1 §44, §52; WC3 C2). -/
theorem SkelV.anchorOrderC {s : SC} {t : S3} (h : SkelV s t)
    (hmem : ∀ f, f ∈ t.F ↔ f ∈ s.frames) (h3 : I3 s.flat) (hao : AnchorOrderC s) :
    AnchorOrderC (s.set t) := by
  intro q hq x hx
  have hq' := (set_usable hmem).1 hq
  have hx' := h.D q hq' x hx
  have hqs := h.usable q hq'
  obtain ⟨y, hy, -⟩ := h3 q hqs x hx'
  have hpf : (s.set t).flat.pframe q = s.flat.pframe q := S3.pframe_congr h.P q
  rw [hpf]
  exact h.effAnchorOKC (lt_of_getElem? hy) (hao q hqs x hx')

/-- `AnchorOrderHeldC` after a `SkelV` step (Spec 1 §44; WC3 C2). -/
theorem SkelV.anchorOrderHeldC {s : SC} {t : S3} (h : SkelV s t)
    (hmem : ∀ f, f ∈ t.F ↔ f ∈ s.frames) (haoh : AnchorOrderHeldC s) :
    AnchorOrderHeldC (s.set t) := by
  intro q hq x y' hy' ya hh
  have hq' := (set_usable hmem).1 hq
  by_cases hx : x < s.A.length
  · obtain ⟨y, hy, -, hyh, hya⟩ := h.old x y' hy' hx
    have hpf : (s.set t).flat.pframe q = s.flat.pframe q := S3.pframe_congr h.P q
    rw [hpf]
    exact h.effAnchorOKC hx (haoh q (h.usable q hq') x y hy (hya ya) (hyh ▸ hh))
  · obtain ⟨f, hf⟩ := h.new x y' hy' (Nat.le_of_not_lt hx)
    rw [hf] at hh; cases hh

/-- `FramesC` after a step that keeps the contexts and `nF` (WC3 C3). -/
theorem framesC_set {s : SC} {t : S3} (hfr : FramesC s) (hn : t.nF = s.nF) :
    FramesC (s.set t) where
  initial := hfr.initial
  nonempty := hfr.nonempty
  nodup := hfr.nodup
  bound := fun f hf => by show f < t.nF; rw [hn]; exact hfr.bound f hf
  rooted := hfr.rooted
  parent := hfr.parent

/-- A `SkelV` step on the view of a context with Spec 1 facts on its result preserves the
re-indexed invariant (WC3 C2, C20). -/
theorem set_preserves {s : SC} {c : Nat} {t : S3} (hk : KInvCA s) (hF : t.F = (s.view c).F)
    (hn : t.nF = s.nF) (hsk : SkelV s t) (hw : WF3 t) (hb : Inv3base t) (hd : NoDangling t)
    (hc : RootHeldConv t) (hh : HeldAnchored t) : KInvCA (s.set t) := by
  have hfr := hk.1.1.1
  have hmem : ∀ f, f ∈ t.F ↔ f ∈ s.frames := fun f => by rw [hF]; exact SC.mem_view_F
  exact kInvCA_of (framesC_set hfr hn)
    (flat_facts rfl hmem hfr.nodup (frames_ne (s := s) hfr) hw hb hd hc hh)
    (hsk.anchorOrderC hmem hk.1.2.1.1.2.2.1 hk.1.2.1.2.1)
    (hsk.anchorOrderHeldC hmem hk.1.2.2.1)

/-! ## Skeletons of the operations on the view (Spec 1 §60–§62, §66–§68, §74, §75 `ok` effects) -/

/-- Usability after a step on the view that keeps places and only adds death markers (Spec 1
§40; WC3 C2). -/
theorem usable_back {s : SC} {c : Nat} {t : S3} {q : Nat} (h : t.Usable q) (hP : t.P = s.P)
    (hF : t.F = (s.view c).F) (hd : ∀ q, t.dead q = false → s.dead q = false) :
    s.flat.Usable q :=
  S3.Usable.mono (s' := t) (s := s.flat) hP (fun _ hf => SC.mem_view_F.1 (hF ▸ hf)) hd h

/-- Skeleton of a step on the view appending frame-held authorities (Spec 1 §60, §61 `ok`
effects; WC3 C15). -/
theorem skelV_append {s : SC} {c : Nat} {E : List Authority}
    (hE : ∀ y ∈ E, ∃ f, y.holder = .frame f) :
    SkelV s { s.view c with A := (s.view c).A ++ E } where
  P := rfl
  len := by simp [SC.view, SC.flat]
  old := fun x y' hy' hx => ⟨y', by
    have : x < (s.view c).A.length := hx
    rw [List.getElem?_append_left this] at hy'; exact hy', rfl, rfl, id⟩
  new := fun x y' hy' hx => hE y' (by
    have : (s.view c).A.length ≤ x := hx
    rw [List.getElem?_append_right this] at hy'; exact List.mem_of_getElem? hy')
  usable := fun _ h => usable_back (c := c) h rfl rfl (fun _ h => h)
  D := fun _ _ _ h => h

/-- Skeleton of a step on the view keeping authorities and anchors (Spec 1 §66–§68, §74, §75 `ok`
effects). -/
theorem skelV_same {s : SC} {c : Nat} {t : S3} (hP : t.P = s.P) (hF : t.F = (s.view c).F)
    (hA : t.A = s.A) (hD : t.D = s.D) (hd : t.dead = s.dead) : SkelV s t where
  P := hP
  len := by rw [hA]; exact Nat.le_refl _
  old := fun x y' hy' _ => ⟨y', by rw [← hA]; exact hy', rfl, rfl, id⟩
  new := fun x y' hy' hx => absurd (lt_of_getElem? hy') (by rw [hA]; omega)
  usable := fun _ h => usable_back h hP hF (fun q h' => by rw [← hd]; exact h')
  D := fun _ _ x hx => by rw [← hD]; exact hx

/-- Skeleton of `release` on the view (Spec 1 §62 `ok` effect). -/
theorem skelV_release {s : SC} {c a : Nat} : SkelV s (releaseEff (s.view c) a) := by
  cases hx₀ : (s.view c).A[a]? with
  | none =>
    simp only [releaseEff, hx₀]
    exact skelV_same rfl rfl rfl rfl rfl
  | some x₀ =>
    rw [releaseEff_eq hx₀]
    have ha : a < (s.view c).A.length := lt_of_getElem? hx₀
    refine ⟨rfl, by simp [SC.view, SC.flat], fun x y' hy' _ => ?_, fun x y' hy' hx => ?_,
      fun _ h => usable_back (c := c) h rfl rfl (fun _ h => h), fun q _ x hx => ?_⟩
    · simp only [set_get ha] at hy'
      split at hy'
      · rename_i e; subst e; cases hy'
        exact ⟨x₀, hx₀, rfl, rfl, fun h => by cases h⟩
      · exact ⟨y', hy', rfl, rfl, id⟩
    · simp only [set_get ha] at hy'
      split at hy'
      · rename_i e; subst e; exact absurd hx (Nat.not_le_of_lt (by exact ha))
      · exact absurd (lt_of_getElem? hy') (by simp [SC.view, SC.flat] at hx ⊢; omega)
    · simp only at hx; split at hx
      · exact (List.mem_filter.1 hx).1
      · exact hx

/-- The `ok` outcomes of the operations other than O6, O7 keep the stack and `nF` (Spec 1
§60–§71, §74, §75 effects). -/
theorem viewOp_FnF {k : K} {t t' : S3} {op : KernelOp} (hop : op.Step k t (.ok t'))
    (hnx : op ≠ .exit) (hne : ∀ ps ls, op ≠ .enter ps ls) : t'.F = t.F ∧ t'.nF = t.nF := by
  cases op with
  | exit => exact absurd rfl hnx
  | enter => exact absurd rfl (hne _ _)
  | transfer => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hop; exact ⟨rfl, rfl⟩
  | depend => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hop; exact ⟨rfl, rfl⟩
  | store => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hop; unfold storeEff; split <;> exact ⟨rfl, rfl⟩
  | derive => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hop; exact ⟨rfl, rfl⟩
  | split => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hop; exact ⟨rfl, rfl⟩
  | release =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hop; unfold releaseEff; split <;> exact ⟨rfl, rfl⟩
  | read => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hop; exact ⟨rfl, rfl⟩
  | write => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hop; exact ⟨rfl, rfl⟩
  | writeShared => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hop; exact ⟨rfl, rfl⟩
  | pin => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hop; exact ⟨rfl, rfl⟩
  | unpin => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hop; exact ⟨rfl, rfl⟩
  | endUse => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hop; exact ⟨rfl, rfl⟩
  | free => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hop; exact ⟨rfl, rfl⟩
  | alloc => cases hop; exact ⟨rfl, rfl⟩

/-! ## `endUse`, `free` (Spec 1 §69, §70) -/

section Releases

open Ern.MemoryModel.Access.EndFree

/-- The part of `EndFree.releases_preserve` (Spec 1 §57, §69, §70) that does not concern the anchor
orders: `WF3`, `I1`–`I4` and `NoDangling` after releasing authorities and marking places dead,
from `WF3`, `I1` and `I2` (the proof of `EndFree.releases_preserve` with the `AnchorOrder` and
`AnchorOrderHeld` parts removed). -/
theorem releases_base {s s₁ : S3} (hw : WF3 s) (i1 : I1 s) (i2 : I2 s)
    (hr : OnlyReleases s s₁) (hP : s₁.P = s.P) (hF : s₁.F = s.F) (hn : s₁.nF = s.nF)
    (hd : ∀ q, s₁.dead q = false → s.dead q = false)
    (hparts : ∀ (q : Nat) (pl : Place) (r : Nat), s.P[q]? = some pl → pl.parent = some r →
      s₁.dead r = s₁.dead q)
    (hI3 : ∀ q, s₁.Usable q → ∀ x ∈ s₁.D q, (cleanup s₁).Active x)
    (hroot : ∀ (r i : Nat) (z : Authority) (pr : Place), RootPlace s.P r → s₁.Usable r →
      s.A[i]? = some z → z.active = true → z.origin = none → s.P[r]? = some pr →
      z.holder = pr.owner → (∀ l, l ∈ z.footprint ↔ l ∈ footprint s.P r) → s₁.A[i]? = some z)
    (hkept : ∀ a b, s.Active a → ¬ (cleanup s₁).Active a → a ∈ s.ancs b →
      ¬ (cleanup s₁).Active b)
    (hnd : WF3 (cleanup s₁) → NoDangling (cleanup s₁)) :
    WF3 (cleanup s₁) ∧ Inv3base (cleanup s₁) ∧ NoDangling (cleanup s₁) := by
  have hc := hr.trans (cleanup_releases s₁)
  have cP : (cleanup s₁).P = s.P := hP
  have hu : ∀ q, s₁.Usable q → s.Usable q :=
    fun q h => S3.Usable.mono hP (fun f hf => hF ▸ hf) hd h
  have hU := cleanup_usable s₁
  have hw' : WF3 (cleanup s₁) :=
    { frames := by
        show s₁.F ≠ [] ∧ s₁.F.Nodup ∧ ∀ f ∈ s₁.F, f < s₁.nF
        rw [hF, hn]; exact hw.frames
      places := fun q pl r hq hp => by
        rw [cP] at hq
        obtain ⟨pr, hpr, hlt, ho, -⟩ := hw.places q pl r hq hp
        exact ⟨pr, by rw [cP]; exact hpr, hlt, ho, hparts q pl r hq hp⟩
      owners :=
        ⟨fun q pl f hq ho => by
          show f < s₁.nF
          rw [hn]; exact hw.owners.1 q pl f (by rw [← cP]; exact hq) ho,
        fun q pl o hq ho => by
          rw [cP]; exact hw.owners.2.1 q pl o (by rw [← cP]; exact hq) ho,
        fun q hq => hq.frameOf⟩
      footprints := fun a x hx l hl => by
        obtain ⟨x₀, hx₀, -, -, e, -⟩ := hc.2 a x hx
        rw [cP]; exact hw.footprints a x₀ hx₀ l (e ▸ hl)
      origins := fun b y a hb ho => by
        obtain ⟨y₀, hy₀, -, e, -⟩ := hc.2 b y hb
        exact hw.origins b y₀ a hy₀ (e ▸ ho)
      rootChain := hw.rootChain.transport (by rw [cP]) (by rw [cP]) (fun a => by rw [hc.ancs])
        (fun a y' hy' => by obtain ⟨y, hy, -, -, e, -⟩ := hc.2 a y' hy'; exact ⟨y, hy, e⟩)
        (fun x z hz hzo => by
          obtain ⟨z', hz', -, e1, e2, -⟩ := hc.get' hz
          exact ⟨z', hz', e1.trans hzo, e2⟩)
      rootHeld := fun r hrp hur => by
        rw [cP] at hrp
        have hu₁ := (hU r).1 hur
        obtain ⟨i, z, pr, hz, za, zo, zm, hpr, hh, hf⟩ := hw.rootHeld r hrp (hu r hu₁)
        have hz₁ := hroot r i z pr hrp hu₁ hz za zo hpr hh hf
        have hlive : HolderLive s₁ z.holder := by
          rw [hh]; exact owner_live hu₁ (by rw [hP]; exact hpr)
        refine ⟨i, z, pr, ?_, za, zo, zm, by rw [cP]; exact hpr, hh, by rw [cP]; exact hf⟩
        rw [cleanup_get, hz₁]; simp [hlive]
      holders := fun a y hy ya => by
        obtain ⟨-, hl⟩ := cleanup_active hy ya
        exact (HolderLive.congr (s := s₁) (s' := cleanup s₁) rfl rfl rfl _).2 hl }
  refine ⟨hw', ⟨?_, ?_, ?_, i4_always _⟩, hnd hw'⟩
  · intro a b x y p hab hx hy xa ya xp yp hnab hnba
    obtain ⟨x₀, hx₀, m₁, -, f₁, -, a₁⟩ := hc.2 a x hx
    obtain ⟨y₀, hy₀, m₂, -, f₂, -, a₂⟩ := hc.2 b y hy
    rw [hc.ancs] at hnab hnba; rw [m₁, m₂]
    exact i1 a b x₀ y₀ p hab hx₀ hy₀ (a₁ xa) (a₂ ya) (f₁ ▸ xp) (f₂ ▸ yp) hnab hnba
  · intro b y a hb ho
    obtain ⟨y₀, hy₀, m₀, e, f₀, -, a₀⟩ := hc.2 b y hb
    obtain ⟨x₁, hx₁, hm, hsub, hact⟩ := i2 b y₀ a hy₀ (e ▸ ho)
    obtain ⟨x', hx', mx, -, fx, -⟩ := hc.get' hx₁
    refine ⟨x', hx', by rw [m₀, mx]; exact hm, fun l hl => by rw [fx]; exact hsub l (f₀ ▸ hl),
      fun ya => ?_⟩
    have hob : s.org b = some a := by simp [S3.org, hy₀, ← e, ho]
    have hab : a ∈ s.ancs b := by
      rw [S3.ancs, chain_cons hob (hw.origins b y₀ a hy₀ (e ▸ ho))]; exact List.mem_cons_self ..
    cases hxa : x'.active
    · refine absurd ⟨y, hb, ya⟩ (hkept a b ⟨x₁, hx₁, hact (a₀ ya)⟩ ?_ hab)
      rintro ⟨x'', hx'', xa⟩
      rw [hx'] at hx''; cases hx''; rw [hxa] at xa; cases xa
    · rfl
  · exact fun q hq x hx => hI3 q ((hU q).1 hq) x hx

/-- `endUse` preserves `WF3`, `I1`–`I4` and `NoDangling` (Spec 1 §69; the proof of
`endUse_preserves` without the anchor orders). -/
theorem endUse_base {k : K} {s s' : S3} {p : Nat} (hw : WF3 s) (hb : Inv3base s)
    (hnd : NoDangling s) (h : EndUseStep k p s (.ok s')) :
    WF3 s' ∧ Inv3base s' ∧ NoDangling s' := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  refine releases_base hw hb.1 hb.2.1 (endUseS_releases s p) rfl rfl rfl
    (fun q h => by simp only [endUseS, Bool.or_eq_false_iff] at h; exact h.1)
    (fun q pl r hq hp => ?_) (endUse_anchors hb.2.2.1 hpre)
    (fun r i z pr _ hur hz _ _ hpr hzh _ => ?_)
    (kept_of_range ((endUseS_releases s p).trans (cleanup_releases _)) hpre.keptDesc)
    (endUse_noDangling hw hnd hb.1 hpre)
  · obtain ⟨-, -, -, -, hd⟩ := hw.places q pl r hq hp
    simp only [endUseS, hd, decide_eq_decide.2 (ownedIn_parent hw hq hp)]
  · have hnh : ¬ heldIn s.P p z.holder := fun hh => by
      have hd := dead_false hur
      simp only [endUseS, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hd
      rw [hzh] at hh
      cases ho : pr.owner with
      | frame f => rw [ho] at hh; exact hh
      | place o => rw [ho] at hh; exact hd.2 (.direct hpr ho hh)
    rw [endUseS_get, hz]; simp [hnh]

/-- `free` preserves `WF3`, `I1`–`I4` and `NoDangling` (Spec 1 §70; the proof of `free_preserves`
without the anchor orders). -/
theorem free_base {k : K} {s s' : S3} {p auth : Nat} (hw : WF3 s) (hb : Inv3base s)
    (hnd : NoDangling s) (h : FreeStep k p auth s (.ok s')) :
    WF3 s' ∧ Inv3base s' ∧ NoDangling s' := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  have hroot := rootPlace_of_ownedRoot hpre.ownedRoot
  refine releases_base hw hb.1 hb.2.1 (freeS_releases s p) rfl rfl rfl
    (fun q h => by simp only [freeS, Bool.or_eq_false_iff] at h; exact h.1)
    (fun q pl r hq hp => ?_) (free_anchors hb.2.2.1 hpre)
    (fun r i z pr hrp hur hz _ _ hpr hzh hzf => ?_)
    (kept_of_range ((freeS_releases s p).trans (cleanup_releases _)) hpre.keptDesc)
    (free_noDangling hw hnd hb.1 hpre)
  · obtain ⟨pr, hpr, hlt, -, hd⟩ := hw.places q pl r hq hp
    have hpo : parentOf s.P q = some r := by simp [parentOf, hq, hp]
    have hf : FreedPlace s.P p r ↔ FreedPlace s.P p q := by
      unfold FreedPlace
      rw [partOf_parent hpo hlt (lt_of_getElem? hpr) hroot.2, ownedIn_parent hw hq hp]
    simp only [freeS, hd, decide_eq_decide.2 hf]
  · have hnf : ¬ FreedPlace s.P p r := fun hf => by
      have := dead_false hur
      simp only [freeS, Bool.or_eq_false_iff, decide_eq_false_iff_not] at this
      exact this.2 hf
    have hc : ¬ ((∃ l ∈ z.footprint, FreedPlace s.P p l) ∨ heldIn s.P p z.holder) := by
      rintro (⟨l, hl, hfl⟩ | hh)
      · obtain ⟨-, -, hlr⟩ := mem_footprint.1 ((hzf l).1 hl)
        rcases hfl with hlp | hown
        · obtain rfl := rootOf_unique hrp hroot hlr hlp
          exact hnf (.inl ⟨hroot.1, .inl rfl⟩)
        · obtain ⟨pl, pr', hpl, hpr', ho⟩ := hw.ownerOf hlr
          exact hnf (.inr (ownedIn_of_owner hpl hpr' ho.symm hown))
      · rw [hzh] at hh
        cases ho : pr.owner with
        | frame f => rw [ho] at hh; exact hh
        | place o => rw [ho] at hh; exact hnf (.inr (.direct hpr ho hh))
    rw [freeS_get, hz]; simp [hc]

/-- Skeleton of a step that only releases authorities, shrinks usability and anchors (Spec 1
§69, §70 `ok` effects). -/
theorem skelV_releases {s : SC} {c : Nat} {t : S3} (hr : OnlyReleases (s.view c) t)
    (hP : t.P = s.P) (hu : ∀ q, t.Usable q → s.flat.Usable q)
    (hD : ∀ q, t.Usable q → ∀ x ∈ t.D q, x ∈ s.D q) : SkelV s t where
  P := hP
  len := by rw [hr.1]; exact Nat.le_refl _
  old := fun x y' hy' _ => by
    obtain ⟨y, hy, -, ho, -, hh, ha⟩ := hr.2 x y' hy'
    exact ⟨y, hy, ho, hh, ha⟩
  new := fun x y' hy' hx => absurd (lt_of_getElem? hy') (by rw [hr.1]; exact Nat.not_lt.2 hx)
  usable := hu
  D := hD

end Releases

/-! ## `alloc` (Spec 1 §71) -/

section AllocC

variable {k : K} {s : SC} {c pr ow : Nat} {ls : LocalShape}

/-- Usability on the view is usability on the flat state (WC3 C2). -/
theorem view_usable_flat {q : Nat} (h : (s.view c).Usable q) : s.flat.Usable q :=
  (usable_mem_congr (t := s.flat) (F' := (s.view c).F) (fun _ => SC.mem_view_F)).1 h

/-- The anchor-order condition of an existing authority carries over `alloc` on the extended
ancestry (Spec 1 §44, §71 `ok`; mirrors `Alloc.effAnchorOK_old`). -/
theorem alloc_effAnchorOKC_old (hst : AllocStatic k (s.view c) pr ow ls) (hw : WF3 (s.view c))
    {x : Nat} {fd : Option Nat} (h : EffAnchorOKC s x fd) :
    EffAnchorOKC (s.set (allocEff (s.view c) ow ls)) x fd := by
  have he : (s.set (allocEff (s.view c) ow ls)).flat.effAnchor x = s.flat.effAnchor x := by
    show (allocEff (s.view c) ow ls).effAnchor x = (s.view c).effAnchor x
    simp only [S3.effAnchor, Alloc.ancs_eq hst]
  obtain ⟨z, hz⟩ := effAnchorOKC_get h
  have hel : s.flat.effAnchor x < (s.view c).A.length := lt_of_getElem? hz
  have hz' : (s.set (allocEff (s.view c) ow ls)).A[(s.set (allocEff (s.view c) ow ls)).flat.effAnchor
      x]? = some z := by
    rw [he]; show (allocEff (s.view c) ow ls).A[s.flat.effAnchor x]? = _
    rw [Alloc.A_lt hel]; exact hz
  refine effAnchorOKC_of_same hz hz' ?_ (fun g f _ hg => hg) h
  cases hzh : z.holder with
  | frame f => rfl
  | place p =>
    cases hg : s.flat.pframe p with
    | none =>
      exfalso; unfold EffAnchorOKC at h; rw [hz] at h; simp [OptP, hzh, S3.hframe, hg] at h
    | some g =>
      have := Alloc.pframe_old (ls := ls) (ow := ow) hw (q := p) (pframe_iff.1 hg).lt
      show (s.set (allocEff (s.view c) ow ls)).flat.pframe p = s.flat.pframe p
      rw [S3.pframe_congr (s' := (s.set (allocEff (s.view c) ow ls)).flat)
        (s := allocEff (s.view c) ow ls) rfl p, this, S3.pframe_congr (s' := s.view c)
        (s := s.flat) rfl p]

/-- The new root authority of `alloc` satisfies the anchor-order condition for its holder on the
extended ancestry (Spec 1 §44, §71 `ok`; mirrors `Alloc.effAnchorOK_new`). -/
theorem alloc_effAnchorOKC_new (hst : AllocStatic k (s.view c) pr ow ls) (hw : WF3 (s.view c)) :
    EffAnchorOKC (s.set (allocEff (s.view c) ow ls)) s.A.length
      ((s.set (allocEff (s.view c) ow ls)).flat.pframe ow) := by
  have hA : (allocEff (s.view c) ow ls).A[(s.view c).A.length]? =
      some ⟨.modify, none, footprint (allocP (s.view c) ow ls) (s.view c).P.length, .place ow,
        true⟩ := by
    rw [Alloc.allocEff_A hst]; simp
  have he : (allocEff (s.view c) ow ls).effAnchor (s.view c).A.length = (s.view c).A.length := by
    simp only [S3.effAnchor, S3.ancs,
      chain_none (show (allocEff (s.view c) ow ls).org (s.view c).A.length = none by
        simp [S3.org, hA]),
      List.getLastD_nil]
  obtain ⟨f, hf, hfF⟩ := hst.ownerUsable.frameOf
  have hpf : (s.set (allocEff (s.view c) ow ls)).flat.pframe ow = some f := by
    rw [S3.pframe_congr (s' := (s.set (allocEff (s.view c) ow ls)).flat)
      (s := allocEff (s.view c) ow ls) rfl ow, Alloc.pframe_old hw hst.ownerUsable.lt]
    exact pframe_iff.2 hf
  unfold EffAnchorOKC
  show OptP ((allocEff (s.view c) ow ls).A[(allocEff (s.view c) ow ls).effAnchor
    (s.view c).A.length]?) _ False
  rw [he, hA]
  simp only [OptP, S3.hframe, hpf]
  exact ⟨SC.mem_view_F.1 hfF, .inl rfl⟩

/-- `alloc` preserves `AnchorOrderC` (Spec 1 §44, §71 `ok`; mirrors `Alloc.anchorOrder`). -/
theorem alloc_anchorOrderC (hst : AllocStatic k (s.view c) pr ow ls) (hw : WF3 (s.view c))
    (hao : AnchorOrderC s) : AnchorOrderC (s.set (allocEff (s.view c) ow ls)) := by
  intro q hq x hx
  have hq' : (allocEff (s.view c) ow ls).Usable q :=
    (set_usable (t := allocEff (s.view c) ow ls) (fun _ => SC.mem_view_F)).1 hq
  change x ∈ (if (s.view c).P.length ≤ q then [] else (s.view c).D q) at hx
  by_cases hql : q < (s.view c).P.length
  · have hq0 := Alloc.usable_back hw hq' hql
    simp only [show ¬ (s.view c).P.length ≤ q from Nat.not_le.2 hql, ↓reduceIte] at hx
    rw [S3.pframe_congr (s' := (s.set (allocEff (s.view c) ow ls)).flat)
      (s := allocEff (s.view c) ow ls) rfl q, Alloc.pframe_old hw hql,
      S3.pframe_congr (s' := s.view c) (s := s.flat) rfl q]
    exact alloc_effAnchorOKC_old hst hw (hao q (view_usable_flat hq0) x hx)
  · simp only [show (s.view c).P.length ≤ q from Nat.le_of_not_lt hql, ↓reduceIte] at hx
    cases hx

/-- `alloc` preserves `AnchorOrderHeldC` (Spec 1 §44, §71 `ok`; mirrors
`Alloc.anchorOrderHeld`). -/
theorem alloc_anchorOrderHeldC (hst : AllocStatic k (s.view c) pr ow ls) (hw : WF3 (s.view c))
    (haoh : AnchorOrderHeldC s) : AnchorOrderHeldC (s.set (allocEff (s.view c) ow ls)) := by
  intro q hq x y hx ya hh
  rcases Alloc.allocA_get hst hx with ⟨-, hx'⟩ | ⟨rfl, rfl⟩
  · have hq0 : (s.view c).Usable q := by
      have := hw.holders x y hx' ya; rw [hh] at this; exact this
    rw [S3.pframe_congr (s' := (s.set (allocEff (s.view c) ow ls)).flat)
      (s := allocEff (s.view c) ow ls) rfl q, Alloc.pframe_old hw hq0.lt,
      S3.pframe_congr (s' := s.view c) (s := s.flat) rfl q]
    exact alloc_effAnchorOKC_old hst hw (haoh q (view_usable_flat hq0) x y hx' ya hh)
  · cases hh
    exact alloc_effAnchorOKC_new hst hw

end AllocC

/-! ## The operations run on the view (Spec 1 §60–§62, §66–§71, §74, §75) -/

/-- Every inherited operation other than O4, O5, O6, O7, O8, run on the view of a context,
preserves the re-indexed invariant (Spec 1 §57 re-indexed; WC3 C2, C20), under `DDSound`
(Spec 1 §80, used by `split`). -/
theorem viewOp_preserves {k : K} {s : SC} {c : Nat} {op : KernelOp} {t : S3} (hdd : DDSound k)
    (hk : KInvCA s) (hop : op.Step k (s.view c) (.ok t)) (hnx : op ≠ .exit)
    (hne : ∀ ps ls, op ≠ .enter ps ls) (hnt : ∀ a b, op ≠ .transfer a b)
    (hnd : ∀ q x, op ≠ .depend q x) (hns : ∀ a p, op ≠ .store a p) : KInvCA (s.set t) := by
  obtain ⟨hw, hb, hd, hc, hh⟩ := view_facts hk c
  obtain ⟨hF, hn⟩ := viewOp_FnF hop hnx hne
  have hh' := op_preserves_heldAnchored hw hh hop
  cases op with
  | exit => exact absurd rfl hnx
  | enter => exact absurd rfl (hne _ _)
  | transfer => exact absurd rfl (hnt _ _)
  | depend => exact absurd rfl (hnd _ _)
  | store => exact absurd rfl (hns _ _)
  | derive src region m =>
    have h := hop
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hop
    exact set_preserves hk hF hn
      (skelV_append fun y hy => by rw [List.mem_singleton.1 hy]; exact ⟨_, rfl⟩)
      (derive_preserves_wf3 hw h)
      ⟨derive_preserves_exclusivity hb.1 h, derive_preserves_i2 hb.2.1 h,
        derive_preserves_i3 hb.2.2.1 h, i4_always _⟩
      (derive_preserves_noDangling hd h) (derive_preserves_rootHeldConv hc h) hh'
  | split src rs =>
    have h := hop
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hop
    exact set_preserves hk hF hn
      (skelV_append fun y hy => by obtain ⟨r, -, rfl⟩ := List.mem_map.1 hy; exact ⟨_, rfl⟩)
      (split_preserves_wf3 hw h)
      ⟨split_preserves_exclusivity hdd hb.1 h, split_preserves_i2 hb.2.1 h,
        split_preserves_i3 hb.2.2.1 h, i4_always _⟩
      (split_preserves_noDangling hd h) (split_preserves_rootHeldConv hc h) hh'
  | release a =>
    have h := hop
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hop
    exact set_preserves hk hF hn skelV_release (release_preserves_wf3 hw h)
      ⟨release_preserves_exclusivity hb.1 h, release_preserves_i2 hw hb.2.1 h,
        release_preserves_i3 hb.2.2.1 h, i4_always _⟩
      (release_preserves_noDangling hd h) (release_preserves_rootHeldConv hc h) hh'
  | read =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hop
    exact set_preserves hk hF hn (skelV_same rfl rfl rfl rfl rfl) hw hb hd hc hh'
  | write a ls =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hop
    obtain ⟨hw', hb'⟩ := write3Eff_preserves_base ls hw hb
    exact set_preserves hk hF hn (skelV_same rfl rfl rfl rfl rfl) hw' hb'
      (write3Eff_preserves_noDangling ls hd) (write3Eff_preserves_rootHeldConv ls hc) hh'
  | writeShared a ls =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hop
    obtain ⟨hw', hb'⟩ := write3Eff_preserves_base ls hw hb
    exact set_preserves hk hF hn (skelV_same rfl rfl rfl rfl rfl) hw' hb'
      (write3Eff_preserves_noDangling ls hd) (write3Eff_preserves_rootHeldConv ls hc) hh'
  | pin p =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hop
    obtain ⟨hw', hb'⟩ := pinEff_preserves_base p hw hb
    exact set_preserves hk hF hn (skelV_same rfl rfl rfl rfl rfl) hw' hb'
      (pinEff_preserves_noDangling p hd) (pinEff_preserves_rootHeldConv p hc) hh'
  | unpin o =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hop
    obtain ⟨hw', hb'⟩ := unpinEff_preserves_base o hw hb
    exact set_preserves hk hF hn (skelV_same rfl rfl rfl rfl rfl) hw' hb'
      (unpinEff_preserves_noDangling o hd) (unpinEff_preserves_rootHeldConv o hc) hh'
  | endUse p =>
    have h := hop
    obtain ⟨hw', hb', hd'⟩ := endUse_base hw hb hd h
    have hc' := endUse_preserves_kAux hc h
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hop
    refine set_preserves hk hF hn (skelV_releases
      ((EndFree.endUseS_releases _ p).trans (EndFree.cleanup_releases _)) rfl
      (fun q hq => view_usable_flat (EndFree.endUseS_usable ((EndFree.cleanup_usable _ q).1 hq)))
      (fun q _ x hx => ?_)) hw' hb' hd' hc' hh'
    change x ∈ (if partOf (s.view c).P q p then [] else (s.view c).D q) at hx
    split at hx
    · cases hx
    · exact hx
  | free p auth =>
    have h := hop
    obtain ⟨hw', hb', hd'⟩ := free_base hw hb hd h
    have hc' := free_preserves_kAux hc h
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hop
    exact set_preserves hk hF hn (skelV_releases
      ((EndFree.freeS_releases _ p).trans (EndFree.cleanup_releases _)) rfl
      (fun q hq => view_usable_flat (EndFree.freeS_usable ((EndFree.cleanup_usable _ q).1 hq)))
      (fun q _ x hx => hx)) hw' hb' hd' hc' hh'
  | alloc pr ow ls =>
    cases hop with
    | ok hst _ =>
      have hfr := hk.1.1.1
      have hmem : ∀ f, f ∈ (allocEff (s.view c) ow ls).F ↔ f ∈ s.frames :=
        fun _ => SC.mem_view_F
      exact kInvCA_of (framesC_set hfr hn)
        (flat_facts rfl hmem hfr.nodup (frames_ne (s := s) hfr) (Alloc.wf3 hst hw)
          ⟨Alloc.i1 hst hw hb.1, Alloc.i2 hst hb.2.1, Alloc.i3 hw hb.2.2.1, i4_always _⟩
          (Alloc.noDangling hst hw hd) (Alloc.rootHeldConv hst hw hc) hh')
        (alloc_anchorOrderC hst hw hk.1.2.1.2.1) (alloc_anchorOrderHeldC hst hw hk.1.2.2.1)

/-! ## Skeleton transport (the helpers of `Ern.MemoryModel.Access` §64, §65 preservation,
private there) -/

/-- Equal authority lists have the same skeletons (Spec 1 §42; copy of the private `skel_of_A` of
`Preserve/Small.lean`). -/
theorem skel_of_A {s s' : S3} (hA : s'.A = s.A) : SameSkel s s' :=
  ⟨by rw [hA], fun j => by rw [hA]⟩

/-- `WF3` (Spec 1 §49) carries over to a state with the same places, stack, fresh frame bound
and death markers, the same skeletons, the same authorities with no origin, and live holders for
its active authorities (copy of the private `wf3_skel` of `Preserve/Small.lean`). -/
theorem wf3_skel {s s' : S3} (hw : WF3 s) (sk : SameSkel s s') (hP : s'.P = s.P)
    (hF : s'.F = s.F) (hn : s'.nF = s.nF) (hd : s'.dead = s.dead)
    (hroot : ∀ (i : Nat) (z : Authority), z.origin = none → (s'.A[i]? = some z ↔ s.A[i]? = some z))
    (hhold : ∀ (a : Nat) (y : Authority), s'.A[a]? = some y → y.active = true →
      HolderLive s y.holder) : WF3 s' :=
  { frames := by rw [hF, hn]; exact hw.frames
    places := by rw [hP, hd]; exact hw.places
    owners := by
      refine ⟨by rw [hP, hn]; exact hw.owners.1, by rw [hP]; exact hw.owners.2.1, fun q hq => ?_⟩
      obtain ⟨f, hf, hfF⟩ := hw.owners.2.2 q ((S3.Usable.congr hP hF hd).1 hq)
      exact ⟨f, (FrameOf.congr hP).2 hf, by rw [hF]; exact hfF⟩
    footprints := by
      rw [hP]; exact sk.footprints (Q := fun l => l < s.P.length ∧ isLeaf s.P l) hw.footprints
    origins := sk.origins hw.origins
    rootChain := sk.rootChain hw.rootChain (by rw [hP]) (by rw [hP])
    rootHeld := hw.rootHeld.transport hP (fun _ hr => (S3.Usable.congr hP hF hd).1 hr)
      fun i z hz _ hzo => (hroot i z hzo).2 hz
    holders := fun a y hy ya => (HolderLive.congr hP hF hd _).2 (hhold a y hy ya) }

/-- `I1`–`I4` (Spec 1 §50–§53) carry over to a state with the same places, stack, death markers and
skeletons, whose anchors of usable places are active (copy of the private `inv3base_skel` of
`Preserve/Small.lean`). -/
theorem inv3base_skel {s s' : S3} (hi : Inv3base s) (sk : SameSkel s s')
    (hP : s'.P = s.P) (hF : s'.F = s.F) (hd : s'.dead = s.dead)
    (hD : ∀ q : Nat, s.Usable q → ∀ x ∈ s'.D q, s.Active x) : Inv3base s' := by
  obtain ⟨i1, i2, -, -⟩ := hi
  exact ⟨sk.i1 i1, sk.i2 i2,
    fun q hq x hx => sk.active.2 (hD q ((S3.Usable.congr hP hF hd).1 hq) x hx), i4_always _⟩

/-- `NoDangling` (Spec 1 §54) carries over to a state with the same places, stack, death markers
and skeletons (copy of the private `noDangling_skel` of `Preserve/Small.lean`). -/
theorem noDangling_skel {s s' : S3} (h : NoDangling s) (sk : SameSkel s s')
    (hP : s'.P = s.P) (hF : s'.F = s.F) (hd : s'.dead = s.dead) : NoDangling s' := by
  intro j y hy ya q hq l hl hly
  obtain ⟨y0, hy0, e⟩ := sk.get hy
  simp only [skel, Prod.mk.injEq] at e
  rw [hP] at hl
  exact h j y0 hy0 (by rw [← e.2.2.2]; exact ya) q
    (fun hu => hq ((S3.Usable.congr hP hF hd).2 hu)) l hl (by rw [← e.2.2.1]; exact hly)

/-- `RootHeldConv` (Spec 1 §40, §49.7) carries over to a state with the same places whose
authorities with no origin are authorities of the previous state (copy of the private
`rootHeldConv_of` of `Preserve/Small.lean`). -/
theorem rootHeldConv_of {s s' : S3} (h : RootHeldConv s) (hP : s'.P = s.P)
    (hroot : ∀ (i : Nat) (z : Authority), z.origin = none → s'.A[i]? = some z → s.A[i]? = some z) :
    RootHeldConv s' :=
  h.transport hP fun x z hx hzo => ⟨z, hroot x z hzo hx, hzo, rfl, rfl⟩

/-- `EffAnchorOKC` is unchanged by a step keeping places, contexts, skeletons and the authorities
with no origin: under `WF3` the effective anchor has no origin (Spec 1 §44; mirrors the private
`effAnchorOK_skel` of `Preserve/Small.lean`). -/
theorem effAnchorOKC_skel {s : SC} {t : S3} (hw : WF3 s.flat) (sk : SameSkel s.flat t)
    (hP : t.P = s.P)
    (hroot : ∀ (i : Nat) (z : Authority), z.origin = none → (t.A[i]? = some z ↔ s.A[i]? = some z))
    {x : Nat} {fd : Option Nat} (h : EffAnchorOKC s x fd) : EffAnchorOKC (s.set t) x fd := by
  have he : (s.set t).flat.effAnchor x = s.flat.effAnchor x := by
    show t.effAnchor x = _; simp only [S3.effAnchor, sk.ancs]
  obtain ⟨z, hz⟩ := effAnchorOKC_get h
  have hzo : z.origin = none := by
    have := Frames.effAnchor_root hw x
    simpa only [S3.org, show s.flat.A[s.flat.effAnchor x]? = some z from hz,
      Option.bind_some] using this
  have hz' : (s.set t).A[(s.set t).flat.effAnchor x]? = some z := by
    rw [he]; exact (hroot _ z hzo).2 hz
  exact effAnchorOKC_of_same hz hz' (S3.hframe_congr hP _) (fun g f _ hg => hg) h

/-- Usability on the flat state after a write-back keeping places and death markers (WC3
C2). -/
theorem set_usable_iff {s : SC} {t : S3} (hP : t.P = s.P) (hd : t.dead = s.dead) {q : Nat} :
    (s.set t).flat.Usable q ↔ s.flat.Usable q :=
  S3.Usable.congr (s := s.flat) (s' := (s.set t).flat) hP rfl hd

/-- `HeldAnchored` after a step keeping places, stack and death markers whose held derived
authorities were held derived authorities before, with anchors kept (Spec 1 §44; the
`HeldAnchored` argument of Spec 1 `op_preserves_heldAnchored`). -/
theorem heldAnchored_of_step {s s' : S3} (hw : WF3 s) (hh : HeldAnchored s)
    (hstep : ∀ x y q, s'.A[x]? = some y → y.active = true → y.origin ≠ none →
      y.holder = .place q → x ∈ s'.D q ∨ ∃ y₀ : Authority, s.A[x]? = some y₀ ∧
        y₀.active = true ∧ y₀.origin ≠ none ∧ y₀.holder = .place q ∧
        (s.Usable q → x ∈ s.D q → x ∈ s'.D q)) : HeldAnchored s' := by
  intro x y q hy ya ho hhq _
  rcases hstep x y q hy ya ho hhq with h | ⟨y₀, hy₀, ya₀, ho₀, hh₀, himp⟩
  · exact h
  · have hu : s.Usable q := by have := hw.holders x y₀ hy₀ ya₀; rw [hh₀] at this; exact this
    exact himp hu (hh x y₀ q hy₀ ya₀ ho₀ hh₀ hu)

/-! ## O5 `depend` re-indexed (Spec 1 §64) -/

/-- `depend` executed by a context preserves the re-indexed invariant (Spec 1 §57, §64; WC3 C2,
C20): only anchors change; the new anchor is active (§64.2) and satisfies §64.3 on
`ancestorC`. -/
theorem depend_preserves {s : SC} {c q x : Nat} (hk : KInvCA s) (hpre : DependPreC s c q x) :
    KInvCA (dependEffC s c q x) := by
  obtain ⟨hw, hb, hd, hc, hh⟩ := view_facts hk c
  have hfr := hk.1.1.1
  have hD : ∀ r y, y ∈ (dependEff (s.view c) q x).D r → y ∈ s.D r ∨ (r = q ∧ y = x) := by
    intro r y hy
    change y ∈ (if r = q then (s.view c).D q ++ [x] else (s.view c).D r) at hy
    split at hy
    · rename_i hrq
      rcases List.mem_append.1 hy with hy | hy
      · exact .inl (hrq ▸ hy)
      · exact .inr ⟨hrq, List.mem_singleton.1 hy⟩
    · exact .inl hy
  have hw' : WF3 (dependEff (s.view c) q x) :=
    wf3_skel hw (skel_of_A rfl) rfl rfl rfl rfl (fun _ _ _ => Iff.rfl)
      fun a y hy ya => hw.holders a y hy ya
  have hb' : Inv3base (dependEff (s.view c) q x) :=
    inv3base_skel hb (skel_of_A rfl) rfl rfl rfl fun r hr y hy => by
      rcases hD r y hy with hy | ⟨-, rfl⟩
      · exact hb.2.2.1 r hr y hy
      · exact hpre.anchorActive
  have hh' : HeldAnchored (dependEff (s.view c) q x) :=
    heldAnchored_of_step hw hh fun x' y r hy ya ho hhq => .inr ⟨y, hy, ya, ho, hhq, fun _ hx => by
      change x' ∈ (if r = q then (s.view c).D q ++ [x] else (s.view c).D r)
      split
      · rename_i e; subst e; exact List.mem_append_left _ hx
      · exact hx⟩
  have hmem : ∀ f, f ∈ (dependEff (s.view c) q x).F ↔ f ∈ s.frames := fun _ => SC.mem_view_F
  refine kInvCA_of (framesC_set hfr rfl)
    (flat_facts rfl hmem hfr.nodup (frames_ne (s := s) hfr) hw' hb'
      (noDangling_skel hd (skel_of_A rfl) rfl rfl rfl) (rootHeldConv_of hc rfl fun _ _ _ h => h)
      hh') ?_ ?_
  · intro r hr y hy
    have hr' := (set_usable_iff (t := dependEff (s.view c) q x) rfl rfl).1 hr
    rw [S3.pframe_congr (s' := (dependEffC s c q x).flat) (s := s.flat) rfl r]
    refine effAnchorOKC_skel (t := dependEff (s.view c) q x) hk.1.1.2 (skel_of_A rfl) rfl
      (fun _ _ _ => Iff.rfl) ?_
    rcases hD r y hy with hy | ⟨rfl, rfl⟩
    · exact hk.1.2.1.2.1 r hr' y hy
    · have := hpre.anchorOrder
      rwa [S3.pframe_congr (s' := s.view c) (s := s.flat) rfl r] at this
  · intro r hr x' y hy ya hhq
    have hr' := (set_usable_iff (t := dependEff (s.view c) q x) rfl rfl).1 hr
    rw [S3.pframe_congr (s' := (dependEffC s c q x).flat) (s := s.flat) rfl r]
    exact effAnchorOKC_skel (t := dependEff (s.view c) q x) hk.1.1.2 (skel_of_A rfl) rfl
      (fun _ _ _ => Iff.rfl) (hk.1.2.2.1 r hr' x' y hy ya hhq)

/-! ## O8 `store` re-indexed (Spec 1 §65) -/

section Store

variable {t : S3} {a p : Nat} {y : Authority}

/-- The effect of `store` on an existing authority (Spec 1 §65 `ok` effect; copy of the private
`storeEff_eq` of `Preserve/Small.lean`). -/
theorem storeEff_eq (hy : t.A[a]? = some y) :
    storeEff t a p = { t with
      A := t.A.set a { y with holder := .place p }
      D := fun q => if q = p then t.D p ++ [a] else t.D q
      I := fun l => if l = p then .init else t.I l } := by
  unfold storeEff; rw [hy]

/-- The authorities after `store` (Spec 1 §65 `ok` effect; copy of the private `store_get` of
`Preserve/Small.lean`). -/
theorem store_get (hy : t.A[a]? = some y) (j : Nat) :
    (storeEff t a p).A[j]? = if a = j then some { y with holder := .place p } else t.A[j]? := by
  rw [storeEff_eq hy]; exact set_get (lt_of_getElem? hy)

/-- `store` changes only the holder of `a` (Spec 1 §65 `ok` effect; copy of the private `store_skel`
of `Preserve/Small.lean`). -/
theorem store_skel (hy : t.A[a]? = some y) : SameSkel t (storeEff t a p) := by
  refine ⟨by rw [storeEff_eq hy]; simp, fun j => ?_⟩
  rw [store_get hy]; split
  · subst_vars; simp [hy, skel]
  · rfl

/-- `store` of a derived authority keeps the authorities with no origin (Spec 1 §65.1, §65 `ok`
effect; copy of the private `store_root` of `Preserve/Small.lean`). -/
theorem store_root (hy : t.A[a]? = some y) (ho : y.origin ≠ none) (i : Nat) (z : Authority)
    (hzo : z.origin = none) : (storeEff t a p).A[i]? = some z ↔ t.A[i]? = some z := by
  rw [store_get hy]; split
  · subst_vars; rw [hy]
    constructor <;> intro h <;> cases h <;> exact absurd hzo ho
  · exact Iff.rfl

/-- The anchors after `store(a, p)` (Spec 1 §65 `ok` effect; copy of the private `store_D` of
`Preserve/Small.lean`). -/
theorem store_D (hy : t.A[a]? = some y) {q x : Nat} (hx : x ∈ (storeEff t a p).D q) :
    x ∈ t.D q ∨ (q = p ∧ x = a) := by
  rw [storeEff_eq hy] at hx; simp only at hx
  split at hx
  · rename_i hqp
    rcases List.mem_append.1 hx with hx | hx
    · exact .inl (hqp ▸ hx)
    · exact .inr ⟨hqp, List.mem_singleton.1 hx⟩
  · exact .inl hx

end Store

/-- `store` executed by a context preserves the re-indexed invariant (Spec 1 §57, §65; WC3 C2,
C20): the stored authority is derived and keeps its skeleton; §65.4 and §65.5 hold on
`ancestorC`. -/
theorem store_preserves {s : SC} {c a p : Nat} (hk : KInvCA s) (hpre : StorePreC s c a p) :
    KInvCA (storeEffC s c a p) := by
  obtain ⟨hw, hb, hd, hc, hh⟩ := view_facts hk c
  have hfr := hk.1.1.1
  obtain ⟨y, hy, ya, ho, -⟩ : ∃ y, (s.view c).A[a]? = some y ∧ y.active = true ∧
      y.origin ≠ none ∧ y.holder = .frame (s.view c).top := by
    have h := hpre.derivedHeld
    unfold OptP at h; split at h
    · rename_i y hy; exact ⟨y, hy, h⟩
    · exact h.elim
  have hP : (storeEff (s.view c) a p).P = s.P := by rw [storeEff_eq hy]; rfl
  have hF : (storeEff (s.view c) a p).F = (s.view c).F := by rw [storeEff_eq hy]
  have hn : (storeEff (s.view c) a p).nF = s.nF := by rw [storeEff_eq hy]; rfl
  have hdd : (storeEff (s.view c) a p).dead = s.dead := by rw [storeEff_eq hy]; rfl
  have sk := store_skel (p := p) hy
  have hw' : WF3 (storeEff (s.view c) a p) :=
    wf3_skel hw sk hP hF hn hdd (store_root hy ho) fun j z hz za => by
      rw [store_get hy] at hz; split at hz
      · cases hz; exact hpre.usable
      · exact hw.holders j z hz za
  have hb' : Inv3base (storeEff (s.view c) a p) :=
    inv3base_skel hb sk hP hF hdd fun q hq x hx => by
      rcases store_D hy hx with hx | ⟨-, rfl⟩
      · exact hb.2.2.1 q hq x hx
      · exact ⟨y, hy, ya⟩
  have hh' : HeldAnchored (storeEff (s.view c) a p) := by
    rw [storeEff_eq hy]
    refine heldAnchored_of_step hw hh fun x y' q hy' ya' ho' hhq => ?_
    simp only [set_get (lt_of_getElem? hy)] at hy'
    split at hy'
    · rename_i e; subst e; cases hy'
      cases hhq
      exact .inl (by simp)
    · refine .inr ⟨y', hy', ya', ho', hhq, fun _ hx => ?_⟩
      simp only
      split
      · rename_i e; subst e; exact List.mem_append_left _ hx
      · exact hx
  have hmem : ∀ f, f ∈ (storeEff (s.view c) a p).F ↔ f ∈ s.frames := fun f => by
    rw [hF]; exact SC.mem_view_F
  have sk' : SameSkel s.flat (storeEff (s.view c) a p) := sk
  refine kInvCA_of (framesC_set hfr hn)
    (flat_facts rfl hmem hfr.nodup (frames_ne (s := s) hfr) hw' hb'
      (noDangling_skel hd sk hP hF hdd)
      (rootHeldConv_of hc hP fun i z hzo hz => (store_root hy ho i z hzo).1 hz) hh') ?_
    hpre.anchorOrderHeld
  intro q hq x hx
  have hq' := (set_usable_iff (t := storeEff (s.view c) a p) hP hdd).1 hq
  rw [S3.pframe_congr (s' := (storeEffC s c a p).flat) (s := s.flat) hP q]
  refine effAnchorOKC_skel hk.1.1.2 sk' hP (store_root hy ho) ?_
  rcases store_D hy hx with hx | ⟨rfl, rfl⟩
  · exact hk.1.2.1.2.1 q hq' x hx
  · have := hpre.anchorOrder
    rwa [S3.pframe_congr (s' := s.view c) (s := s.flat) rfl q] at this

/-! ## `deriveSync` (WC3 C15) -/

/-- `deriveSync` preserves the re-indexed invariant (Spec 1 §57, §60; WC3 C15, C20); the own mode
of `guarded` is the clause C15.1 of `DeriveSyncPre`. -/
theorem deriveSync_preserves {R : Type} {kc : KC R} {r : R} {s : SC} {c g : Nat} (hk : KInvCA s)
    (hpre : DeriveSyncPre kc r s c g) : KInvCA (deriveSyncEff s c g) := by
  obtain ⟨hw, hb, hd, hc, hh⟩ := view_facts hk c
  obtain ⟨x, hx, xa⟩ := hpre.active
  have hxm : Mode.modify.le x.mode := by
    have hm := hpre.mode
    rw [hx] at hm; exact hm
  have hafp : (s.view c).afp g = x.footprint := by simp [S3.afp, hx]
  have hbase := addAuth_preserves hw hb hx xa hxm
    (fun p hp => by rw [← hafp]; exact hp) hpre.modeOK
    (hd := .frame (s.view c).top) hpre.frameLive
  have hd' : NoDangling (deriveEff (s.view c) g ((s.view c).afp g) .modify) := by
    intro j z hz za q hq l hl hlz
    have hU := S3.Usable.congr (q := q) (s := s.view c)
      (s' := deriveEff (s.view c) g ((s.view c).afp g) .modify) rfl rfl rfl
    rcases addAuth_get hz with ⟨-, hz⟩ | ⟨-, rfl⟩
    · exact hd j z hz za q (fun hu => hq (hU.2 hu)) l hl hlz
    · rw [hafp] at hlz
      exact hd g x hx xa q (fun hu => hq (hU.2 hu)) l hl hlz
  have hc' : RootHeldConv (deriveEff (s.view c) g ((s.view c).afp g) .modify) :=
    rootHeldConv_of hc rfl fun i z hzo hz => by
      rcases addAuth_get hz with ⟨-, hz⟩ | ⟨-, rfl⟩
      · exact hz
      · cases hzo
  have hh' : HeldAnchored (deriveEff (s.view c) g ((s.view c).afp g) .modify) :=
    heldAnchored_of_step hw hh fun x' y q hy ya ho hhq => by
      rcases addAuth_get hy with ⟨-, hy⟩ | ⟨-, rfl⟩
      · exact .inr ⟨y, hy, ya, ho, hhq, fun _ h => h⟩
      · cases hhq
  exact set_preserves hk rfl rfl
    (skelV_append fun y hy => by rw [List.mem_singleton.1 hy]; exact ⟨_, rfl⟩)
    hbase.1 hbase.2 hd' hc' hh'

/-! ## The effect of O6 on kernel components (Spec 1 §72), shared by `enterFrame` and `spawn` -/

section EnterS3

open Ern.MemoryModel.Access.Frames

variable {s : S3} {ps : List Nat} {ls : LocalShape}

/-- Parameters of O6 (Spec 1 §72.1; WC3 C4.3). -/
def ParamsOK (s : S3) (ps : List Nat) : Prop :=
  ∀ a ∈ ps, OptP (s.A[a]?) (fun y => y.active = true ∧ y.holder = .frame s.top ∧
    y.origin ≠ none) False

/-- §49.7 after the effect of O6 (Spec 1 §72; the proof of `Frames.enter_rootHeld`, which uses
only §72.1 and §72.2). -/
theorem enter_rootHeld' (hwf : WF3 s) (hpar : ParamsOK s ps) (hsh : ShapeOK s.P.length ls.toShape) :
    RootHeld (enterEff s ps ls) := by
  intro r hrp hur
  by_cases hr : r < s.P.length
  · have hrp0 : RootPlace s.P r := ⟨hr, by rw [← enter_parentOf_lt hr]; exact hrp.2⟩
    obtain ⟨i, z, pr, hz, za, zo, zm, hpr, hzh, hzf⟩ :=
      hwf.rootHeld r hrp0 (enter_usable_back hwf hur hr)
    have hni : i ∉ ps := fun hm => by
      have h2 := hpar i hm
      simp only [OptP, hz] at h2; exact h2.2.2 zo
    refine ⟨i, z, pr, by rw [enter_lt (lt_of_getElem? hz), hz]; simp [hni], za, zo, zm,
      by show (enterP s ls)[r]? = _; rw [enterP_lt hr]; exact hpr, hzh, fun l => ?_⟩
    show _ ↔ l ∈ footprint (enterP s ls) r
    rw [enter_footprint_old hsh hr]; exact hzf l
  · have hrl := hrp.1
    rw [show (enterEff s ps ls).P = enterP s ls from rfl, enterP_len] at hrl
    obtain ⟨k, rfl⟩ : ∃ k, r = s.P.length + k := ⟨r - s.P.length, by omega⟩
    have hk : k < ls.length := by omega
    have hn : (ls.toShape[k]?).bind (·.1) = none := by
      have := hrp.2
      rw [show (enterEff s ps ls).P = enterP s ls from rfl, enter_parentOf_new hk] at this
      exact this
    obtain ⟨j, hj⟩ := append_map_get
      (mapI (fun j y => if j ∈ ps then { y with holder := .frame s.nF } else y) 0 s.A)
      (fun i => (⟨.modify, none, footprint (enterP s ls) (s.P.length + i),
        shapeOwner ls.toShape (.frame s.nF) i, true⟩ : Authority)) (mem_rootIdx hk hn)
    exact ⟨_, _, _, hj, rfl, rfl, rfl, enterP_new hk, shapeOwner_toShape _ _ _,
      fun _ => Iff.rfl⟩

/-- `WF3` after the effect of O6 (Spec 1 §49, §72; the proof of `Frames.enter_wf`, which uses
only §72.1 and §72.2). -/
theorem enter_wf' (hwf : WF3 s) (hpar : ParamsOK s ps) (hsh : ShapeOK s.P.length ls.toShape) :
    WF3 (enterEff s ps ls) := by
  have live : ∀ (hd : Holder), HolderLive s hd → HolderLive (enterEff s ps ls) hd := by
    intro hd hl; cases hd with
    | frame f => exact List.mem_cons_of_mem _ hl
    | place p => exact enter_usable_old hl
  refine ⟨⟨by simp [enterEff], ?_, ?_⟩, ?_, ⟨?_, ?_, fun q hq => hq.frameOf⟩, ?_, ?_,
    enter_rootChain hwf hsh, enter_rootHeld' hwf hpar hsh, ?_⟩
  · exact List.nodup_cons.2 ⟨fun hm => Nat.lt_irrefl _ (hwf.frames.2.2 _ hm), hwf.frames.2.1⟩
  · intro f hf; rcases List.mem_cons.1 hf with rfl | hf
    · exact Nat.lt_succ_self _
    · exact Nat.lt_succ_of_lt (hwf.frames.2.2 f hf)
  · intro q pl r hq hp
    rcases enterP_get hq with ⟨hq', hq''⟩ | ⟨hq', i, hi, rfl, rfl⟩
    · obtain ⟨pr, hpr, hlt, ho, hd⟩ := hwf.places q pl r hq'' hp
      refine ⟨pr, by show (enterP s ls)[r]? = _; rw [enterP_lt (by omega)]; exact hpr, hlt, ho, ?_⟩
      simp [enterEff, show ¬ s.P.length ≤ r by omega, show ¬ s.P.length ≤ q by omega, hd]
    · have h1 := shape_parent hsh hi hp
      have hri : r - s.P.length < ls.length := by omega
      have hr' := enterP_new (s := s) (ls := ls) hri
      rw [show s.P.length + (r - s.P.length) = r by omega] at hr'
      exact ⟨_, hr', by omega, rfl, by simp [enterEff, show s.P.length ≤ r by omega]⟩
  · intro q pl f hq ho
    rcases enterP_get hq with ⟨-, hq'⟩ | ⟨-, i, -, -, rfl⟩
    · exact Nat.lt_succ_of_lt (hwf.owners.1 q pl f hq' ho)
    · cases ho; exact Nat.lt_succ_self _
  · intro q pl o hq ho
    rcases enterP_get hq with ⟨-, hq'⟩ | ⟨-, i, -, -, rfl⟩
    · have := hwf.owners.2.1 q pl o hq' ho
      show o < (enterP s ls).length; rw [enterP_len]; omega
    · cases ho
  · intro a y hy l hl
    rcases enter_get hy with ⟨-, y₀, hy₀, rfl⟩ | ⟨-, i, -, rfl⟩
    · obtain ⟨hlt, hleaf⟩ := hwf.footprints a y₀ hy₀ l (by split at hl <;> exact hl)
      exact ⟨by show l < (enterP s ls).length; rw [enterP_len]; omega,
        (enter_isLeaf_old hsh hlt).2 hleaf⟩
    · exact ⟨(mem_footprint.1 hl).1, (mem_footprint.1 hl).2.1⟩
  · intro b y a hb ho
    rcases enter_get hb with ⟨-, y₀, hy₀, rfl⟩ | ⟨-, _, -, rfl⟩
    · exact hwf.origins b y₀ a hy₀ (by split at ho <;> exact ho)
    · cases ho
  · intro a y hy ya
    rcases enter_get hy with ⟨-, y₀, hy₀, rfl⟩ | ⟨-, i, -, rfl⟩
    · have ya₀ : y₀.active = true := by split at ya <;> exact ya
      split
      · exact (List.mem_cons_self .. : s.nF ∈ s.nF :: s.F)
      · exact live _ (hwf.holders a y₀ hy₀ ya₀)
    · exact (List.mem_cons_self .. : s.nF ∈ s.nF :: s.F)

/-- `NoDangling` after the effect of O6 (Spec 1 §54, §72; the proof of `Frames.enter_noDangling`,
which uses only §72.2). -/
theorem enter_noDangling' (hwf : WF3 s) (hnd : NoDangling s) (hsh : ShapeOK s.P.length ls.toShape) :
    NoDangling (enterEff s ps ls) := by
  intro j z hz za q hq l hl hlz
  obtain ⟨hlP, -, hlq⟩ := mem_footprint.1 hl
  have hql : q ≤ l := partOf_le hlq
  rcases enter_get hz with ⟨-, y, hy, rfl⟩ | ⟨-, i, -, rfl⟩
  · have hly : l ∈ y.footprint := by split at hlz <;> exact hlz
    have ya : y.active = true := by split at za <;> exact za
    have hqo : q < s.P.length := Nat.lt_of_le_of_lt hql (hwf.footprints j y hy l hly).1
    exact hnd j y hy ya q (fun hu => hq (enter_usable_old hu)) l
      ((enter_footprint_old hsh hqo l).1 hl) hly
  · have hge : s.P.length ≤ l := enter_root_fp_ge hlz
    by_cases hqo : q < s.P.length
    · have := (mem_footprint.1 ((enter_footprint_old hsh hqo l).1 hl)).1; omega
    · have hlP' : l < (enterP s ls).length := hlP
      rw [enterP_len] at hlP'
      have hu := enter_usable_new (s := s) (ps := ps) (ls := ls) (i := q - s.P.length) (by omega)
      rw [show s.P.length + (q - s.P.length) = q by omega] at hu
      exact hq hu

/-- `RootHeldConv` after the effect of O6 (Spec 1 §40, §49.7, §72; the proof of
`Frames.enter_rootHeldConv`, which uses only §72.1). -/
theorem enter_rootHeldConv' (hwf : WF3 s) (hpar : ParamsOK s ps) (hr : RootHeldConv s) :
    RootHeldConv (enterEff s ps ls) := by
  intro x z l r hx ho hl hrp hlr
  rcases enter_get hx with ⟨-, z₀, hz₀, rfl⟩ | ⟨-, i, hi, rfl⟩
  · have ho' : z₀.origin = none := by split at ho <;> exact ho
    have hl' : l ∈ z₀.footprint := by split at hl <;> exact hl
    have hnp : x ∉ ps := fun hp => by
      have := hpar x hp; simp only [OptP, hz₀] at this; exact this.2.2 ho'
    have hlt := (hwf.footprints x z₀ hz₀ l hl').1
    have hlr' : partOf s.P l r := (enter_partOf_old hlt).1 hlr
    have hrl : r < s.P.length := Nat.lt_of_le_of_lt (partOf_le hlr') hlt
    have hrp' : RootPlace s.P r := ⟨hrl, by rw [← enter_parentOf_lt hrl]; exact hrp.2⟩
    obtain ⟨pr, hpr, hh⟩ := hr x z₀ l r hz₀ ho' hl' hrp' hlr'
    exact ⟨pr, by show (enterP s ls)[r]? = _; rw [enterP_lt hrl]; exact hpr, by simp [hnp, hh]⟩
  · obtain ⟨hil, hin⟩ := rootIdx_mem hi
    have hroot : RootPlace (enterEff s ps ls).P (s.P.length + i) :=
      ⟨by show s.P.length + i < (enterP s ls).length; rw [enterP_len]; omega,
        by show parentOf (enterP s ls) (s.P.length + i) = none
           rw [enter_parentOf_new hil]; exact hin⟩
    obtain rfl := rootOf_unique hrp hroot hlr (mem_footprint.1 hl).2.2
    exact ⟨_, enterP_new hil, rfl⟩

/-- An element of an appended list comes from one of the two parts (Spec 1 §42; copy of the private
`getElem?_append_cases` of `Access/Main.lean`). -/
theorem getElem?_append_cases {α : Type} {l E : List α} {x : Nat} {y : α}
    (h : (l ++ E)[x]? = some y) : l[x]? = some y ∨ y ∈ E := by
  by_cases hx : x < l.length
  · rw [List.getElem?_append_left hx] at h; exact .inl h
  · rw [List.getElem?_append_right (by omega)] at h; exact .inr (List.mem_of_getElem? h)

/-- `HeldAnchored` after the effect of O6 (Spec 1 §44, §72; the `enter` case of
`op_preserves_heldAnchored`, which uses no precondition). -/
theorem enter_heldAnchored' (hwf : WF3 s) (hh : HeldAnchored s) :
    HeldAnchored (enterEff s ps ls) := by
  refine heldAnchored_of_step hwf hh fun x y q hy ya ho hhq => ?_
  rcases getElem?_append_cases hy with hy | hy
  · rw [getElem?_mapI] at hy
    obtain ⟨y₀, hy₀, e⟩ := Option.map_eq_some_iff.1 hy
    split at e
    · subst e; cases hhq
    · subst e
      refine .inr ⟨y₀, hy₀, ya, ho, hhq, fun hu hx => ?_⟩
      show x ∈ (if s.P.length ≤ q then [] else s.D q)
      split
      · exact absurd hu.lt (Nat.not_lt.2 ‹_›)
      · exact hx
  · obtain ⟨r, -, rfl⟩ := List.mem_map.1 hy; exact absurd rfl ho

end EnterS3

/-! ## Adding a fresh frame (WC3 C3, C4; Spec 1 §72) -/

/-- Frame structure after adding the fresh frame `nF` whose parent is the live frame `top`, the
other parent links unchanged (WC3 C3; Spec 1 §72 `ok` effect, WC3 C4 effect). -/
structure Push (s s' : SC) (top : Nat) : Prop where
  mem : ∀ f, f ∈ s'.frames ↔ f = s.nF ∨ f ∈ s.frames
  nodup : s'.frames.Nodup
  parOld : ∀ j, j ≠ s.nF → s'.parC j = s.parC j
  parNew : s'.parC s.nF = some top
  top : top ∈ s.frames
  nF : s'.nF = s.nF + 1
  initial : OptP (s'.C[0]?) (fun x => x.life = .live ∧ x.parent = none) False
  nonempty : ∀ c, s'.Live c → s'.stk c ≠ []
  rooted : ∀ c, c ≠ 0 → s'.Live c → s'.ctxParent c ≠ none

/-- `FramesC` after adding a fresh frame (WC3 C3). -/
theorem Push.framesC {s s' : SC} {top : Nat} (hfr : FramesC s) (h : Push s s' top) :
    FramesC s' where
  initial := h.initial
  nonempty := h.nonempty
  nodup := h.nodup
  bound := fun f hf => by
    rw [h.nF]
    rcases (h.mem f).1 hf with rfl | hf
    · exact Nat.lt_succ_self _
    · exact Nat.lt_succ_of_lt (hfr.bound f hf)
  rooted := h.rooted
  parent := fun f hf g hg => by
    by_cases e : f = s.nF
    · subst e; rw [h.parNew] at hg; cases hg
      exact ⟨(h.mem _).2 (.inr h.top), hfr.bound _ h.top⟩
    · rw [h.parOld f e] at hg
      have hf' : f ∈ s.frames := ((h.mem f).1 hf).resolve_left e
      obtain ⟨hg', hlt⟩ := hfr.parent f hf' g hg
      exact ⟨(h.mem g).2 (.inr hg'), hlt⟩

/-- Adding a fresh frame keeps the extended ancestry of the live frames (WC3 C3). -/
theorem Push.ancestorC {s s' : SC} {top : Nat} (hfr : FramesC s) (h : Push s s' top) {g f : Nat}
    (hf : s.ancestorC g f) : s'.ancestorC g f := by
  refine ⟨(h.mem f).2 (.inr hf.1), ?_⟩
  have hfn : f < s.nF := hfr.bound f hf.1
  rw [chain_congr (org := s'.parC) (org' := s.parC) fun j hj => h.parOld j (by omega)]
  exact hf.2

/-- The re-indexed invariant after the effect of O6 on the view of `c` with a fresh frame added
to the frame structure (Spec 1 §57, §72; WC3 C3, C4, C20): `WF3`, `I1`–`I4`, `NoDangling` and the
auxiliaries come from the Spec 1 effect; `AnchorOrderC` from the unchanged ancestry of existing
frames (mirrors `Frames.enter_anchorOrder`); `AnchorOrderHeldC` is a hypothesis (§72.4, WC3
C4.5). -/
theorem push_preserves {s : SC} {c top : Nat} {ps : List Nat} {ls : LocalShape}
    {C' : List Ctx} (hk : KInvCA s) (hpar : ParamsOK (s.view c) ps)
    (hsh : ShapeOK s.P.length ls.toShape)
    (hpush : Push s { s.set (enterEff (s.view c) ps ls) with C := C' } top)
    (haoh : AnchorOrderHeldC { s.set (enterEff (s.view c) ps ls) with C := C' }) :
    KInvCA { s.set (enterEff (s.view c) ps ls) with C := C' } := by
  obtain ⟨hw, hb, hd, hc, hh⟩ := view_facts hk c
  have hfr := hk.1.1.1
  have hmem : ∀ f, f ∈ (enterEff (s.view c) ps ls).F ↔
      f ∈ ({ s.set (enterEff (s.view c) ps ls) with C := C' } : SC).frames := fun f => by
    rw [hpush.mem]
    show f ∈ s.nF :: (s.view c).F ↔ _
    rw [List.mem_cons, SC.mem_view_F]
  have hne : ({ s.set (enterEff (s.view c) ps ls) with C := C' } : SC).frames ≠ [] := fun he => by
    have := (hpush.mem s.nF).2 (.inl rfl); rw [he] at this; cases this
  refine kInvCA_of (hpush.framesC hfr)
    (flat_facts rfl hmem hpush.nodup hne (enter_wf' hw hpar hsh) (Frames.enter_inv3base hw hb)
      (enter_noDangling' hw hd hsh) (enter_rootHeldConv' hw hpar hc) (enter_heldAnchored' hw hh))
    ?_ haoh
  intro q hq x hx
  have hqt : (enterEff (s.view c) ps ls).Usable q :=
    (usable_mem_congr (t := enterEff (s.view c) ps ls) (fun f => (hmem f).symm)).1 hq
  change x ∈ (if (s.view c).P.length ≤ q then [] else (s.view c).D q) at hx
  by_cases hlt : q < (s.view c).P.length
  · simp only [show ¬ (s.view c).P.length ≤ q from Nat.not_le.2 hlt, ↓reduceIte] at hx
    have hq0 := Frames.enter_usable_back hw hqt hlt
    have hqf := view_usable_flat hq0
    have hok := hk.1.2.1.2.1 q hqf x hx
    have hxl : x < (s.view c).A.length := by
      obtain ⟨y, hy, -⟩ := hk.1.2.1.1.2.2.1 q hqf x hx; exact lt_of_getElem? hy
    obtain ⟨z, hz⟩ := effAnchorOKC_get hok
    have he : (enterEff (s.view c) ps ls).effAnchor x = (s.view c).effAnchor x :=
      Frames.effAnchor_congr (Frames.enter_ancs_lt hxl)
    have hrl : (s.view c).effAnchor x < (s.view c).A.length :=
      Nat.lt_of_le_of_lt (Frames.effAnchor_le _ x) hxl
    have hz₀ : (s.view c).A[(s.view c).effAnchor x]? = some z := hz
    have hro := Frames.effAnchor_root hw x
    have hnp : (s.view c).effAnchor x ∉ ps := fun hp => by
      have := hpar _ hp; simp only [OptP, hz₀] at this
      exact this.2.2 (by simpa [S3.org, hz₀] using hro)
    have hz' : ({ s.set (enterEff (s.view c) ps ls) with C := C' } : SC).A[
        ({ s.set (enterEff (s.view c) ps ls) with C := C' } : SC).flat.effAnchor x]? = some z := by
      show (enterEff (s.view c) ps ls).A[(enterEff (s.view c) ps ls).effAnchor x]? = some z
      rw [he, Frames.enter_lt hrl, hz₀]; simp [hnp]
    rw [S3.pframe_congr (s' := ({ s.set (enterEff (s.view c) ps ls) with C := C' } : SC).flat)
      (s := enterEff (s.view c) ps ls) rfl q, Frames.enter_pframe_old hw hlt,
      S3.pframe_congr (s' := s.view c) (s := s.flat) rfl q]
    refine effAnchorOKC_of_same hz hz' ?_ (fun g f _ hg => hpush.ancestorC hfr hg) hok
    cases hzh : z.holder with
    | frame f => rfl
    | place p =>
      cases hg : s.flat.pframe p with
      | none =>
        exfalso; unfold EffAnchorOKC at hok; rw [hz] at hok
        simp [OptP, hzh, S3.hframe, hg] at hok
      | some g =>
        show ({ s.set (enterEff (s.view c) ps ls) with C := C' } : SC).flat.pframe p =
          s.flat.pframe p
        rw [S3.pframe_congr (s' := ({ s.set (enterEff (s.view c) ps ls) with C := C' } : SC).flat)
          (s := enterEff (s.view c) ps ls) rfl p,
          Frames.enter_pframe_old hw (q := p) (pframe_iff.1 hg).lt,
          S3.pframe_congr (s' := s.view c) (s := s.flat) rfl p]
  · simp only [show (s.view c).P.length ≤ q from Nat.le_of_not_lt hlt, ↓reduceIte] at hx
    cases hx

/-! ### Lists -/

/-- `List.range` is duplicate-free (local version without classical lemmas). -/
theorem range_nodup (n : Nat) : (List.range n).Nodup :=
  (Frames.range_pairwise_lt n).imp fun h => Nat.ne_of_lt h

/-- `find?` returns the unique member satisfying the predicate. -/
theorem find?_unique {p : Nat → Bool} {c : Nat} : ∀ {l : List Nat}, c ∈ l → p c = true →
    (∀ i ∈ l, p i = true → i = c) → l.find? p = some c
  | a :: l, hc, hp, hu => by
    by_cases ha : p a = true
    · rw [List.find?_cons_of_pos ha, hu a (List.mem_cons_self ..) ha]
    · rw [List.find?_cons_of_neg ha]
      have hc' : c ∈ l := by
        rcases List.mem_cons.1 hc with rfl | hc
        · exact absurd hp ha
        · exact hc
      exact find?_unique hc' hp fun i hi => hu i (List.mem_cons_of_mem _ hi)

/-- `find?` depends only on the predicate on the members. -/
theorem find?_congr_mem {p q : Nat → Bool} : ∀ {l : List Nat}, (∀ i ∈ l, p i = q i) →
    l.find? p = l.find? q
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.find?_cons, h a (List.mem_cons_self ..)]
    rw [find?_congr_mem fun i hi => h i (List.mem_cons_of_mem _ hi)]

/-- `flatMap` depends only on the function on the members. -/
theorem flatMap_congr_mem {f g : Nat → List Nat} : ∀ {l : List Nat}, (∀ i ∈ l, f i = g i) →
    l.flatMap f = l.flatMap g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h a (List.mem_cons_self ..),
      flatMap_congr_mem fun i hi => h i (List.mem_cons_of_mem _ hi)]

/-- Pushing a fresh element on one block of a duplicate-free concatenation keeps it
duplicate-free. -/
theorem nodup_flatMap_push {f g : Nat → List Nat} {c a : Nat}
    (hg : ∀ i, g i = if i = c then a :: f i else f i) :
    ∀ {l : List Nat}, l.Nodup → (l.flatMap f).Nodup → a ∉ l.flatMap f → (l.flatMap g).Nodup
  | [], _, _, _ => List.nodup_nil
  | b :: l, hl, hnd, ha => by
    rw [List.flatMap_cons] at hnd ha ⊢
    obtain ⟨hfb, hfl, hdis⟩ := List.nodup_append.1 hnd
    have hab : a ∉ f b := fun h => ha (List.mem_append_left _ h)
    have hal : a ∉ l.flatMap f := fun h => ha (List.mem_append_right _ h)
    obtain ⟨hbl, hl'⟩ := List.nodup_cons.1 hl
    have hgb : (g b).Nodup := by
      rw [hg b]; split
      · exact List.nodup_cons.2 ⟨hab, hfb⟩
      · exact hfb
    refine List.nodup_append.2 ⟨hgb, nodup_flatMap_push hg hl' hfl hal, fun x hx y hy e => ?_⟩
    subst e
    obtain ⟨i, hi, hyi⟩ := List.mem_flatMap.1 hy
    have hx' : x = a ∧ b = c ∨ x ∈ f b := by
      rw [hg b] at hx; split at hx
      · rename_i hbc; rcases List.mem_cons.1 hx with rfl | hx
        · exact .inl ⟨rfl, hbc⟩
        · exact .inr hx
      · exact .inr hx
    have hy' : x = a ∧ i = c ∨ x ∈ f i := by
      rw [hg i] at hyi; split at hyi
      · rename_i hic; rcases List.mem_cons.1 hyi with rfl | hyi
        · exact .inl ⟨rfl, hic⟩
        · exact .inr hyi
      · exact .inr hyi
    rcases hx' with ⟨rfl, rfl⟩ | hx'
    · rcases hy' with ⟨-, rfl⟩ | hy'
      · exact hbl hi
      · exact hal (List.mem_flatMap.2 ⟨i, hi, hy'⟩)
    · rcases hy' with ⟨rfl, -⟩ | hy'
      · exact hab hx'
      · exact hdis x hx' x (List.mem_flatMap.2 ⟨i, hi, hy'⟩) rfl

/-- `List.modify` read at an index (local version of `List.getElem?_modify`, which uses
`Classical.choice`). -/
theorem getElem?_modify' {α : Type} (f : α → α) :
    ∀ (i : Nat) (l : List α) (j : Nat), (l.modify i f)[j]? = if i = j then (l[j]?).map f else l[j]?
  | _, [], _ => by rw [List.modify_nil]; split <;> rfl
  | 0, a :: l, 0 => by rw [List.modify_zero_cons]; rfl
  | 0, a :: l, j + 1 => by
    rw [List.modify_zero_cons]
    simp only [show ¬ (0 = j + 1) by omega, ↓reduceIte]; rfl
  | i + 1, a :: l, 0 => by
    rw [List.modify_succ_cons]
    simp only [show ¬ (i + 1 = 0) by omega, ↓reduceIte]; rfl
  | i + 1, a :: l, j + 1 => by
    rw [List.modify_succ_cons]
    show (l.modify i f)[j]? = if i + 1 = j + 1 then (l[j]?).map f else l[j]?
    rw [getElem?_modify' f i l j]
    by_cases h : i = j
    · simp only [h, ↓reduceIte]
    · simp only [h, show ¬ (i + 1 = j + 1) by omega, ↓reduceIte]

/-- `List.modify` read at an index, in the form of `List.getElem?_modify`. -/
theorem getElem?_modify'' {α : Type} (f : α → α) (i : Nat) (l : List α) (j : Nat) :
    (l.modify i f)[j]? = (fun a => if i = j then f a else a) <$> l[j]? := by
  rw [getElem?_modify']
  by_cases h : i = j
  · simp only [h, ↓reduceIte]; rfl
  · simp only [h, ↓reduceIte]; cases l[j]? <;> rfl

/-! ### `enterFrame` (Spec 1 §72 re-indexed) -/

/-- A context with a nonempty stack is an existing live context whose stack is its own (WC3
C2). -/
theorem stk_ctx {s : SC} {c : Nat} (hc : s.stk c ≠ []) :
    ∃ x, s.C[c]? = some x ∧ x.life = .live ∧ s.stk c = x.stack := by
  unfold SC.stk at hc ⊢
  split at hc
  · rename_i x hx; split at hc
    · rename_i hl; exact ⟨x, hx, hl, by simp [hl]⟩
    · exact absurd rfl hc
  · exact absurd rfl hc

/-- The stacks after `enterFrame` executed by `c` (Spec 1 §72 re-indexed; WC3 C2). -/
theorem enter_stk {s : SC} {c : Nat} {ps : List Nat} {ls : LocalShape} (hc : s.stk c ≠ [])
    (i : Nat) : (enterEffC s c ps ls).stk i = if i = c then s.nF :: s.stk c else s.stk i := by
  obtain ⟨x, hx, hl, hs⟩ := stk_ctx hc
  unfold SC.stk
  simp only [enterEffC, getElem?_modify'']
  by_cases e : i = c
  · subst e; simp [hx, hl]
  · have e' : ¬ c = i := fun h => e h.symm
    simp only [e, e', ↓reduceIte]
    cases s.C[i]? <;> simp

/-- `Push` for `enterFrame` executed by `c` (Spec 1 §72 re-indexed; WC3 C2, C3). -/
theorem enter_push {s : SC} {c : Nat} {ps : List Nat} {ls : LocalShape} (hfr : FramesC s)
    (hc : s.stk c ≠ []) : Push s (enterEffC s c ps ls) ((s.stk c).headD 0) := by
  obtain ⟨x, hx, hl, hs⟩ := stk_ctx hc
  have hcl : c < s.C.length := lt_of_getElem? hx
  have hlen : (enterEffC s c ps ls).C.length = s.C.length := List.length_modify _ _ _
  have hstk := enter_stk (ps := ps) (ls := ls) hc
  have hnF : s.nF ∉ s.frames := fun h => Nat.lt_irrefl _ (hfr.bound _ h)
  have hfr' : (enterEffC s c ps ls).frames = (List.range s.C.length).flatMap
      (enterEffC s c ps ls).stk := by
    unfold SC.frames; rw [hlen]
  have hC : ∀ i, (enterEffC s c ps ls).C[i]? =
      (s.C[i]?).map fun y => if c = i then { y with stack := s.nF :: y.stack } else y := by
    intro i; simp only [enterEffC, getElem?_modify'']; rfl
  have hlive : ∀ i, (enterEffC s c ps ls).Live i ↔ s.Live i := by
    intro i; unfold SC.Live; rw [hC i]
    cases s.C[i]? with
    | none => exact Iff.rfl
    | some y => simp only [Option.map_some, OptP]; split <;> exact Iff.rfl
  have hpar : ∀ i, (enterEffC s c ps ls).ctxParent i = s.ctxParent i := by
    intro i; unfold SC.ctxParent; rw [hC i]
    cases s.C[i]? with
    | none => rfl
    | some y => simp only [Option.map_some, Option.bind_some]; split <;> rfl
  have hcont : ∀ j, j ≠ s.nF → ∀ i, ((enterEffC s c ps ls).stk i).contains j =
      (s.stk i).contains j := by
    intro j hj i; rw [hstk i]; split
    · rename_i e; subst e; rw [List.contains_cons]
      have : (j == s.nF) = false := by simp [hj]
      rw [this, Bool.false_or]
    · rfl
  have hctx : ∀ j, j ≠ s.nF → (enterEffC s c ps ls).ctxOf j = s.ctxOf j := by
    intro j hj; unfold SC.ctxOf; rw [hlen]
    exact find?_congr_mem fun i _ => hcont j hj i
  obtain ⟨top, rest, hst⟩ := List.exists_cons_of_ne_nil hc
  refine ⟨fun f => ?_, ?_, fun j hj => ?_, ?_, ?_, rfl, ?_, ?_, ?_⟩
  · rw [hfr', SC.mem_frames]
    simp only [List.mem_flatMap, List.mem_range, hstk]
    constructor
    · rintro ⟨i, hi, hf⟩; split at hf
      · rename_i e; subst e
        rcases List.mem_cons.1 hf with rfl | hf
        · exact .inl rfl
        · exact .inr ⟨i, hf⟩
      · exact .inr ⟨i, hf⟩
    · rintro (rfl | ⟨i, hf⟩)
      · exact ⟨c, hcl, by simp⟩
      · have hi : i < s.C.length := by
          rcases Nat.lt_or_ge i s.C.length with h | h
          · exact h
          · simp [SC.stk, List.getElem?_eq_none_iff.2 h] at hf
        refine ⟨i, hi, ?_⟩; split
        · exact List.mem_cons_of_mem _ (by rename_i e; subst e; exact hf)
        · exact hf
  · rw [hfr']
    exact nodup_flatMap_push (f := s.stk) (g := (enterEffC s c ps ls).stk) (c := c) (a := s.nF)
      (fun i => by rw [hstk i]; by_cases e : i = c <;> simp [e])
      (range_nodup _) hfr.nodup hnF
  · unfold SC.parC
    rw [hctx j hj]
    cases hcj : s.ctxOf j with
    | none => rfl
    | some c' =>
      simp only [Option.bind_some]
      rw [hpar c', hstk c']; split
      · rename_i e; subst e; exact parIn_cons_ne (fun e => hj e.symm)
      · rfl
  · unfold SC.parC
    have : (enterEffC s c ps ls).ctxOf s.nF = some c := by
      unfold SC.ctxOf; rw [hlen]
      refine find?_unique (List.mem_range.2 hcl) (by rw [hstk c]; simp) fun i _ hi => ?_
      rw [hstk i] at hi; split at hi
      · rename_i e; exact e
      · exact absurd (List.contains_iff_mem.1 hi) fun h => hnF (SC.mem_frames_of h)
    rw [this]
    simp only [Option.bind_some, hstk c, ↓reduceIte, parIn, hst, List.head?_cons,
      Option.some_or, List.headD_cons]
  · rw [hst]; exact SC.mem_frames_of (by rw [hst]; exact List.mem_cons_self ..)
  · have h0 := hfr.initial
    rw [hC 0]
    unfold OptP at h0 ⊢
    cases e : s.C[0]? with
    | none => rw [e] at h0; exact h0
    | some y => rw [e] at h0; simp only [Option.map_some]; split <;> exact h0
  · intro i hi
    rw [hstk i]; split
    · exact List.cons_ne_nil _ _
    · exact hfr.nonempty i ((hlive i).1 hi)
  · intro i hi hl'
    rw [hpar i]; exact hfr.rooted i hi ((hlive i).1 hl')

/-! ### `spawn` (WC3 C4) -/

/-- The stacks after `spawn` (WC3 C4 effect). -/
theorem spawn_stk {s : SC} {c : Nat} {ps : List Nat} {ls : LocalShape} (i : Nat) :
    (spawnEff s c ps ls).stk i =
      if i < s.C.length then s.stk i else if i = s.C.length then [s.nF] else [] := by
  unfold SC.stk
  simp only [spawnEff]
  by_cases hi : i < s.C.length
  · rw [List.getElem?_append_left hi]; simp [hi]
  · rw [List.getElem?_append_right (Nat.le_of_not_lt hi)]
    by_cases e : i = s.C.length
    · subst e; simp
    · have : i - s.C.length ≠ 0 := by omega
      simp only [hi, e, ↓reduceIte]
      rw [List.getElem?_eq_none_iff.2 (by simp; omega)]

/-- `Push` for `spawn` executed by `c` (WC3 C3, C4). -/
theorem spawn_push {s : SC} {c : Nat} {ps : List Nat} {ls : LocalShape} (hfr : FramesC s)
    (hc : s.stk c ≠ []) : Push s (spawnEff s c ps ls) ((s.stk c).headD 0) := by
  have hlen : (spawnEff s c ps ls).C.length = s.C.length + 1 := by simp [spawnEff]
  have hstk := spawn_stk (s := s) (c := c) (ps := ps) (ls := ls)
  have hnF : s.nF ∉ s.frames := fun h => Nat.lt_irrefl _ (hfr.bound _ h)
  have hlow : ∀ i ∈ List.range s.C.length, (spawnEff s c ps ls).stk i = s.stk i :=
    fun i hi => by rw [hstk i]; simp only [List.mem_range.1 hi, ↓reduceIte]
  have hframes : (spawnEff s c ps ls).frames = s.frames ++ [s.nF] := by
    unfold SC.frames
    rw [hlen, List.range_succ, List.flatMap_append, flatMap_congr_mem hlow]
    simp [hstk]
  have hCl : ∀ i, i < s.C.length → (spawnEff s c ps ls).C[i]? = s.C[i]? := fun i hi => by
    simp only [spawnEff]; rw [List.getElem?_append_left hi]
  have hCn : (spawnEff s c ps ls).C[s.C.length]? = some ⟨[s.nF], .live, (s.stk c).head?⟩ := by
    simp [spawnEff]
  have hCg : ∀ i, s.C.length < i → (spawnEff s c ps ls).C[i]? = none := fun i hi => by
    rw [List.getElem?_eq_none_iff, hlen]; omega
  have hctx : ∀ j, j ≠ s.nF → (spawnEff s c ps ls).ctxOf j = s.ctxOf j := by
    intro j hj; unfold SC.ctxOf
    rw [hlen, List.range_succ, List.find?_append,
      find?_congr_mem (q := fun i => (s.stk i).contains j) fun i hi => by rw [hlow i hi]]
    have : List.find? (fun i => ((spawnEff s c ps ls).stk i).contains j) [s.C.length] = none := by
      simp [hstk, hj]
    rw [this, Option.or_none]
  obtain ⟨top, rest, hst⟩ := List.exists_cons_of_ne_nil hc
  have h0 := hfr.initial
  have hC0 : 0 < s.C.length := by
    unfold OptP at h0; split at h0
    · exact lt_of_getElem? ‹_›
    · exact h0.elim
  refine ⟨fun f => ?_, ?_, fun j hj => ?_, ?_, ?_, rfl, ?_, ?_, ?_⟩
  · rw [hframes, List.mem_append, List.mem_singleton]; exact Or.comm
  · rw [hframes]
    exact List.nodup_append.2 ⟨hfr.nodup, List.nodup_cons.2 ⟨(fun h => nomatch h), List.nodup_nil⟩,
      fun a ha b hb e => by
      rw [List.mem_singleton] at hb; subst hb; subst e; exact hnF ha⟩
  · unfold SC.parC
    rw [hctx j hj]
    cases hcj : s.ctxOf j with
    | none => rfl
    | some c' =>
      have hc' : c' < s.C.length := List.mem_range.1 (List.mem_of_find?_eq_some hcj)
      simp only [Option.bind_some, SC.ctxParent, hCl c' hc', hlow c' (List.mem_range.2 hc')]
  · unfold SC.parC
    have : (spawnEff s c ps ls).ctxOf s.nF = some s.C.length := by
      unfold SC.ctxOf
      rw [hlen, List.range_succ, List.find?_append]
      have hnone : List.find? (fun i => ((spawnEff s c ps ls).stk i).contains s.nF)
          (List.range s.C.length) = none := by
        refine List.find?_eq_none.2 fun i hi h => ?_
        rw [hlow i hi] at h
        exact hnF (SC.mem_frames_of (List.contains_iff_mem.1 h))
      rw [hnone, Option.none_or]
      simp [hstk]
    rw [this]
    simp [SC.ctxParent, hCn, hstk, parIn, hst]
  · exact SC.mem_frames_of (by rw [hst]; exact List.mem_cons_self ..)
  · rw [hCl 0 hC0]; exact h0
  · intro i hi
    rw [hstk i]
    by_cases h1 : i < s.C.length
    · simp only [h1, ↓reduceIte]
      refine hfr.nonempty i ?_
      unfold SC.Live at hi ⊢; rw [hCl i h1] at hi; exact hi
    · simp only [h1, ↓reduceIte]; split
      · exact List.cons_ne_nil _ _
      · rename_i h2
        unfold SC.Live at hi; rw [hCg i (by omega)] at hi; exact hi.elim
  · intro i hi hl'
    by_cases h1 : i < s.C.length
    · unfold SC.Live at hl'; rw [hCl i h1] at hl'
      have := hfr.rooted i hi hl'
      unfold SC.ctxParent at this ⊢; rw [hCl i h1]; exact this
    · by_cases h2 : i = s.C.length
      · subst h2; simp [SC.ctxParent, hCn, hst]
      · unfold SC.Live at hl'; rw [hCg i (by omega)] at hl'; exact hl'.elim

/-! ## O4 `transfer` re-indexed (Spec 1 §63): copies of the private helpers of the Spec 1
proof, with only the clauses of §63 they use -/

section TransferS3

variable {s : S3} {src dst : Nat}

/-- `OptP` with default `False` holds on a present value (Spec 1 §38; copy of the private
`optP_false_iff` of `Preserve/Transfer.lean`). -/
theorem optP_false_iff' {α : Type} {o : Option α} {P : α → Prop} :
    OptP o P False ↔ ∃ y, o = some y ∧ P y := by
  cases o with
  | none => exact ⟨fun h => h.elim, fun ⟨_, h, _⟩ => by cases h⟩
  | some y => exact ⟨fun h => ⟨y, rfl, h⟩, fun ⟨_, h, hy⟩ => by cases h; exact hy⟩

/-- Membership in `movedTo` (Spec 1 §63 `ok` effect, fourth item; copy of the private `mem_movedTo`
of `Preserve/Transfer.lean`). -/
theorem mem_movedTo' {x q : Nat} :
    x ∈ movedTo s src dst q ↔
      ∃ r, partOf s.P r src ∧ corr s.P src dst r = some q ∧ x ∈ s.D r := by
  simp only [movedTo, List.mem_flatMap, List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨r, ⟨-, hr, hc⟩, hx⟩; exact ⟨r, hr, hc, hx⟩
  · rintro ⟨r, hr, hc, hx⟩; exact ⟨r, ⟨hr.1, hr, hc⟩, hx⟩

/-- An anchor of a part of `src` is checked by Spec 1 §63.6 (copy of the private
`mem_movedDeps_part` of `Preserve/Transfer.lean`). -/
theorem mem_movedDeps_part' {r x : Nat} (hr : partOf s.P r src) (hx : x ∈ s.D r) :
    x ∈ movedDeps s src := by
  simp only [movedDeps, List.mem_flatMap, List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨r, ⟨hr.1, .inl hr⟩, hx⟩

/-- Under `WF3`, a part of `dst` is not a part of `src` when their footprints are disjoint (Spec
1 §40, §63.3; copy of the private `not_partOf_src` of `Preserve/Transfer.lean`). -/
theorem not_partOf_src' (hw : WF3 s) {r : Nat} (hdis : ¬ overlap s.P src dst)
    (hr : partOf s.P r dst) : ¬ partOf s.P r src := fun hs => by
  obtain ⟨l, hl⟩ := exists_mem_footprint hw (s.P.length - r + 1) r (by omega) hr.1
  exact hdis ⟨l, footprint_sub hw hs hl, footprint_sub hw hr hl⟩

/-- Spec 1 §49.7 after a transfer of a usable `src` (copy of the private `transfer_rootHeld` of
`Preserve/Transfer.lean`). -/
theorem transfer_rootHeld' (hw : WF3 s) (hsrc : s.Usable src) :
    RootHeld (transferEff s src dst) := by
  intro r hrp hur
  have hrp0 : RootPlace s.P r := by
    simpa only [RootPlace, transfer_len, transfer_parentOf] using hrp
  obtain ⟨i, z, pr, hz, za, zo, zm, hpr, hzh, hzf⟩ :=
    hw.rootHeld r hrp0 (transfer_usable_back hw hsrc hur)
  have hf : ∀ l, l ∈ z.footprint ↔ l ∈ footprint (transferEff s src dst).P r := fun l => by
    rw [transfer_footprint]; exact hzf l
  by_cases hc : heldIn s.P src z.holder
  · have hc' : heldIn s.P src pr.owner := hzh ▸ hc
    exact ⟨i, { z with holder := mvTo s.P src dst z.holder },
      { pr with owner := mvTo s.P src dst pr.owner },
      by rw [transfer_A_get, hz]; simp [hc], za, zo, zm, by rw [transfer_P_get, hpr]; simp [hc'],
      by simp [hzh], hf⟩
  · have hc' : ¬ heldIn s.P src pr.owner := hzh ▸ hc
    exact ⟨i, z, pr, by rw [transfer_A_get, hz]; simp [hc], za, zo, zm,
      by rw [transfer_P_get, hpr]; simp [hc'], hzh, hf⟩

/-- `RootHeldConv` after a transfer (Spec 1 §40, §49.7, §63; copy of the private
`transfer_rootHeldConv` of `Preserve/Transfer.lean`). -/
theorem transfer_rootHeldConv' (hr : RootHeldConv s) : RootHeldConv (transferEff s src dst) := by
  intro x z' l r hx ho hl hrp hlr
  rw [transfer_A_get] at hx
  obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.1 hx
  have ho' : z.origin = none := by split at ho <;> exact ho
  have hl' : l ∈ z.footprint := by split at hl <;> exact hl
  have hrp' : RootPlace s.P r := by
    simpa only [RootPlace, transfer_len, transfer_parentOf] using hrp
  have hlr' : partOf s.P l r := (transfer_partOf s src dst l r).1 hlr
  obtain ⟨pr, hpr, hh⟩ := hr x z l r hz ho' hl' hrp' hlr'
  refine ⟨_, by rw [transfer_P_get, hpr]; rfl, ?_⟩
  by_cases hc : heldIn s.P src pr.owner <;> simp [hc, hh]

/-- `WF3` after a transfer (Spec 1 §49, §63; the proof of the private `transfer_wf3`, which uses
only §63.1 usability and §63.9). -/
theorem transfer_wf3' (hwf : WF3 s) (hsrc : s.Usable src) (hdst : s.Usable dst)
    (hd' : (transferEff s src dst).Usable dst) : WF3 (transferEff s src dst) := by
  have sk := transfer_skel s src dst
  have hdl := hdst.lt
  refine ⟨hwf.frames, ?_, ⟨?_, ?_, fun q hq => hq.frameOf⟩, fun a x hx l hl => ?_,
    sk.origins hwf.origins,
    sk.rootChain hwf.rootChain (transfer_len s src dst) (transfer_parentOf s src dst),
    transfer_rootHeld' hwf hsrc, ?_⟩
  · intro q pl r hq hp
    rw [transfer_P_get] at hq
    cases h' : s.P[q]? with
    | none => rw [h'] at hq; cases hq
    | some pl₀ =>
      rw [h'] at hq; simp only [Option.map_some, Option.some.injEq] at hq; subst hq
      have hp₀ : pl₀.parent = some r := by split at hp <;> exact hp
      obtain ⟨pr, hpr, hlt, ho, hdd⟩ := hwf.places q pl₀ r h' hp₀
      refine ⟨_, by rw [transfer_P_get, hpr]; rfl, hlt, ?_, hdd⟩
      by_cases hc : heldIn s.P src pl₀.owner <;> simp [hc, ho]
  · intro q pl f hq ho
    rw [transfer_P_get] at hq
    cases h' : s.P[q]? with
    | none => rw [h'] at hq; cases hq
    | some pl₀ =>
      rw [h'] at hq; simp only [Option.map_some, Option.some.injEq] at hq; subst hq
      split at ho
      · rename_i hh
        obtain ⟨r', e⟩ := mvTo_place (dst := dst) hh
        simp [e] at ho
      · exact hwf.owners.1 q pl₀ f h' ho
  · intro q pl o hq ho
    rw [transfer_len]; rw [transfer_P_get] at hq
    cases h' : s.P[q]? with
    | none => rw [h'] at hq; cases hq
    | some pl₀ =>
      rw [h'] at hq; simp only [Option.map_some, Option.some.injEq] at hq; subst hq
      split at ho
      · rename_i hh
        obtain ⟨r', e, hr'⟩ := mvTo_part hwf hdl hh
        simp only [e, Holder.place.injEq] at ho; subst ho; exact hr'.1
      · exact hwf.owners.2.1 q pl₀ o h' ho
  · have := sk.footprints hwf.footprints a x hx l hl
    simpa only [isLeaf, transfer_len, transfer_parentOf] using this
  · intro a y hy ya
    rw [transfer_A_get] at hy
    cases h' : s.A[a]? with
    | none => rw [h'] at hy; cases hy
    | some y₀ =>
      rw [h'] at hy; simp only [Option.map_some, Option.some.injEq] at hy; subst hy
      have ya₀ : y₀.active = true := by split at ya <;> exact ya
      have hl := hwf.holders a y₀ h' ya₀
      split
      · rename_i hh
        obtain ⟨r', e, hr'⟩ := mvTo_part hwf hdl hh
        show HolderLive _ (mvTo s.P src dst y₀.holder)
        rw [e]; exact transfer_usable_part hwf hr' hd'
      · cases hh : y₀.holder with
        | frame f => rw [hh] at hl; exact hl
        | place p => rw [hh] at hl; exact transfer_usable_fwd hwf hd' hl

/-- `I1`–`I4` and `NoDangling` after a transfer (Spec 1 §50–§54, §63; the proof of the private
`transfer_inv3` without `AnchorOrder`, using §63.1 usability, §63.6 first half and §63.9). -/
theorem transfer_base' (hwf : WF3 s) (hb : Inv3base s) (hnd : NoDangling s)
    (hsrc : s.Usable src) (hdeps : ∀ x ∈ movedDeps s src, s.Active x)
    (hd' : (transferEff s src dst).Usable dst) :
    Inv3base (transferEff s src dst) ∧ NoDangling (transferEff s src dst) := by
  have sk := transfer_skel s src dst
  obtain ⟨i1, i2, i3, -⟩ := hb
  refine ⟨⟨sk.i1 i1, sk.i2 i2, fun q hq x hx => ?_, i4_always _⟩, ?_⟩
  · have hq' := transfer_usable_back hwf hsrc hq
    refine sk.active.2 ?_
    change x ∈ (if partOf s.P q src then [] else s.D q ++ movedTo s src dst q) at hx
    split at hx
    · simp at hx
    · rcases List.mem_append.1 hx with hx | hx
      · exact i3 q hq' x hx
      · obtain ⟨r, hr, -, hxr⟩ := mem_movedTo'.1 hx
        exact hdeps x (mem_movedDeps_part' hr hxr)
  · intro j y hy ya q hq l hl hly
    rw [transfer_A_get] at hy
    obtain ⟨y₀, hy₀, rfl⟩ := Option.map_eq_some_iff.1 hy
    have ya₀ : y₀.active = true := by split at ya <;> exact ya
    have hly₀ : l ∈ y₀.footprint := by split at hly <;> exact hly
    rw [transfer_footprint] at hl
    exact hnd j y₀ hy₀ ya₀ q (fun hu => hq (transfer_usable_fwd hwf hd' hu)) l hl hly₀

/-- `HeldAnchored` after a transfer (Spec 1 §44, §63; the proof of
`transfer_preserves_heldAnchored`, which uses §63.1 usability, §63.2 and §63.3). -/
theorem transfer_heldAnchored' (hwf : WF3 s) (hheld : HeldAnchored s) (hsrc : s.Usable src)
    (hdst : s.Usable dst) (hsh : SameShape s.P src dst) (hdis : ¬ overlap s.P src dst) :
    HeldAnchored (transferEff s src dst) := by
  intro x y q hy ya ho hh hq
  rw [transfer_A_get] at hy
  obtain ⟨y₀, hy₀, rfl⟩ := Option.map_eq_some_iff.1 hy
  have ya₀ : y₀.active = true := by split at ya <;> exact ya
  have ho₀ : y₀.origin ≠ none := by split at ho <;> exact ho
  by_cases hc : heldIn s.P src y₀.holder
  · simp only [hc, ↓reduceIte] at hh
    cases e : y₀.holder with
    | frame _ => rw [e] at hc; exact hc.elim
    | place r =>
      rw [e] at hc hh
      obtain ⟨r', hcr, -⟩ := optP_false_iff'.1 (hsh.1 r (List.mem_range.2 hc.1) hc)
      simp only [mvTo, hcr, Option.getD_some, Holder.place.injEq] at hh
      subst hh
      have hr' := corr_partOf hwf hdst.lt (r + 1) r r' (Nat.lt_succ_self r) hcr
      have hxr := hheld x y₀ r hy₀ ya₀ ho₀ e
        (usable_of_partOf hwf (r + 1) r src (Nat.lt_succ_self r) hc hsrc)
      change x ∈ (if partOf s.P r' src then [] else s.D r' ++ movedTo s src dst r')
      simp only [not_partOf_src' hwf hdis hr', ↓reduceIte]
      exact List.mem_append_right _ (mem_movedTo'.2 ⟨r, hc, hcr, hxr⟩)
  · simp only [hc, ↓reduceIte] at hh
    have hqs : ¬ partOf s.P q src := by rw [hh] at hc; exact hc
    have hxq := hheld x y₀ q hy₀ ya₀ ho₀ hh (transfer_usable_back hwf hsrc hq)
    change x ∈ (if partOf s.P q src then [] else s.D q ++ movedTo s src dst q)
    simp only [hqs, ↓reduceIte]
    exact List.mem_append_left _ hxq

end TransferS3

/-- `transfer` executed by a context preserves the re-indexed invariant (Spec 1 §57, §63; WC3
C2, C20): §63.6 gives `AnchorOrderC`; `AnchorOrderHeldC` from §63.7 for moved held authorities,
from `AnchorOrderC` and `HeldAnchored` for unmoved derived ones, and from the frame of the
holder for unmoved root authorities (mirrors the private `transfer_anchorOrderHeld`). -/
theorem transfer_preserves {k : K} {s : SC} {c src dst : Nat} (hk : KInvCA s)
    (hpre : TransferPreC k s c src dst) : KInvCA (transferEffC s c src dst) := by
  obtain ⟨hw, hb, hd, hc, hh⟩ := view_facts hk c
  have hfr := hk.1.1.1
  have hw' := transfer_wf3' hw hpre.srcUsable hpre.dstUsable hpre.dstUsableAfter
  obtain ⟨hb', hd'⟩ := transfer_base' hw hb hd hpre.srcUsable hpre.depsValid hpre.dstUsableAfter
  have hh' := transfer_heldAnchored' hw hh hpre.srcUsable hpre.dstUsable hpre.sameShape
    hpre.disjoint
  have hmem : ∀ f, f ∈ (transferEff (s.view c) src dst).F ↔ f ∈ s.frames := fun _ =>
    SC.mem_view_F
  refine kInvCA_of (framesC_set hfr rfl)
    (flat_facts rfl hmem hfr.nodup (frames_ne (s := s) hfr) hw' hb' hd'
      (transfer_rootHeldConv' hc) hh') hpre.anchorOrder ?_
  intro q hq x y hy ya hh₁
  have hqt : (transferEff (s.view c) src dst).Usable q := (set_usable hmem).1 hq
  have hy' := hy
  change (transferEff (s.view c) src dst).A[x]? = some y at hy
  rw [transfer_A_get] at hy
  obtain ⟨y₀, hy₀, rfl⟩ := Option.map_eq_some_iff.1 hy
  have hpq : (transferEffC s c src dst).flat.pframe q = (transferEff (s.view c) src dst).pframe q :=
    S3.pframe_congr (s' := (transferEffC s c src dst).flat) (s := transferEff (s.view c) src dst)
      rfl q
  by_cases hm : AnchorMoves (s.view c) src x
  · have e := hpre.anchorOrderHeld x (List.mem_range.2 (lt_of_getElem? hy₀)) hm q
      (List.mem_range.2 (by rw [← transfer_len (s.view c) src dst]; exact hqt.lt)) hqt
    have hy'' : (transferEff (s.view c) src dst).A[x]? = some _ := hy'
    rw [hy''] at e
    rw [hpq]; exact e ya hh₁
  · have hmv : ¬ HolderMoves (s.view c) src y₀.holder := by
      unfold AnchorMoves at hm; rw [hy₀] at hm; exact hm
    have hnh : ¬ heldIn (s.view c).P src y₀.holder := by
      cases e : y₀.holder with
      | frame g => simp [heldIn]
      | place p => rw [e] at hmv; exact fun h => hmv (.inl h)
    simp only [hnh, ↓reduceIte] at ya hh₁ hy'
    have hqs : ¬ partOf (s.view c).P q src := by rw [hh₁] at hmv; exact fun h => hmv (.inl h)
    cases ho : y₀.origin with
    | none =>
      have horg : (transferEff (s.view c) src dst).org x = none := by
        simp [S3.org, show (transferEff (s.view c) src dst).A[x]? = some y₀ from hy', ho]
      have hex : (transferEffC s c src dst).flat.effAnchor x = x := by
        show (transferEff (s.view c) src dst).effAnchor x = x
        simp [S3.effAnchor, S3.ancs, chain_none horg]
      obtain ⟨f, hf, hfF⟩ := hq.frameOf
      unfold EffAnchorOKC
      rw [hex, hy', pframe_iff.2 hf]
      simp only [OptP, hh₁, S3.hframe, pframe_iff.2 hf]
      exact ⟨hfF, .inl rfl⟩
    | some o =>
      have hxq := hh x y₀ q hy₀ ya (by rw [ho]; exact fun h => by cases h) hh₁
        (transfer_usable_back hw hpre.srcUsable hqt)
      have hxq' : x ∈ (transferEffC s c src dst).D q := by
        change x ∈ (if partOf (s.view c).P q src then [] else
          (s.view c).D q ++ movedTo (s.view c) src dst q)
        simp only [hqs, ↓reduceIte]; exact List.mem_append_left _ hxq
      exact hpre.anchorOrder q hq x hxq'

end PreservationAux

open PreservationAux

/-! ## Theorem 2 (except `exitFrameC` and `terminate`) -/

/-- Theorem 2 (WC3 C20, C23; Spec 1 §57 re-indexed): every inherited operation O1–O16 other than
O7, executed by a context with an `ok` outcome, preserves `KInvC` with the auxiliaries `KAux` and
`HeldAnchored` on the flat state, under `DDSound` (Spec 1 §80, used by `split`). Fragment: the
concurrent kernel without synchronization; O7 (`exitFrameC`) is not covered here. -/
theorem opStepC_preservesC {k : K} (hdd : DDSound k) {s s' : SC} {c : Nat} {op : KernelOp}
    (hk : KInvCA s) (hnx : op ≠ .exit) (h : opStepC k op c s (.ok s')) : KInvCA s' := by
  cases op with
  | exit => exact absurd rfl hnx
  | transfer src dst =>
    obtain ⟨-, h⟩ := h; obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
    exact transfer_preserves hk hpre
  | depend q x =>
    obtain ⟨-, h⟩ := h; obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
    exact depend_preserves hk hpre
  | store a p =>
    obtain ⟨-, h⟩ := h; obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
    exact store_preserves hk hpre
  | enter ps ls =>
    obtain ⟨-, h⟩ := h; obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
    exact push_preserves hk hpre.params hpre.localsOK (enter_push hk.1.1.1 hpre.callerLive)
      hpre.anchorOrderHeld
  | derive | split | release | read | write | writeShared | pin | unpin | endUse | free | alloc =>
    obtain ⟨-, o₃, hR, ho⟩ := h
    cases o₃ with
    | ok t =>
      cases ho
      exact viewOp_preserves hdd hk hR (by simp) (by simp) (by simp) (by simp) (by simp)
    | reject => cases ho
    | fail => cases ho

/-- Theorem 2 (WC3 C4, C20, C23): `spawn` (with the preconditions `SpawnPre`) preserves `KInvC`
with the auxiliaries on the flat state: the new context has the fresh frame `nF`, child of the
creating frame; the kernel effect is that of Spec 1 §72. -/
theorem spawn_preservesC {s s' : SC} {c : Nat} {ps : List Nat} {ls : LocalShape}
    (hk : KInvCA s) (h : SpawnStep s c ps ls (.ok s')) : KInvCA s' := by
  obtain ⟨-, h⟩ := h; obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  exact push_preserves hk hpre.params hpre.localsOK (spawn_push hk.1.1.1 hpre.creatorLive)
    hpre.anchorOrderHeld

/-- Theorem 2 (WC3 C8, C20): `join` leaves the state unchanged, hence preserves the invariant. -/
theorem join_preservesC {s s' : SC} {c d : Nat} (hk : KInvCA s) (h : JoinStep s c d (.ok s')) :
    KInvCA s' := by
  cases h; exact hk

/-- Theorem 2 (WC3 C15, C20, C23) for `deriveSync`, for every contract `K_C` and registry: the
own mode of `guarded` is the clause C15.1 of `DeriveSyncPre`. -/
theorem deriveSync_preservesC {R : Type} {kc : KC R} {r : R} {s s' : SC} {c g : Nat}
    (hk : KInvCA s) (h : DeriveSyncStep kc r s c g (.ok s')) : KInvCA s' := by
  obtain ⟨-, h⟩ := h; obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  exact deriveSync_preserves hk hpre

namespace DeriveSyncWitness

/-- A contract `K_C` whose `SyncAuthorized` always holds, on a trivial registry (test contract,
Spec 1 `Examples.K0` for `K`). -/
def kcTrue : KC Unit := { Examples.K0 with SyncAuthorized := fun _ _ _ _ => True }

/-- Decidability of `kcTrue.SyncAuthorized`. -/
instance (r : Unit) (s : SC) (g f : Nat) : Decidable (kcTrue.SyncAuthorized r s g f) :=
  inferInstanceAs (Decidable True)

/-- The single-context state after `derive(0, [], Observe)` from the statics of Spec 1
`Examples.st`: authority 3 is an active `Observe` derivative of root 0 with an empty footprint,
held by frame 0. -/
def wd : SC := SC.ofS3 (deriveEff Examples.s0 0 [] .observe)

end DeriveSyncWitness

open DeriveSyncWitness in
/-- WC3 C15.1: `deriveSync` from the active `Observe` authority 3 with an empty footprint is
rejected, even with a `SyncAuthorized` that always holds (the milestone-1 counterexample
`deriveSync_breaks_i2`, whose `ok` step created a `Modify` derivative of an `Observe` authority). -/
theorem deriveSync_observe_rejected :
    ¬ DeriveSyncPre kcTrue () wd 0 3 ∧ DeriveSyncStep kcTrue () wd 0 3 .reject :=
  ⟨by decide, by decide, .reject (by decide)⟩

open DeriveSyncWitness in
/-- Positive twin of `deriveSync_observe_rejected` (WC3 C15): in the same state, `deriveSync` from
the root `Modify` authority 0 is `ok`. -/
theorem deriveSync_modify_ok :
    DeriveSyncStep kcTrue () wd 0 0 (.ok (deriveSyncEff wd 0 0)) := ⟨by decide, .ok (by decide)⟩

/-- WC3 C15.1: the statement of the milestone-1 counterexample `deriveSync_breaks_i2` is refuted,
for every contract `K_C` and registry: an `ok` step of `deriveSync` from a state satisfying
`KInvCA` keeps `I2` (Spec 1 §51). -/
theorem deriveSync_breaks_i2_false {R : Type} (c g : Nat) :
    ¬ ∃ (kc : KC R) (r : R) (s s' : SC), KInvCA s ∧ DeriveSyncStep kc r s c g (.ok s') ∧
      ¬ I2 s'.flat := by
  rintro ⟨kc, r, s, s', hk, h, hi⟩
  exact hi (deriveSync_preservesC hk h).1.2.1.1.2.1

end Ern.Concurrency
