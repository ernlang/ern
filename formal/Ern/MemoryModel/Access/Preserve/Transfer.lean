import Ern.MemoryModel.Access.Preserve.Common

/-!
# Access kernel: `transfer` (O4, §63)

Properties of `transfer` (§63 of `specs/ERN_Memory_Model_Specification_v0.1.md`), its
preservation of the kernel invariant `KInv` (§57), of the auxiliary `KAux`
(`transfer_preserves_kAux`), of the auxiliary `HeldAnchored` (`transfer_preserves_heldAnchored`)
and of `I5` (`transfer_preserves_i5`).

* With §63.9 (the destination is usable in the resulting state), `WF3`, `Inv3` and `NoOrphan` are
  preserved (`transfer_preserves_wf3_inv3`). `AnchorOrderHeld` needs more: §63.7 constrains only
  the moved held authorities, and an authority held outside the value whose effective anchor
  moves with it escapes the check (`transfer_preserves_of_dst_usable_fails`, on a state that is not
  built by kernel steps). With the auxiliary `HeldAnchored` (not a clause of §57), `KInv` is
  preserved (`transfer_preserves`).
* A transfer that would close an ownership cycle, and break `KInv`, is rejected by §63.9
  (`transfer_cycle_rejected`).
* The effect and rejection theorems of §63.
-/

namespace Ern.MemoryModel.Access

/-! ## Helpers on options and stacks -/

/-- Reading `OptP` with default `True` on a present value (§38). -/
private theorem optP_true {α : Type} {o : Option α} {P : α → Prop} {y : α} (h : OptP o P True)
    (hy : o = some y) : P y := by
  subst hy; exact h

/-- `OptP` with default `False` holds on a present value (§38). -/
private theorem optP_false_iff {α : Type} {o : Option α} {P : α → Prop} :
    OptP o P False ↔ ∃ y, o = some y ∧ P y := by
  cases o with
  | none => exact ⟨fun h => h.elim, fun ⟨_, h, _⟩ => by cases h⟩
  | some y => exact ⟨fun h => ⟨y, rfl, h⟩, fun ⟨_, h, hy⟩ => by cases h; exact hy⟩

/-- A frame of the stack is its own ancestor (§39). -/
private theorem ancestor_self {F : Frames} {f : Nat} (h : f ∈ F) : ancestor F f f := by
  unfold ancestor
  induction F with
  | nil => cases h
  | cons g F ih =>
    rw [List.dropWhile_cons]
    by_cases e : g = f
    · subst e; simp
    · have hne : (g != f) = true := by simp [e]
      simp only [hne, ↓reduceIte]
      rcases List.mem_cons.1 h with rfl | h
      · exact absurd rfl e
      · exact ih h

/-- In a duplicate-free stack `f :: F₀`, a frame of `F₀` does not have `f` as an ancestor (§39,
§49.1). -/
private theorem not_ancestor_top {f g : Nat} {F₀ : Frames} (hnd : (f :: F₀).Nodup) (hg : g ∈ F₀) :
    ¬ ancestor (f :: F₀) f g := by
  have hn := List.nodup_cons.1 hnd
  have hfg : f ≠ g := fun e => hn.1 (e ▸ hg)
  unfold ancestor
  simp only [List.dropWhile_cons, show (f != g) = true by simp [hfg], ↓reduceIte]
  exact fun h => hn.1 (mem_of_mem_dropWhile h)

/-! ## Bounded form of `KInv ∧ KAux` (§49, §50–§54, §57)

Every quantifier of `KInv ∧ KAux` bounded by the indices of `P` and `A`, so that `decide` checks
it on a concrete state. Used only by the counterexamples below. -/

/-- Owner validity of §49.3 for one place (bounded form). -/
private def OwnerOK (s : S3) : Holder → Prop
  | .frame f => f < s.nF
  | .place o => o < s.P.length

/-- Decidability of `OwnerOK` (§49.3). -/
private instance (s : S3) (h : Holder) : Decidable (OwnerOK s h) := by
  cases h <;> unfold OwnerOK <;> infer_instance

/-- The origin chain of an authority covering leaf `l` ends at `z`, a root authority whose
footprint is the footprint of a root place containing `l` (§49.6, bounded form). -/
private def RootOfLeaf (s : S3) (l : Nat) (z : Authority) : Prop :=
  z.origin = none ∧ ∃ r ∈ List.range s.P.length, RootPlace s.P r ∧ partOf s.P l r ∧
    (∀ l' ∈ z.footprint, l' ∈ footprint s.P r) ∧ ∀ l' ∈ footprint s.P r, l' ∈ z.footprint

/-- Decidability of `RootOfLeaf` (§49.6). -/
private instance (s : S3) (l : Nat) (z : Authority) : Decidable (RootOfLeaf s l z) := by
  unfold RootOfLeaf; infer_instance

/-- `z` is the root authority of the root place `r` (§49.7, bounded form). -/
private def RootAuthOf (s : S3) (r : Nat) (z : Authority) : Prop :=
  z.active = true ∧ z.origin = none ∧ z.mode = .modify ∧
    OptP (s.P[r]?) (fun pr => z.holder = pr.owner) False ∧
    (∀ l ∈ z.footprint, l ∈ footprint s.P r) ∧ ∀ l ∈ footprint s.P r, l ∈ z.footprint

/-- Decidability of `RootAuthOf` (§49.7). -/
private instance (s : S3) (r : Nat) (z : Authority) : Decidable (RootAuthOf s r z) := by
  unfold RootAuthOf; infer_instance

/-- `I1` for one pair of authorities (§50, bounded form). -/
private def I1Pair (s : S3) (a b : Nat) (x y : Authority) : Prop :=
  x.active = true → y.active = true → (∃ p ∈ x.footprint, p ∈ y.footprint) → a ∉ s.ancs b →
    b ∉ s.ancs a → x.mode = .observe ∧ y.mode = .observe

/-- Decidability of `I1Pair` (§50). -/
private instance (s : S3) (a b : Nat) (x y : Authority) : Decidable (I1Pair s a b x y) := by
  unfold I1Pair; infer_instance

/-- §49.2, bounded form. -/
private def PlacesB (s : S3) : Prop :=
  ∀ q ∈ List.range s.P.length, OptP (s.P[q]?) (fun pl => OptP pl.parent (fun r =>
    OptP (s.P[r]?) (fun pr => r < q ∧ pr.owner = pl.owner ∧ s.dead r = s.dead q) False) True)
    True

/-- Decidability of `PlacesB` (§49.2). -/
private instance (s : S3) : Decidable (PlacesB s) := by unfold PlacesB; infer_instance

/-- §49.3, first two items, bounded form. -/
private def OwnersB (s : S3) : Prop :=
  ∀ q ∈ List.range s.P.length, OptP (s.P[q]?) (fun pl => OwnerOK s pl.owner) True

/-- Decidability of `OwnersB` (§49.3). -/
private instance (s : S3) : Decidable (OwnersB s) := by unfold OwnersB; infer_instance

/-- §49.4, bounded form. -/
private def FootprintsB (s : S3) : Prop :=
  ∀ a ∈ List.range s.A.length, OptP (s.A[a]?) (fun x =>
    ∀ l ∈ x.footprint, l < s.P.length ∧ isLeaf s.P l) True

/-- Decidability of `FootprintsB` (§49.4). -/
private instance (s : S3) : Decidable (FootprintsB s) := by unfold FootprintsB; infer_instance

/-- §49.5, bounded form. -/
private def OriginsB (s : S3) : Prop :=
  ∀ b ∈ List.range s.A.length, OptP (s.A[b]?) (fun y => OptP y.origin (fun a => a < b) True) True

/-- Decidability of `OriginsB` (§49.5). -/
private instance (s : S3) : Decidable (OriginsB s) := by unfold OriginsB; infer_instance

/-- `RootChain` (§49.6), bounded form. -/
private def RootChainB (s : S3) : Prop :=
  ∀ a ∈ List.range s.A.length, OptP (s.A[a]?) (fun y => ∀ l ∈ y.footprint, isLeaf s.P l →
    ∃ x ∈ a :: s.ancs a, OptP (s.A[x]?) (RootOfLeaf s l) False) True

/-- Decidability of `RootChainB` (§49.6). -/
private instance (s : S3) : Decidable (RootChainB s) := by unfold RootChainB; infer_instance

/-- `RootHeld` (§49.7), bounded form. -/
private def RootHeldB (s : S3) : Prop :=
  ∀ r ∈ List.range s.P.length, RootPlace s.P r → s.Usable r →
    ∃ i ∈ List.range s.A.length, OptP (s.A[i]?) (RootAuthOf s r) False

/-- Decidability of `RootHeldB` (§49.7). -/
private instance (s : S3) : Decidable (RootHeldB s) := by unfold RootHeldB; infer_instance

/-- §49.8, bounded form. -/
private def HoldersB (s : S3) : Prop :=
  ∀ a ∈ List.range s.A.length, OptP (s.A[a]?) (fun y => y.active = true →
    HolderLive s y.holder) True

/-- Decidability of `HoldersB` (§49.8). -/
private instance (s : S3) : Decidable (HoldersB s) := by unfold HoldersB; infer_instance

/-- `I1` (§50), bounded form. -/
private def I1B (s : S3) : Prop :=
  ∀ a ∈ List.range s.A.length, ∀ b ∈ List.range s.A.length, a ≠ b →
    OptP (s.A[a]?) (fun x => OptP (s.A[b]?) (I1Pair s a b x) True) True

/-- Decidability of `I1B` (§50). -/
private instance (s : S3) : Decidable (I1B s) := by unfold I1B; infer_instance

/-- `I2` (§51), bounded form. -/
private def I2B (s : S3) : Prop :=
  ∀ b ∈ List.range s.A.length, OptP (s.A[b]?) (fun y => OptP y.origin (fun a =>
    OptP (s.A[a]?) (fun x => y.mode.le x.mode ∧ (∀ p ∈ y.footprint, p ∈ x.footprint) ∧
      (y.active = true → x.active = true)) False) True)
    True

/-- Decidability of `I2B` (§51). -/
private instance (s : S3) : Decidable (I2B s) := by unfold I2B; infer_instance

/-- `I3` (§52), bounded form. -/
private def I3B (s : S3) : Prop :=
  ∀ q ∈ List.range s.P.length, s.Usable q → ∀ x ∈ s.D q, s.Active x

/-- Decidability of `I3B` (§52). -/
private instance (s : S3) : Decidable (I3B s) := by unfold I3B; infer_instance

/-- `NoDangling` (§54) for one authority, bounded form. -/
private def NoDanglingOne (s : S3) (y : Authority) : Prop :=
  y.active = true → ∀ q ∈ List.range s.P.length, ¬ s.Usable q →
    ∀ l ∈ footprint s.P q, l ∉ y.footprint

/-- Decidability of `NoDanglingOne` (§54). -/
private instance (s : S3) (y : Authority) : Decidable (NoDanglingOne s y) := by
  unfold NoDanglingOne; infer_instance

/-- `NoDangling` (§54), bounded form. -/
private def NoDanglingB (s : S3) : Prop :=
  ∀ j ∈ List.range s.A.length, OptP (s.A[j]?) (NoDanglingOne s) True

/-- Decidability of `NoDanglingB` (§54). -/
private instance (s : S3) : Decidable (NoDanglingB s) := by unfold NoDanglingB; infer_instance

/-- `RootHeldConv` (§40, §49.7) for one authority, bounded form. -/
private def ConvOne (s : S3) (z : Authority) : Prop :=
  z.origin = none → ∀ l ∈ z.footprint, ∀ r ∈ List.range s.P.length, RootPlace s.P r →
    partOf s.P l r → OptP (s.P[r]?) (fun pr => z.holder = pr.owner) False

/-- Decidability of `ConvOne` (§40, §49.7). -/
private instance (s : S3) (z : Authority) : Decidable (ConvOne s z) := by
  unfold ConvOne; infer_instance

/-- `RootHeldConv` (§40, §49.7), bounded form. -/
private def ConvB (s : S3) : Prop :=
  ∀ x ∈ List.range s.A.length, OptP (s.A[x]?) (ConvOne s) True

/-- Decidability of `ConvB` (§40, §49.7). -/
private instance (s : S3) : Decidable (ConvB s) := by unfold ConvB; infer_instance

/-- `KInv ∧ KAux` (§57, §49.7) with every quantifier bounded. -/
private def KInvB (s : S3) : Prop :=
  (s.F ≠ [] ∧ s.F.Nodup ∧ ∀ f ∈ s.F, f < s.nF) ∧ PlacesB s ∧ OwnersB s ∧ FootprintsB s ∧
    OriginsB s ∧ RootChainB s ∧ RootHeldB s ∧ HoldersB s ∧ I1B s ∧ I2B s ∧ I3B s ∧
    AnchorOrder s ∧ NoDanglingB s ∧ AnchorOrderHeld s ∧ ConvB s

/-- Decidability of `KInvB` (§57). -/
private instance (s : S3) : Decidable (KInvB s) := by unfold KInvB; infer_instance

/-- A place of a footprint is a place of the state (§40). -/
private theorem lt_of_mem_footprint {P : List Place} {q l : Nat} (h : l ∈ footprint P q) :
    q < P.length := by
  obtain ⟨hl, -, -, hlq⟩ := mem_footprint.1 h
  rcases hlq with rfl | hc
  · exact hl
  · exact Nat.lt_trans (chain_lt hc) hl

/-- The bounded form gives `KInv ∧ KAux` (§57, §49.7). -/
private theorem kInvAux_of_bounded {s : S3} (h : KInvB s) : KInv s ∧ KAux s := by
  obtain ⟨hF, hpl, hown, hfp, hor, hrc, hrh, hho, h1, h2, h3, hao, hnd, haoh, hconv⟩ := h
  have wf : WF3 s := {
    frames := hF
    places := fun q pl r hq hp => by
      have h1 := optP_true (hpl q (List.mem_range.2 (lt_of_getElem? hq))) hq
      have h2 := optP_true h1 hp
      obtain ⟨pr, hpr, h⟩ := optP_false_iff.1 h2
      exact ⟨pr, hpr, h⟩
    owners := ⟨fun q pl f hq ho => by
        have := optP_true (hown q (List.mem_range.2 (lt_of_getElem? hq))) hq
        rw [ho] at this; exact this,
      fun q pl o hq ho => by
        have := optP_true (hown q (List.mem_range.2 (lt_of_getElem? hq))) hq
        rw [ho] at this; exact this,
      fun q hq => hq.frameOf⟩
    footprints := fun a x hx => optP_true (hfp a (List.mem_range.2 (lt_of_getElem? hx))) hx
    origins := fun b y a hb ho => by
      have h1 := optP_true (hor b (List.mem_range.2 (lt_of_getElem? hb))) hb
      exact optP_true (P := fun a => a < b) h1 ho
    rootChain := fun a y l ha hl hleaf => by
      obtain ⟨x, hx, hz⟩ :=
        optP_true (hrc a (List.mem_range.2 (lt_of_getElem? ha))) ha l hl hleaf
      obtain ⟨z, hz, hzo, r, -, hr, hlr, hs1, hs2⟩ := optP_false_iff.1 hz
      exact ⟨x, z, r, List.mem_cons.1 hx, hz, hzo, hr, hlr, fun l' => ⟨hs1 l', hs2 l'⟩⟩
    rootHeld := fun r hr hu => by
      obtain ⟨i, -, hz⟩ := hrh r (List.mem_range.2 hr.1) hr hu
      obtain ⟨z, hz, za, zo, zm, hpr, hs1, hs2⟩ := optP_false_iff.1 hz
      obtain ⟨pr, hpr, hh⟩ := optP_false_iff.1 hpr
      exact ⟨i, z, pr, hz, za, zo, zm, hpr, hh, fun l => ⟨hs1 l, hs2 l⟩⟩
    holders := fun a y hy ya => optP_true (hho a (List.mem_range.2 (lt_of_getElem? hy))) hy ya }
  refine ⟨kInv_of wf ⟨⟨fun a b x y p hab ha hb xa ya xp yp hn hn' => ?_, fun b y a hb ho => ?_,
    fun q hq => h3 q (List.mem_range.2 hq.lt) hq, i4_always s⟩, hao,
    fun j y hy ya q hq l hl => ?_⟩ haoh, fun x z l r hx ho hl hr hlr => ?_⟩
  · have e1 := optP_true (h1 a (List.mem_range.2 (lt_of_getElem? ha)) b
      (List.mem_range.2 (lt_of_getElem? hb)) hab) ha
    exact optP_true e1 hb xa ya ⟨p, xp, yp⟩ hn hn'
  · have e1 := optP_true (h2 b (List.mem_range.2 (lt_of_getElem? hb))) hb
    have e2 := optP_true e1 ho
    obtain ⟨x, hx, h⟩ := optP_false_iff.1 e2
    exact ⟨x, hx, h⟩
  · exact optP_true (hnd j (List.mem_range.2 (lt_of_getElem? hy))) hy ya q
      (List.mem_range.2 (lt_of_mem_footprint hl)) hq l hl
  · exact optP_false_iff.1 (optP_true (hconv x (List.mem_range.2 (lt_of_getElem? hx))) hx ho l hl
      r (List.mem_range.2 hr.1) hr hlr)

/-! ## Effect of `transfer` on anchors, frames and usability (§63) -/

/-- Anchors after a transfer (§63, `ok` effect, fourth item): parts of `src` lose theirs, and
place `q` receives those of every part `r` of `src` with `corr(r) = q`. -/
private theorem transfer_D (s : S3) (src dst q : Nat) : (transferEff s src dst).D q =
    if partOf s.P q src then [] else s.D q ++ movedTo s src dst q := rfl

/-- Membership in `movedTo` (§63, `ok` effect, fourth item). -/
private theorem mem_movedTo {s : S3} {src dst q x : Nat} :
    x ∈ movedTo s src dst q ↔
      ∃ r, partOf s.P r src ∧ corr s.P src dst r = some q ∧ x ∈ s.D r := by
  simp only [movedTo, List.mem_flatMap, List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨r, ⟨-, hr, hc⟩, hx⟩; exact ⟨r, hr, hc, hx⟩
  · rintro ⟨r, hr, hc, hx⟩; exact ⟨r, ⟨hr.1, hr, hc⟩, hx⟩

/-- An anchor of a part of `src` is among the dependencies checked by §63.6. -/
private theorem mem_movedDeps_part {s : S3} {src r x : Nat} (hr : partOf s.P r src)
    (hx : x ∈ s.D r) : x ∈ movedDeps s src := by
  simp only [movedDeps, List.mem_flatMap, List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨r, ⟨hr.1, .inl hr⟩, hx⟩

/-- Under `WF3`, a part of `dst` is not a part of `src` when their footprints are disjoint
(§40, §63.3): every place has a leaf. -/
private theorem not_partOf_src {s : S3} (hw : WF3 s) {src dst r : Nat}
    (hdis : ¬ overlap s.P src dst) (hr : partOf s.P r dst) : ¬ partOf s.P r src := fun hs => by
  obtain ⟨l, hl⟩ := exists_mem_footprint hw (s.P.length - r + 1) r (by omega) hr.1
  exact hdis ⟨l, footprint_sub hw hs hl, footprint_sub hw hr hl⟩

/-- An ownership chain avoiding the storage of `src` is unchanged by the transfer (§40, §63
`ok` effect, third item). -/
private theorem transfer_frameOf_fwd {s : S3} {src dst q f : Nat} (h : FrameOf s q f)
    (hn : ¬ OwnedIn s.P src q) : FrameOf (transferEff s src dst) q f := by
  induction h with
  | @frame q f pl hpl ho =>
    exact .frame (pl := pl) (by rw [transfer_P_get, hpl]; simp [ho, heldIn]) ho
  | @place q o f pl hpl ho hf ih =>
    have h1 : ¬ partOf s.P o src := fun hp => hn (.direct hpl ho hp)
    have h2 : ¬ OwnedIn s.P src o := fun ho' => hn (.step hpl ho ho')
    exact .place (pl := pl) (by rw [transfer_P_get, hpl]; simp [ho, heldIn, h1]) ho (ih h2)

/-- A place usable before the transfer whose ownership chain avoids the storage of `src` stays
usable (§40, §63 `ok` effect, third item). -/
private theorem transfer_usable_unmoved {s : S3} {src dst q : Nat} (h : s.Usable q)
    (hn : ¬ OwnedIn s.P src q) : (transferEff s src dst).Usable q := by
  induction h with
  | @frame q f pl hpl hd ho hf =>
    exact .frame (pl := pl) (by rw [transfer_P_get, hpl]; simp [ho, heldIn]) hd ho hf
  | @place q o pl hpl hd ho _ ih =>
    have h1 : ¬ partOf s.P o src := fun hp => hn (.direct hpl ho hp)
    have h2 : ¬ OwnedIn s.P src o := fun ho' => hn (.step hpl ho ho')
    exact .place (pl := pl) (by rw [transfer_P_get, hpl]; simp [ho, heldIn, h1]) hd ho (ih h2)

/-- The ownership chain of a place after the transfer (§40, §63 `ok` effect, third item): the
former chain if it avoids the storage of `src`; otherwise it goes through the place
corresponding to a part of `src`. -/
private theorem transfer_frameOf_back {s : S3} {src dst q f : Nat}
    (h : FrameOf (transferEff s src dst) q f) :
    (FrameOf s q f ∧ ¬ OwnedIn s.P src q) ∨
      (OwnedIn s.P src q ∧ ∃ r, partOf s.P r src ∧
        FrameOf (transferEff s src dst) ((corr s.P src dst r).getD dst) f) := by
  induction h with
  | @frame q f pl hpl ho =>
    rw [transfer_P_get] at hpl
    cases h' : s.P[q]? with
    | none => rw [h'] at hpl; cases hpl
    | some pl₀ =>
      rw [h'] at hpl; simp only [Option.map_some, Option.some.injEq] at hpl; subst hpl
      split at ho
      · rename_i hh
        obtain ⟨r', e⟩ := mvTo_place (dst := dst) hh
        simp [e] at ho
      · left; refine ⟨.frame h' ho, fun hn => ?_⟩
        cases hn with
        | direct h1 h2 _ => rw [h'] at h1; cases h1; rw [ho] at h2; cases h2
        | step h1 h2 _ => rw [h'] at h1; cases h1; rw [ho] at h2; cases h2
  | @place q o f pl hpl ho hf ih =>
    rw [transfer_P_get] at hpl
    cases h' : s.P[q]? with
    | none => rw [h'] at hpl; cases hpl
    | some pl₀ =>
      rw [h'] at hpl; simp only [Option.map_some, Option.some.injEq] at hpl; subst hpl
      split at ho
      · rename_i hh
        cases hpo : pl₀.owner with
        | frame g => rw [hpo] at hh; exact hh.elim
        | place r =>
          rw [hpo] at hh ho
          simp only [mvTo, Holder.place.injEq] at ho
          exact .inr ⟨.direct h' hpo hh, r, hh, ho ▸ hf⟩
      · rename_i hh
        rcases ih with ⟨hf0, hn⟩ | ⟨ho', hd⟩
        · left; refine ⟨.place h' ho hf0, fun hq => ?_⟩
          cases hq with
          | direct h1 h2 h3 =>
            rw [h'] at h1; cases h1; rw [ho] at h2; cases h2; exact hh (by rw [ho]; exact h3)
          | step h1 h2 h3 => rw [h'] at h1; cases h1; rw [ho] at h2; cases h2; exact hn h3
        · exact .inr ⟨.step h' ho ho', hd⟩

/-- Places with the same owner are owned through the value at `src` together (§40). -/
private theorem ownedIn_of_owner {P : List Place} {src q r : Nat} {pq pr : Place}
    (hq : P[q]? = some pq) (hr : P[r]? = some pr) (ho : pr.owner = pq.owner)
    (h : OwnedIn P src q) : OwnedIn P src r := by
  cases h with
  | direct h1 h2 h3 => rw [hq] at h1; cases h1; exact .direct hr (ho.trans h2) h3
  | step h1 h2 h3 => rw [hq] at h1; cases h1; exact .step hr (ho.trans h2) h3

/-- If a place owned through the value at `src` has a frame after the transfer, the destination
is not owned through that value (§40, §63 `ok` effect, third item): otherwise the chain would
come back to it. -/
private theorem transfer_dst_not_owned {s : S3} {src dst f : Nat} (hw : WF3 s) :
    ∀ {q}, FrameOf (transferEff s src dst) q f → OwnedIn s.P src q → ¬ OwnedIn s.P src dst := by
  intro q h
  induction h with
  | @frame q f pl hpl ho =>
    intro hq _
    rw [transfer_P_get] at hpl
    cases h' : s.P[q]? with
    | none => rw [h'] at hpl; cases hpl
    | some pl₀ =>
      rw [h'] at hpl; simp only [Option.map_some, Option.some.injEq] at hpl; subst hpl
      split at ho
      · rename_i hh
        obtain ⟨r', e⟩ := mvTo_place (dst := dst) hh
        simp [e] at ho
      · cases hq with
        | direct h1 h2 _ => rw [h'] at h1; cases h1; rw [ho] at h2; cases h2
        | step h1 h2 _ => rw [h'] at h1; cases h1; rw [ho] at h2; cases h2
  | @place q o f pl hpl ho hf ih =>
    intro hq hd
    rw [transfer_P_get] at hpl
    cases h' : s.P[q]? with
    | none => rw [h'] at hpl; cases hpl
    | some pl₀ =>
      rw [h'] at hpl; simp only [Option.map_some, Option.some.injEq] at hpl; subst hpl
      split at ho
      · rename_i hh
        obtain ⟨r', e, hr'⟩ := mvTo_part hw hd.lt hh
        simp only [e, Holder.place.injEq] at ho; subst ho
        obtain ⟨pl', pd, hpl', hpd, ho'⟩ := hw.ownerOf hr'
        exact ih (ownedIn_of_owner hpd hpl' ho' hd) hd
      · rename_i hh
        cases hq with
        | direct h1 h2 h3 =>
          rw [h'] at h1; cases h1; rw [ho] at h2; cases h2; exact hh (by rw [ho]; exact h3)
        | step h1 h2 h3 => rw [h'] at h1; cases h1; rw [ho] at h2; cases h2; exact ih h3 hd

/-- The frame of a place whose ownership chain avoids the storage of `src` is unchanged (§40,
`placeFrame`; §63). -/
private theorem transfer_pframe_unmoved {s : S3} {src dst q : Nat} (hn : ¬ OwnedIn s.P src q) :
    (transferEff s src dst).pframe q = s.pframe q :=
  Option.ext fun f => by
    rw [pframe_iff, pframe_iff]
    exact ⟨fun h => (transfer_frameOf_back h).elim (fun h => h.1) (fun h => absurd h.1 hn),
      fun h => transfer_frameOf_fwd h hn⟩

/-- If the destination has a frame after the transfer, it is still usable (§40, §63): its
ownership chain avoids the storage of `src`. -/
private theorem transfer_usable_dst {s : S3} {src dst g : Nat} (hw : WF3 s)
    (hdst : s.Usable dst) (hg : FrameOf (transferEff s src dst) dst g) :
    (transferEff s src dst).Usable dst := by
  rcases transfer_frameOf_back hg with ⟨-, hn⟩ | ⟨ho, -⟩
  · exact transfer_usable_unmoved hdst hn
  · exact absurd ho (transfer_dst_not_owned hw hg ho)

/-- The effective anchor depends only on the origin chain (§44). -/
private theorem effAnchor_congr {s s' : S3} {x : Nat} (h : s'.ancs x = s.ancs x) :
    s'.effAnchor x = s.effAnchor x := by simp only [S3.effAnchor, h]

/-- `EffAnchorOK` carries over between states whose effective anchors have the same holder frame
and whose ancestor relations agree on the target frame (§44). -/
private theorem effAnchorOK_of_same {s s' : S3} {x x' : Nat} {z z' : Authority}
    (hz : s.A[s.effAnchor x]? = some z) (hz' : s'.A[s'.effAnchor x']? = some z')
    (hh : s'.hframe z'.holder = s.hframe z.holder) {fd fd' : Option Nat}
    (hanc : ∀ g f, fd = some f → (ancestor s'.F g f ↔ ancestor s.F g f)) (hfd : fd' = fd) :
    EffAnchorOK s' x' fd' ↔ EffAnchorOK s x fd := by
  rw [hfd]; unfold EffAnchorOK; rw [hz, hz']; simp only [OptP]; rw [hh]
  cases hg : s.hframe z.holder with
  | none => simp
  | some g =>
    cases hf : fd with
    | none => simp
    | some f => simp only; rw [hanc g f hf]

/-- An anchor whose effective anchor does not move with the value keeps its order (§44, §63):
the holder of the effective anchor and its frame are unchanged. -/
private theorem transfer_effAnchorOK_unmoved {s : S3} {src dst x : Nat} {z : Authority}
    (hz : s.A[s.effAnchor x]? = some z) (hm : ¬ AnchorMoves s src (s.effAnchor x))
    (fd : Option Nat) :
    EffAnchorOK (transferEff s src dst) x fd ↔ EffAnchorOK s x fd := by
  have hm' : ¬ HolderMoves s src z.holder := by unfold AnchorMoves at hm; rw [hz] at hm; exact hm
  have hnh : ¬ heldIn s.P src z.holder := by
    cases hh : z.holder with
    | frame g => simp [heldIn]
    | place p => rw [hh] at hm'; exact fun h => hm' (.inl h)
  have he : (transferEff s src dst).effAnchor x = s.effAnchor x :=
    effAnchor_congr (by rw [(transfer_skel s src dst).ancs])
  refine effAnchorOK_of_same (z' := z) hz (by rw [he, transfer_A_get, hz]; simp [hnh]) ?_
    (fun _ _ _ => Iff.rfl) rfl
  cases hh : z.holder with
  | frame g => rfl
  | place p =>
    rw [hh] at hm'
    exact transfer_pframe_unmoved (fun ho => hm' (.inr ho))

/-! ## Preservation (§57, §63) -/

/-- §49.7 (`RootHeld`) after a transfer of a usable `src`: the holder of a root authority and the
owner of its root place change together (§40, §63 `ok` effect, third item). -/
private theorem transfer_rootHeld {s : S3} {src dst : Nat} (hw : WF3 s) (hsrc : s.Usable src) :
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

/-- `KAux` (`RootHeldConv`, §40, §49.7) after a transfer: the holder of a root authority and the
owner of its root place change together (§63 `ok` effect, third item). -/
private theorem transfer_rootHeldConv {s : S3} {src dst : Nat} (hr : RootHeldConv s) :
    RootHeldConv (transferEff s src dst) := by
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

/-- `WF3` (§49) after an accepted transfer. Only §49.8 (holder validity) uses §63.9, the
destination usable in the resulting state. -/
private theorem transfer_wf3 {k : K} {s : S3} {src dst : Nat} (hwf : WF3 s)
    (hpre : TransferPre k s src dst) : WF3 (transferEff s src dst) := by
  have hd' := hpre.dstUsableAfter
  have sk := transfer_skel s src dst
  have hdl := hpre.dstUsable.lt
  refine ⟨hwf.frames, ?_, ⟨?_, ?_, fun q hq => hq.frameOf⟩, fun a x hx l hl => ?_,
    sk.origins hwf.origins,
    sk.rootChain hwf.rootChain (transfer_len s src dst) (transfer_parentOf s src dst),
    transfer_rootHeld hwf hpre.srcUsable, ?_⟩
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

/-- `Inv3` (§57) after an accepted transfer. `I1`, `I2` (§50, §51): no authority changes but its
holder; `I3` (§52): kept anchors come from usable places, moved ones are checked by §63.6;
`AnchorOrder` is §63.6; `NoDangling` (§54): with §63.9, no usable place becomes unusable. -/
private theorem transfer_inv3 {k : K} {s : S3} {src dst : Nat} (hwf : WF3 s) (hinv : Inv3 s)
    (hpre : TransferPre k s src dst) : Inv3 (transferEff s src dst) := by
  have hd' := hpre.dstUsableAfter
  have sk := transfer_skel s src dst
  obtain ⟨⟨i1, i2, i3, -⟩, -, hnd⟩ := hinv
  refine ⟨⟨sk.i1 i1, sk.i2 i2, fun q hq x hx => ?_, i4_always _⟩, hpre.anchorOrder, ?_⟩
  · have hq' := transfer_usable_back hwf hpre.srcUsable hq
    refine sk.active.2 ?_
    rw [transfer_D] at hx
    split at hx
    · simp at hx
    · rcases List.mem_append.1 hx with hx | hx
      · exact i3 q hq' x hx
      · obtain ⟨r, hr, -, hxr⟩ := mem_movedTo.1 hx
        exact hpre.depsValid x (mem_movedDeps_part hr hxr)
  · intro j y hy ya q hq l hl hly
    rw [transfer_A_get] at hy
    obtain ⟨y₀, hy₀, rfl⟩ := Option.map_eq_some_iff.1 hy
    have ya₀ : y₀.active = true := by split at ya <;> exact ya
    have hly₀ : l ∈ y₀.footprint := by split at hly <;> exact hly
    rw [transfer_footprint] at hl
    exact hnd j y₀ hy₀ ya₀ q (fun hu => hq (transfer_usable_fwd hwf hd' hu)) l hl hly₀

/-- An accepted transfer preserves `WF3`, `Inv3` and `NoOrphan` (§57; §63, with §63.9). -/
theorem transfer_preserves_wf3_inv3 {k : K} {s s' : S3} {src dst : Nat} (hinv : KInv s)
    (h : TransferStep k src dst s (.ok s')) : WF3 s' ∧ Inv3 s' ∧ NoOrphan s' := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  have hw' := transfer_wf3 hinv.1 hpre
  exact ⟨hw', transfer_inv3 hinv.1 hinv.2.1 hpre, noOrphan_of_wf3 hw'⟩

/-- An accepted transfer preserves the auxiliary `KAux` (`RootHeldConv`, §40, §49.7; §63 `ok`
effect, third item), with no further hypothesis. -/
theorem transfer_preserves_kAux {k : K} {s s' : S3} {src dst : Nat} (haux : KAux s)
    (h : TransferStep k src dst s (.ok s')) : KAux s' := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
  exact transfer_rootHeldConv haux

/-- Auxiliary invariant, not a clause of §57 nor of §63: every active derived
authority held by a usable place is among the anchors of that place (§44). `store` (§65) adds
the stored authority to the anchors of its target, and the `ok` effect of §63 moves an
authority held by a part `r` of the source together with the anchors of `r`. -/
def HeldAnchored (s : S3) : Prop :=
  ∀ (x : Nat) (y : Authority) (q : Nat), s.A[x]? = some y → y.active = true → y.origin ≠ none →
    y.holder = .place q → s.Usable q → x ∈ s.D q

/-- `AnchorOrderHeld` (§44, §54) after an accepted transfer, under `HeldAnchored`: a moved held
authority is checked by §63.7; an unmoved derived one is an anchor of its unmoved holder,
checked by `AnchorOrder` in the resulting state (§63.6); an unmoved root authority is its own
effective anchor, held by the place. -/
private theorem transfer_anchorOrderHeld {k : K} {s : S3} {src dst : Nat} (hwf : WF3 s)
    (hheld : HeldAnchored s) (hpre : TransferPre k s src dst) :
    AnchorOrderHeld (transferEff s src dst) := by
  intro q hq x y hy ya hh
  have hy' := hy
  rw [transfer_A_get] at hy
  obtain ⟨y₀, hy₀, rfl⟩ := Option.map_eq_some_iff.1 hy
  by_cases hm : AnchorMoves s src x
  · have e := hpre.anchorOrderHeld x (List.mem_range.2 (lt_of_getElem? hy₀)) hm q
      (List.mem_range.2 (by rw [← transfer_len s src dst]; exact hq.lt)) hq
    rw [hy'] at e
    exact e ya hh
  · have hmv : ¬ HolderMoves s src y₀.holder := by
      unfold AnchorMoves at hm; rw [hy₀] at hm; exact hm
    have hnh : ¬ heldIn s.P src y₀.holder := by
      cases e : y₀.holder with
      | frame g => simp [heldIn]
      | place p => rw [e] at hmv; exact fun h => hmv (.inl h)
    simp only [hnh, ↓reduceIte] at ya hh hy'
    have hqs : ¬ partOf s.P q src := by rw [hh] at hmv; exact fun h => hmv (.inl h)
    cases ho : y₀.origin with
    | none =>
      have hex : (transferEff s src dst).effAnchor x = x := by
        have : (transferEff s src dst).org x = none := by simp [S3.org, hy', ho]
        simp [S3.effAnchor, S3.ancs, chain_none this]
      obtain ⟨f, hf, hfF⟩ := hq.frameOf
      unfold EffAnchorOK
      rw [hex, hy', pframe_iff.2 hf]
      simp only [OptP, hh, S3.hframe, pframe_iff.2 hf]
      exact ancestor_self hfF
    | some o =>
      have hxq := hheld x y₀ q hy₀ ya (by rw [ho]; exact fun h => by cases h) hh
        (transfer_usable_back hwf hpre.srcUsable hq)
      have hxq' : x ∈ (transferEff s src dst).D q := by
        rw [transfer_D]; simp only [hqs, ↓reduceIte]; exact List.mem_append_left _ hxq
      exact hpre.anchorOrder q hq x hxq'

/-- An accepted transfer preserves `HeldAnchored` (§44; §63 `ok` effect, second and fourth items):
an authority held by a part `r` of the source moves to `corr(r)` together with the anchors of
`r`; the other holders and their anchors are unchanged. -/
theorem transfer_preserves_heldAnchored {k : K} {s s' : S3} {src dst : Nat} (hwf : WF3 s)
    (hheld : HeldAnchored s) (h : TransferStep k src dst s (.ok s')) : HeldAnchored s' := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
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
      obtain ⟨r', hcr, -⟩ :=
        optP_false_iff.1 (hpre.sameShape.1 r (List.mem_range.2 hc.1) hc)
      simp only [mvTo, hcr, Option.getD_some, Holder.place.injEq] at hh
      subst hh
      have hr' := corr_partOf hwf hpre.dstUsable.lt (r + 1) r r' (Nat.lt_succ_self r) hcr
      have hxr := hheld x y₀ r hy₀ ya₀ ho₀ e
        (usable_of_partOf hwf (r + 1) r src (Nat.lt_succ_self r) hc hpre.srcUsable)
      rw [transfer_D]; simp only [not_partOf_src hwf hpre.disjoint hr', ↓reduceIte]
      exact List.mem_append_right _ (mem_movedTo.2 ⟨r, hc, hcr, hxr⟩)
  · simp only [hc, ↓reduceIte] at hh
    have hqs : ¬ partOf s.P q src := by rw [hh] at hc; exact hc
    have hxq := hheld x y₀ q hy₀ ya₀ ho₀ hh (transfer_usable_back hwf hpre.srcUsable hq)
    rw [transfer_D]; simp only [hqs, ↓reduceIte]
    exact List.mem_append_left _ hxq

/-- On a state satisfying `KInv` and the auxiliary `HeldAnchored`, an accepted transfer preserves
`KInv` (§57; §63). `HeldAnchored` is not a clause of §57: `transfer_preserves_of_dst_usable_fails`
shows that `KInv ∧ KAux` does not suffice on states not built by kernel steps. -/
theorem transfer_preserves {k : K} {s s' : S3} {src dst : Nat} (hinv : KInv s)
    (hheld : HeldAnchored s) (h : TransferStep k src dst s (.ok s')) : KInv s' := by
  obtain ⟨hw', hi', -⟩ := transfer_preserves_wf3_inv3 hinv h
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  exact kInv_of hw' hi' (transfer_anchorOrderHeld hinv.1 hheld hpre)

/-- An accepted transfer preserves `I5` (§57; §63 `ok` effect, §74), from a `WF3` state (§49):
the pinning obligations, the leaves and the footprints are unchanged, and with §63.9 every usable
place stays usable. `WF3` is used only for the last point. -/
theorem transfer_preserves_i5 {k : K} {s s' : S3} {src dst : Nat} (hwf : WF3 s) (h5 : I5 k s)
    (h : TransferStep k src dst s (.ok s')) : I5 k s' := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  intro l hl
  rw [S3.pin_congr (pins_transferEff s src dst)] at hl
  obtain ⟨q, hq, hlq⟩ := h5 l hl
  exact ⟨q, transfer_usable_fwd hwf hpre.dstUsableAfter hq, by rw [transfer_footprint]; exact hlq⟩

/-! ## §63.9 rejects the ownership-cycle run (§49.8, §54) -/

namespace TransferWitness

/-- Statics of the ownership-cycle counterexample (§47): two leaves owned by frame 0, place 0 and
place 1, both `Init`. -/
def cycStatics : Statics := [((none, none, 0), true), ((none, none, 0), true)]

/-- Initial state of the counterexample (§47). -/
def cyc0 : S3 := S3.init cycStatics

/-- After `alloc` with provider 1 and owner place 0 (§71): place 2 owned by place 0, root
authority 2 held by place 0. -/
def cyc1 : S3 := allocEff cyc0 0 [(none, 0)]

/-- After `alloc` with provider 1 and owner place 2 (§71): place 3 owned by place 2, root
authority 3 held by place 2. -/
def cyc2 : S3 := allocEff cyc1 2 [(none, 0)]

/-- The effect of `transfer(0, 3)` on `cyc2` (§63 `ok` effect): place 2 would be owned by place 3,
which is owned by place 2. -/
def cyc3 : S3 := transferEff cyc2 0 3

/-- `cyc2` is reached from `S3.init cycStatics` by two `alloc` steps (§57, §71). -/
theorem cyc2_reachable : Reachable Examples.K0 cycStatics cyc2 :=
  .step (.step .init (KStep.alloc (pr := 1) (ow := 0) (ls := [(none, 0)])
    (AllocStep.ok (by decide) trivial))) (KStep.alloc (pr := 1) (ow := 2) (ls := [(none, 0)])
    (AllocStep.ok (by decide) trivial))

/-- `cyc2` satisfies `KInv` and `KAux` (§57, §49.7). -/
theorem cyc2_kInv : KInv cyc2 ∧ KAux cyc2 := kInvAux_of_bounded (by decide)

/-- In `cyc3`, places 2 and 3 own each other and are unusable (§40; §63.9 fails); root authority
2 is active, held by the unusable place 3 and covers the leaf of the unusable place 2. -/
theorem cyc3_cycle : ¬ cyc3.Usable 2 ∧ ¬ cyc3.Usable 3 ∧ cyc3.Active 2 ∧
    OptP (cyc3.A[2]?) (fun y => y.holder = .place 3 ∧ 2 ∈ y.footprint) False := by decide

/-- `cyc3` violates holder validity (§49.8), so `WF3`, and `NoDangling` (§54). -/
theorem cyc3_not_wf3_noDangling : ¬ WF3 cyc3 ∧ ¬ NoDangling cyc3 := by
  obtain ⟨hu2, hu3, -, hy⟩ := cyc3_cycle
  obtain ⟨y, hy, hh, hl⟩ := optP_false_iff.1 hy
  have ya : y.active = true := by
    have : OptP (cyc3.A[2]?) (fun y => y.active = true) False := by decide
    rw [hy] at this; exact this
  refine ⟨fun hw => ?_, fun hnd => ?_⟩
  · have := hw.holders 2 y hy ya
    rw [hh] at this; exact hu3 this
  · exact hnd 2 y hy ya 2 hu2 2 (by decide) hl

end TransferWitness

open TransferWitness in
/-- The ownership-cycle run of §63 is rejected by §63.9 alone: under a contract with `DDSound`
(§80), in a reachable state satisfying `KInv ∧ KAux`, `transfer(0, 3)` satisfies §63.1–§63.8, its
destination is not usable in the resulting state (§63.9 fails), so the step is rejected; that
state would violate `KInv` (holder validity §49.8, `cyc3_not_wf3_noDangling`). -/
theorem transfer_cycle_rejected : DDSound Examples.K0 ∧ Reachable Examples.K0 cycStatics cyc2 ∧
    KInv cyc2 ∧ KAux cyc2 ∧
    (cyc2.Usable 0 ∧ cyc2.Usable 3 ∧ HasRight cyc2 .modify 0 ∧ HasRight cyc2 .modify 3 ∧
      SameShape cyc2.P 0 3 ∧ (∀ l ∈ footprint cyc2.P 0, cyc2.I l = .init) ∧
      (∀ l ∈ footprint cyc2.P 3, cyc2.I l ≠ .init) ∧ ¬ overlap cyc2.P 0 3 ∧
      (∃ g ∈ List.range cyc2.A.length, Grounds cyc2 .modify 0 g ∧
        ∀ j ∈ List.range cyc2.A.length, ActiveDerivedOutside cyc2 0 j → RightChain cyc2 g j) ∧
      (∀ l ∈ footprint cyc2.P 0, ¬ Examples.K0.Pinned l ∧ cyc2.pin l = false) ∧
      (∀ x ∈ movedDeps cyc2 0, cyc2.Active x) ∧ AnchorOrder cyc3 ∧
      (∀ x ∈ List.range cyc2.A.length, AnchorMoves cyc2 0 x →
        ∀ q ∈ List.range cyc2.P.length, cyc3.Usable q →
          OptP (cyc3.A[x]?) (fun y => y.active = true → y.holder = .place q →
            EffAnchorOK cyc3 x (cyc3.pframe q)) True) ∧
      NoLocalSelfLock cyc2 0 3) ∧
    ¬ cyc3.Usable 3 ∧ TransferStep Examples.K0 0 3 cyc2 .reject ∧ ¬ KInv cyc3 :=
  ⟨fun _ _ h => (h : False).elim, cyc2_reachable, cyc2_kInv.1, cyc2_kInv.2, by decide,
    cyc3_cycle.2.1, .reject fun hpre => cyc3_cycle.2.1 hpre.dstUsableAfter,
    fun h => cyc3_not_wf3_noDangling.1 h.1⟩

/-! ## `KInv ∧ KAux` does not suffice without `HeldAnchored` (§44, §63.7)

The transfer below satisfies every precondition of §63, §63.9 included. §63.7 checks
`AnchorOrderHeld` only for the moved held authorities. In `ahx`, the derived authority 6 is held
by place 2, outside the transferred value, without being among its anchors (`HeldAnchored`
fails), and its effective anchor, the root 3 held by the source, moves with the value to a
younger frame. The state is not built by kernel steps: in such runs a derived
authority is held by a place only through `store` (§65), which also anchors it there. -/

namespace TransferWitness

/-- A state satisfying `KInv ∧ KAux` (§57, §49.7), not reached by kernel steps: frames 1 (current)
and 0; place 0 owned by frame 0; source place 1 owned by place 0, `Init`; place 2 owned by
frame 0; place 3 owned by the source; destination place 4 owned by frame 1. Authorities 0–4 are
the roots of places 0–4; authority 5, derived from 0, gives frame 1 `Modify` on place 0 and,
through it, on the source; authority 6, derived from the root 3, is held by place 2, with no
anchor anywhere. -/
def ahx : S3 where
  F := [1, 0]
  nF := 2
  P := [⟨none, .frame 0, 0⟩, ⟨none, .place 0, 0⟩, ⟨none, .frame 0, 0⟩, ⟨none, .place 1, 0⟩,
    ⟨none, .frame 1, 0⟩]
  I := fun l => if l = 1 then .init else .uninit
  A := [⟨.modify, none, [0], .frame 0, true⟩, ⟨.modify, none, [1], .place 0, true⟩,
    ⟨.modify, none, [2], .frame 0, true⟩, ⟨.modify, none, [3], .place 1, true⟩,
    ⟨.modify, none, [4], .frame 1, true⟩, ⟨.modify, some 0, [0], .frame 1, true⟩,
    ⟨.modify, some 3, [3], .place 2, true⟩]
  D := fun _ => []
  dead := fun _ => false
  pins := []

/-- `transfer(1, 4)` from `ahx` (§63, `ok` effect). -/
def ahx' : S3 := transferEff ahx 1 4

end TransferWitness

open TransferWitness in
/-- From a state satisfying `KInv ∧ KAux`, an accepted transfer (§63, its destination usable in
the resulting state by §63.9) can still break `AnchorOrderHeld` (§44, §54): in `ahx'`, authority
6 is held by place 2 of frame 0 and its effective anchor, the root 3, is now held by the
destination in frame 1. `HeldAnchored` fails in `ahx`. -/
theorem transfer_preserves_of_dst_usable_fails : ∃ s s', KInv s ∧ KAux s ∧ ¬ HeldAnchored s ∧
    TransferStep Examples.K0 1 4 s (.ok s') ∧ s'.Usable 4 ∧ ¬ AnchorOrderHeld s' := by
  have hk := kInvAux_of_bounded (s := ahx) (by decide)
  refine ⟨ahx, ahx', hk.1, hk.2, fun h => ?_, .ok (by decide), by decide, by decide⟩
  have := h 6 ⟨.modify, some 3, [3], .place 2, true⟩ 2 rfl rfl (by simp) rfl (by decide)
  simp [ahx] at this

/-! ## Effects and rejections of `transfer` (§63) -/

/-- Determinism of `transfer` (§58, §63): one outcome per state. -/
theorem transfer_det {k : K} {src dst : Nat} {s : S3} {o₁ o₂ : Outcome3 S3}
    (h₁ : TransferStep k src dst s o₁) (h₂ : TransferStep k src dst s o₂) : o₁ = o₂ :=
  Guarded.det h₁ h₂

/-- §63 `ok` effect, second and third items: after an accepted transfer, an authority held by a
part `r` of the source is held by the corresponding part `corr(r)` of the destination, not
indiscriminately by the destination root; a place owned by `r` is owned by `corr(r)`. -/
theorem transfer_to_corresponding_parts {k : K} {s s' : S3} {src dst : Nat} (hwf : WF3 s)
    (h : TransferStep k src dst s (.ok s')) {r : Nat} (hr : partOf s.P r src) :
    ∃ r', corr s.P src dst r = some r' ∧ partOf s.P r' dst ∧
      (∀ (b : Nat) (y : Authority), s.A[b]? = some y → y.holder = .place r →
        s'.A[b]? = some { y with holder := .place r' }) ∧
      (∀ (q : Nat) (pl : Place), s.P[q]? = some pl → pl.owner = .place r →
        s'.P[q]? = some { pl with owner := .place r' }) := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  have h1 := hpre.sameShape.1 r (List.mem_range.2 hr.1) hr
  unfold OptP at h1; split at h1
  · rename_i r' hc
    refine ⟨r', hc, corr_partOf hwf hpre.dstUsable.lt (r + 1) r r' (Nat.lt_succ_self r) hc,
      fun b y hy hh => ?_, fun q pl hq ho => ?_⟩
    · rw [transfer_A_get, hy]; simp [hh, heldIn, hr, mvTo, hc]
    · rw [transfer_P_get, hq]; simp [ho, heldIn, hr, mvTo, hc]
  · exact h1.elim

/-- §63 `ok` effect, third item: every place owned by a part of the source is owned by the moved
holder (`mvTo`, the corresponding part of the destination); every other place keeps its owner;
no place changes parent. -/
theorem transfer_moves_ownership {k : K} {s s' : S3} {src dst : Nat}
    (h : TransferStep k src dst s (.ok s')) :
    ∀ (q : Nat) (pl : Place), s.P[q]? = some pl →
      s'.P[q]? = some (if heldIn s.P src pl.owner then
        { pl with owner := mvTo s.P src dst pl.owner } else pl) := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
  exact fun q pl hq => by rw [transfer_P_get, hq]; rfl

/-- §63.4 and §63 `ok` effect, fourth item ("no authority is created or duplicated"): an accepted
transfer keeps the number of authorities and the mode, origin, footprint and activity of each;
an authority held within the source gets the moved holder, the others keep theirs. -/
theorem transfer_no_duplicate_authority {k : K} {s s' : S3} {src dst : Nat}
    (h : TransferStep k src dst s (.ok s')) :
    SameSkel s s' ∧ ∀ (b : Nat) (y : Authority), s.A[b]? = some y →
      s'.A[b]? = some (if heldIn s.P src y.holder then
        { y with holder := mvTo s.P src dst y.holder } else y) := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
  exact ⟨transfer_skel s src dst, fun b y hy => by rw [transfer_A_get, hy]; rfl⟩

/-- §63 `ok` effect, first item, and §41, §53: after an accepted transfer every source leaf is
`Moved`, and no read of a region containing one is permitted. -/
theorem transfer_invalidates_source {k : K} {s s' : S3} {src dst : Nat}
    (h : TransferStep k src dst s (.ok s')) :
    ∀ l ∈ footprint s.P src, s'.I l = .moved ∧ ∀ a ls, l ∈ ls → ¬ Read3Pre s' a ls := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  intro l hl
  have hm : (transferEff s src dst).I l = .moved := by
    simp only [transferEff, show l ∉ footprint s.P dst from fun h' => hpre.disjoint ⟨l, hl, h'⟩,
      hl, ↓reduceIte]
  exact ⟨hm, fun a ls hls => i4_always _ a ls l hls hm⟩

/-- §63 `ok` effect, fourth item: the dependencies of each part `r` of the source follow the
value to the corresponding part `corr(r)` of the destination and leave `r`; every other place
keeps its anchors; no anchor appears from elsewhere. -/
theorem transfer_deps_follow {k : K} {s s' : S3} {src dst : Nat} (hwf : WF3 s)
    (h : TransferStep k src dst s (.ok s')) :
    (∀ r, partOf s.P r src → ∃ r', corr s.P src dst r = some r' ∧ partOf s.P r' dst ∧
      ∀ x ∈ s.D r, x ∈ s'.D r') ∧
    (∀ r, partOf s.P r src → s'.D r = []) ∧
    (∀ q, ¬ partOf s.P q src → ∀ x ∈ s.D q, x ∈ s'.D q) ∧
    (∀ q x, x ∈ s'.D q → (¬ partOf s.P q src ∧ x ∈ s.D q) ∨
      ∃ r, partOf s.P r src ∧ corr s.P src dst r = some q ∧ x ∈ s.D r) := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  refine ⟨fun r hr => ?_, fun r hr => by rw [transfer_D]; simp [hr],
    fun q hq x hx => by
      rw [transfer_D]; simp only [hq, ↓reduceIte]; exact List.mem_append_left _ hx,
    fun q x hx => ?_⟩
  · have h1 := hpre.sameShape.1 r (List.mem_range.2 hr.1) hr
    obtain ⟨r', hc, -⟩ := optP_false_iff.1 h1
    have hr' := corr_partOf hwf hpre.dstUsable.lt (r + 1) r r' (Nat.lt_succ_self r) hc
    refine ⟨r', hc, hr', fun x hx => ?_⟩
    rw [transfer_D]; simp only [not_partOf_src hwf hpre.disjoint hr', ↓reduceIte]
    exact List.mem_append_right _ (mem_movedTo.2 ⟨r, hr, hc, hx⟩)
  · rw [transfer_D] at hx
    split at hx
    · simp at hx
    · rename_i hq
      rcases List.mem_append.1 hx with hx | hx
      · exact .inl ⟨hq, hx⟩
      · exact .inr (mem_movedTo.1 hx)

/-- §63.6 rejects an escape through anchors: if a part of the source is anchored on an authority
`a` whose effective anchor does not move with the value and belongs to the current frame `f`,
the transfer to a destination whose frame, in the resulting state, is an older frame `g` is
rejected. The anchor follows the value to the corresponding part of the destination (§63 `ok`
effect, fourth item), where `AnchorOrder` (§44) fails in the resulting state. -/
theorem anchor_escape_rejected_at_transfer {k : K} {s : S3} {src dst a f g : Nat}
    {F₀ : Frames} {z : Authority} (hwf : WF3 s) (hF : s.F = f :: F₀) (ha : a ∈ depsOf s src)
    (hz : s.A[s.effAnchor a]? = some z) (hm : ¬ AnchorMoves s src (s.effAnchor a))
    (hzf : s.hframe z.holder = some f)
    (hg : (transferEff s src dst).pframe dst = some g) (hgF : g ∈ F₀) :
    TransferStep k src dst s .reject := by
  refine .reject fun hpre => ?_
  have hdst := transfer_usable_dst hwf hpre.dstUsable (pframe_iff.1 hg)
  simp only [depsOf, List.mem_flatMap, List.mem_filter, List.mem_range, decide_eq_true_eq] at ha
  obtain ⟨r, ⟨-, hr⟩, hx⟩ := ha
  obtain ⟨r', hc, -⟩ := optP_false_iff.1 (hpre.sameShape.1 r (List.mem_range.2 hr.1) hr)
  have hr' := corr_partOf hwf hpre.dstUsable.lt (r + 1) r r' (Nat.lt_succ_self r) hc
  have hin : a ∈ (transferEff s src dst).D r' := by
    rw [transfer_D]; simp only [not_partOf_src hwf hpre.disjoint hr', ↓reduceIte]
    exact List.mem_append_right _ (mem_movedTo.2 ⟨r, hr, hc, hx⟩)
  have hok := hpre.anchorOrder r' (transfer_usable_part hwf hr' hdst) a hin
  rw [transfer_pframe_part hwf hr', transfer_effAnchorOK_unmoved hz hm, hg] at hok
  unfold EffAnchorOK at hok
  rw [hz] at hok
  simp only [OptP, hzf] at hok
  rw [hF] at hok
  exact not_ancestor_top (hF ▸ hwf.frames.2.1) hgF hok

/-- §63.7 rejects an escape through held authorities: if a part of the source holds an active
authority `a` whose effective anchor does not move with the value and belongs to the current
frame `f`, the transfer to a destination whose frame, in the resulting state, is an older frame
`g` is rejected. The authority moves to the corresponding part of the destination (§63 `ok`
effect, second item), where `AnchorOrderHeld` (§44) fails in the resulting state. -/
theorem store_escape_rejected_at_transfer {k : K} {s : S3} {src dst a f g : Nat} {F₀ : Frames}
    {y z : Authority} (hwf : WF3 s) (hF : s.F = f :: F₀) (ha : s.A[a]? = some y)
    (ya : y.active = true) (hh : heldIn s.P src y.holder)
    (hz : s.A[s.effAnchor a]? = some z) (hm : ¬ AnchorMoves s src (s.effAnchor a))
    (hzf : s.hframe z.holder = some f)
    (hg : (transferEff s src dst).pframe dst = some g) (hgF : g ∈ F₀) :
    TransferStep k src dst s .reject := by
  refine .reject fun hpre => ?_
  have hdst := transfer_usable_dst hwf hpre.dstUsable (pframe_iff.1 hg)
  obtain ⟨r', e, hr'⟩ := mvTo_part hwf hpre.dstUsable.lt hh
  have ha' : (transferEff s src dst).A[a]? = some { y with holder := .place r' } := by
    rw [transfer_A_get, ha]; simp [hh, e]
  have hmv : AnchorMoves s src a := by
    unfold AnchorMoves; rw [ha]
    show HolderMoves s src y.holder
    cases e' : y.holder with
    | frame _ => rw [e'] at hh; exact hh.elim
    | place p => rw [e'] at hh; exact Or.inl hh
  have hok := hpre.anchorOrderHeld a (List.mem_range.2 (lt_of_getElem? ha)) hmv r'
    (List.mem_range.2 hr'.1) (transfer_usable_part hwf hr' hdst)
  rw [ha'] at hok
  have hok := hok ya rfl
  rw [transfer_pframe_part hwf hr', transfer_effAnchorOK_unmoved hz hm, hg] at hok
  unfold EffAnchorOK at hok
  rw [hz] at hok
  simp only [OptP, hzf] at hok
  rw [hF] at hok
  exact not_ancestor_top (hF ▸ hwf.frames.2.1) hgF hok

/-- §63.8 is a local check: its decision depends on the state only through the places and the
authorities held within the source, the ones the transfer moves. Two states with the same places
and the same such authorities, at the same identities, get the same decision; no global
authority-acyclicity check is involved. -/
theorem noLocalSelfLock_local {s s' : S3} {src dst : Nat} (hP : s'.P = s.P)
    (hA : ∀ (j : Nat) (y : Authority), (s.A[j]? = some y ∨ s'.A[j]? = some y) →
      heldIn s.P src y.holder → s'.A[j]? = s.A[j]?) :
    NoLocalSelfLock s' src dst ↔ NoLocalSelfLock s src dst := by
  have key : ∀ (t t' : S3), t'.P = t.P →
      (∀ (j : Nat) (y : Authority), (t.A[j]? = some y ∨ t'.A[j]? = some y) →
        heldIn t.P src y.holder → t'.A[j]? = t.A[j]?) →
      NoLocalSelfLock t src dst → NoLocalSelfLock t' src dst := by
    intro t t' hP hA h j _ hheld hsl
    obtain ⟨y, hy, hh⟩ := optP_false_iff.1 hheld
    rw [hP] at hh
    have e := hA j y (.inr hy) hh
    have hy' : t.A[j]? = some y := e.symm.trans hy
    refine h j (List.mem_range.2 (lt_of_getElem? hy')) (optP_false_iff.2 ⟨y, hy', hh⟩) ?_
    have ga : (transferEff t' src dst).A[j]? = (transferEff t src dst).A[j]? := by
      rw [transfer_A_get, transfer_A_get, e, hP]
    have gl : holderLeaves (transferEff t' src dst) = holderLeaves (transferEff t src dst) := by
      funext hd
      cases hd with
      | place p => simp only [holderLeaves, transferEff, hP]
      | frame f => rfl
    unfold SelfLock at hsl ⊢
    rw [ga, gl] at hsl
    exact hsl
  refine ⟨key s' s hP.symm (fun j y hy hh => ?_), key s s' hP hA⟩
  rw [hP] at hh
  exact (hA j y hy.symm hh).symm

end Ern.MemoryModel.Access
