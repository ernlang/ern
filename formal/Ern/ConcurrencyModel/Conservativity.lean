import Ern.ConcurrencyModel.Steps

/-!
# Sequential conservativity (C24)

On states whose only live context is the initial one, without parent (`SC.Sole`), in particular
single-context states (`SC.Single`: one context, the initial one, live, without parent), whose
frame structure satisfies `FramesC`:

* `ancestorC` coincides with `ancestor` of Spec 1 §39 on the stack of the context
  (`single_ancestorC`);
* `AnchorOrderC`, `AnchorOrderHeldC` and `KInvC` coincide with their Spec 1 counterparts on the
  projection `SC.toS3` (`single_anchorOrderC`, `single_anchorOrderHeldC`, `single_kInvC`);
* every inherited operation O1–O16 executed by the context has the outcomes of Spec 1 on the
  projection, and an `ok` outcome stays a single-context state (`conservative_ok`), or keeps the
  initial context the only live one (`conservative_ok_sole`), whose projection is the Spec 1
  effect (`conservative_op`).

The statements on `K_C.SyncAuthorized` and `deriveSync` are in `SequentialConservativity`
(`projection_libKC`, `registry_none_no_deriveSync`).

Theorem numbers are those of `formal/DESIGN.md`, Milestone 4, target theorems.
-/

namespace Ern.ConcurrencyModel

open Ern.MemoryModel.Access

/-! ## Lists -/

/-- `parIn` of an element absent from the stack is `none` (C3). -/
theorem parIn_not_mem {par : Option Nat} {f : Nat} : ∀ {l : List Nat}, f ∉ l → parIn par f l = none
  | [], _ => rfl
  | a :: l, h => by
    have ha : a ≠ f := fun e => h (e ▸ List.mem_cons_self ..)
    simp only [parIn, ha, ↓reduceIte]
    exact parIn_not_mem fun hm => h (List.mem_cons_of_mem _ hm)

/-- `parIn` ignores a head distinct from the frame (C3). -/
theorem parIn_cons_ne {par : Option Nat} {f a : Nat} {l : List Nat} (h : a ≠ f) :
    parIn par f (a :: l) = parIn par f l := by simp [parIn, h]

/-- In a strictly decreasing stack, the chain of `parIn` from a frame lists the frames below it
(C3; Spec 1 §39). -/
theorem chain_parIn : ∀ {F : List Nat}, F.Pairwise (· > ·) → ∀ {f : Nat}, f ∈ F →
    chain (fun g => parIn none g F) f = (F.dropWhile (· != f)).tail
  | [], _, _, hf => absurd hf List.not_mem_nil
  | a :: F, hd, f, hf => by
    obtain ⟨hlt, hdF⟩ := List.pairwise_cons.1 hd
    have hcongr : ∀ i, i < a →
        chain (fun g => parIn none g (a :: F)) i = chain (fun g => parIn none g F) i :=
      fun i hi => chain_congr fun j hj => parIn_cons_ne (by omega)
    by_cases e : a = f
    · subst e
      simp only [List.dropWhile_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
        List.tail_cons]
      cases F with
      | nil => exact chain_none (by simp [parIn])
      | cons b F' =>
        have hb : b < a := hlt b (List.mem_cons_self ..)
        rw [chain_cons (by simp [parIn]) hb, hcongr b hb,
          chain_parIn hdF (List.mem_cons_self ..)]
        simp
    · have hf' : f ∈ F := (List.mem_cons.1 hf).resolve_left (Ne.symm e)
      have hfa : f < a := hlt f hf'
      rw [hcongr f hfa, chain_parIn hdF hf']
      simp [bne_iff_ne, e]

/-- `dropWhile (· != f)` of a list containing `f` starts with `f` (Spec 1 §39). -/
theorem dropWhile_ne_head : ∀ {F : List Nat} {f : Nat}, f ∈ F →
    F.dropWhile (· != f) = f :: (F.dropWhile (· != f)).tail
  | [], _, hf => absurd hf List.not_mem_nil
  | a :: F, f, hf => by
    by_cases e : a = f
    · subst e; simp
    · have hf' : f ∈ F := (List.mem_cons.1 hf).resolve_left (Ne.symm e)
      simp only [List.dropWhile_cons, bne_iff_ne, ne_eq, e, not_false_eq_true, ↓reduceIte]
      exact dropWhile_ne_head hf'

/-- `dropWhile (· != f)` of a list without `f` is empty (Spec 1 §39). -/
theorem dropWhile_ne_nil : ∀ {F : List Nat} {f : Nat}, f ∉ F → F.dropWhile (· != f) = []
  | [], _, _ => rfl
  | a :: F, f, hf => by
    have e : a ≠ f := fun e => hf (e ▸ List.mem_cons_self ..)
    simp only [List.dropWhile_cons, bne_iff_ne, ne_eq, e, not_false_eq_true, ↓reduceIte]
    exact dropWhile_ne_nil fun h => hf (List.mem_cons_of_mem _ h)

/-- A filter rejecting every element is empty (C2). -/
theorem filter_nil_of {α : Type} {p : α → Bool} : ∀ {l : List α}, (∀ a ∈ l, p a = false) →
    l.filter p = []
  | [], _ => rfl
  | a :: l, h => by
    rw [List.filter_cons, h a (List.mem_cons_self ..)]
    exact filter_nil_of fun b hb => h b (List.mem_cons_of_mem _ hb)

/-! ## Single-context states (C24) -/

/-- The initial context is live, without parent, and no other context is live (C24): a
single-context state (`SC.Single`), or a state reached once every additional context has
terminated, their identities remaining with the completed lifecycle state (C24, last paragraph). -/
def SC.Sole (s : SC) : Prop :=
  (∃ stk, s.C[0]? = some ⟨stk, .live, none⟩) ∧ ∀ c, s.Live c → c = 0

section Single

variable {s : SC}

/-- The stack of the context of a single-context state (C24). -/
theorem single_C (hs : s.Single) : s.C = [⟨s.stk 0, .live, none⟩] := by
  obtain ⟨stk, hC⟩ := hs; rw [hC]; simp [SC.stk, hC]

/-- In a single-context state, the initial context is the only live context (C24). -/
theorem SC.Single.sole (hs : s.Single) : s.Sole := by
  have hC := single_C hs
  refine ⟨⟨s.stk 0, by rw [hC]; rfl⟩, fun c hc => ?_⟩
  unfold SC.Live at hc; rw [hC] at hc
  cases c with
  | zero => rfl
  | succ n => simp [OptP] at hc

/-- The initial context of a state whose only live context is the initial one (C24). -/
theorem sole_C0 (hs : s.Sole) : s.C[0]? = some ⟨s.stk 0, .live, none⟩ := by
  obtain ⟨⟨stk, h0⟩, -⟩ := hs
  rw [h0]; simp [SC.stk, h0]

/-- The context of a single-context state is live (C24). -/
theorem single_live (hs : s.Sole) : s.Live 0 := by
  rw [SC.Live, sole_C0 hs]; simp [OptP]

/-- A context other than the initial one has an empty stack (C2, C24). -/
theorem sole_stk (hs : s.Sole) {c : Nat} (hc : c ≠ 0) : s.stk c = [] := by
  unfold SC.stk
  cases h : s.C[c]? with
  | none => rfl
  | some x =>
    simp only
    split
    · rename_i hl; exact absurd (hs.2 c (by simp [SC.Live, h, OptP, hl])) hc
    · rfl

/-- The context list of a state whose only live context is the initial one starts with the initial
context (C24). -/
theorem sole_cons (hs : s.Sole) :
    ∃ x0 rest, s.C = x0 :: rest ∧ x0 = ⟨s.stk 0, .live, none⟩ := by
  have h0 := sole_C0 hs
  cases e : s.C with
  | nil => rw [e] at h0; cases h0
  | cons x0 rest => rw [e] at h0; exact ⟨x0, rest, rfl, Option.some.inj h0⟩

/-- The identities of the contexts of a state whose initial context exists (C2). -/
theorem sole_length (hs : s.Sole) : ∃ n, s.C.length = n + 1 :=
  ⟨s.C.length - 1, by have := lt_of_getElem? (sole_C0 hs); omega⟩

/-- A `flatMap` whose every image is empty is empty. -/
theorem flatMap_nil_of {f : Nat → List Nat} : ∀ {l : List Nat}, (∀ c ∈ l, f c = []) →
    l.flatMap f = []
  | [], _ => rfl
  | a :: l, h => by
    rw [List.flatMap_cons, h a (List.mem_cons_self ..), List.nil_append]
    exact flatMap_nil_of fun c hc => h c (List.mem_cons_of_mem _ hc)

/-- The live frames of a single-context state are its stack (C24). -/
theorem single_frames (hs : s.Sole) : s.frames = s.stk 0 := by
  obtain ⟨n, hn⟩ := sole_length hs
  have h : (List.map Nat.succ (List.range n)).flatMap s.stk = [] := flatMap_nil_of fun c hc => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hc
    exact sole_stk hs (Nat.succ_ne_zero i)
  unfold SC.frames
  rw [hn, List.range_succ_eq_map, List.flatMap_cons, h, List.append_nil]

/-- The flat state of a single-context state is its projection (C24). -/
theorem single_flat (hs : s.Sole) : s.flat = s.toS3 := by
  simp only [SC.flat, SC.toS3, single_frames hs]

/-- The view of the context of a single-context state is its projection (C2, C24). -/
theorem single_view (hs : s.Sole) : s.view 0 = s.toS3 := by
  have h0 : s.Live 0 := single_live hs
  simp only [SC.view, h0, ite_true, single_flat hs, single_frames hs, SC.toS3]
  congr 1
  have : (s.stk 0).filter (fun f => decide (f ∉ s.stk 0)) = [] :=
    filter_nil_of (fun f hf => by simpa using hf)
  rw [this, List.append_nil]

/-- The parent relation of a single-context state follows its stack (C3, C24). -/
theorem single_parC (hs : s.Sole) (f : Nat) : s.parC f = parIn none f (s.stk 0) := by
  have hp : s.ctxParent 0 = none := by simp [SC.ctxParent, sole_C0 hs]
  obtain ⟨n, hn⟩ := sole_length hs
  have hrest : ∀ c ∈ List.map Nat.succ (List.range n), (s.stk c).contains f = false := by
    intro c hc
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hc
    rw [sole_stk hs (Nat.succ_ne_zero i)]; rfl
  by_cases hf : f ∈ s.stk 0
  · have : s.ctxOf f = some 0 := by
      simp only [SC.ctxOf, hn, List.range_succ_eq_map, List.find?_cons]
      simp [hf]
    simp [SC.parC, this, hp]
  · have : s.ctxOf f = none := by
      simp only [SC.ctxOf, hn, List.range_succ_eq_map, List.find?_cons]
      have h0 : (s.stk 0).contains f = false := by simpa using hf
      rw [h0]
      exact List.find?_eq_none.2 fun c hc => by rw [hrest c hc]; exact Bool.false_ne_true
    simp [SC.parC, this, parIn_not_mem hf]

/-- C24, C3: on a single-context state with a strictly decreasing stack, `ancestorC` is `ancestor`
of Spec 1 §39 on the stack. -/
theorem single_ancestorC (hs : s.Sole) (hd : (s.stk 0).Pairwise (· > ·)) (g f : Nat) :
    s.ancestorC g f ↔ ancestor (s.stk 0) g f := by
  unfold SC.ancestorC ancestor
  rw [single_frames hs, show s.parC = fun g => parIn none g (s.stk 0) from
    funext (single_parC hs)]
  by_cases hf : f ∈ s.stk 0
  · rw [chain_parIn hd hf, dropWhile_ne_head hf]
    simp [hf]
  · rw [dropWhile_ne_nil hf]; simp [hf]

/-- The head of a strictly decreasing list bounds its elements (Spec 1 §49, last paragraph). -/
theorem le_head_of_pairwise {h : Nat} {l : List Nat} (hd : (h :: l).Pairwise (· > ·)) :
    ∀ b ∈ h :: l, b ≤ h := by
  intro b hb
  rcases List.mem_cons.1 hb with rfl | hb
  · exact Nat.le_refl _
  · exact Nat.le_of_lt ((List.pairwise_cons.1 hd).1 b hb)

/-- A duplicate-free stack whose `parIn` links decrease is strictly decreasing (C3; Spec 1
§49, last paragraph). -/
theorem pairwise_of_parIn : ∀ {F : List Nat}, F.Nodup →
    (∀ f g, parIn none f F = some g → g < f) → F.Pairwise (· > ·)
  | [], _, _ => List.Pairwise.nil
  | a :: F, hnd, h => by
    obtain ⟨hna, hndF⟩ := List.nodup_cons.1 hnd
    have ih : F.Pairwise (· > ·) := pairwise_of_parIn hndF fun f g hg => by
      by_cases hf : f ∈ F
      · have hne : a ≠ f := fun e => hna (by rw [e]; exact hf)
        exact h f g (by rw [parIn_cons_ne hne]; exact hg)
      · rw [parIn_not_mem hf] at hg; cases hg
    refine List.pairwise_cons.2 ⟨?_, ih⟩
    cases F with
    | nil => intro b hb; cases hb
    | cons b' F' =>
      have hb' : b' < a := h a b' (by simp [parIn])
      intro b hb
      exact Nat.lt_of_le_of_lt (le_head_of_pairwise ih b hb) hb'

/-- The frame structure of a single-context state makes its stack strictly decreasing (C3;
Spec 1 §49, last paragraph). -/
theorem single_decreasing (hs : s.Sole) (hfr : FramesC s) : (s.stk 0).Pairwise (· > ·) := by
  refine pairwise_of_parIn (SC.stk_nodup hfr.nodup 0) fun f g hg => ?_
  by_cases hf : f ∈ s.stk 0
  · exact (hfr.parent f (by rw [single_frames hs]; exact hf) g
      (by rw [single_parC hs]; exact hg)).2
  · rw [parIn_not_mem hf] at hg; cases hg

/-- `EffAnchorOKC` of a single-context state is `EffAnchorOK` of its projection (Spec 1 §44;
C24). -/
theorem single_effAnchorOKC (hs : s.Sole) (hd : (s.stk 0).Pairwise (· > ·)) (x : Nat)
    (fd : Option Nat) : EffAnchorOKC s x fd ↔ EffAnchorOK s.toS3 x fd := by
  unfold EffAnchorOKC EffAnchorOK
  rw [single_flat hs]
  show OptP (s.toS3.A[s.toS3.effAnchor x]?) _ False ↔ _
  cases s.toS3.A[s.toS3.effAnchor x]? with
  | none => exact Iff.rfl
  | some z =>
    simp only [OptP]
    cases s.toS3.hframe z.holder with
    | none => exact Iff.rfl
    | some g =>
      simp only
      cases fd with
      | none => exact Iff.rfl
      | some f => exact single_ancestorC hs hd g f

/-- `AnchorOrderC` of a single-context state is `AnchorOrder` of its projection (Spec 1 §44;
C24). -/
theorem single_anchorOrderC (hs : s.Sole) (hd : (s.stk 0).Pairwise (· > ·)) :
    AnchorOrderC s ↔ AnchorOrder s.toS3 := by
  unfold AnchorOrderC AnchorOrder
  rw [single_flat hs]
  exact forall_congr' fun q => imp_congr_right fun _ => forall₂_congr fun x _ =>
    single_effAnchorOKC hs hd x _

/-- `AnchorOrderHeldC` of a single-context state is `AnchorOrderHeld` of its projection (Spec 1
§44; C24). -/
theorem single_anchorOrderHeldC (hs : s.Sole) (hd : (s.stk 0).Pairwise (· > ·)) :
    AnchorOrderHeldC s ↔ AnchorOrderHeld s.toS3 := by
  unfold AnchorOrderHeldC AnchorOrderHeld
  rw [single_flat hs]
  exact forall_congr' fun q => imp_congr_right fun _ => forall_congr' fun x =>
    forall_congr' fun y => imp_congr_right fun _ => imp_congr_right fun _ =>
      imp_congr_right fun _ => single_effAnchorOKC hs hd x _

/-- C24: on a single-context state, the re-indexed kernel invariant is the frame structure together
with the kernel invariant of Spec 1 §57 on the projection. -/
theorem single_kInvC (hs : s.Sole) : KInvC s ↔ FramesC s ∧ KInv s.toS3 := by
  have hv : ∀ c, s.view c = s.toS3 ∨ I4 (s.view c) := fun c => .inr (i4_always _)
  constructor
  · rintro ⟨⟨hfr, hw⟩, ⟨⟨i1, i2, i3, -⟩, hao, hnd⟩, haoh, hno⟩
    have hd := single_decreasing hs hfr
    unfold NoOrphanC at hno
    rw [single_flat hs] at hw i1 i2 i3 hnd hno
    exact ⟨hfr, hw, ⟨⟨i1, i2, i3, i4_always _⟩, (single_anchorOrderC hs hd).1 hao, hnd⟩,
      (single_anchorOrderHeldC hs hd).1 haoh, hno⟩
  · rintro ⟨hfr, hw, ⟨⟨i1, i2, i3, -⟩, hao, hnd⟩, haoh, hno⟩
    have hd := single_decreasing hs hfr
    refine ⟨⟨hfr, by rw [single_flat hs]; exact hw⟩,
      ⟨⟨by rw [single_flat hs]; exact i1, by rw [single_flat hs]; exact i2,
        by rw [single_flat hs]; exact i3, fun c => i4_always _⟩,
        (single_anchorOrderC hs hd).2 hao, by rw [single_flat hs]; exact hnd⟩,
      (single_anchorOrderHeldC hs hd).2 haoh, by unfold NoOrphanC; rw [single_flat hs]; exact hno⟩

/-! ### Results of operations -/

/-- Writing back kernel components keeps a single-context state (C2, C24). -/
theorem single_set (hs : s.Single) (t : S3) : (s.set t).Single := hs

/-- Projection of a write-back whose stack is the stack of the context (C24). -/
theorem toS3_set {t : S3} (hF : t.F = s.stk 0) : (s.set t).toS3 = t := by
  cases t; subst hF; rfl

/-- The stack of context 0 after a write-back is unchanged (C2). -/
theorem stk_set (t : S3) (c : Nat) : (s.set t).stk c = s.stk c := rfl

end Single

/-! ## Inherited operations on single-context states (C24) -/

section Ops

variable {k : K} {s : SC}

/-- An operation run on the view of the single context has the outcomes of Spec 1 on the
projection when its `ok` outcomes keep the stack (C2, C24). -/
theorem viewStep_single {R : S3 → Outcome3 S3 → Prop} (hs : s.Sole)
    (hF : ∀ t', R s.toS3 (.ok t') → t'.F = s.toS3.F) :
    (∀ o, ViewStep R 0 s o → R s.toS3 (omap SC.toS3 o)) ∧
    (∀ o₃, R s.toS3 o₃ → ∃ o, ViewStep R 0 s o ∧ omap SC.toS3 o = o₃) := by
  have hv := single_view hs
  have back : ∀ o₃, R s.toS3 o₃ → omap SC.toS3 (omap s.set o₃) = o₃ := by
    intro o₃ hR
    cases o₃ with
    | ok t => exact congrArg Outcome3.ok (toS3_set (hF t hR))
    | reject => rfl
    | fail => rfl
  refine ⟨fun o ⟨o₃, hR, ho⟩ => ?_, fun o₃ hR => ⟨_, ⟨o₃, hv ▸ hR, rfl⟩, back o₃ hR⟩⟩
  rw [hv] at hR; rw [ho, back o₃ hR]; exact hR

/-- A guarded operation of the single context has the outcomes of Spec 1 on the projection when
its precondition is equivalent and its effect projects to the Spec 1 effect (C24). -/
theorem guarded_single {Pre Pre₃ : Prop} {e : SC} {e₃ : S3} (hp : Pre ↔ Pre₃)
    (he : e.toS3 = e₃) :
    (∀ o, Guarded Pre e o → Guarded Pre₃ e₃ (omap SC.toS3 o)) ∧
    (∀ o₃, Guarded Pre₃ e₃ o₃ → ∃ o, Guarded Pre e o ∧ omap SC.toS3 o = o₃) := by
  refine ⟨fun o h => ?_, fun o₃ h => ?_⟩
  · cases h with
    | ok hpre => rw [omap, he]; exact .ok (hp.1 hpre)
    | reject hn => exact .reject fun h => hn (hp.2 h)
  · cases h with
    | ok hpre => exact ⟨_, .ok (hp.2 hpre), by rw [omap, he]⟩
    | reject hn => exact ⟨_, .reject fun h => hn (hp.1 h), rfl⟩

/-- The `ok` outcomes of the operations that do not read `ancestor` keep the stack (Spec 1
§60–§62, §66–§71, §74, §75 effects). -/
theorem viewOp_F {t t' : S3} {op : KernelOp} (hop : op.Step k t (.ok t'))
    (hnot : ∀ src dst, op ≠ .transfer src dst) (hnd : ∀ q x, op ≠ .depend q x)
    (hns : ∀ a p, op ≠ .store a p) (hne : ∀ ps ls, op ≠ .enter ps ls) (hnx : op ≠ .exit) :
    t'.F = t.F := by
  cases op with
  | transfer => exact absurd rfl (hnot _ _)
  | depend => exact absurd rfl (hnd _ _)
  | store => exact absurd rfl (hns _ _)
  | enter => exact absurd rfl (hne _ _)
  | exit => exact absurd rfl hnx
  | derive => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hop; rfl
  | split => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hop; rfl
  | release a =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hop; unfold releaseEff; split <;> rfl
  | read => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hop; rfl
  | write => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hop; rfl
  | writeShared => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hop; rfl
  | pin => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hop; rfl
  | unpin => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hop; rfl
  | endUse => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hop; rfl
  | free => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hop; rfl
  | alloc => cases hop; rfl

/-- `transfer` of the single context: preconditions (Spec 1 §63; C24). -/
theorem transferPreC_single (hs : s.Sole) (hd : (s.stk 0).Pairwise (· > ·)) {src dst : Nat} :
    TransferPreC k s 0 src dst ↔ TransferPre k s.toS3 src dst := by
  have hv := single_view hs
  have ht : (transferEffC s 0 src dst).toS3 = transferEff s.toS3 src dst := by
    unfold transferEffC; rw [hv]; exact toS3_set rfl
  have hao := single_anchorOrderC (s := transferEffC s 0 src dst) hs hd
  have hef := single_effAnchorOKC (s := transferEffC s 0 src dst) hs hd
  rw [ht] at hao hef
  constructor
  · rintro ⟨a, b, c, d, e, f, g, h, i, j, l, m, n, o, p⟩
    simp only [hv] at a b c d e f g h i j l n o p
    simp only [hef] at n
    exact ⟨a, b, c, d, e, f, g, h, i, j, l, hao.1 m, n, o, p⟩
  · rintro ⟨a, b, c, d, e, f, g, h, i, j, l, m, n, o, p⟩
    simp only [← hef] at n
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hao.2 m, ?_, ?_, ?_⟩ <;>
      simp only [hv] <;> assumption

/-- `depend` of the single context: preconditions (Spec 1 §64; C24). -/
theorem dependPreC_single (hs : s.Sole) (hd : (s.stk 0).Pairwise (· > ·)) {q x : Nat} :
    DependPreC s 0 q x ↔ DependPre s.toS3 q x := by
  have hv := single_view hs
  have hef := single_effAnchorOKC hs hd
  constructor
  · rintro ⟨a, b, c, d⟩
    simp only [hv] at a b c d
    exact ⟨a, b, c, (hef _ _).1 d⟩
  · rintro ⟨a, b, c, d⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [hv]
    · exact a
    · exact b
    · exact c
    · exact (hef _ _).2 d

/-- `store` of the single context: preconditions (Spec 1 §65; C24). -/
theorem storePreC_single (hs : s.Sole) (hd : (s.stk 0).Pairwise (· > ·)) {a p : Nat} :
    StorePreC s 0 a p ↔ StorePre s.toS3 a p := by
  have hv := single_view hs
  have hef := single_effAnchorOKC hs hd
  have ht : (storeEffC s 0 a p).toS3 = storeEff s.toS3 a p := by
    unfold storeEffC; rw [hv]; refine toS3_set ?_
    unfold storeEff; split <;> rfl
  have haoh := single_anchorOrderHeldC (s := storeEffC s 0 a p) hs hd
  rw [ht] at haoh
  constructor
  · rintro ⟨a₁, b, c, d, e, f, g, h, i⟩
    simp only [hv] at a₁ b c d e f g h
    exact ⟨a₁, b, c, d, e, f, (hef _ _).1 g, h, haoh.1 i⟩
  · rintro ⟨a₁, b, c, d, e, f, g, h, i⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, haoh.2 i⟩ <;> simp only [hv]
    · exact a₁
    · exact b
    · exact c
    · exact d
    · exact e
    · exact f
    · exact (hef _ _).2 g
    · exact h

/-- `enterFrame` of the single context keeps a single-context state and pushes the new frame
(Spec 1 §72; C24). -/
theorem single_enterEffC (hs : s.Single) (ps : List Nat) (ls : LocalShape) :
    (enterEffC s 0 ps ls).Single ∧ (enterEffC s 0 ps ls).stk 0 = s.nF :: s.stk 0 := by
  have hC := single_C hs
  have : (enterEffC s 0 ps ls).C = [⟨s.nF :: s.stk 0, .live, none⟩] := by
    simp only [enterEffC, hC]; rfl
  exact ⟨⟨_, this⟩, by simp [SC.stk, this]⟩

/-- `enterFrame` of the initial context keeps it the only live context and pushes the new frame
(Spec 1 §72; C24). -/
theorem sole_enterEffC (hs : s.Sole) (ps : List Nat) (ls : LocalShape) :
    (enterEffC s 0 ps ls).Sole ∧ (enterEffC s 0 ps ls).stk 0 = s.nF :: s.stk 0 := by
  obtain ⟨x0, rest, hC, hx⟩ := sole_cons hs
  have hC' : (enterEffC s 0 ps ls).C = { x0 with stack := s.nF :: x0.stack } :: rest := by
    show s.C.modify 0 _ = _; rw [hC]; rfl
  have hC0 : (enterEffC s 0 ps ls).C[0]? = some ⟨s.nF :: s.stk 0, .live, none⟩ := by
    rw [hC', hx]; rfl
  refine ⟨⟨⟨_, hC0⟩, fun c hc => hs.2 c ?_⟩, by unfold SC.stk; rw [hC0]; rfl⟩
  cases c with
  | zero => exact single_live hs
  | succ n => unfold SC.Live at hc ⊢; rw [hC'] at hc; rw [hC]; exact hc

/-- Projection of `enterFrame` of the single context (Spec 1 §72; C24). -/
theorem toS3_enterEffC (hs : s.Sole) (ps : List Nat) (ls : LocalShape) :
    (enterEffC s 0 ps ls).toS3 = enterEff s.toS3 ps ls := by
  have hstk := (sole_enterEffC hs ps ls).2
  have hv := single_view hs
  simp only [SC.toS3, hstk]
  simp only [enterEffC, SC.set, hv]
  rfl

/-- `enterFrame` of the single context: preconditions (Spec 1 §72; C24). -/
theorem enterPreC_single (hs : s.Sole) (hfr : FramesC s) {ps : List Nat} {ls : LocalShape} :
    EnterPreC s 0 ps ls ↔ EnterPre s.toS3 ps ls := by
  have hd := single_decreasing hs hfr
  have hv := single_view hs
  obtain ⟨hs', hstk⟩ := sole_enterEffC hs ps ls
  have hd' : ((enterEffC s 0 ps ls).stk 0).Pairwise (· > ·) := by
    rw [hstk]
    exact List.pairwise_cons.2 ⟨fun f hf => hfr.bound f (by rw [single_frames hs]; exact hf), hd⟩
  have hv' : (enterEffC s 0 ps ls).view 0 = enterEff s.toS3 ps ls := by
    rw [single_view hs', toS3_enterEffC hs]
  have haoh := single_anchorOrderHeldC hs' hd'
  rw [toS3_enterEffC hs] at haoh
  constructor
  · rintro ⟨a, b, c, d, e⟩
    simp only [hv] at b
    rw [hv'] at d
    exact ⟨a, b, c, d, haoh.1 e⟩
  · rintro ⟨a, b, c, d, e⟩
    refine ⟨a, by simp only [hv]; exact b, c, by rw [hv']; exact d, haoh.2 e⟩

/-- `exitFrameC` of the single context keeps a single-context state, pops the stack, and
reparents nothing (Spec 1 §73; C6, C24). -/
theorem single_exitEffC (hs : s.Single) :
    (exitEffC s 0).Single ∧ (exitEffC s 0).stk 0 = (s.stk 0).tail := by
  have hC := single_C hs
  have : (exitEffC s 0).C = [⟨(s.stk 0).tail, .live, none⟩] := by
    simp only [exitEffC, hC, reparent]; simp
  exact ⟨⟨_, this⟩, by simp [SC.stk, this]⟩

/-- `exitFrameC` of the initial context keeps it the only live context and pops the stack
(Spec 1 §73; C6, C24). -/
theorem sole_exitEffC (hs : s.Sole) :
    (exitEffC s 0).Sole ∧ (exitEffC s 0).stk 0 = (s.stk 0).tail := by
  obtain ⟨x0, rest, hC, hx⟩ := sole_cons hs
  have hC' : (exitEffC s 0).C = List.map (fun x => if x.life = .live ∧
      x.parent = some ((s.stk 0).headD 0) then { x with parent := some ((s.stk 0).tail.headD 0) }
      else x) ({ x0 with stack := x0.stack.tail } :: rest) := by
    show List.map _ (s.C.modify 0 _) = _; rw [hC]; rfl
  have hC0 : (exitEffC s 0).C[0]? = some ⟨(s.stk 0).tail, .live, none⟩ := by
    rw [hC', hx]; rfl
  refine ⟨⟨⟨_, hC0⟩, fun c hc => hs.2 c ?_⟩, by unfold SC.stk; rw [hC0]; rfl⟩
  cases c with
  | zero => exact single_live hs
  | succ n =>
    unfold SC.Live at hc ⊢
    rw [hC', List.map_cons, List.getElem?_cons_succ, List.getElem?_map] at hc
    rw [hC, List.getElem?_cons_succ]
    cases h : rest[n]? with
    | none => rw [h] at hc; exact hc
    | some y =>
      rw [h] at hc
      change (if y.life = .live ∧ _ then _ else y).life = .live at hc
      change y.life = .live
      split at hc <;> exact hc

/-- Projection of `exitFrameC` of the single context (Spec 1 §73; C24). -/
theorem toS3_exitEffC (hs : s.Sole) : (exitEffC s 0).toS3 = exitEff s.toS3 := by
  have hstk := (sole_exitEffC hs).2
  have hv := single_view hs
  simp only [SC.toS3, hstk]
  simp only [exitEffC, SC.set, hv]
  rfl

/-- `exitFrameC` of the single context: preconditions (Spec 1 §73; C24). -/
theorem exitPreC_single (hs : s.Sole) (hd : (s.stk 0).Pairwise (· > ·)) :
    ExitPreC k s 0 ↔ ExitPre k s.toS3 := by
  have hv := single_view hs
  obtain ⟨hs', hstk⟩ := sole_exitEffC hs
  have hd' : ((exitEffC s 0).stk 0).Pairwise (· > ·) := by rw [hstk]; exact hd.sublist (List.tail_sublist _)
  have haoh := single_anchorOrderHeldC hs' hd'
  rw [toS3_exitEffC hs] at haoh
  constructor
  · rintro ⟨a, b, c, d, e⟩
    simp only [hv] at b c d
    exact ⟨a, b, c, d, haoh.1 e⟩
  · rintro ⟨a, b, c, d, e⟩
    refine ⟨a, ?_, ?_, ?_, haoh.2 e⟩ <;> simp only [hv] <;> assumption

/-- Theorem 1 (C24): on a state whose only live context is the initial one, with the frame structure
`FramesC`, every inherited operation O1–O16 executed by the context has exactly the outcomes of Spec
1 (§58, §60–§75) on the projection `SC.toS3`, outcome by outcome. Fragment: states whose only live
context is the initial one (`SC.Sole`), single-context states included; operations O1–O16. -/
theorem conservative_op (hs : s.Sole) (hfr : FramesC s) (op : KernelOp) :
    (∀ o, opStepC k op 0 s o → op.Step k s.toS3 (omap SC.toS3 o)) ∧
    (∀ o₃, op.Step k s.toS3 o₃ → ∃ o, opStepC k op 0 s o ∧ omap SC.toS3 o = o₃) := by
  have hd := single_decreasing hs hfr
  have hv := single_view hs
  cases op with
  | transfer src dst =>
    exact guarded_single (transferPreC_single hs hd)
      (by unfold transferEffC; rw [hv]; exact toS3_set rfl)
  | depend q x =>
    exact guarded_single (dependPreC_single hs hd)
      (by unfold dependEffC; rw [hv]; exact toS3_set rfl)
  | store a p =>
    exact guarded_single (storePreC_single hs hd)
      (by unfold storeEffC; rw [hv]; refine toS3_set ?_; unfold storeEff; split <;> rfl)
  | enter ps ls => exact guarded_single (enterPreC_single hs hfr) (toS3_enterEffC hs ps ls)
  | exit => exact guarded_single (exitPreC_single hs hd) (toS3_exitEffC hs)
  | derive => exact viewStep_single hs fun t' h => viewOp_F h (by simp) (by simp) (by simp) (by simp) (by simp)
  | split => exact viewStep_single hs fun t' h => viewOp_F h (by simp) (by simp) (by simp) (by simp) (by simp)
  | release => exact viewStep_single hs fun t' h => viewOp_F h (by simp) (by simp) (by simp) (by simp) (by simp)
  | read => exact viewStep_single hs fun t' h => viewOp_F h (by simp) (by simp) (by simp) (by simp) (by simp)
  | write => exact viewStep_single hs fun t' h => viewOp_F h (by simp) (by simp) (by simp) (by simp) (by simp)
  | writeShared => exact viewStep_single hs fun t' h => viewOp_F h (by simp) (by simp) (by simp) (by simp) (by simp)
  | pin => exact viewStep_single hs fun t' h => viewOp_F h (by simp) (by simp) (by simp) (by simp) (by simp)
  | unpin => exact viewStep_single hs fun t' h => viewOp_F h (by simp) (by simp) (by simp) (by simp) (by simp)
  | endUse => exact viewStep_single hs fun t' h => viewOp_F h (by simp) (by simp) (by simp) (by simp) (by simp)
  | free => exact viewStep_single hs fun t' h => viewOp_F h (by simp) (by simp) (by simp) (by simp) (by simp)
  | alloc => exact viewStep_single hs fun t' h => viewOp_F h (by simp) (by simp) (by simp) (by simp) (by simp)

/-- C24: an `ok` outcome of an inherited operation O1–O16 executed by the context of a
single-context state is a single-context state whose projection is the Spec 1 effect (§60–§75)
on the projection. -/
theorem conservative_ok (hs : s.Single) (hfr : FramesC s) {op : KernelOp} {s' : SC}
    (h : opStepC k op 0 s (.ok s')) : s'.Single ∧ op.Step k s.toS3 (.ok s'.toS3) := by
  refine ⟨?_, (conservative_op hs.sole hfr op).1 _ h⟩
  cases op with
  | transfer => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; exact hs
  | depend => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; exact hs
  | store => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; exact hs
  | enter => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; exact (single_enterEffC hs _ _).1
  | exit => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; exact (single_exitEffC hs).1
  | derive | split | release | read | write | writeShared | pin | unpin | endUse | free | alloc =>
    obtain ⟨o₃, -, ho⟩ := h
    cases o₃ with
    | ok t => cases ho; exact hs
    | reject => cases ho
    | fail => cases ho

/-- C24: an `ok` outcome of an inherited operation O1–O16 executed by the initial context, when it
is the only live context, keeps it the only live context, and its projection is the Spec 1 effect
(§60–§75) on the projection. -/
theorem conservative_ok_sole (hs : s.Sole) (hfr : FramesC s) {op : KernelOp} {s' : SC}
    (h : opStepC k op 0 s (.ok s')) : s'.Sole ∧ op.Step k s.toS3 (.ok s'.toS3) := by
  refine ⟨?_, (conservative_op hs hfr op).1 _ h⟩
  cases op with
  | transfer => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; exact hs
  | depend => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; exact hs
  | store => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; exact hs
  | enter => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; exact (sole_enterEffC hs _ _).1
  | exit => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; exact (sole_exitEffC hs).1
  | derive | split | release | read | write | writeShared | pin | unpin | endUse | free | alloc =>
    obtain ⟨o₃, -, ho⟩ := h
    cases o₃ with
    | ok t => cases ho; exact hs
    | reject => cases ho
    | fail => cases ho

end Ops

/-! ## The reachable sequential domain (C24) -/

/-- A kernel step of Spec 1 keeps the stack, pushes `nF` (§72) or pops the top (§73). -/
theorem kstep_F {k : K} {t t' : S3} (h : KStep k t t') :
    t'.F = t.F ∨ t'.F = t.nF :: t.F ∨ t'.F = t.F.tail := by
  cases h with
  | derive h => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; exact .inl rfl
  | split h => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; exact .inl rfl
  | release h =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; left; unfold releaseEff; split <;> rfl
  | transfer h => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; exact .inl rfl
  | depend h => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; exact .inl rfl
  | enter h => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; exact .inr (.inl rfl)
  | exit h => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; exact .inr (.inr rfl)
  | read h => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; exact .inl rfl
  | write h => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; exact .inl rfl
  | writeShared h => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; exact .inl rfl
  | pin h => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; exact .inl rfl
  | unpin h => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; exact .inl rfl
  | endUse h => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; exact .inl rfl
  | free h => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; exact .inl rfl
  | alloc h => cases h; exact .inl rfl
  | store h =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; left; unfold storeEff; split <;> rfl

/-- The stack of every state reachable in Spec 1 (§57) is strictly decreasing: `enterFrame`
pushes the fresh `nF` (§72, §49.1). -/
theorem reachable_decreasing {k : K} {statics : Statics} {t : S3} (hdd : DDSound k)
    (hst : StaticsOK statics) (h : Reachable k statics t) : t.F.Pairwise (· > ·) := by
  induction h with
  | init => simp [S3.init]
  | @step t t' hr hs ih =>
    rcases kstep_F hs with e | e | e <;> rw [e]
    · exact ih
    · have hw := (reachable_kinv hdd hst hr).1
      exact List.pairwise_cons.2 ⟨fun f hf => hw.frames.2.2 f hf, ih⟩
    · exact ih.sublist (List.tail_sublist _)

/-- `parIn` in a strictly decreasing list gives a smaller element of the list (C3). -/
theorem parIn_lt : ∀ {F : List Nat}, F.Pairwise (· > ·) → ∀ {f g : Nat},
    parIn none f F = some g → g ∈ F ∧ g < f
  | [], _, _, _, h => by cases h
  | a :: F, hd, f, g, h => by
    obtain ⟨hlt, hdF⟩ := List.pairwise_cons.1 hd
    by_cases e : a = f
    · subst e
      cases F with
      | nil => simp [parIn] at h
      | cons b F' =>
        simp only [parIn, ↓reduceIte, List.head?_cons, Option.some_or, Option.some.injEq] at h
        subst h
        exact ⟨List.mem_cons_of_mem _ (List.mem_cons_self ..), hlt _ (List.mem_cons_self ..)⟩
    · rw [parIn_cons_ne e] at h
      obtain ⟨hm, hg⟩ := parIn_lt hdF h
      exact ⟨List.mem_cons_of_mem _ hm, hg⟩

/-- Projection of the single-context state of an `S3` (C24). -/
theorem toS3_ofS3 (t : S3) : (SC.ofS3 t).toS3 = t := by cases t; rfl

/-- C24: every state reachable in Spec 1 (§57) is the projection of a single-context state with the
frame structure `FramesC`, the domain of `conservative_op`; with `single_kInvC`, the re-indexed
kernel invariant holds there. -/
theorem reachable_single {k : K} {statics : Statics} {t : S3} (hdd : DDSound k)
    (hst : StaticsOK statics) (h : Reachable k statics t) :
    (SC.ofS3 t).Single ∧ FramesC (SC.ofS3 t) ∧ (SC.ofS3 t).toS3 = t ∧ KInvC (SC.ofS3 t) := by
  have hw := (reachable_kinv hdd hst h).1
  have hd := reachable_decreasing hdd hst h
  have hs : (SC.ofS3 t).Single := ⟨_, rfl⟩
  have hstk : (SC.ofS3 t).stk 0 = t.F := rfl
  have hfr : FramesC (SC.ofS3 t) := by
    have hlt : ∀ c, (SC.ofS3 t).Live c → c = 0 := fun c hc => by
      unfold SC.Live at hc; unfold OptP at hc; split at hc
      · rename_i x hx
        have := lt_of_getElem? hx; simp [SC.ofS3] at this; exact this
      · exact hc.elim
    refine ⟨by simp [SC.ofS3, OptP], fun c hc => ?_, ?_, ?_, fun c h0 hc => absurd (hlt c hc) h0,
      fun f hf g hg => ?_⟩
    · rw [hlt c hc, hstk]; exact hw.frames.1
    · rw [single_frames hs.sole, hstk]; exact hw.frames.2.1
    · rw [single_frames hs.sole, hstk]; exact hw.frames.2.2
    · rw [single_parC hs.sole, hstk] at hg
      rw [single_frames hs.sole, hstk]
      exact parIn_lt hd hg
  refine ⟨hs, hfr, toS3_ofS3 t, (single_kInvC hs.sole).2 ⟨hfr, ?_⟩⟩
  rw [toS3_ofS3]; exact reachable_kinv hdd hst h

end Ern.ConcurrencyModel
