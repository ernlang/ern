import Ern.MemoryModel.Access.Main

/-!
# Concurrent authority machine: state, frames, invariants

Exploratory formalization of the concurrent state `S_C = (C, F_C, P, I, A, D)` of the working
candidate `ERN_Concurrency_Model_WC4.md` (WC4 C1–C3, C20) on top of the frozen kernel of
`specs/ERN_Memory_Model_Specification_v0.1.md` (Spec 1 §38–§45, §49–§57).

* contexts with lifecycle states, local stacks and the parent of their initial frame (WC4 C1–C3);
* globally live frames, current frame of a context, extended parent relation `parC` and
  `ancestorC` (WC4 C3);
* the `S3` seen by an executing context (`SC.view`, WC4 C2: current frame = top of its stack,
  liveness = globally live frames), the kernel components alone (`SC.flat`), and the projection
  `SC.toS3` on single-context states (WC4 C24);
* `ConcurrentWF`, `Inv3C`, `AnchorOrderC`, `AnchorOrderHeldC`, `NoOrphanC` (WC4 C20; Spec 1 §44,
  §49–§57 re-indexed);
* membership congruence: the kernel invariants of Spec 1 that read the stack only through
  membership agree on every view (WC4 C2).
-/

namespace Ern.Concurrency

open Ern.MemoryModel.Access

/-! ## State (WC4 C1–C3) -/

/-- Lifecycle state of an execution context (WC4 C2, C7, C8): live, or completed. -/
inductive Life where
  | live
  | done
deriving DecidableEq, Repr

/-- Execution context (WC4 C1–C3): its local frame stack, current frame first; its lifecycle
state; the parent of its initial frame (`none` for the initial context, whose initial frame is
the base frame of Spec 1 §39). -/
structure Ctx where
  stack : List Nat
  life : Life
  parent : Option Nat
deriving DecidableEq, Repr

/-- `S_C = (C, F_C, P, I, A, D)` (WC4 C2). `C` lists the contexts by identity (their index); their
stacks and the parents of their initial frames form `F_C`; `P`, `I`, `A`, `D` keep their Spec 1
meaning (§38); `nF`, `dead` and `pins` are the auxiliary components of `S3` (Spec 1 §38). -/
structure SC where
  C : List Ctx
  nF : Nat
  P : List Place
  I : Nat → InitSt
  A : List Authority
  D : Nat → List Nat
  dead : Nat → Bool
  pins : List PinOb

/-- Context `c` is live (WC4 C2). -/
def SC.Live (s : SC) (c : Nat) : Prop := OptP (s.C[c]?) (fun x => x.life = .live) False

/-- Decidability of `SC.Live` (WC4 C2). -/
instance (s : SC) (c : Nat) : Decidable (s.Live c) := by unfold SC.Live; infer_instance

/-- Local stack of context `c` if it is live, empty otherwise (WC4 C2, C3). -/
def SC.stk (s : SC) (c : Nat) : List Nat :=
  match s.C[c]? with
  | some x => if x.life = .live then x.stack else []
  | none => []

/-- Parent of the initial frame of context `c` (WC4 C3). -/
def SC.ctxParent (s : SC) (c : Nat) : Option Nat := (s.C[c]?).bind (·.parent)

/-- Globally live frames: the frames of the stacks of live contexts (WC4 C2). -/
def SC.frames (s : SC) : List Nat := (List.range s.C.length).flatMap s.stk

/-- The kernel components of `s` as an `S3` whose stack lists the globally live frames (WC4 C2:
references to live frames consider the globally live frame structure). -/
def SC.flat (s : SC) : S3 :=
  { F := s.frames, nF := s.nF, P := s.P, I := s.I, A := s.A, D := s.D, dead := s.dead,
    pins := s.pins }

/-- The `S3` seen by executing context `c` (WC4 C2): the stack of `c` first, so that the current
frame is the top of its local stack, followed by the other globally live frames. It is the `S₃`
view of WC4 C2 (candidate P1) on which `K.Satisfiable` of an `alloc` executed by `c` is evaluated
(`alloc_ok_satisfiable`, `alloc_fail_unsatisfiable`). -/
def SC.view (s : SC) (c : Nat) : S3 :=
  { s.flat with F := s.stk c ++ s.frames.filter fun f => decide (f ∉ s.stk c) }

/-- Kernel components of an `S3` written back into `s`; contexts unchanged (WC4 C2). -/
def SC.set (s : SC) (t : S3) : SC :=
  { s with nF := t.nF, P := t.P, I := t.I, A := t.A, D := t.D, dead := t.dead, pins := t.pins }

/-! ## Single-context states (WC4 C24) -/

/-- Single-context state (WC4 C24): exactly one context, the initial one, live, without
parent. -/
def SC.Single (s : SC) : Prop := ∃ stk, s.C = [⟨stk, .live, none⟩]

/-- Projection of a state to `S3` (WC4 C24): the stack of context 0. -/
def SC.toS3 (s : SC) : S3 :=
  { F := s.stk 0, nF := s.nF, P := s.P, I := s.I, A := s.A, D := s.D, dead := s.dead,
    pins := s.pins }

/-- The single-context state of an `S3` (WC4 C24). -/
def SC.ofS3 (t : S3) : SC :=
  { C := [⟨t.F, .live, none⟩], nF := t.nF, P := t.P, I := t.I, A := t.A, D := t.D,
    dead := t.dead, pins := t.pins }

/-! ## Extended frame-parent relation and ancestry (WC4 C3) -/

/-- Parent of frame `f` within a stack whose initial frame has parent `par`: the next frame of
the stack, or `par` for the initial frame; `none` if `f` is not in the stack (WC4 C3; Spec 1
§39). -/
def parIn (par : Option Nat) (f : Nat) : List Nat → Option Nat
  | [] => none
  | a :: rest => if a = f then rest.head?.or par else parIn par f rest

/-- The live context whose stack contains `f` (WC4 C3: frame identities are globally unique). -/
def SC.ctxOf (s : SC) (f : Nat) : Option Nat :=
  (List.range s.C.length).find? fun c => (s.stk c).contains f

/-- Extended frame-parent relation `parC` (WC4 C3): the parent of a live frame, following the
links across contexts; `none` for the base frame and for frames that are not live. -/
def SC.parC (s : SC) (f : Nat) : Option Nat :=
  (s.ctxOf f).bind fun c => parIn (s.ctxParent c) f (s.stk c)

/-- Extended `ancestor_C(f₁, f₂)` (WC4 C3; Spec 1 §39): `f₂` is live and `f₁` is `f₂` or one of
its ancestors along `parC`. Chains follow links to smaller identities (Spec 1 §49, last
paragraph: identity order represents well-foundedness, required by `FramesC.parent`). -/
def SC.ancestorC (s : SC) (f₁ f₂ : Nat) : Prop :=
  f₂ ∈ s.frames ∧ (f₁ = f₂ ∨ f₁ ∈ chain s.parC f₂)

/-- Decidability of `ancestorC` (WC4 C3). -/
instance (s : SC) (f₁ f₂ : Nat) : Decidable (s.ancestorC f₁ f₂) := by
  unfold SC.ancestorC; infer_instance

/-! ## Anchor order on the extended ancestry (Spec 1 §44, §54 re-indexed; WC4 C2, C3) -/

/-- Spec 1 §44 re-indexed (WC4 C2, C3): the frame of the effective anchor of `x` exists and is
`fd` or one of its ancestors along `ancestorC`. -/
def EffAnchorOKC (s : SC) (x : Nat) (fd : Option Nat) : Prop :=
  OptP (s.A[s.flat.effAnchor x]?) (fun z => OptP (s.flat.hframe z.holder)
    (fun g => OptP fd (fun f => s.ancestorC g f) False) False) False

/-- Decidability of `EffAnchorOKC` (Spec 1 §44). -/
instance (s : SC) (x : Nat) (fd : Option Nat) : Decidable (EffAnchorOKC s x fd) := by
  unfold EffAnchorOKC; infer_instance

/-- `AnchorOrder` re-indexed (Spec 1 §44, §54; WC4 C2): for every anchor `x ∈ D(q)` of a usable
place `q`, the frame of the effective anchor of `x` is an `ancestorC` of the frame of `q`. -/
def AnchorOrderC (s : SC) : Prop :=
  ∀ q, s.flat.Usable q → ∀ x ∈ s.D q, EffAnchorOKC s x (s.flat.pframe q)

/-- `AnchorOrderC` read on the places of `P` (decision procedure for Spec 1 §44). -/
theorem anchorOrderC_iff {s : SC} : AnchorOrderC s ↔
    ∀ q ∈ List.range s.P.length, s.flat.Usable q → ∀ x ∈ s.D q,
      EffAnchorOKC s x (s.flat.pframe q) :=
  ⟨fun h q _ hq => h q hq, fun h q hq => h q (List.mem_range.2 hq.lt) hq⟩

/-- Decidability of `AnchorOrderC` (Spec 1 §44). -/
instance (s : SC) : Decidable (AnchorOrderC s) := decidable_of_iff _ anchorOrderC_iff.symm

/-- `AnchorOrderHeld` re-indexed (Spec 1 §44, §54; WC4 C2): the rule of `AnchorOrderC` for every
active authority held by a usable place `q`. -/
def AnchorOrderHeldC (s : SC) : Prop :=
  ∀ q, s.flat.Usable q → ∀ (x : Nat) (y : Authority), s.A[x]? = some y → y.active = true →
    y.holder = .place q → EffAnchorOKC s x (s.flat.pframe q)

/-- `AnchorOrderHeldC` read on the places of `P` and the authorities of `A` (decision procedure
for Spec 1 §44). -/
theorem anchorOrderHeldC_iff {s : SC} : AnchorOrderHeldC s ↔
    ∀ q ∈ List.range s.P.length, s.flat.Usable q → ∀ x ∈ List.range s.A.length,
      OptP (s.A[x]?) (fun y => y.active = true → y.holder = .place q →
        EffAnchorOKC s x (s.flat.pframe q)) True := by
  constructor
  · intro h q _ hq x _
    unfold OptP; split
    · rename_i y hy; exact h q hq x y hy
    · trivial
  · intro h q hq x y hy ya hh
    have := h q (List.mem_range.2 hq.lt) hq x (List.mem_range.2 (lt_of_getElem? hy))
    simp only [OptP, hy] at this; exact this ya hh

/-- Decidability of `AnchorOrderHeldC` (Spec 1 §44). -/
instance (s : SC) : Decidable (AnchorOrderHeldC s) :=
  decidable_of_iff _ anchorOrderHeldC_iff.symm

/-! ## Invariants (WC4 C3, C20; Spec 1 §49–§57 re-indexed) -/

/-- Frame structure of `S_C` (WC4 C3, C20; Spec 1 §49.1 re-indexed: "the stack" read as the
globally live frames). -/
structure FramesC (s : SC) : Prop where
  /-- WC4 C3: the initial context, context 0, is live and its initial frame, the base frame of
  Spec 1 §39, has no parent. -/
  initial : OptP (s.C[0]?) (fun x => x.life = .live ∧ x.parent = none) False
  /-- WC4 C3: every live context has a nonempty local stack. -/
  nonempty : ∀ c, s.Live c → s.stk c ≠ []
  /-- WC4 C3: frame identities are globally unique; Spec 1 §49.1: duplicate-free. -/
  nodup : s.frames.Nodup
  /-- Spec 1 §49.1: every frame has a valid identity (below `nF`). -/
  bound : ∀ f ∈ s.frames, f < s.nF
  /-- WC4 C3: the initial frame of a non-initial live context has a parent (the frame that
  created the context, or its reparenting target, WC4 C6). -/
  rooted : ∀ c, c ≠ 0 → s.Live c → s.ctxParent c ≠ none
  /-- Spec 1 §49.1 re-indexed, WC4 C3: the parent of a live frame is live; the parent precedes
  its child, which represents well-foundedness (Spec 1 §49, last paragraph). -/
  parent : ∀ f ∈ s.frames, ∀ g, s.parC f = some g → g ∈ s.frames ∧ g < f

/-- `ConcurrentWF` (WC4 C20): the frame structure of `FramesC` and `WF3` (Spec 1 §49.1–§49.8)
read with "the stack" as the globally live frames. -/
def ConcurrentWF (s : SC) : Prop := FramesC s ∧ WF3 s.flat

/-- `I1 ∧ I2 ∧ I3 ∧ I4` re-indexed (Spec 1 §50–§53, §57; WC4 C2): `I4` reads `Read3Pre`, which
depends on the current frame, so it is required for every executing context. -/
def Inv3baseC (s : SC) : Prop :=
  I1 s.flat ∧ I2 s.flat ∧ I3 s.flat ∧ ∀ c, I4 (s.view c)

/-- `Inv3 = I1 ∧ I2 ∧ I3 ∧ I4 ∧ AnchorOrder ∧ NoDangling` re-indexed (Spec 1 §57; WC4 C2). -/
def Inv3C (s : SC) : Prop := Inv3baseC s ∧ AnchorOrderC s ∧ NoDangling s.flat

/-- `NoOrphan` re-indexed (Spec 1 §54; WC4 C2): chains start at a globally live frame. -/
def NoOrphanC (s : SC) : Prop := NoOrphan s.flat

/-- The kernel invariant of Spec 1 §57 re-indexed (WC4 C20, C23):
`ConcurrentWF ∧ Inv3 ∧ AnchorOrderHeld ∧ NoOrphan`. -/
def KInvC (s : SC) : Prop := ConcurrentWF s ∧ Inv3C s ∧ AnchorOrderHeldC s ∧ NoOrphanC s

/-! ## Views: membership and current frame (WC4 C2) -/

/-- Unfolding of `stk` (WC4 C2). -/
theorem SC.stk_of {s : SC} {c : Nat} {x : Ctx} (h : s.C[c]? = some x) (hl : x.life = .live) :
    s.stk c = x.stack := by simp [SC.stk, h, hl]

/-- A context with a nonempty stack is live (WC4 C2). -/
theorem SC.live_of_stk {s : SC} {c : Nat} (h : s.stk c ≠ []) : s.Live c := by
  unfold SC.stk at h; unfold SC.Live
  split at h
  · rename_i x hx; rw [hx]; simp only [OptP]; split at h
    · assumption
    · exact absurd rfl h
  · exact absurd rfl h

/-- A frame of a stack is globally live (WC4 C2). -/
theorem SC.mem_frames_of {s : SC} {c f : Nat} (h : f ∈ s.stk c) : f ∈ s.frames := by
  have hc : c < s.C.length := by
    unfold SC.stk at h; split at h
    · exact lt_of_getElem? ‹_›
    · simp at h
  exact List.mem_flatMap.2 ⟨c, List.mem_range.2 hc, h⟩

/-- Globally live frames are the frames of some stack (WC4 C2). -/
theorem SC.mem_frames {s : SC} {f : Nat} : f ∈ s.frames ↔ ∃ c, f ∈ s.stk c := by
  constructor
  · intro h; obtain ⟨c, -, hc⟩ := List.mem_flatMap.1 h; exact ⟨c, hc⟩
  · rintro ⟨c, hc⟩; exact SC.mem_frames_of hc

/-- The view of a context lists exactly the globally live frames (WC4 C2). -/
theorem SC.mem_view_F {s : SC} {c f : Nat} : f ∈ (s.view c).F ↔ f ∈ s.frames := by
  simp only [SC.view, SC.flat, List.mem_append, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro (h | ⟨h, -⟩)
    · exact SC.mem_frames_of h
    · exact h
  · intro h
    by_cases hc : f ∈ s.stk c
    · exact .inl hc
    · exact .inr ⟨h, hc⟩

/-- A block of a duplicate-free concatenation is duplicate-free (WC4 C3). -/
theorem nodup_of_flatMap {α β : Type} {f : α → List β} :
    ∀ {l : List α} {a : α}, (l.flatMap f).Nodup → a ∈ l → (f a).Nodup
  | b :: l, a, h, ha => by
    rw [List.flatMap_cons] at h
    rcases List.mem_cons.1 ha with rfl | ha
    · exact (List.nodup_append.1 h).1
    · exact nodup_of_flatMap (List.nodup_append.1 h).2.1 ha

/-- Two blocks of a duplicate-free concatenation share no element (WC4 C3: frame identities are
globally unique). -/
theorem disjoint_of_flatMap {α β : Type} {f : α → List β} :
    ∀ {l : List α}, (l.flatMap f).Nodup → l.Nodup → ∀ {a a' : α} {x : β}, a ∈ l → a' ∈ l →
      x ∈ f a → x ∈ f a' → a = a'
  | b :: l, h, hl, a, a', x, ha, ha', hx, hx' => by
    rw [List.flatMap_cons] at h
    obtain ⟨-, h₂, h₃⟩ := List.nodup_append.1 h
    have hl' := (List.nodup_cons.1 hl).2
    rcases List.mem_cons.1 ha with e₁ | h₁ <;> rcases List.mem_cons.1 ha' with e₂ | h₂'
    · rw [e₁, e₂]
    · subst e₁; exact absurd rfl (h₃ x hx x (List.mem_flatMap.2 ⟨a', h₂', hx'⟩))
    · subst e₂; exact absurd rfl (h₃ x hx' x (List.mem_flatMap.2 ⟨a, h₁, hx⟩))
    · exact disjoint_of_flatMap h₂ hl' h₁ h₂' hx hx'

/-- The stack of a context is duplicate-free when the live frames are (WC4 C3). -/
theorem SC.stk_nodup {s : SC} (hnd : s.frames.Nodup) (c : Nat) : (s.stk c).Nodup := by
  by_cases hc : c < s.C.length
  · exact nodup_of_flatMap hnd (List.mem_range.2 hc)
  · simp [SC.stk, List.getElem?_eq_none_iff.2 (Nat.le_of_not_lt hc)]

/-- The view of a context is duplicate-free when the live frames are (WC4 C3). -/
theorem SC.view_nodup {s : SC} (hnd : s.frames.Nodup) (c : Nat) : (s.view c).F.Nodup := by
  simp only [SC.view, SC.flat]
  refine List.nodup_append.2 ⟨SC.stk_nodup hnd c, hnd.sublist (List.filter_sublist ..),
    fun a ha b hb e => ?_⟩
  subst e
  simp only [List.mem_filter, decide_eq_true_eq] at hb
  exact hb.2 ha

/-- The current frame of the view of `c` is the top of the stack of `c` (WC4 C2). -/
theorem SC.view_top {s : SC} {c f : Nat} {rest : List Nat} (h : s.stk c = f :: rest) :
    (s.view c).top = f := by
  simp [SC.view, S3.top, h]

/-! ## Membership congruence (WC4 C2)

The clauses of `WF3`, `I1`–`I3`, `NoDangling` and `NoOrphan` (Spec 1 §49–§54) read the stack only
through membership; they agree on states that differ only by the order of the stack. -/

section Congr

variable {t : S3} {F' : Frames}

/-- Usability depends on the stack only through membership (Spec 1 §40). -/
theorem usable_mem_congr (hF : ∀ f, f ∈ F' ↔ f ∈ t.F) {q : Nat} :
    ({ t with F := F' } : S3).Usable q ↔ t.Usable q :=
  ⟨S3.Usable.mono (s' := { t with F := F' }) (s := t) rfl (fun f h => (hF f).1 h)
    (fun _ h => h),
   S3.Usable.mono (s' := t) (s := { t with F := F' }) rfl (fun f h => (hF f).2 h)
    (fun _ h => h)⟩

/-- Holder liveness depends on the stack only through membership (Spec 1 §49.8). -/
theorem holderLive_mem_congr (hF : ∀ f, f ∈ F' ↔ f ∈ t.F) (h : Holder) :
    HolderLive ({ t with F := F' } : S3) h ↔ HolderLive t h := by
  cases h with
  | frame f => exact hF f
  | place p => exact usable_mem_congr hF

/-- `WF3` depends on the stack only through membership, duplicate-freedom and nonemptiness
(Spec 1 §49). -/
theorem wf3_mem_congr (hw : WF3 t) (hF : ∀ f, f ∈ F' ↔ f ∈ t.F) (hnd : F'.Nodup)
    (hne : F' ≠ []) : WF3 { t with F := F' } where
  frames := ⟨hne, hnd, fun f hf => hw.frames.2.2 f ((hF f).1 hf)⟩
  places := hw.places
  owners := ⟨hw.owners.1, hw.owners.2.1, fun q hq => by
    obtain ⟨f, hf, hfF⟩ := hw.owners.2.2 q ((usable_mem_congr hF).1 hq)
    exact ⟨f, (FrameOf.congr (s' := { t with F := F' }) (s := t) rfl).2 hf, (hF f).2 hfF⟩⟩
  footprints := hw.footprints
  origins := hw.origins
  rootChain := hw.rootChain
  rootHeld := fun r hr hu => hw.rootHeld r hr ((usable_mem_congr hF).1 hu)
  holders := fun a y hy ya => (holderLive_mem_congr hF _).2 (hw.holders a y hy ya)

/-- `I3` depends on the stack only through membership (Spec 1 §52). -/
theorem i3_mem_congr (h : I3 t) (hF : ∀ f, f ∈ F' ↔ f ∈ t.F) : I3 { t with F := F' } :=
  fun q hq x hx => h q ((usable_mem_congr hF).1 hq) x hx

/-- `NoDangling` depends on the stack only through membership (Spec 1 §54). -/
theorem noDangling_mem_congr (h : NoDangling t) (hF : ∀ f, f ∈ F' ↔ f ∈ t.F) :
    NoDangling { t with F := F' } :=
  fun j y hy ya q hq => h j y hy ya q fun hu => hq ((usable_mem_congr hF).2 hu)

end Congr

/-- The view of a context is the flat state with a reordered stack (WC4 C2). -/
theorem SC.view_eq (s : SC) (c : Nat) :
    s.view c = { s.flat with F := (s.view c).F } := rfl

/-- `WF3` of the flat state carries to every view (WC4 C2). -/
theorem SC.wf3_view {s : SC} (hfr : FramesC s) (hw : WF3 s.flat) {c : Nat} :
    WF3 (s.view c) := by
  rw [SC.view_eq]
  refine wf3_mem_congr hw (fun f => SC.mem_view_F) (SC.view_nodup hfr.nodup c) ?_
  intro he
  have h0 := hfr.initial
  unfold OptP at h0; split at h0
  · rename_i x hx
    have hs := hfr.nonempty 0 (by simp [SC.Live, hx, OptP, h0.1])
    obtain ⟨f, hf⟩ := List.exists_mem_of_ne_nil _ hs
    have := (SC.mem_view_F (c := c)).2 (SC.mem_frames_of hf)
    rw [he] at this; simp at this
  · exact h0.elim

/-- `WF3` of a view carries to the flat state (WC4 C2). -/
theorem SC.wf3_flat_of_view {s : SC} {c : Nat} (hw : WF3 (s.view c)) (hnd : s.frames.Nodup) :
    WF3 s.flat := by
  have := wf3_mem_congr (t := s.view c) (F' := s.frames) hw
    (fun f => SC.mem_view_F.symm) hnd (fun he => by
      obtain ⟨f, hf⟩ := List.exists_mem_of_ne_nil _ hw.frames.1
      have := SC.mem_view_F.1 hf; rw [he] at this; simp at this)
  exact this

end Ern.Concurrency
