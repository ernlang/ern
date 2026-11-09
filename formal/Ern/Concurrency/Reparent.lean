import Ern.Concurrency.Conservativity

/-!
# Reparenting at frame exit and context termination (WC4 C6, C7; OB-C13)

`exitFrameC` (Spec 1 §73 re-indexed with the reparenting of WC4 C6 effect) and `terminate` (WC4 C7):

* the frame structure after the step (`FramesC`), and the extended ancestry of the surviving
  frames, which is the ancestry before the step with the exiting frame skipped
  (`exitEffC_ancestorC`, `termEffC_ancestorC`);
* Theorem 3 (OB-C13): both steps preserve `AnchorOrderC` and `AnchorOrderHeldC`, and change `A`
  and `D` exactly as the effect of Spec 1 §73 (`exitEffC_kernel`, `termEffC_kernel`); reparenting
  targets the immediate surviving parent (`exitEffC_reparent`, `termEffC_reparent`);
* Theorem 2 restricted to these steps: `KInvC` and the auxiliaries `RootHeldConv`,
  `HeldAnchored` of Spec 1 on the globally live frames are preserved (`exitFrameC_preserves`,
  `terminate_preserves`).
-/

namespace Ern.Concurrency

open Ern.MemoryModel.Access

namespace ReparentAux

/-! ## Lists -/

/-- Blockwise sublists give a sublist of the concatenation (WC4 C3). -/
theorem sublist_flatMap {α β : Type} {f g : α → List β} :
    ∀ {l : List α}, (∀ a ∈ l, (f a).Sublist (g a)) → (l.flatMap f).Sublist (l.flatMap g)
  | [], _ => List.Sublist.slnil
  | a :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons]
    exact (h a (List.mem_cons_self ..)).append
      (sublist_flatMap fun b hb => h b (List.mem_cons_of_mem _ hb))

/-- `List.modify` read at an index (WC4 C6, C7: the context list after the step), proved
without the classical core lemma. -/
theorem getElem?_modify' {α : Type} (f : α → α) : ∀ (l : List α) (i j : Nat),
    (l.modify i f)[j]? = (l[j]?).map fun a => if i = j then f a else a
  | [], i, _ => by cases i <;> rfl
  | _ :: _, 0, 0 => rfl
  | _ :: l, 0, j + 1 => by
    show l[j]? = Option.map _ l[j]?
    cases l[j]? <;> rfl
  | _ :: _, _ + 1, 0 => rfl
  | _ :: l, i + 1, j + 1 => by
    show (l.modify i f)[j]? = Option.map _ l[j]?
    rw [getElem?_modify' f l i j]
    cases l[j]? with
    | none => rfl
    | some b => simp only [Option.map_some, Nat.add_right_cancel_iff]

/-- `List.range` is duplicate-free (identities of contexts, WC4 C2). -/
theorem range_nodup (n : Nat) : (List.range n).Nodup :=
  (Frames.range_pairwise_lt n).imp Nat.ne_of_lt

/-! ## Parent replacement (WC4 C6 effect) -/

/-- Replacement of the parent `f` by `p` (WC4 C6 effect). -/
def repO (f p : Nat) (o : Option Nat) : Option Nat := if o = some f then some p else o

/-- `repO` of `none` (WC4 C6 effect). -/
theorem repO_none (f p : Nat) : repO f p none = none := by simp [repO]

/-- `repO` of a value other than `f` (WC4 C6 effect). -/
theorem repO_ne {f p g : Nat} (h : g ≠ f) : repO f p (some g) = some g := by simp [repO, h]

/-- `repO` of `f` (WC4 C6 effect). -/
theorem repO_eq (f p : Nat) : repO f p (some f) = some p := by simp [repO]

/-- Replacing the parent of the initial frame replaces the parent within a stack without `f`
(WC4 C3, C6 effect). -/
theorem parIn_repO {f p y : Nat} {par : Option Nat} : ∀ {l : List Nat}, f ∉ l →
    parIn (repO f p par) y l = repO f p (parIn par y l)
  | [], _ => by simp [parIn, repO]
  | a :: l, h => by
    by_cases e : a = y
    · simp only [parIn, e, ↓reduceIte]
      cases l with
      | nil => simp
      | cons b l =>
        have hb : b ≠ f := fun e' => h (by simp [e'])
        simp [repO_ne hb]
    · simp only [parIn, e, ↓reduceIte]
      exact parIn_repO fun hm => h (List.mem_cons_of_mem _ hm)

/-- A duplicate-free stack whose `parIn` links decrease is strictly decreasing (WC4 C3; Spec 1
§49, last paragraph). -/
theorem pairwise_of_parIn' {par : Option Nat} : ∀ {F : List Nat}, F.Nodup →
    (∀ f g, parIn par f F = some g → g < f) → F.Pairwise (· > ·)
  | [], _, _ => List.Pairwise.nil
  | a :: F, hnd, h => by
    obtain ⟨hna, hndF⟩ := List.nodup_cons.1 hnd
    have ih : F.Pairwise (· > ·) := pairwise_of_parIn' hndF fun f g hg => by
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

/-! ## Contexts of frames (WC4 C3) -/

/-- A frame of a stack belongs to an existing context (WC4 C2). -/
theorem stk_lt {s : SC} {f d : Nat} (h : f ∈ s.stk d) : d < s.C.length := by
  unfold SC.stk at h; split at h
  · exact lt_of_getElem? ‹_›
  · simp at h

/-- With unique frame identities, the context of a frame is the one whose stack contains it
(WC4 C3). -/
theorem ctxOf_of_mem {s : SC} (hnd : s.frames.Nodup) {f d : Nat} (h : f ∈ s.stk d) :
    s.ctxOf f = some d := by
  have hd := stk_lt h
  cases hc : s.ctxOf f with
  | none =>
    exfalso
    have := List.find?_eq_none.1 hc d (List.mem_range.2 hd)
    exact this (List.contains_iff_mem.2 h)
  | some d₀ =>
    have hc' : (List.range s.C.length).find? (fun c => (s.stk c).contains f) = some d₀ := hc
    have h0 := List.find?_some hc'
    have h1 : f ∈ s.stk d₀ := List.contains_iff_mem.1 h0
    have h2 := List.mem_of_find?_eq_some hc'
    exact congrArg some (disjoint_of_flatMap (f := s.stk) hnd (range_nodup _) h2
      (List.mem_range.2 hd) h1 h)

/-- The parent of a live frame is read in the stack of its context (WC4 C3). -/
theorem parC_of_mem {s : SC} (hnd : s.frames.Nodup) {f d : Nat} (h : f ∈ s.stk d) :
    s.parC f = parIn (s.ctxParent d) f (s.stk d) := by
  simp [SC.parC, ctxOf_of_mem hnd h]

/-- Two stacks sharing a frame are the same stack (WC4 C3). -/
theorem stk_unique {s : SC} (hnd : s.frames.Nodup) {f d d' : Nat} (h : f ∈ s.stk d)
    (h' : f ∈ s.stk d') : d = d' := by
  have := (ctxOf_of_mem hnd h).symm.trans (ctxOf_of_mem hnd h')
  exact Option.some.inj this

/-- Under `FramesC`, every stack is strictly decreasing (WC4 C3; Spec 1 §49, last
paragraph). -/
theorem stk_decreasing {s : SC} (hfr : FramesC s) (d : Nat) : (s.stk d).Pairwise (· > ·) := by
  refine pairwise_of_parIn' (par := s.ctxParent d) (SC.stk_nodup hfr.nodup d) fun f g hg => ?_
  by_cases hf : f ∈ s.stk d
  · exact (hfr.parent f (SC.mem_frames_of hf) g
      (by rw [parC_of_mem hfr.nodup hf]; exact hg)).2
  · rw [parIn_not_mem hf] at hg; cases hg

/-! ## Popping a frame with reparenting (WC4 C6, C7) -/

/-- Shape of the frame structure after popping the top frame `f` of context `c`, whose parent is
`p`, with the reparenting of WC4 C6 effect: the stack of `c` loses `f`, other stacks are unchanged,
the initial frames whose parent was `f` get the parent `p`. -/
structure Pop (s s' : SC) (c f p : Nat) : Prop where
  head : (s.stk c).head? = some f
  stk : ∀ d, s'.stk d = if d = c then (s.stk c).tail else s.stk d
  len : s'.C.length = s.C.length
  nF : s'.nF = s.nF
  par : ∀ d, s'.Live d → s'.ctxParent d = repO f p (s.ctxParent d)
  live : ∀ d, s'.Live d → s.Live d
  pf : s.parC f = some p

section Pop

variable {s s' : SC} {c f p : Nat}

/-- The stack of `c` starts with `f` (WC4 C6). -/
theorem Pop.stk_c (h : Pop s s' c f p) : s.stk c = f :: (s.stk c).tail := by
  have := h.head
  cases e : s.stk c with
  | nil => rw [e] at this; cases this
  | cons a l => rw [e] at this; cases this; rfl

/-- The popped frame is live before the step (WC4 C6). -/
theorem Pop.f_mem (h : Pop s s' c f p) : f ∈ s.frames := by
  apply SC.mem_frames_of (c := c); rw [h.stk_c]; exact List.mem_cons_self ..

/-- The frames live after the step are those live before, except `f` (WC4 C6, C7). -/
theorem Pop.mem_frames (hnd : s.frames.Nodup) (h : Pop s s' c f p) {y : Nat} :
    y ∈ s'.frames ↔ y ∈ s.frames ∧ y ≠ f := by
  have hc := h.stk_c
  have hfc : f ∈ s.stk c := by rw [hc]; exact List.mem_cons_self ..
  have hft : f ∉ (s.stk c).tail := by
    have := SC.stk_nodup hnd c; rw [hc] at this; exact (List.nodup_cons.1 this).1
  constructor
  · intro hy
    obtain ⟨d, hd⟩ := SC.mem_frames.1 hy
    rw [h.stk d] at hd
    split at hd
    · subst d
      exact ⟨SC.mem_frames_of (List.mem_of_mem_tail hd), fun e => hft (e ▸ hd)⟩
    · rename_i hne
      exact ⟨SC.mem_frames_of hd, fun e => hne (stk_unique hnd hd (e ▸ hfc))⟩
  · rintro ⟨hy, hyf⟩
    obtain ⟨d, hd⟩ := SC.mem_frames.1 hy
    apply SC.mem_frames_of (c := d)
    rw [h.stk d]
    split
    · subst d; rw [hc] at hd
      exact (List.mem_cons.1 hd).resolve_left hyf
    · exact hd

/-- The frames live after the step are duplicate-free (WC4 C3). -/
theorem Pop.nodup (hnd : s.frames.Nodup) (h : Pop s s' c f p) : s'.frames.Nodup := by
  refine hnd.sublist ?_
  unfold SC.frames; rw [h.len]
  refine sublist_flatMap fun d _ => ?_
  rw [h.stk d]; split
  · subst d; exact List.tail_sublist _
  · exact List.Sublist.refl _

/-- The parent of a frame live after the step is its parent before, with `f` replaced by `p`
(WC4 C6 effect). -/
theorem Pop.parC (hnd : s.frames.Nodup) (h : Pop s s' c f p) {y : Nat} (hy : y ∈ s'.frames) :
    s'.parC y = repO f p (s.parC y) := by
  have hc := h.stk_c
  have hfc : f ∈ s.stk c := by rw [hc]; exact List.mem_cons_self ..
  have hft : f ∉ (s.stk c).tail := by
    have := SC.stk_nodup hnd c; rw [hc] at this; exact (List.nodup_cons.1 this).1
  obtain ⟨d, hd⟩ := SC.mem_frames.1 hy
  have hnd' := h.nodup hnd
  rw [parC_of_mem hnd' hd, h.par d (SC.live_of_stk (List.ne_nil_of_mem hd))]
  have hd' := hd
  rw [h.stk d] at hd' ⊢
  by_cases hdc : d = c
  · subst d
    simp only [↓reduceIte] at hd' ⊢
    have hyf : y ≠ f := fun e => hft (e ▸ hd')
    rw [parIn_repO hft, parC_of_mem hnd (List.mem_of_mem_tail hd')]
    have e : ∀ l, s.stk c = f :: l →
        parIn (s.ctxParent c) y (s.stk c) = parIn (s.ctxParent c) y l :=
      fun l hl => by rw [hl, parIn_cons_ne (Ne.symm hyf)]
    rw [e _ hc]
  · simp only [hdc, ↓reduceIte] at hd' ⊢
    have hfd : f ∉ s.stk d := fun hm => hdc (stk_unique hnd hm hfc)
    rw [parIn_repO hfd, parC_of_mem hnd hd']

/-- The chain of parents after the step is the chain before without `f` (WC4 C6 effect). -/
theorem Pop.chain (hfr : FramesC s) (h : Pop s s' c f p) :
    ∀ n y, y < n → y ∈ s'.frames → chain s'.parC y = (chain s.parC y).filter (· != f)
  | 0, _, hy, _ => absurd hy (Nat.not_lt_zero _)
  | n + 1, y, hyn, hy => by
    have hy₀ := ((h.mem_frames hfr.nodup).1 hy)
    have hpar := h.parC hfr.nodup hy
    cases hg : s.parC y with
    | none =>
      rw [hg, repO_none] at hpar
      rw [chain_none hpar, chain_none hg]; rfl
    | some g =>
      obtain ⟨hgF, hgy⟩ := hfr.parent y hy₀.1 g hg
      rw [chain_cons hg hgy]
      by_cases hgf : g = f
      · subst g
        have hpar' : s'.parC y = some p := by rw [hpar, hg]; exact repO_eq f p
        obtain ⟨hpF, hpf⟩ := hfr.parent f h.f_mem p h.pf
        have hp' : p ∈ s'.frames := (h.mem_frames hfr.nodup).2 ⟨hpF, Nat.ne_of_lt hpf⟩
        rw [chain_cons hpar' (Nat.lt_trans hpf hgy), chain_cons h.pf hpf,
          Pop.chain hfr h n p (by omega) hp']
        simp [Nat.ne_of_lt hpf]
      · have hg' : g ∈ s'.frames := (h.mem_frames hfr.nodup).2 ⟨hgF, hgf⟩
        rw [chain_cons (show s'.parC y = some g by rw [hpar, hg]; exact repO_ne hgf) hgy,
          Pop.chain hfr h n g (by omega) hg']
        simp [hgf]

/-- The extended ancestry of frames live after the step is the ancestry before (WC4 C6 effect):
popping `f` only removes `f` from the chains. -/
theorem Pop.ancestorC (hfr : FramesC s) (h : Pop s s' c f p) {g y : Nat} (hg : g ∈ s'.frames)
    (hy : y ∈ s'.frames) : s'.ancestorC g y ↔ s.ancestorC g y := by
  have hgf := ((h.mem_frames hfr.nodup).1 hg).2
  have hy₀ := (h.mem_frames hfr.nodup).1 hy
  unfold SC.ancestorC
  rw [h.chain hfr (y + 1) y (Nat.lt_succ_self y) hy]
  simp [hy, hy₀.1, List.mem_filter, hgf]

/-- The frame structure after the step (WC4 C3, C6 preservation obligations, C20), given the initial context and the
nonempty stacks of the live contexts. -/
theorem Pop.framesC (hfr : FramesC s) (h : Pop s s' c f p)
    (hinit : OptP (s'.C[0]?) (fun x => x.life = .live ∧ x.parent = none) False)
    (hne : ∀ d, s'.Live d → s'.stk d ≠ []) : FramesC s' where
  initial := hinit
  nonempty := hne
  nodup := h.nodup hfr.nodup
  bound := fun y hy => by rw [h.nF]; exact hfr.bound y ((h.mem_frames hfr.nodup).1 hy).1
  rooted := fun d hd hl => by
    rw [h.par d hl]
    have := hfr.rooted d hd (h.live d hl)
    unfold repO; split
    · simp
    · exact this
  parent := fun y hy g hpg => by
    have hy₀ := (h.mem_frames hfr.nodup).1 hy
    rw [h.parC hfr.nodup hy] at hpg
    cases hg : s.parC y with
    | none => rw [hg, repO_none] at hpg; cases hpg
    | some g₀ =>
      obtain ⟨hgF, hgy⟩ := hfr.parent y hy₀.1 g₀ hg
      rw [hg] at hpg
      by_cases e : g₀ = f
      · subst g₀
        rw [repO_eq] at hpg
        have e2 : g = p := (Option.some.inj hpg).symm
        subst e2
        obtain ⟨hpF, hpf⟩ := hfr.parent f h.f_mem g h.pf
        exact ⟨(h.mem_frames hfr.nodup).2 ⟨hpF, Nat.ne_of_lt hpf⟩, Nat.lt_trans hpf hgy⟩
      · rw [repO_ne e] at hpg
        have e2 : g = g₀ := (Option.some.inj hpg).symm
        subst e2
        exact ⟨(h.mem_frames hfr.nodup).2 ⟨hgF, e⟩, hgy⟩

/-- The surviving frames of the view of `c` (Spec 1 §73: the stack without its top) are the
frames live after the step (WC4 C6, C7). -/
theorem Pop.view_tail (hnd : s.frames.Nodup) (h : Pop s s' c f p) {y : Nat} :
    y ∈ (s.view c).F.tail ↔ y ∈ s'.frames := by
  rw [h.mem_frames hnd]
  have hc := h.stk_c
  have hft : f ∉ (s.stk c).tail := by
    have := SC.stk_nodup hnd c; rw [hc] at this; exact (List.nodup_cons.1 this).1
  have hF : (s.view c).F.tail = (s.stk c).tail ++ s.frames.filter fun g => decide (g ∉ s.stk c) := by
    show (s.stk c ++ _).tail = _
    rw [hc]; rfl
  rw [hF, List.mem_append, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro (hy | ⟨hy, hyc⟩)
    · exact ⟨SC.mem_frames_of (List.mem_of_mem_tail hy), fun e => hft (e ▸ hy)⟩
    · exact ⟨hy, fun e => hyc (by rw [hc, e]; exact List.mem_cons_self ..)⟩
  · rintro ⟨hy, hyf⟩
    by_cases hyc : y ∈ s.stk c
    · rw [hc] at hyc; exact .inl ((List.mem_cons.1 hyc).resolve_left hyf)
    · exact .inr ⟨hy, hyc⟩

end Pop

/-- A frame structure has a live frame (WC4 C3). -/
theorem frames_ne {s : SC} (hfr : FramesC s) : s.frames ≠ [] := by
  intro he
  have h0 := hfr.initial
  unfold OptP at h0; split at h0
  · rename_i x hx
    have hs := hfr.nonempty 0 (by simp [SC.Live, hx, OptP, h0.1])
    obtain ⟨f, hf⟩ := List.exists_mem_of_ne_nil _ hs
    have := SC.mem_frames_of hf; rw [he] at this; simp at this
  · exact h0.elim

/-- A live holder has a holder frame among the live frames (Spec 1 §40, §44, §49.8). -/
theorem hframe_of_live {t : S3} {F₀ : Frames} {h : Holder}
    (hl : HolderLive ({ t with F := F₀ } : S3) h) : ∃ g, t.hframe h = some g ∧ g ∈ F₀ := by
  cases h with
  | frame g => exact ⟨g, rfl, hl⟩
  | place q =>
    obtain ⟨g, hg, hgF⟩ := S3.Usable.frameOf hl
    exact ⟨g, pframe_iff.2 ((FrameOf.congr (s' := ({ t with F := F₀ } : S3)) (s := t) rfl).1 hg),
      hgF⟩

/-- An anchor satisfying `EffAnchorOKC` has an existing effective anchor (Spec 1 §44). -/
theorem effAnchorOKC_get {s : SC} {x : Nat} {fd : Option Nat} (h : EffAnchorOKC s x fd) :
    ∃ y, s.A[s.flat.effAnchor x]? = some y := by
  unfold EffAnchorOKC at h
  cases hz : s.A[s.flat.effAnchor x]? with
  | none => rw [hz] at h; exact h.elim
  | some z => exact ⟨z, rfl⟩

/-- `EffAnchorOKC` carries over between states with the same holder frame of the effective anchor
and the same extended ancestry on the relevant frames (Spec 1 §44 re-indexed). -/
theorem effAnchorOKC_of_same {s s' : SC} {x x' : Nat} {z z' : Authority} {fd : Option Nat}
    (hz : s.A[s.flat.effAnchor x]? = some z) (hz' : s'.A[s'.flat.effAnchor x']? = some z')
    (hh : s'.flat.hframe z'.holder = s.flat.hframe z.holder)
    (hanc : ∀ g f, s.flat.hframe z.holder = some g → fd = some f →
      (s'.ancestorC g f ↔ s.ancestorC g f)) :
    EffAnchorOKC s' x' fd ↔ EffAnchorOKC s x fd := by
  unfold EffAnchorOKC; rw [hz, hz']; simp only [OptP]; rw [hh]
  cases hg : s.flat.hframe z.holder with
  | none => simp
  | some g =>
    cases hf : fd with
    | none => simp
    | some f => simp only; exact hanc g f hg hf

section PopPreserve

variable {s s' : SC} {c f p : Nat}

/-- Theorem 3 (OB-C13; WC4 C6 effect and preservation obligations; Spec 1 §44, §73): popping a frame with the effect of Spec
1 §73 on the view of `c` and the reparenting of WC4 C6 effect preserves `AnchorOrderC`: a reanchored
anchor has the root of the original chain as effective anchor, which survives, and the extended
ancestry between surviving frames is unchanged. -/
theorem Pop.anchorOrderC (hfr : FramesC s) (hw : WF3 s.flat) (hao : AnchorOrderC s)
    (h : Pop s s' c f p) (hflat : s'.flat = { exitEff (s.view c) with F := s'.frames })
    (hR1 : ∀ q ∈ List.range s.P.length,
      ({ s.view c with F := (s.view c).F.tail } : S3).Usable q →
      ∀ x ∈ s.D q, firstSurv (s.view c) (s.view c).F.tail (x :: (s.view c).ancs x) ≠ none)
    (h3 : Frames.OriginsSurvive (s.view c)) : AnchorOrderC s' := by
  have hwt := SC.wf3_view hfr hw (c := c)
  have hP : s'.P = s.P := congrArg S3.P hflat
  have hD : s'.D = (exitEff (s.view c)).D := congrArg S3.D hflat
  intro q hq x' hx'
  have hq₁ : ({ s.view c with F := (s.view c).F.tail } : S3).Usable q := by
    rw [hflat] at hq
    exact S3.Usable.mono (s' := { exitEff (s.view c) with F := s'.frames })
      (s := { s.view c with F := (s.view c).F.tail }) rfl
      (fun y hy => (h.view_tail hfr.nodup).2 hy) (fun _ h => h) hq
  have hq₀ : (s.view c).Usable q := Frames.usable_of_tail hq₁
  have hqf : s.flat.Usable q :=
    (usable_mem_congr (t := s.flat) (F' := (s.view c).F) fun y => SC.mem_view_F).1 hq₀
  rw [hD] at hx'
  simp only [exitEff, List.mem_map] at hx'
  obtain ⟨x, hx, rfl⟩ := hx'
  obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.1 (hR1 q (List.mem_range.2 hq₀.lt) hq₁ x hx)
  rw [hz]; simp only [Option.getD_some]
  have hok := hao q hqf x hx
  obtain ⟨r, hr, hro⟩ := Frames.reaches_root hwt (x + 1) x (Nat.lt_succ_self x)
  have hex : (s.view c).effAnchor x = r :=
    Frames.effAnchor_eq (x + 1) x (Nat.lt_succ_self x) r hr hro
  have hzx : z = x ∨ z ∈ (s.view c).ancs x := List.mem_cons.1 (Frames.firstSurv_some hz).1
  have hrz : r = z ∨ r ∈ (s.view c).ancs z := by
    rcases hzx with rfl | hzx
    · exact hr
    · rcases hr with rfl | hr
      · rw [S3.ancs, chain_none hro] at hzx; simp at hzx
      · exact Frames.ancs_root_after (x + 1) x (Nat.lt_succ_self x) z r hzx hr hro
  obtain ⟨y, hy⟩ := effAnchorOKC_get hok
  have hy' : (s.view c).A[r]? = some y := by rw [← hex]; exact hy
  have hyo : y.origin = none := by simpa [S3.org, hy'] using hro
  have hro' : (exitEff (s.view c)).org r = none := by
    simp only [S3.org, Frames.exit_A_get, hy', Option.map_some, Option.bind_some]
    rcases Frames.exitG_origin (s := s.view c) (F₀ := (s.view c).F.tail) (a := r) (y := y)
      with e' | ⟨-, hn, -⟩
    · rw [e']; exact hyo
    · exact absurd hyo hn
  have hrz' : r = z ∨ r ∈ (exitEff (s.view c)).ancs z := hrz.imp id fun hh =>
    Frames.exit_root_kept h3 (z + 1) z (Nat.lt_succ_self z) r hh hro
  have hez : (exitEff (s.view c)).effAnchor z = r :=
    Frames.effAnchor_eq (z + 1) z (Nat.lt_succ_self z) r hrz' hro'
  have hsr : Survives (s.view c) (s.view c).F.tail r := Frames.exit_root_survives h3 (z + 1) z
    (Nat.lt_succ_self z) (Frames.firstSurv_some hz).2 r hrz hro
  have hlive : HolderLive ({ s.view c with F := (s.view c).F.tail } : S3) y.holder := by
    unfold Survives at hsr; rw [hy'] at hsr; exact hsr.2
  obtain ⟨g, hg, hgF⟩ := hframe_of_live hlive
  obtain ⟨f₁, hf₁, hf₁F⟩ := S3.Usable.frameOf hq
  have hpq : s.flat.pframe q = some f₁ :=
    pframe_iff.2 ((FrameOf.congr (s' := s'.flat) (s := s.flat) hP).1 hf₁)
  rw [pframe_iff.2 hf₁]; rw [hpq] at hok
  refine (effAnchorOKC_of_same (s := s) (s' := s') (x := x) (x' := z) (z := y)
    (z' := exitG (s.view c) (s.view c).F.tail r y) hy ?_ ?_ ?_).2 hok
  · show s'.flat.A[s'.flat.effAnchor z]? = _
    rw [hflat]
    show (exitEff (s.view c)).A[(exitEff (s.view c)).effAnchor z]? = _
    rw [hez, Frames.exit_A_get, hy']; rfl
  · rw [(Frames.exitG_same (s.view c) (s.view c).F.tail r y).2.2]
    exact S3.hframe_congr (s := s.flat) (s' := s'.flat) hP _
  · intro g' f' hg' hf'
    have hg2 : s.flat.hframe y.holder = some g :=
      (S3.hframe_congr (s := s.flat) (s' := s.view c) rfl _).symm.trans hg
    have e1 : g' = g := Option.some.inj (hg'.symm.trans hg2)
    have e2 : f' = f₁ := (Option.some.inj hf').symm
    subst e1 e2
    exact h.ancestorC hfr ((h.view_tail hfr.nodup).1 hgF) hf₁F

/-- Theorem 2 restricted to a popped frame (WC4 C20, C23; Spec 1 §57, §73): the effect of Spec 1
§73 on the view of `c` with the reparenting of WC4 C6 effect, under the preconditions §73.2–§73.5,
preserves `KInvC`. -/
theorem Pop.kInvC (hk : KInvC s) (h : Pop s s' c f p) (hfr' : FramesC s')
    (hflat : s'.flat = { exitEff (s.view c) with F := s'.frames })
    (hR1 : ∀ q ∈ List.range s.P.length,
      ({ s.view c with F := (s.view c).F.tail } : S3).Usable q →
      ∀ x ∈ s.D q, firstSurv (s.view c) (s.view c).F.tail (x :: (s.view c).ancs x) ≠ none)
    (h3 : Frames.OriginsSurvive (s.view c)) (haoh : AnchorOrderHeldC s') : KInvC s' := by
  obtain ⟨⟨hfr, hw⟩, ⟨⟨i1, i2, i3, -⟩, hao, hnd⟩, -, -⟩ := hk
  have hwt := SC.wf3_view hfr hw (c := c)
  have hmem : ∀ y, y ∈ s'.frames ↔ y ∈ (exitEff (s.view c)).F :=
    fun y => (h.view_tail hfr.nodup).symm
  have hne' : s'.frames ≠ [] := frames_ne hfr'
  have hne : (s.view c).F.tail ≠ [] := fun he => by
    obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ hne'
    have := (hmem y).1 hy; rw [show (exitEff (s.view c)).F = (s.view c).F.tail from rfl, he] at this
    simp at this
  have hw' := Frames.exit_wf hwt hne h3
  have hwf' : WF3 s'.flat := by
    rw [hflat]; exact wf3_mem_congr hw' hmem (h.nodup hfr.nodup) hne'
  have i3t : I3 (s.view c) := by
    rw [SC.view_eq]; exact i3_mem_congr i3 fun y => SC.mem_view_F
  have hb' := Frames.exit_inv3base (s := s.view c) ⟨i1, i2, i3t, i4_always _⟩ hR1
  have hndt : NoDangling (s.view c) := by
    rw [SC.view_eq]; exact noDangling_mem_congr hnd fun y => SC.mem_view_F
  have hnd' := Frames.exit_noDangling hwt i1 hndt h3
  refine ⟨⟨hfr', hwf'⟩, ⟨⟨?_, ?_, ?_, fun _ => i4_always _⟩,
    h.anchorOrderC hfr hw hao hflat hR1 h3, ?_⟩, haoh, noOrphan_of_wf3 hwf'⟩
  · rw [hflat]; exact hb'.1
  · rw [hflat]; exact hb'.2.1
  · rw [hflat]; exact i3_mem_congr hb'.2.2.1 hmem
  · rw [hflat]; exact noDangling_mem_congr hnd' hmem

/-- The auxiliaries of Spec 1 (`RootHeldConv`, `HeldAnchored`, not clauses of §57) on the live
frames are preserved by a popped frame (Spec 1 §73; WC4 C6, C7). -/
theorem Pop.aux (hfr : FramesC s) (haux : RootHeldConv s.flat) (hh : HeldAnchored s.flat)
    (h : Pop s s' c f p) (hflat : s'.flat = { exitEff (s.view c) with F := s'.frames })
    (h3 : Frames.OriginsSurvive (s.view c)) :
    RootHeldConv s'.flat ∧ HeldAnchored s'.flat := by
  refine ⟨by rw [hflat]; exact Frames.exit_rootHeldConv haux h3, ?_⟩
  intro x y q hy ya ho hhq hu
  rw [hflat] at hy hu ⊢
  obtain ⟨y₀, hy₀, rfl⟩ := Frames.exit_get hy
  have hs := Frames.exitG_active ya
  have ya₀ := Frames.exitG_active' hy₀ ya
  have hh0 : y₀.holder = .place q := (Frames.exitG_same _ _ x y₀).2.2 ▸ hhq
  have ho₀ : y₀.origin ≠ none := by
    rcases Frames.exitG_origin (s := s.view c) (F₀ := (s.view c).F.tail) (a := x) (y := y₀)
      with e | ⟨-, hn, -⟩
    · rwa [← e]
    · exact hn
  have hq₁ : ({ s.view c with F := (s.view c).F.tail } : S3).Usable q :=
    S3.Usable.mono (s' := { exitEff (s.view c) with F := s'.frames })
      (s := { s.view c with F := (s.view c).F.tail }) rfl
      (fun y hy => (h.view_tail hfr.nodup).2 hy) (fun _ h => h) hu
  have hu₀ : s.flat.Usable q :=
    (usable_mem_congr (t := s.flat) (F' := (s.view c).F) fun y => SC.mem_view_F).1
      (Frames.usable_of_tail hq₁)
  have hx := hh x y₀ q hy₀ ya₀ ho₀ hh0 hu₀
  show x ∈ (exitEff (s.view c)).D q
  simp only [exitEff]
  refine List.mem_map.2 ⟨x, hx, ?_⟩
  show (firstSurv (s.view c) (s.view c).F.tail (x :: (s.view c).ancs x)).getD x = x
  rw [firstSurv, List.find?_cons_of_pos (p := fun z => decide (Survives (s.view c)
    (s.view c).F.tail z)) (a := x) (decide_eq_true hs)]
  rfl

end PopPreserve

end ReparentAux

open ReparentAux

/-! ## `exitFrameC` and `terminate` pop a frame (WC4 C6, C7) -/

section Steps

variable {s : SC} {c : Nat}

/-- Unfolding of the context list after `exitFrameC` (WC4 C6). -/
theorem exitEffC_C_get (d : Nat) : (exitEffC s c).C[d]? = (s.C[d]?).map fun x =>
    let x' := if c = d then { x with stack := x.stack.tail } else x
    if x'.life = .live ∧ x'.parent = some ((s.stk c).headD 0) then
      { x' with parent := some ((s.stk c).tail.headD 0) } else x' := by
  simp only [exitEffC, reparent, List.getElem?_map, getElem?_modify']
  cases s.C[d]? <;> rfl

/-- Unfolding of the context list after `terminate` (WC4 C7). -/
theorem termEffC_C_get (d : Nat) : (termEffC s c).C[d]? = (s.C[d]?).map fun x =>
    let x' := if c = d then { x with stack := [], life := .done } else x
    if x'.life = .live ∧ x'.parent = some ((s.stk c).headD 0) then
      { x' with parent := some ((s.ctxParent c).getD 0) } else x' := by
  simp only [termEffC, reparent, List.getElem?_map, getElem?_modify']
  cases s.C[d]? <;> rfl

/-- `exitFrameC` pops the top frame of `c` and reparents to its caller (WC4 C6). -/
theorem exitEffC_pop (hnd : s.frames.Nodup) (hcall : (s.stk c).tail ≠ []) :
    Pop s (exitEffC s c) c ((s.stk c).headD 0) ((s.stk c).tail.headD 0) := by
  obtain ⟨f, p, rest, hc⟩ : ∃ f p rest, s.stk c = f :: p :: rest := by
    cases e : s.stk c with
    | nil => rw [e] at hcall; exact absurd rfl hcall
    | cons f l => cases l with
      | nil => rw [e] at hcall; exact absurd rfl hcall
      | cons p rest => exact ⟨f, p, rest, rfl⟩
  have hfc : f ∈ s.stk c := by rw [hc]; exact List.mem_cons_self ..
  refine ⟨by rw [hc]; rfl, fun d => ?_, by simp [exitEffC, reparent], rfl, fun d hl => ?_,
    fun d hl => ?_, ?_⟩
  · unfold SC.stk; rw [exitEffC_C_get]
    by_cases hcd : c = d
    · subst d; simp only [↓reduceIte]
      cases hx : s.C[c]? with
      | none => simp
      | some x => simp only [Option.map_some]; split <;> split <;> simp_all
    · simp only [hcd, ↓reduceIte, Ne.symm hcd]
      cases hx : s.C[d]? with
      | none => simp
      | some x => simp only [Option.map_some]; split <;> simp_all
  · unfold SC.Live at hl; unfold SC.ctxParent; rw [exitEffC_C_get] at hl ⊢
    cases hx : s.C[d]? with
    | none => rw [hx] at hl; exact hl.elim
    | some x =>
      rw [hx] at hl
      simp only [Option.map_some, OptP] at hl
      simp only [Option.map_some, Option.bind_some, repO]
      by_cases hcd : c = d <;> simp_all <;> split <;> simp_all
  · unfold SC.Live at hl ⊢; rw [exitEffC_C_get] at hl
    cases hx : s.C[d]? with
    | none => rw [hx] at hl; exact hl.elim
    | some x =>
      rw [hx] at hl
      simp only [Option.map_some, OptP] at hl ⊢
      by_cases hcd : c = d <;> simp_all <;> split at hl <;> simp_all
  · have e := ReparentAux.parC_of_mem hnd hfc
    rw [hc] at e ⊢
    simpa [parIn] using e

/-- `terminate` pops the initial frame of `c` and reparents to its parent (WC4 C7, C6 effect). -/
theorem termEffC_pop (hnd : s.frames.Nodup) (hone : (s.stk c).length = 1)
    (hpar : s.ctxParent c ≠ none) :
    Pop s (termEffC s c) c ((s.stk c).headD 0) ((s.ctxParent c).getD 0) := by
  obtain ⟨f, hc⟩ : ∃ f, s.stk c = [f] := by
    cases e : s.stk c with
    | nil => rw [e] at hone; cases hone
    | cons f l => cases l with
      | nil => exact ⟨f, rfl⟩
      | cons _ _ => rw [e] at hone; exact absurd (Nat.succ.inj hone) (Nat.succ_ne_zero _)
  obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.1 hpar
  have hfc : f ∈ s.stk c := by rw [hc]; exact List.mem_cons_self ..
  refine ⟨by rw [hc]; rfl, fun d => ?_, by simp [termEffC, reparent], rfl, fun d hl => ?_,
    fun d hl => ?_, ?_⟩
  · unfold SC.stk; rw [termEffC_C_get]
    by_cases hcd : c = d
    · subst d; simp only [↓reduceIte]
      have hc' := hc; unfold SC.stk at hc'
      cases hx : s.C[c]? with
      | none => simp
      | some x => simp only [Option.map_some]; split <;> simp_all
    · simp only [hcd, ↓reduceIte, Ne.symm hcd]
      cases hx : s.C[d]? with
      | none => simp
      | some x => simp only [Option.map_some]; split <;> simp_all
  · have hp' : (s.C[c]?.bind fun x => x.parent) = some p := hp
    unfold SC.Live at hl; unfold SC.ctxParent; rw [termEffC_C_get] at hl ⊢
    cases hx : s.C[d]? with
    | none => rw [hx] at hl; exact hl.elim
    | some x =>
      rw [hx] at hl
      simp only [Option.map_some, OptP] at hl
      simp only [Option.map_some, Option.bind_some, repO]
      by_cases hcd : c = d <;> simp_all <;> split <;> simp_all
  · unfold SC.Live at hl ⊢; rw [termEffC_C_get] at hl
    cases hx : s.C[d]? with
    | none => rw [hx] at hl; exact hl.elim
    | some x =>
      rw [hx] at hl
      simp only [Option.map_some, OptP] at hl ⊢
      by_cases hcd : c = d <;> simp_all <;> split at hl <;> simp_all
  · have e := ReparentAux.parC_of_mem hnd hfc
    rw [hc] at e ⊢
    simp only [parIn, ↓reduceIte, List.head?_nil, Option.none_or] at e
    show s.parC f = some ((s.ctxParent c).getD 0)
    rw [e, hp]; rfl

/-- After `terminate`, the terminated context is not live (WC4 C7). -/
theorem termEffC_not_live : ¬ (termEffC s c).Live c := by
  unfold SC.Live; rw [termEffC_C_get]
  cases hx : s.C[c]? with
  | none => simp [OptP]
  | some x => simp only [Option.map_some, OptP, ↓reduceIte]; split <;> simp

/-- WC4 C3, C6 preservation obligations, C20: `exitFrameC` keeps a well-founded frame structure. -/
theorem exitEffC_framesC (hfr : FramesC s) (hcall : (s.stk c).tail ≠ []) :
    FramesC (exitEffC s c) := by
  have h := exitEffC_pop hfr.nodup hcall
  refine h.framesC hfr ?_ fun d hl => ?_
  · have h0 := hfr.initial
    rw [exitEffC_C_get]
    cases hx : s.C[0]? with
    | none => rw [hx] at h0; exact h0.elim
    | some x =>
      rw [hx] at h0; simp only [OptP] at h0
      simp only [Option.map_some, OptP]
      by_cases hc0 : c = 0 <;> simp_all
  · rw [h.stk d]; split
    · exact hcall
    · exact hfr.nonempty d (h.live d hl)

/-- WC4 C3, C6 preservation obligations, C7, C20: `terminate` keeps a well-founded frame structure. -/
theorem termEffC_framesC (hfr : FramesC s) (hc0 : c ≠ 0) (hone : (s.stk c).length = 1)
    (hpar : s.ctxParent c ≠ none) : FramesC (termEffC s c) := by
  have h := termEffC_pop hfr.nodup hone hpar
  refine h.framesC hfr ?_ fun d hl => ?_
  · have h0 := hfr.initial
    rw [termEffC_C_get]
    cases hx : s.C[0]? with
    | none => rw [hx] at h0; exact h0.elim
    | some x =>
      rw [hx] at h0; simp only [OptP] at h0
      simp only [Option.map_some, OptP]
      simp_all
  · rw [h.stk d]; split
    · rename_i hdc; subst hdc; exact absurd hl termEffC_not_live
    · exact hfr.nonempty d (h.live d hl)

/-- WC4 C6 effect (OB-C13): after `exitFrameC`, the live frames are those before except the
exiting frame, and the extended ancestry between live frames is unchanged: reparenting only
removes the exiting frame from the chains. -/
theorem exitEffC_ancestorC (hfr : FramesC s) (hcall : (s.stk c).tail ≠ []) {g y : Nat} :
    (y ∈ (exitEffC s c).frames ↔ y ∈ s.frames ∧ y ≠ (s.stk c).headD 0) ∧
    (g ∈ (exitEffC s c).frames → y ∈ (exitEffC s c).frames →
      ((exitEffC s c).ancestorC g y ↔ s.ancestorC g y)) :=
  ⟨(exitEffC_pop hfr.nodup hcall).mem_frames hfr.nodup,
   (exitEffC_pop hfr.nodup hcall).ancestorC hfr⟩

/-- WC4 C6 effect, C7 (OB-C13): after `terminate`, the live frames are those before except the
initial frame of the terminated context, and the extended ancestry between live frames is
unchanged. -/
theorem termEffC_ancestorC (hfr : FramesC s) (hone : (s.stk c).length = 1)
    (hpar : s.ctxParent c ≠ none) {g y : Nat} :
    (y ∈ (termEffC s c).frames ↔ y ∈ s.frames ∧ y ≠ (s.stk c).headD 0) ∧
    (g ∈ (termEffC s c).frames → y ∈ (termEffC s c).frames →
      ((termEffC s c).ancestorC g y ↔ s.ancestorC g y)) :=
  ⟨(termEffC_pop hfr.nodup hone hpar).mem_frames hfr.nodup,
   (termEffC_pop hfr.nodup hone hpar).ancestorC hfr⟩

/-- WC4 C6 effect (OB-C13): `exitFrameC` reparents exactly the live contexts whose initial frame had
the exiting frame as parent, to the immediate surviving parent of the exiting frame (its caller),
and changes no other parent. -/
theorem exitEffC_reparent (hfr : FramesC s) (hcall : (s.stk c).tail ≠ []) :
    s.parC ((s.stk c).headD 0) = some ((s.stk c).tail.headD 0) ∧
    ∀ d, (exitEffC s c).Live d → (exitEffC s c).ctxParent d =
      if s.ctxParent d = some ((s.stk c).headD 0) then some ((s.stk c).tail.headD 0)
      else s.ctxParent d :=
  ⟨(exitEffC_pop hfr.nodup hcall).pf, (exitEffC_pop hfr.nodup hcall).par⟩

/-- WC4 C6 effect, C7 (OB-C13): `terminate` reparents exactly the live contexts whose initial frame
had the terminated initial frame as parent, to the immediate parent of that frame. -/
theorem termEffC_reparent (hfr : FramesC s) (hone : (s.stk c).length = 1)
    (hpar : s.ctxParent c ≠ none) :
    s.parC ((s.stk c).headD 0) = some ((s.ctxParent c).getD 0) ∧
    ∀ d, (termEffC s c).Live d → (termEffC s c).ctxParent d =
      if s.ctxParent d = some ((s.stk c).headD 0) then some ((s.ctxParent c).getD 0)
      else s.ctxParent d :=
  ⟨(termEffC_pop hfr.nodup hone hpar).pf, (termEffC_pop hfr.nodup hone hpar).par⟩

/-- Theorem 3 (OB-C13; WC4 C6 effect; Spec 1 §73 effect): `exitFrameC` changes the kernel
components exactly as the effect of Spec 1 §73 on the view of `c`; reparenting changes only the
contexts, so it creates, elevates, revives and reanchors nothing. -/
theorem exitEffC_kernel (s : SC) (c : Nat) :
    (exitEffC s c).A = (exitEff (s.view c)).A ∧ (exitEffC s c).D = (exitEff (s.view c)).D ∧
    (exitEffC s c).P = s.P ∧ (exitEffC s c).I = s.I ∧ (exitEffC s c).dead = s.dead ∧
    (exitEffC s c).pins = s.pins ∧ (exitEffC s c).nF = s.nF :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Theorem 3 (OB-C13; WC4 C6, C7; Spec 1 §73 effect): `terminate` changes the kernel components
exactly as the effect of Spec 1 §73 on the view of `c`. -/
theorem termEffC_kernel (s : SC) (c : Nat) :
    (termEffC s c).A = (exitEff (s.view c)).A ∧ (termEffC s c).D = (exitEff (s.view c)).D ∧
    (termEffC s c).P = s.P ∧ (termEffC s c).I = s.I ∧ (termEffC s c).dead = s.dead ∧
    (termEffC s c).pins = s.pins ∧ (termEffC s c).nF = s.nF :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Steps

/-! ## Theorems 2 and 3 for `exitFrameC` and `terminate` -/

section Main

variable {k : K} {s s' : SC} {c : Nat}

/-- Theorem 3 (OB-C13; WC4 C6; Spec 1 §44, §73): an `ok` `exitFrameC` preserves `AnchorOrderC`
(not a precondition of O7) and establishes `AnchorOrderHeldC` (§73.5), with the reparented
initial frames. Fragment: states with the frame structure `FramesC`, `WF3` and `AnchorOrderC`
on the live frames. -/
theorem exitFrameC_anchorOrder (hfr : FramesC s) (hw : WF3 s.flat) (hao : AnchorOrderC s)
    (h : opStepC k .exit c s (.ok s')) : AnchorOrderC s' ∧ AnchorOrderHeldC s' := by
  obtain ⟨-, hg⟩ := h
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 hg
  exact ⟨(exitEffC_pop hfr.nodup hpre.hasCaller).anchorOrderC hfr hw hao rfl hpre.anchors
    hpre.origins, hpre.anchorOrderHeld⟩

/-- Theorem 3 (OB-C13; WC4 C6, C7; Spec 1 §44, §73): an `ok` `terminate` preserves
`AnchorOrderC` and establishes `AnchorOrderHeldC`, with the reparented initial frames.
Fragment: as `exitFrameC_anchorOrder`. -/
theorem terminate_anchorOrder (hfr : FramesC s) (hw : WF3 s.flat) (hao : AnchorOrderC s)
    (h : TermStep k s c (.ok s')) : AnchorOrderC s' ∧ AnchorOrderHeldC s' := by
  obtain ⟨-, hg⟩ := h
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 hg
  have hpar : s.ctxParent c ≠ none := fun e => by
    have := hpre.hasParent; rw [e] at this; exact this
  exact ⟨(termEffC_pop hfr.nodup hpre.initialOnly hpar).anchorOrderC hfr hw hao rfl
    hpre.anchors hpre.origins, hpre.anchorOrderHeld⟩

/-- Theorem 2 for `exitFrameC` (WC4 C6, C20, C23; Spec 1 §57, §73): an `ok` `exitFrameC`
preserves `KInvC` and the auxiliaries `RootHeldConv` and `HeldAnchored` of Spec 1 (not clauses
of §57) on the live frames. Fragment: O7 re-indexed. -/
theorem exitFrameC_preserves (hk : KInvC s) (haux : RootHeldConv s.flat)
    (hh : HeldAnchored s.flat) (h : opStepC k .exit c s (.ok s')) :
    KInvC s' ∧ RootHeldConv s'.flat ∧ HeldAnchored s'.flat := by
  obtain ⟨-, hg⟩ := h
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 hg
  have hfr := hk.1.1
  have hp := exitEffC_pop hfr.nodup hpre.hasCaller
  exact ⟨hp.kInvC hk (exitEffC_framesC hfr hpre.hasCaller) rfl hpre.anchors hpre.origins
    hpre.anchorOrderHeld, hp.aux hfr haux hh rfl hpre.origins⟩

/-- Theorem 2 for `terminate` (WC4 C7, C20, C23; Spec 1 §57, §73): an `ok` `terminate`
preserves `KInvC` and the auxiliaries `RootHeldConv` and `HeldAnchored` of Spec 1 on the live
frames. -/
theorem terminate_preserves (hk : KInvC s) (haux : RootHeldConv s.flat)
    (hh : HeldAnchored s.flat) (h : TermStep k s c (.ok s')) :
    KInvC s' ∧ RootHeldConv s'.flat ∧ HeldAnchored s'.flat := by
  obtain ⟨-, hg⟩ := h
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 hg
  have hfr := hk.1.1
  have hpar : s.ctxParent c ≠ none := fun e => by
    have := hpre.hasParent; rw [e] at this; exact this
  have hp := termEffC_pop hfr.nodup hpre.initialOnly hpar
  exact ⟨hp.kInvC hk (termEffC_framesC hfr hpre.nonInitial hpre.initialOnly hpar) rfl
    hpre.anchors hpre.origins hpre.anchorOrderHeld, hp.aux hfr haux hh rfl hpre.origins⟩

end Main

end Ern.Concurrency
