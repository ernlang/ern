import Ern.ConcurrencyModel.Rc11
import Ern.ConcurrencyModel.EventLemmas

/-!
# Theorem 10e: the canonical projection of the RC11 fragment to ERN graphs (C34; `OB-C23`,
`OB-C26`)

`rc11.cat` and the corrigendum named below are the sources identified in the header of `Rc11`:
`rc11.cat` of herdtools7 7.58 and the corrigendum named by C34.

`proj` is the canonical projection `π`, from the fragment of `Rc11` to
the event graphs of `EventGraph`, entirely determined:

* events: one ERN event per event of the fragment outside a pair, one per pair `(r, w)`; the pair
  is represented by its read component, its write component is dropped (`PE`);
* units: one atomic unit per location, covering the byte of its index;
* contexts: one per thread; each initial write alone in a context of its own; `proj` adds no `po`
  edge, and an `sb` edge from an initial write is not transported;
* `po`: the `sb` order of the thread, a pair counting for one event;
* `rf` and `mo`: transported; a pair appears through its write component as a source of `rf` or as
  a modification, through its read component as a target of `rf` (`wc`);
* values: those of the components; the image of a pair carries the value read by `r` and the value
  written by `w`;
* orders, by the order table: a read `RLX`, `ACQ`, `SC` to `relaxed`, `acquire`, `seq_cst`;
  a write `RLX`, `REL`, `SC` to `relaxed`, `release`, `seq_cst`; the five pair rows to the five
  RMW orders; an initial write to a non-atomic write designating the unit (C31), with no order;
* no `sync` event, no `validity` event, no marker: the `sw` of the image reduces to its atomic
  source.

The image is not claimed free of races in the sense of C33, which is not a conjunct.

Statement (b): for every finite graph of the fragment consistent for RC11 with the amended `psc`,
the image satisfies `EventConsistent` (`proj_consistent`). Finiteness serves only the atomic `sw`
edges: RC11 extends a release sequence by `(rf ; myrmw)*` chains, C48 by an `mo` segment (retained
reading 5), and statement 3 of `EventLemmas` makes them coincide on a finite graph. Each conjunct
is proved from the checks it needs (`proj_rfWF` … `proj_scConsistent`).
-/

namespace Ern.ConcurrencyModel.Rc11

open Relation
open Ern.ConcurrencyModel (MemOrder)

namespace Graph

variable {E T V : Type} (G : Graph E T V)

/-! ## The projection -/

/-- The write component of an event: the partner of the read component of a pair, the event itself
otherwise. -/
def wc (e : E) : E := (G.partner e).getD e

/-- The event is the write component of a pair. -/
def IsPairW (e : E) : Prop := ∃ r, G.partner r = some e

/-- The events of the image: every event but the write components of pairs. -/
abbrev PE := {e : E // ¬ G.IsPairW e}

/-- The order of the image of a read (order table of the module header). -/
def ordR : Ann → MemOrder
  | .acq => .acquire
  | .sc => .seqCst
  | _ => .relaxed

/-- The order of the image of a write (order table of the module header). -/
def ordW : Ann → MemOrder
  | .rel => .release
  | .sc => .seqCst
  | _ => .relaxed

/-- The order of the image of a pair, from the annotations of its read and write components (the
five pair rows of the order table of the module header). -/
def ordPair : Ann → Ann → MemOrder
  | .rlx, .rlx => .relaxed
  | .acq, .rlx => .acquire
  | .rlx, .rel => .release
  | .acq, .rel => .acqRel
  | .sc, .sc => .seqCst
  | _, _ => .relaxed

/-- The access of the image of an event (C27, C31, C40; order table of the module header). -/
def accOf (e : E) : Events.Acc Nat V :=
  match G.lab e with
  | .init l v => .unit l (.write v)
  | .write _ l v a => .atomic l (ordW a) (.write v)
  | .read _ l v a =>
    match G.partner e with
    | none => .atomic l (ordR a) (.read v)
    | some w =>
      match G.lab w with
      | .write _ _ v' a' => .atomic l (ordPair a a') (.rmw v v')
      | _ => .atomic l (ordR a) (.read v)

/-- The context of the image of an event: its thread, or the initial write itself. -/
def ctxOf (e : E) : T ⊕ E :=
  match G.lab e with
  | .init .. => .inr e
  | .read t .. | .write t .. => .inl t

/-- Every event of the fragment is an initial write, a write, a read outside a pair, or the read
component of a pair whose write component has the same thread and location. -/
theorem classify (hF : G.Frag) (e : E) :
    (∃ l v, G.lab e = .init l v ∧ G.partner e = none) ∨
    (∃ t l v a, G.lab e = .write t l v a ∧ G.partner e = none) ∨
    (∃ t l v a, G.lab e = .read t l v a ∧ G.partner e = none) ∨
    (∃ t l v a w v' a', G.lab e = .read t l v a ∧ G.partner e = some w ∧
      G.lab w = .write t l v' a') := by
  have hnp : ¬ G.R e → G.partner e = none := fun hr => by
    cases hp : G.partner e with
    | none => rfl
    | some w => exact (hr (hF.rmw_read e w hp)).elim
  cases hl : G.lab e with
  | init l v => exact .inl ⟨l, v, rfl, hnp (by simp [R, hl, Lab.isR])⟩
  | write t l v a => exact .inr (.inl ⟨t, l, v, a, rfl, hnp (by simp [R, hl, Lab.isR])⟩)
  | read t l v a =>
    cases hp : G.partner e with
    | none => exact .inr (.inr (.inl ⟨t, l, v, a, rfl, rfl⟩))
    | some w =>
      have hw := hF.rmw_write e w hp
      have ht := hF.rmw_thread e w hp
      have hlc := hF.rmw_loc e w hp
      cases hlw : G.lab w with
      | init => simp [hlw, Lab.isIW] at hw
      | read => simp [hlw, Lab.isW] at hw
      | write t' l' v' a' =>
        simp only [loc, hl, hlw, Lab.loc] at hlc
        simp only [hl, hlw, Lab.thread?, Option.some.injEq] at ht
        subst ht hlc
        exact .inr (.inr (.inr ⟨t, l, v, a, w, v', a', rfl, rfl, hlw⟩))

/-- The context of an event of a thread is the thread. -/
theorem ctxOf_inl {e : E} {t : T} : G.ctxOf e = .inl t ↔ (G.lab e).thread? = some t := by
  unfold ctxOf; cases G.lab e <;> simp [Lab.thread?]

/-- An event whose context is an event is that event, an initial write. -/
theorem ctxOf_inr {e x : E} (h : G.ctxOf e = .inr x) : x = e := by
  unfold ctxOf at h; cases hl : G.lab e <;> simp_all

/-- The image of a fragment graph, the canonical projection `π` of the module header. -/
def proj (hF : G.Frag) : Events.Graph G.PE (T ⊕ E) Nat V Unit where
  ev a := ⟨G.ctxOf a.1, ⟨0, 0⟩, .marks (some (G.accOf a.1)) none⟩
  uRange l := ⟨l, 1⟩
  po a b := G.sb a.1 b.1 ∧ ¬ G.IW a.1
  rf a b := G.rf (G.wc a.1) b.1
  mo a b := G.mo (G.wc a.1) (G.wc b.1)
  po_irrefl a h := hF.sb_irrefl _ h.1
  po_trans h₁ h₂ := ⟨hF.sb_trans _ _ _ h₁.1 h₂.1, h₁.2⟩
  po_ctx {a b} h := by
    show G.ctxOf a.1 = G.ctxOf b.1
    obtain ⟨hs, hi⟩ := h
    have hb := hF.sb_not_init _ _ hs
    unfold ctxOf
    cases ha : G.lab a.1 with
    | init => simp [IW, ha, Lab.isIW] at hi
    | read t l v o =>
      have := hF.sb_thread _ _ t hs (by simp [ha, Lab.thread?])
      cases hbl : G.lab b.1 <;> simp_all [Lab.thread?, IW, Lab.isIW]
    | write t l v o =>
      have := hF.sb_thread _ _ t hs (by simp [ha, Lab.thread?])
      cases hbl : G.lab b.1 <;> simp_all [Lab.thread?, IW, Lab.isIW]
  po_total {a b} hc hne := by
    change G.ctxOf a.1 = G.ctxOf b.1 at hc
    have hst : ∀ t, (G.lab a.1).thread? = some t → (G.lab b.1).thread? = some t →
        (G.sb a.1 b.1 ∧ ¬ G.IW a.1) ∨ (G.sb b.1 a.1 ∧ ¬ G.IW b.1) := fun t ha hb => by
      have hiw : ∀ e, (G.lab e).thread? = some t → ¬ G.IW e := fun e he hi => by
        simp only [IW] at hi; cases h : G.lab e <;> simp_all [Lab.isIW, Lab.thread?]
      rcases hF.sb_total _ _ t ha hb (fun e => hne (Subtype.ext e)) with h | h
      · exact .inl ⟨h, hiw _ ha⟩
      · exact .inr ⟨h, hiw _ hb⟩
    rcases hca : G.ctxOf a.1 with t | x
    · exact hst t (G.ctxOf_inl.1 hca) (G.ctxOf_inl.1 (hc.symm.trans hca))
    · exact (hne (Subtype.ext ((G.ctxOf_inr hca).symm.trans
        (G.ctxOf_inr (hc.symm.trans hca))))).elim

/-! ## The write component -/

/-- The write component of an event outside a pair is the event. -/
theorem wc_none {e : E} (h : G.partner e = none) : G.wc e = e := by unfold wc; rw [h]; rfl

/-- The write component of the read component of a pair is its partner. -/
theorem wc_some {e w : E} (h : G.partner e = some w) : G.wc e = w := by unfold wc; rw [h]; rfl

variable {G} (hF : G.Frag)
include hF

/-- `wc` is injective on the events of the image. -/
theorem wc_inj {a b : G.PE} (h : G.wc a.1 = G.wc b.1) : a = b := by
  apply Subtype.ext
  cases ha : G.partner a.1 with
  | none =>
    cases hb : G.partner b.1 with
    | none => rwa [G.wc_none ha, G.wc_none hb] at h
    | some w =>
      rw [G.wc_none ha, G.wc_some hb] at h
      exact (a.2 ⟨b.1, h ▸ hb⟩).elim
  | some w =>
    cases hb : G.partner b.1 with
    | none =>
      rw [G.wc_some ha, G.wc_none hb] at h
      exact (b.2 ⟨a.1, h ▸ ha⟩).elim
    | some w' =>
      rw [G.wc_some ha, G.wc_some hb] at h
      subst h
      exact hF.rmw_inj _ _ _ ha hb

/-- The shape of the image of an event, with its access and its write component. -/
theorem shape (e : E) :
    (∃ l v, G.lab e = .init l v ∧ G.accOf e = .unit l (.write v) ∧ G.wc e = e) ∨
    (∃ t l v o, G.lab e = .write t l v o ∧ G.accOf e = .atomic l (ordW o) (.write v) ∧
      G.wc e = e) ∨
    (∃ t l v o, G.lab e = .read t l v o ∧ G.partner e = none ∧
      G.accOf e = .atomic l (ordR o) (.read v) ∧ G.wc e = e) ∨
    (∃ t l v o w v' o', G.lab e = .read t l v o ∧ G.partner e = some w ∧
      G.lab w = .write t l v' o' ∧ G.accOf e = .atomic l (ordPair o o') (.rmw v v') ∧
      G.wc e = w) := by
  rcases G.classify hF e with ⟨l, v, hl, hp⟩ | ⟨t, l, v, o, hl, hp⟩ | ⟨t, l, v, o, hl, hp⟩ |
    ⟨t, l, v, o, w, v', o', hl, hp, hw⟩
  · exact .inl ⟨l, v, hl, by simp [accOf, hl], G.wc_none hp⟩
  · exact .inr (.inl ⟨t, l, v, o, hl, by simp [accOf, hl], G.wc_none hp⟩)
  · exact .inr (.inr (.inl ⟨t, l, v, o, hl, hp, by simp [accOf, hl, hp], G.wc_none hp⟩))
  · exact .inr (.inr (.inr ⟨t, l, v, o, w, v', o', hl, hp, hw, by simp [accOf, hl, hp, hw],
      G.wc_some hp⟩))

/-- The write component has the location of the event. -/
theorem loc_wc (e : E) : (G.lab (G.wc e)).loc = (G.lab e).loc := by
  rcases shape hF e with ⟨_, _, -, -, h⟩ | ⟨_, _, _, _, -, -, h⟩ | ⟨_, _, _, _, -, -, -, h⟩ |
    ⟨_, _, _, _, _, _, _, hl, -, hw, -, h⟩ <;> rw [h]
  rw [hl, hw]; rfl

/-! ## The attributes of the image -/

omit hF in
/-- The access of the image of an event (order table of the module header). -/
theorem proj_acc (hF : G.Frag) (a : G.PE) : (G.proj hF).acc? a = some (G.accOf a.1) := rfl

/-- The unit of the image of an event is its location. -/
theorem proj_unitOf (a : G.PE) : (G.proj hF).unitOf a = some (G.lab a.1).loc := by
  unfold Events.Graph.unitOf; rw [proj_acc hF]
  rcases shape hF a.1 with ⟨l, v, hl, h, -⟩ | ⟨t, l, v, o, hl, h, -⟩ | ⟨t, l, v, o, hl, -, h, -⟩ |
    ⟨t, l, v, o, w, v', o', hl, -, -, h, -⟩ <;> rw [h, hl] <;> rfl

/-- The image of an event writes exactly when its write component is a write. -/
theorem proj_writes_iff (a : G.PE) : (G.proj hF).Writes a ↔ G.W (G.wc a.1) := by
  unfold Events.Graph.Writes Events.Graph.kind?; rw [proj_acc hF]
  rcases shape hF a.1 with ⟨l, v, hl, h, hw⟩ | ⟨t, l, v, o, hl, h, hw⟩ |
    ⟨t, l, v, o, hl, -, h, hw⟩ | ⟨t, l, v, o, w, v', o', hl, -, hlw, h, hw⟩ <;>
    rw [h, hw]
  · simp [W, hl, Lab.isW, Events.UKind.kind, Events.Kind.Writes]
  · simp [W, hl, Lab.isW, Events.UKind.kind, Events.Kind.Writes]
  · simp [W, hl, Lab.isW, Events.UKind.kind, Events.Kind.Writes]
  · simp [W, hlw, Lab.isW, Events.UKind.kind, Events.Kind.Writes]

/-- The image of an event reads exactly when the event is a read. -/
theorem proj_reads_iff (a : G.PE) : (G.proj hF).Reads a ↔ G.R a.1 := by
  unfold Events.Graph.Reads Events.Graph.kind?; rw [proj_acc hF]
  rcases shape hF a.1 with ⟨l, v, hl, h, -⟩ | ⟨t, l, v, o, hl, h, -⟩ |
    ⟨t, l, v, o, hl, -, h, -⟩ | ⟨t, l, v, o, w, v', o', hl, -, -, h, -⟩ <;>
    rw [h] <;> simp [R, hl, Lab.isR, Events.UKind.kind, Events.Kind.Reads]

/-- The modifications of a unit in the image (C31): the events whose write component is a write of
that location. -/
theorem proj_modOn_iff (a : G.PE) (u : Nat) :
    (G.proj hF).ModOn a u ↔ G.W (G.wc a.1) ∧ (G.lab a.1).loc = u := by
  unfold Events.Graph.ModOn
  rw [proj_unitOf hF, proj_writes_iff hF, Option.some.injEq, and_comm]

/-- The read components of a unit in the image (C31): the reads of that location. -/
theorem proj_readOn_iff (a : G.PE) (u : Nat) :
    (G.proj hF).ReadOn a u ↔ G.R a.1 ∧ (G.lab a.1).loc = u := by
  unfold Events.Graph.ReadOn
  rw [proj_unitOf hF, proj_reads_iff hF, Option.some.injEq, and_comm]

/-- The RMW events of the image are the read components of the pairs. -/
theorem proj_isRMW_iff (a : G.PE) : (G.proj hF).IsRMW a ↔ ∃ w, G.partner a.1 = some w := by
  unfold Events.Graph.IsRMW Events.Graph.kind?; rw [proj_acc hF]
  rcases shape hF a.1 with ⟨l, v, hl, h, -⟩ | ⟨t, l, v, o, hl, h, -⟩ |
    ⟨t, l, v, o, hl, hp, h, -⟩ | ⟨t, l, v, o, w, v', o', hl, hp, -, h, -⟩ <;> rw [h]
  · have := (G.classify hF a.1); simp_all [Events.UKind.kind]
  · have := (G.classify hF a.1); simp_all [Events.UKind.kind]
  · simp [Events.UKind.kind, hp]
  · simp [Events.UKind.kind, hp]

/-- The value written by the image of an event is the value of its write component (order table
of the module header). -/
theorem proj_valW (a : G.PE) (h : G.W (G.wc a.1)) :
    (G.proj hF).valW a = some (G.lab (G.wc a.1)).val := by
  unfold Events.Graph.valW; rw [proj_acc hF]
  rcases shape hF a.1 with ⟨l, v, hl, hacc, hw⟩ | ⟨t, l, v, o, hl, hacc, hw⟩ |
    ⟨t, l, v, o, hl, -, hacc, hw⟩ | ⟨t, l, v, o, w, v', o', hl, -, hlw, hacc, hw⟩ <;>
    rw [hacc] <;> rw [hw] at h ⊢
  · rw [hl]; rfl
  · rw [hl]; rfl
  · simp [W, hl, Lab.isW] at h
  · rw [hlw]; rfl

/-- The value read by the image of a read is its value (order table of the module header). -/
theorem proj_valR (a : G.PE) (h : G.R a.1) : (G.proj hF).valR a = some (G.lab a.1).val := by
  unfold Events.Graph.valR; rw [proj_acc hF]
  rcases shape hF a.1 with ⟨l, v, hl, hacc, -⟩ | ⟨t, l, v, o, hl, hacc, -⟩ |
    ⟨t, l, v, o, hl, -, hacc, -⟩ | ⟨t, l, v, o, w, v', o', hl, -, -, hacc, -⟩ <;> rw [hacc]
  · simp [R, hl, Lab.isR] at h
  · simp [R, hl, Lab.isR] at h
  · rw [hl]; rfl
  · rw [hl]; rfl

/-- The representative in the image of a write: the read component of its pair, or itself. -/
theorem rep_exists {w : E} (hw : G.W w) : ∃ a : G.PE, G.wc a.1 = w := by
  by_cases hp : G.IsPairW w
  · obtain ⟨r, hr⟩ := hp
    refine ⟨⟨r, fun ⟨x, hx⟩ => ?_⟩, G.wc_some hr⟩
    exact not_R_W (hF.rmw_read r w hr) (hF.rmw_write x r hx).1
  · refine ⟨⟨w, hp⟩, G.wc_none ?_⟩
    cases h : G.partner w with
    | none => rfl
    | some _ => exact (not_R_W (hF.rmw_read w _ h) hw).elim

/-! ## Conjuncts 1 and 2 of the image (C34.1, C34.2) -/

/-- **Conjunct 1 of the image** (C34.1): from the fragment alone. -/
theorem proj_rfWF : (G.proj hF).RfWF := by
  refine ⟨fun a b h => ?_, fun r u hr => ?_, fun a b h => ?_⟩
  · obtain ⟨hw, hr, hl, -⟩ := hF.rf_type _ _ h
    refine ⟨(G.lab a.1).loc, (proj_modOn_iff hF a _).2 ⟨hw, rfl⟩, (proj_readOn_iff hF b _).2
      ⟨hr, ?_⟩⟩
    have := loc_wc hF a.1
    simp only [loc] at hl
    rw [← hl, this]
  · have hR := ((proj_readOn_iff hF r u).1 hr).1
    obtain ⟨w, hrf⟩ := hF.rf_exists _ hR
    obtain ⟨a, ha⟩ := rep_exists hF (hF.rf_type _ _ hrf).1
    refine ⟨⟨a, show G.rf (G.wc a.1) r.1 from ha ▸ hrf⟩, fun w₁ w₂ h₁ h₂ => ?_⟩
    exact wc_inj hF (hF.rf_unique _ _ _ h₁ h₂)
  · obtain ⟨hw, hr, -, hv⟩ := hF.rf_type _ _ h
    exact ⟨_, proj_valW hF a hw, by rw [proj_valR hF b hr]; exact congrArg some hv.symm⟩

/-- **Conjunct 2 of the image** (C34.2): from the fragment alone. -/
theorem proj_moTotal : (G.proj hF).MoTotal := by
  refine ⟨fun a b h => ?_, fun u => ⟨fun a _ h => hF.mo_irrefl _ h,
    fun a b c _ _ _ h₁ h₂ => hF.mo_trans _ _ _ h₁ h₂, fun a b ha hb hne => ?_⟩⟩
  · obtain ⟨hwa, hwb, hl⟩ := hF.mo_type _ _ h
    refine ⟨(G.lab a.1).loc, (proj_modOn_iff hF a _).2 ⟨hwa, rfl⟩,
      (proj_modOn_iff hF b _).2 ⟨hwb, ?_⟩⟩
    simp only [loc] at hl
    rw [← loc_wc hF b.1, ← hl, loc_wc hF a.1]
  · obtain ⟨hwa, hla⟩ := (proj_modOn_iff hF a u).1 ha
    obtain ⟨hwb, hlb⟩ := (proj_modOn_iff hF b u).1 hb
    refine hF.mo_total _ _ hwa hwb ?_ fun e => hne (wc_inj hF e)
    show (G.lab (G.wc a.1)).loc = (G.lab (G.wc b.1)).loc
    rw [loc_wc hF, loc_wc hF, hla, hlb]

/-! ## Conjunct 3 of the image (C34.3) -/

omit hF in
/-- On the fragment, under `coherencermw` and `atomicity`, the `rf` source of the read component
of a pair is the immediate `mo`-predecessor of its write component. -/
theorem pair_src (hF : G.Frag) (hcr : G.CoherenceRmw) (hat : G.Atomicity) {z r w : E}
    (hrf : G.rf z r) (hp : G.rmw r w) : G.mo z w ∧ ∀ x, ¬ (G.mo z x ∧ G.mo x w) := by
  obtain ⟨hz, hr, hlz, -⟩ := hF.rf_type _ _ hrf
  have hw := (hF.rmw_write r w hp).1
  refine ⟨?_, fun x ⟨h₁, h₂⟩ => ?_⟩
  · by_cases hzw : z = w
    · subst hzw
      exact (hcr r z (.inr hp) (.single (.inl hrf))).elim
    · rcases hF.mo_total z w hz hw (hlz.trans (hF.rmw_loc r w hp)) hzw with h | h
      · exact h
      · exact (hcr r w (.inr hp) (.tail (.single (.inr (.inl h))) (.inl hrf))).elim
  · have hxW := (hF.mo_type _ _ h₁).2.1
    exact hat r w (.inr hp) ⟨x, ⟨⟨z, hrf, h₁⟩, fun e => not_R_W hr (e ▸ hxW)⟩, h₂⟩

/-- **Conjunct 3 of the image** (C34.3): from the fragment, `coherencermw` and `atomicity`. -/
theorem proj_rmwAtomic (hcr : G.CoherenceRmw) (hat : G.Atomicity) :
    (G.proj hF).RmwAtomic := by
  intro w r hr _ hrf
  obtain ⟨pw, hp⟩ := (proj_isRMW_iff hF r).1 hr
  have ⟨hmo, himm⟩ := pair_src hF hcr hat hrf hp
  refine ⟨show G.mo (G.wc w.1) (G.wc r.1) by rw [G.wc_some hp]; exact hmo, fun x hx => ?_⟩
  obtain ⟨h₁, h₂⟩ := hx
  change G.mo (G.wc x.1) (G.wc r.1) at h₂
  rw [G.wc_some hp] at h₂
  exact himm _ ⟨h₁, h₂⟩

/-! ## `po`, `sw` and `hb` of the image -/

/-- An event precedes its write component in `sb`, or is it. -/
theorem sb_wc (e : E) : e = G.wc e ∨ G.sb e (G.wc e) := by
  cases hp : G.partner e with
  | none => exact .inl (G.wc_none hp).symm
  | some w => rw [G.wc_some hp]; exact .inr (hF.rmw_sb _ _ hp)

/-- The write component of an event of the image is the partner of no event. -/
theorem partner_wc (a : G.PE) : G.partner (G.wc a.1) = none := by
  cases hp : G.partner a.1 with
  | none => rw [G.wc_none hp]; exact hp
  | some w =>
    rw [G.wc_some hp]
    cases hw : G.partner w with
    | none => rfl
    | some _ => exact (not_R_W (hF.rmw_read _ _ hw) (hF.rmw_write _ _ hp).1).elim

/-- A `po` edge of the image is an `sb` edge from the write component (a pair counts for one
event: its write component immediately follows its read component). -/
theorem proj_po_sb {a b : G.PE} (h : (G.proj hF).po a b) : G.sb (G.wc a.1) b.1 := by
  obtain ⟨hs, -⟩ := h
  cases hp : G.partner a.1 with
  | none => rw [G.wc_none hp]; exact hs
  | some w =>
    rw [G.wc_some hp]
    have hR := hF.rmw_read _ _ hp
    obtain ⟨t, ht⟩ : ∃ t, (G.lab a.1).thread? = some t := by
      simp only [R] at hR; cases h : G.lab a.1 <;> simp_all [Lab.isR, Lab.thread?]
    have hbt := hF.sb_thread _ _ t hs ht
    have hwt : (G.lab w).thread? = some t := (hF.rmw_thread _ _ hp) ▸ ht
    have hne : b.1 ≠ w := fun e => b.2 ⟨a.1, e ▸ hp⟩
    rcases hF.sb_total _ _ t hbt hwt hne with h | h
    · exact (hF.rmw_imm _ _ _ hp ⟨hs, h⟩).elim
    · exact h

omit hF in
/-- A pair row with a release-capable order has its write component annotated `REL` or `SC`. -/
theorem ordPair_rel {o o' : Ann}
    (h : ordPair o o' = .release ∨ ordPair o o' = .acqRel ∨ ordPair o o' = .seqCst) :
    o' = .rel ∨ o' = .sc := by
  cases o <;> cases o' <;> simp_all [ordPair]

omit hF in
/-- A pair row with an acquire-capable order has its read component annotated `ACQ` or `SC`. -/
theorem ordPair_acq {o o' : Ann}
    (h : ordPair o o' = .acquire ∨ ordPair o o' = .acqRel ∨ ordPair o o' = .seqCst) :
    o = .acq ∨ o = .sc := by
  cases o <;> cases o' <;> simp_all [ordPair]

/-- A release-capable event of the image has a write component annotated `REL` or `SC`. -/
theorem proj_relCap {a : G.PE} {u : Nat} (h : (G.proj hF).RelCap a u) :
    G.W (G.wc a.1) ∧ (G.REL (G.wc a.1) ∨ G.SC (G.wc a.1)) := by
  obtain ⟨o, k, hacc, hw, ho⟩ := h
  rw [proj_acc hF, Option.some.injEq] at hacc
  rcases shape hF a.1 with ⟨l, v, hl, h, -⟩ | ⟨t, l, v, o', hl, h, hwc⟩ |
    ⟨t, l, v, o', hl, -, h, -⟩ | ⟨t, l, v, o', w, v', o'', hl, -, hlw, h, hwc⟩ <;>
    rw [h] at hacc <;> cases hacc
  · rw [hwc]
    refine ⟨by simp [W, hl, Lab.isW], ?_⟩
    cases o' <;> simp_all [ordW, REL, SC, Lab.ann?]
  · exact hw.elim
  · rw [hwc]
    refine ⟨by simp [W, hlw, Lab.isW], ?_⟩
    rcases ordPair_rel ho with rfl | rfl <;> simp [REL, SC, hlw, Lab.ann?]

/-- An acquire-capable event of the image is a read annotated `ACQ` or `SC`. -/
theorem proj_acqCap {b : G.PE} {u : Nat} (h : (G.proj hF).AcqCap b u) :
    G.R b.1 ∧ (G.ACQ b.1 ∨ G.SC b.1) := by
  obtain ⟨o, k, hacc, hr, ho⟩ := h
  rw [proj_acc hF, Option.some.injEq] at hacc
  rcases shape hF b.1 with ⟨l, v, hl, h, -⟩ | ⟨t, l, v, o', hl, h, -⟩ |
    ⟨t, l, v, o', hl, -, h, -⟩ | ⟨t, l, v, o', w, v', o'', hl, -, -, h, -⟩ <;>
    rw [h] at hacc <;> cases hacc
  · exact hr.elim
  · refine ⟨by simp [R, hl, Lab.isR], ?_⟩
    cases o' <;> simp_all [ordR, ACQ, SC, Lab.ann?]
  · refine ⟨by simp [R, hl, Lab.isR], ?_⟩
    rcases ordPair_acq ho with rfl | rfl <;> simp [ACQ, SC, hl, Lab.ann?]

omit hF in
/-- An event annotated `REL`, `SC` or `ACQ` is in `RLX | REL | ACQ_REL | ACQ | SC`. -/
theorem atomic_of_ann {e : E} (h : G.REL e ∨ G.SC e ∨ G.ACQ e) : G.Atomic e := by
  rcases h with h | h | h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inr (.inr h)))
  · exact .inr (.inr (.inr (.inl h)))

omit hF in
/-- The events of the image of a finite graph are finitely many. -/
theorem finite_PE (hfin : Events.Finite E) : Events.Finite G.PE := by
  classical
  obtain ⟨l, hl⟩ := hfin
  refine ⟨l.filterMap (fun e => if h : ¬ G.IsPairW e then some ⟨e, h⟩ else none), fun a => ?_⟩
  exact List.mem_filterMap.2 ⟨a.1, hl a.1, by simp [a.2]⟩

/-- A chain of the image is a `(rf; rmw)+` path between the write components. -/
theorem proj_chain_rfMy {u : Nat} {a m : G.PE} (h : (G.proj hF).Chain u a m) :
    TransGen G.rfMy (G.wc a.1) (G.wc m.1) := by
  induction h with
  | @one m hm hrf =>
    obtain ⟨w, hp⟩ := (proj_isRMW_iff hF m).1 ((G.proj hF).isRMW_of_rmw hm)
    rw [show G.wc m.1 = w from G.wc_some hp]
    exact .single ⟨m.1, hrf, .inr hp⟩
  | @step x m _ hm hrf ih =>
    obtain ⟨w, hp⟩ := (proj_isRMW_iff hF m).1 ((G.proj hF).isRMW_of_rmw hm)
    rw [show G.wc m.1 = w from G.wc_some hp] at *
    exact .tail ih ⟨m.1, hrf, .inr hp⟩

/-- An `sw` edge of the image is an `sw` edge of RC11 from the write component, on a finite graph
of the fragment under `coherencermw` and `atomicity`: the member of the release sequence (retained
reading 5) is reached from the head by an `rf` chain (statement 3 of `EventLemmas`), that is by
`(rf; myrmw)*`. -/
theorem proj_sw (hfin : Events.Finite E) (hcr : G.CoherenceRmw) (hat : G.Atomicity)
    {a b : G.PE} (h : (G.proj hF).SW a b) : G.sw (G.wc a.1) b.1 := by
  rcases h with ⟨u, m, hrel, hacq, hm, hrf⟩ | ⟨c, ha, -⟩ | ⟨c, ha, -⟩
  · obtain ⟨hW, hra⟩ := proj_relCap hF hrel
    obtain ⟨hR, hab⟩ := proj_acqCap hF hacq
    have hpath : RTC G.rfMy (G.wc a.1) (G.wc m.1) := by
      by_cases hma : m = a
      · subst hma; exact .inl rfl
      · have hc := ((G.proj hF).rsMember_iff_chain (finite_PE hfin) (proj_rfWF hF)
          (proj_moTotal hF) (proj_rmwAtomic hF hcr hat)).1 ⟨hm, hma⟩
        exact .inr (proj_chain_rfMy hF hc.2)
    refine ⟨hra.elim (fun h => .inl h) (fun h => .inr (.inr h)), ⟨G.wc m.1,
      ⟨hW, G.wc a.1, .inl rfl, hW, G.atomic_of_ann (hra.elim .inl (fun h => .inr (.inl h))),
        hpath⟩, hrf⟩, hR, G.atomic_of_ann (hab.elim (fun h => .inr (.inr h)) (fun h => .inr (.inl h))),
      hab.elim .inl (fun h => .inr (.inr h))⟩
  · cases ha
  · cases ha

/-- `hb` of the image is `hb` of RC11 from the write component. -/
theorem proj_hb (hfin : Events.Finite E) (hcr : G.CoherenceRmw) (hat : G.Atomicity)
    {a b : G.PE} (h : (G.proj hF).HB a b) : G.hb (G.wc a.1) b.1 := by
  have edge : ∀ {x y : G.PE}, (G.proj hF).PoSw x y → G.sbsw (G.wc x.1) y.1 := by
    rintro x y (h | h)
    · exact .inl (proj_po_sb hF h)
    · exact .inr (proj_sw hF hfin hcr hat h)
  induction h with
  | single h => exact .single (edge h)
  | @tail c b _ h ih =>
    have hc : G.hb (G.wc a.1) (G.wc c.1) := by
      rcases sb_wc hF c.1 with e | e
      · rw [← e]; exact ih
      · exact .tail ih (.inl e)
    exact .tail hc (edge h)

/-- `hb` of the image, to the write component of the target. -/
theorem proj_hb_wc (hfin : Events.Finite E) (hcr : G.CoherenceRmw) (hat : G.Atomicity)
    {a b : G.PE} (h : (G.proj hF).HB a b) : G.hb (G.wc a.1) (G.wc b.1) := by
  have := proj_hb hF hfin hcr hat h
  rcases sb_wc hF b.1 with e | e
  · rw [← e]; exact this
  · exact .tail this (.inl e)

/-! ## `eco` of the image -/

/-- An `rb` edge of the image from the read component of a pair starts, in RC11, at the write
component of the pair, through `mo`. -/
theorem proj_rb_mo (hcr : G.CoherenceRmw) (hat : G.Atomicity) {x y : G.PE}
    (h : (G.proj hF).RB x y) : G.rb x.1 (G.wc y.1) ∧ ∀ w, G.partner x.1 = some w →
      G.mo w (G.wc y.1) := by
  obtain ⟨⟨s, hrf, hmo⟩, hne⟩ := h
  change G.rf (G.wc s.1) x.1 at hrf
  change G.mo (G.wc s.1) (G.wc y.1) at hmo
  have hR := (hF.rf_type _ _ hrf).2.1
  have hyW := (hF.mo_type _ _ hmo).2.1
  refine ⟨⟨⟨_, hrf, hmo⟩, fun e => not_R_W hR (e ▸ hyW)⟩, fun w hp => ?_⟩
  obtain ⟨hsw, himm⟩ := pair_src hF hcr hat hrf hp
  have hwW := (hF.rmw_write _ _ hp).1
  have hl : G.loc (G.wc y.1) w := by
    have h1 := (hF.mo_type _ _ hmo).2.2
    have h2 := (hF.mo_type _ _ hsw).2.2
    simp only [loc] at h1 h2 ⊢; rw [← h1, h2]
  have hyw : G.wc y.1 ≠ w := fun e => hne (wc_inj hF (by rw [G.wc_some hp, e]))
  rcases hF.mo_total _ _ hyW hwW hl hyw with h | h
  · exact (himm _ ⟨hmo, h⟩).elim
  · exact h

/-- An edge of `rf ∪ mo ∪ rb` of the image is an `eco` path of RC11 between the write
components. -/
theorem proj_ecoBase (hcr : G.CoherenceRmw) (hat : G.Atomicity) {x y : G.PE}
    (h : (G.proj hF).EcoBase x y) : G.eco (G.wc x.1) (G.wc y.1) := by
  rcases h with h | h | h
  · change G.rf (G.wc x.1) y.1 at h
    cases hp : G.partner y.1 with
    | none => rw [G.wc_none hp]; exact .single (.inl h)
    | some w => rw [G.wc_some hp]; exact .single (.inr (.inl (pair_src hF hcr hat h hp).1))
  · exact .single (.inr (.inl h))
  · obtain ⟨hrb, hmo⟩ := proj_rb_mo hF hcr hat h
    cases hp : G.partner x.1 with
    | none => rw [G.wc_none hp]; exact .single (.inr (.inr hrb))
    | some w => rw [G.wc_some hp]; exact .single (.inr (.inl (hmo w hp)))

/-- `eco` of the image is `eco` of RC11 between the write components. -/
theorem proj_eco (hcr : G.CoherenceRmw) (hat : G.Atomicity) {x y : G.PE}
    (h : (G.proj hF).ECO x y) : G.eco (G.wc x.1) (G.wc y.1) := by
  induction h with
  | single h => exact proj_ecoBase hF hcr hat h
  | tail _ h ih => exact TransGen.trans ih (proj_ecoBase hF hcr hat h)

/-! ## Conjuncts 4 to 7 of the image (C34.4–C34.7) -/

/-- **Conjunct 5 of the image** (C34.5): on a finite graph, from `coherence1`, `coherencermw` and
`atomicity`. -/
theorem proj_hbIrrefl (hfin : Events.Finite E) (hc1 : G.Coherence1) (hcr : G.CoherenceRmw)
    (hat : G.Atomicity) : (G.proj hF).HbIrrefl := fun _ h =>
  hc1 _ _ (proj_hb_wc hF hfin hcr hat h) (.inl rfl)

/-- **Conjunct 4 of the image** (C34.4): on a finite graph, from `coherence1`, `coherencermw` and
`atomicity`. -/
theorem proj_coherence (hfin : Events.Finite E) (hc1 : G.Coherence1) (hcr : G.CoherenceRmw)
    (hat : G.Atomicity) : (G.proj hF).Coherence := by
  intro a b hab hba
  rcases hba with e | heco
  · subst e; exact proj_hbIrrefl hF hfin hc1 hcr hat _ hab
  · exact hc1 _ _ (proj_hb_wc hF hfin hcr hat hab) (.inr (proj_eco hF hcr hat heco))

/-- **Conjunct 6 of the image** (C34.6): from the fragment and `no-thin-air`. -/
theorem proj_noThinAir (hnta : G.NoThinAir) : (G.proj hF).NoThinAir := by
  have edge : ∀ {x y : G.PE}, (G.proj hF).PoRf x y → TransGen G.sbrf (G.wc x.1) (G.wc y.1) := by
    intro x y h
    have h1 : G.sbrf (G.wc x.1) y.1 := by
      rcases h with h | h
      · exact .inl (proj_po_sb hF h)
      · exact .inr h
    rcases sb_wc hF y.1 with e | e
    · rw [← e]; exact .single h1
    · exact .tail (.single h1) (.inl e)
  intro a h
  have key : ∀ {b}, TransGen (G.proj hF).PoRf a b → TransGen G.sbrf (G.wc a.1) (G.wc b.1) := by
    intro b h
    induction h with
    | single h => exact edge h
    | tail _ h ih => exact TransGen.trans ih (edge h)
  exact hnta _ (key h)

/-- A `seq_cst` event of the image has both components annotated `SC`. -/
theorem proj_sc {a : G.PE} (h : (G.proj hF).SC a) : G.SC a.1 ∧ G.SC (G.wc a.1) := by
  obtain ⟨u, k, hacc⟩ := h
  rw [proj_acc hF, Option.some.injEq] at hacc
  rcases shape hF a.1 with ⟨l, v, hl, h, -⟩ | ⟨t, l, v, o, hl, h, hwc⟩ |
    ⟨t, l, v, o, hl, -, h, hwc⟩ | ⟨t, l, v, o, w, v', o', hl, -, hlw, h, hwc⟩ <;>
    rw [h] at hacc
  · cases hacc
  · injection hacc with _ ho _; rw [hwc]; cases o <;> simp_all [ordW, SC, Lab.ann?]
  · injection hacc with _ ho _; rw [hwc]; cases o <;> simp_all [ordR, SC, Lab.ann?]
  · injection hacc with _ ho _; rw [hwc]
    cases o <;> cases o' <;> simp_all [ordPair, SC, Lab.ann?]

/-- **Conjunct 7 of the image** (C34.7): on a finite graph, from `coherencermw`, `atomicity` and
the `SC` check of RC11 with the amended `psc`. The middle term `po ; hb ; po` of ERN becomes the
amended `(sb \ rmw) ; hb ; (sb \ rmw)`: an `sb` edge from a write component is not an `rmw`
edge. -/
theorem proj_scConsistent (hfin : Events.Finite E) (hcr : G.CoherenceRmw) (hat : G.Atomicity)
    (hsc : G.SCCheck G.scbAm) : (G.proj hF).SCConsistent := by
  have noRmw : ∀ (x : G.PE) (y : E), ¬ G.rmw (G.wc x.1) y := fun x y h => by
    rw [rmw, partner_wc hF x] at h; cases h
  have toWc : ∀ {x : G.PE}, (G.proj hF).SC x → ∀ {y : E},
      G.psc G.scbAm y x.1 → TransGen (G.psc G.scbAm) y (G.wc x.1) := by
    intro x hx y h
    rcases sb_wc hF x.1 with e | e
    · rw [← e]; exact .single h
    · exact .tail (.single h) ⟨(proj_sc hF hx).1, .inl e, (proj_sc hF hx).2⟩
  have edge : ∀ {x y : G.PE}, (G.proj hF).PSC x y →
      TransGen (G.psc G.scbAm) (G.wc x.1) (G.wc y.1) := by
    rintro x y ⟨hx, hs, hy⟩
    have hxs := (proj_sc hF hx).2
    have hys := (proj_sc hF hy).1
    rcases hs with h | ⟨c, d, h₁, h₂, h₃⟩ | ⟨h, hl⟩ | h | h
    · exact toWc hy ⟨hxs, .inl (proj_po_sb hF h), hys⟩
    · have hcd : G.hb c.1 (G.wc d.1) := by
        have := proj_hb_wc hF hfin hcr hat h₂
        rcases sb_wc hF c.1 with e | e
        · rw [e]; exact this
        · exact TransGen.trans (.single (.inl e)) this
      exact toWc hy ⟨hxs, .inr (.inl ⟨c.1, G.wc d.1, ⟨proj_po_sb hF h₁, noRmw x _⟩, hcd,
        ⟨proj_po_sb hF h₃, noRmw d _⟩⟩), hys⟩
    · refine toWc hy ⟨hxs, .inr (.inr (.inl ⟨proj_hb hF hfin hcr hat h, ?_⟩)), hys⟩
      obtain ⟨u, hu₁, hu₂⟩ := hl
      rw [proj_unitOf hF] at hu₁ hu₂
      show (G.lab (G.wc x.1)).loc = (G.lab y.1).loc
      rw [loc_wc hF, Option.some.inj hu₁, Option.some.inj hu₂]
    · exact .single ⟨hxs, .inr (.inr (.inr (.inl h))), (proj_sc hF hy).2⟩
    · obtain ⟨hrb, hmo⟩ := proj_rb_mo hF hcr hat h
      cases hp : G.partner x.1 with
      | none =>
        rw [G.wc_none hp] at hxs ⊢
        exact .single ⟨hxs, .inr (.inr (.inr (.inr hrb))), (proj_sc hF hy).2⟩
      | some w =>
        rw [G.wc_some hp] at hxs ⊢
        exact .single ⟨hxs, .inr (.inr (.inr (.inl (hmo w hp)))), (proj_sc hF hy).2⟩
  intro a h
  have key : ∀ {b}, TransGen (G.proj hF).PSC a b →
      TransGen (G.psc G.scbAm) (G.wc a.1) (G.wc b.1) := by
    intro b h
    induction h with
    | single h => exact edge h
    | tail _ h ih => exact TransGen.trans ih (edge h)
  exact hsc _ (key h)

/-! ## Statement (b) -/

/-- **Statement (b) of 10e** (C34, `OB-C23`, `OB-C26`): on the declared fragment, for every finite
graph consistent for RC11 with the amended `psc` of the corrigendum, the canonical projection
satisfies `EventConsistent`. Proved, not posed. Finiteness serves the atomic `sw` edges only
(statement 3 of `EventLemmas`, retained reading 5 coinciding with the chains of `rc11.cat` on a
finite graph). The checks used, conjunct by conjunct: 1 and 2, none (the fragment); 3,
`coherencermw` and `atomicity`; 4 and 5, also `coherence1`; 6, `no-thin-air`; 7, `coherencermw`,
`atomicity` and the `SC` check. The representation of an RMW by one event is outside the
fragment. -/
theorem proj_consistent (hfin : Events.Finite E) (hc : G.ConsistentAm) :
    (G.proj hF).EventConsistent := by
  obtain ⟨hc1, hcr, hat, hsc, hnta⟩ := hc
  exact ⟨proj_rfWF hF, proj_moTotal hF, proj_rmwAtomic hF hcr hat,
    proj_coherence hF hfin hc1 hcr hat, proj_hbIrrefl hF hfin hc1 hcr hat,
    proj_noThinAir hF hnta, proj_scConsistent hF hfin hcr hat hsc⟩

end Graph

end Ern.ConcurrencyModel.Rc11
