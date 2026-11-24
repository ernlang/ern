import Ern.ConcurrencyModel.LossMarker
import Ern.ConcurrencyModel.FrameAncestry
import Ern.ConcurrencyModel.EventGraph

/-!
# Correspondence of fragment F; ordered handoff, `spawn`, completion and `join` (C26–C28, C32,
C46, C47)

Theorem 12 (12f) and theorem 13 (13a, 13b) of `formal/DESIGN.md`, Milestone 4, target theorems.

**Fragment F** (formalization hypothesis): one event per represented step; `start(c)` and
`complete(c)` are separate events; the loss and gain markers and the accesses of a step are
projected on its single event only for properties between steps. This does not represent or prove
the internal order constraints of C28 within a step (`OB-C19`, `OB-C20`), and there are no validity
events.

* `Corresponds`: a partial correspondence between an execution with named states (`EncapRun`)
  and an event graph of the event model (`Events.Graph`, contexts identified by numbers), K1–K4.
  The `sw` edges from `spawn(c)` to `start(c)` and from `complete(c)` to `join(c)` are not
  conditions: they follow from `Events.Graph.SW` by the roles of the events.
* 12f (C46, C33; `OB-C25`): an ordered handoff excludes the race (`handoff_compose`,
  `handoff_no_race`).
* 13a (C47, first paragraph; C32.2; `OB-C11`): `spawn_hb`.
* 13b (C47, second paragraph; C32.3; `OB-C11`): `join_hb`.
* The lifecycle of contexts along a step (`lstep_life`): contexts are never removed, a new context
  is live, and only `terminate(d)` ends the life of `d` (C4, C5, C7).
-/

namespace Ern.ConcurrencyModel

open Ern.MemoryModel Ern.MemoryModel.Access

variable {pm : ProviderMeta}

/-! ## The lifecycle of contexts along a step (C4, C5, C7) -/

/-- The lifecycle state of context `d` in `s`, if it exists (C1, C2). -/
def lifeOf (s : SC) (d : Nat) : Option Life := (s.C[d]?).map Ctx.life

/-- A context that has ended is not live (C2). -/
theorem not_live_of_done {s : SC} {d : Nat} (h : lifeOf s d = some .done) : ¬ s.Live d := by
  unfold lifeOf at h; unfold SC.Live
  cases hd : s.C[d]? with
  | none => rw [hd] at h; cases h
  | some x => rw [hd] at h; simp only [Option.map_some, Option.some.injEq] at h; simp [OptP, h]

/-- A context index beyond the context list is not live (C2). -/
theorem not_live_of_ge {s : SC} {d : Nat} (h : s.C.length ≤ d) : ¬ s.Live d := by
  unfold SC.Live; rw [List.getElem?_eq_none h]; exact id

/-- The context list of `s.set t` is that of `s` (C2). -/
theorem set_C (s : SC) (t : S3) : (s.set t).C = s.C := rfl

/-- An inherited operation keeps the length of the context list and the lifecycle state of every
context: only frame stacks and frame parents change (C2, C6). -/
theorem opStepC_life {k : K} {op : KernelOp} {c : Nat} {s s' : SC}
    (h : opStepC k op c s (.ok s')) : s'.C.length = s.C.length ∧ ∀ d, lifeOf s' d = lifeOf s d := by
  have viaSet : ∀ t : S3, s' = s.set t → s'.C.length = s.C.length ∧ ∀ d, lifeOf s' d = lifeOf s d :=
    fun t e => by subst e; exact ⟨rfl, fun _ => rfl⟩
  cases op with
  | transfer => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; exact viaSet _ rfl
  | depend => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; exact viaSet _ rfl
  | store => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; exact viaSet _ rfl
  | enter =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
    refine ⟨List.length_modify .., fun d => ?_⟩
    simp only [lifeOf, enterEffC, ReparentAux.getElem?_modify', Option.map_map]
    cases s.C[d]? with
    | none => rfl
    | some x => simp only [Option.map_some]; split <;> rfl
  | exit =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
    refine ⟨by simp [exitEffC, reparent], fun d => ?_⟩
    simp only [lifeOf, exitEffC_C_get, Option.map_map]
    cases s.C[d]? with
    | none => rfl
    | some x =>
      simp only [Option.map_some, Function.comp]
      split <;> split <;> rfl
  | _ =>
    obtain ⟨o, -, ho⟩ := h
    cases o with
    | ok t => exact viaSet t (by cases ho; rfl)
    | reject => cases ho
    | fail => cases ho

/-- The context list after a `spawn` (C4) or a by-value `spawn` (C5): one new live context. -/
theorem spawn_C (s : SC) (c : Nat) (ps : List Nat) (ls : LocalShape) :
    (spawnEff s c ps ls).C = s.C ++ [⟨[s.nF], .live, (s.stk c).head?⟩] := rfl

/-- Appending a context keeps the lifecycle states of the others and makes the new one live
(C4). -/
theorem life_append {s s' : SC} {x : Ctx} (hC : s'.C = s.C ++ [x]) (hx : x.life = .live)
    (d : Nat) :
    s.C.length ≤ s'.C.length ∧
    (d < s.C.length → lifeOf s' d = lifeOf s d) ∧
    (s.C.length ≤ d → lifeOf s' d = none ∨ lifeOf s' d = some .live) := by
  refine ⟨by rw [hC]; simp, fun hd => ?_, fun hd => ?_⟩
  · simp only [lifeOf, hC, List.getElem?_append_left hd]
  · rcases Nat.lt_or_ge s.C.length d with h | h
    · left; simp only [lifeOf, hC]
      rw [List.getElem?_eq_none (by simp; omega)]; rfl
    · right
      have : d = s.C.length := by omega
      subst this
      simp [lifeOf, hC, hx]

/-- The lifecycle of contexts along a labelled step (C4, C5, C7): the context list does not
shrink; an existing context keeps its lifecycle state, except that `terminate(d)` makes `d`
`done`; a context created by the step is live. -/
theorem lstep_life {ks : KShared} {L : MutexLayout} {lbl : Label}
    {st st' : SC × SyncReg × ArenaReg} (h : LStep ks L lbl st st') (d : Nat) :
    st.1.C.length ≤ st'.1.C.length ∧
    (d < st.1.C.length → lifeOf st'.1 d = lifeOf st.1 d ∨
      (lbl = .terminate d ∧ lifeOf st'.1 d = some .done)) ∧
    (st.1.C.length ≤ d → lifeOf st'.1 d = none ∨ lifeOf st'.1 d = some .live) := by
  have same : ∀ s s' : SC, s'.C.length = s.C.length → (∀ d, lifeOf s' d = lifeOf s d) →
      s.C.length ≤ s'.C.length ∧
      (d < s.C.length → lifeOf s' d = lifeOf s d ∨ (lbl = .terminate d ∧ lifeOf s' d = some .done)) ∧
      (s.C.length ≤ d → lifeOf s' d = none ∨ lifeOf s' d = some .live) :=
    fun s s' hl hd => ⟨Nat.le_of_eq hl.symm, fun _ => .inl (hd d), fun h => .inl (by
      rw [hd d]; unfold lifeOf; rw [List.getElem?_eq_none h]; rfl)⟩
  have unchanged : ∀ s s' : SC, s'.C = s.C →
      s.C.length ≤ s'.C.length ∧
      (d < s.C.length → lifeOf s' d = lifeOf s d ∨ (lbl = .terminate d ∧ lifeOf s' d = some .done)) ∧
      (s.C.length ≤ d → lifeOf s' d = none ∨ lifeOf s' d = some .live) :=
    fun s s' hC => same s s' (by rw [hC]) (fun d => by unfold lifeOf; rw [hC])
  cases h with
  | kernel hop =>
    obtain ⟨hl, hd⟩ := opStepC_life hop
    exact same _ _ hl hd
  | spawn hs =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
    obtain ⟨h1, h2, h3⟩ := life_append (spawn_C _ _ _ _) rfl d
    exact ⟨h1, fun hd => .inl (h2 hd), h3⟩
  | @terminate s s' reg ar c ht =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 ht
    refine ⟨by simp [termEffC, reparent], fun hd => ?_, fun hd => ?_⟩
    · by_cases hcd : c = d
      · subst hcd
        right
        refine ⟨rfl, ?_⟩
        simp only [lifeOf, termEffC_C_get]
        rw [List.getElem?_eq_getElem hd]
        simp only [Option.map_some, ite_true]
        split <;> rfl
      · left
        simp only [lifeOf, termEffC_C_get, hcd, ite_false]
        cases s.C[d]? with
        | none => rfl
        | some x => simp only [Option.map_some]; split <;> rfl
    · left
      simp only [lifeOf, termEffC_C_get]
      rw [List.getElem?_eq_none hd]; rfl
  | join hj => cases hj; exact unchanged _ _ rfl
  | deriveSync hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact unchanged _ _ rfl
  | newMutex hn => obtain ⟨-, rfl⟩ := hn; exact unchanged _ _ rfl
  | acquire ha => obtain ⟨_, _, _, _, rfl⟩ := ha; exact unchanged _ _ rfl
  | unlock hu => obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := hu; exact unchanged _ _ rfl
  | resetLock hr => obtain ⟨_, _, _, _, _, _, rfl⟩ := hr; exact unchanged _ _ rfl
  | @spawnVal s s' reg ar c ps ls vs hs =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
    obtain ⟨h1, h2, h3⟩ := life_append (s := s) (s' := spawnValEff s c ps ls vs)
      (by simp only [spawnValEff, yieldEff]; rw [transfersEff_C]; exact spawn_C _ _ _ _) rfl d
    exact ⟨h1, fun hd => .inl (h2 hd), h3⟩
  | newArena hn => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hn; exact unchanged _ _ rfl
  | issue hi =>
    cases hi with
    | ok _ _ _ h₁ h₂ =>
      obtain ⟨l1, d1⟩ := opStepC_life h₁
      obtain ⟨l2, d2⟩ := opStepC_life h₂
      exact same _ _ (l2.trans l1) (fun d => (d2 d).trans (d1 d))
  | reset hr =>
    obtain ⟨o, -, ho⟩ := hr
    cases o with
    | ok t => cases ho; exact unchanged _ _ rfl
    | reject => cases ho
    | fail => cases ho
  | readShared => exact unchanged _ _ rfl
  | writeShared hw => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hw; exact unchanged _ _ rfl
  | cas hc =>
    rcases cas_ok_cases hc with hk | rfl
    · obtain ⟨hl, hd⟩ := opStepC_life hk
      exact same _ _ hl hd
    · exact unchanged _ _ rfl

/-! ## The correspondence of fragment F (C26–C28, C32) -/

/-- The events a correspondence gives (fragment F): the event of each represented step, and the
`start(c)` and `complete(c)` markers of contexts (C28). -/
structure StepEvents (E : Type) where
  ev : Nat → Option E
  start : Nat → Option E
  complete : Nat → Option E

/-- Step `s` creates context `c` (C4, C5): it is a `spawn` or a by-value `spawn`, and `c` is the
identity of the new context, the length of the context list before the step. -/
def Creates (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) (s c : Nat) : Prop :=
  ∃ h : s < lbls.length,
    ((∃ c' ps ls, lbls[s] = .spawn c' ps ls) ∨ (∃ c' ps ls vs, lbls[s] = .spawnVal c' ps ls vs)) ∧
    c = (σ s).1.C.length

/-- The correspondence of fragment F between an execution `(σ, lbls)` and an event graph `G`
whose contexts are context identities (C26 item 3), partial: `K` gives the events of the
represented steps and markers.

* K1 (C26, C27): the event of step `i` has the context of label `i`; two distinct steps have
  distinct events.
* K2 (C28): for `i < j` of the same context, `po` relates the event of `i` to that of `j`.
* K3 (C28, C32.2, C47): the event of a step that creates `c` has the role `spawn(c)`; the marker
  `start(c)` is an event of context `c`, of role `start(c)`, `po`-before the event of every step
  of `c`. Conversely, an event of role `spawn(c)` is the event of a step that creates `c`, and an
  event of role `start(c)` is the marker `start(c)` of a context that a step creates.
* K4 (C28, C32.3, C47): the marker `complete(c)` is an event of context `c`, of role
  `complete(c)`, `po`-after the event of every step of `c`; the event of a step `join(d)` has the
  role `join(d)`. Conversely, an event of role `complete(c)` is the marker `complete(c)` of a
  context that executes `terminate`, and an event of role `join(d)` is the event of a step
  `join(d)`.

K3 and K4 hold in both directions: a lifecycle role is carried only by the event of the step, or
by the marker, that C28 names. Exported obligation `OB-C20` (C27–C29, C50), stated part: the
correspondence of the events of steps and of the lifecycle markers. The obligation is exported and
remains open (`ExportedObligations`). -/
structure Corresponds {E U V S : Type} (G : Events.Graph E Nat U V S)
    (σ : Nat → SC × SyncReg × ArenaReg) (lbls : List Label) (K : StepEvents E) : Prop where
  /-- K1 (C26, C27). -/
  ctx : ∀ i (h : i < lbls.length) e, K.ev i = some e → G.ctx e = lbls[i].requester
  /-- K1 (C26, C27). -/
  inj : ∀ i j e, K.ev i = some e → K.ev j = some e → i = j
  /-- K2 (C28). -/
  po : ∀ i j (hi : i < lbls.length) (hj : j < lbls.length) a b, i < j →
    lbls[i].requester = lbls[j].requester → K.ev i = some a → K.ev j = some b → G.po a b
  /-- K3 (C28, C32.2, C47). -/
  spawnRole : ∀ s c, Creates σ lbls s c → ∀ e, K.ev s = some e → G.sync? e = some (.spawn c)
  /-- K3 (C28, C32.2, C47). -/
  start : ∀ c x, K.start c = some x → G.ctx x = c ∧ G.sync? x = some (.start c) ∧
    ∀ j (h : j < lbls.length) d, lbls[j].requester = c → K.ev j = some d → G.po x d
  /-- K4 (C28, C32.3, C47). -/
  complete : ∀ c x, K.complete c = some x → G.ctx x = c ∧ G.sync? x = some (.complete c) ∧
    ∀ j (h : j < lbls.length) d, lbls[j].requester = c → K.ev j = some d → G.po d x
  /-- K4 (C28, C32.3, C47). -/
  joinRole : ∀ q (h : q < lbls.length) c d e, lbls[q] = .join c d → K.ev q = some e →
    G.sync? e = some (.join d)
  /-- K3, provenance (C28, C32 item 2): an event of role `spawn(c)` is the event of a step that
  creates `c`. -/
  spawnFrom : ∀ e c, G.sync? e = some (.spawn c) → ∃ s, Creates σ lbls s c ∧ K.ev s = some e
  /-- K3, provenance (C28): an event of role `start(c)` is the marker `start(c)`, and a step creates
  `c`. -/
  startFrom : ∀ e c, G.sync? e = some (.start c) → K.start c = some e ∧ ∃ s, Creates σ lbls s c
  /-- K4, provenance (C28): an event of role `complete(c)` is the marker `complete(c)`, and `c`
  executes `terminate`. -/
  completeFrom : ∀ e c, G.sync? e = some (.complete c) →
    K.complete c = some e ∧ ∃ t, ∃ h : t < lbls.length, lbls[t] = .terminate c
  /-- K4, provenance (C28, C32 item 3): an event of role `join(d)` is the event of a step
  `join(d)`. -/
  joinFrom : ∀ e d, G.sync? e = some (.join d) →
    ∃ q, ∃ h : q < lbls.length, ∃ c, lbls[q] = .join c d ∧ K.ev q = some e

namespace Corresponds

variable {E U V S : Type} {G : Events.Graph E Nat U V S} {σ : Nat → SC × SyncReg × ArenaReg}
  {lbls : List Label} {K : StepEvents E}

/-- K2 with equality: for `i ≤ j` of the same context, the events are equal or related by `po`
(C28). -/
theorem po_or_eq (hK : Corresponds G σ lbls K) {i j : Nat} (hi : i < lbls.length)
    (hj : j < lbls.length) (hij : i ≤ j) (hs : lbls[i].requester = lbls[j].requester) {a b : E}
    (ha : K.ev i = some a) (hb : K.ev j = some b) : a = b ∨ G.po a b := by
  rcases Nat.lt_or_eq_of_le hij with h | h
  · exact .inr (hK.po i j hi hj a b h hs ha hb)
  · subst h; rw [ha] at hb; exact .inl (Option.some.inj hb)

end Corresponds

/-! ## 12f: ordered handoff excludes the race (C46, C33) -/

/-- `po` is in `hb` (C33). -/
theorem hb_of_po {E C U V S : Type} {G : Events.Graph E C U V S} {a b : E} (h : G.po a b) :
    G.HB a b :=
  .single (.inl h)

/-- **Theorem 12f**, composition (C46: "When the event-model mapping has also established
`po(e1,r)`, the protocol requirement `hb(r,e2)` implies `hb(e1,e2)` by transitivity"; C33;
`OB-C25`): for steps `i ≤ r < j` with `r` a step of the context of `i`, their events `a`, `b`,
and any event `d` (in particular the event of step `j`): `a = b` or `po(a, b)`; and if `hb(b, d)`
(`HandoffOrdered`), then `hb(a, d)`, and `(a, d)` is not a race. A composition statement: it assumes `HandoffOrdered` and does not establish it. When
`r = i` the hypothesis is `hb(a, d)` itself: no exemption (C46). -/
theorem handoff_compose {E U V S : Type} {G : Events.Graph E Nat U V S}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} {K : StepEvents E}
    (hK : Corresponds G σ lbls K) {i r j : Nat} (hir : i ≤ r) (hrj : r < j)
    (hj : j < lbls.length) (hsame : lbls[r].requester = lbls[i].requester) {a b d : E}
    (ha : K.ev i = some a) (hb : K.ev r = some b) :
    (a = b ∨ G.po a b) ∧ (G.HB b d → G.HB a d ∧ ¬ G.Race a d) := by
  have hab := hK.po_or_eq (by omega) (by omega) hir hsame.symm ha hb
  refine ⟨hab, fun hbd => ?_⟩
  have had : G.HB a d := by
    rcases hab with rfl | hpo
    · exact hbd
    · exact Relation.TransGen.trans (.single (.inl hpo)) hbd
  exact ⟨had, fun hr => hr.2.2.2.1 had⟩

/-- **Theorem 12f** in the situation of 12d (C45, C46, C33; `OB-C25`): with the hypotheses of
`loss_marker_modify` and the earlier step `i` a step of `c'` (the access `e1` of C45 is issued by
`c'`), the loss marker `r` of 12d is such that, for the events `a`, `b`, `d` of steps `i`, `r`,
`j`: `a = b` or `po(a, b)`; and `HandoffOrdered`, `hb(b, d)`, gives `hb(a, d)` and excludes the
race on `(a, d)`. -/
theorem handoff_no_race {ks : KShared} {L : MutexLayout} {statics : Statics}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} {E U V S : Type}
    {G : Events.Graph E Nat U V S} {K : StepEvents E} (hdd : DDSound ks.toK)
    (hst : StaticsOK statics) (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], []))
    (hr : EncapRun pm ks L σ lbls) (hK : Corresponds G σ lbls K) {i j c c' l : Nat} {m : Mode}
    (hij : i < j) (hj : j < lbls.length) (hcc : c ≠ c')
    (hm : Allows (cap (σ j).1 (σ j).2.1 c l) m)
    (hi : IncompatModify (cap (σ i).1 (σ i).2.1 c' l) m)
    (hci : ∀ h : i < lbls.length, lbls[i].requester = c') :
    ∃ r, FirstCompatible IncompatModify σ i c' l m r ∧ i ≤ r ∧ r < j ∧
      ∀ a b d, K.ev i = some a → K.ev r = some b → K.ev j = some d →
        (a = b ∨ G.po a b) ∧ (G.HB b d → G.HB a d ∧ ¬ G.Race a d) := by
  obtain ⟨r, hfc, -, hrj, hrl, hreq⟩ :=
    loss_marker_modify hdd hst h0 hr hij (Nat.le_of_lt hj) hcc hm hi
  refine ⟨r, hfc, hfc.1, hrj, fun a b d ha hb _ => ?_⟩
  exact handoff_compose hK hfc.1 hrj hj (by rw [hreq, hci (by omega)]) ha hb

/-! ## 13a: `spawn` (C47, first paragraph; C32.2) -/

/-- The context list does not shrink along an execution (C4, C5). -/
theorem encapRun_C_mono {ks : KShared} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg}
    {lbls : List Label} (hr : EncapRun pm ks L σ lbls) {i j : Nat} (hij : i ≤ j)
    (hj : j ≤ lbls.length) : (σ i).1.C.length ≤ (σ j).1.C.length := by
  induction j with
  | zero => have : i = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ j ih =>
    rcases Nat.lt_or_eq_of_le hij with h | h
    · exact Nat.le_trans (ih (by omega) (by omega)) (lstep_life (hr j (by omega)).2 0).1
    · subst h; exact Nat.le_refl _

/-- **Theorem 13a** (C47: "the creator's authority-yield loss marker precedes its `spawn`
synchronization event within the parent context; the latter `sw`-precedes the child's `start(c)`
marker"; C32.2: "the parent's `spawn(c)` event `sw`-precedes the child's `start(c)` event, with all
prior parent events and subsequent child events related through `po`"; `OB-C11`): let `s` be the
step that creates `c`, with event `es` and the marker `start(c)` = `x`.

1. Trace fact: every step of `c` follows `s` (before `s`, `c` is not a context).
2. The event of every step `p ≤ s` of the creator is `hb`-before the event of every step of `c`:
   `po` (K2), `sw` from `spawn(c)` to `start(c)` (`Events.Graph.SW`, by the roles of K3), `po`
   (K3). -/
theorem spawn_hb {ks : KShared} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg}
    {lbls : List Label} {E U V S : Type} {G : Events.Graph E Nat U V S} {K : StepEvents E}
    (hr : EncapRun pm ks L σ lbls) (hK : Corresponds G σ lbls K) {s c : Nat}
    (hcr : Creates σ lbls s c) {x es : E} (hx : K.start c = some x) (hes : K.ev s = some es) :
    (∀ j (hj : j < lbls.length), lbls[j].requester = c → s < j) ∧
    ∀ p (hp : p < lbls.length) j (hj : j < lbls.length) a d, p ≤ s →
      lbls[p].requester = (lbls[s]'hcr.1).requester → lbls[j].requester = c →
      K.ev p = some a → K.ev j = some d → G.HB a d := by
  obtain ⟨hs, hkind, hc⟩ := hcr
  have after : ∀ j (hj : j < lbls.length), lbls[j].requester = c → s < j := by
    intro j hj hjc
    refine Decidable.byContradiction fun hn => ?_
    have hle : (σ j).1.C.length ≤ c := by
      rw [hc]; exact encapRun_C_mono hr (by omega) (by omega)
    have hl := lstep_live (hr j hj).2
    rw [hjc] at hl
    exact not_live_of_ge hle hl
  refine ⟨after, fun p hp j hj a d hps hpreq hjc ha hd => ?_⟩
  have hsw : G.SW es x := by
    exact .inr (.inl ⟨c, hK.spawnRole s c ⟨hs, hkind, hc⟩ es hes, (hK.start c x hx).2.1⟩)
  have hxd : G.po x d := (hK.start c x hx).2.2 j hj d hjc hd
  have hesd : G.HB es d := Relation.TransGen.trans (.single (.inr hsw)) (.single (.inl hxd))
  rcases hK.po_or_eq hp hs hps hpreq ha hes with rfl | hpo
  · exact hesd
  · exact Relation.TransGen.trans (.single (.inl hpo)) hesd

/-! ## 13b: completion and `join` (C47, second paragraph; C32.3) -/

/-- No context is `done` in the initial state (C3). -/
theorem lifeOf_init (t : S3) (d : Nat) : lifeOf (SC.ofS3 t) d ≠ some .done := by
  unfold lifeOf SC.ofS3
  cases d with
  | zero => simp
  | succ d => simp

/-- A `done` context stays `done` (C7: only `terminate(d)` changes the lifecycle state of an
existing context `d`, to `done`). -/
theorem encapRun_done_stays {ks : KShared} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg}
    {lbls : List Label} (hr : EncapRun pm ks L σ lbls) {d i : Nat}
    (hi : lifeOf (σ i).1 d = some .done) : ∀ k, i ≤ k → k ≤ lbls.length →
      lifeOf (σ k).1 d = some .done := by
  intro k hik hk
  induction k with
  | zero => have : i = 0 := by omega
            subst this; exact hi
  | succ k ih =>
    rcases Nat.lt_or_eq_of_le hik with h | h
    · have hk' := ih (by omega) (by omega)
      have hdl : d < (σ k).1.C.length := by
        unfold lifeOf at hk'
        exact Decidable.byContradiction fun hn => by
          rw [List.getElem?_eq_none (by omega)] at hk'; cases hk'
      rcases (lstep_life (hr k (by omega)).2 d).2.1 hdl with e | ⟨-, e⟩
      · rw [e]; exact hk'
      · exact e
    · subst h; exact hi

/-- An `ok` labelled `join` is an `ok` `JoinStep` with the state unchanged (C8). -/
theorem lstep_join {ks : KShared} {L : MutexLayout} {st st' : SC × SyncReg × ArenaReg} {c d : Nat}
    (h : LStep ks L (.join c d) st st') : JoinStep st.1 c d (.ok st'.1) := by
  cases h with
  | join hj => exact hj

/-- **Theorem 13b** (C47: "every earlier event of the terminating context is `po`-before
`complete(c)`; a successful `join(c)` in another context is the target of `sw` from that
`complete(c)` event. The `join` event is placed in the caller's `po` before subsequent
operations"; C32.3; `OB-C11`): let `q` be a step `join(d)` of a context `c`, with event `eq`, and
the marker `complete(d)` = `x`.

1. Trace facts: some step `t < q` is `terminate(d)`, and no step of `d` follows it.
2. The event of every step of `d` is `hb`-before `eq` and the event of every step of `c` after
   `q`: `po` (K4), `sw` from `complete(d)` to `join(d)` (`Events.Graph.SW`, by the roles of K4),
   `po` (K2). -/
theorem join_hb {ks : KShared} {L : MutexLayout} {statics : Statics}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} {E U V S : Type}
    {G : Events.Graph E Nat U V S} {K : StepEvents E}
    (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], [])) (hr : EncapRun pm ks L σ lbls)
    (hK : Corresponds G σ lbls K) {q c d : Nat} (hq : q < lbls.length)
    (hlq : lbls[q] = .join c d) {x eq : E} (hx : K.complete d = some x)
    (heq : K.ev q = some eq) :
    (∃ t, ∃ ht : t < q, lbls[t]'(by omega) = .terminate d ∧
      ∀ j (hj : j < lbls.length), t < j → lbls[j].requester ≠ d) ∧
    ∀ p (hp : p < lbls.length) a, lbls[p].requester = d → K.ev p = some a →
      G.HB a eq ∧ ∀ j (hj : j < lbls.length) b, q < j → lbls[j].requester = c →
        K.ev j = some b → G.HB a b := by
  have hdone : lifeOf (σ q).1 d = some .done := by
    have hs := (hr q hq).2
    rw [hlq] at hs
    have hj := lstep_join hs
    generalize (σ (q + 1)).1 = s' at hj
    cases hj with
    | ok _ hd =>
      unfold lifeOf
      revert hd
      cases (σ q).1.C[d]? with
      | none => exact False.elim
      | some x => intro hd; simp only [Option.map_some, OptP] at hd ⊢; rw [hd]
  refine ⟨?_, fun p hp a hpd ha => ?_⟩
  · have h0d : ¬ lifeOf (σ 0).1 d = some .done := by rw [h0]; exact lifeOf_init _ d
    obtain ⟨t, -, htq, ht1, ht2⟩ := exists_first (P := fun k => lifeOf (σ k).1 d = some .done)
      (Nat.pos_of_ne_zero fun e => by subst e; exact h0d hdone) h0d hdone
    have htl : t < lbls.length := by omega
    have hterm : lbls[t] = .terminate d := by
      have hlt := lstep_life (hr t htl).2 d
      have hnt : ¬ lifeOf (σ t).1 d = some .done := ht2 t (Nat.zero_le _) (Nat.le_refl _)
      by_cases hdl : d < (σ t).1.C.length
      · rcases hlt.2.1 hdl with e | ⟨e, -⟩
        · rw [e] at ht1; exact absurd ht1 hnt
        · exact e
      · rcases hlt.2.2 (by omega) with e | e <;> rw [e] at ht1 <;> cases ht1
    refine ⟨t, htq, hterm, fun j hj htj hjd => ?_⟩
    have hjdone := encapRun_done_stays hr ht1 j (by omega) (by omega)
    have hl := lstep_live (hr j hj).2
    rw [hjd] at hl
    exact not_live_of_done hjdone hl
  · have hsw : G.SW x eq := by
      refine .inr (.inr ⟨d, (hK.complete d x hx).2.1, hK.joinRole q hq c d eq hlq heq⟩)
    have hax : G.po a x := (hK.complete d x hx).2.2 p hp a hpd ha
    have haeq : G.HB a eq := Relation.TransGen.trans (.single (.inl hax)) (.single (.inr hsw))
    refine ⟨haeq, fun j hj b hqj hjc hb => ?_⟩
    have hreq : lbls[q].requester = c := by rw [hlq]; rfl
    exact Relation.TransGen.tail haeq (.inl (hK.po q j hq hj eq b hqj (by rw [hreq, hjc]) heq hb))

end Ern.ConcurrencyModel
