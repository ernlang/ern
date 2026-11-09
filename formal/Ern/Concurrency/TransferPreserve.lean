import Ern.Concurrency.Preservation
import Ern.Concurrency.Transfer

/-!
# Theorem 2 for the by-value composite (WC4 C5)

`spawnVal_preservesC`: the composite of WC4 C5, with the preconditions `SpawnValPre`, preserves the
re-indexed kernel invariant with the auxiliaries of Spec 1 (`KInvCA`).

The yield of the parameters commutes with the transfers (`yield_transfers`): the parameters are
held by frames, which O4 does not move (Spec 1 §63 effect). The composite is therefore `spawn`
(WC4 C4) followed by the transfers. The anchor orders come from the final checks of WC4 C5.4; the
other invariants are carried phase by phase from the Spec 1 lemmas used by `transfer_preserves`.
-/

namespace Ern.Concurrency

open Ern.MemoryModel.Access

namespace TransferPreserveAux

open PreservationAux

/-! ## Yield and transfer commute -/

/-- `mapI` followed by `map` is `map` followed by `mapI` when the two functions commute on each
element. -/
theorem mapI_map_comm {F : Nat → Authority → Authority} {G : Authority → Authority} :
    ∀ (i : Nat) (l : List Authority),
      (∀ (k : Nat) (y : Authority), l[k]? = some y → G (F (i + k) y) = F (i + k) (G y)) →
      (mapI F i l).map G = mapI F i (l.map G)
  | _, [], _ => rfl
  | i, y :: l, h => by
    have h0 : G (F i y) = F i (G y) := by simpa using h 0 y rfl
    have ih := mapI_map_comm (i + 1) l fun k z hz => by
      have := h (k + 1) z (by simpa using hz)
      rwa [show i + (k + 1) = i + 1 + k by omega] at this
    simp only [mapI, List.map_cons, h0, ih]

/-- The yield function of `yieldEff` (WC4 C5.3). -/
def yieldF (ps : List Nat) (f : Nat) (j : Nat) (y : Authority) : Authority :=
  if j ∈ ps then { y with holder := .frame f } else y

/-- The holder map of the transfer effect (Spec 1 §63 effect). -/
def moveF (P : List Place) (src dst : Nat) (y : Authority) : Authority :=
  if heldIn P src y.holder then { y with holder := mvTo P src dst y.holder } else y

/-- A frame holder is never within a place (Spec 1 §63). -/
theorem not_heldIn_frame {P : List Place} {q g : Nat} : ¬ heldIn P q (.frame g) := fun h => h

/-- A parameter held by a frame is not moved by a transfer. -/
theorem yield_move_comm {P : List Place} {ps : List Nat} {f src dst : Nat} {t : SC}
    (hp : ∀ a ∈ ps, ∀ y, t.A[a]? = some y → ∃ g, y.holder = .frame g) (j : Nat) (y : Authority)
    (hy : t.A[j]? = some y) :
    moveF P src dst (yieldF ps f j y) = yieldF ps f j (moveF P src dst y) := by
  unfold yieldF moveF
  by_cases hk : j ∈ ps
  · obtain ⟨g, hg⟩ := hp _ hk y hy
    have h1 : ¬ heldIn P src y.holder := by rw [hg]; exact not_heldIn_frame
    simp only [hk, h1, not_heldIn_frame, ↓reduceIte]
  · simp only [hk, ↓reduceIte]

/-- Extensionality of `S_C` states. -/
theorem sc_ext {a b : SC} (hC : a.C = b.C) (hn : a.nF = b.nF) (hP : a.P = b.P) (hI : a.I = b.I)
    (hA : a.A = b.A) (hD : a.D = b.D) (hd : a.dead = b.dead) (hp : a.pins = b.pins) : a = b := by
  cases a; cases b
  simp only at hC hn hP hI hA hD hd hp
  subst hC hn hP hI hA hD hd hp; rfl

/-- WC4 C5.2–C5.3: when the parameters are held by frames, yielding them before or after one
transfer gives the same state. -/
theorem yield_transfer {t : SC} {ps : List Nat} {f c src dst : Nat}
    (hp : ∀ a ∈ ps, ∀ y, t.A[a]? = some y → ∃ g, y.holder = .frame g) :
    transferEffC (yieldEff t ps f) c src dst = yieldEff (transferEffC t c src dst) ps f := by
  have hA : (mapI (yieldF ps f) 0 t.A).map (moveF t.P src dst) =
      mapI (yieldF ps f) 0 (t.A.map (moveF t.P src dst)) :=
    mapI_map_comm 0 t.A fun k y hy => by rw [Nat.zero_add]; exact yield_move_comm hp k y hy
  exact sc_ext rfl rfl rfl rfl hA rfl rfl rfl

/-- A transfer keeps the authorities held by frames (Spec 1 §63 effect). -/
theorem transfer_frame_held {t : SC} {c src dst a : Nat} {y : Authority}
    (hy : (transferEffC t c src dst).A[a]? = some y) :
    ∃ y₀, t.A[a]? = some y₀ ∧ ((∃ g, y₀.holder = .frame g) → y.holder = y₀.holder) := by
  have h : (transferEff (t.view c) src dst).A[a]? = some y := hy
  rw [transfer_A_get] at h
  obtain ⟨y₀, hy₀, rfl⟩ := Option.map_eq_some_iff.1 h
  refine ⟨y₀, hy₀, fun ⟨g, hg⟩ => ?_⟩
  simp [hg, heldIn]

/-- WC4 C5.2–C5.3: yielding before the transfers gives the state of the composite. -/
theorem yield_transfers {ps : List Nat} {f c : Nat} :
    ∀ (t : SC) (vs : List (Nat × Nat)),
      (∀ a ∈ ps, ∀ y, t.A[a]? = some y → ∃ g, y.holder = .frame g) →
      transfersEff c (yieldEff t ps f) vs = yieldEff (transfersEff c t vs) ps f
  | _, [], _ => rfl
  | t, v :: vs, hp => by
    simp only [transfersEff]
    rw [yield_transfer hp]
    refine yield_transfers (transferEffC t c v.1 v.2) vs fun a ha y hy => ?_
    obtain ⟨y₀, hy₀, e⟩ := transfer_frame_held hy
    obtain ⟨g, hg⟩ := hp a ha y₀ hy₀
    exact ⟨g, by rw [e ⟨g, hg⟩, hg]⟩

/-- `mapI` with a function that is the identity on the indices of a list. -/
theorem mapI_id {F : Nat → Authority → Authority} :
    ∀ (i : Nat) (l : List Authority), (∀ k y, F (i + k) y = y) → mapI F i l = l
  | _, [], _ => rfl
  | i, y :: l, h => by
    have h0 : F i y = y := by simpa using h 0 y
    have ih := mapI_id (i + 1) l fun k z => by
      have := h (k + 1) z; rwa [show i + (k + 1) = i + 1 + k by omega] at this
    simp only [mapI, h0, ih]

/-- `mapI` over an append. -/
theorem mapI_append {F : Nat → Authority → Authority} :
    ∀ (i : Nat) (l m : List Authority), mapI F i (l ++ m) = mapI F i l ++ mapI F (i + l.length) m
  | i, [], m => by simp [mapI]
  | i, y :: l, m => by
    simp only [List.cons_append, mapI, mapI_append (i + 1) l m, List.length_cons]
    rw [show i + 1 + l.length = i + (l.length + 1) by omega]

/-- WC4 C5.1, C5.3: creating without parameters then yielding them is `spawn` with the
parameters (WC4 C4 effect), when the parameters are existing authorities. -/
theorem create_yield {s : SC} {c : Nat} {ps : List Nat} {ls : LocalShape}
    (hp : ∀ a ∈ ps, a < s.A.length) :
    yieldEff (spawnCreate s c ls) ps s.nF = spawnEff s c ps ls := by
  have h0 : mapI (fun j (y : Authority) => if j ∈ ([] : List Nat) then
      { y with holder := .frame (s.view c).nF } else y) 0 (s.view c).A = (s.view c).A :=
    mapI_id 0 _ fun _ _ => by simp
  refine sc_ext rfl rfl rfl rfl ?_ rfl rfl rfl
  show mapI (yieldF ps s.nF) 0 (enterEff (s.view c) [] ls).A = (enterEff (s.view c) ps ls).A
  simp only [enterEff]
  rw [mapI_append, h0]
  congr 1
  exact mapI_id (0 + (s.view c).A.length) _ fun k y => by
    have : 0 + (s.view c).A.length + k ∉ ps := fun h => by
      have h2 := hp _ h
      change 0 + s.A.length + k < s.A.length at h2
      omega
    simp only [yieldF, this, ↓reduceIte]

/-! ## The kernel invariant without the anchor orders -/

/-- The clauses of `KInvCA` other than the anchor orders (Spec 1 §57 re-indexed, WC4 C20). -/
def KBase (s : SC) : Prop :=
  FramesC s ∧ (WF3 s.flat ∧ I1 s.flat ∧ I2 s.flat ∧ I3 s.flat ∧ NoDangling s.flat ∧
    KAux s.flat ∧ HeldAnchored s.flat)

/-- The kernel facts of Spec 1 on the view of a context, from `KBase` (WC4 C2). -/
theorem view_facts_base {s : SC} (hk : KBase s) (c : Nat) :
    WF3 (s.view c) ∧ Inv3base (s.view c) ∧ NoDangling (s.view c) ∧ RootHeldConv (s.view c) ∧
      HeldAnchored (s.view c) := by
  obtain ⟨hfr, hw, h1, h2, h3, hnd, hc, hh⟩ := hk
  have hF : ∀ f, f ∈ (s.view c).F ↔ f ∈ s.flat.F := fun f => SC.mem_view_F
  exact ⟨SC.wf3_view hfr hw, ⟨h1, h2, i3_mem_congr h3 hF, i4_always _⟩,
    noDangling_mem_congr hnd hF, hc, heldAnchored_mem_congr hh hF⟩

/-- `spawn` (WC4 C4 effect) establishes `KBase` from `KInvCA`, without the resulting-state
condition §72.4 (WC4 C4.5), which the composite checks on its final state. -/
theorem spawn_base {s : SC} {c : Nat} {ps : List Nat} {ls : LocalShape} (hk : KInvCA s)
    (hc : s.stk c ≠ []) (hpar : ParamsOK (s.view c) ps) (hsh : ShapeOK s.P.length ls.toShape) :
    KBase (spawnEff s c ps ls) := by
  obtain ⟨hw, hb, hd, hrc, hh⟩ := view_facts hk c
  have hfr := hk.1.1.1
  have hpush := spawn_push (ps := ps) (ls := ls) hfr hc
  have hmem : ∀ f, f ∈ (enterEff (s.view c) ps ls).F ↔ f ∈ (spawnEff s c ps ls).frames :=
    fun f => by
      rw [hpush.mem]
      show f ∈ s.nF :: (s.view c).F ↔ _
      rw [List.mem_cons, SC.mem_view_F]
  have hne : (spawnEff s c ps ls).frames ≠ [] := fun he => by
    have := (hpush.mem s.nF).2 (.inl rfl); rw [he] at this; cases this
  exact ⟨hpush.framesC hfr, flat_facts rfl hmem hpush.nodup hne (enter_wf' hw hpar hsh)
    (Ern.MemoryModel.Access.Frames.enter_inv3base hw hb) (enter_noDangling' hw hd hsh)
    (enter_rootHeldConv' hw hpar hrc) (enter_heldAnchored' hw hh)⟩

/-- One transfer (Spec 1 §63 effect) keeps `KBase`, from §63.1 usability, §63.2, §63.3
disjointness, §63.6 first half and the usability of the destination after the step. -/
theorem transfer_base {t : SC} {c src dst : Nat} (hk : KBase t) (hsrc : (t.view c).Usable src)
    (hdst : (t.view c).Usable dst) (hdeps : ∀ x ∈ movedDeps (t.view c) src, (t.view c).Active x)
    (hsh : SameShape (t.view c).P src dst) (hdis : ¬ overlap (t.view c).P src dst)
    (hd' : (transferEff (t.view c) src dst).Usable dst) : KBase (transferEffC t c src dst) := by
  obtain ⟨hw, hb, hd, hc, hh⟩ := view_facts_base hk c
  have hw' := transfer_wf3' hw hsrc hdst hd'
  obtain ⟨hb', hd''⟩ := transfer_base' hw hb hd hsrc hdeps hd'
  have hh' := transfer_heldAnchored' hw hh hsrc hdst hsh hdis
  have hmem : ∀ f, f ∈ (transferEff (t.view c) src dst).F ↔ f ∈ t.frames := fun _ =>
    SC.mem_view_F
  exact ⟨framesC_set hk.1 rfl, flat_facts rfl hmem hk.1.nodup (frames_ne (s := t) hk.1) hw' hb' hd''
    (transfer_rootHeldConv' hc) hh'⟩

/-! ## Destinations -/

/-- Place `q` exists and is owned by a frame (Spec 1 §40). -/
def FrameOwned (P : List Place) (q : Nat) : Prop :=
  OptP (P[q]?) (fun pl => ∃ g, pl.owner = .frame g) False

/-- A transfer keeps the places owned by frames (Spec 1 §63 effect). -/
theorem transfer_frameOwned {v : S3} {src dst q : Nat} (h : FrameOwned v.P q) :
    FrameOwned (transferEff v src dst).P q := by
  unfold FrameOwned at h ⊢
  rw [transfer_P_get]
  cases hq : v.P[q]? with
  | none => rw [hq] at h; exact h.elim
  | some pl =>
    rw [hq] at h
    obtain ⟨g, hg⟩ := h
    exact ⟨g, by simp [hg, heldIn]⟩

/-- A usable place owned by a frame stays usable after a transfer (Spec 1 §40, §63 effect). -/
theorem transfer_usable_frameOwned {v : S3} {src dst q : Nat} (h : v.Usable q)
    (ho : FrameOwned v.P q) : (transferEff v src dst).Usable q := by
  cases h with
  | @frame q g pl hpl hd hog hf =>
    refine .frame (pl := pl) ?_ hd hog hf
    rw [transfer_P_get, hpl]; simp [hog, heldIn]
  | @place q o pl hpl hd hoo hu =>
    unfold FrameOwned at ho; rw [hpl] at ho
    obtain ⟨g, hg⟩ := ho; rw [hoo] at hg; cases hg

/-- The fresh root locals of `spawn` are owned by the new frame (Spec 1 §72 effect,
`LocalShape.toShape`). -/
theorem spawn_frameOwned {s : SC} {c : Nat} {ps : List Nat} {ls : LocalShape} {dst : Nat}
    (h : FreshRootLocal s ls dst) : FrameOwned (spawnEff s c ps ls).P dst := by
  obtain ⟨i, hi, rfl⟩ := h
  have hil : i < ls.toShape.length := List.mem_range.1 (List.mem_filter.1 hi).1
  unfold FrameOwned
  show OptP ((enterP (s.view c) ls)[s.P.length + i]?) _ False
  simp only [enterP, shapeP, SC.view, SC.flat]
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left, List.getElem?_map,
    List.getElem?_range hil]
  refine ⟨s.nF, ?_⟩
  simp only [shapeOwner, LocalShape.toShape, List.getElem?_map]
  cases ls[i]? <;> rfl

/-! ## The transfer phases -/

/-- The clauses of `ValTransferPre` read by `transfer_base` hold on the state where the
parameters are already yielded: they read neither holders nor exercise. -/
theorem yield_view {t : SC} {ps : List Nat} {f c : Nat} :
    (yieldEff t ps f).view c = { t.view c with A := mapI (yieldF ps f) 0 t.A } := rfl

/-- `Active` is unchanged by the yield (WC4 C5.3). -/
theorem yield_active {v : S3} {ps : List Nat} {f x : Nat} :
    ({ v with A := mapI (yieldF ps f) 0 v.A } : S3).Active x ↔ v.Active x := by
  constructor
  · rintro ⟨y, hy, ya⟩
    change (mapI (yieldF ps f) 0 v.A)[x]? = some y at hy
    rw [getElem?_mapI] at hy
    obtain ⟨y₀, hy₀, rfl⟩ := Option.map_eq_some_iff.1 hy
    refine ⟨y₀, hy₀, ?_⟩
    unfold yieldF at ya; split at ya <;> exact ya
  · rintro ⟨y, hy, ya⟩
    refine ⟨yieldF ps f (0 + x) y, ?_, ?_⟩
    · change (mapI (yieldF ps f) 0 v.A)[x]? = _
      rw [getElem?_mapI, hy]; rfl
    · unfold yieldF; split <;> exact ya

/-- Theorem 2 along the transfer phases (WC4 C5.2): from a state where the parameters are
yielded and `KBase` holds, the transfers keep `KBase`, given the destination of each transfer
owned by a frame. -/
theorem transfers_base {k : K} {fin : S3} {c f : Nat} {ps : List Nat} :
    ∀ (t : SC) (vs : List (Nat × Nat)), ValTransfersPre k fin c t vs →
      KBase (yieldEff t ps f) → (∀ v ∈ vs, FrameOwned t.P v.2) →
      (∀ a ∈ ps, ∀ y, t.A[a]? = some y → ∃ g, y.holder = .frame g) →
      KBase (yieldEff (transfersEff c t vs) ps f)
  | _, [], _, hk, _, _ => hk
  | t, v :: vs, ⟨hpre, hrest⟩, hk, hown, hp => by
    simp only [transfersEff]
    have hu : ∀ q, ((yieldEff t ps f).view c).Usable q ↔ (t.view c).Usable q := fun q =>
      S3.Usable.congr (s' := (yieldEff t ps f).view c) (s := t.view c) rfl rfl rfl
    have hdeps : ∀ x ∈ movedDeps ((yieldEff t ps f).view c) v.1,
        ((yieldEff t ps f).view c).Active x := by
      intro x hx
      have hmd : movedDeps ((yieldEff t ps f).view c) v.1 = movedDeps (t.view c) v.1 := by
        unfold movedDeps
        congr 1
      rw [hmd] at hx
      exact (yield_active (v := t.view c) (ps := ps) (f := f)).2 (hpre.depsValid x hx)
    have hown₀ : FrameOwned ((yieldEff t ps f).view c).P v.2 := hown v (List.mem_cons_self ..)
    have hk₁ := transfer_base hk ((hu _).2 hpre.srcUsable) ((hu _).2 hpre.dstUsable) hdeps
      hpre.sameShape hpre.disjoint
      (transfer_usable_frameOwned ((hu _).2 hpre.dstUsable) hown₀)
    rw [yield_transfer hp] at hk₁
    refine transfers_base (transferEffC t c v.1 v.2) vs hrest hk₁ (fun w hw => ?_)
      (fun a ha y hy => ?_)
    · exact transfer_frameOwned (hown w (List.mem_cons_of_mem _ hw))
    · obtain ⟨y₀, hy₀, e⟩ := transfer_frame_held hy
      obtain ⟨g, hg⟩ := hp a ha y₀ hy₀
      exact ⟨g, by rw [e ⟨g, hg⟩, hg]⟩

end TransferPreserveAux

open PreservationAux TransferPreserveAux

/-- Theorem 2 (WC4 C4, C5, C20, C23) for the by-value composite: `SpawnValPre` and `KInvCA` before
the composite give `KInvCA` after it. The anchor orders are the final checks of WC4 C5.4
(`SpawnValPre.anchorOrder`, `SpawnValPre.anchorOrderHeld`). -/
theorem spawnVal_preservesC {k : K} {s s' : SC} {c : Nat} {ps : List Nat} {ls : LocalShape}
    {vs : List (Nat × Nat)} (hk : KInvCA s) (h : SpawnValStep k s c ps ls vs (.ok s')) :
    KInvCA s' := by
  obtain ⟨-, h⟩ := h; obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  have hpar : ParamsOK (s.view c) ps := hpre.params
  have hlt : ∀ a ∈ ps, a < s.A.length := fun a ha => by
    have := hpre.params a ha
    unfold OptP at this; split at this
    · exact lt_of_getElem? ‹_›
    · exact this.elim
  have hframe : ∀ a ∈ ps, ∀ y, (spawnCreate s c ls).A[a]? = some y →
      ∃ g, y.holder = .frame g := by
    intro a ha y hy
    have hp := hpre.params a ha
    have hy' : (spawnCreate s c ls).A[a]? = s.A[a]? := by
      show (mapI _ 0 s.A ++ _)[a]? = _
      rw [List.getElem?_append_left (by rw [length_mapI]; exact hlt a ha), getElem?_mapI]
      cases s.A[a]? <;> simp
    rw [hy'] at hy
    have hy₂ : (s.view c).A[a]? = some y := hy
    rw [hy₂] at hp
    exact ⟨_, hp.2.1⟩
  have hb₀ : KBase (yieldEff (spawnCreate s c ls) ps s.nF) := by
    rw [create_yield hlt]; exact spawn_base hk hpre.creatorLive hpar hpre.localsOK
  have hb := transfers_base (spawnCreate s c ls) vs hpre.transfers hb₀
    (fun v hv => spawn_frameOwned (hpre.freshDst v hv)) hframe
  exact kInvCA_of hb.1 hb.2 hpre.anchorOrder hpre.anchorOrderHeld

end Ern.Concurrency
