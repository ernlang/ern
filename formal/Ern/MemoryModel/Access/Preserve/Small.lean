import Ern.MemoryModel.Access.Preserve.Common

/-!
# Access kernel: preservation by `depend`, `store`, `read`, `write`, `writeShared`, `pin`, `unpin`

Every `ok` step of O5 `depend` (§64), O8 `store` (§65), O9 `read` (§66), O10 `write` (§67), O11
`writeShared` (§68), O15 `pin` (§74) and O16 `unpin` (§75) preserves the kernel invariant `KInv`
of §57 and the auxiliary invariant `KAux` (§58: an `ok` transition preserves the relevant
invariants). Per-invariant lemmas come first, then the clause-level properties of these operations
and their determinism (§58).
-/

namespace Ern.MemoryModel.Access

/-! ## Transport of the invariants (§44, §49–§54) -/

/-- Equal authority lists have the same skeletons (§42). -/
private theorem skel_of_A {s s' : S3} (hA : s'.A = s.A) : SameSkel s s' :=
  ⟨by rw [hA], fun j => by rw [hA]⟩

/-- Under the origin order of `WF3` (§49.5), the effective anchor of `x` has no origin: it is the
root reached along the origin chain (§44). -/
private theorem effAnchor_root {s : S3} (hw : WF3 s) :
    ∀ n x, x < n → s.org (s.effAnchor x) = none
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, x, hx => by
    cases ho : s.org x with
    | none => simp [S3.effAnchor, S3.ancs, chain_none ho, ho]
    | some o =>
      have hlt : o < x := by
        simp only [S3.org] at ho
        cases hy : s.A[x]? with
        | none => rw [hy] at ho; cases ho
        | some y => rw [hy] at ho; exact hw.origins x y o hy ho
      have e : s.effAnchor x = s.effAnchor o := by
        simp only [S3.effAnchor, S3.ancs, chain_cons ho hlt, List.getLastD_cons]
      rw [e]; exact effAnchor_root hw n o (by omega)

/-- `EffAnchorOK` (§44) depends only on the authorities, the places and the stack. -/
private theorem effAnchorOK_of_A {s s' : S3} (hA : s'.A = s.A) (hP : s'.P = s.P)
    (hF : s'.F = s.F) (x : Nat) (fd : Option Nat) : EffAnchorOK s' x fd ↔ EffAnchorOK s x fd := by
  have he : s'.effAnchor x = s.effAnchor x := by simp only [S3.effAnchor, (skel_of_A hA).ancs]
  unfold EffAnchorOK; rw [he, hA, hF]; simp only [S3.hframe_congr hP]

/-- `EffAnchorOK` (§44) is unchanged by a step that keeps the places, the stack, the skeletons of
the authorities and every authority with no origin: under `WF3` (§49.5) the effective anchor has
no origin. -/
private theorem effAnchorOK_skel {s s' : S3} (hw : WF3 s) (sk : SameSkel s s') (hP : s'.P = s.P)
    (hF : s'.F = s.F)
    (hroot : ∀ (i : Nat) (z : Authority), z.origin = none → (s'.A[i]? = some z ↔ s.A[i]? = some z))
    (x : Nat) (fd : Option Nat) : EffAnchorOK s' x fd ↔ EffAnchorOK s x fd := by
  have he : s'.effAnchor x = s.effAnchor x := by simp only [S3.effAnchor, sk.ancs]
  unfold EffAnchorOK
  rw [he, hF]
  cases hz : s.A[s.effAnchor x]? with
  | none =>
    have hz' : s'.A[s.effAnchor x]? = none := by
      have := sk.2 (s.effAnchor x); rw [hz] at this
      cases h : s'.A[s.effAnchor x]? with
      | none => rfl
      | some _ => rw [h] at this; cases this
    rw [hz']; exact Iff.rfl
  | some z =>
    have hzo : z.origin = none := by
      have := effAnchor_root hw (x + 1) x (Nat.lt_succ_self x)
      simpa only [S3.org, hz, Option.bind_some] using this
    rw [(hroot _ z hzo).2 hz]
    simp only [OptP, S3.hframe_congr hP]

/-- `WF3` (§49) carries over to a state with the same places, stack, fresh frame bound and death
markers, the same skeletons of authorities, the same authorities with no origin, and live
holders for its active authorities. -/
private theorem wf3_skel {s s' : S3} (hw : WF3 s) (sk : SameSkel s s') (hP : s'.P = s.P)
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

/-- `I1`–`I4` (§50–§53) carry over to a state with the same places, stack, death markers and
skeletons of authorities, whose anchors of usable places are active. -/
private theorem inv3base_skel {s s' : S3} (hi : Inv3base s) (sk : SameSkel s s')
    (hP : s'.P = s.P) (hF : s'.F = s.F) (hd : s'.dead = s.dead)
    (hD : ∀ q : Nat, s.Usable q → ∀ x ∈ s'.D q, s.Active x) : Inv3base s' := by
  obtain ⟨i1, i2, -, -⟩ := hi
  exact ⟨sk.i1 i1, sk.i2 i2,
    fun q hq x hx => sk.active.2 (hD q ((S3.Usable.congr hP hF hd).1 hq) x hx), i4_always _⟩

/-- `AnchorOrder` (§44) in a state with the same places, stack and death markers and the same
`EffAnchorOK`, whose anchors of usable places satisfy the rule in the previous state. -/
private theorem anchorOrder_of {s s' : S3} (hP : s'.P = s.P) (hF : s'.F = s.F)
    (hd : s'.dead = s.dead)
    (heq : ∀ (x : Nat) (fd : Option Nat), EffAnchorOK s' x fd ↔ EffAnchorOK s x fd)
    (hD : ∀ q : Nat, s.Usable q → ∀ x ∈ s'.D q, EffAnchorOK s x (s.pframe q)) : AnchorOrder s' :=
  fun q hq x hx => by
    rw [heq, S3.pframe_congr hP]; exact hD q ((S3.Usable.congr hP hF hd).1 hq) x hx

/-- `AnchorOrderHeld` (§44) carries over to a state with the same places, stack and death markers
and the same `EffAnchorOK`, whose active authorities are active with the same holder before. -/
private theorem anchorOrderHeld_of {s s' : S3} (h : AnchorOrderHeld s) (hP : s'.P = s.P)
    (hF : s'.F = s.F) (hd : s'.dead = s.dead)
    (heq : ∀ (x : Nat) (fd : Option Nat), EffAnchorOK s' x fd ↔ EffAnchorOK s x fd)
    (hback : ∀ (x : Nat) (y' : Authority), s'.A[x]? = some y' → y'.active = true →
      ∃ y, s.A[x]? = some y ∧ y.active = true ∧ y.holder = y'.holder) : AnchorOrderHeld s' := by
  intro q hq x y' hy ya hh
  obtain ⟨y, hy0, ya0, hh0⟩ := hback x y' hy ya
  rw [heq, S3.pframe_congr hP]
  exact h q ((S3.Usable.congr hP hF hd).1 hq) x y hy0 ya0 (hh0.trans hh)

/-- `NoDangling` (§54) carries over to a state with the same places, stack, death markers and
skeletons of authorities. -/
private theorem noDangling_skel {s s' : S3} (h : NoDangling s) (sk : SameSkel s s')
    (hP : s'.P = s.P) (hF : s'.F = s.F) (hd : s'.dead = s.dead) : NoDangling s' := by
  intro j y hy ya q hq l hl hly
  obtain ⟨y0, hy0, e⟩ := sk.get hy
  simp only [skel, Prod.mk.injEq] at e
  rw [hP] at hl
  exact h j y0 hy0 (by rw [← e.2.2.2]; exact ya) q
    (fun hu => hq ((S3.Usable.congr hP hF hd).2 hu)) l hl (by rw [← e.2.2.1]; exact hly)

/-- `RootHeldConv` (§40, §49.7) carries over to a state with the same places whose authorities
with no origin are authorities of the previous state. -/
private theorem rootHeldConv_of {s s' : S3} (h : RootHeldConv s) (hP : s'.P = s.P)
    (hroot : ∀ (i : Nat) (z : Authority), z.origin = none → s'.A[i]? = some z → s.A[i]? = some z) :
    RootHeldConv s' :=
  h.transport hP fun x z hx hzo => ⟨z, hroot x z hzo hx, hzo, rfl, rfl⟩

/-- The conjuncts of `KInv` (§57) and `KAux` give `KInv ∧ KAux`; `NoOrphan` follows from `WF3`
(§54). -/
private theorem kinv_of_parts {s : S3} (hb : WF3 s ∧ Inv3base s) (ho : AnchorOrder s)
    (hn : NoDangling s) (hh : AnchorOrderHeld s) (hc : RootHeldConv s) : KInv s ∧ KAux s :=
  ⟨kInv_of hb.1 ⟨hb.2, ho, hn⟩ hh, hc⟩

/-! ## Steps that keep the authorities (§64, §67, §68, §74, §75) -/

/-- `WF3` (§49) and `I1`–`I4` (§50–§53) carry over to a state with the same authorities, places,
stack, fresh frame bound and death markers, whose anchors of usable places are active. -/
private theorem sameA_base {s s' : S3} (hw : WF3 s) (hi : Inv3base s) (hA : s'.A = s.A)
    (hP : s'.P = s.P) (hF : s'.F = s.F) (hn : s'.nF = s.nF) (hd : s'.dead = s.dead)
    (hD : ∀ q : Nat, s.Usable q → ∀ x ∈ s'.D q, s.Active x) : WF3 s' ∧ Inv3base s' :=
  ⟨wf3_skel hw (skel_of_A hA) hP hF hn hd (fun _ _ _ => by rw [hA])
      fun a y hy ya => hw.holders a y (by rw [← hA]; exact hy) ya,
    inv3base_skel hi (skel_of_A hA) hP hF hd hD⟩

/-- `AnchorOrderHeld` (§44) carries over to a state with the same authorities, places, stack and
death markers. -/
private theorem sameA_anchorOrderHeld {s s' : S3} (h : AnchorOrderHeld s) (hA : s'.A = s.A)
    (hP : s'.P = s.P) (hF : s'.F = s.F) (hd : s'.dead = s.dead) : AnchorOrderHeld s' :=
  anchorOrderHeld_of h hP hF hd (effAnchorOK_of_A hA hP hF)
    fun _ y' hy ya => ⟨y', by rw [← hA]; exact hy, ya, rfl⟩

/-- `RootHeldConv` (§40, §49.7) carries over to a state with the same authorities and places. -/
private theorem sameA_rootHeldConv {s s' : S3} (h : RootHeldConv s) (hA : s'.A = s.A)
    (hP : s'.P = s.P) : RootHeldConv s' :=
  rootHeldConv_of h hP fun _ _ _ hz => by rw [← hA]; exact hz

/-! ## O5 `depend` (§64) -/

/-- The anchors after `depend(q, x)` (§64, `ok` effect): those before, and `x` on `q`. -/
private theorem depend_D {s : S3} {q x r y : Nat} (hy : y ∈ (dependEff s q x).D r) :
    y ∈ s.D r ∨ (r = q ∧ y = x) := by
  simp only [dependEff] at hy
  split at hy
  · rename_i hrq
    rcases List.mem_append.1 hy with hy | hy
    · exact .inl (hrq ▸ hy)
    · exact .inr ⟨hrq, List.mem_singleton.1 hy⟩
  · exact .inl hy

/-- `depend` preserves `WF3` (§49) and `I1`–`I4` (§50–§53): only `D` changes, and the new anchor
is active (§64.2). -/
theorem depend_preserves_base {s s' : S3} {q x : Nat} (hw : WF3 s) (hi : Inv3base s)
    (h : DependStep q x s (.ok s')) : WF3 s' ∧ Inv3base s' := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  have i3 := hi.2.2.1
  refine sameA_base hw hi rfl rfl rfl rfl rfl fun r hr y hy => ?_
  rcases depend_D hy with hy | ⟨-, rfl⟩
  · exact i3 r hr y hy
  · exact hpre.anchorActive

/-- `depend` preserves `AnchorOrder` (§44): the new anchor satisfies §64.3. -/
theorem depend_preserves_anchorOrder {s s' : S3} {q x : Nat} (hao : AnchorOrder s)
    (h : DependStep q x s (.ok s')) : AnchorOrder s' := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  refine anchorOrder_of (s := s) rfl rfl rfl (effAnchorOK_of_A rfl rfl rfl) fun r hr y hy => ?_
  rcases depend_D hy with hy | ⟨rfl, rfl⟩
  · exact hao r hr y hy
  · exact hpre.anchorOrder

/-- `depend` preserves `NoDangling` (§54): authorities and places are unchanged. -/
theorem depend_preserves_noDangling {s s' : S3} {q x : Nat} (hnd : NoDangling s)
    (h : DependStep q x s (.ok s')) : NoDangling s' := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
  exact noDangling_skel hnd (skel_of_A rfl) rfl rfl rfl

/-- `depend` preserves `AnchorOrderHeld` (§44): authorities and places are unchanged. -/
theorem depend_preserves_anchorOrderHeld {s s' : S3} {q x : Nat} (haoh : AnchorOrderHeld s)
    (h : DependStep q x s (.ok s')) : AnchorOrderHeld s' := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
  exact sameA_anchorOrderHeld haoh rfl rfl rfl rfl

/-- `depend` preserves `RootHeldConv` (§40, §49.7): authorities and places are unchanged. -/
theorem depend_preserves_rootHeldConv {s s' : S3} {q x : Nat} (hc : RootHeldConv s)
    (h : DependStep q x s (.ok s')) : RootHeldConv s' := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
  exact sameA_rootHeldConv hc rfl rfl

/-- `depend` preserves `KInv` (§57) and `KAux` (§58, §64). -/
theorem depend_preserves {s s' : S3} {q x : Nat} (hinv : KInv s) (haux : KAux s)
    (h : DependStep q x s (.ok s')) : KInv s' ∧ KAux s' := by
  obtain ⟨hw, ⟨hb, ho, hnd⟩, hh, -⟩ := hinv
  exact kinv_of_parts (depend_preserves_base hw hb h) (depend_preserves_anchorOrder ho h)
    (depend_preserves_noDangling hnd h) (depend_preserves_anchorOrderHeld hh h)
    (depend_preserves_rootHeldConv haux h)

/-- `depend_preserves_anchor_validity` (§64.2, §52): `I3` is preserved and every authority keeps
its activity, so a declared dependency extends no lifetime. -/
theorem depend_preserves_anchor_validity {s s' : S3} {q x : Nat} (hi3 : I3 s)
    (h : DependStep q x s (.ok s')) : I3 s' ∧ ∀ y, s'.Active y ↔ s.Active y := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  refine ⟨fun r hr y hy => ?_, fun _ => Iff.rfl⟩
  have hr' := (S3.Usable.congr (s := s) (s' := dependEff s q x) rfl rfl rfl).1 hr
  rcases depend_D hy with hy | ⟨-, rfl⟩
  · exact hi3 r hr' y hy
  · exact hpre.anchorActive

/-- Determinism of `depend` (§58, §64): one outcome. -/
theorem depend_det {q x : Nat} {s : S3} {o₁ o₂ : Outcome3 S3} (h₁ : DependStep q x s o₁)
    (h₂ : DependStep q x s o₂) : o₁ = o₂ := Guarded.det h₁ h₂

/-! ## O8 `store` (§65) -/

/-- The authority of an accepted `store` is active, derived and held by the current frame
(§65.1). -/
private theorem store_pre_auth {s : S3} {a : Nat}
    (h : OptP (s.A[a]?) (fun y => y.active = true ∧ y.origin ≠ none ∧ y.holder = .frame s.top)
      False) :
    ∃ y, s.A[a]? = some y ∧ y.active = true ∧ y.origin ≠ none ∧ y.holder = .frame s.top := by
  unfold OptP at h; split at h
  · rename_i y hy; exact ⟨y, hy, h⟩
  · exact h.elim

/-- The effect of `store` on an existing authority (§65, `ok` effect). -/
private theorem storeEff_eq {s : S3} {a p : Nat} {y : Authority} (hy : s.A[a]? = some y) :
    storeEff s a p = { s with
      A := s.A.set a { y with holder := .place p }
      D := fun q => if q = p then s.D p ++ [a] else s.D q
      I := fun l => if l = p then .init else s.I l } := by
  unfold storeEff; rw [hy]

/-- `store` keeps the places, the stack, the fresh frame bound and the death markers (§65, `ok`
effect). -/
private theorem store_eqs (s : S3) (a p : Nat) : (storeEff s a p).P = s.P ∧
    (storeEff s a p).F = s.F ∧ (storeEff s a p).nF = s.nF ∧ (storeEff s a p).dead = s.dead := by
  unfold storeEff; split <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- The authorities after `store`: `a` held by `p`, the others unchanged (§65, `ok` effect). -/
private theorem store_get {s : S3} {a p : Nat} {y : Authority} (hy : s.A[a]? = some y) (j : Nat) :
    (storeEff s a p).A[j]? = if a = j then some { y with holder := .place p } else s.A[j]? := by
  rw [storeEff_eq hy]; exact set_get (lt_of_getElem? hy)

/-- `store` changes only the holder of `a` among the authorities (§65, `ok` effect). -/
private theorem store_skel {s : S3} {a p : Nat} {y : Authority} (hy : s.A[a]? = some y) :
    SameSkel s (storeEff s a p) := by
  refine ⟨by rw [storeEff_eq hy]; simp, fun j => ?_⟩
  rw [store_get hy]; split
  · subst_vars; simp [hy, skel]
  · rfl

/-- `store` of a derived authority keeps every authority with no origin (§65.1, §65 `ok`
effect). -/
private theorem store_root {s : S3} {a p : Nat} {y : Authority} (hy : s.A[a]? = some y)
    (ho : y.origin ≠ none) (i : Nat) (z : Authority) (hzo : z.origin = none) :
    (storeEff s a p).A[i]? = some z ↔ s.A[i]? = some z := by
  rw [store_get hy]; split
  · subst_vars; rw [hy]
    constructor <;> intro h <;> cases h <;> exact absurd hzo ho
  · exact Iff.rfl

/-- The anchors after `store(a, p)` (§65, `ok` effect): those before, and `a` on `p`. -/
private theorem store_D {s : S3} {a p : Nat} {y : Authority} (hy : s.A[a]? = some y) {q x : Nat}
    (hx : x ∈ (storeEff s a p).D q) : x ∈ s.D q ∨ (q = p ∧ x = a) := by
  rw [storeEff_eq hy] at hx; simp only at hx
  split at hx
  · rename_i hqp
    rcases List.mem_append.1 hx with hx | hx
    · exact .inl (hqp ▸ hx)
    · exact .inr ⟨hqp, List.mem_singleton.1 hx⟩
  · exact .inl hx

/-- `store` preserves `WF3` (§49) and `I1`–`I4` (§50–§53): the stored authority is derived, keeps
its skeleton, is held by a usable place (§65.2) and joins the anchors of `p` while active. -/
theorem store_preserves_base {s s' : S3} {a p : Nat} (hw : WF3 s) (hi : Inv3base s)
    (h : StoreStep a p s (.ok s')) : WF3 s' ∧ Inv3base s' := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  obtain ⟨y, hy, ya, ho, -⟩ := store_pre_auth hpre.derivedHeld
  obtain ⟨hP, hF, hn, hd⟩ := store_eqs s a p
  have i3 := hi.2.2.1
  refine ⟨wf3_skel hw (store_skel hy) hP hF hn hd (store_root hy ho) fun j z hz za => ?_,
    inv3base_skel hi (store_skel hy) hP hF hd fun q hq x hx => ?_⟩
  · rw [store_get hy] at hz; split at hz
    · cases hz; exact hpre.usable
    · exact hw.holders j z hz za
  · rcases store_D hy hx with hx | ⟨-, rfl⟩
    · exact i3 q hq x hx
    · exact ⟨y, hy, ya⟩

/-- `store` preserves `AnchorOrder` (§44): the new anchor satisfies §65.4, and the effective
anchors keep their holders since `a` is derived. -/
theorem store_preserves_anchorOrder {s s' : S3} {a p : Nat} (hw : WF3 s) (hao : AnchorOrder s)
    (h : StoreStep a p s (.ok s')) : AnchorOrder s' := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  obtain ⟨y, hy, -, ho, -⟩ := store_pre_auth hpre.derivedHeld
  obtain ⟨hP, hF, -, hd⟩ := store_eqs s a p
  refine anchorOrder_of hP hF hd (effAnchorOK_skel hw (store_skel hy) hP hF (store_root hy ho))
    fun q hq x hx => ?_
  rcases store_D hy hx with hx | ⟨rfl, rfl⟩
  · exact hao q hq x hx
  · exact hpre.anchorOrder

/-- `store` preserves `NoDangling` (§54): footprints, activity and usability are unchanged. -/
theorem store_preserves_noDangling {s s' : S3} {a p : Nat} (hnd : NoDangling s)
    (h : StoreStep a p s (.ok s')) : NoDangling s' := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  obtain ⟨y, hy, -⟩ := store_pre_auth hpre.derivedHeld
  obtain ⟨hP, hF, -, hd⟩ := store_eqs s a p
  exact noDangling_skel hnd (store_skel hy) hP hF hd

/-- `store` preserves `AnchorOrderHeld` (§44): it is the resulting-state precondition §65.5. -/
theorem store_preserves_anchorOrderHeld {s s' : S3} {a p : Nat} (h : StoreStep a p s (.ok s')) :
    AnchorOrderHeld s' := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  exact hpre.anchorOrderHeld

/-- `store` preserves `RootHeldConv` (§40, §49.7): a root authority is never stored (§65.1). -/
theorem store_preserves_rootHeldConv {s s' : S3} {a p : Nat} (hc : RootHeldConv s)
    (h : StoreStep a p s (.ok s')) : RootHeldConv s' := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  obtain ⟨y, hy, -, ho, -⟩ := store_pre_auth hpre.derivedHeld
  exact rootHeldConv_of hc (store_eqs s a p).1 fun i z hzo hz => (store_root hy ho i z hzo).1 hz

/-- `store` preserves `KInv` (§57) and `KAux` (§58, §65). -/
theorem store_preserves {s s' : S3} {a p : Nat} (hinv : KInv s) (haux : KAux s)
    (h : StoreStep a p s (.ok s')) : KInv s' ∧ KAux s' := by
  obtain ⟨hw, ⟨hb, ho, hnd⟩, -, -⟩ := hinv
  exact kinv_of_parts (store_preserves_base hw hb h) (store_preserves_anchorOrder hw ho h)
    (store_preserves_noDangling hnd h) (store_preserves_anchorOrderHeld h)
    (store_preserves_rootHeldConv haux h)

/-- `store_writes_one_leaf` (§65.2, §65 `ok` effect): the target is a leaf, it becomes `Init`,
and no other leaf changes its initialization state. -/
theorem store_writes_one_leaf {s s' : S3} {a p : Nat} (h : StoreStep a p s (.ok s')) :
    isLeaf s.P p ∧ s'.I p = .init ∧ ∀ l, l ≠ p → s'.I l = s.I l := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  obtain ⟨y, hy, -⟩ := store_pre_auth hpre.derivedHeld
  rw [storeEff_eq hy]
  exact ⟨hpre.leaf, by simp, fun l hl => by simp [hl]⟩

/-- `store_keeps_target_reachable` (§65.5): after an accepted `store`, the current frame has
exercisable `Modify` over the target. -/
theorem store_keeps_target_reachable {s s' : S3} {a p : Nat} (h : StoreStep a p s (.ok s')) :
    HasRight s' .modify p := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  exact hpre.keepsTarget

/-- §65.2: `store` into a target that holds an active authority is rejected. -/
theorem store_occupied_rejected {s : S3} {a p j : Nat} {z : Authority} (hz : s.A[j]? = some z)
    (za : z.active = true) (hzp : z.holder = .place p) : StoreStep a p s .reject :=
  .reject fun hpre => by
    have := hpre.free j (List.mem_range.2 (lt_of_getElem? hz))
    simp only [OptP, hz] at this
    exact this za hzp

/-- §65.1: a root authority (no origin) is never stored. -/
theorem store_root_rejected {s : S3} {a p : Nat} {y : Authority} (hy : s.A[a]? = some y)
    (ho : y.origin = none) : StoreStep a p s .reject :=
  .reject fun hpre => by
    obtain ⟨y', hy', -, ho', -⟩ := store_pre_auth hpre.derivedHeld
    rw [hy] at hy'; cases hy'; exact ho' ho

/-- Determinism of `store` (§58, §65): one outcome. -/
theorem store_det {a p : Nat} {s : S3} {o₁ o₂ : Outcome3 S3} (h₁ : StoreStep a p s o₁)
    (h₂ : StoreStep a p s o₂) : o₁ = o₂ := Guarded.det h₁ h₂

/-! ## O9 `read` (§66) -/

/-- `read_preserves_state` (§66, `ok` effect): an accepted read leaves the state unchanged, in
particular `F`, `P`, `I`, `A` and `D`. -/
theorem read_preserves_state {s s' : S3} {a : Nat} {ls : List Nat}
    (h : Read3Step a ls s (.ok s')) : s' = s := (Guarded.ok_iff.1 h).2

/-- `read` preserves `KInv` (§57) and `KAux` (§58, §66). -/
theorem read_preserves {s s' : S3} {a : Nat} {ls : List Nat} (hinv : KInv s) (haux : KAux s)
    (h : Read3Step a ls s (.ok s')) : KInv s' ∧ KAux s' := by
  rw [read_preserves_state h]; exact ⟨hinv, haux⟩

/-- Determinism of `read` (§58, §66): one outcome. -/
theorem read_det {a : Nat} {ls : List Nat} {s : S3} {o₁ o₂ : Outcome3 S3}
    (h₁ : Read3Step a ls s o₁) (h₂ : Read3Step a ls s o₂) : o₁ = o₂ := Guarded.det h₁ h₂

/-! ## O10 `write`, O11 `writeShared` (§67, §68) -/

/-- The write effect preserves `WF3` (§49) and `I1`–`I4` (§50–§53): only `I` changes (§67, §68
`ok` effects). -/
theorem write3Eff_preserves_base {s : S3} (ls : List Nat) (hw : WF3 s) (hi : Inv3base s) :
    WF3 (write3Eff s ls) ∧ Inv3base (write3Eff s ls) :=
  sameA_base hw hi rfl rfl rfl rfl rfl fun q hq x hx => hi.2.2.1 q hq x hx

/-- The write effect preserves `AnchorOrder` (§44): only `I` changes (§67, §68). -/
theorem write3Eff_preserves_anchorOrder {s : S3} (ls : List Nat) (hao : AnchorOrder s) :
    AnchorOrder (write3Eff s ls) :=
  anchorOrder_of (s := s) rfl rfl rfl (effAnchorOK_of_A rfl rfl rfl) fun q hq x hx =>
    hao q hq x hx

/-- The write effect preserves `NoDangling` (§54): only `I` changes (§67, §68). -/
theorem write3Eff_preserves_noDangling {s : S3} (ls : List Nat) (hnd : NoDangling s) :
    NoDangling (write3Eff s ls) :=
  noDangling_skel hnd (skel_of_A rfl) rfl rfl rfl

/-- The write effect preserves `AnchorOrderHeld` (§44): only `I` changes (§67, §68). -/
theorem write3Eff_preserves_anchorOrderHeld {s : S3} (ls : List Nat) (h : AnchorOrderHeld s) :
    AnchorOrderHeld (write3Eff s ls) :=
  sameA_anchorOrderHeld h rfl rfl rfl rfl

/-- The write effect preserves `RootHeldConv` (§40, §49.7): only `I` changes (§67, §68). -/
theorem write3Eff_preserves_rootHeldConv {s : S3} (ls : List Nat) (h : RootHeldConv s) :
    RootHeldConv (write3Eff s ls) :=
  sameA_rootHeldConv h rfl rfl

/-- The write effect preserves `KInv` (§57) and `KAux` (§67, §68 `ok` effects). -/
private theorem write3Eff_preserves {s : S3} (ls : List Nat) (hinv : KInv s) (haux : KAux s) :
    KInv (write3Eff s ls) ∧ KAux (write3Eff s ls) := by
  obtain ⟨hw, ⟨hb, ho, hnd⟩, hh, -⟩ := hinv
  exact kinv_of_parts (write3Eff_preserves_base ls hw hb) (write3Eff_preserves_anchorOrder ls ho)
    (write3Eff_preserves_noDangling ls hnd) (write3Eff_preserves_anchorOrderHeld ls hh)
    (write3Eff_preserves_rootHeldConv ls haux)

/-- `write` preserves `KInv` (§57) and `KAux` (§58, §67). -/
theorem write_preserves {s s' : S3} {a : Nat} {ls : List Nat} (hinv : KInv s) (haux : KAux s)
    (h : Write3Step a ls s (.ok s')) : KInv s' ∧ KAux s' := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
  exact write3Eff_preserves ls hinv haux

/-- `writeShared` preserves `KInv` (§57) and `KAux` (§58, §68: authorities and I1 do not
change). -/
theorem writeShared_preserves {k : K} {s s' : S3} {a : Nat} {ls : List Nat} (hinv : KInv s)
    (haux : KAux s) (h : WriteSharedStep k a ls s (.ok s')) : KInv s' ∧ KAux s' := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
  exact write3Eff_preserves ls hinv haux

/-- `write_exclusive` (§67.1, §67.2, §50): on every leaf of an accepted write, `access` has
effective `Modify` and no other authority has an effective mode. -/
theorem write_exclusive {s s' : S3} {a : Nat} {ls : List Nat} (h : Write3Step a ls s (.ok s')) :
    ∀ l ∈ ls, effective s a l = some .modify ∧ ∀ b, b ≠ a → effective s b l = none := by
  obtain ⟨hpre, -⟩ := Guarded.ok_iff.1 h
  intro l hl
  refine ⟨hpre.effectiveModify l hl, fun b hb => ?_⟩
  by_cases hbl : b < s.A.length
  · exact hpre.exclusive l hl b (List.mem_range.2 hbl) hb
  · simp [effective, List.getElem?_eq_none_iff.2 (Nat.le_of_not_lt hbl)]

/-- Effective exclusivity of the written leaves (§50, `effective_exclusive`): under `I1`, the
condition §67.2 follows from the effective `Modify` of §67.1. -/
theorem write_exclusive_of_i1 {s : S3} {a : Nat} {ls : List Nat} (h1 : I1 s)
    (heff : ∀ l ∈ ls, effective s a l = some .modify) :
    ∀ l ∈ ls, ∀ b ∈ List.range s.A.length, b ≠ a → effective s b l = none :=
  fun l hl _ _ hb => effective_exclusive h1 (Ne.symm hb) (heff l hl)

/-- Determinism of `write` (§58, §67): one outcome. -/
theorem write_det {a : Nat} {ls : List Nat} {s : S3} {o₁ o₂ : Outcome3 S3}
    (h₁ : Write3Step a ls s o₁) (h₂ : Write3Step a ls s o₂) : o₁ = o₂ := Guarded.det h₁ h₂

/-- Determinism of `writeShared` (§58, §68): one outcome. -/
theorem writeShared_det {k : K} {a : Nat} {ls : List Nat} {s : S3} {o₁ o₂ : Outcome3 S3}
    (h₁ : WriteSharedStep k a ls s o₁) (h₂ : WriteSharedStep k a ls s o₂) : o₁ = o₂ :=
  Guarded.det h₁ h₂

/-! ## O15 `pin`, O16 `unpin` (§74, §75) -/

/-- The pinning effect preserves `WF3` (§49) and `I1`–`I4` (§50–§53): only the pin flags change
(§74, §75 `ok` effects). -/
theorem pinEff_preserves_base {s : S3} (p : Nat) (b : Bool) (hw : WF3 s) (hi : Inv3base s) :
    WF3 (pinEff s p b) ∧ Inv3base (pinEff s p b) :=
  sameA_base hw hi rfl rfl rfl rfl rfl fun q hq x hx => hi.2.2.1 q hq x hx

/-- The pinning effect preserves `AnchorOrder` (§44): only the pin flags change (§74, §75). -/
theorem pinEff_preserves_anchorOrder {s : S3} (p : Nat) (b : Bool) (hao : AnchorOrder s) :
    AnchorOrder (pinEff s p b) :=
  anchorOrder_of (s := s) rfl rfl rfl (effAnchorOK_of_A rfl rfl rfl) fun q hq x hx =>
    hao q hq x hx

/-- The pinning effect preserves `NoDangling` (§54): only the pin flags change (§74, §75). -/
theorem pinEff_preserves_noDangling {s : S3} (p : Nat) (b : Bool) (hnd : NoDangling s) :
    NoDangling (pinEff s p b) :=
  noDangling_skel hnd (skel_of_A rfl) rfl rfl rfl

/-- The pinning effect preserves `AnchorOrderHeld` (§44): only the pin flags change (§74,
§75). -/
theorem pinEff_preserves_anchorOrderHeld {s : S3} (p : Nat) (b : Bool) (h : AnchorOrderHeld s) :
    AnchorOrderHeld (pinEff s p b) :=
  sameA_anchorOrderHeld h rfl rfl rfl rfl

/-- The pinning effect preserves `RootHeldConv` (§40, §49.7): only the pin flags change (§74,
§75). -/
theorem pinEff_preserves_rootHeldConv {s : S3} (p : Nat) (b : Bool) (h : RootHeldConv s) :
    RootHeldConv (pinEff s p b) :=
  sameA_rootHeldConv h rfl rfl

/-- The pinning effect preserves `KInv` (§57) and `KAux` (§74, §75 `ok` effects). -/
private theorem pinEff_preserves {s : S3} (p : Nat) (b : Bool) (hinv : KInv s) (haux : KAux s) :
    KInv (pinEff s p b) ∧ KAux (pinEff s p b) := by
  obtain ⟨hw, ⟨hb, ho, hnd⟩, hh, -⟩ := hinv
  exact kinv_of_parts (pinEff_preserves_base p b hw hb) (pinEff_preserves_anchorOrder p b ho)
    (pinEff_preserves_noDangling p b hnd) (pinEff_preserves_anchorOrderHeld p b hh)
    (pinEff_preserves_rootHeldConv p b haux)

/-- `pin` preserves `KInv` (§57) and `KAux` (§58, §74). -/
theorem pin_preserves {s s' : S3} {p : Nat} (hinv : KInv s) (haux : KAux s)
    (h : PinStep p s (.ok s')) : KInv s' ∧ KAux s' := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
  exact pinEff_preserves p true hinv haux

/-- `unpin` preserves `KInv` (§57) and `KAux` (§58, §75). -/
theorem unpin_preserves {k : K} {s s' : S3} {p : Nat} (hinv : KInv s) (haux : KAux s)
    (h : UnpinStep k p s (.ok s')) : KInv s' ∧ KAux s' := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
  exact pinEff_preserves p false hinv haux

/-- Determinism of `pin` (§58, §74): one outcome. -/
theorem pin_det {p : Nat} {s : S3} {o₁ o₂ : Outcome3 S3} (h₁ : PinStep p s o₁)
    (h₂ : PinStep p s o₂) : o₁ = o₂ := Guarded.det h₁ h₂

/-- Determinism of `unpin` (§58, §75): one outcome. -/
theorem unpin_det {k : K} {p : Nat} {s : S3} {o₁ o₂ : Outcome3 S3} (h₁ : UnpinStep k p s o₁)
    (h₂ : UnpinStep k p s o₂) : o₁ = o₂ := Guarded.det h₁ h₂

end Ern.MemoryModel.Access
