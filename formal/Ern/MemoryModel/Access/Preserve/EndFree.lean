import Ern.MemoryModel.Access.Preserve.Common

/-!
# Preservation by `endUse` (O12, §69) and `free` (O13, §70)

Both effects only make authorities inactive and mark places dead, then release the authorities
whose holder died (§69, §70 `ok` effects). The shared argument is in namespace `EndFree`; the
per-operation results state that each step preserves `KInv` (§57), separately the auxiliary `KAux`
(§40, §49.7), and
the effects of §69 and §70: the ended place stays usable, its leaves become `Uninit`, transitively
owned storage and the released unit are dead, pinned leaves block the step (§69.4, §70.4).
-/

namespace Ern.MemoryModel.Access

namespace EndFree

/-! ## Authorities that are only released (§69, §70) -/

/-- The authorities of `s₁` are those of `s`, some of them made inactive (§69, §70 `ok` effects:
authorities are released, never created or changed otherwise). -/
def OnlyReleases (s s₁ : S3) : Prop :=
  s₁.A.length = s.A.length ∧ ∀ (j : Nat) (z : Authority), s₁.A[j]? = some z →
    ∃ y, s.A[j]? = some y ∧ z.mode = y.mode ∧ z.origin = y.origin ∧ z.footprint = y.footprint ∧
      z.holder = y.holder ∧ (z.active = true → y.active = true)

/-- Mapping the authorities by a function that keeps an authority or makes it inactive only
releases authorities (§69, §70). -/
theorem map_releases {s s₁ : S3} {g : Authority → Authority} (hA : s₁.A = s.A.map g)
    (hg : ∀ y, g y = y ∨ g y = { y with active := false }) : OnlyReleases s s₁ := by
  refine ⟨by rw [hA, List.length_map], fun j z hz => ?_⟩
  rw [hA, List.getElem?_map] at hz
  cases hy : s.A[j]? with
  | none => rw [hy] at hz; cases hz
  | some y =>
    rw [hy] at hz; simp only [Option.map_some, Option.some.injEq] at hz; subst hz
    refine ⟨y, rfl, ?_⟩
    rcases hg y with e | e <;> rw [e] <;> simp

/-- Releases compose (§69, §70: release, then release the authorities whose holder died). -/
theorem OnlyReleases.trans {s s₁ s₂ : S3} (h₁ : OnlyReleases s s₁) (h₂ : OnlyReleases s₁ s₂) :
    OnlyReleases s s₂ := by
  refine ⟨h₂.1.trans h₁.1, fun j z hz => ?_⟩
  obtain ⟨y₁, hy₁, m₁, o₁, f₁, h₁', a₁⟩ := h₂.2 j z hz
  obtain ⟨y, hy, m, o, f, hh, a⟩ := h₁.2 j y₁ hy₁
  exact ⟨y, hy, m₁.trans m, o₁.trans o, f₁.trans f, h₁'.trans hh, fun h => a (a₁ h)⟩

/-- Every authority of `s` has a counterpart after releases, with the same fields but its
activity (§69, §70). -/
theorem OnlyReleases.get' {s s₁ : S3} (h : OnlyReleases s s₁) {j : Nat} {y : Authority}
    (hy : s.A[j]? = some y) : ∃ z, s₁.A[j]? = some z ∧ z.mode = y.mode ∧ z.origin = y.origin ∧
      z.footprint = y.footprint ∧ z.holder = y.holder := by
  obtain ⟨z, hz⟩ : ∃ z, s₁.A[j]? = some z :=
    ⟨_, List.getElem?_eq_some_iff.2 ⟨by rw [h.1]; exact lt_of_getElem? hy, rfl⟩⟩
  obtain ⟨y₀, hy₀, e1, e2, e3, e4, -⟩ := h.2 j z hz
  rw [hy] at hy₀; cases hy₀
  exact ⟨z, hz, e1, e2, e3, e4⟩

/-- Releases keep the origin links (§42, §69, §70). -/
theorem OnlyReleases.org {s s₁ : S3} (h : OnlyReleases s s₁) : s₁.org = s.org := by
  funext j; simp only [S3.org]
  cases hz : s₁.A[j]? with
  | none =>
    have : s.A.length ≤ j := by rw [← h.1]; exact List.getElem?_eq_none_iff.1 hz
    rw [List.getElem?_eq_none_iff.2 this]
  | some z => obtain ⟨y, hy, -, ho, -⟩ := h.2 j z hz; simp [hy, ho]

/-- Releases keep the origin chains (§42, §69, §70). -/
theorem OnlyReleases.ancs {s s₁ : S3} (h : OnlyReleases s s₁) : s₁.ancs = s.ancs := by
  funext j; simp only [S3.ancs, h.org]

/-- Releases keep the holders (§42, §69, §70). -/
theorem OnlyReleases.holder_get {s s₁ : S3} (h : OnlyReleases s s₁) (j : Nat) :
    (s₁.A[j]?).map (·.holder) = (s.A[j]?).map (·.holder) := by
  cases hz : s₁.A[j]? with
  | none =>
    have : s.A.length ≤ j := by rw [← h.1]; exact List.getElem?_eq_none_iff.1 hz
    rw [List.getElem?_eq_none_iff.2 this]
  | some z => obtain ⟨y, hy, -, -, -, e, -⟩ := h.2 j z hz; simp [hy, e]

/-- After releases, with the same places and stack, the anchor-order condition of an authority
is unchanged (§44). -/
theorem OnlyReleases.effAnchorOK {s s₁ : S3} (h : OnlyReleases s s₁) (hP : s₁.P = s.P)
    (hF : s₁.F = s.F) (x : Nat) (fd : Option Nat) :
    EffAnchorOK s₁ x fd ↔ EffAnchorOK s x fd := by
  have he : s₁.effAnchor x = s.effAnchor x := by simp only [S3.effAnchor, h.ancs]
  have hh := h.holder_get (s.effAnchor x)
  unfold EffAnchorOK
  rw [he, hF]
  cases h₁ : s₁.A[s.effAnchor x]? with
  | none =>
    cases h₀ : s.A[s.effAnchor x]? with
    | none => exact Iff.rfl
    | some y => rw [h₁, h₀] at hh; cases hh
  | some z =>
    cases h₀ : s.A[s.effAnchor x]? with
    | none => rw [h₁, h₀] at hh; cases hh
    | some y =>
      rw [h₁, h₀] at hh
      simp only [Option.map_some, Option.some.injEq] at hh
      simp only [OptP, hh, S3.hframe_congr hP]

/-! ## Release of authorities whose holder died (§69, §70) -/

/-- The authorities after `cleanup` (§69, §70): those whose holder is not live are inactive. -/
theorem cleanup_get (s : S3) (j : Nat) : (cleanup s).A[j]? =
    (s.A[j]?).map fun y => if HolderLive s y.holder then y else { y with active := false } := by
  simp [cleanup]

/-- `cleanup` only releases authorities (§69, §70). -/
theorem cleanup_releases (s : S3) : OnlyReleases s (cleanup s) :=
  map_releases rfl fun y => by by_cases h : HolderLive s y.holder <;> simp [h]

/-- An active authority after `cleanup` was active before and has a live holder (§69, §70). -/
theorem cleanup_active {s : S3} {j : Nat} {z : Authority} (hz : (cleanup s).A[j]? = some z)
    (za : z.active = true) : s.A[j]? = some z ∧ HolderLive s z.holder := by
  rw [cleanup_get] at hz
  cases hy : s.A[j]? with
  | none => rw [hy] at hz; cases hz
  | some y =>
    rw [hy] at hz
    by_cases hl : HolderLive s y.holder
    · simp only [hl, Option.map_some, ↓reduceIte, Option.some.injEq] at hz
      subst hz; exact ⟨rfl, hl⟩
    · simp only [hl, Option.map_some, ↓reduceIte, Option.some.injEq] at hz
      subst hz; simp at za

/-- Usability after `cleanup` is usability before (§40: it depends on places, stack and death
markers only). -/
theorem cleanup_usable (s : S3) (q : Nat) : (cleanup s).Usable q ↔ s.Usable q :=
  S3.Usable.congr (s := s) (s' := cleanup s) rfl rfl rfl

/-! ## Usability (§40) -/

/-- A usable place is not marked dead (§40, item 1). -/
theorem dead_false {s : S3} {q : Nat} (h : s.Usable q) : s.dead q = false := by
  cases h <;> assumption

/-- The owner of a usable place is live (§40, items 2–3). -/
theorem owner_live {s : S3} {q : Nat} {pl : Place} (h : s.Usable q) (hpl : s.P[q]? = some pl) :
    HolderLive s pl.owner := by
  cases h with
  | frame hp _ ho hf => rw [hpl] at hp; cases hp; rw [ho]; exact hf
  | place hp _ ho hu => rw [hpl] at hp; cases hp; rw [ho]; exact hu

/-- A place that is not dead and whose owner is live is usable (§40, items 1–3). -/
theorem usable_of_owner {s : S3} {q : Nat} {pl : Place} (hpl : s.P[q]? = some pl)
    (hd : s.dead q = false) (hl : HolderLive s pl.owner) : s.Usable q := by
  cases ho : pl.owner with
  | frame f => rw [ho] at hl; exact .frame hpl hd ho hl
  | place o => rw [ho] at hl; exact .place hpl hd ho hl

/-- Transitive ownership depends only on the owner (§40): a place with the owner of a place owned
through `src` is owned through `src`. -/
theorem ownedIn_of_owner {P : List Place} {src q r : Nat} {pq pr : Place} (hq : P[q]? = some pq)
    (hr : P[r]? = some pr) (ho : pr.owner = pq.owner) (h : OwnedIn P src q) : OwnedIn P src r := by
  cases h with
  | direct hpl hpo hpart => rw [hq] at hpl; cases hpl; exact .direct hr (ho.trans hpo) hpart
  | step hpl hpo hown => rw [hq] at hpl; cases hpl; exact .step hr (ho.trans hpo) hown

/-- Transitive ownership through `src` is shared by a place and its structural parent (§40,
§49.2: parts share their parent's owner). -/
theorem ownedIn_parent {s : S3} (hw : WF3 s) {src q r : Nat} {pl : Place}
    (hq : s.P[q]? = some pl) (hp : pl.parent = some r) : OwnedIn s.P src r ↔ OwnedIn s.P src q := by
  obtain ⟨pr, hpr, -, ho, -⟩ := hw.places q pl r hq hp
  exact ⟨ownedIn_of_owner hpr hq ho.symm, ownedIn_of_owner hq hpr ho⟩

/-! ## Ownership cycles (§40) -/

/-- `Above P q c` (§40): place `c` is on the ownership chain of `q`, strictly above `q`. -/
inductive Above (P : List Place) : Nat → Nat → Prop where
  /-- The owner place of `q` is above `q` (§40). -/
  | owner {q o : Nat} {pl : Place} : P[q]? = some pl → pl.owner = .place o → Above P q o
  /-- A place above the owner place of `q` is above `q` (§40). -/
  | step {q o c : Nat} {pl : Place} : P[q]? = some pl → pl.owner = .place o → Above P o c →
      Above P q c

/-- The ownership chain is transitive (§40). -/
theorem Above.trans {P : List Place} {a b c : Nat} (h₁ : Above P a b) (h₂ : Above P b c) :
    Above P a c := by
  induction h₁ with
  | owner hpl ho => exact .step hpl ho h₂
  | step hpl ho _ ih => exact .step hpl ho (ih h₂)

/-- A usable place is not on its own ownership chain (§40: an ownership cycle makes no place
usable). -/
theorem not_above_self {s : S3} {c : Nat} (h : s.Usable c) : ¬ Above s.P c c := by
  induction h with
  | frame hpl _ ho _ =>
    intro ha; cases ha with
    | owner hpl' ho' => rw [hpl] at hpl'; cases hpl'; rw [ho] at ho'; cases ho'
    | step hpl' ho' _ => rw [hpl] at hpl'; cases hpl'; rw [ho] at ho'; cases ho'
  | @place q o pl hpl _ ho _ ih =>
    intro ha; cases ha with
    | owner hpl' ho' =>
      rw [hpl] at hpl'; cases hpl'; rw [ho] at ho'; cases ho'
      exact ih (.owner hpl ho)
    | step hpl' ho' hc =>
      rw [hpl] at hpl'; cases hpl'; rw [ho] at ho'; cases ho'
      exact ih (hc.trans (.owner hpl ho))

/-- A place owned through `src` has a part of `src` on its ownership chain (§40). -/
theorem OwnedIn.above {P : List Place} {src q : Nat} (h : OwnedIn P src q) :
    ∃ x, partOf P x src ∧ Above P q x := by
  induction h with
  | direct hpl ho hpart => exact ⟨_, hpart, .owner hpl ho⟩
  | step hpl ho _ ih => obtain ⟨x, hx, ha⟩ := ih; exact ⟨x, hx, .step hpl ho ha⟩

/-- Under `WF3`, no place on the ownership chain of a usable place `p`, `p` included, is owned
through `p` (§40: an ownership cycle makes no place usable; §49.2: parts share the owner). -/
theorem not_ownedIn_chain {s : S3} (hw : WF3 s) {p q : Nat} (hp : s.Usable p)
    (hq : q = p ∨ Above s.P p q) : ¬ OwnedIn s.P p q := by
  intro h
  obtain ⟨x, hx, hqx⟩ := OwnedIn.above h
  have hpx : Above s.P p x := by
    rcases hq with rfl | hq
    · exact hqx
    · exact hq.trans hqx
  obtain ⟨plx, plp, hplx, hplp, ho⟩ := hw.ownerOf hx
  cases hpx with
  | owner hpl hpo =>
    rw [hplp] at hpl; cases hpl
    cases hp with
    | frame hpl' _ hpo' _ => rw [hplp] at hpl'; cases hpl'; rw [hpo] at hpo'; cases hpo'
    | place hpl' _ hpo' hu =>
      rw [hplp] at hpl'; cases hpl'; rw [hpo] at hpo'; cases hpo'
      exact not_above_self hu (.owner hplx (ho.trans hpo))
  | step hpl hpo hcx =>
    rw [hplp] at hpl; cases hpl
    cases hp with
    | frame hpl' _ hpo' _ => rw [hplp] at hpl'; cases hpl'; rw [hpo] at hpo'; cases hpo'
    | place hpl' _ hpo' hu =>
      rw [hplp] at hpl'; cases hpl'; rw [hpo] at hpo'; cases hpo'
      exact not_above_self hu (hcx.trans (.owner hplx (ho.trans hpo)))

/-! ## The shared preservation argument (§57, §69, §70) -/

/-- Releasing authorities and marking places dead, then releasing the authorities whose holder
died, preserves `KInv` (§57), provided the death markers respect parts (§49.2), usable places keep
only valid former anchors (§52, §44), the root authorities of usable root places are kept (§49.7),
and `NoDangling` (§54) holds afterwards. -/
theorem releases_preserve {s s₁ : S3} (hk : KInv s) (hr : OnlyReleases s s₁)
    (hP : s₁.P = s.P) (hF : s₁.F = s.F) (hn : s₁.nF = s.nF)
    (hd : ∀ q, s₁.dead q = false → s.dead q = false)
    (hparts : ∀ (q : Nat) (pl : Place) (r : Nat), s.P[q]? = some pl → pl.parent = some r →
      s₁.dead r = s₁.dead q)
    (hD : ∀ q, s₁.Usable q → ∀ x ∈ s₁.D q, x ∈ s.D q)
    (hI3 : ∀ q, s₁.Usable q → ∀ x ∈ s₁.D q, (cleanup s₁).Active x)
    (hroot : ∀ (r i : Nat) (z : Authority) (pr : Place), RootPlace s.P r → s₁.Usable r →
      s.A[i]? = some z → z.active = true → z.origin = none → s.P[r]? = some pr →
      z.holder = pr.owner → (∀ l, l ∈ z.footprint ↔ l ∈ footprint s.P r) → s₁.A[i]? = some z)
    (hnd : WF3 (cleanup s₁) → NoDangling (cleanup s₁)) :
    KInv (cleanup s₁) := by
  obtain ⟨hw, ⟨⟨i1, i2, -, -⟩, hao, -⟩, haoh, -⟩ := hk
  have hc := hr.trans (cleanup_releases s₁)
  have cP : (cleanup s₁).P = s.P := hP
  have cF : (cleanup s₁).F = s.F := hF
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
  refine kInv_of hw' ⟨⟨?_, ?_, ?_, i4_always _⟩, ?_, hnd hw'⟩ ?_
  · intro a b x y p hab hx hy xa ya xp yp hnab hnba
    obtain ⟨x₀, hx₀, m₁, -, f₁, -, a₁⟩ := hc.2 a x hx
    obtain ⟨y₀, hy₀, m₂, -, f₂, -, a₂⟩ := hc.2 b y hy
    rw [hc.ancs] at hnab hnba; rw [m₁, m₂]
    exact i1 a b x₀ y₀ p hab hx₀ hy₀ (a₁ xa) (a₂ ya) (f₁ ▸ xp) (f₂ ▸ yp) hnab hnba
  · intro b y a hb ho
    obtain ⟨y₀, hy₀, m₀, e, f₀, -⟩ := hc.2 b y hb
    obtain ⟨x₁, hx₁, hm, hsub⟩ := i2 b y₀ a hy₀ (e ▸ ho)
    obtain ⟨x', hx', mx, -, fx, -⟩ := hc.get' hx₁
    exact ⟨x', hx', by rw [m₀, mx]; exact hm, fun l hl => by rw [fx]; exact hsub l (f₀ ▸ hl)⟩
  · exact fun q hq x hx => hI3 q ((hU q).1 hq) x hx
  · intro q hq x hx
    have hq₁ := (hU q).1 hq
    refine (hc.effAnchorOK cP cF x _).2 ?_
    rw [S3.pframe_congr cP]
    exact hao q (hu q hq₁) x (hD q hq₁ x hx)
  · intro q hq x y' hx ya hh
    obtain ⟨y, hy, -, -, -, e, ea⟩ := hc.2 x y' hx
    refine (hc.effAnchorOK cP cF x _).2 ?_
    rw [S3.pframe_congr cP]
    exact haoh q (hu q ((hU q).1 hq)) x y hy (ea ya) (e.symm.trans hh)

/-- Releasing authorities with the places unchanged, then releasing the authorities whose holder
died, preserves the auxiliary `KAux` (`RootHeldConv`, §40, §49.7): authorities with no origin keep
their footprint and holder. -/
theorem releases_preserve_kAux {s s₁ : S3} (ha : KAux s) (hr : OnlyReleases s s₁)
    (hP : s₁.P = s.P) : KAux (cleanup s₁) := by
  have hc := hr.trans (cleanup_releases s₁)
  exact RootHeldConv.transport ha hP fun x z' hx ho => by
    obtain ⟨z, hz, -, e1, e2, e3, -⟩ := hc.2 x z' hx
    exact ⟨z, hz, e1 ▸ ho, e2, e3⟩

end EndFree

open EndFree

/-! ## O12 `endUse` (§69) -/

/-- The authorities after `endUseS` (§69, `ok` effect): those held within `p` are inactive. -/
theorem EndFree.endUseS_get (s : S3) (p j : Nat) : (endUseS s p).A[j]? =
    (s.A[j]?).map fun y => if heldIn s.P p y.holder then { y with active := false } else y := by
  simp [endUseS]

/-- `endUseS` only releases authorities (§69, `ok` effect). -/
theorem EndFree.endUseS_releases (s : S3) (p : Nat) : OnlyReleases s (endUseS s p) :=
  map_releases rfl fun y => by by_cases h : heldIn s.P p y.holder <;> simp [h]

/-- A place usable after `endUseS` was usable before (§69: the effect only adds death
markers). -/
theorem EndFree.endUseS_usable {s : S3} {p q : Nat} (h : (endUseS s p).Usable q) : s.Usable q :=
  S3.Usable.mono (s := s) (s' := endUseS s p) rfl (fun _ h => h)
    (fun q h => by simp only [endUseS, Bool.or_eq_false_iff] at h; exact h.1) h

/-- An active authority after `endUse p` (§69, `ok` effect): active before, not held within `p`,
with a holder live after `endUseS`. -/
theorem EndFree.endUse_active {s : S3} {p j : Nat} {z : Authority}
    (hz : (endUseEff s p).A[j]? = some z) (za : z.active = true) :
    s.A[j]? = some z ∧ ¬ heldIn s.P p z.holder ∧ HolderLive (endUseS s p) z.holder := by
  obtain ⟨hz₁, hl⟩ := cleanup_active hz za
  rw [endUseS_get] at hz₁
  cases hy : s.A[j]? with
  | none => rw [hy] at hz₁; cases hz₁
  | some y =>
    rw [hy] at hz₁
    by_cases hh : heldIn s.P p y.holder
    · simp only [hh, Option.map_some, ↓reduceIte, Option.some.injEq] at hz₁
      subst hz₁; simp at za
    · simp only [hh, Option.map_some, ↓reduceIte, Option.some.injEq] at hz₁
      subst hz₁; exact ⟨rfl, hh, hl⟩

/-- Under `EndUsePre` (§69.3) and `I3` (§52), every anchor of a place usable after `endUseS`
stays active after `endUse`. -/
theorem EndFree.endUse_anchors {k : K} {s : S3} {p : Nat} (h3 : I3 s) (hpre : EndUsePre k s p) :
    ∀ q, (endUseS s p).Usable q → ∀ x ∈ (endUseS s p).D q, (endUseEff s p).Active x := by
  intro q hq x hx
  have hq₀ := endUseS_usable hq
  have hx₀ : x ∈ s.D q := by
    simp only [endUseS] at hx; split at hx
    · simp at hx
    · exact hx
  obtain ⟨y, hy, ya⟩ := h3 q hq₀ x hx₀
  have hc := hpre.anchors q (List.mem_range.2 hq₀.lt) hq x hx
  unfold EndUseAnchorOK OptP at hc; rw [hy] at hc
  obtain ⟨hnh, -, hl⟩ := hc
  exact ⟨y, by rw [endUseEff, cleanup_get, endUseS_get, hy]; simp [hnh, hl], ya⟩

/-- `endUse` preserves `NoDangling` (§54, §69), under `WF3` (§49) and `I1` (§50): an active
authority on a leaf of a place that stops being usable is derived, and blocked by §69.2, or a
root, held by the owner of the root place of the leaf (`rootHeldConv_active`), which would stay
usable. -/
theorem EndFree.endUse_noDangling {k : K} {s : S3} {p : Nat} (hw : WF3 s) (hnd : NoDangling s)
    (h1 : I1 s) (hpre : EndUsePre k s p) (hw' : WF3 (endUseEff s p)) :
    NoDangling (endUseEff s p) := by
  have hU := cleanup_usable (endUseS s p)
  intro j z hz za q hq l hl hlz
  obtain ⟨hz₀, hnh, hlive⟩ := endUse_active hz za
  by_cases hq₀ : ¬ s.Usable q
  · exact hnd j z hz₀ za q hq₀ l hl hlz
  replace hq₀ := Decidable.of_not_not hq₀
  obtain ⟨-, hleaf, hlq⟩ := mem_footprint.1 hl
  have hl₀ : s.Usable l := usable_of_partOf hw (l + 1) l q (Nat.lt_succ_self l) hlq hq₀
  have hl₁ : ¬ (endUseS s p).Usable l := fun hu => hq (usable_of_part hw' hlq ((hU l).2 hu))
  cases hzo : z.origin with
  | some o =>
    have hacc := hpre.access j (List.mem_range.2 (lt_of_getElem? hz₀))
    unfold EndUseAccessOK OptP at hacc; rw [hz₀] at hacc
    rcases hacc za (by rw [hzo]; simp) ⟨l, hlz, .inr ⟨hleaf, hl₀, hl₁⟩⟩ with e | e
    · exact hnh e
    · exact e hlive
  | none =>
    obtain ⟨-, -, r, -, -, -, hr, hlr, -⟩ := hw.rootChain j z l hz₀ hlz hleaf
    obtain ⟨pr, hpr, hh⟩ := rootHeldConv_active hw h1 hnd j z l r hz₀ za hzo hlz hr hlr
    have hnown : ¬ OwnedIn s.P p r := fun hown => by
      cases hown with
      | @direct _ o _ hpl ho hpart =>
        have e : pr.owner = .place o := by rw [hpr] at hpl; cases hpl; exact ho
        rw [hh, e] at hnh; exact hnh hpart
      | @step _ o _ hpl ho hown' =>
        have e : pr.owner = .place o := by rw [hpr] at hpl; cases hpl; exact ho
        rw [hh, e] at hlive
        have := dead_false hlive
        simp only [endUseS, Bool.or_eq_false_iff, decide_eq_false_iff_not] at this
        exact this.2 hown'
    have hd : (endUseS s p).dead r = false := by
      simp only [endUseS, ← hw.deadOf hlr, dead_false hl₀, Bool.false_or,
        decide_eq_false_iff_not]
      exact hnown
    have hr₁ : (endUseS s p).Usable r := usable_of_owner hpr hd (hh ▸ hlive)
    exact hl₁ ((hU l).1 (usable_of_partOf hw' (l + 1) l r (Nat.lt_succ_self l) hlr ((hU r).2 hr₁)))

/-- `endUse` preserves the kernel invariant `KInv` (§57) (O12, §69). -/
theorem endUse_preserves {k : K} {s s' : S3} {p : Nat} (hk : KInv s)
    (h : EndUseStep k p s (.ok s')) : KInv s' := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  have hw := hk.1
  refine releases_preserve hk (endUseS_releases s p) rfl rfl rfl
    (fun q h => by simp only [endUseS, Bool.or_eq_false_iff] at h; exact h.1)
    (fun q pl r hq hp => ?_) (fun q _ x hx => ?_) (endUse_anchors hk.2.1.1.2.2.1 hpre)
    (fun r i z pr _ hur hz _ _ hpr hzh _ => ?_)
    (endUse_noDangling hw hk.2.1.2.2 hk.2.1.1.1 hpre)
  · obtain ⟨-, -, -, -, hd⟩ := hw.places q pl r hq hp
    simp only [endUseS, hd, decide_eq_decide.2 (ownedIn_parent hw hq hp)]
  · simp only [endUseS] at hx; split at hx
    · simp at hx
    · exact hx
  · have hnh : ¬ heldIn s.P p z.holder := fun hh => by
      have hd := dead_false hur
      simp only [endUseS, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hd
      rw [hzh] at hh
      cases ho : pr.owner with
      | frame f => rw [ho] at hh; exact hh
      | place o => rw [ho] at hh; exact hd.2 (.direct hpr ho hh)
    rw [endUseS_get, hz]; simp [hnh]

/-- `endUse` preserves the auxiliary `KAux` (`RootHeldConv`, §40, §49.7; O12, §69 `ok` effect:
places are unchanged and authorities are only released). -/
theorem endUse_preserves_kAux {k : K} {s s' : S3} {p : Nat} (ha : KAux s)
    (h : EndUseStep k p s (.ok s')) : KAux s' := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
  exact releases_preserve_kAux ha (endUseS_releases s p) rfl

/-- `endUse` keeps the anchors of every usable place that is not a part of the ended value, and
they are valid (§69 `ok` effect, §52), under `KInv` (§57). -/
theorem endUse_keeps_dependents {k : K} {s s' : S3} {p : Nat} (hk : KInv s)
    (h : EndUseStep k p s (.ok s')) :
    ∀ q, s'.Usable q → ¬ partOf s.P q p → s'.D q = s.D q ∧ ∀ x ∈ s'.D q, s'.Active x := by
  have hi3 := (endUse_preserves hk h).2.1.1.2.2.1
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
  intro q hq hnp
  exact ⟨by simp [endUseEff, cleanup, endUseS, hnp], hi3 q hq⟩

/-- After `endUse p` the place `p` remains usable (§69 `ok` effect), under `KInv` (§57). -/
theorem endUse_place_usable {k : K} {s s' : S3} {p : Nat} (hk : KInv s)
    (h : EndUseStep k p s (.ok s')) : s'.Usable p := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  have hw := hk.1
  have hp := hpre.usable
  refine (cleanup_usable _ p).2 ?_
  suffices ∀ q, s.Usable q → (q = p ∨ Above s.P p q) → (endUseS s p).Usable q from
    this p hp (.inl rfl)
  intro q hq
  induction hq with
  | frame hpl hd ho hf =>
    intro hc
    have hn := not_ownedIn_chain hw hp hc
    exact .frame hpl (by simp [endUseS, hd, hn]) ho hf
  | place hpl hd ho _ ih =>
    intro hc
    have hn := not_ownedIn_chain hw hp hc
    refine .place hpl (by simp [endUseS, hd, hn]) ho (ih ?_)
    rcases hc with rfl | hc
    · exact .inr (.owner hpl ho)
    · exact .inr (hc.trans (.owner hpl ho))

/-- After `endUse p` the leaves of `p` are `Uninit` (§69 `ok` effect). -/
theorem endUse_uninit {k : K} {s s' : S3} {p : Nat} (h : EndUseStep k p s (.ok s')) :
    ∀ l ∈ footprint s.P p, s'.I l = .uninit := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
  intro l hl
  show (if l ∈ footprint s.P p then InitSt.uninit else s.I l) = .uninit
  simp only [hl, ↓reduceIte]

/-- After `endUse p` every place transitively owned by the value at `p` is marked dead and is not
usable (§69 `ok` effect). -/
theorem endUse_owned_dead {k : K} {s s' : S3} {p q : Nat} (h : EndUseStep k p s (.ok s'))
    (hq : OwnedIn s.P p q) : s'.dead q = true ∧ ¬ s'.Usable q := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
  have hd : (endUseEff s p).dead q = true := by simp [endUseEff, cleanup, endUseS, hq]
  exact ⟨hd, fun hu => by rw [dead_false hu] at hd; cases hd⟩

/-- A leaf whose use ends with the value at `p` is a place (§69). -/
theorem EndFree.endingLeaf_lt {s : S3} {p l : Nat} (h : EndingLeaf s p l) : l < s.P.length := by
  rcases h with h | ⟨-, h, -⟩
  · exact (mem_footprint.1 h).1
  · exact h.lt

/-- A leaf of usable storage transitively owned by the value at `p` ends with it (§69.4,
"including transitively owned storage"), under `WF3` (§49). -/
theorem endingLeaf_of_owned {s : S3} (hw : WF3 s) {p q l : Nat} (hq : OwnedIn s.P p q)
    (hu : s.Usable q) (hl : l ∈ footprint s.P q) : EndingLeaf s p l := by
  obtain ⟨-, hleaf, hlq⟩ := mem_footprint.1 hl
  refine .inr ⟨hleaf, usable_of_partOf hw (l + 1) l q (Nat.lt_succ_self l) hlq hu, fun hu' => ?_⟩
  obtain ⟨pl, pq, hpl, hpq, ho⟩ := hw.ownerOf hlq
  have := dead_false hu'
  simp only [endUseS, Bool.or_eq_false_iff, decide_eq_false_iff_not] at this
  exact this.2 (ownedIn_of_owner hpq hpl ho hq)

/-- A pinned leaf whose use ends blocks `endUse` (§69.4): statically (`K.Pinned`) or dynamically
pinned, the outcome is `reject`. -/
theorem endUse_pinned_reject {k : K} {s : S3} {p l : Nat} {o : Outcome3 S3}
    (hl : EndingLeaf s p l) (hpin : s.pin l = true ∨ k.Pinned l) (h : EndUseStep k p s o) :
    o = .reject := by
  cases h with
  | ok hpre =>
    have hn := hpre.notPinned l (List.mem_range.2 (endingLeaf_lt hl)) hl
    rcases hpin with e | e
    · rw [hn.1] at e; cases e
    · exact absurd e hn.2
  | reject _ => rfl

/-- `endUse` has one outcome (§58). -/
theorem endUse_det {k : K} {p : Nat} {s : S3} {o₁ o₂ : Outcome3 S3}
    (h₁ : EndUseStep k p s o₁) (h₂ : EndUseStep k p s o₂) : o₁ = o₂ := Guarded.det h₁ h₂

/-- The `ok` outcome of `endUse` (§58, §69): the preconditions hold and the state is the
effect. -/
theorem endUse_ok_iff {k : K} {p : Nat} {s s' : S3} :
    EndUseStep k p s (.ok s') ↔ EndUsePre k s p ∧ s' = endUseEff s p := Guarded.ok_iff

/-! ## O13 `free` (§70) -/

/-- The authorities after `freeS` (§70, `ok` effect): those covering the released unit or held
within `p` are inactive. -/
theorem EndFree.freeS_get (s : S3) (p j : Nat) : (freeS s p).A[j]? = (s.A[j]?).map fun y =>
    if (∃ l ∈ y.footprint, FreedPlace s.P p l) ∨ heldIn s.P p y.holder then
      { y with active := false } else y := by
  simp [freeS]

/-- `freeS` only releases authorities (§70, `ok` effect). -/
theorem EndFree.freeS_releases (s : S3) (p : Nat) : OnlyReleases s (freeS s p) :=
  map_releases rfl fun y => by
    by_cases h : (∃ l ∈ y.footprint, FreedPlace s.P p l) ∨ heldIn s.P p y.holder <;> simp [h]

/-- A place usable after `freeS` was usable before (§70: the effect only adds death markers). -/
theorem EndFree.freeS_usable {s : S3} {p q : Nat} (h : (freeS s p).Usable q) : s.Usable q :=
  S3.Usable.mono (s := s) (s' := freeS s p) rfl (fun _ h => h)
    (fun q h => by simp only [freeS, Bool.or_eq_false_iff] at h; exact h.1) h

/-- An active authority after `free p` (§70, `ok` effect): active before, covering no leaf of the
released unit, not held within `p`, with a holder live after `freeS`. -/
theorem EndFree.free_active {s : S3} {p j : Nat} {z : Authority}
    (hz : (freeEff s p).A[j]? = some z) (za : z.active = true) :
    s.A[j]? = some z ∧ ¬ ((∃ l ∈ z.footprint, FreedPlace s.P p l) ∨ heldIn s.P p z.holder) ∧
      HolderLive (freeS s p) z.holder := by
  obtain ⟨hz₁, hl⟩ := cleanup_active hz za
  rw [freeS_get] at hz₁
  cases hy : s.A[j]? with
  | none => rw [hy] at hz₁; cases hz₁
  | some y =>
    rw [hy] at hz₁
    by_cases hc : (∃ l ∈ y.footprint, FreedPlace s.P p l) ∨ heldIn s.P p y.holder
    · simp only [hc, Option.map_some, ↓reduceIte, Option.some.injEq] at hz₁
      subst hz₁; simp at za
    · simp only [hc, Option.map_some, ↓reduceIte, Option.some.injEq] at hz₁
      subst hz₁; exact ⟨rfl, hc, hl⟩

/-- The place released by `free` is a root place (§70.1, `OwnedRoot`). -/
theorem EndFree.rootPlace_of_ownedRoot {s : S3} {p : Nat} (h : OwnedRoot s p) : RootPlace s.P p := by
  unfold OwnedRoot OptP at h
  split at h
  · rename_i pl hpl; exact ⟨lt_of_getElem? hpl, by simp [parentOf, hpl, h.1]⟩
  · exact h.elim

/-- A part of a root place `r` is a part of `p` exactly when it is `p` or its structural parent is
a part of `p`, for `p` a root place (§40). -/
theorem EndFree.partOf_parent {P : List Place} {q r p : Nat} (hp : parentOf P q = some r)
    (hlt : r < q) (hr : r < P.length) (hroot : parentOf P p = none) :
    partOf P q p ↔ partOf P r p := by
  have hq : q < P.length := by
    simp only [parentOf] at hp
    cases h : P[q]? with
    | none => rw [h] at hp; cases hp
    | some _ => exact lt_of_getElem? h
  simp only [partOf, hq, hr, true_and]
  rw [chain_cons hp hlt]
  constructor
  · rintro (rfl | h)
    · rw [hroot] at hp; cases hp
    · rcases List.mem_cons.1 h with rfl | h
      · exact .inl rfl
      · exact .inr h
  · rintro (rfl | h)
    · exact .inr (List.mem_cons_self ..)
    · exact .inr (List.mem_cons_of_mem _ h)

/-- A root place that is a part of `p` is `p` (§40). -/
theorem EndFree.eq_of_partOf_root {P : List Place} {r p : Nat} (hr : RootPlace P r)
    (h : partOf P r p) : r = p := by
  obtain ⟨-, e | hc⟩ := h
  · exact e
  · rw [chain_none hr.2] at hc; simp at hc

/-- Under `FreePre` (§70.3) and `I3` (§52), every anchor of a place usable after `freeS` stays
active after `free`. -/
theorem EndFree.free_anchors {k : K} {s : S3} {p auth : Nat} (h3 : I3 s) (hpre : FreePre k s p auth) :
    ∀ q, (freeS s p).Usable q → ∀ x ∈ (freeS s p).D q, (freeEff s p).Active x := by
  intro q hq x hx
  have hq₀ := freeS_usable hq
  obtain ⟨y, hy, ya⟩ := h3 q hq₀ x hx
  have hc := hpre.anchors q (List.mem_range.2 hq₀.lt) hq x hx
  unfold FreeAnchorOK OptP at hc; rw [hy] at hc
  obtain ⟨hcov, hnh, hl⟩ := hc
  have hn : ¬ ((∃ l ∈ y.footprint, FreedPlace s.P p l) ∨ heldIn s.P p y.holder) :=
    fun h => h.elim hcov hnh
  exact ⟨y, by rw [freeEff, cleanup_get, freeS_get, hy]; simp only [Option.map_some, hn,
    ↓reduceIte, hl], ya⟩

/-- After `free p`, no active authority covers a leaf of the released unit, and every active
authority has a live holder (§70 `ok` effect, §54). -/
theorem free_no_dangling {k : K} {s s' : S3} {p auth : Nat} (h : FreeStep k p auth s (.ok s')) :
    ∀ (j : Nat) (y : Authority), s'.A[j]? = some y → y.active = true →
      (∀ l ∈ y.footprint, ¬ FreedPlace s.P p l) ∧ HolderLive s' y.holder := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
  intro j y hy ya
  obtain ⟨-, hc, hl⟩ := free_active hy ya
  exact ⟨fun l hl' hf => hc (.inl ⟨l, hl', hf⟩),
    (HolderLive.congr (s := freeS s p) (s' := freeEff s p) rfl rfl rfl _).2 hl⟩

/-- `free` preserves `NoDangling` (§54, §70), under `WF3` (§49) and `I1` (§50): an active
authority on a leaf of a place that stops being usable is derived, and blocked by §70.3, or a
root, held by the owner of the root place of the leaf (`rootHeldConv_active`), which would stay
usable. -/
theorem EndFree.free_noDangling {k : K} {s : S3} {p auth : Nat} (hw : WF3 s) (hnd : NoDangling s)
    (h1 : I1 s) (hpre : FreePre k s p auth) (hw' : WF3 (freeEff s p)) :
    NoDangling (freeEff s p) := by
  have hU := cleanup_usable (freeS s p)
  intro j z hz za q hq l hl hlz
  obtain ⟨hz₀, hnc, hlive⟩ := free_active hz za
  by_cases hq₀ : ¬ s.Usable q
  · exact hnd j z hz₀ za q hq₀ l hl hlz
  replace hq₀ := Decidable.of_not_not hq₀
  obtain ⟨-, hleaf, hlq⟩ := mem_footprint.1 hl
  have hl₀ : s.Usable l := usable_of_partOf hw (l + 1) l q (Nat.lt_succ_self l) hlq hq₀
  have hl₁ : ¬ (freeS s p).Usable l := fun hu => hq (usable_of_part hw' hlq ((hU l).2 hu))
  cases hzo : z.origin with
  | some o =>
    have hacc := hpre.access j (List.mem_range.2 (lt_of_getElem? hz₀))
    unfold FreeAccessOK OptP at hacc; rw [hz₀] at hacc
    rcases hacc za (by rw [hzo]; simp) ⟨l, hlz, .inr ⟨hleaf, hl₀, hl₁⟩⟩ with e | e
    · exact hnc (.inr e)
    · exact e hlive
  | none =>
    obtain ⟨-, -, r, -, -, -, hr, hlr, -⟩ := hw.rootChain j z l hz₀ hlz hleaf
    obtain ⟨pr, hpr, hh⟩ := rootHeldConv_active hw h1 hnd j z l r hz₀ za hzo hlz hr hlr
    have hnf : ¬ FreedPlace s.P p r := by
      rintro (hrp | hown)
      · obtain rfl := eq_of_partOf_root hr hrp
        exact hnc (.inl ⟨l, hlz, .inl hlr⟩)
      · cases hown with
        | @direct _ o _ hpl ho hpart =>
          have e : pr.owner = .place o := by rw [hpr] at hpl; cases hpl; exact ho
          rw [hh, e] at hnc; exact hnc (.inr hpart)
        | @step _ o _ hpl ho hown' =>
          have e : pr.owner = .place o := by rw [hpr] at hpl; cases hpl; exact ho
          rw [hh, e] at hlive
          have := dead_false hlive
          simp only [freeS, Bool.or_eq_false_iff, decide_eq_false_iff_not] at this
          exact this.2 (.inr hown')
    have hd : (freeS s p).dead r = false := by
      simp only [freeS, ← hw.deadOf hlr, dead_false hl₀, Bool.false_or, decide_eq_false_iff_not]
      exact hnf
    have hr₁ : (freeS s p).Usable r := usable_of_owner hpr hd (hh ▸ hlive)
    exact hl₁ ((hU l).1 (usable_of_partOf hw' (l + 1) l r (Nat.lt_succ_self l) hlr ((hU r).2 hr₁)))

/-- `free` preserves the kernel invariant `KInv` (§57) (O13, §70). -/
theorem free_preserves {k : K} {s s' : S3} {p auth : Nat} (hk : KInv s)
    (h : FreeStep k p auth s (.ok s')) : KInv s' := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  have hw := hk.1
  have hroot := rootPlace_of_ownedRoot hpre.ownedRoot
  refine releases_preserve hk (freeS_releases s p) rfl rfl rfl
    (fun q h => by simp only [freeS, Bool.or_eq_false_iff] at h; exact h.1)
    (fun q pl r hq hp => ?_) (fun q _ x hx => hx) (free_anchors hk.2.1.1.2.2.1 hpre)
    (fun r i z pr hrp hur hz _ _ hpr hzh hzf => ?_)
    (free_noDangling hw hk.2.1.2.2 hk.2.1.1.1 hpre)
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

/-- `free` preserves the auxiliary `KAux` (`RootHeldConv`, §40, §49.7; O13, §70 `ok` effect:
places are unchanged and authorities are only released). -/
theorem free_preserves_kAux {k : K} {s s' : S3} {p auth : Nat} (ha : KAux s)
    (h : FreeStep k p auth s (.ok s')) : KAux s' := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
  exact releases_preserve_kAux ha (freeS_releases s p) rfl

/-- After `free p` every place of the released unit, `p`, its parts and the storage it owns
transitively, is marked dead and is not usable (§70 `ok` effect). -/
theorem free_unit_dead {k : K} {s s' : S3} {p auth q : Nat} (h : FreeStep k p auth s (.ok s'))
    (hq : FreedPlace s.P p q) : s'.dead q = true ∧ ¬ s'.Usable q := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
  have hd : (freeEff s p).dead q = true := by simp [freeEff, cleanup, freeS, hq]
  exact ⟨hd, fun hu => by rw [dead_false hu] at hd; cases hd⟩

/-- A leaf of the released unit is a place (§70). -/
theorem EndFree.freedLeaf_lt {s : S3} {p l : Nat} (h : FreedLeaf s p l) : l < s.P.length := by
  rcases h with h | ⟨-, h, -⟩
  · exact (mem_footprint.1 h).1
  · exact h.lt

/-- A leaf of a usable place of the released unit, a part of `p` or storage it owns
transitively, belongs to the released unit (§70.4), under `WF3` (§49). -/
theorem freedLeaf_of_unit {s : S3} (hw : WF3 s) {p q l : Nat} (hq : FreedPlace s.P p q)
    (hu : s.Usable q) (hl : l ∈ footprint s.P q) : FreedLeaf s p l := by
  rcases hq with hq | hq
  · exact .inl (footprint_sub hw hq hl)
  obtain ⟨-, hleaf, hlq⟩ := mem_footprint.1 hl
  refine .inr ⟨hleaf, usable_of_partOf hw (l + 1) l q (Nat.lt_succ_self l) hlq hu, fun hu' => ?_⟩
  obtain ⟨pl, pq, hpl, hpq, ho⟩ := hw.ownerOf hlq
  have := dead_false hu'
  simp only [freeS, Bool.or_eq_false_iff, decide_eq_false_iff_not] at this
  exact this.2 (.inr (ownedIn_of_owner hpq hpl ho hq))

/-- A pinned leaf of the released unit blocks `free` (§70.4): statically (`K.Pinned`) or
dynamically pinned, the outcome is `reject`. -/
theorem free_pinned_reject {k : K} {s : S3} {p auth l : Nat} {o : Outcome3 S3}
    (hl : FreedLeaf s p l) (hpin : s.pin l = true ∨ k.Pinned l) (h : FreeStep k p auth s o) :
    o = .reject := by
  cases h with
  | ok hpre =>
    have hn := hpre.notPinned l (List.mem_range.2 (freedLeaf_lt hl)) hl
    rcases hpin with e | e
    · rw [hn.1] at e; cases e
    · exact absurd e hn.2
  | reject _ => rfl

/-- `free` has one outcome (§58). -/
theorem free_det {k : K} {p auth : Nat} {s : S3} {o₁ o₂ : Outcome3 S3}
    (h₁ : FreeStep k p auth s o₁) (h₂ : FreeStep k p auth s o₂) : o₁ = o₂ := Guarded.det h₁ h₂

/-- The `ok` outcome of `free` (§58, §70): the preconditions hold and the state is the
effect. -/
theorem free_ok_iff {k : K} {p auth : Nat} {s s' : S3} :
    FreeStep k p auth s (.ok s') ↔ FreePre k s p auth ∧ s' = freeEff s p := Guarded.ok_iff

end Ern.MemoryModel.Access
