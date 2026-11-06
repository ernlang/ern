import Ern.MemoryModel.Access.Main

/-!
# Renaming of identities: core definitions

Foundation of the renaming bisimulation of the access kernel for
`specs/ERN_Memory_Model_Specification_v0.1.md` §49, last paragraph: renamings of place and
authority identities (`Ren`), the relation they induce on places, authorities, pinning
obligations (§74, §75) and states (§38), the order facts carried along runs (`Down`, `SibMono`),
the renamed contract (§48, §80), the renamed operations (§60–§75), and the relation of outcomes
(§58). Generic lemmas on these relations, closed by symmetry.
-/

namespace Ern.MemoryModel.Access

namespace Rename

/-! ## Renamings (§49, last paragraph) -/

/-- A renaming of identities (§49, last paragraph): a bijection of `Nat` with its inverse. -/
structure Ren where
  f : Nat → Nat
  g : Nat → Nat
  gf : ∀ i, g (f i) = i
  fg : ∀ i, f (g i) = i

/-- The identity renaming (§49, last paragraph). -/
def Ren.id : Ren := ⟨fun i => i, fun i => i, fun _ => rfl, fun _ => rfl⟩

/-- The inverse renaming (§49, last paragraph). -/
def Ren.symm (π : Ren) : Ren := ⟨π.g, π.f, π.fg, π.gf⟩

/-- Composition of renamings, `π` first (§49, last paragraph). -/
def Ren.comp (π' π : Ren) : Ren :=
  ⟨fun i => π'.f (π.f i), fun i => π.g (π'.g i), fun i => by simp [π'.gf, π.gf],
   fun i => by simp [π'.fg, π.fg]⟩

/-- Renaming of a permutation `τ` of `List.range n` (§49, last paragraph): old `x < n` goes to its
position in `τ`, new `i < n` comes from `τ[i]`; identity from `n` on. -/
def Ren.ofPerm (τ : List Nat) (n : Nat) (h : τ.Perm (List.range n)) : Ren where
  f x := if x < n then τ.idxOf x else x
  g i := if hi : i < τ.length then τ[i] else i
  gf x := by
    have hl : τ.length = n := by simpa using h.length_eq
    by_cases hx : x < n
    · have hm : x ∈ τ := h.mem_iff.2 (List.mem_range.2 hx)
      have hi := List.idxOf_lt_length_of_mem hm
      simp [hx, hi, List.getElem_idxOf hi]
    · simp [hx, hl]
  fg i := by
    have hl : τ.length = n := by simpa using h.length_eq
    have hnd : τ.Nodup := h.nodup_iff.2 List.nodup_range
    by_cases hi : i < τ.length
    · have hlt : τ[i] < n := List.mem_range.1 (h.mem_iff.1 (List.getElem_mem hi))
      simp only [hi, dite_true, hlt, ite_true]
      exact (List.Nodup.getElem_inj hnd).1
        (List.getElem_idxOf (List.idxOf_lt_length_of_mem (List.getElem_mem hi)))
    · simp [hi, hl ▸ hi]

/-- The inverse of `π` maps forward by `π.g` (§49, last paragraph). -/
@[simp] theorem Ren.symm_f (π : Ren) (i : Nat) : π.symm.f i = π.g i := rfl

/-- The inverse of `π` maps backward by `π.f` (§49, last paragraph). -/
@[simp] theorem Ren.symm_g (π : Ren) (i : Nat) : π.symm.g i = π.f i := rfl

/-- The inverse of the inverse is the renaming (§49, last paragraph). -/
theorem Ren.symm_symm (π : Ren) : π.symm.symm = π := rfl

/-- A renaming is injective (§49, last paragraph). -/
theorem Ren.f_inj (π : Ren) {i j : Nat} : π.f i = π.f j ↔ i = j :=
  ⟨fun h => by rw [← π.gf i, h, π.gf], fun h => h ▸ rfl⟩

/-- A renaming is determined by its forward map (§49, last paragraph). -/
theorem Ren.ext {π π' : Ren} (h : ∀ i, π.f i = π'.f i) : π = π' := by
  have hg : ∀ i, π.g i = π'.g i := fun i =>
    calc π.g i = π.g (π.f (π'.g i)) := by rw [h, π'.fg]
      _ = π'.g i := π.gf _
  obtain ⟨f, g, _, _⟩ := π
  obtain ⟨f', g', _, _⟩ := π'
  simp only [Ren.mk.injEq]
  exact ⟨funext h, funext hg⟩

/-- A renaming composed with its inverse is the identity (§49, last paragraph). -/
theorem Ren.symm_comp (π : Ren) : π.symm.comp π = Ren.id := Ren.ext fun i => π.gf i

/-- Mapping by `π.f` then `π.g` is the identity on lists (§49, last paragraph). -/
theorem Ren.map_gf (π : Ren) (l : List Nat) : (l.map π.f).map π.g = l := by
  simp [List.map_map, Function.comp_def, π.gf]

/-- Mapping by `π.g` then `π.f` is the identity on lists (§49, last paragraph). -/
theorem Ren.map_fg (π : Ren) (l : List Nat) : (l.map π.g).map π.f = l := by
  simp [List.map_map, Function.comp_def, π.fg]

/-- Membership in a renamed list, read backward (§49, last paragraph). -/
theorem Ren.mem_map (π : Ren) (l : List Nat) (y : Nat) : y ∈ l.map π.f ↔ π.g y ∈ l := by
  constructor
  · intro hy; obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy; rwa [π.gf]
  · intro hy; exact List.mem_map.2 ⟨π.g y, hy, π.fg y⟩

/-- Membership of a renamed identity in a renamed list (§49, last paragraph). -/
theorem Ren.mem_map_f (π : Ren) (l : List Nat) (x : Nat) : π.f x ∈ l.map π.f ↔ x ∈ l := by
  rw [π.mem_map, π.gf]

/-- The f-form of a membership correspondence gives its g-form (§49, last paragraph). -/
theorem Ren.mem_iff_g (π : Ren) {L L' : List Nat} (h : ∀ x, π.f x ∈ L' ↔ x ∈ L) (y : Nat) :
    y ∈ L' ↔ π.g y ∈ L := by rw [← h, π.fg]

/-- Universal quantification over all identities, renamed (§49, last paragraph). -/
theorem Ren.forall_iff (π : Ren) {Q Q' : Nat → Prop} (hQ : ∀ x, Q' (π.f x) ↔ Q x) :
    (∀ y, Q' y) ↔ ∀ x, Q x :=
  ⟨fun h x => (hQ x).1 (h _), fun h y => by rw [← π.fg y]; exact (hQ _).2 (h _)⟩

/-- Universal quantification over corresponding lists (§49, last paragraph). -/
theorem Ren.forall_mem_iff (π : Ren) {L L' : List Nat} (hL : ∀ x, π.f x ∈ L' ↔ x ∈ L)
    {Q Q' : Nat → Prop} (hQ : ∀ x, Q' (π.f x) ↔ Q x) :
    (∀ y ∈ L', Q' y) ↔ ∀ x ∈ L, Q x :=
  ⟨fun h x hx => (hQ x).1 (h _ ((hL x).2 hx)),
   fun h y hy => by
    rw [← π.fg y] at hy ⊢; exact (hQ _).2 (h _ ((hL _).1 hy))⟩

/-- Existential quantification over corresponding lists (§49, last paragraph). -/
theorem Ren.exists_mem_iff (π : Ren) {L L' : List Nat} (hL : ∀ x, π.f x ∈ L' ↔ x ∈ L)
    {Q Q' : Nat → Prop} (hQ : ∀ x, Q' (π.f x) ↔ Q x) :
    (∃ y ∈ L', Q' y) ↔ ∃ x ∈ L, Q x :=
  ⟨fun ⟨y, hy, hq⟩ => by
    rw [← π.fg y] at hy hq; exact ⟨_, (hL _).1 hy, (hQ _).1 hq⟩,
   fun ⟨x, hx, hq⟩ => ⟨_, (hL x).2 hx, (hQ x).2 hq⟩⟩

/-- Duplicate-free lists with corresponding members are permutations up to renaming (§42: sets
represented by lists; §49, last paragraph). -/
theorem Ren.perm_of_mem (π : Ren) {L L' : List Nat} (hnd : L.Nodup) (hnd' : L'.Nodup)
    (h : ∀ x, π.f x ∈ L' ↔ x ∈ L) : L'.Perm (L.map π.f) := by
  have hm : (L.map π.f).Nodup :=
    List.pairwise_map.2 (hnd.imp fun hab e => hab ((Ren.f_inj π).1 e))
  refine (List.perm_ext_iff_of_nodup hnd' hm).2 fun y => ?_
  rw [π.mem_iff_g h, π.mem_map]

/-! ## Generic list and option lemmas -/

/-- A duplicate-free list of `n` identities below `n` is a permutation of `List.range n` (§49,
last paragraph). -/
theorem perm_range_of_nodup {l : List Nat} {n : Nat} (hnd : l.Nodup) (hlt : ∀ a ∈ l, a < n)
    (hlen : l.length = n) : l.Perm (List.range n) := by
  refine (List.perm_ext_iff_of_nodup hnd List.nodup_range).2 fun a =>
    ⟨fun ha => List.mem_range.2 (hlt a ha), fun ha => ?_⟩
  refine Classical.byContradiction fun hna => ?_
  have hsub : l ⊆ (List.range n).erase a := fun b hb =>
    (List.mem_erase_of_ne (fun e => hna (by subst e; exact hb))).2 (List.mem_range.2 (hlt b hb))
  have := List.Nodup.length_le_of_subset hnd hsub
  rw [List.length_erase_of_mem ha, List.length_range] at this
  have : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) (List.mem_range.1 ha)
  omega

/-- `flatMap` of pointwise permutations is a permutation (§44: `D(p)` is a set; §49, last
paragraph). -/
theorem perm_flatMap_pointwise {α β : Type} {f g : α → List β} :
    ∀ {l : List α}, (∀ a ∈ l, (f a).Perm (g a)) → (l.flatMap f).Perm (l.flatMap g)
  | [], _ => .nil
  | a :: l, h => by
    simp only [List.flatMap_cons]
    exact (h a (List.mem_cons_self ..)).append
      (perm_flatMap_pointwise fun b hb => h b (List.mem_cons_of_mem _ hb))

/-- Positions are kept by an injective map (§63.2; §49, last paragraph). -/
theorem posIn_map {f : Nat → Nat} (hf : ∀ i j, f i = f j → i = j) (r : Nat) :
    ∀ l : List Nat, posIn (f r) (l.map f) = posIn r l
  | [] => rfl
  | a :: l => by
    simp only [List.map_cons, posIn, posIn_map hf r l]
    by_cases h : a = r
    · subst h; simp
    · have : f a ≠ f r := fun e => h (hf _ _ e)
      simp [h, this]

/-- Two strictly sorted lists with the same members are equal (§63.2: children in index order;
§49, last paragraph). -/
theorem eq_of_sorted_mem {l l' : List Nat} (h : l.Pairwise (· < ·)) (h' : l'.Pairwise (· < ·))
    (hm : ∀ a, a ∈ l ↔ a ∈ l') : l = l' :=
  List.Perm.eq_of_pairwise (le := (· < ·))
    (fun _ _ _ _ hab hba => absurd (Nat.lt_trans hab hba) (Nat.lt_irrefl _)) h h'
    ((List.perm_ext_iff_of_nodup (h.imp Nat.ne_of_lt) (h'.imp Nat.ne_of_lt)).2 hm)

/-- A related `some` has a related `some` (§38: components read by index; §49, last
paragraph). -/
theorem optionRel_some {α β : Type} {r : α → β → Prop} {o : Option α} {o' : Option β} {a : α}
    (h : Option.Rel r o o') (ha : o = some a) : ∃ b, o' = some b ∧ r a b := by
  subst ha; cases h with | some h => exact ⟨_, rfl, h⟩

/-- A related `some`, read backward (§38; §49, last paragraph). -/
theorem optionRel_some' {α β : Type} {r : α → β → Prop} {o : Option α} {o' : Option β} {b : β}
    (h : Option.Rel r o o') (hb : o' = some b) : ∃ a, o = some a ∧ r a b := by
  subst hb; cases h with | some h => exact ⟨_, rfl, h⟩

/-- Related options are `none` together (§38; §49, last paragraph). -/
theorem optionRel_none_iff {α β : Type} {r : α → β → Prop} {o : Option α} {o' : Option β}
    (h : Option.Rel r o o') : o = none ↔ o' = none := by
  cases h <;> simp

/-- Symmetry of `Option.Rel` (§38; §49, last paragraph). -/
theorem optionRel_symm {α β : Type} {r : α → β → Prop} {r' : β → α → Prop}
    (hr : ∀ a b, r a b → r' b a) : ∀ {o o'}, Option.Rel r o o' → Option.Rel r' o' o
  | _, _, .some h => .some (hr _ _ h)
  | _, _, .none => .none

/-- Transitivity of `Option.Rel` (§38; §49, last paragraph). -/
theorem optionRel_trans {α β γ : Type} {r : α → β → Prop} {r' : β → γ → Prop}
    {r'' : α → γ → Prop} (hr : ∀ a b c, r a b → r' b c → r'' a c) :
    ∀ {o o' o''}, Option.Rel r o o' → Option.Rel r' o' o'' → Option.Rel r'' o o''
  | _, _, _, .some h, .some h' => .some (hr _ _ _ h h')
  | _, _, _, .none, .none => .none

end Rename

open Rename

/-! ## Renamed holders and places (§40, §42) -/

/-- A holder renamed (§40, §42; §49, last paragraph): frames are not renamed. -/
def Holder.ren (π : Ren) : Holder → Holder
  | .frame f => .frame f
  | .place p => .place (π.f p)

/-- A place renamed (§40; §49, last paragraph): parent and owner renamed, `kind` kept. -/
def Place.ren (π : Ren) (pl : Place) : Place := ⟨pl.parent.map π.f, pl.owner.ren π, pl.kind⟩

namespace Rename

/-- Renaming a holder back (§40, §42; §49, last paragraph). -/
theorem Holder.ren_symm (π : Ren) (h : Holder) : (h.ren π).ren π.symm = h := by
  cases h <;> simp [Holder.ren, π.gf]

/-- Renaming holders is injective (§40, §42; §49, last paragraph). -/
theorem Holder.ren_inj (π : Ren) {a b : Holder} : a.ren π = b.ren π ↔ a = b :=
  ⟨fun h => by rw [← Holder.ren_symm π a, h, Holder.ren_symm], fun h => h ▸ rfl⟩

/-- Renaming holders twice is renaming by the composition (§40, §42; §49, last paragraph). -/
theorem Holder.ren_comp (π π' : Ren) (h : Holder) : (h.ren π).ren π' = h.ren (π'.comp π) := by
  cases h <;> rfl

/-- A renamed holder is a place exactly when the holder is (§70.1; §49, last paragraph). -/
theorem Holder.isPlace_ren (π : Ren) (h : Holder) : (h.ren π).isPlace = h.isPlace := by
  cases h <;> rfl

/-- Renaming a place back (§40; §49, last paragraph). -/
theorem Place.ren_symm (π : Ren) (pl : Place) : (pl.ren π).ren π.symm = pl := by
  obtain ⟨p, o, k⟩ := pl
  simp only [Place.ren, Holder.ren_symm, Option.map_map]
  cases p <;> simp [π.gf]

/-- Renaming places twice is renaming by the composition (§40; §49, last paragraph). -/
theorem Place.ren_comp (π π' : Ren) (pl : Place) : (pl.ren π).ren π' = pl.ren (π'.comp π) := by
  obtain ⟨p, o, k⟩ := pl
  simp only [Place.ren, Holder.ren_comp, Option.map_map]
  rfl

/-! ## Related authorities, obligations, places and states (§38, §40, §42, §74, §75) -/

/-- Authorities related by the renaming (§42; §49, last paragraph); footprints up to permutation
(§42: a set). -/
structure AuthRel (π α : Ren) (y y' : Authority) : Prop where
  mode : y'.mode = y.mode
  origin : y'.origin = y.origin.map α.f
  footprint : y'.footprint.Perm (y.footprint.map π.f)
  holder : y'.holder = y.holder.ren π
  active : y'.active = y.active

/-- Pinning obligations related by the renaming (§74, §75; §49, last paragraph); identities
kept, leaves up to permutation. -/
structure PinRel (π : Ren) (ob ob' : PinOb) : Prop where
  place : ob'.place = π.f ob.place
  leaves : ob'.leaves.Perm (ob.leaves.map π.f)
  active : ob'.active = ob.active

/-- Place lists related by the renaming (§40; §49, last paragraph); fresh identities fixed. -/
structure PRel (π : Ren) (P P' : List Place) : Prop where
  len : P'.length = P.length
  get : ∀ q, P'[π.f q]? = (P[q]?).map (Place.ren π)
  fix : ∀ q, P.length ≤ q → π.f q = q

/-- States related by place renaming `π` and authority renaming `α` (§38; §49, last paragraph);
footprints, anchors (§44: a set) and pinned leaves up to permutation. -/
structure SRel (π α : Ren) (s s' : S3) : Prop where
  F : s'.F = s.F
  nF : s'.nF = s.nF
  P : PRel π s.P s'.P
  I : ∀ l, s'.I (π.f l) = s.I l
  Alen : s'.A.length = s.A.length
  A : ∀ x, Option.Rel (AuthRel π α) (s.A[x]?) (s'.A[α.f x]?)
  Afix : ∀ x, s.A.length ≤ x → α.f x = x
  D : ∀ q, (s'.D (π.f q)).Perm ((s.D q).map α.f)
  dead : ∀ q, s'.dead (π.f q) = s.dead q
  pins : ∀ o : Nat, Option.Rel (PinRel π) (s.pins[o]?) (s'.pins[o]?)

/-- Parent links go to smaller identities (§49.2; representation of acyclicity, §49 last
paragraph). -/
def DownP (P : List Place) : Prop := ∀ j o, parentOf P j = some o → o < j

/-- Origin links go to smaller identities (§49.5; representation of acyclicity, §49 last
paragraph). -/
def DownA (s : S3) : Prop := ∀ j o, s.org j = some o → o < j

/-- Parent and origin links go to smaller identities (§49.2, §49.5; §49, last paragraph). -/
def Down (s : S3) : Prop := DownP s.P ∧ DownA s

/-- `π` keeps the order of the parts of every place, their positional field order (§63.2; §49,
last paragraph). -/
def SibMono (π : Ren) (P : List Place) : Prop :=
  ∀ x y p, parentOf P x = some p → parentOf P y = some p → x < y → π.f x < π.f y

/-- The simulation invariant (§49, last paragraph; §57): related states, both with downward
links, and `π` keeping field order (§63.2). -/
structure Sim (π α : Ren) (s s' : S3) : Prop where
  rel : SRel π α s s'
  down : Down s
  down' : Down s'
  sib : SibMono π s.P

/-- Interface obligation on the contract `K`, attached to §42 (the `footprint` of an authority is a
set; likewise the anchors `D(p)`, §44, and the leaves of a pinning obligation, §74): `Satisfiable`
(§71) does not distinguish states equal up to permutation of footprint, anchor and pin-leaf lists,
which the formalization represents as lists (§49, last paragraph). `K` is a parameter of the
formalization (§48, §80), not a concrete definition, so this is a hypothesis on it (accepted by the
owner on 2026-11-06), satisfied for instance by `Examples.K0` (`MainExamples.k0_ext`). Only the
renaming bisimulation depends on it: `satisfiable_ren` and `alloc_corr` (OpsEndFree), then
`op_corr`, `Sim.step`, `Sim.step_back`, `Sim.run`, `Sim.run_back`, `Sim.run_back_any`,
`Renumbered.run`, `Renumbered.run_back`, `Renumbered.reachable`, `Renumbered.reachable_back` and
`Renumbered.properties` (Main). -/
def KExt (k : K) : Prop :=
  ∀ p sh s t, SRel Ren.id Ren.id s t → k.Satisfiable p sh s → k.Satisfiable p sh t

end Rename

/-! ## Renamed contract and operations (§48, §60–§75, §80) -/

/-- The contract renamed (§48, §80; §49, last paragraph). `FreeCompat`'s `auth` is opaque
(§70.2); obligations keep their identities (§75); `Satisfiable` (§71) is read on related
states. -/
def K.rename (π α : Ren) (k : K) : K where
  DeclaredDisjoint r r' := k.DeclaredDisjoint (r.map π.g) (r'.map π.g)
  SharedMutable l := k.SharedMutable (π.g l)
  Pinned l := k.Pinned (π.g l)
  ExternalDone o := k.ExternalDone o
  Deallocable p := k.Deallocable (π.g p)
  FreeCompat p a := k.FreeCompat (π.g p) a
  Satisfiable p sh t := ∃ t₀, SRel π α t₀ t ∧ k.Satisfiable (π.g p) sh t₀

/-- Arguments renamed (§60–§75; §49, last paragraph). Shapes are not renamed (§71.1, §72.2:
fresh parents); `auth` is opaque (§70.2); `o` is an obligation identity (§75). -/
def KernelOp.ren (π α : Ren) : KernelOp → KernelOp
  | .derive src region m => .derive (α.f src) (region.map π.f) m
  | .split src rs => .split (α.f src) (rs.map (·.map π.f))
  | .release a => .release (α.f a)
  | .transfer src dst => .transfer (π.f src) (π.f dst)
  | .depend q x => .depend (π.f q) (α.f x)
  | .enter ps ls => .enter (ps.map α.f) ls
  | .exit => .exit
  | .read a ls => .read (α.f a) (ls.map π.f)
  | .write a ls => .write (α.f a) (ls.map π.f)
  | .writeShared a ls => .writeShared (α.f a) (ls.map π.f)
  | .pin p => .pin (π.f p)
  | .unpin o => .unpin o
  | .endUse p => .endUse (π.f p)
  | .free p auth => .free (π.f p) auth
  | .alloc pr ow ls => .alloc (π.f pr) (π.f ow) ls
  | .store a p => .store (α.f a) (π.f p)

namespace Rename

/-- Contracts corresponding under the renaming, `Satisfiable` excepted (§48, §80; §49, last
paragraph). -/
structure KCorr (π α : Ren) (k k' : K) : Prop where
  dd : ∀ r r', k'.DeclaredDisjoint (r.map π.f) (r'.map π.f) ↔ k.DeclaredDisjoint r r'
  shared : ∀ l, k'.SharedMutable (π.f l) ↔ k.SharedMutable l
  pinned : ∀ l, k'.Pinned (π.f l) ↔ k.Pinned l
  done : ∀ o, k'.ExternalDone o ↔ k.ExternalDone o
  dealloc : ∀ p, k'.Deallocable (π.f p) ↔ k.Deallocable p
  compat : ∀ p a, k'.FreeCompat (π.f p) a ↔ k.FreeCompat p a

/-- Outcomes related by the renaming (§58; §49, last paragraph). -/
def OutRel (π α : Ren) : Outcome3 S3 → Outcome3 S3 → Prop
  | .ok t, .ok t' => SRel π α t t'
  | .reject, .reject => True
  | .fail, .fail => True
  | _, _ => False

/-- Outcome relations corresponding in both directions (§58; §49, last paragraph). -/
def StepCorr (π α : Ren) (R R' : Outcome3 S3 → Prop) : Prop :=
  (∀ o, R o → ∃ o', R' o' ∧ OutRel π α o o') ∧ ∀ o', R' o' → ∃ o, R o ∧ OutRel π α o o'

/-! ## Generic lemmas on the relations (§49, last paragraph) -/

section
variable {π π' α α' : Ren} {s s' s'' : S3} {P P' P'' : List Place}

/-- Related place lists have related bounds (§40; §49, last paragraph). -/
theorem PRel.lt_iff (hP : PRel π P P') (q : Nat) : π.f q < P'.length ↔ q < P.length := by
  have := hP.get q
  constructor
  · intro hq
    rw [List.getElem?_eq_getElem hq] at this
    cases e : P[q]? with
    | none => rw [e] at this; cases this
    | some _ => exact (List.getElem?_eq_some_iff.1 e).1
  · intro hq
    rw [List.getElem?_eq_getElem hq] at this
    cases e : P'[π.f q]? with
    | none => rw [e] at this; cases this
    | some _ => exact (List.getElem?_eq_some_iff.1 e).1

/-- Membership in the place range, renamed (§40; §49, last paragraph). -/
theorem PRel.mem_range (hP : PRel π P P') (q : Nat) :
    π.f q ∈ List.range P'.length ↔ q ∈ List.range P.length := by
  simp only [List.mem_range, hP.lt_iff]

/-- Universal quantification over the places, renamed (§40; §49, last paragraph). -/
theorem PRel.forall_range (hP : PRel π P P') {Q : Nat → Prop} :
    (∀ y ∈ List.range P'.length, Q y) ↔ ∀ x ∈ List.range P.length, Q (π.f x) :=
  π.forall_mem_iff hP.mem_range fun _ => Iff.rfl

/-- Existential quantification over the places, renamed (§40; §49, last paragraph). -/
theorem PRel.exists_range (hP : PRel π P P') {Q : Nat → Prop} :
    (∃ y ∈ List.range P'.length, Q y) ↔ ∃ x ∈ List.range P.length, Q (π.f x) :=
  π.exists_mem_iff hP.mem_range fun _ => Iff.rfl

/-- Symmetry of related place lists (§40; §49, last paragraph). -/
theorem PRel.symm (hP : PRel π P P') : PRel π.symm P' P where
  len := hP.len.symm
  get q := by
    have := hP.get (π.g q)
    rw [π.fg] at this
    rw [Ren.symm_f, this, Option.map_map]
    cases P[π.g q]? <;> simp [Function.comp_def, Place.ren_symm]
  fix q hq := by
    have := hP.fix q (hP.len ▸ hq)
    show π.g q = q
    conv => lhs; rw [← this]
    exact π.gf q

/-- Transitivity of related place lists (§40; §49, last paragraph). -/
theorem PRel.trans (hP : PRel π P P') (hP' : PRel π' P' P'') : PRel (π'.comp π) P P'' where
  len := hP'.len.trans hP.len
  get q := by
    show P''[π'.f (π.f q)]? = _
    rw [hP'.get, hP.get, Option.map_map]
    congr 1; funext pl; exact Place.ren_comp π π' pl
  fix q hq := by
    show π'.f (π.f q) = q
    rw [hP.fix q hq, hP'.fix q (hP.len ▸ hq)]

/-- Authorities related: footprint membership (§42; §49, last paragraph). -/
theorem AuthRel.mem_footprint {y y' : Authority} (hr : AuthRel π α y y') (l : Nat) :
    π.f l ∈ y'.footprint ↔ l ∈ y.footprint :=
  hr.footprint.mem_iff.trans (π.mem_map_f _ _)

/-- Symmetry of related authorities (§42; §49, last paragraph). -/
theorem AuthRel.symm {y y' : Authority} (h : AuthRel π α y y') : AuthRel π.symm α.symm y' y where
  mode := h.mode.symm
  origin := by rw [h.origin, Option.map_map]; cases y.origin <;> simp [α.gf]
  footprint := by
    have := h.footprint.map π.g
    rw [Ren.map_gf] at this; exact this.symm
  holder := by rw [h.holder, Holder.ren_symm]
  active := h.active.symm

/-- Transitivity of related authorities (§42; §49, last paragraph). -/
theorem AuthRel.trans {y y' y'' : Authority} (h : AuthRel π α y y') (h' : AuthRel π' α' y' y'') :
    AuthRel (π'.comp π) (α'.comp α) y y'' where
  mode := h'.mode.trans h.mode
  origin := by rw [h'.origin, h.origin, Option.map_map]; rfl
  footprint := h'.footprint.trans ((h.footprint.map π'.f).trans (by rw [List.map_map]; rfl))
  holder := by rw [h'.holder, h.holder, Holder.ren_comp]
  active := h'.active.trans h.active

/-- Related obligations: leaf membership (§74, §75; §49, last paragraph). -/
theorem PinRel.mem_leaves {ob ob' : PinOb} (hr : PinRel π ob ob') (l : Nat) :
    π.f l ∈ ob'.leaves ↔ l ∈ ob.leaves :=
  hr.leaves.mem_iff.trans (π.mem_map_f _ _)

/-- Symmetry of related obligations (§74, §75; §49, last paragraph). -/
theorem PinRel.symm {ob ob' : PinOb} (h : PinRel π ob ob') : PinRel π.symm ob' ob where
  place := by rw [h.place]; exact (π.gf _).symm
  leaves := by have := h.leaves.map π.g; rw [Ren.map_gf] at this; exact this.symm
  active := h.active.symm

/-- Transitivity of related obligations (§74, §75; §49, last paragraph). -/
theorem PinRel.trans {ob ob' ob'' : PinOb} (h : PinRel π ob ob') (h' : PinRel π' ob' ob'') :
    PinRel (π'.comp π) ob ob'' where
  place := by rw [h'.place, h.place]; rfl
  leaves := h'.leaves.trans ((h.leaves.map π'.f).trans (by rw [List.map_map]; rfl))
  active := h'.active.trans h.active

/-- Symmetry of related states (§38; §49, last paragraph). -/
theorem SRel.symm (h : SRel π α s s') : SRel π.symm α.symm s' s where
  F := h.F.symm
  nF := h.nF.symm
  P := h.P.symm
  I l := by have := h.I (π.g l); rw [π.fg] at this; exact this.symm
  Alen := h.Alen.symm
  A x := by
    have := optionRel_symm (fun _ _ hy => AuthRel.symm hy) (h.A (α.g x))
    rw [α.fg] at this; exact this
  Afix x hx := by
    have := h.Afix x (h.Alen ▸ hx)
    show α.g x = x
    conv => lhs; rw [← this]
    exact α.gf x
  D q := by
    have := (h.D (π.g q)).map α.g
    rw [π.fg, Ren.map_gf] at this; exact this.symm
  dead q := by have := h.dead (π.g q); rw [π.fg] at this; exact this.symm
  pins o := optionRel_symm (fun _ _ hy => PinRel.symm hy) (h.pins o)

/-- Transitivity of related states (§38; §49, last paragraph). -/
theorem SRel.trans (h : SRel π α s s') (h' : SRel π' α' s' s'') :
    SRel (π'.comp π) (α'.comp α) s s'' where
  F := h'.F.trans h.F
  nF := h'.nF.trans h.nF
  P := h.P.trans h'.P
  I l := (h'.I (π.f l)).trans (h.I l)
  Alen := h'.Alen.trans h.Alen
  A x := optionRel_trans (r := AuthRel π α) (r' := AuthRel π' α')
    (r'' := AuthRel (π'.comp π) (α'.comp α))
    (fun _ _ _ hy hy' => AuthRel.trans hy hy') (h.A x) (h'.A (α.f x))
  Afix x hx := by
    show α'.f (α.f x) = x
    rw [h.Afix x hx, h'.Afix x (h.Alen ▸ hx)]
  D q := (h'.D (π.f q)).trans (((h.D q).map α'.f).trans (by rw [List.map_map]; rfl))
  dead q := (h'.dead (π.f q)).trans (h.dead q)
  pins o := optionRel_trans (r := PinRel π) (r' := PinRel π') (r'' := PinRel (π'.comp π))
    (fun _ _ _ hy hy' => PinRel.trans hy hy') (h.pins o) (h'.pins o)

/-- Related states with the same new frame stack are related (§38, §39; §49, last
paragraph). -/
theorem SRel.withF (h : SRel π α s s') (F₀ : Frames) :
    SRel π α { s with F := F₀ } { s' with F := F₀ } :=
  { h with F := rfl }

/-- An existing authority has a related authority (§42; §49, last paragraph). -/
theorem SRel.A_some (h : SRel π α s s') {x : Nat} {y : Authority} (hy : s.A[x]? = some y) :
    ∃ y', s'.A[α.f x]? = some y' ∧ AuthRel π α y y' :=
  optionRel_some (h.A x) hy

/-- An existing renamed authority has a related authority (§42; §49, last paragraph). -/
theorem SRel.A_some' (h : SRel π α s s') {x : Nat} {y' : Authority}
    (hy : s'.A[α.f x]? = some y') : ∃ y, s.A[x]? = some y ∧ AuthRel π α y y' :=
  optionRel_some' (h.A x) hy

/-- Authorities are absent together (§42; §49, last paragraph). -/
theorem SRel.A_none (h : SRel π α s s') (x : Nat) : s.A[x]? = none ↔ s'.A[α.f x]? = none :=
  optionRel_none_iff (h.A x)

/-- An existing obligation has a related obligation (§74, §75; §49, last paragraph). -/
theorem SRel.pins_some (h : SRel π α s s') {o : Nat} {ob : PinOb} (hob : s.pins[o]? = some ob) :
    ∃ ob', s'.pins[o]? = some ob' ∧ PinRel π ob ob' :=
  optionRel_some (h.pins o) hob

/-- An existing obligation of the related state has a related obligation (§74, §75; §49, last
paragraph). -/
theorem SRel.pins_some' (h : SRel π α s s') {o : Nat} {ob' : PinOb}
    (hob : s'.pins[o]? = some ob') : ∃ ob, s.pins[o]? = some ob ∧ PinRel π ob ob' :=
  optionRel_some' (h.pins o) hob

/-- Obligations are absent together (§74, §75; §49, last paragraph). -/
theorem SRel.pins_none (h : SRel π α s s') (o : Nat) : s.pins[o]? = none ↔ s'.pins[o]? = none :=
  optionRel_none_iff (h.pins o)

/-- Related states have related authority bounds (§42; §49, last paragraph). -/
theorem SRel.Alt (h : SRel π α s s') (x : Nat) : α.f x < s'.A.length ↔ x < s.A.length := by
  have := h.A_none x
  rw [List.getElem?_eq_none_iff, List.getElem?_eq_none_iff] at this
  omega

/-- Membership in the authority range, renamed (§42; §49, last paragraph). -/
theorem SRel.mem_rangeA (h : SRel π α s s') (x : Nat) :
    α.f x ∈ List.range s'.A.length ↔ x ∈ List.range s.A.length := by
  simp only [List.mem_range, h.Alt]

/-- Universal quantification over the authorities, renamed (§42; §49, last paragraph). -/
theorem SRel.forall_rangeA (h : SRel π α s s') {Q : Nat → Prop} :
    (∀ y ∈ List.range s'.A.length, Q y) ↔ ∀ x ∈ List.range s.A.length, Q (α.f x) :=
  α.forall_mem_iff h.mem_rangeA fun _ => Iff.rfl

/-- Existential quantification over the authorities, renamed (§42; §49, last paragraph). -/
theorem SRel.exists_rangeA (h : SRel π α s s') {Q : Nat → Prop} :
    (∃ y ∈ List.range s'.A.length, Q y) ↔ ∃ x ∈ List.range s.A.length, Q (α.f x) :=
  α.exists_mem_iff h.mem_rangeA fun _ => Iff.rfl

/-- `WF3` gives downward links (§49.2, §49.5; §49, last paragraph). -/
theorem Down.of_wf3 (hw : WF3 s) : Down s := by
  refine ⟨fun _ _ hp => (hw.parent_lt hp).1, fun j o ho => ?_⟩
  obtain ⟨y, hy, hyo⟩ := Option.bind_eq_some_iff.1 ho
  exact hw.origins j y o hy hyo

/-- Field order kept by `π` is kept by its inverse on the related list (§63.2; §49, last
paragraph). -/
theorem SibMono.symm (hP : PRel π P P') (hs : SibMono π P) : SibMono π.symm P' := by
  have hpar : ∀ x p, parentOf P' x = some p → parentOf P (π.g x) = some (π.g p) := by
    intro x p hx
    have := hP.get (π.g x)
    rw [π.fg] at this
    simp only [parentOf, this] at hx ⊢
    cases e : P[π.g x]? with
    | none => rw [e] at hx; cases hx
    | some pl =>
      rw [e] at hx
      simp only [Option.map_some, Option.bind_some, Place.ren] at hx
      cases hpp : pl.parent with
      | none => rw [hpp] at hx; cases hx
      | some r =>
        rw [hpp] at hx; simp only [Option.map_some, Option.some.injEq] at hx
        simp only [Option.bind_some, hpp, ← hx, π.gf]
  intro x y p hx hy hxy
  simp only [Ren.symm_f]
  rcases Nat.lt_trichotomy (π.g x) (π.g y) with hlt | heq | hgt
  · exact hlt
  · exact absurd ((by rw [← π.fg x, heq, π.fg] : x = y) ▸ hxy) (Nat.lt_irrefl _)
  · have := hs _ _ _ (hpar y p hy) (hpar x p hx) hgt
    rw [π.fg, π.fg] at this; omega

/-- Field order depends only on the parent links (§63.2; §49, last paragraph). -/
theorem SibMono.congr {P₁ : List Place} (hpar : parentOf P₁ = parentOf P) (hs : SibMono π P) :
    SibMono π P₁ := by
  intro x y p hx hy; rw [hpar] at hx hy; exact hs x y p hx hy

/-- Symmetry of the simulation invariant (§49, last paragraph; §57). -/
theorem Sim.symm (hS : Sim π α s s') : Sim π.symm α.symm s' s where
  rel := hS.rel.symm
  down := hS.down'
  down' := hS.down
  sib := SibMono.symm hS.rel.P hS.sib

/-- The renamed contract corresponds to the contract (§48, §80; §49, last paragraph). -/
theorem KCorr.rename (π α : Ren) (k : K) : KCorr π α k (k.rename π α) where
  dd r r' := by simp only [K.rename, Ren.map_gf]
  shared l := by simp only [K.rename, π.gf]
  pinned l := by simp only [K.rename, π.gf]
  done _ := Iff.rfl
  dealloc p := by simp only [K.rename, π.gf]
  compat p a := by simp only [K.rename, π.gf]

/-- Symmetry of corresponding contracts (§48, §80; §49, last paragraph). -/
theorem KCorr.symm {k k' : K} (hK : KCorr π α k k') : KCorr π.symm α.symm k' k where
  dd r r' := by
    have := hK.dd (r.map π.g) (r'.map π.g)
    rw [Ren.map_fg, Ren.map_fg] at this; exact this.symm
  shared l := by have := hK.shared (π.g l); rw [π.fg] at this; exact this.symm
  pinned l := by have := hK.pinned (π.g l); rw [π.fg] at this; exact this.symm
  done o := (hK.done o).symm
  dealloc p := by have := hK.dealloc (π.g p); rw [π.fg] at this; exact this.symm
  compat p a := by have := hK.compat (π.g p) a; rw [π.fg] at this; exact this.symm

/-- `DDSound` (§80, §23) is invariant under renaming of the contract (§49, last paragraph). -/
theorem ddSound_rename (π α : Ren) (k : K) : DDSound (k.rename π α) ↔ DDSound k := by
  constructor
  · intro h r r' hd l hl hl'
    have hd' : (k.rename π α).DeclaredDisjoint (r.map π.f) (r'.map π.f) := by
      simp only [K.rename, Ren.map_gf]; exact hd
    exact h _ _ hd' (π.f l) ((π.mem_map_f _ _).2 hl) ((π.mem_map_f _ _).2 hl')
  · intro h r r' hd l hl hl'
    exact h _ _ hd (π.g l) (List.mem_map_of_mem hl) (List.mem_map_of_mem hl')

/-- Guarded steps with corresponding preconditions and related effects correspond (§58; §49, last
paragraph). -/
theorem guarded_corr {Pre Pre' : Prop} {e e' : S3} (hp : Pre' ↔ Pre)
    (he : Pre → SRel π α e e') : StepCorr π α (Guarded Pre e) (Guarded Pre' e') := by
  constructor
  · intro o ho
    cases ho with
    | ok hpre => exact ⟨.ok e', .ok (hp.2 hpre), he hpre⟩
    | reject hpre => exact ⟨.reject, .reject (fun h' => hpre (hp.1 h')), trivial⟩
  · intro o' ho'
    cases ho' with
    | ok hpre => exact ⟨.ok e, .ok (hp.1 hpre), he (hp.1 hpre)⟩
    | reject hpre => exact ⟨.reject, .reject (fun h => hpre (hp.2 h)), trivial⟩

end

/-- Renaming the arguments by the inverse, then by the renaming, gives the operation back (§60–§75;
§49, last paragraph). -/
theorem KernelOp.ren_symm_ren (π α : Ren) (op : KernelOp) :
    (op.ren π.symm α.symm).ren π α = op := by
  cases op <;>
    simp [KernelOp.ren, List.map_map, Function.comp_def, π.fg, α.fg]

/-- Renaming the arguments, then by the inverse, gives the operation back (§60–§75; §49, last
paragraph). -/
theorem KernelOp.symm_ren_ren (π α : Ren) (op : KernelOp) :
    (op.ren π α).ren π.symm α.symm = op :=
  KernelOp.ren_symm_ren π.symm α.symm op

end Rename

end Ern.MemoryModel.Access
