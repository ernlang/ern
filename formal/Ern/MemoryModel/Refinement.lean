import Ern.MemoryModel.Machine
import Ern.MemoryModel.Access.Preserve.Common

/-!
# Refinement of the access kernel into the elementary memory machine (spec v0, Part XVII)

Source: `specs/ERN_Memory_Model_Specification_v0.md`, §82 (items 1–8) with §10, §16, §17, §23.

* A layout of places in allocations and its interface `LayoutWF` (§82.1, §23).
* The representation relation `Repr` between a kernel state (`Access.S3`) and an admissible state
  of the memory machine (`Machine.State`, §9) (§82.1, §82.3, §82.4, §82.5).
* For every kernel operation O1–O16, the sequence of raw operations that realizes its `ok` step,
  proven to be a sequence of `ok` raw steps that keeps `Repr` (§82 preamble, §82.2, §82.4, §82.5).
* Safe reads and writes (§82.2), lifetimes (§82.5), deallocation contracts (§82.4), pinned
  addresses (§82.6), exclusivity of bytes (§82.8), pointers written by `store` (§82.3).
* A simulation of runs from the initial state with parameters fixed once per run, and concrete
  runs checked by evaluation.

The sequential fragment only (§18, §29): no theorem here says anything about concurrency.
-/

namespace Ern.MemoryModel.Refinement

open Ern.MemoryModel.Access

/-! ## Allocations of the memory machine (§9) -/

/-- The allocation `i` of `s2` is registered and satisfies `p` (§9, §11 ¶2). -/
def AllocP (s2 : Machine.State) (i : Nat) (p : Machine.Alloc → Prop) : Prop :=
  ∃ a, s2.allocs i = some a ∧ p a

/-- The allocation `i` of `s2` is registered and live (§9 ¶1, §17 ¶3). -/
abbrev LiveAlloc (s2 : Machine.State) (i : Nat) : Prop := AllocP s2 i (·.live = true)

/-- Weakening of the property of a registered allocation (§9). -/
theorem AllocP.mono {s : Machine.State} {i : Nat} {p q : Machine.Alloc → Prop}
    (h : AllocP s i p) (hpq : ∀ a, p a → q a) : AllocP s i q :=
  let ⟨a, ha, hp⟩ := h; ⟨a, ha, hpq a hp⟩

/-- Two properties of one registered allocation (§9). -/
theorem AllocP.and {s : Machine.State} {i : Nat} {p q : Machine.Alloc → Prop}
    (hp : AllocP s i p) (hq : AllocP s i q) : AllocP s i fun a => p a ∧ q a := by
  obtain ⟨a, ha, h1⟩ := hp
  obtain ⟨b, hb, h2⟩ := hq
  rw [ha] at hb; cases hb
  exact ⟨a, ha, h1, h2⟩

/-- A registered allocation is below the counter of a state with fresh identities (§9 ¶7). -/
theorem AllocP.lt {s : Machine.State} (hwf : Machine.WF s) {i : Nat} {p : Machine.Alloc → Prop}
    (h : AllocP s i p) : i < s.next :=
  Nat.lt_of_not_le fun hle => by obtain ⟨a, ha, -⟩ := h; rw [hwf i hle] at ha; cases ha

/-- Base address of the allocation `i` of `s2`, `0` if unregistered (§9 ¶1, §12 ¶1). -/
def baseOf (s2 : Machine.State) (i : Nat) : Nat := ((s2.allocs i).map (·.base)).getD 0

/-- The base of a registered allocation (§9 ¶1). -/
theorem baseOf_of {s2 : Machine.State} {i : Nat} {a : Machine.Alloc} (h : s2.allocs i = some a) :
    baseOf s2 i = a.base := by
  simp [baseOf, h]

/-! ## Layout of places (§82.1, §23) -/

/-- Layout of places (§82.1): place `q` occupies the range `L q` of the elementary memory machine:
an allocation identity, an offset and a length (§11 ¶1). A parameter fixed for a run, defined on
every index, present or future. Only the allocation of a non-leaf place is read. -/
abbrev Layout := Nat → Machine.Place

/-- Layout interface in the states `s3`, `s2` (§82.1; §23 "a memory layout satisfying
`LayoutWF`"). The spec names `LayoutWF` without stating its clauses; the clauses below are the
guarantees §82.1 and §23 ask the layout to provide. No lower bound on lengths: a leaf may have
size zero (§71.1). -/
structure LayoutWF (L : Layout) (s3 : S3) (s2 : Machine.State) : Prop where
  /-- §82.1 (parts): a structural part lies in the allocation of its parent. -/
  parts : ∀ q r, parentOf s3.P q = some r → (L q).alloc = (L r).alloc
  /-- §23, §82.1 (disjointness): two distinct leaves in one allocation have disjoint ranges. -/
  disjoint : ∀ l l', l < s3.P.length → l' < s3.P.length → isLeaf s3.P l → isLeaf s3.P l' →
    l ≠ l' → (L l).alloc = (L l').alloc →
    Machine.RangeDisjoint (L l).off (L l).len (L l').off (L l').len
  /-- §82.1, §15 ¶1: the range of a leaf lies within its allocation, which is registered. -/
  within : ∀ l, l < s3.P.length → isLeaf s3.P l →
    AllocP s2 (L l).alloc fun a => (L l).off + (L l).len ≤ a.size

/-- Elements of a parent chain lie in the allocation of its start (§82.1 parts, §40). -/
theorem alloc_chainF {L : Layout} {P : List Place}
    (hp : ∀ q r, parentOf P q = some r → (L q).alloc = (L r).alloc) :
    ∀ k i r, r ∈ chainF (parentOf P) k i → (L i).alloc = (L r).alloc
  | 0, _, _, h => by simp [chainF] at h
  | k + 1, i, r, h => by
    simp only [chainF] at h
    split at h
    · rename_i o ho
      split at h
      · rcases List.mem_cons.1 h with rfl | h
        · exact hp i _ ho
        · exact (hp i o ho).trans (alloc_chainF hp k o r h)
      · simp at h
    · simp at h

/-- A part lies in the allocation of every place it belongs to (§82.1 parts, §40). -/
theorem LayoutWF.alloc_part {L : Layout} {s3 : S3} {s2 : Machine.State} (hl : LayoutWF L s3 s2)
    {l r : Nat} (h : partOf s3.P l r) : (L l).alloc = (L r).alloc := by
  rcases h.2 with rfl | h
  · rfl
  · exact alloc_chainF hl.parts l l r h

/-! ## Representation relation (§82.1, §82.3, §82.4, §82.5, §9) -/

/-- Representation relation between a kernel state `s3` and a state `s2` of the memory machine,
for the layout `L` and the deallocation tokens `rtok` recorded for the allocation of each root
place (`rtok r` for the root place `r`; §17 ¶4, §70.2):
- `adm`: `s2` is admissible (§9 ¶8: freshness, live disjointness, alignment);
- `layout`: the layout interface (§82.1, §23);
- `inj`: two distinct root places are in distinct allocations (§82.1: storage units and
  identities; §9 ¶5: subplaces are not new allocations, so parts share their root's);
- `tokens`: the allocation of a root place is registered and records the token `rtok r`
  (§82.4, §17 ¶4);
- `live`: the allocation of a usable root place is live (§82.5);
- `init`: the bytes of the range of an `Init` leaf are initialized (§82.3; `Uninit` and `Moved`
  impose nothing, §41).
It does not read the contract `K` (§48). -/
structure Repr (L : Layout) (rtok : Nat → Nat) (s3 : S3) (s2 : Machine.State) : Prop where
  /-- §9 ¶8: admissibility of the memory state. -/
  adm : Machine.Admissible s2
  /-- §82.1, §23: layout interface. -/
  layout : LayoutWF L s3 s2
  /-- §82.1, §9 ¶5: distinct root places, distinct allocations. -/
  inj : ∀ r r', RootPlace s3.P r → RootPlace s3.P r' → r ≠ r' → (L r).alloc ≠ (L r').alloc
  /-- §82.4, §17 ¶4: the allocation of a root place is registered with the token `rtok r`. -/
  tokens : ∀ r, RootPlace s3.P r → AllocP s2 (L r).alloc fun a => a.freeAuth = some (rtok r)
  /-- §82.5: the allocation of a usable root place is live. -/
  live : ∀ r, RootPlace s3.P r → s3.Usable r → LiveAlloc s2 (L r).alloc
  /-- §82.3: the range of an `Init` leaf is initialized. -/
  init : ∀ l, l < s3.P.length → isLeaf s3.P l → s3.I l = .init →
    AllocP s2 (L l).alloc fun a => a.InitRange (L l).off (L l).len

/-! ## Sequences of raw operations (§20.1, §20.3) -/

section Seq

variable {Ty : Type}

/-- Effect of an `ok` raw operation (§20.2): a read leaves the state unchanged. -/
def opEff : Machine.Op Ty → Machine.State → Machine.State
  | .read _ _, s => s
  | .write ac _ w, s => s.write ac w
  | .dealloc id _, s => s.dealloc id
  | .alloc sp b sz al fa, s => s.alloc sp b sz al fa

/-- State after a sequence of `ok` raw operations (§20.3 ¶3). -/
def run : Machine.State → List (Machine.Op Ty) → Machine.State
  | s, [] => s
  | s, o :: os => run (opEff o s) os

/-- `p s o` holds for each operation `o` of the sequence in the state where it runs (§20.3). -/
def Along (p : Machine.State → Machine.Op Ty → Prop) :
    Machine.State → List (Machine.Op Ty) → Prop
  | _, [] => True
  | s, o :: os => p s o ∧ Along p (opEff o s) os

/-- Decidability of `Along` for a decidable property (§20.3 ¶3). -/
instance decAlong (p : Machine.State → Machine.Op Ty → Prop) [h : ∀ s o, Decidable (p s o)] :
    (s : Machine.State) → (os : List (Machine.Op Ty)) → Decidable (Along p s os)
  | _, [] => isTrue trivial
  | s, o :: os => @instDecidableAnd _ _ (h s o) (decAlong p (opEff o s) os)

/-- The parametric obligations of a raw read or write hold, both parts (§15 ¶5, §16 ¶4,
§20.3 ¶1): explicit predicates of the execution context, never replaced by `True`. -/
def Obl (ObR : Machine.ReadOblSpec Ty) (ObW : Machine.WriteOblSpec Ty) (s : Machine.State) :
    Machine.Op Ty → Prop
  | .read ac t => ObR.dec s ac t ∧ ObR.stat s ac t
  | .write ac t w => ObW.dec s ac t w ∧ ObW.stat s ac t w
  | _ => True

/-- The parametric obligations hold for every read and write of a sequence, in the state where it
runs (§20.3). -/
abbrev OblAlong (ObR : Machine.ReadOblSpec Ty) (ObW : Machine.WriteOblSpec Ty) :
    Machine.State → List (Machine.Op Ty) → Prop :=
  Along (Obl ObR ObW)

/-- The operation is an `ok` raw step from `s` to its effect (§20.1 ¶2). -/
def OkAt (C : Nat → Nat → Prop) (ObR : Machine.ReadOblSpec Ty) (ObW : Machine.WriteOblSpec Ty)
    (s : Machine.State) (o : Machine.Op Ty) : Prop :=
  Machine.Step C ObR ObW o s (opEff o s)

/-- A sequence of operations each `ok` where it runs is an execution (§20.3 ¶3). -/
theorem exec_of_along {C : Nat → Nat → Prop} {ObR : Machine.ReadOblSpec Ty}
    {ObW : Machine.WriteOblSpec Ty} :
    ∀ (os : List (Machine.Op Ty)) (s : Machine.State), Along (OkAt C ObR ObW) s os →
      Machine.Exec C ObR ObW os s (run s os)
  | [], s, _ => .nil s
  | _ :: os, _, ⟨h, hs⟩ => .cons h (exec_of_along os _ hs)

/-- Composition of sequences (§20.3 ¶3). -/
theorem run_append (s : Machine.State) (os os' : List (Machine.Op Ty)) :
    run s (os ++ os') = run (run s os) os' := by
  induction os generalizing s with
  | nil => rfl
  | cons o os ih => exact ih _

/-- `Along` over a composed sequence (§20.3 ¶3). -/
theorem along_append {p : Machine.State → Machine.Op Ty → Prop} {s : Machine.State}
    {os os' : List (Machine.Op Ty)} :
    Along p s (os ++ os') ↔ Along p s os ∧ Along p (run s os) os' := by
  induction os generalizing s with
  | nil => simp [Along, run]
  | cons o os ih => simp only [List.cons_append, Along, run, ih, and_assoc]

/-- Executions compose (§20.3 ¶3). -/
theorem exec_append {C : Nat → Nat → Prop} {ObR : Machine.ReadOblSpec Ty}
    {ObW : Machine.WriteOblSpec Ty} {os os' : List (Machine.Op Ty)} {s s' s'' : Machine.State}
    (h : Machine.Exec C ObR ObW os s s') (h' : Machine.Exec C ObR ObW os' s' s'') :
    Machine.Exec C ObR ObW (os ++ os') s s'' := by
  induction h with
  | nil => exact h'
  | cons hs _ ih => exact .cons hs (ih h')

end Seq

/-! ## Allocations kept by raw operations (§13 ¶3, §16 ¶3, §17 ¶3) -/

/-- `s'` keeps every allocation of `s` registered, with its base, size and deallocation token, and
every initialized byte initialized; liveness is not constrained (§13 ¶3, §16 ¶2, §16 ¶3,
§17 ¶3). -/
def Dom (s s' : Machine.State) : Prop :=
  ∀ i a, s.allocs i = some a → ∃ a', s'.allocs i = some a' ∧ a'.base = a.base ∧
    a'.size = a.size ∧ a'.freeAuth = a.freeAuth ∧ ∀ j, a.bytes j ≠ .uninit → a'.bytes j ≠ .uninit

/-- `Dom` is reflexive (§13). -/
theorem Dom.refl (s : Machine.State) : Dom s s :=
  fun _ a h => ⟨a, h, rfl, rfl, rfl, fun _ h => h⟩

/-- `Dom` is transitive (§13). -/
theorem Dom.trans {s s' s'' : Machine.State} (h : Dom s s') (h' : Dom s' s'') : Dom s s'' := by
  intro i a ha
  obtain ⟨a', ha', e1, e2, e3, hb⟩ := h i a ha
  obtain ⟨a'', ha'', f1, f2, f3, hb'⟩ := h' i a' ha'
  exact ⟨a'', ha'', f1.trans e1, f2.trans e2, f3.trans e3, fun j hj => hb' j (hb j hj)⟩

/-- Transport of a property of a registered allocation along `Dom` (§13 ¶3). -/
theorem AllocP.dom {s s' : Machine.State} {i : Nat} {p : Machine.Alloc → Prop}
    (h : AllocP s i p) (hd : Dom s s')
    (hp : ∀ a a' : Machine.Alloc, a'.base = a.base → a'.size = a.size →
      a'.freeAuth = a.freeAuth → (∀ j, a.bytes j ≠ .uninit → a'.bytes j ≠ .uninit) →
      p a → p a') :
    AllocP s' i p := by
  obtain ⟨a, ha, hpa⟩ := h
  obtain ⟨a', ha', e1, e2, e3, hb⟩ := hd i a ha
  exact ⟨a', ha', hp a a' e1 e2 e3 hb hpa⟩

/-- Initialized ranges stay initialized along `Dom` (§16 ¶2). -/
theorem AllocP.dom_init {s s' : Machine.State} {i off len : Nat}
    (h : AllocP s i fun a => a.InitRange off len) (hd : Dom s s') :
    AllocP s' i fun a => a.InitRange off len :=
  h.dom hd fun _ _ _ _ _ hb h j hj => hb _ (h j hj)

/-- Allocation entries after a write (§16 ¶2, ¶3). -/
theorem write_allocs (s : Machine.State) (ac : Machine.Access) (w : Nat → UInt8 × Option Nat)
    (i : Nat) :
    (s.write ac w).allocs i = if i = ac.prov then
      (s.allocs i).map (fun a => a.write (ac.addr - a.base) ac.len w) else s.allocs i := rfl

/-- Allocation entries after a deallocation (§17 ¶3). -/
theorem dealloc_allocs (s : Machine.State) (id i : Nat) :
    (s.dealloc id).allocs i = if i = id then
      (s.allocs i).map (fun a => { a with live := false }) else s.allocs i := rfl

/-- Allocation entries after a creation (§9 ¶11, §13 ¶3). -/
theorem alloc_allocs (s : Machine.State) (sp b sz al : Nat) (fa : Option Nat) (i : Nat) :
    (s.alloc sp b sz al fa).allocs i = if i = s.next then
      some { space := sp, base := b, size := sz, align := al, live := true,
             bytes := fun _ => .uninit, freeAuth := fa } else s.allocs i := rfl

section Keep

variable {Ty : Type}

/-- Every `ok` effect keeps the allocations of a state with fresh identities (§13 ¶3, §16 ¶3,
§17 ¶3). -/
theorem dom_opEff {s : Machine.State} (hwf : Machine.WF s) (o : Machine.Op Ty) :
    Dom s (opEff o s) := by
  intro i a ha
  cases o with
  | read => exact ⟨a, ha, rfl, rfl, rfl, fun _ h => h⟩
  | write ac t w =>
    show ∃ a', (s.write ac w).allocs i = some a' ∧ _
    rw [write_allocs]
    split
    · refine ⟨a.write (ac.addr - a.base) ac.len w, by rw [ha]; simp, rfl, rfl, rfl, fun j hj => ?_⟩
      simp only [Machine.Alloc.write]
      split
      · exact fun h => by cases h
      · exact hj
    · exact ⟨a, ha, rfl, rfl, rfl, fun _ h => h⟩
  | dealloc id au =>
    show ∃ a', (s.dealloc id).allocs i = some a' ∧ _
    rw [dealloc_allocs]
    split
    · exact ⟨{ a with live := false }, by rw [ha]; simp, rfl, rfl, rfl, fun _ h => h⟩
    · exact ⟨a, ha, rfl, rfl, rfl, fun _ h => h⟩
  | alloc sp b sz al fa =>
    show ∃ a', (s.alloc sp b sz al fa).allocs i = some a' ∧ _
    have hi : i ≠ s.next := fun e => by rw [e, hwf s.next (Nat.le_refl _)] at ha; cases ha
    rw [alloc_allocs, ite_eq_right hi]
    exact ⟨a, ha, rfl, rfl, rfl, fun _ h => h⟩

/-- Every `ok` effect keeps freshness (§9 ¶7). -/
theorem wf_opEff {s : Machine.State} (hwf : Machine.WF s) (o : Machine.Op Ty) :
    Machine.WF (opEff o s) := by
  cases o with
  | read => exact hwf
  | write ac t w => exact Machine.write_wf hwf ac w
  | dealloc id au => exact Machine.dealloc_wf hwf id
  | alloc sp b sz al fa => exact Machine.alloc_wf hwf sp b sz al fa

/-- Every sequence of `ok` effects keeps freshness (§9 ¶7). -/
theorem wf_run : ∀ (os : List (Machine.Op Ty)) (s : Machine.State), Machine.WF s →
    Machine.WF (run s os)
  | [], _, h => h
  | o :: os, _, h => wf_run os _ (wf_opEff h o)

/-- Every sequence of `ok` effects keeps the allocations (§13 ¶3, §16 ¶3, §17 ¶3). -/
theorem dom_run : ∀ (os : List (Machine.Op Ty)) (s : Machine.State), Machine.WF s →
    Dom s (run s os)
  | [], s, _ => Dom.refl s
  | o :: os, _, h => (dom_opEff h o).trans (dom_run os _ (wf_opEff h o))

/-- An operation that deallocates no identity: a read, a write or a creation (§13 ¶3,
§16 ¶3). -/
def NoDealloc : Machine.Op Ty → Prop
  | .dealloc .. => False
  | _ => True

/-- An effect other than a deallocation keeps every live allocation live (§13 ¶3, §16 ¶3). -/
theorem live_opEff {s : Machine.State} (hwf : Machine.WF s) {o : Machine.Op Ty}
    (ho : NoDealloc o) {i : Nat} (h : LiveAlloc s i) : LiveAlloc (opEff o s) i := by
  obtain ⟨a, ha, hl⟩ := h
  cases o with
  | read => exact ⟨a, ha, hl⟩
  | write ac t w =>
    show AllocP (s.write ac w) i _
    rw [AllocP, write_allocs]
    split
    · exact ⟨a.write (ac.addr - a.base) ac.len w, by rw [ha]; simp, hl⟩
    · exact ⟨a, ha, hl⟩
  | dealloc => exact ho.elim
  | alloc sp b sz al fa =>
    have hi : i ≠ s.next := fun e => by rw [e, hwf s.next (Nat.le_refl _)] at ha; cases ha
    show AllocP (s.alloc sp b sz al fa) i _
    rw [AllocP, alloc_allocs, ite_eq_right hi]
    exact ⟨a, ha, hl⟩

/-- A sequence without deallocation keeps every live allocation live (§13 ¶3, §16 ¶3). -/
theorem live_run : ∀ (os : List (Machine.Op Ty)) (s : Machine.State), Machine.WF s →
    (∀ o ∈ os, NoDealloc o) → ∀ {i : Nat}, LiveAlloc s i → LiveAlloc (run s os) i
  | [], _, _, _, _, h => h
  | o :: os, _, hwf, hn, _, h =>
    live_run os _ (wf_opEff hwf o) (fun o' ho' => hn o' (List.mem_cons_of_mem _ ho'))
      (live_opEff hwf (hn o (List.mem_cons_self ..)) h)

/-- The base of a registered allocation is kept by every sequence of `ok` effects (§13 ¶3: no
allocation moves). -/
theorem baseOf_run {s : Machine.State} (hwf : Machine.WF s) (os : List (Machine.Op Ty)) {i : Nat}
    (h : AllocP s i fun _ => True) : baseOf (run s os) i = baseOf s i := by
  obtain ⟨a, ha, -⟩ := h
  obtain ⟨a', ha', e, -⟩ := dom_run os s hwf i a ha
  rw [baseOf_of ha, baseOf_of ha', e]

end Keep

/-! ## Transport of `Repr` -/

/-- `Repr` carries over to a kernel state with the same tree of places (same number of places
and same parents) and a memory state that keeps the allocations (`Dom`) and is admissible, when
every usable root place of the new state has a live allocation and every leaf that becomes `Init`
has its range initialized (§82.1, §82.3, §82.5). -/
theorem Repr.transport {L : Layout} {rtok : Nat → Nat} {s3 s3' : S3} {s2 s2' : Machine.State}
    (hR : Repr L rtok s3 s2) (hadm : Machine.Admissible s2') (hd : Dom s2 s2')
    (hlen : s3'.P.length = s3.P.length) (hpar : parentOf s3'.P = parentOf s3.P)
    (hlive : ∀ r, RootPlace s3.P r → s3'.Usable r → LiveAlloc s2' (L r).alloc)
    (hI : ∀ l, l < s3.P.length → isLeaf s3.P l → s3'.I l = .init →
      s3.I l = .init ∨ AllocP s2' (L l).alloc fun a => a.InitRange (L l).off (L l).len) :
    Repr L rtok s3' s2' := by
  have hleaf : ∀ l, isLeaf s3'.P l ↔ isLeaf s3.P l := fun l => by simp only [isLeaf, hlen, hpar]
  have hroot : ∀ r, RootPlace s3'.P r ↔ RootPlace s3.P r := fun r => by
    simp only [RootPlace, hlen, hpar]
  refine ⟨hadm, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro q r h; rw [hpar] at h; exact hR.layout.parts q r h
  · intro l l' hl hl' hf hf' hne he
    rw [hlen] at hl hl'; rw [hleaf] at hf hf'
    exact hR.layout.disjoint l l' hl hl' hf hf' hne he
  · intro l hl hf
    rw [hlen] at hl; rw [hleaf] at hf
    exact (hR.layout.within l hl hf).dom hd fun _ _ _ e _ _ h => e ▸ h
  · intro r r' hr hr' hne
    exact hR.inj r r' ((hroot r).1 hr) ((hroot r').1 hr') hne
  · intro r hr
    exact (hR.tokens r ((hroot r).1 hr)).dom hd fun _ _ _ _ e _ h => e ▸ h
  · intro r hr hu
    exact hlive r ((hroot r).1 hr) hu
  · intro l hl hf hi
    rw [hlen] at hl; rw [hleaf] at hf
    rcases hI l hl hf hi with h | h
    · exact (hR.init l hl hf h).dom_init hd
    · exact h

/-! ## Accesses to leaves (§12, §15, §16) -/

/-- Address of the range of place `l` in `s2`: the base of its allocation plus its offset (§12 ¶1,
§82.1). -/
def leafAddr (s2 : Machine.State) (L : Layout) (l : Nat) : Nat := baseOf s2 (L l).alloc + (L l).off

/-- The means of access to the range of leaf `l` in `s2` (§12 ¶1, §82.2): address of the range,
provenance its allocation, length its size, elementary authority `au`. -/
def leafAcc (s2 : Machine.State) (L : Layout) (au : Machine.Auth) (l : Nat) : Machine.Access :=
  ⟨leafAddr s2 L l, (L l).alloc, (L l).len, au⟩

/-- The access to a leaf of a registered allocation (§12 ¶1). -/
theorem leafAcc_of {s2 : Machine.State} {L : Layout} {au : Machine.Auth} {l : Nat}
    {a : Machine.Alloc} (h : s2.allocs (L l).alloc = some a) :
    leafAcc s2 L au l = ⟨a.base + (L l).off, (L l).alloc, (L l).len, au⟩ := by
  simp [leafAcc, leafAddr, baseOf_of h]

/-- The access to a leaf is kept by `Dom` when its allocation is registered (§13 ¶3). -/
theorem leafAcc_dom {s2 s2' : Machine.State} (hd : Dom s2 s2') {L : Layout} {au : Machine.Auth}
    {l : Nat} (h : AllocP s2 (L l).alloc fun _ => True) :
    leafAcc s2' L au l = leafAcc s2 L au l := by
  obtain ⟨a, ha, -⟩ := h
  obtain ⟨a', ha', e, -⟩ := hd _ a ha
  rw [leafAcc_of ha, leafAcc_of ha', e]

/-- The kernel read conditions of the access to a leaf whose allocation is live, contains the
range and has it initialized (§15.1, §15.2, §15.3, §15.5). -/
theorem canRead_leaf {s2 : Machine.State} {L : Layout} {l : Nat} {a : Machine.Alloc}
    (ha : s2.allocs (L l).alloc = some a) (hl : a.live = true)
    (hs : (L l).off + (L l).len ≤ a.size) (hi : a.InitRange (L l).off (L l).len) :
    Machine.CanRead s2 (leafAcc s2 L .read l) := by
  rw [leafAcc_of ha]
  refine ⟨a, ha, hl, ⟨Nat.le_add_right _ _, by simp only; omega⟩, ?_, .inl rfl⟩
  simp only [Nat.add_sub_cancel_left]; exact hi

/-- The kernel write conditions of the access to a leaf whose allocation is live and contains the
range (§16.1, §16.2, §16.3). -/
theorem canWrite_leaf {s2 : Machine.State} {L : Layout} {l : Nat} {a : Machine.Alloc}
    (ha : s2.allocs (L l).alloc = some a) (hl : a.live = true)
    (hs : (L l).off + (L l).len ≤ a.size) : Machine.CanWrite s2 (leafAcc s2 L .write l) := by
  rw [leafAcc_of ha]
  exact ⟨a, ha, hl, ⟨Nat.le_add_right _ _, by simp only; omega⟩, .inr rfl⟩

/-- After the write of the range of a leaf of a registered allocation, the range is initialized
(§16 ¶2). -/
theorem write_leaf_init {s2 : Machine.State} {L : Layout} {l : Nat}
    {w : Nat → UInt8 × Option Nat} (h : AllocP s2 (L l).alloc fun _ => True) :
    AllocP (s2.write (leafAcc s2 L .write l) w) (L l).alloc
      fun a => a.InitRange (L l).off (L l).len := by
  obtain ⟨a, ha, -⟩ := h
  refine ⟨a.write (L l).off (L l).len w, ?_, fun i hi => ?_⟩
  · rw [write_allocs, leafAcc_of ha]
    simp only [↓reduceIte, ha, Option.map_some, Nat.add_sub_cancel_left]
  · rw [Machine.Alloc.write_bytes_in a w hi]; exact fun h => by cases h

/-! ## Leaves of usable places -/

/-- A leaf of a usable place has a usable root place (§40, §49.2). -/
theorem root_of_leaf {s3 : S3} (hw : WF3 s3) {l : Nat} (hl : l < s3.P.length)
    (hu : s3.Usable l) : ∃ r, RootPlace s3.P r ∧ partOf s3.P l r ∧ s3.Usable r := by
  obtain ⟨r, hr, hlr⟩ := exists_rootPlace hw (l + 1) l (Nat.lt_succ_self l) hl
  exact ⟨r, hr, hlr, usable_of_part hw hlr hu⟩

/-- A leaf that belongs to a usable place is an existing usable leaf (§66.1, §67.1, §68.1,
§40). -/
theorem leaf_of_leafOfUsable {s3 : S3} (hw : WF3 s3) {l : Nat} (h : LeafOfUsable s3 l) :
    l < s3.P.length ∧ isLeaf s3.P l ∧ s3.Usable l := by
  obtain ⟨q, -, hq, hl⟩ := h
  obtain ⟨hlP, hlf, hlq⟩ := mem_footprint.1 hl
  exact ⟨hlP, hlf, usable_of_partOf hw (l + 1) l q (Nat.lt_succ_self l) hlq hq⟩

/-- The allocation of a usable leaf is live and contains its range (§82.5, §82.1). -/
theorem Repr.leaf_live {L : Layout} {rtok : Nat → Nat} {s3 : S3} {s2 : Machine.State}
    (hR : Repr L rtok s3 s2) (hw : WF3 s3) {l : Nat} (hl : l < s3.P.length)
    (hlf : isLeaf s3.P l) (hu : s3.Usable l) :
    AllocP s2 (L l).alloc fun a => a.live = true ∧ (L l).off + (L l).len ≤ a.size := by
  obtain ⟨r, hr, hlr, hur⟩ := root_of_leaf hw hl hu
  have hlive := hR.live r hr hur
  rw [← hR.layout.alloc_part hlr] at hlive
  exact hlive.and (hR.layout.within l hl hlf)

/-! ## R1: safe reads (§82.2, §66, §15) -/

/-- The reads realizing `read(access, ls)` (§82.2, §66): one raw read per leaf, of the range of
the leaf, at the type `ty l` of the leaf. -/
def readOps {Ty : Type} (s2 : Machine.State) (L : Layout) (ty : Nat → Ty) (ls : List Nat) :
    List (Machine.Op Ty) :=
  ls.map fun l => .read (leafAcc s2 L .read l) (ty l)

/-- Safe read (§82.2, §66, §15): under `Repr`, `WF3` and the preconditions of `read` (§66), the
raw read of the range of each leaf read is `ok` when the parametric obligations of that read hold
(§15.4, §15.6, §15.7): its allocation is live, the range is initialized, and the read returns the
bytes of the range. -/
theorem r1_read {Ty : Type} {ObR : Machine.ReadOblSpec Ty} {ty : Nat → Ty} {L : Layout}
    {rtok : Nat → Nat} {s3 : S3} {s2 : Machine.State} {a : Nat} {ls : List Nat}
    (hR : Repr L rtok s3 s2) (hw : WF3 s3) (hpre : Read3Pre s3 a ls) {l : Nat} (hl : l ∈ ls)
    (hob : ObR.dec s2 (leafAcc s2 L .read l) (ty l) ∧ ObR.stat s2 (leafAcc s2 L .read l) (ty l)) :
    ∃ al, s2.allocs (L l).alloc = some al ∧ al.live = true ∧ al.InitRange (L l).off (L l).len ∧
      Machine.ReadStep ObR (leafAcc s2 L .read l) (ty l) s2
        (.ok (al.bytesAt (L l).off (L l).len)) := by
  obtain ⟨hlP, hlf, hu⟩ := leaf_of_leafOfUsable hw (hpre.usable l hl)
  obtain ⟨al, hal, hlive, hsz⟩ := hR.leaf_live hw hlP hlf hu
  obtain ⟨al', hal', hi⟩ := hR.init l hlP hlf (hpre.init l hl)
  rw [hal] at hal'; cases hal'
  refine ⟨al, hal, hlive, hi, ?_⟩
  have hc := canRead_leaf hal hlive hsz hi
  have hst := Machine.ReadStep.ok (ObR := ObR) (t := ty l) hal ⟨hc, hob.1, hob.2⟩
  rw [leafAcc_of hal] at hst ⊢
  simpa only [Nat.add_sub_cancel_left] using hst

/-- The reads of a sequence of leaves leave the memory state unchanged (§20.2 ¶1). -/
theorem run_readOps {Ty : Type} (s2 : Machine.State) (L : Layout) (ty : Nat → Ty) :
    ∀ ls t, run t (readOps s2 L ty ls) = t
  | [], _ => rfl
  | _ :: ls, t => run_readOps s2 L ty ls t

/-- Realization of `read` (§82 preamble, §82.2, §66): under `Repr`, `WF3`, an `ok` step of `read`
and the parametric obligations along the reads, the reads form an execution of `ok` raw steps
that leaves the memory state unchanged, and `Repr` holds after the step. -/
theorem r6_read {Ty : Type} {C : Nat → Nat → Prop} {ObR : Machine.ReadOblSpec Ty}
    {ObW : Machine.WriteOblSpec Ty} {ty : Nat → Ty} {L : Layout} {rtok : Nat → Nat}
    {s3 s3' : S3} {s2 : Machine.State} {a : Nat} {ls : List Nat} (hR : Repr L rtok s3 s2)
    (hw : WF3 s3) (h : Read3Step a ls s3 (.ok s3'))
    (hob : OblAlong ObR ObW s2 (readOps s2 L ty ls)) :
    Machine.Exec C ObR ObW (readOps s2 L ty ls) s2 (run s2 (readOps s2 L ty ls)) ∧
      run s2 (readOps s2 L ty ls) = s2 ∧ Repr L rtok s3' (run s2 (readOps s2 L ty ls)) := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  rw [run_readOps]
  refine ⟨?_, rfl, hR⟩
  have key : ∀ ls', (∀ l ∈ ls', l ∈ ls) → OblAlong ObR ObW s2 (readOps s2 L ty ls') →
      Along (OkAt C ObR ObW) s2 (readOps s2 L ty ls') := by
    intro ls'
    induction ls' with
    | nil => intro _ _; trivial
    | cons l ls' ih =>
      intro hsub hob'
      obtain ⟨al, hal, -, -, hst⟩ := r1_read hR hw hpre (hsub l (List.mem_cons_self ..)) hob'.1
      exact ⟨.read hst, ih (fun l' hl' => hsub l' (List.mem_cons_of_mem _ hl')) hob'.2⟩
  have := exec_of_along _ _ (key ls (fun _ h => h) hob)
  rwa [run_readOps] at this

/-! ## Transport for steps that keep the places -/

/-- `Repr` carries over a step that keeps the places and makes no place usable, along raw steps
that keep the allocations and every live allocation live (§82.1, §82.3, §82.5). -/
theorem Repr.same_places {L : Layout} {rtok : Nat → Nat} {s3 s3' : S3} {s2 s2' : Machine.State}
    (hR : Repr L rtok s3 s2) (hadm : Machine.Admissible s2') (hd : Dom s2 s2')
    (hl : ∀ i, LiveAlloc s2 i → LiveAlloc s2' i) (hP : s3'.P = s3.P)
    (hU : ∀ q, s3'.Usable q → s3.Usable q)
    (hI : ∀ l, l < s3.P.length → isLeaf s3.P l → s3'.I l = .init →
      s3.I l = .init ∨ AllocP s2' (L l).alloc fun a => a.InitRange (L l).off (L l).len) :
    Repr L rtok s3' s2' :=
  hR.transport hadm hd (by rw [hP]) (by rw [hP]) (fun r hr hu => hl _ (hR.live r hr (hU r hu))) hI

/-- `Repr` carries over a step that changes none of the places, the stack, the death markers and
the initialization states, with no raw operation (§82; §60–§62, §64, §74, §75: no storage
effect). -/
theorem Repr.of_eqs {L : Layout} {rtok : Nat → Nat} {s3 s3' : S3} {s2 : Machine.State}
    (hR : Repr L rtok s3 s2) (hP : s3'.P = s3.P) (hF : s3'.F = s3.F) (hd : s3'.dead = s3.dead)
    (hI : s3'.I = s3.I) : Repr L rtok s3' s2 :=
  hR.same_places hR.adm (Dom.refl _) (fun _ h => h) hP (fun _ h => h.of_eqs hP hF hd)
    fun _ _ _ h => .inl (hI ▸ h)

/-! ## R2: safe writes (§82.2, §67, §68, §16) -/

/-- The writes realizing `write(access, ls)` and `writeShared(access, ls)` (§82.2, §67, §68): one
raw write per leaf, of the range of the leaf, at the type `ty l`, of the representation `w l`
supplied by the program (§10 ¶4, §16 ¶2). -/
def writeOps {Ty : Type} (s2 : Machine.State) (L : Layout) (ty : Nat → Ty)
    (w : Nat → Nat → UInt8 × Option Nat) (ls : List Nat) : List (Machine.Op Ty) :=
  ls.map fun l => .write (leafAcc s2 L .write l) (ty l) (w l)

/-- The writes of the ranges of leaves whose allocations are live and contain them are `ok` under
their parametric obligations (§16, §82.2), and afterwards every written range is initialized
(§16 ¶2). -/
theorem writes_ok {Ty : Type} {C : Nat → Nat → Prop} {ObR : Machine.ReadOblSpec Ty}
    {ObW : Machine.WriteOblSpec Ty} {L : Layout} {ty : Nat → Ty}
    {w : Nat → Nat → UInt8 × Option Nat} :
    ∀ (ls : List Nat) (s2 : Machine.State), Machine.WF s2 →
      (∀ l ∈ ls, AllocP s2 (L l).alloc fun a => a.live = true ∧ (L l).off + (L l).len ≤ a.size) →
      OblAlong ObR ObW s2 (writeOps s2 L ty w ls) →
      Along (OkAt C ObR ObW) s2 (writeOps s2 L ty w ls) ∧
        ∀ l ∈ ls, AllocP (run s2 (writeOps s2 L ty w ls)) (L l).alloc
          fun a => a.InitRange (L l).off (L l).len
  | [], _, _, _, _ => ⟨trivial, fun _ h => nomatch h⟩
  | l :: ls, s2, hwf, hls, hob => by
    obtain ⟨al, hal, hlive, hsz⟩ := hls l (List.mem_cons_self ..)
    have hex : AllocP s2 (L l).alloc fun _ => True := ⟨al, hal, trivial⟩
    have hd₁ : Dom s2 (s2.write (leafAcc s2 L .write l) (w l)) :=
      dom_opEff (Ty := Ty) hwf (.write (leafAcc s2 L .write l) (ty l) (w l))
    have hwf₁ : Machine.WF (s2.write (leafAcc s2 L .write l) (w l)) :=
      Machine.write_wf hwf _ _
    have hops : writeOps (s2.write (leafAcc s2 L .write l) (w l)) L ty w ls =
        writeOps s2 L ty w ls := by
      simp only [writeOps, List.map_inj_left]
      intro l' hl'
      obtain ⟨b, hb, -⟩ := hls l' (List.mem_cons_of_mem _ hl')
      rw [leafAcc_dom hd₁ ⟨b, hb, trivial⟩]
    have hls₁ : ∀ l' ∈ ls, AllocP (s2.write (leafAcc s2 L .write l) (w l)) (L l').alloc
        fun a => a.live = true ∧ (L l').off + (L l').len ≤ a.size := by
      intro l' hl'
      obtain ⟨b, hb, hbl, hbs⟩ := hls l' (List.mem_cons_of_mem _ hl')
      obtain ⟨b', hb', -, e, -⟩ := hd₁ _ b hb
      refine ⟨b', hb', ?_, e ▸ hbs⟩
      have := live_opEff (Ty := Ty) (o := .write (leafAcc s2 L .write l) (ty l) (w l)) hwf trivial
        ⟨b, hb, hbl⟩
      obtain ⟨b'', hb'', hl''⟩ := this
      change (s2.write (leafAcc s2 L .write l) (w l)).allocs _ = _ at hb''
      rw [hb'] at hb''; cases hb''; exact hl''
    have hob₁ : OblAlong ObR ObW (s2.write (leafAcc s2 L .write l) (w l))
        (writeOps (s2.write (leafAcc s2 L .write l) (w l)) L ty w ls) := by
      rw [hops]; exact hob.2
    obtain ⟨ih1, ih2⟩ := writes_ok (C := C) ls _ hwf₁ hls₁ hob₁
    rw [hops] at ih1 ih2
    refine ⟨⟨.write (.ok ⟨canWrite_leaf hal hlive hsz, hob.1⟩), ih1⟩, fun l' hl' => ?_⟩
    rcases List.mem_cons.1 hl' with rfl | hl'
    · exact (write_leaf_init hex).dom_init (dom_run _ _ hwf₁)
    · exact ih2 l' hl'

/-- The writes form no deallocation (§16). -/
theorem writeOps_noDealloc {Ty : Type} (s2 : Machine.State) (L : Layout) (ty : Nat → Ty)
    (w : Nat → Nat → UInt8 × Option Nat) (ls : List Nat) :
    ∀ o ∈ writeOps s2 L ty w ls, NoDealloc o := by
  intro o ho
  obtain ⟨l, -, rfl⟩ := List.mem_map.1 ho
  trivial

/-- Realization of the writes of a step whose written leaves belong to usable places, which keeps
the places, the stack and the death markers, and makes `Init` only written leaves (§82.2, §82.3,
§67, §68, §65, §16): the raw writes are `ok` and `Repr` holds after the step. -/
theorem writes_repr {Ty : Type} {C : Nat → Nat → Prop} {ObR : Machine.ReadOblSpec Ty}
    {ObW : Machine.WriteOblSpec Ty} {ty : Nat → Ty} {w : Nat → Nat → UInt8 × Option Nat}
    {L : Layout} {rtok : Nat → Nat} {s3 s3' : S3} {s2 : Machine.State} {ls : List Nat}
    (hR : Repr L rtok s3 s2) (hw : WF3 s3) (hu : ∀ l ∈ ls, LeafOfUsable s3 l)
    (hob : OblAlong ObR ObW s2 (writeOps s2 L ty w ls)) (hP : s3'.P = s3.P) (hF : s3'.F = s3.F)
    (hd : s3'.dead = s3.dead) (hI : ∀ l, s3'.I l = .init → s3.I l = .init ∨ l ∈ ls) :
    Machine.Exec C ObR ObW (writeOps s2 L ty w ls) s2 (run s2 (writeOps s2 L ty w ls)) ∧
      Repr L rtok s3' (run s2 (writeOps s2 L ty w ls)) := by
  have hls : ∀ l ∈ ls, AllocP s2 (L l).alloc
      fun a => a.live = true ∧ (L l).off + (L l).len ≤ a.size := fun l hl => by
    obtain ⟨hlP, hlf, hu⟩ := leaf_of_leafOfUsable hw (hu l hl)
    exact hR.leaf_live hw hlP hlf hu
  obtain ⟨hok, hinit⟩ := writes_ok (C := C) ls s2 hR.adm.wf hls hob
  have hex := exec_of_along _ _ hok
  refine ⟨hex, hR.same_places (hex.admissible hR.adm) (dom_run _ _ hR.adm.wf)
    (fun _ h => live_run _ _ hR.adm.wf (writeOps_noDealloc s2 L ty w ls) h) hP
    (fun _ h => h.of_eqs hP hF hd) fun l _ _ hi => ?_⟩
  rcases hI l hi with h | h
  · exact .inl h
  · exact .inr (hinit l h)

/-- Realization of the writes of a step whose effect is `write3Eff` (§82.2, §67, §68, §16). -/
theorem r2_core {Ty : Type} {C : Nat → Nat → Prop} {ObR : Machine.ReadOblSpec Ty}
    {ObW : Machine.WriteOblSpec Ty} {ty : Nat → Ty} {w : Nat → Nat → UInt8 × Option Nat}
    {L : Layout} {rtok : Nat → Nat} {s3 : S3} {s2 : Machine.State} {ls : List Nat}
    (hR : Repr L rtok s3 s2) (hw : WF3 s3) (hu : ∀ l ∈ ls, LeafOfUsable s3 l)
    (hob : OblAlong ObR ObW s2 (writeOps s2 L ty w ls)) :
    Machine.Exec C ObR ObW (writeOps s2 L ty w ls) s2 (run s2 (writeOps s2 L ty w ls)) ∧
      Repr L rtok (write3Eff s3 ls) (run s2 (writeOps s2 L ty w ls)) :=
  writes_repr hR hw hu hob rfl rfl rfl fun l hi => by
    simp only [write3Eff] at hi
    split at hi
    · exact .inr ‹_›
    · exact .inl hi

/-- R2 and realization of `write` (§82.2, §82 preamble, §67, §16): under `Repr`, `WF3`, an `ok`
step of `write(access, ls)` and the parametric obligations along the writes, the raw writes of
the ranges of the written leaves, with any supplied representation `w`, form an execution of `ok`
raw steps, and `Repr` holds after the step. -/
theorem r2_write {Ty : Type} {C : Nat → Nat → Prop} {ObR : Machine.ReadOblSpec Ty}
    {ObW : Machine.WriteOblSpec Ty} {ty : Nat → Ty} {w : Nat → Nat → UInt8 × Option Nat}
    {L : Layout} {rtok : Nat → Nat} {s3 s3' : S3} {s2 : Machine.State} {a : Nat}
    {ls : List Nat} (hR : Repr L rtok s3 s2) (hw : WF3 s3) (h : Write3Step a ls s3 (.ok s3'))
    (hob : OblAlong ObR ObW s2 (writeOps s2 L ty w ls)) :
    Machine.Exec C ObR ObW (writeOps s2 L ty w ls) s2 (run s2 (writeOps s2 L ty w ls)) ∧
      Repr L rtok s3' (run s2 (writeOps s2 L ty w ls)) := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  exact r2_core hR hw hpre.usable hob

/-- R2 and realization of `writeShared` (§82.2, §82 preamble, §68, §16): as `r2_write`, for an
`ok` step of `writeShared(access, ls)`. -/
theorem r2_writeShared {Ty : Type} {k : K} {C : Nat → Nat → Prop} {ObR : Machine.ReadOblSpec Ty}
    {ObW : Machine.WriteOblSpec Ty} {ty : Nat → Ty} {w : Nat → Nat → UInt8 × Option Nat}
    {L : Layout} {rtok : Nat → Nat} {s3 s3' : S3} {s2 : Machine.State} {a : Nat}
    {ls : List Nat} (hR : Repr L rtok s3 s2) (hw : WF3 s3)
    (h : WriteSharedStep k a ls s3 (.ok s3'))
    (hob : OblAlong ObR ObW s2 (writeOps s2 L ty w ls)) :
    Machine.Exec C ObR ObW (writeOps s2 L ty w ls) s2 (run s2 (writeOps s2 L ty w ls)) ∧
      Repr L rtok s3' (run s2 (writeOps s2 L ty w ls)) := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  exact r2_core hR hw hpre.usable hob

/-! ## Steps without storage effect (§60–§62, §64, §69, §74, §75) -/

/-- Realization of `derive` (§82 preamble, §60: no storage or place is created): no raw
operation; `Repr` holds after the step. -/
theorem r6_derive {L : Layout} {rtok : Nat → Nat} {s3 s3' : S3} {s2 : Machine.State} {src : Nat}
    {region : List Nat} {m : Mode} (hR : Repr L rtok s3 s2)
    (h : DeriveStep src region m s3 (.ok s3')) : Repr L rtok s3' s2 := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
  exact hR.of_eqs rfl rfl rfl rfl

/-- Realization of `split` (§82 preamble, §61: "`split` performs no physical allocation"): no raw
operation; `Repr` holds after the step. -/
theorem r6_split {k : K} {L : Layout} {rtok : Nat → Nat} {s3 s3' : S3} {s2 : Machine.State}
    {src : Nat} {rs : List (List Nat)} (hR : Repr L rtok s3 s2)
    (h : SplitStep k src rs s3 (.ok s3')) : Repr L rtok s3' s2 := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
  exact hR.of_eqs rfl rfl rfl rfl

/-- Realization of `release` (§82 preamble, §62: "There is no implicit deallocation"): no raw
operation; `Repr` holds after the step. -/
theorem r6_release {L : Layout} {rtok : Nat → Nat} {s3 s3' : S3} {s2 : Machine.State} {a : Nat}
    (hR : Repr L rtok s3 s2) (h : ReleaseStep a s3 (.ok s3')) : Repr L rtok s3' s2 := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
  unfold releaseEff
  split
  · exact hR.of_eqs rfl rfl rfl rfl
  · exact hR

/-- Realization of `depend` (§82 preamble, §64: no access right or storage is created): no raw
operation; `Repr` holds after the step. -/
theorem r6_depend {L : Layout} {rtok : Nat → Nat} {s3 s3' : S3} {s2 : Machine.State} {q x : Nat}
    (hR : Repr L rtok s3 s2) (h : DependStep q x s3 (.ok s3')) : Repr L rtok s3' s2 := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
  exact hR.of_eqs rfl rfl rfl rfl

/-- Realization of `pin` (§82 preamble, §82.6, §74: pinning does not move storage): no raw
operation; `Repr` holds after the step. -/
theorem r6_pin {L : Layout} {rtok : Nat → Nat} {s3 s3' : S3} {s2 : Machine.State} {p : Nat}
    (hR : Repr L rtok s3 s2) (h : PinStep p s3 (.ok s3')) : Repr L rtok s3' s2 := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
  exact hR.of_eqs rfl rfl rfl rfl

/-- Realization of `unpin` (§82 preamble, §82.6, §75): no raw operation; `Repr` holds after the
step. -/
theorem r6_unpin {k : K} {L : Layout} {rtok : Nat → Nat} {s3 s3' : S3} {s2 : Machine.State}
    {p : Nat} (hR : Repr L rtok s3 s2) (h : UnpinStep k p s3 (.ok s3')) : Repr L rtok s3' s2 := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
  exact hR.of_eqs rfl rfl rfl rfl

/-- Realization of `endUse` (§82.5, §69: "The operation does not automatically trigger physical
deallocation in the elementary memory machine"): no raw operation; the allocations of the storage
that dies stay live (a leak, which §69 does not prohibit); `Repr` holds after the step. -/
theorem r6_endUse {k : K} {L : Layout} {rtok : Nat → Nat} {s3 s3' : S3} {s2 : Machine.State}
    {p : Nat} (hR : Repr L rtok s3 s2) (h : EndUseStep k p s3 (.ok s3')) :
    Repr L rtok s3' s2 := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
  refine hR.same_places hR.adm (Dom.refl _) (fun _ h => h) rfl
    (fun q hq => S3.Usable.mono (s := s3) (s' := endUseEff s3 p) rfl (fun _ h => h) (fun q h => by
      simp only [endUseEff, cleanup, endUseS, Bool.or_eq_false_iff] at h; exact h.1) hq)
    fun l _ _ hi => .inl ?_
  · simp only [endUseEff, cleanup, endUseS] at hi
    split at hi
    · cases hi
    · exact hi

/-! ## Deallocations (§17, §70, §73, §82.4, §82.5) -/

/-- The elements of `range n` are increasing (§49, last paragraph: identities as indices). -/
theorem range_pairwise : ∀ n, (List.range n).Pairwise (· < ·)
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.pairwise_append]
    exact ⟨range_pairwise n, by simp, fun a ha b hb => by
      simp only [List.mem_range, List.mem_singleton] at ha hb; omega⟩

/-- Deallocations of the allocations of the root places `rs`, each presenting the token recorded
for it (§17, §73: automatic storage of an exiting frame). -/
def deallocOps {Ty : Type} (L : Layout) (rtok : Nat → Nat) (rs : List Nat) :
    List (Machine.Op Ty) :=
  rs.map fun r => .dealloc (L r).alloc (rtok r)

/-- Deallocations of distinct live allocations recording their tokens are `ok` when each token is
compatible with itself (§17.1, §17.2); afterwards they are dead and every other allocation is
unchanged (§17 ¶3). -/
theorem deallocOps_run {Ty : Type} {C : Nat → Nat → Prop} {ObR : Machine.ReadOblSpec Ty}
    {ObW : Machine.WriteOblSpec Ty} {L : Layout} {rtok : Nat → Nat}
    (htc : ∀ r, C (rtok r) (rtok r)) :
    ∀ (rs : List Nat) (s2 : Machine.State), rs.Pairwise (fun r r' => (L r).alloc ≠ (L r').alloc) →
      (∀ r ∈ rs, AllocP s2 (L r).alloc fun a => a.live = true ∧ a.freeAuth = some (rtok r)) →
      Along (OkAt C ObR ObW) s2 (deallocOps (Ty := Ty) L rtok rs) ∧
      (∀ i, (∀ r ∈ rs, (L r).alloc ≠ i) →
        (run s2 (deallocOps (Ty := Ty) L rtok rs)).allocs i = s2.allocs i) ∧
      ∀ r ∈ rs, AllocP (run s2 (deallocOps (Ty := Ty) L rtok rs)) (L r).alloc (·.live = false)
  | [], _, _, _ => ⟨trivial, fun _ _ => rfl, fun _ h => nomatch h⟩
  | r :: rs, s2, hp, hrs => by
    obtain ⟨hr, hp⟩ := List.pairwise_cons.1 hp
    obtain ⟨a, ha, hla, hfa⟩ := hrs r (List.mem_cons_self ..)
    have hrs' : ∀ r' ∈ rs, AllocP (s2.dealloc (L r).alloc) (L r').alloc
        fun a => a.live = true ∧ a.freeAuth = some (rtok r') := fun r' hr' => by
      obtain ⟨b, hb, hbl⟩ := hrs r' (List.mem_cons_of_mem _ hr')
      refine ⟨b, ?_, hbl⟩
      rw [dealloc_allocs, ite_eq_right (Ne.symm (hr r' hr')), hb]
    obtain ⟨ih1, ih2, ih3⟩ := deallocOps_run htc rs _ hp hrs'
    refine ⟨⟨.dealloc (.ok ⟨a, ha, hla, _, hfa, htc r⟩), ih1⟩, fun i hi => ?_, fun r' hr' => ?_⟩
    · change (run (s2.dealloc (L r).alloc) (deallocOps L rtok rs)).allocs i = _
      rw [ih2 i fun r' hr' => hi r' (List.mem_cons_of_mem _ hr'), dealloc_allocs,
        ite_eq_right (Ne.symm (hi r (List.mem_cons_self ..)))]
    · rcases List.mem_cons.1 hr' with rfl | hr'
      · refine ⟨{ a with live := false }, ?_, rfl⟩
        change (run (s2.dealloc (L r').alloc) (deallocOps L rtok rs)).allocs _ = _
        rw [ih2 _ fun r'' hr'' => Ne.symm (hr r'' hr''), dealloc_allocs, ite_eq_left rfl, ha]
        rfl
      · exact ih3 r' hr'

/-- Root places directly owned by the current frame and not marked dead: the automatic storage
deallocated when the frame exits (§73, §82.5). -/
def exitRoots (s3 : S3) : List Nat :=
  (List.range s3.P.length).filter fun r => decide (parentOf s3.P r = none ∧
    OptP (s3.P[r]?) (fun pl => pl.owner = .frame s3.top) False ∧ s3.dead r = false)

/-- Membership in `exitRoots` (§73). -/
theorem mem_exitRoots {s3 : S3} {r : Nat} : r ∈ exitRoots s3 ↔ RootPlace s3.P r ∧
    OptP (s3.P[r]?) (fun pl => pl.owner = .frame s3.top) False ∧ s3.dead r = false := by
  simp only [exitRoots, List.mem_filter, List.mem_range, decide_eq_true_eq, RootPlace]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨⟨h1, h2⟩, h3, h4⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨h1, h2, h3, h4⟩

/-- The raw operations realizing `exitFrame` (§73, §82.5): one deallocation per root place
directly owned by the exiting frame, presenting the token recorded for its allocation. -/
def exitOps {Ty : Type} (L : Layout) (rtok : Nat → Nat) (s3 : S3) : List (Machine.Op Ty) :=
  deallocOps L rtok (exitRoots s3)

/-- Realization of `exitFrame` (§82 preamble, §82.5, §73, §17): under `Repr`, `WF3`, an `ok` step
of `exitFrame` and tokens compatible with themselves (§17.2), the deallocations of the allocations
of the root places directly owned by the exiting frame are `ok` raw steps, those allocations are
dead afterwards, and `Repr` holds after the step. The storage owned by those places is not
deallocated (§73: "Exiting does not entail automatic physical deallocation of all dead
places"). -/
theorem r6_exit {Ty : Type} {k : K} {C : Nat → Nat → Prop} {ObR : Machine.ReadOblSpec Ty}
    {ObW : Machine.WriteOblSpec Ty} {L : Layout} {rtok : Nat → Nat} {s3 s3' : S3}
    {s2 : Machine.State} (hR : Repr L rtok s3 s2) (hw : WF3 s3) (h : ExitStep k s3 (.ok s3'))
    (htc : ∀ r, C (rtok r) (rtok r)) :
    Machine.Exec C ObR ObW (exitOps L rtok s3) s2 (run s2 (exitOps (Ty := Ty) L rtok s3)) ∧
      (∀ r ∈ exitRoots s3, AllocP (run s2 (exitOps (Ty := Ty) L rtok s3)) (L r).alloc
        (·.live = false)) ∧
      Repr L rtok s3' (run s2 (exitOps (Ty := Ty) L rtok s3)) := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  have hF : s3.F ≠ [] := fun e => hpre.hasCaller (by rw [e]; rfl)
  have hpw : (exitRoots s3).Pairwise (fun r r' => (L r).alloc ≠ (L r').alloc) :=
    ((range_pairwise _).filter _).imp_of_mem fun {r r'} hr hr' hlt =>
      hR.inj r r' (mem_exitRoots.1 hr).1 (mem_exitRoots.1 hr').1 (Nat.ne_of_lt hlt)
  have hlive : ∀ r ∈ exitRoots s3, AllocP s2 (L r).alloc
      fun a => a.live = true ∧ a.freeAuth = some (rtok r) := fun r hr => by
    obtain ⟨hrt, ho, hd⟩ := mem_exitRoots.1 hr
    cases hpl : s3.P[r]? with
    | none => rw [hpl] at ho; exact ho.elim
    | some pl =>
      rw [hpl] at ho
      exact (hR.live r hrt (.frame hpl hd ho (top_mem hF))).and (hR.tokens r hrt)
  obtain ⟨hok, hkeep, hdead⟩ := deallocOps_run (C := C) (ObR := ObR) (ObW := ObW) htc _ s2 hpw hlive
  have hex := exec_of_along _ _ hok
  refine ⟨hex, hdead, hR.transport (hex.admissible hR.adm) (dom_run _ _ hR.adm.wf) rfl rfl
    (fun r hr hu => ?_) fun l _ _ hi => .inl hi⟩
  have hu0 : s3.Usable r := S3.Usable.mono (s := s3) (s' := exitEff s3) rfl
    (fun f h => List.mem_of_mem_tail h) (fun _ h => h) hu
  have hnot : r ∉ exitRoots s3 := fun hm => by
    obtain ⟨-, ho, -⟩ := mem_exitRoots.1 hm
    have hnd := hw.frames.2.1
    cases hu with
    | frame hpl _ ho' hf =>
      change s3.P[r]? = some _ at hpl
      rw [hpl] at ho; simp only [OptP] at ho; rw [ho] at ho'; cases ho'
      have ht : s3.top ∈ s3.F.tail := hf
      unfold S3.top at ht
      cases hFe : s3.F with
      | nil => exact hF hFe
      | cons f F =>
        rw [hFe] at ht hnd
        exact (List.nodup_cons.1 hnd).1 ht
    | place hpl _ ho' _ =>
      change s3.P[r]? = some _ at hpl
      rw [hpl] at ho; simp only [OptP] at ho; rw [ho] at ho'; cases ho'
  obtain ⟨a, ha, hla⟩ := hR.live r hr hu0
  refine ⟨a, ?_, hla⟩
  change (run s2 (deallocOps (Ty := Ty) L rtok (exitRoots s3))).allocs _ = _
  rw [hkeep _ fun r' hr' e => hR.inj r' r (mem_exitRoots.1 hr').1 hr
    (fun e' => hnot (e' ▸ hr')) e, ha]

/-- Instantiation of `K.FreeCompat(place, auth)` (§80, §70.2, §82.4): the presented authority is
compatible, under the deallocation compatibility `C` of the memory machine (§17 ¶2), with the
token recorded for the allocation of the place. -/
def FreeCompatInst (C : Nat → Nat → Prop) (rtok : Nat → Nat) (p auth : Nat) : Prop :=
  C auth (rtok p)

/-- The place of an `ok` `free` is a usable root place (§70.1, §70.3 under `WF3` and `NoDangling`,
§54: the exercisable `Modify` over its footprint, which is nonempty, is held by an active
authority covering one of its leaves). -/
theorem free_usable {k : K} {s3 : S3} {p auth : Nat} (hw : WF3 s3) (hnd : NoDangling s3)
    (hpre : FreePre k s3 p auth) : RootPlace s3.P p ∧ s3.Usable p := by
  have hp : p < s3.P.length ∧ parentOf s3.P p = none := by
    have h := hpre.ownedRoot
    unfold OwnedRoot at h
    cases hpl : s3.P[p]? with
    | none => rw [hpl] at h; exact h.elim
    | some pl =>
      rw [hpl] at h
      exact ⟨lt_of_getElem? hpl, by simp [parentOf, hpl, h.1]⟩
  refine ⟨hp, ?_⟩
  obtain ⟨l, hl⟩ := exists_mem_footprint hw (s3.P.length - p + 1) p (Nat.lt_succ_self _) hp.1
  obtain ⟨b, -, -, hall⟩ := hpre.right
  have hal := hall l hl
  unfold Allows OptP at hal
  split at hal
  · rename_i e he
    obtain ⟨y, hy, ya, yl, -⟩ := effective_some he
    exact Decidable.of_not_not fun hnu => hnd b y hy ya p hnu l hl yl
  · exact hal.elim

/-- The raw operation realizing `free(place, auth)` (§70, §82.4): one deallocation of the
allocation of the root place, presenting `auth`. -/
def freeOps {Ty : Type} (L : Layout) (p auth : Nat) : List (Machine.Op Ty) :=
  [.dealloc (L p).alloc auth]

/-- `freeSound_derived` (§82.4, §70.2, §17, §80 `FreeCompat`, `Deallocable`): under `Repr`,
`WF3`, `NoDangling` and the preconditions of `free`, when `K.FreeCompat` is instantiated by
`FreeCompatInst`, the raw deallocation of the allocation of the place with the authority `auth` has
the conditions of §17: the allocation is live and deallocatable (it records a token, so
`K.Deallocable(place)` is justified) and `auth` is compatible with its token. -/
theorem freeSound_derived {k : K} {C : Nat → Nat → Prop} {L : Layout} {rtok : Nat → Nat}
    {s3 : S3} {s2 : Machine.State} {p auth : Nat} (hR : Repr L rtok s3 s2) (hw : WF3 s3)
    (hnd : NoDangling s3) (hpre : FreePre k s3 p auth)
    (hinst : k.FreeCompat p auth → FreeCompatInst C rtok p auth) :
    Machine.CanDealloc C s2 (L p).alloc auth := by
  obtain ⟨hrt, hu⟩ := free_usable hw hnd hpre
  obtain ⟨a, ha, hla, hfa⟩ := (hR.live p hrt hu).and (hR.tokens p hrt)
  exact ⟨a, ha, hla, _, hfa, hinst hpre.freeCompat⟩

/-- Realization of `free` (§82 preamble, §82.4, §70, §17): under `Repr`, `WF3`, `NoDangling`, an
`ok` step of `free(place, auth)` and the instantiation of `K.FreeCompat` (§80), the deallocation
of the allocation of the place is an `ok` raw step, the allocation is dead afterwards, and `Repr`
holds after the step. Storage owned by the place dies without deallocation (§70 effect). -/
theorem r6_free {Ty : Type} {k : K} {C : Nat → Nat → Prop} {ObR : Machine.ReadOblSpec Ty}
    {ObW : Machine.WriteOblSpec Ty} {L : Layout} {rtok : Nat → Nat} {s3 s3' : S3}
    {s2 : Machine.State} {p auth : Nat} (hR : Repr L rtok s3 s2) (hw : WF3 s3)
    (hnd : NoDangling s3) (h : FreeStep k p auth s3 (.ok s3'))
    (hinst : k.FreeCompat p auth → FreeCompatInst C rtok p auth) :
    Machine.Exec C ObR ObW (freeOps L p auth) s2 (run s2 (freeOps (Ty := Ty) L p auth)) ∧
      AllocP (run s2 (freeOps (Ty := Ty) L p auth)) (L p).alloc (·.live = false) ∧
      Repr L rtok s3' (run s2 (freeOps (Ty := Ty) L p auth)) := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  have hcd := freeSound_derived hR hw hnd hpre hinst
  have hrt := (free_usable hw hnd hpre).1
  have hex : Machine.Exec C ObR ObW (freeOps L p auth) s2 (run s2 (freeOps (Ty := Ty) L p auth)) :=
    exec_of_along _ _ ⟨.dealloc (.ok hcd), trivial⟩
  obtain ⟨a, ha, -⟩ := hcd
  refine ⟨hex, ⟨{ a with live := false }, ?_, rfl⟩, hR.transport (hex.admissible hR.adm)
    (dom_run _ _ hR.adm.wf) rfl rfl (fun r hr hu => ?_) fun l _ _ hi => .inl hi⟩
  · show (s2.dealloc (L p).alloc).allocs _ = _
    rw [dealloc_allocs, ite_eq_left rfl, ha]; rfl
  · have hrp : r ≠ p := fun e => by
      subst e
      cases hu with
      | frame _ hd _ _ | place _ hd _ _ =>
        simp only [freeEff, cleanup, freeS, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hd
        exact hd.2 (.inl ⟨hrt.1, .inl rfl⟩)
    have hu0 : s3.Usable r := S3.Usable.mono (s := s3) (s' := freeEff s3 p) rfl (fun _ h => h)
      (fun q h => by
        simp only [freeEff, cleanup, freeS, Bool.or_eq_false_iff] at h; exact h.1) hu
    obtain ⟨b, hb, hbl⟩ := hR.live r hr hu0
    exact ⟨b, by show (s2.dealloc (L p).alloc).allocs _ = _
                 rw [dealloc_allocs, ite_eq_right (hR.inj r p hr hrt hrp), hb], hbl⟩

/-! ## Bytes of a range (§10, §20.2) -/

/-- The bytes of the range of place `l` in `s2`, as a representation: value and provenance of each
initialized byte, `(0, none)` for an uninitialized or unregistered one (§10 ¶2, §20.2 ¶1). -/
def bytesOf (s2 : Machine.State) (L : Layout) (l : Nat) : Nat → UInt8 × Option Nat := fun i =>
  match s2.allocs (L l).alloc with
  | some a => match a.bytes ((L l).off + i) with
    | .init v pv => (v, pv)
    | .uninit => (0, none)
  | none => (0, none)

/-- After the write of `w` into the range of leaf `l`, the bytes of the range are those of `w`
(§16 ¶2, ¶5). -/
theorem bytesOf_write {s2 : Machine.State} {L : Layout} {l : Nat} {w : Nat → UInt8 × Option Nat}
    (h : AllocP s2 (L l).alloc fun _ => True) {i : Nat} (hi : i < (L l).len) :
    bytesOf (s2.write (leafAcc s2 L .write l) w) L l i = w i := by
  obtain ⟨a, ha, -⟩ := h
  have he : (s2.write (leafAcc s2 L .write l) w).allocs (L l).alloc =
      some (a.write (L l).off (L l).len w) := by
    rw [write_allocs, leafAcc_of ha]
    simp only [↓reduceIte, ha, Option.map_some, Nat.add_sub_cancel_left]
  simp only [bytesOf, he, Machine.Alloc.write_bytes_in a w hi]

/-! ## Pointers written by `store` (§82.2, §82.3) -/

/-- Encoding of references into bytes (§82.3 "an appropriate representation"; encodings belong to
Spec 11, §81): a reference occupies `size` bytes; `enc addr prov i` is its `i`-th byte for the
address `addr` and the provenance `prov`; `decode` reads an address back from a representation and
reads only its first `size` bytes. -/
structure PtrEnc where
  /-- §82.3: number of bytes of a reference. -/
  size : Nat
  /-- §82.3, §10 ¶4: byte `i` of the reference to `addr` with provenance `prov`. -/
  enc : Nat → Option Nat → Nat → UInt8 × Option Nat
  /-- §82.3: the address read back from a representation. -/
  decode : (Nat → UInt8 × Option Nat) → Nat
  /-- `decode` reads only the first `size` bytes of a representation (§82.3, §81 Spec 11). -/
  reads : ∀ f g, (∀ i, i < size → f i = g i) → decode f = decode g

/-- Obligation of the encoding for a reference to `addr` with provenance `prov` (§82.3; Spec 11,
§81: address width and encodings are not fixed here): it decodes back to `addr` and every byte
carries the provenance `prov` (§10 ¶4). -/
def PtrEncAt (pe : PtrEnc) (addr : Nat) (prov : Option Nat) : Prop :=
  pe.decode (pe.enc addr prov) = addr ∧ ∀ i, (pe.enc addr prov i).2 = prov

/-- The allocation of the effective anchor of authority `a` (§44, §82.3; provenance rule recorded
for §82.3): the allocation of the root authority reached along its origin chain, read on the first
leaf of its footprint. -/
def anchorAlloc (L : Layout) (s3 : S3) (a : Nat) : Nat :=
  (L ((s3.afp (s3.effAnchor a)).headD 0)).alloc

/-- Smallest value of `f` over a list, starting from `m` (§82.3; lowest-address rule). -/
def minOver (f : Nat → Nat) : Nat → List Nat → Nat
  | m, [] => m
  | m, l :: ls => minOver f (min m (f l)) ls

/-- `minOver` is at most the start and at most `f` on the list (§82.3). -/
theorem minOver_le (f : Nat → Nat) :
    ∀ (ls : List Nat) (m : Nat), minOver f m ls ≤ m ∧ ∀ l ∈ ls, minOver f m ls ≤ f l
  | [], m => ⟨Nat.le_refl m, fun _ h => nomatch h⟩
  | l :: ls, m => by
    obtain ⟨h1, h2⟩ := minOver_le f ls (min m (f l))
    refine ⟨Nat.le_trans h1 (Nat.min_le_left _ _), fun l' hl' => ?_⟩
    rcases List.mem_cons.1 hl' with rfl | hl'
    · exact Nat.le_trans h1 (Nat.min_le_right _ _)
    · exact h2 l' hl'

/-- `minOver` is the start or a value of `f` on the list (§82.3). -/
theorem minOver_mem (f : Nat → Nat) :
    ∀ (ls : List Nat) (m : Nat), minOver f m ls = m ∨ ∃ l ∈ ls, minOver f m ls = f l
  | [], m => .inl rfl
  | l :: ls, m => by
    simp only [minOver]
    rcases minOver_mem f ls (min m (f l)) with h | ⟨l', hl', h⟩
    · rw [h]
      rcases Nat.le_total m (f l) with hle | hle
      · exact .inl (Nat.min_eq_left hle)
      · exact .inr ⟨l, List.mem_cons_self .., Nat.min_eq_right hle⟩
    · exact .inr ⟨l', List.mem_cons_of_mem _ hl', h⟩

/-- Address of the reference to the region of authority `a` in `s2` (§82.3, address rules recorded
for §82.3): the lowest address among the leaves of the region with a nonzero size; for the empty
region, the base of the allocation of the effective anchor. `none` for a nonempty region whose
leaves all have size zero: neither rule covers it. -/
def ptrAddr (s2 : Machine.State) (L : Layout) (s3 : S3) (a : Nat) : Option Nat :=
  match (s3.afp a).filter (fun l => decide (0 < (L l).len)) with
  | l :: ls => some (minOver (leafAddr s2 L) (leafAddr s2 L l) ls)
  | [] => if s3.afp a = [] then some (baseOf s2 (anchorAlloc L s3 a)) else none

/-- The region of authority `a` is empty or has a leaf of nonzero size: the domain where the
the address rules recorded for §82.3 define the address of a reference. -/
def PtrDecided (L : Layout) (s3 : S3) (a : Nat) : Prop :=
  s3.afp a = [] ∨ ∃ l ∈ s3.afp a, 0 < (L l).len

/-- Decidability of `PtrDecided` (§82.3). -/
instance (L : Layout) (s3 : S3) (a : Nat) : Decidable (PtrDecided L s3 a) := by
  unfold PtrDecided; infer_instance

/-- The address of a reference is defined exactly on `PtrDecided` (§82.3). -/
theorem ptrAddr_isSome {s2 : Machine.State} {L : Layout} {s3 : S3} {a : Nat}
    (h : PtrDecided L s3 a) : ∃ ad, ptrAddr s2 L s3 a = some ad := by
  unfold ptrAddr
  split
  · exact ⟨_, rfl⟩
  · rename_i he
    rcases h with h | ⟨l, hl, hpos⟩
    · exact ⟨_, by rw [ite_eq_left h]⟩
    · have : l ∈ (s3.afp a).filter (fun l => decide (0 < (L l).len)) :=
        List.mem_filter.2 ⟨hl, by simpa using hpos⟩
      rw [he] at this; cases this

/-- The raw operation realizing `store(authority, target)` (§82.3, §65): one write into the range
of the leaf `target` of the reference to the region of the authority, with the address of
`ptrAddr` and the provenance of the allocation of its effective anchor (address rules recorded
for §82.3). No operation when the address is undefined (outside `PtrDecided`). -/
def storeOps {Ty : Type} (pe : PtrEnc) (s2 : Machine.State) (L : Layout) (ty : Nat → Ty) (s3 : S3)
    (a p : Nat) : List (Machine.Op Ty) :=
  match ptrAddr s2 L s3 a with
  | some ad => writeOps s2 L ty (fun _ => pe.enc ad (some (anchorAlloc L s3 a))) [p]
  | none => []

/-- The target of an `ok` `store` is a leaf of a usable place (§65.2). -/
theorem store_target {s3 : S3} {a p : Nat} (hpre : StorePre s3 a p) : LeafOfUsable s3 p :=
  ⟨p, List.mem_range.2 hpre.usable.lt, hpre.usable,
    mem_footprint.2 ⟨hpre.usable.lt, hpre.leaf, hpre.usable.lt, .inl rfl⟩⟩

/-- Realization of `store` (§82 preamble, §82.3, §65, §16): under `Repr`, `WF3`, an `ok` step of
`store(authority, target)` whose region has a reference address (`PtrDecided`, address rules)
and the parametric obligations of the write, the write of the reference into the range of
`target` is an `ok` raw step, and `Repr` holds after the step. `PtrDecided` is not a clause of
the spec: it excludes the nonempty regions whose leaves all have size zero, for which no address
rule is recorded (§82.3 fixes no address). -/
theorem r6_store {Ty : Type} {C : Nat → Nat → Prop} {ObR : Machine.ReadOblSpec Ty}
    {ObW : Machine.WriteOblSpec Ty} {ty : Nat → Ty} {pe : PtrEnc} {L : Layout} {rtok : Nat → Nat}
    {s3 s3' : S3} {s2 : Machine.State} {a p : Nat} (hR : Repr L rtok s3 s2) (hw : WF3 s3)
    (h : StoreStep a p s3 (.ok s3')) (hpd : PtrDecided L s3 a)
    (hob : OblAlong ObR ObW s2 (storeOps pe s2 L ty s3 a p)) :
    Machine.Exec C ObR ObW (storeOps pe s2 L ty s3 a p) s2 (run s2 (storeOps pe s2 L ty s3 a p)) ∧
      Repr L rtok s3' (run s2 (storeOps pe s2 L ty s3 a p)) := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  obtain ⟨ad, had⟩ := ptrAddr_isSome (s2 := s2) hpd
  simp only [storeOps, had] at hob ⊢
  refine writes_repr hR hw (fun l hl => by rw [List.mem_singleton.1 hl]; exact store_target hpre)
    hob ?_ ?_ ?_ ?_ <;> unfold storeEff <;> split
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · intro l hl
    dsimp only at hl
    split at hl
    · exact .inr (List.mem_singleton.2 ‹_›)
    · exact .inl hl
  · exact fun l hl => .inl hl


/-- An element without link of `i :: chain` is the last element of that chain (§42, §44: the
effective anchor is the root reached along the origin chain). -/
theorem chainF_last {org : Nat → Option Nat} :
    ∀ k i x, (x = i ∨ x ∈ chainF org k i) → org x = none → x = (chainF org k i).getLastD i
  | 0, i, x, h, _ => by
    rcases h with rfl | h
    · rfl
    · simp [chainF] at h
  | k + 1, i, x, h, hx => by
    cases ho : org i with
    | none =>
      have e : chainF org (k + 1) i = [] := chainF_none ho (k + 1)
      rw [e] at h ⊢
      rcases h with rfl | h
      · rfl
      · simp at h
    | some o =>
      by_cases hlt : o < i
      · have e : chainF org (k + 1) i = o :: chainF org k o := by simp [chainF, ho, hlt]
        rw [e] at h ⊢
        rcases h with rfl | h
        · rw [hx] at ho; cases ho
        · rw [List.getLastD_cons]
          exact chainF_last k o x (List.mem_cons.1 h) hx
      · have e : chainF org (k + 1) i = [] := by simp [chainF, ho, hlt]
        rw [e] at h ⊢
        rcases h with rfl | h
        · rw [hx] at ho; cases ho
        · simp at h

/-- The footprint of the effective anchor of an authority covering a leaf is the footprint of the
root place of that leaf (§44, §49.6 `RootChain`). -/
theorem effAnchor_footprint {s3 : S3} (hw : WF3 s3) {a l : Nat} {y : Authority}
    (hy : s3.A[a]? = some y) (hl : l ∈ y.footprint) :
    ∃ r, RootPlace s3.P r ∧ partOf s3.P l r ∧
      ∀ l', l' ∈ s3.afp (s3.effAnchor a) ↔ l' ∈ footprint s3.P r := by
  have hlf := (hw.footprints a y hy l hl).2
  obtain ⟨x, z, r, hx, hz, hzo, hr, hlr, hfz⟩ := hw.rootChain a y l hy hl hlf
  have hxo : s3.org x = none := by simp [S3.org, hz, hzo]
  have hxe : x = s3.effAnchor a := chainF_last a a x hx hxo
  refine ⟨r, hr, hlr, fun l' => ?_⟩
  rw [← hxe]
  simp only [S3.afp, hz]
  exact hfz l'

/-- The first element of a nonempty list belongs to it (§82.3). -/
theorem headD_mem {l : List Nat} {x d : Nat} (h : x ∈ l) : l.headD d ∈ l := by
  cases l with
  | nil => cases h
  | cons a l => exact List.mem_cons_self ..

/-- Every leaf covered by an authority lies in the allocation of its effective anchor (§44,
§49.6, §82.1, §82.3). -/
theorem anchorAlloc_eq {L : Layout} {s3 : S3} {s2 : Machine.State} (hlw : LayoutWF L s3 s2)
    (hw : WF3 s3) {a l : Nat} {y : Authority} (hy : s3.A[a]? = some y) (hl : l ∈ y.footprint) :
    anchorAlloc L s3 a = (L l).alloc := by
  obtain ⟨r, hr, hlr, hfp⟩ := effAnchor_footprint hw hy hl
  have hlP := (hw.footprints a y hy l hl)
  have hin : l ∈ s3.afp (s3.effAnchor a) := (hfp l).2 (mem_footprint.2 ⟨hlP.1, hlP.2, hlr⟩)
  have hh := (hfp _).1 (headD_mem (d := 0) hin)
  unfold anchorAlloc
  rw [hlw.alloc_part (mem_footprint.1 hh).2.2, hlw.alloc_part hlr]

/-- Pointer soundness of `store` (§82.2 pointer validity, §82.3 with the reference rules recorded
for it): under `Repr`, `WF3`, `NoDangling`, an `ok` step of `store(authority, target)` whose
reference has the address `ad` (`ptrAddr`), the obligations of the write, a target of pointer size
(pointer-size rule, a stated hypothesis: types and ABI, §81) and the obligation of the encoding for
that reference, the range of `target` after the write decodes to `ad` and carries the provenance
of the allocation of the effective anchor. Every leaf of the region lies in that allocation, which
is live and contains the range of the leaf. For the empty region, `ad` is the base of that
allocation (empty-region rule); otherwise `ad` is the address of a leaf of nonzero size of the
region, the lowest among them (lowest-address rule). -/
theorem pointer_sound_store {Ty : Type} {ty : Nat → Ty} {pe : PtrEnc} {L : Layout}
    {rtok : Nat → Nat}
    {s3 s3' : S3} {s2 : Machine.State} {a p ad : Nat} (hR : Repr L rtok s3 s2) (hw : WF3 s3)
    (hnd : NoDangling s3) (h : StoreStep a p s3 (.ok s3')) (had : ptrAddr s2 L s3 a = some ad)
    (hsz : (L p).len = pe.size) (henc : PtrEncAt pe ad (some (anchorAlloc L s3 a))) :
    pe.decode (bytesOf (run s2 (storeOps (Ty := Ty) pe s2 L ty s3 a p)) L p) = ad ∧
      (∀ i, i < (L p).len →
        (bytesOf (run s2 (storeOps (Ty := Ty) pe s2 L ty s3 a p)) L p i).2 =
          some (anchorAlloc L s3 a)) ∧
      (∀ l ∈ s3.afp a, (L l).alloc = anchorAlloc L s3 a ∧
        AllocP s2 (L l).alloc fun al => al.live = true ∧ (L l).off + (L l).len ≤ al.size) ∧
      (s3.afp a = [] → ad = baseOf s2 (anchorAlloc L s3 a)) ∧
      (s3.afp a ≠ [] → ∃ l ∈ s3.afp a, 0 < (L l).len ∧ ad = leafAddr s2 L l ∧
        ∀ l' ∈ s3.afp a, 0 < (L l').len → ad ≤ leafAddr s2 L l') := by
  obtain ⟨hpre, -⟩ := Guarded.ok_iff.1 h
  obtain ⟨hpP, hpf, hpu⟩ := leaf_of_leafOfUsable hw (store_target hpre)
  obtain ⟨pa, hpa, -⟩ := hR.leaf_live hw hpP hpf hpu
  have hrun : run s2 (storeOps (Ty := Ty) pe s2 L ty s3 a p) =
      s2.write (leafAcc s2 L .write p) (pe.enc ad (some (anchorAlloc L s3 a))) := by
    simp only [storeOps, had, writeOps, List.map_cons, List.map_nil, run, opEff]
  have hbytes : ∀ i, i < (L p).len →
      bytesOf (run s2 (storeOps (Ty := Ty) pe s2 L ty s3 a p)) L p i =
      pe.enc ad (some (anchorAlloc L s3 a)) i := fun i hi => by
    rw [hrun]; exact bytesOf_write ⟨pa, hpa, trivial⟩ hi
  have hy : ∃ y, s3.A[a]? = some y ∧ y.active = true := by
    have h := hpre.derivedHeld
    unfold OptP at h
    split at h
    · exact ⟨_, ‹_›, h.1⟩
    · exact h.elim
  obtain ⟨y, hy, ya⟩ := hy
  have hafp : s3.afp a = y.footprint := by simp [S3.afp, hy]
  refine ⟨?_, fun i hi => by rw [hbytes i hi]; exact henc.2 i, fun l hl => ?_, fun he => ?_,
    fun hne => ?_⟩
  · rw [pe.reads _ _ fun i hi => hbytes i (hsz ▸ hi)]; exact henc.1
  · rw [hafp] at hl
    refine ⟨(anchorAlloc_eq hR.layout hw hy hl).symm, ?_⟩
    obtain ⟨hlP, hlf⟩ := hw.footprints a y hy l hl
    obtain ⟨r, hr, hlr⟩ := exists_rootPlace hw (l + 1) l (Nat.lt_succ_self l) hlP
    have hur : s3.Usable r := Decidable.of_not_not fun hn =>
      hnd a y hy ya r hn l (mem_footprint.2 ⟨hlP, hlf, hlr⟩) hl
    exact hR.leaf_live hw hlP hlf (usable_of_partOf hw (l + 1) l r (Nat.lt_succ_self l) hlr hur)
  · simp only [ptrAddr, he, List.filter_nil, ↓reduceIte, Option.some.injEq] at had
    exact had.symm
  · unfold ptrAddr at had
    split at had
    · rename_i l0 ls hf
      simp only [Option.some.injEq] at had
      have hmem : ∀ x, x ∈ l0 :: ls → x ∈ s3.afp a ∧ 0 < (L x).len := fun x hx => by
        rw [← hf] at hx; simpa using List.mem_filter.1 hx
      obtain ⟨hle0, hle⟩ := minOver_le (leafAddr s2 L) ls (leafAddr s2 L l0)
      have hlow : ∀ l' ∈ s3.afp a, 0 < (L l').len → ad ≤ leafAddr s2 L l' := by
        intro l' hl' hpos
        have : l' ∈ l0 :: ls := by rw [← hf]; exact List.mem_filter.2 ⟨hl', by simpa using hpos⟩
        rw [← had]
        rcases List.mem_cons.1 this with rfl | h'
        · exact hle0
        · exact hle l' h'
      rcases minOver_mem (leafAddr s2 L) ls (leafAddr s2 L l0) with e | ⟨l', hl', e⟩
      · obtain ⟨h1, h2⟩ := hmem l0 (List.mem_cons_self ..)
        exact ⟨l0, h1, h2, by rw [← had, e], hlow⟩
      · obtain ⟨h1, h2⟩ := hmem l' (List.mem_cons_of_mem _ hl')
        exact ⟨l', h1, h2, by rw [← had, e], hlow⟩
    · split at had
      · exact absurd ‹_› hne
      · cases had


/-! ## Transfer (§63, §82.2, §82.3) -/

/-- Pairs of corresponding leaves of a transfer (§63.2, §63 effect): each leaf `l` of `src` with
its corresponding part `corr(l)` of `dst`. -/
def transferPairs (P : List Place) (src dst : Nat) : List (Nat × Nat) :=
  (footprint P src).filterMap fun l => (corr P src dst l).map fun l' => (l, l')

/-- Membership in `transferPairs` (§63.2). -/
theorem mem_transferPairs {P : List Place} {src dst l l' : Nat} :
    (l, l') ∈ transferPairs P src dst ↔ l ∈ footprint P src ∧ corr P src dst l = some l' := by
  simp only [transferPairs, List.mem_filterMap]
  constructor
  · rintro ⟨x, hx, h⟩
    cases hc : corr P src dst x with
    | none => rw [hc] at h; cases h
    | some y => rw [hc] at h; simp only [Option.map_some, Option.some.injEq,
        Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨hx, hc⟩
  · rintro ⟨hl, hc⟩
    exact ⟨l, hl, by rw [hc]; rfl⟩

/-- The raw operations realizing the copy of the values of a transfer (§63 effect, §82.3; the
realization chosen for §10 ¶6: a read of the source range, then a write of the bytes read, with
their provenance, into the destination range): for each pair `(l, l')`, a read of `l` at type
`ty l` and a write of its bytes into `l'` at type `ty l'`. -/
def copyOps {Ty : Type} (L : Layout) (ty : Nat → Ty) : Machine.State → List (Nat × Nat) →
    List (Machine.Op Ty)
  | _, [] => []
  | s2, (l, l') :: ps => .read (leafAcc s2 L .read l) (ty l) ::
      .write (leafAcc s2 L .write l') (ty l') (bytesOf s2 L l) ::
      copyOps L ty (s2.write (leafAcc s2 L .write l') (bytesOf s2 L l)) ps

/-- The copies are `ok` raw steps when the source ranges are live, contained and initialized and
the destination ranges live and contained, under the parametric obligations (§15, §16); the
destination ranges are initialized afterwards (§16 ¶2). -/
theorem copyOps_run {Ty : Type} {C : Nat → Nat → Prop} {ObR : Machine.ReadOblSpec Ty}
    {ObW : Machine.WriteOblSpec Ty} {L : Layout} {ty : Nat → Ty} :
    ∀ (ps : List (Nat × Nat)) (s2 : Machine.State), Machine.WF s2 →
      (∀ q ∈ ps, AllocP s2 (L q.1).alloc fun a => a.live = true ∧
        (L q.1).off + (L q.1).len ≤ a.size ∧ a.InitRange (L q.1).off (L q.1).len) →
      (∀ q ∈ ps, AllocP s2 (L q.2).alloc fun a => a.live = true ∧
        (L q.2).off + (L q.2).len ≤ a.size) →
      OblAlong ObR ObW s2 (copyOps L ty s2 ps) →
      Along (OkAt C ObR ObW) s2 (copyOps L ty s2 ps) ∧
        ∀ q ∈ ps, AllocP (run s2 (copyOps L ty s2 ps)) (L q.2).alloc
          fun a => a.InitRange (L q.2).off (L q.2).len
  | [], _, _, _, _, _ => ⟨trivial, fun _ h => nomatch h⟩
  | (l, l') :: ps, s2, hwf, hsrc, hdst, hob => by
    obtain ⟨a, ha, hla, hsa, hia⟩ := hsrc (l, l') (List.mem_cons_self ..)
    obtain ⟨b, hb, hlb, hsb⟩ := hdst (l, l') (List.mem_cons_self ..)
    have hwf₁ : Machine.WF (s2.write (leafAcc s2 L .write l') (bytesOf s2 L l)) :=
      Machine.write_wf hwf _ _
    have hd₁ : Dom s2 (s2.write (leafAcc s2 L .write l') (bytesOf s2 L l)) :=
      dom_opEff (Ty := Ty) hwf (.write (leafAcc s2 L .write l') (ty l') (bytesOf s2 L l))
    have hkeep : ∀ (i : Nat) (p : Machine.Alloc → Prop), AllocP s2 i
        (fun a => a.live = true ∧ p a) →
        (∀ a a' : Machine.Alloc, a'.base = a.base → a'.size = a.size →
          (∀ j, a.bytes j ≠ .uninit → a'.bytes j ≠ .uninit) → p a → p a') →
        AllocP (s2.write (leafAcc s2 L .write l') (bytesOf s2 L l)) i
          (fun a => a.live = true ∧ p a) := by
      intro i p ⟨c, hc, hcl, hcp⟩ hp
      obtain ⟨c', hc', e1, e2, -, hb'⟩ := hd₁ i c hc
      have := live_opEff (Ty := Ty) (o := .write (leafAcc s2 L .write l') (ty l') (bytesOf s2 L l))
        hwf trivial ⟨c, hc, hcl⟩
      obtain ⟨c'', hc'', hcl''⟩ := this
      change (s2.write (leafAcc s2 L .write l') (bytesOf s2 L l)).allocs i = _ at hc''
      rw [hc'] at hc''; cases hc''
      exact ⟨c', hc', hcl'', hp c c' e1 e2 hb' hcp⟩
    have hsrc₁ := fun q (hq : q ∈ ps) => hkeep _ _ (hsrc q (List.mem_cons_of_mem _ hq))
      fun a a' e1 e2 hb ⟨h1, h2⟩ => ⟨e2 ▸ h1, fun j hj => hb _ (h2 j hj)⟩
    have hdst₁ := fun q (hq : q ∈ ps) => hkeep _ _ (hdst q (List.mem_cons_of_mem _ hq))
      fun a a' _ e2 _ h1 => e2 ▸ h1
    obtain ⟨ih1, ih2⟩ := copyOps_run (C := C) ps _ hwf₁ hsrc₁ hdst₁ hob.2.2
    have hrd := Machine.ReadStep.ok (ObR := ObR) (t := ty l) (s := s2)
      (ac := leafAcc s2 L .read l) (by rw [leafAcc_of ha]; exact ha)
      ⟨canRead_leaf ha hla hsa hia, hob.1⟩
    refine ⟨⟨.read hrd, .write (.ok ⟨canWrite_leaf hb hlb hsb, hob.2.1⟩), ih1⟩, fun q hq => ?_⟩
    rcases List.mem_cons.1 hq with rfl | hq
    · exact (write_leaf_init ⟨b, hb, trivial⟩).dom_init (dom_run _ _ hwf₁)
    · exact ih2 q hq

/-- The copies contain no deallocation (§16). -/
theorem copyOps_noDealloc {Ty : Type} (L : Layout) (ty : Nat → Ty) :
    ∀ (s2 : Machine.State) (ps : List (Nat × Nat)), ∀ o ∈ copyOps L ty s2 ps, NoDealloc o
  | _, [], _, h => nomatch h
  | s2, (l, l') :: ps, o, h => by
    rcases List.mem_cons.1 h with rfl | h
    · trivial
    rcases List.mem_cons.1 h with rfl | h
    · trivial
    · exact copyOps_noDealloc L ty _ ps o h

/-- The raw operations realizing `transfer(source, destination)` (§63, §82.2, §82.3): the copies of
the corresponding leaves. -/
def transferOps {Ty : Type} (L : Layout) (ty : Nat → Ty) (s2 : Machine.State) (s3 : S3)
    (src dst : Nat) : List (Machine.Op Ty) :=
  copyOps L ty s2 (transferPairs s3.P src dst)

/-- A leaf of `src` corresponds to a leaf of `dst` (§63.2: same shape of ordered subtrees). -/
theorem corr_leaf {s3 : S3} (hw : WF3 s3) {src dst l l' : Nat} (hd : dst < s3.P.length)
    (hsh : SameShape s3.P src dst) (hl : l ∈ footprint s3.P src)
    (hc : corr s3.P src dst l = some l') : l' ∈ footprint s3.P dst := by
  obtain ⟨hlP, hlf, hls⟩ := mem_footprint.1 hl
  have hp := corr_partOf hw hd (l + 1) l l' (Nat.lt_succ_self l) hc
  have hk := hsh.1 l (List.mem_range.2 hlP) hls
  rw [hc] at hk; simp only [OptP] at hk
  rw [kids_nil_iff.2 hlf] at hk
  exact mem_footprint.2 ⟨hp.1, kids_nil_iff.1 (List.eq_nil_of_length_eq_zero hk), hp⟩

/-- Every leaf of `dst` corresponds to a leaf of `src` (§63.2: "all nodes are matched"). -/
theorem corr_leaf_back {s3 : S3} {src dst z : Nat} (hsh : SameShape s3.P src dst)
    (hz : z ∈ footprint s3.P dst) : ∃ l, (l, z) ∈ transferPairs s3.P src dst := by
  obtain ⟨hzP, hzf, hzd⟩ := mem_footprint.1 hz
  obtain ⟨r, hr, hrs, hc⟩ := hsh.2 z (List.mem_range.2 hzP) hzd
  have hk := hsh.1 r hr hrs
  rw [hc] at hk; simp only [OptP] at hk
  rw [kids_nil_iff.2 hzf] at hk
  exact ⟨r, mem_transferPairs.2 ⟨mem_footprint.2 ⟨List.mem_range.1 hr,
    kids_nil_iff.1 (List.eq_nil_of_length_eq_zero hk.symm), hrs⟩, hc⟩⟩

/-- Realization of `transfer` (§82 preamble, §82.2, §82.3, §63, §16): under `Repr`, `WF3`, an `ok`
step of `transfer(source, destination)` and the parametric obligations along the copies, the
reads of the source leaves and the writes of their bytes into the corresponding destination
leaves are `ok` raw steps, and `Repr` holds after the step. No allocation is created, moved or
deallocated (§63 effect: storage not owned by a moved part does not move). -/
theorem r6_transfer {Ty : Type} {k : K} {C : Nat → Nat → Prop} {ObR : Machine.ReadOblSpec Ty}
    {ObW : Machine.WriteOblSpec Ty} {ty : Nat → Ty} {L : Layout} {rtok : Nat → Nat}
    {s3 s3' : S3} {s2 : Machine.State} {src dst : Nat} (hR : Repr L rtok s3 s2) (hw : WF3 s3)
    (h : TransferStep k src dst s3 (.ok s3'))
    (hob : OblAlong ObR ObW s2 (transferOps L ty s2 s3 src dst)) :
    Machine.Exec C ObR ObW (transferOps L ty s2 s3 src dst) s2
        (run s2 (transferOps L ty s2 s3 src dst)) ∧
      Repr L rtok s3' (run s2 (transferOps L ty s2 s3 src dst)) := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  have hdl := hpre.dstUsable.lt
  have hsrc : ∀ q ∈ transferPairs s3.P src dst, AllocP s2 (L q.1).alloc fun a => a.live = true ∧
      (L q.1).off + (L q.1).len ≤ a.size ∧ a.InitRange (L q.1).off (L q.1).len := by
    rintro ⟨l, l'⟩ hq
    obtain ⟨hl, -⟩ := mem_transferPairs.1 hq
    obtain ⟨hlP, hlf, hls⟩ := mem_footprint.1 hl
    have hu := usable_of_partOf hw (l + 1) l src (Nat.lt_succ_self l) hls hpre.srcUsable
    obtain ⟨a, ha, h1, h2⟩ := hR.leaf_live hw hlP hlf hu
    obtain ⟨a', ha', h3⟩ := hR.init l hlP hlf (hpre.srcInit l hl)
    rw [ha] at ha'; cases ha'
    exact ⟨a, ha, h1, h2, h3⟩
  have hdst : ∀ q ∈ transferPairs s3.P src dst, AllocP s2 (L q.2).alloc fun a => a.live = true ∧
      (L q.2).off + (L q.2).len ≤ a.size := by
    rintro ⟨l, l'⟩ hq
    obtain ⟨hl, hc⟩ := mem_transferPairs.1 hq
    obtain ⟨hlP, hlf, hld⟩ := mem_footprint.1 (corr_leaf hw hdl hpre.sameShape hl hc)
    exact hR.leaf_live hw hlP hlf
      (usable_of_partOf hw (l' + 1) l' dst (Nat.lt_succ_self l') hld hpre.dstUsable)
  obtain ⟨hok, hinit⟩ := copyOps_run (C := C) _ s2 hR.adm.wf hsrc hdst hob
  have hex := exec_of_along _ _ hok
  refine ⟨hex, hR.transport (hex.admissible hR.adm) (dom_run _ _ hR.adm.wf)
    (transfer_len s3 src dst) (transfer_parentOf s3 src dst) (fun r hr hu => ?_)
    fun l _ _ hi => ?_⟩
  · exact live_run _ _ hR.adm.wf (copyOps_noDealloc L ty s2 _) (hR.live r hr
      (transfer_usable_back hw hpre.srcUsable hu))
  · simp only [transferEff] at hi
    split at hi
    · obtain ⟨l0, hq⟩ := corr_leaf_back hpre.sameShape ‹_›
      exact .inr (hinit (l0, l) hq)
    · split at hi
      · cases hi
      · exact .inl hi

/-! ## Shapes appended to the places (§47, §71.1, §72) -/

section Shape

variable {P : List Place} {hd : Holder} {ls : List (Option Nat × Option Nat × Nat)}

/-- Number of places after appending a shape (§71, §72). -/
theorem shapeP_len (P : List Place) (hd : Holder) (ls : List (Option Nat × Option Nat × Nat)) :
    (shapeP P hd ls).length = P.length + ls.length := by
  simp [shapeP]

/-- Old places are kept by appending a shape (§71, §72). -/
theorem shapeP_get_lt {q : Nat} (hq : q < P.length) : (shapeP P hd ls)[q]? = P[q]? := by
  simp only [shapeP]; exact List.getElem?_append_left hq

/-- The parent of a new place is the parent given by the shape (§71.1, §72). -/
theorem shape_parentOf_new {i : Nat} (hi : i < ls.length) :
    parentOf (shapeP P hd ls) (P.length + i) = (ls[i]?).bind (·.1) := by
  simp only [parentOf, shapeP, List.getElem?_append_right (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left, List.getElem?_map, List.getElem?_range hi, Option.map_some,
    Option.bind_some]

/-- Old places keep their parent (§71, §72). -/
theorem shape_parentOf_lt {q : Nat} (hq : q < P.length) :
    parentOf (shapeP P hd ls) q = parentOf P q := by
  simp only [parentOf, shapeP_get_lt hq]

/-- A new place has a parent among the new places, under `ShapeOK` (§71.1, §72.2). -/
theorem shape_parent_ge (hsh : ShapeOK P.length ls) {q r : Nat} (hq : P.length ≤ q)
    (h : parentOf (shapeP P hd ls) q = some r) : P.length ≤ r := by
  have hql : q < (shapeP P hd ls).length := by
    simp only [parentOf] at h
    cases e : (shapeP P hd ls)[q]? with
    | none => rw [e] at h; cases h
    | some _ => exact lt_of_getElem? e
  rw [shapeP_len] at hql
  have hi : q - P.length < ls.length := by omega
  have hp := shape_parentOf_new (P := P) (hd := hd) hi
  rw [show P.length + (q - P.length) = q by omega, h] at hp
  have := (hsh (q - P.length) (List.mem_range.2 hi)).1
  rw [← hp] at this; exact this.1

/-- An old leaf stays a leaf, under `ShapeOK` (§40, §71.1, §72.2). -/
theorem shape_isLeaf_old (hsh : ShapeOK P.length ls) {l : Nat} (hl : l < P.length) :
    isLeaf (shapeP P hd ls) l ↔ isLeaf P l := by
  constructor
  · intro h r hr; rw [← shape_parentOf_lt hr]; exact h r (by rw [shapeP_len]; omega)
  · intro h r _ e
    by_cases hrn : r < P.length
    · rw [shape_parentOf_lt hrn] at e; exact h r hrn e
    · have := shape_parent_ge hsh (Nat.le_of_not_lt hrn) e; omega

/-- Old root places are the root places of the old places (§40, §71, §72). -/
theorem shape_rootPlace_old {r : Nat} (hr : r < P.length) :
    RootPlace (shapeP P hd ls) r ↔ RootPlace P r := by
  simp only [RootPlace, shape_parentOf_lt hr, shapeP_len]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by omega, h2⟩

/-- A new root place is a root element of the shape (§40, §71, §72). -/
theorem shape_rootPlace_new {r : Nat} (h : RootPlace (shapeP P hd ls) r) (hr : P.length ≤ r) :
    r - P.length ∈ rootIdx ls := by
  obtain ⟨hlt, hn⟩ := h
  rw [shapeP_len] at hlt
  have hi : r - P.length < ls.length := by omega
  have hp := shape_parentOf_new (P := P) (hd := hd) hi
  rw [show P.length + (r - P.length) = r by omega, hn] at hp
  simp only [rootIdx, List.mem_filter, List.mem_range]
  exact ⟨hi, by rw [← hp]; rfl⟩

end Shape

/-! ## New allocations (§9 ¶11, §71, §72, §47, §82.4) -/

/-- Geometry of a new allocation: address space, size, alignment (§9 ¶1). -/
structure Geom where
  /-- §9 ¶1: address space. -/
  space : Nat
  /-- §9 ¶1: extent in bytes. -/
  size : Nat
  /-- §9 ¶1: alignment. -/
  align : Nat

/-- Placement: the base address chosen for a new allocation of geometry `g` in the state `s`
(§9 ¶11, §82.4). -/
abbrev Placement := Machine.State → Geom → Nat

/-- Obligation of a placement (§9 ¶11, §82.4): in every state with fresh identities, for every
valid alignment, the chosen base satisfies the preconditions of raw creation. -/
def PlacementOK (pl : Placement) : Prop :=
  ∀ s g, Machine.WF s → 0 < g.align → Machine.Pow2 g.align →
    Machine.AllocPre s g.space (pl s g) g.size g.align

/-- Obligation of the geometries (§9 ¶1, ¶4): every alignment is strictly positive and a power of
two. -/
def GeomOK (g : Nat → Geom) : Prop := ∀ r, 0 < (g r).align ∧ Machine.Pow2 (g r).align

/-- End of the allocation `i` of `s`, `0` if unregistered (§9 ¶3). -/
def allocEnd (s : Machine.State) (i : Nat) : Nat :=
  ((s.allocs i).map fun a => a.base + a.size).getD 0

/-- Largest end of the allocations of identity below `n` (§9 ¶3). -/
def maxEnd (s : Machine.State) : Nat → Nat
  | 0 => 0
  | n + 1 => max (maxEnd s n) (allocEnd s n)

/-- Every allocation below `n` ends at most at `maxEnd s n` (§9 ¶3). -/
theorem le_maxEnd (s : Machine.State) : ∀ n i, i < n → allocEnd s i ≤ maxEnd s n
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, i, h => by
    simp only [maxEnd]
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
    · exact Nat.le_trans (le_maxEnd s n i h) (Nat.le_max_left _ _)
    · exact Nat.le_max_right _ _

/-- A placement above every registered allocation, on a multiple of the alignment (§9 ¶11; a
witness that `PlacementOK` is satisfiable, `topPlacement_ok`). -/
def topPlacement : Placement := fun s g => g.align * (maxEnd s s.next / g.align + 1)

/-- `topPlacement` satisfies its obligation (§9 ¶11, §82.4). -/
theorem topPlacement_ok : PlacementOK topPlacement := by
  intro s g hwf h0 h2
  refine ⟨hwf _ (Nat.le_refl _), h0, h2, Nat.mul_mod_right _ _, fun i a ha _ _ => ?_⟩
  have hi : i < s.next := Nat.lt_of_not_le fun hle => by rw [hwf i hle] at ha; cases ha
  have he : a.base + a.size ≤ maxEnd s s.next := by
    have := le_maxEnd s s.next i hi; simpa [allocEnd, ha] using this
  have hb := Nat.lt_mul_div_succ (maxEnd s s.next) h0
  exact Machine.rangeDisjoint_iff.2 (.inl (by simp only [topPlacement]; omega))

/-- Justification of `Satisfiable` on the side of the memory machine (§82.4, §71, §9): addresses
are unbounded naturals in this kernel (§9 ¶6), so every allocation of valid alignment has a valid
placement in a state with fresh identities. A defined `fail` of `alloc` (§71) therefore comes from
the provider's contract, never from the machine; address width belongs to §81 (Spec 11). -/
theorem placement_exists {s : Machine.State} (hwf : Machine.WF s) (g : Geom) (h0 : 0 < g.align)
    (h2 : Machine.Pow2 g.align) : ∃ base, Machine.AllocPre s g.space base g.size g.align :=
  ⟨_, topPlacement_ok s g hwf h0 h2⟩

/-- The creations realizing new root places (§71, §72, §47): for each root element `i` of a shape
appended after `n` places, in order, one allocation of geometry `g (n + i)` at the base chosen by
`pl`, recording the token `rtok (n + i)`. -/
def allocOps {Ty : Type} (pl : Placement) (g : Nat → Geom) (rtok : Nat → Nat) (n : Nat) :
    Machine.State → List Nat → List (Machine.Op Ty)
  | _, [] => []
  | s, i :: is => .alloc (g (n + i)).space (pl s (g (n + i))) (g (n + i)).size (g (n + i)).align
      (some (rtok (n + i))) :: allocOps pl g rtok n (s.alloc (g (n + i)).space (pl s (g (n + i)))
        (g (n + i)).size (g (n + i)).align (some (rtok (n + i)))) is

section AllocOps

variable {Ty : Type} (pl : Placement) (g : Nat → Geom) (rtok : Nat → Nat) (n : Nat)

/-- The creations are `ok` under the placement and geometry obligations (§9 ¶11). -/
theorem allocOps_ok {C : Nat → Nat → Prop} {ObR : Machine.ReadOblSpec Ty}
    {ObW : Machine.WriteOblSpec Ty} {pl : Placement} {g : Nat → Geom} (hpl : PlacementOK pl)
    (hg : GeomOK g) : ∀ (is : List Nat) (s : Machine.State), Machine.WF s →
      Along (OkAt C ObR ObW) s (allocOps (Ty := Ty) pl g rtok n s is)
  | [], _, _ => trivial
  | _ :: is, s, h =>
    ⟨.alloc (.ok (hpl s _ h (hg _).1 (hg _).2)),
      allocOps_ok hpl hg is _ (Machine.alloc_wf h _ _ _ _ _)⟩

/-- The creations keep every identity below the counter (§13 ¶3). -/
theorem allocOps_old : ∀ (is : List Nat) (s : Machine.State) (i : Nat), i < s.next →
    (run s (allocOps (Ty := Ty) pl g rtok n s is)).allocs i = s.allocs i
  | [], _, _, _ => rfl
  | _ :: is, s, i, hi => by
    show (run (s.alloc _ _ _ _ _) (allocOps pl g rtok n _ is)).allocs i = _
    rw [allocOps_old is _ i (by simp only [Machine.State.alloc]; omega)]
    simp [Machine.State.alloc, Nat.ne_of_lt hi]

/-- The `j`-th creation registers the identity `next + j`, live, uninitialized, with the geometry
of its root and its token (§9 ¶11, §10 ¶5, §13 ¶1). -/
theorem allocOps_new : ∀ (is : List Nat) (s : Machine.State) (j i : Nat), is[j]? = some i →
    ∃ b, (run s (allocOps (Ty := Ty) pl g rtok n s is)).allocs (s.next + j) =
      some ⟨(g (n + i)).space, b, (g (n + i)).size, (g (n + i)).align, true, fun _ => .uninit,
        some (rtok (n + i))⟩
  | [], _, _, _, h => by simp at h
  | k :: is, s, 0, i, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h
    refine ⟨pl s (g (n + k)), ?_⟩
    show (run (s.alloc _ _ _ _ _) (allocOps pl g rtok n _ is)).allocs _ = _
    rw [allocOps_old pl g rtok n is _ _ (by simp [Machine.State.alloc])]
    simp [Machine.State.alloc]
  | k :: is, s, j + 1, i, h => by
    simp only [List.getElem?_cons_succ] at h
    obtain ⟨b, hb⟩ := allocOps_new is (s.alloc (g (n + k)).space (pl s (g (n + k)))
      (g (n + k)).size (g (n + k)).align (some (rtok (n + k)))) j i h
    refine ⟨b, ?_⟩
    show (run (s.alloc _ _ _ _ _) (allocOps pl g rtok n _ is)).allocs _ = _
    rw [show s.next + (j + 1) = (s.alloc (g (n + k)).space (pl s (g (n + k))) (g (n + k)).size
      (g (n + k)).align (some (rtok (n + k)))).next + j by simp only [Machine.State.alloc]; omega]
    exact hb

/-- The creations contain no deallocation (§9 ¶11). -/
theorem allocOps_noDealloc : ∀ (s : Machine.State) (is : List Nat),
    ∀ o ∈ allocOps (Ty := Ty) pl g rtok n s is, NoDealloc o
  | _, [], _, h => nomatch h
  | _, _ :: is, o, h => by
    rcases List.mem_cons.1 h with rfl | h
    · trivial
    · exact allocOps_noDealloc _ is o h

end AllocOps

/-- Two distinct new leaves in one allocation have disjoint ranges (§23, §82.1). -/
def NewDisjoint (L : Layout) (P' : List Place) (n l l' : Nat) : Prop :=
  n ≤ l → n ≤ l' → isLeaf P' l → isLeaf P' l' → l ≠ l' → (L l).alloc = (L l').alloc →
    Machine.RangeDisjoint (L l).off (L l).len (L l').off (L l').len

/-- Decidability of `NewDisjoint` (§82.1). -/
instance (L : Layout) (P' : List Place) (n l l' : Nat) : Decidable (NewDisjoint L P' n l l') := by
  unfold NewDisjoint; infer_instance

/-- Layout obligations of a shape appended after `n` places, whose root elements `roots` receive
the fresh allocations `next`, `next + 1`, … (§82.1, §71, §72, §47): the `j`-th new root is in the
allocation `next + j`; a new part is in the allocation of its parent; a new leaf is in the
allocation of a new root, within its size; two distinct new leaves in one allocation have
disjoint ranges. -/
structure NewLayout (L : Layout) (P' : List Place) (n next : Nat) (g : Nat → Geom)
    (roots : List Nat) : Prop where
  /-- §82.1: the `j`-th new root lies in the allocation `next + j`. -/
  rootAt : ∀ j < roots.length, OptP (roots[j]?) (fun i => (L (n + i)).alloc = next + j) True
  /-- §82.1: a new part lies in the allocation of its parent. -/
  parts : ∀ q < P'.length, n ≤ q → OptP (parentOf P' q) (fun r => (L q).alloc = (L r).alloc) True
  /-- §82.1: a new leaf lies in the allocation of a new root, within its size. -/
  leaves : ∀ l < P'.length, n ≤ l → isLeaf P' l → ∃ j < roots.length,
    OptP (roots[j]?) (fun i => (L l).alloc = next + j ∧ (L l).off + (L l).len ≤ (g (n + i)).size)
      False
  /-- §23, §82.1: two distinct new leaves in one allocation have disjoint ranges. -/
  disjoint : ∀ l < P'.length, ∀ l' < P'.length, NewDisjoint L P' n l l'

/-- Decidability of `NewLayout` (§82.1). -/
instance (L : Layout) (P' : List Place) (n next : Nat) (g : Nat → Geom) (roots : List Nat) :
    Decidable (NewLayout L P' n next g roots) := by
  haveI d1 : Decidable (∀ j < roots.length,
      OptP (roots[j]?) (fun i => (L (n + i)).alloc = next + j) True) := inferInstance
  haveI d2 : Decidable (∀ q < P'.length, n ≤ q →
      OptP (parentOf P' q) (fun r => (L q).alloc = (L r).alloc) True) := inferInstance
  haveI d3 : Decidable (∀ l < P'.length, n ≤ l → isLeaf P' l → ∃ j < roots.length,
      OptP (roots[j]?) (fun i => (L l).alloc = next + j ∧ (L l).off + (L l).len ≤ (g (n + i)).size)
        False) := inferInstance
  haveI d4 : Decidable (∀ l < P'.length, ∀ l' < P'.length, NewDisjoint L P' n l l') :=
    inferInstance
  exact decidable_of_iff ((∀ j < roots.length,
      OptP (roots[j]?) (fun i => (L (n + i)).alloc = next + j) True) ∧
    (∀ q < P'.length, n ≤ q → OptP (parentOf P' q) (fun r => (L q).alloc = (L r).alloc) True) ∧
    (∀ l < P'.length, n ≤ l → isLeaf P' l → ∃ j < roots.length,
      OptP (roots[j]?) (fun i => (L l).alloc = next + j ∧ (L l).off + (L l).len ≤ (g (n + i)).size)
        False) ∧
    (∀ l < P'.length, ∀ l' < P'.length, NewDisjoint L P' n l l'))
    ⟨fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩, fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩⟩

/-- `Repr` carries over the creation of the allocations of the root places of a shape appended to
the places (§82.1, §82.4, §71, §72, §47, §9 ¶11): the old places keep their parents, usability
(none becomes usable) and initialization; the new leaves are not `Init`; the layout of the new
places satisfies `NewLayout`. The creations are `ok` raw steps. -/
theorem repr_extend {Ty : Type} {C : Nat → Nat → Prop} {ObR : Machine.ReadOblSpec Ty}
    {ObW : Machine.WriteOblSpec Ty} {L : Layout} {rtok : Nat → Nat} {s3 s3' : S3}
    {s2 : Machine.State} {hd : Holder} {ls : List (Option Nat × Option Nat × Nat)}
    {pl : Placement} {g : Nat → Geom} (hR : Repr L rtok s3 s2) (hpl : PlacementOK pl)
    (hg : GeomOK g) (hP : s3'.P = shapeP s3.P hd ls) (hsh : ShapeOK s3.P.length ls)
    (hUold : ∀ q, q < s3.P.length → s3'.Usable q → s3.Usable q)
    (hIold : ∀ l, l < s3.P.length → s3'.I l = s3.I l)
    (hInew : ∀ l, s3.P.length ≤ l → s3'.I l ≠ .init)
    (hlay : NewLayout L s3'.P s3.P.length s2.next g (rootIdx ls)) :
    Machine.Exec C ObR ObW (allocOps pl g rtok s3.P.length s2 (rootIdx ls)) s2
        (run s2 (allocOps (Ty := Ty) pl g rtok s3.P.length s2 (rootIdx ls))) ∧
      Repr L rtok s3' (run s2 (allocOps (Ty := Ty) pl g rtok s3.P.length s2 (rootIdx ls))) := by
  have hex := exec_of_along _ _ (allocOps_ok (C := C) (ObR := ObR) (ObW := ObW) (rtok := rtok)
    (n := s3.P.length) hpl hg (rootIdx ls) s2 hR.adm.wf)
  refine ⟨hex, ?_⟩
  have hwf := hR.adm.wf
  have hold := allocOps_old (Ty := Ty) pl g rtok s3.P.length (rootIdx ls) s2
  have hnew := allocOps_new (Ty := Ty) pl g rtok s3.P.length (rootIdx ls) s2
  have hleaf : ∀ l, l < s3.P.length → (isLeaf s3'.P l ↔ isLeaf s3.P l) := fun l hl => by
    rw [hP]; exact shape_isLeaf_old hsh hl
  have hroot : ∀ r, r < s3.P.length → (RootPlace s3'.P r ↔ RootPlace s3.P r) := fun r hr => by
    rw [hP]; exact shape_rootPlace_old hr
  have hlen : s3'.P.length = s3.P.length + ls.length := by rw [hP, shapeP_len]
  have hpar : ∀ q, q < s3.P.length → parentOf s3'.P q = parentOf s3.P q := fun q hq => by
    rw [hP]; exact shape_parentOf_lt hq
  -- old leaves and roots are in old allocations, below the counter
  have hold_leaf : ∀ l, l < s3.P.length → isLeaf s3.P l → (L l).alloc < s2.next := fun l hl hf =>
    (hR.layout.within l hl hf).lt hwf
  have hold_root : ∀ r, RootPlace s3.P r → (L r).alloc < s2.next := fun r hr =>
    (hR.tokens r hr).lt hwf
  -- new leaves and roots are in new allocations
  have hnew_leaf : ∀ l, s3.P.length ≤ l → l < s3'.P.length → isLeaf s3'.P l →
      ∃ j i, (rootIdx ls)[j]? = some i ∧ (L l).alloc = s2.next + j ∧
        (L l).off + (L l).len ≤ (g (s3.P.length + i)).size := fun l hl1 hl2 hf => by
    obtain ⟨j, hj, hji⟩ := hlay.leaves l hl2 hl1 hf
    cases e : (rootIdx ls)[j]? with
    | none => rw [e] at hji; exact hji.elim
    | some i => rw [e] at hji; exact ⟨j, i, e, hji⟩
  have hnew_root : ∀ r, RootPlace s3'.P r → s3.P.length ≤ r →
      ∃ j, (rootIdx ls)[j]? = some (r - s3.P.length) ∧ (L r).alloc = s2.next + j :=
      fun r hr hr1 => by
    have hm := shape_rootPlace_new (hP ▸ hr) hr1
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hm
    have := hlay.rootAt j (lt_of_getElem? hj)
    rw [hj] at this; simp only [OptP] at this
    rw [show s3.P.length + (r - s3.P.length) = r by omega] at this
    exact ⟨j, hj, this⟩
  refine ⟨hex.admissible hR.adm, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro q r h
    by_cases hq : q < s3.P.length
    · rw [hpar q hq] at h; exact hR.layout.parts q r h
    · have hql : q < s3'.P.length := by
        simp only [parentOf] at h
        cases e : s3'.P[q]? with
        | none => rw [e] at h; cases h
        | some _ => exact lt_of_getElem? e
      have := hlay.parts q hql (Nat.le_of_not_lt hq)
      rw [h] at this; exact this
  · intro l l' hl hl' hf hf' hne he
    by_cases h1 : l < s3.P.length <;> by_cases h2 : l' < s3.P.length
    · exact hR.layout.disjoint l l' h1 h2 ((hleaf l h1).1 hf) ((hleaf l' h2).1 hf') hne he
    · obtain ⟨j, i, -, e, -⟩ := hnew_leaf l' (Nat.le_of_not_lt h2) hl' hf'
      have := hold_leaf l h1 ((hleaf l h1).1 hf); omega
    · obtain ⟨j, i, -, e, -⟩ := hnew_leaf l (Nat.le_of_not_lt h1) hl hf
      have := hold_leaf l' h2 ((hleaf l' h2).1 hf'); omega
    · exact hlay.disjoint l hl l' hl' (Nat.le_of_not_lt h1) (Nat.le_of_not_lt h2) hf hf' hne he
  · intro l hl hf
    by_cases h1 : l < s3.P.length
    · have hf0 := (hleaf l h1).1 hf
      obtain ⟨a, ha, hs⟩ := hR.layout.within l h1 hf0
      exact ⟨a, by rw [hold _ (hold_leaf l h1 hf0), ha], hs⟩
    · obtain ⟨j, i, hji, e, hs⟩ := hnew_leaf l (Nat.le_of_not_lt h1) hl hf
      obtain ⟨b, hb⟩ := hnew j i hji
      exact ⟨_, by rw [e, hb], hs⟩
  · intro r r' hr hr' hne he
    by_cases h1 : r < s3.P.length <;> by_cases h2 : r' < s3.P.length
    · exact hR.inj r r' ((hroot r h1).1 hr) ((hroot r' h2).1 hr') hne he
    · obtain ⟨j, -, e⟩ := hnew_root r' hr' (Nat.le_of_not_lt h2)
      have := hold_root r ((hroot r h1).1 hr); omega
    · obtain ⟨j, -, e⟩ := hnew_root r hr (Nat.le_of_not_lt h1)
      have := hold_root r' ((hroot r' h2).1 hr'); omega
    · obtain ⟨j, hj, e⟩ := hnew_root r hr (Nat.le_of_not_lt h1)
      obtain ⟨j', hj', e'⟩ := hnew_root r' hr' (Nat.le_of_not_lt h2)
      have hjj : j = j' := by omega
      subst hjj
      rw [hj] at hj'; simp only [Option.some.injEq] at hj'
      exact hne (by omega)
  · intro r hr
    by_cases h1 : r < s3.P.length
    · have hr0 := (hroot r h1).1 hr
      obtain ⟨a, ha, hfa⟩ := hR.tokens r hr0
      exact ⟨a, by rw [hold _ (hold_root r hr0), ha], hfa⟩
    · obtain ⟨j, hj, e⟩ := hnew_root r hr (Nat.le_of_not_lt h1)
      obtain ⟨b, hb⟩ := hnew j _ hj
      refine ⟨_, by rw [e, hb], ?_⟩
      simp only [show s3.P.length + (r - s3.P.length) = r by omega]
  · intro r hr hu
    by_cases h1 : r < s3.P.length
    · have hr0 := (hroot r h1).1 hr
      obtain ⟨a, ha, hla⟩ := hR.live r hr0 (hUold r h1 hu)
      exact ⟨a, by rw [hold _ (hold_root r hr0), ha], hla⟩
    · obtain ⟨j, hj, e⟩ := hnew_root r hr (Nat.le_of_not_lt h1)
      obtain ⟨b, hb⟩ := hnew j _ hj
      exact ⟨_, by rw [e, hb], rfl⟩
  · intro l hl hf hi
    by_cases h1 : l < s3.P.length
    · have hf0 := (hleaf l h1).1 hf
      obtain ⟨a, ha, hia⟩ := hR.init l h1 hf0 (by rw [← hIold l h1]; exact hi)
      exact ⟨a, by rw [hold _ (hold_leaf l h1 hf0), ha], hia⟩
    · exact absurd hi (hInew l (Nat.le_of_not_lt h1))


/-- A place of the old places that is usable after a step extending the places, keeping their
death markers and the frames below `nF`, was usable before (§40, §49.3). -/
theorem usable_old {s s' : S3} (hw : WF3 s) (hP : ∀ q < s.P.length, s'.P[q]? = s.P[q]?)
    (hd : ∀ q < s.P.length, s'.dead q = s.dead q) (hF : ∀ f, f < s.nF → f ∈ s'.F → f ∈ s.F) :
    ∀ q, q < s.P.length → s'.Usable q → s.Usable q := by
  intro q hq h
  induction h with
  | @frame q f pl hpl hdq ho hf =>
    rw [hP q hq] at hpl
    exact .frame hpl (by rw [← hd q hq]; exact hdq) ho (hF f (hw.owners.1 q pl f hpl ho) hf)
  | @place q o pl hpl hdq ho _ ih =>
    rw [hP q hq] at hpl
    exact .place hpl (by rw [← hd q hq]; exact hdq) ho (ih (hw.owners.2.1 q pl o hpl ho))

/-- The number of creations is the number of new roots (§71, §72). -/
theorem allocOps_length {Ty : Type} (pl : Placement) (g : Nat → Geom) (rtok : Nat → Nat)
    (n : Nat) : ∀ (s : Machine.State) (is : List Nat),
      (allocOps (Ty := Ty) pl g rtok n s is).length = is.length
  | _, [] => rfl
  | _, _ :: is => by simp only [allocOps, List.length_cons, allocOps_length pl g rtok n _ is]

/-- Realization of `alloc` (§82 preamble, §82.4, §71, §9 ¶11): under `Repr`, `WF3`, an `ok` step
of `alloc(provider, owner, shape)`, a valid placement and geometries, and the layout obligations
of the new places, the creation of one allocation for the new storage root (`oneRoot`, §71) is an
`ok` raw step (`AllocStep`, §71 last paragraph), and `Repr` holds after the step. -/
theorem r6_alloc {Ty : Type} {k : K} {C : Nat → Nat → Prop} {ObR : Machine.ReadOblSpec Ty}
    {ObW : Machine.WriteOblSpec Ty} {L : Layout} {rtok : Nat → Nat} {s3 s3' : S3}
    {s2 : Machine.State} {pr ow : Nat} {ls : LocalShape} {pl : Placement} {g : Nat → Geom}
    (hR : Repr L rtok s3 s2) (hw : WF3 s3) (h : AllocStep k pr ow ls s3 (.ok s3'))
    (hpl : PlacementOK pl) (hg : GeomOK g)
    (hlay : NewLayout L (allocP s3 ow ls) s3.P.length s2.next g (rootIdx ls.toShape)) :
    (allocOps (Ty := Ty) pl g rtok s3.P.length s2 (rootIdx ls.toShape)).length = 1 ∧
    Machine.Exec C ObR ObW (allocOps pl g rtok s3.P.length s2 (rootIdx ls.toShape)) s2
        (run s2 (allocOps (Ty := Ty) pl g rtok s3.P.length s2 (rootIdx ls.toShape))) ∧
      Repr L rtok s3' (run s2 (allocOps (Ty := Ty) pl g rtok s3.P.length s2
        (rootIdx ls.toShape))) := by
  cases h with
  | ok hst _ =>
    refine ⟨by rw [allocOps_length]; exact hst.oneRoot, repr_extend hR hpl hg rfl hst.shapeOK
      (usable_old hw (fun q hq => shapeP_get_lt hq) (fun q hq => ?_) (fun _ _ h => h))
      (fun l hl => ?_) (fun l hl => ?_) hlay⟩
    · simp only [allocEff, Nat.not_le.2 hq, ↓reduceIte]
    · simp only [allocEff, Nat.not_le.2 hl, ↓reduceIte]
    · simp only [allocEff, hl, ↓reduceIte]; exact fun h => by cases h

/-- A `fail` of `alloc` (§71, §58: "no state change") is realized by no raw operation: `Repr` is
kept as is. -/
theorem r6_alloc_fail {Ty : Type} {k : K} {C : Nat → Nat → Prop} {ObR : Machine.ReadOblSpec Ty}
    {ObW : Machine.WriteOblSpec Ty} {L : Layout} {rtok : Nat → Nat} {s3 : S3}
    {s2 : Machine.State} {pr ow : Nat} {ls : LocalShape} (hR : Repr L rtok s3 s2)
    (_h : AllocStep k pr ow ls s3 .fail) :
    Machine.Exec C ObR ObW ([] : List (Machine.Op Ty)) s2 s2 ∧ Repr L rtok s3 s2 :=
  ⟨.nil s2, hR⟩

/-- Realization of `enterFrame` (§82 preamble, §82.5, §72, §9 ¶11): under `Repr`, `WF3`, an `ok`
step of `enterFrame(params, locals)`, a valid placement and geometries, and the layout
obligations of the locals, the creation of one allocation per root local (automatic storage) is a
sequence of `ok` raw steps, and `Repr` holds after the step. -/
theorem r6_enter {Ty : Type} {C : Nat → Nat → Prop} {ObR : Machine.ReadOblSpec Ty}
    {ObW : Machine.WriteOblSpec Ty} {L : Layout} {rtok : Nat → Nat} {s3 s3' : S3}
    {s2 : Machine.State} {ps : List Nat} {ls : LocalShape} {pl : Placement} {g : Nat → Geom}
    (hR : Repr L rtok s3 s2) (hw : WF3 s3) (h : EnterStep ps ls s3 (.ok s3'))
    (hpl : PlacementOK pl) (hg : GeomOK g)
    (hlay : NewLayout L (enterP s3 ls) s3.P.length s2.next g (rootIdx ls.toShape)) :
    Machine.Exec C ObR ObW (allocOps pl g rtok s3.P.length s2 (rootIdx ls.toShape)) s2
        (run s2 (allocOps (Ty := Ty) pl g rtok s3.P.length s2 (rootIdx ls.toShape))) ∧
      Repr L rtok s3' (run s2 (allocOps (Ty := Ty) pl g rtok s3.P.length s2
        (rootIdx ls.toShape))) := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  refine repr_extend hR hpl hg rfl hpre.localsOK
    (usable_old hw (fun q hq => shapeP_get_lt hq) (fun q hq => ?_) (fun f hf h => ?_))
    (fun l hl => ?_) (fun l hl => ?_) hlay
  · simp only [enterEff, Nat.not_le.2 hq, ↓reduceIte]
  · rcases List.mem_cons.1 h with rfl | h
    · exact absurd hf (Nat.lt_irrefl _)
    · exact h
  · simp only [enterEff, Nat.not_le.2 hl, ↓reduceIte]
  · simp only [enterEff, hl, ↓reduceIte]; exact fun h => by cases h

/-! ## Initial state (§47, §10 ¶5, §82.6) -/

/-- The kernel state with no place, before the declared statics (§47; the starting point of
`repr_init`). -/
def S3.base : S3 :=
  { F := [0], nF := 1, P := [], I := fun _ => .uninit, A := [], D := fun _ => [],
    dead := fun _ => false, pin := fun _ => false }

/-- The kernel state without places is represented by the empty memory state (§9 ¶9, §82). -/
theorem repr_base (L : Layout) (rtok : Nat → Nat) : Repr L rtok S3.base Machine.State.empty := by
  refine ⟨Machine.admissible_empty, ⟨fun q r h => ?_, fun l _ hl => ?_, fun l hl => ?_⟩,
    fun r _ hr => ?_, fun r hr => ?_, fun r hr => ?_, fun l hl => ?_⟩
  · simp [parentOf, S3.base] at h
  all_goals first
    | exact absurd hl (Nat.not_lt_zero _)
    | exact absurd hr.1 (Nat.not_lt_zero _)

/-- Static leaves declared `Init` (§47). -/
def initLeaves (statics : Statics) : List Nat :=
  (List.range statics.length).filter fun l =>
    decide (isLeaf (S3.init statics).P l ∧ (S3.init statics).I l = .init)

/-- The raw operations realizing the initial state (§47, §10 ¶5, §82.6): one allocation per root
static, then one write of the declared initial representation `ival l` into each static leaf
declared `Init` (initializing static values is an additional operation, §10 ¶5). -/
def initOps {Ty : Type} (pl : Placement) (g : Nat → Geom) (rtok : Nat → Nat) (L : Layout)
    (ty : Nat → Ty) (ival : Nat → Nat → UInt8 × Option Nat) (statics : Statics) :
    List (Machine.Op Ty) :=
  allocOps pl g rtok 0 Machine.State.empty (rootIdx (statics.map (·.1))) ++
    writeOps (run Machine.State.empty (allocOps (Ty := Ty) pl g rtok 0 Machine.State.empty
      (rootIdx (statics.map (·.1))))) L ty ival (initLeaves statics)

/-- Every registered allocation after creations from a state whose allocations are live is live
(§9 ¶11). -/
theorem allocOps_live {Ty : Type} (pl : Placement) (g : Nat → Geom) (rtok : Nat → Nat) (n : Nat) :
    ∀ (is : List Nat) (s : Machine.State), (∀ i a, s.allocs i = some a → a.live = true) →
      ∀ i a, (run s (allocOps (Ty := Ty) pl g rtok n s is)).allocs i = some a → a.live = true
  | [], _, h => h
  | _ :: is, s, h => allocOps_live pl g rtok n is _ fun i a ha => by
      change (s.alloc _ _ _ _ _).allocs i = some a at ha
      rw [alloc_allocs] at ha
      split at ha
      · cases ha; rfl
      · exact h i a ha

/-- Realization of the initial state (§82 preamble, §47, §82.6, §10 ¶5): under the well-formedness
of the statics declaration (`StaticsOK`, a hypothesis recorded for §47), a valid placement and
geometries, the layout obligations of the statics and the parametric obligations of the
initializing writes, the creations of the static allocations followed by the writes of the static
leaves declared `Init` form an execution of `ok` raw steps from the empty state (§9 ¶9), and
`Repr` holds between `S3.init statics` and the reached state. -/
theorem repr_init {Ty : Type} {C : Nat → Nat → Prop} {ObR : Machine.ReadOblSpec Ty}
    {ObW : Machine.WriteOblSpec Ty} {L : Layout} {rtok : Nat → Nat} {pl : Placement}
    {g : Nat → Geom} {ty : Nat → Ty} {ival : Nat → Nat → UInt8 × Option Nat} {statics : Statics}
    (hst : StaticsOK statics) (hpl : PlacementOK pl) (hg : GeomOK g)
    (hlay : NewLayout L (S3.init statics).P 0 0 g (rootIdx (statics.map (·.1))))
    (hob : OblAlong ObR ObW (run Machine.State.empty (allocOps (Ty := Ty) pl g rtok 0
      Machine.State.empty (rootIdx (statics.map (·.1))))) (writeOps (run Machine.State.empty
        (allocOps (Ty := Ty) pl g rtok 0 Machine.State.empty (rootIdx (statics.map (·.1))))) L ty
        ival (initLeaves statics))) :
    Machine.Exec C ObR ObW (initOps pl g rtok L ty ival statics) Machine.State.empty
        (run Machine.State.empty (initOps (Ty := Ty) pl g rtok L ty ival statics)) ∧
      Repr L rtok (S3.init statics)
        (run Machine.State.empty (initOps (Ty := Ty) pl g rtok L ty ival statics)) := by
  let sU : S3 := { S3.init statics with I := fun _ => .uninit }
  obtain ⟨hex₁, hR₁⟩ := repr_extend (C := C) (ObR := ObR) (ObW := ObW) (s3' := sU)
    (repr_base L rtok) hpl hg rfl hst (fun q hq => absurd hq (Nat.not_lt_zero _))
    (fun l hl => absurd hl (Nat.not_lt_zero _)) (fun _ _ h => by cases h) hlay
  have hwf₁ := hR₁.adm.wf
  have hls : ∀ l ∈ initLeaves statics, AllocP (run Machine.State.empty (allocOps (Ty := Ty) pl g
      rtok 0 Machine.State.empty (rootIdx (statics.map (·.1))))) (L l).alloc
      fun a => a.live = true ∧ (L l).off + (L l).len ≤ a.size := fun l hl => by
    simp only [initLeaves, List.mem_filter, List.mem_range, decide_eq_true_eq] at hl
    have hlP : l < sU.P.length := by
      show l < (shapeP [] (.frame 0) (statics.map (·.1))).length
      rw [shapeP_len]; simpa using hl.1
    obtain ⟨a, ha, hs⟩ := hR₁.layout.within l hlP hl.2.1
    exact ⟨a, ha, allocOps_live pl g rtok 0 _ _
      (fun _ _ h => by simp [Machine.State.empty] at h) _ a ha, hs⟩
  obtain ⟨hok, hinit⟩ := writes_ok (C := C) _ _ hwf₁ hls hob
  have hex := exec_append hex₁ (exec_of_along _ _ hok)
  rw [← run_append] at hex
  refine ⟨hex, ?_⟩
  rw [initOps, run_append]
  refine hR₁.same_places ((exec_of_along _ _ hok).admissible hR₁.adm) (dom_run _ _ hwf₁)
    (fun _ h => live_run _ _ hwf₁ (writeOps_noDealloc _ L ty ival _) h) rfl
    (fun _ h => h.of_eqs rfl rfl rfl) fun l hl hf hi => .inr (hinit l ?_)
  simp only [initLeaves, List.mem_filter, List.mem_range, decide_eq_true_eq]
  refine ⟨?_, hf, hi⟩
  have : l < (shapeP [] (.frame 0) (statics.map (·.1))).length := hl
  rw [shapeP_len] at this; simpa using this

/-! ## R4: lifetimes and dependencies (§82.5, §54, §52) -/

/-- R4 (§82.5, §54 `NoDangling`): under `Repr`, `WF3` and `NoDangling`, every leaf covered by an
active authority is an existing leaf whose allocation is live and contains its range: no active
authority designates dead storage. -/
theorem r4_no_dead_cover {L : Layout} {rtok : Nat → Nat} {s3 : S3} {s2 : Machine.State}
    (hR : Repr L rtok s3 s2) (hw : WF3 s3) (hnd : NoDangling s3) {j : Nat} {y : Authority}
    (hy : s3.A[j]? = some y) (ya : y.active = true) {l : Nat} (hl : l ∈ y.footprint) :
    l < s3.P.length ∧ isLeaf s3.P l ∧
      AllocP s2 (L l).alloc fun a => a.live = true ∧ (L l).off + (L l).len ≤ a.size := by
  obtain ⟨hlP, hlf⟩ := hw.footprints j y hy l hl
  obtain ⟨r, hr, hlr⟩ := exists_rootPlace hw (l + 1) l (Nat.lt_succ_self l) hlP
  have hur : s3.Usable r := Decidable.of_not_not fun hn =>
    hnd j y hy ya r hn l (mem_footprint.2 ⟨hlP, hlf, hlr⟩) hl
  exact ⟨hlP, hlf, hR.leaf_live hw hlP hlf
    (usable_of_partOf hw (l + 1) l r (Nat.lt_succ_self l) hlr hur)⟩

/-- Dependencies and storage (§82.5, §52 `I3`, §44): under `Repr`, `WF3`, `I3` and `NoDangling`,
every anchor of a usable place is active, and every leaf it covers has a live allocation
containing its range. -/
theorem r4_anchors {L : Layout} {rtok : Nat → Nat} {s3 : S3} {s2 : Machine.State}
    (hR : Repr L rtok s3 s2) (hw : WF3 s3) (hi3 : I3 s3) (hnd : NoDangling s3) {q x : Nat}
    (hq : s3.Usable q) (hx : x ∈ s3.D q) :
    s3.Active x ∧ ∀ l ∈ s3.afp x,
      AllocP s2 (L l).alloc fun a => a.live = true ∧ (L l).off + (L l).len ≤ a.size := by
  obtain ⟨y, hy, ya⟩ := hi3 q hq x hx
  refine ⟨⟨y, hy, ya⟩, fun l hl => ?_⟩
  have hl' : l ∈ y.footprint := by simpa [S3.afp, hy] using hl
  exact (r4_no_dead_cover hR hw hnd hy ya hl').2.2

/-- `Deallocable` (§82.4, §80, §70.2, §17.1): under `Repr`, the allocation of every root place is
registered and records a deallocation token, so it is deallocatable; `K.Deallocable(place)` for an
`OwnedRoot` place is justified by this representation. -/
theorem deallocable_sound {L : Layout} {rtok : Nat → Nat} {s3 : S3} {s2 : Machine.State}
    (hR : Repr L rtok s3 s2) {p : Nat} (hp : RootPlace s3.P p) :
    AllocP s2 (L p).alloc fun a => ∃ d, a.freeAuth = some d :=
  (hR.tokens p hp).mono fun _ h => ⟨_, h⟩

/-! ## Disjointness (§23, §82.1, §82.8) -/

/-- Disjointness of the bytes of two regions (§23, §82.1): every leaf of `r` and every leaf of `r'`
are in different allocations or have disjoint ranges (§9 ¶3). -/
def ByteDisjoint (L : Layout) (r r' : List Nat) : Prop :=
  ∀ l ∈ r, ∀ l' ∈ r', (L l).alloc ≠ (L l').alloc ∨
    Machine.RangeDisjoint (L l).off (L l).len (L l').off (L l').len

/-- §23: leaf disjointness, the normative condition of `DeclaredDisjoint`, implies disjointness of
the corresponding bytes under a layout satisfying `LayoutWF`. -/
theorem byteDisjoint_of_leaves {L : Layout} {s3 : S3} {s2 : Machine.State}
    (hlw : LayoutWF L s3 s2) {r r' : List Nat} (hr : ∀ l ∈ r, l < s3.P.length ∧ isLeaf s3.P l)
    (hr' : ∀ l ∈ r', l < s3.P.length ∧ isLeaf s3.P l) (hd : ∀ l ∈ r, l ∉ r') :
    ByteDisjoint L r r' := by
  intro l hl l' hl'
  by_cases e : (L l).alloc = (L l').alloc
  · exact .inr (hlw.disjoint l l' (hr l hl).1 (hr' l' hl').1 (hr l hl).2 (hr' l' hl').2
      (fun h => hd l hl (h ▸ hl')) e)
  · exact .inl e

/-- Actual disjointness of `DeclaredDisjoint` declarations (§82.1, §23, §80 `DDSound`): under
`DDSound(K)` and `LayoutWF`, two regions of leaves declared disjoint have disjoint bytes. -/
theorem declaredDisjoint_bytes {k : K} {L : Layout} {s3 : S3} {s2 : Machine.State}
    (hdd : DDSound k) (hlw : LayoutWF L s3 s2) {r r' : List Nat} (hdecl : k.DeclaredDisjoint r r')
    (hr : ∀ l ∈ r, l < s3.P.length ∧ isLeaf s3.P l)
    (hr' : ∀ l ∈ r', l < s3.P.length ∧ isLeaf s3.P l) : ByteDisjoint L r r' :=
  byteDisjoint_of_leaves hlw hr hr' (hdd r r' hdecl)

/-- `exclusive_bytes` (§82.8, §50, §23): under `LayoutWF` and `I1`, if authority `a` has the
effective mode `Modify` on leaf `l`, no other authority has an effective mode on a leaf `l'` whose
range overlaps the range of `l` in the same allocation: the memory justification of non-aliasing on
the side of the kernel. -/
theorem exclusive_bytes {L : Layout} {s3 : S3} {s2 : Machine.State} (hlw : LayoutWF L s3 s2)
    (hI1 : I1 s3) {a b l l' : Nat} (hl : l < s3.P.length) (hlf : isLeaf s3.P l)
    (hl' : l' < s3.P.length) (hlf' : isLeaf s3.P l') (ha : effective s3 a l = some .modify)
    (hab : a ≠ b) (hsame : (L l).alloc = (L l').alloc)
    (hover : ¬ Machine.RangeDisjoint (L l).off (L l).len (L l').off (L l').len) :
    effective s3 b l' = none := by
  by_cases e : l = l'
  · subst e; exact effective_exclusive hI1 hab ha
  · exact absurd (hlw.disjoint l l' hl hl' hlf hlf' e hsame) hover

/-! ## Kernel steps with their arguments (§60–§75) -/

/-- A kernel operation O1–O16 with its arguments (§60–§75). The representations written by
`write` and `writeShared` are data of the program (§10 ¶4, §16 ¶2), carried by the operation; the
kernel does not read them. -/
inductive KOp where
  /-- O1 `derive` (§60). -/
  | derive (src : Nat) (region : List Nat) (m : Mode)
  /-- O2 `split` (§61). -/
  | split (src : Nat) (rs : List (List Nat))
  /-- O3 `release` (§62). -/
  | release (a : Nat)
  /-- O4 `transfer` (§63). -/
  | transfer (src dst : Nat)
  /-- O5 `depend` (§64). -/
  | depend (q x : Nat)
  /-- O6 `enterFrame` (§72). -/
  | enter (ps : List Nat) (ls : LocalShape)
  /-- O7 `exitFrame` (§73). -/
  | exit
  /-- O9 `read` (§66). -/
  | read (a : Nat) (ls : List Nat)
  /-- O10 `write` (§67), with the written representations. -/
  | write (a : Nat) (ls : List Nat) (w : Nat → Nat → UInt8 × Option Nat)
  /-- O11 `writeShared` (§68), with the written representations. -/
  | writeShared (a : Nat) (ls : List Nat) (w : Nat → Nat → UInt8 × Option Nat)
  /-- O15 `pin` (§74). -/
  | pin (p : Nat)
  /-- O16 `unpin` (§75). -/
  | unpin (p : Nat)
  /-- O12 `endUse` (§69). -/
  | endUse (p : Nat)
  /-- O13 `free` (§70). -/
  | free (p auth : Nat)
  /-- O14 `alloc` (§71). -/
  | alloc (pr ow : Nat) (ls : LocalShape)
  /-- O8 `store` (§65). -/
  | store (a p : Nat)

/-- The `ok` step of a kernel operation (§58, §60–§75). -/
def OpStep (k : K) : KOp → S3 → S3 → Prop
  | .derive src region m, s, s' => DeriveStep src region m s (.ok s')
  | .split src rs, s, s' => SplitStep k src rs s (.ok s')
  | .release a, s, s' => ReleaseStep a s (.ok s')
  | .transfer src dst, s, s' => TransferStep k src dst s (.ok s')
  | .depend q x, s, s' => DependStep q x s (.ok s')
  | .enter ps ls, s, s' => EnterStep ps ls s (.ok s')
  | .exit, s, s' => ExitStep k s (.ok s')
  | .read a ls, s, s' => Read3Step a ls s (.ok s')
  | .write a ls _, s, s' => Write3Step a ls s (.ok s')
  | .writeShared a ls _, s, s' => WriteSharedStep k a ls s (.ok s')
  | .pin p, s, s' => PinStep p s (.ok s')
  | .unpin p, s, s' => UnpinStep k p s (.ok s')
  | .endUse p, s, s' => EndUseStep k p s (.ok s')
  | .free p auth, s, s' => FreeStep k p auth s (.ok s')
  | .alloc pr ow ls, s, s' => AllocStep k pr ow ls s (.ok s')
  | .store a p, s, s' => StoreStep a p s (.ok s')

/-- A labelled kernel step is a kernel step (§57, §58). -/
theorem OpStep.kstep {k : K} {op : KOp} {s s' : S3} (h : OpStep k op s s') : KStep k s s' := by
  cases op with
  | derive => exact .derive h
  | split => exact .split h
  | release => exact .release h
  | transfer => exact .transfer h
  | depend => exact .depend h
  | enter => exact .enter h
  | exit => exact .exit h
  | read => exact .read h
  | write => exact .write h
  | writeShared => exact .writeShared h
  | pin => exact .pin h
  | unpin => exact .unpin h
  | endUse => exact .endUse h
  | free => exact .free h
  | alloc => exact .alloc h
  | store => exact .store h

/-! ## Parameters of a run and realization of each step (§82, §20.3) -/

/-- Parameters of the refinement, fixed once for a run (§20.3 ¶3, §82): the layout of the places
(§82.1), the deallocation token recorded for the allocation of each root place (§17 ¶4, §82.4),
the placement and geometry of new allocations (§9 ¶11, §82.4), the type of each leaf (§15, §16;
types belong to Spec 4), the encoding of references (§82.3; Spec 11), the initial representation
of the static leaves (§47, §10 ¶5). -/
structure Params (Ty : Type) where
  /-- §82.1: layout of the places. -/
  L : Layout
  /-- §17 ¶4, §82.4: token recorded for the allocation of each root place. -/
  rtok : Nat → Nat
  /-- §9 ¶11, §82.4: placement of new allocations. -/
  pl : Placement
  /-- §9 ¶1: geometry of the allocation of each root place. -/
  geom : Nat → Geom
  /-- §15, §16: type of each leaf. -/
  ty : Nat → Ty
  /-- §82.3: encoding of references. -/
  pe : PtrEnc
  /-- §47, §10 ¶5: initial representation of the static leaves. -/
  ival : Nat → Nat → UInt8 × Option Nat

/-- Obligations of the parameters (§9 ¶11, §17.2): a valid placement, valid alignments, and each
recorded token compatible with itself (the automatic deallocation at `exitFrame` presents the
recorded token, §73, §82.5). -/
def ParamsOK {Ty : Type} (C : Nat → Nat → Prop) (π : Params Ty) : Prop :=
  PlacementOK π.pl ∧ GeomOK π.geom ∧ ∀ r, C (π.rtok r) (π.rtok r)

/-- The raw operations realizing a kernel step from `s3`, the memory state being `s2` (§82
preamble; §82.2–§82.5): computed from the parameters and the two states, nothing chosen per
step. -/
def opsOf {Ty : Type} (π : Params Ty) : KOp → S3 → Machine.State → List (Machine.Op Ty)
  | .transfer src dst, s3, s2 => transferOps π.L π.ty s2 s3 src dst
  | .enter _ ls, s3, s2 => allocOps π.pl π.geom π.rtok s3.P.length s2 (rootIdx ls.toShape)
  | .exit, s3, _ => exitOps π.L π.rtok s3
  | .read _ ls, _, s2 => readOps s2 π.L π.ty ls
  | .write _ ls w, _, s2 => writeOps s2 π.L π.ty w ls
  | .writeShared _ ls w, _, s2 => writeOps s2 π.L π.ty w ls
  | .free p auth, _, _ => freeOps π.L p auth
  | .alloc _ _ ls, s3, s2 => allocOps π.pl π.geom π.rtok s3.P.length s2 (rootIdx ls.toShape)
  | .store a p, s3, s2 => storeOps π.pe s2 π.L π.ty s3 a p
  | _, _, _ => []

/-- Obligations of one step (§20.3, §82): the parametric obligations of its reads and writes; the
layout of new places (`enterFrame`, `alloc`, §82.1); the instantiation of `K.FreeCompat` (`free`,
§80, §82.4); a reference address defined by the address rules (`store`, §82.3; not a clause of
the spec, see `r6_store`). -/
def StepObl {Ty : Type} (k : K) (C : Nat → Nat → Prop) (ObR : Machine.ReadOblSpec Ty)
    (ObW : Machine.WriteOblSpec Ty) (π : Params Ty) (op : KOp) (s3 : S3) (s2 : Machine.State) :
    Prop :=
  OblAlong ObR ObW s2 (opsOf π op s3 s2) ∧
    match op with
    | .enter _ ls => NewLayout π.L (enterP s3 ls) s3.P.length s2.next π.geom (rootIdx ls.toShape)
    | .alloc _ ow ls => NewLayout π.L (allocP s3 ow ls) s3.P.length s2.next π.geom
        (rootIdx ls.toShape)
    | .free p auth => k.FreeCompat p auth → FreeCompatInst C π.rtok p auth
    | .store a _ => PtrDecided π.L s3 a
    | _ => True

/-- Realization of every kernel step (§82 preamble, R6): under the obligations of the parameters,
`Repr`, `WF3` and `NoDangling` (parts of the kernel invariant `KInv`, §57) and the obligations of
the step, the raw operations of the step form an execution of `ok` raw steps, and `Repr` holds
after the step. -/
theorem r6 {Ty : Type} {k : K} {C : Nat → Nat → Prop} {ObR : Machine.ReadOblSpec Ty}
    {ObW : Machine.WriteOblSpec Ty} {π : Params Ty} {op : KOp} {s3 s3' : S3} {s2 : Machine.State}
    (hπ : ParamsOK C π) (hR : Repr π.L π.rtok s3 s2) (hw : WF3 s3) (hnd : NoDangling s3)
    (h : OpStep k op s3 s3') (hob : StepObl k C ObR ObW π op s3 s2) :
    Machine.Exec C ObR ObW (opsOf π op s3 s2) s2 (run s2 (opsOf π op s3 s2)) ∧
      Repr π.L π.rtok s3' (run s2 (opsOf π op s3 s2)) := by
  obtain ⟨hpl, hg, htc⟩ := hπ
  obtain ⟨hob, hx⟩ := hob
  cases op with
  | derive => exact ⟨.nil _, r6_derive hR h⟩
  | split => exact ⟨.nil _, r6_split hR h⟩
  | release => exact ⟨.nil _, r6_release hR h⟩
  | transfer => exact r6_transfer hR hw h hob
  | depend => exact ⟨.nil _, r6_depend hR h⟩
  | enter => exact r6_enter hR hw h hpl hg hx
  | exit =>
    have := r6_exit (ObR := ObR) (ObW := ObW) hR hw h htc
    exact ⟨this.1, this.2.2⟩
  | read =>
    have := r6_read (C := C) hR hw h hob
    exact ⟨this.1, this.2.2⟩
  | write => exact r2_write hR hw h hob
  | writeShared => exact r2_writeShared hR hw h hob
  | pin => exact ⟨.nil _, r6_pin hR h⟩
  | unpin => exact ⟨.nil _, r6_unpin hR h⟩
  | endUse => exact ⟨.nil _, r6_endUse hR h⟩
  | free =>
    have := r6_free (ObR := ObR) (ObW := ObW) hR hw hnd h hx
    exact ⟨this.1, this.2.2⟩
  | alloc => exact (r6_alloc hR hw h hpl hg hx).2
  | store => exact r6_store hR hw h hx hob

/-! ## Simulation (§82 preamble) -/

/-- Runs of the kernel from `S3.init statics` translated into the memory machine, with the
contract `K`, the deallocation compatibility `C`, the obligations `ObR`, `ObW` and the parameters
`π` fixed once for the run (§20.3 ¶3, §82): the initial state with the creations and writes of the
statics (`repr_init`); then each `ok` kernel step from a state satisfying `WF3` and `NoDangling`
(parts of the kernel invariant, §57) under its obligations, followed by its raw operations. The
invariant is a hypothesis on the states of the run, not a consequence of reachability, since
`transfer` can break it (an ownership cycle, §63 against §49.8 and §54). -/
inductive SimRun {Ty : Type} (k : K) (C : Nat → Nat → Prop) (ObR : Machine.ReadOblSpec Ty)
    (ObW : Machine.WriteOblSpec Ty) (statics : Statics) (π : Params Ty) :
    S3 → Machine.State → Prop where
  | init : StaticsOK statics →
      NewLayout π.L (S3.init statics).P 0 0 π.geom (rootIdx (statics.map (·.1))) →
      OblAlong ObR ObW (run Machine.State.empty (allocOps (Ty := Ty) π.pl π.geom π.rtok 0
        Machine.State.empty (rootIdx (statics.map (·.1))))) (writeOps (run Machine.State.empty
          (allocOps (Ty := Ty) π.pl π.geom π.rtok 0 Machine.State.empty
            (rootIdx (statics.map (·.1))))) π.L π.ty π.ival (initLeaves statics)) →
      SimRun k C ObR ObW statics π (S3.init statics)
        (run Machine.State.empty (initOps π.pl π.geom π.rtok π.L π.ty π.ival statics))
  | step {op : KOp} {s3 s3' : S3} {s2 : Machine.State} : SimRun k C ObR ObW statics π s3 s2 →
      WF3 s3 → NoDangling s3 → OpStep k op s3 s3' → StepObl k C ObR ObW π op s3 s2 →
      SimRun k C ObR ObW statics π s3' (run s2 (opsOf π op s3 s2))

/-- Simulation (§82 preamble, §57, §9 ¶9): for every translated run, the memory state is reached
from the empty state by an execution of `ok` raw steps, it is related to the kernel state by
`Repr` (admissibility included), and the kernel state is reachable from `S3.init statics` by the
kernel steps O1–O16. -/
theorem simulation {Ty : Type} {k : K} {C : Nat → Nat → Prop} {ObR : Machine.ReadOblSpec Ty}
    {ObW : Machine.WriteOblSpec Ty} {statics : Statics} {π : Params Ty} {s3 : S3}
    {s2 : Machine.State} (hπ : ParamsOK C π) (h : SimRun k C ObR ObW statics π s3 s2) :
    (∃ ops, Machine.Exec C ObR ObW ops Machine.State.empty s2) ∧ Repr π.L π.rtok s3 s2 ∧
      Access.Reachable k statics s3 := by
  induction h with
  | init hst hlay hob =>
    obtain ⟨hex, hR⟩ := repr_init (C := C) hst hπ.1 hπ.2.1 hlay hob
    exact ⟨⟨_, hex⟩, hR, .init⟩
  | step _ hw hnd hs hob ih =>
    obtain ⟨⟨ops, hex⟩, hR, hr⟩ := ih
    obtain ⟨hex', hR'⟩ := r6 hπ hR hw hnd hs hob
    exact ⟨⟨_, exec_append hex hex'⟩, hR', .step hr hs.kstep⟩

/-! ## Pinned addresses (§82.6, §74, §75) -/

/-- The automatic storage deallocated by `exitFrame` dies with the frame (§73): every place of
`exitRoots` is usable before the exit and not after. -/
theorem exitRoots_dies {s3 : S3} (hw : WF3 s3) (hF : s3.F ≠ []) {r : Nat}
    (hr : r ∈ exitRoots s3) :
    s3.Usable r ∧ ¬ ({ s3 with F := s3.F.tail } : S3).Usable r := by
  obtain ⟨hrt, ho, hd⟩ := mem_exitRoots.1 hr
  cases hpl : s3.P[r]? with
  | none => rw [hpl] at ho; exact ho.elim
  | some pl =>
    rw [hpl] at ho; simp only [OptP] at ho
    refine ⟨.frame hpl hd ho (top_mem hF), fun hu => ?_⟩
    cases hu with
    | frame hpl' _ ho' hf =>
      change s3.P[r]? = some _ at hpl'
      rw [hpl] at hpl'; cases hpl'; rw [ho] at ho'; cases ho'
      have hnd := hw.frames.2.1
      have ht : s3.top ∈ s3.F.tail := hf
      unfold S3.top at ht
      cases hFe : s3.F with
      | nil => exact hF hFe
      | cons f F => rw [hFe] at ht hnd; exact (List.nodup_cons.1 hnd).1 ht
    | place hpl' _ ho' _ =>
      change s3.P[r]? = some _ at hpl'
      rw [hpl] at hpl'; cases hpl'; rw [ho] at ho'; cases ho'

/-- A leaf in the allocation of a root place belongs to that root place (§82.1, `inj`). -/
theorem Repr.leaf_of_alloc {L : Layout} {rtok : Nat → Nat} {s3 : S3} {s2 : Machine.State}
    (hR : Repr L rtok s3 s2) (hw : WF3 s3) {l r : Nat} (hl : l < s3.P.length)
    (hlf : isLeaf s3.P l) (hr : RootPlace s3.P r) (he : (L l).alloc = (L r).alloc) :
    l ∈ footprint s3.P r := by
  obtain ⟨r', hr', hlr'⟩ := exists_rootPlace hw (l + 1) l (Nat.lt_succ_self l) hl
  have : r' = r := Decidable.of_not_not fun hne =>
    hR.inj r' r hr' hr hne (by rw [← hR.layout.alloc_part hlr', he])
  subst this
  exact mem_footprint.2 ⟨hl, hlf, hlr'⟩

/-- `pinned_address_stable` (§82.6, §74, §75; §63.5, §69.4, §70.4, §73.3): for every realized
kernel step (`r6`), a leaf pinned dynamically or by `K.Pinned` whose allocation is live before the
step keeps a live allocation and the same address after the raw operations of the step. The
memory machine never moves an allocation (§13); the content is that no deallocation of the step
touches a pinned leaf. -/
theorem pinned_address_stable {Ty : Type} {k : K} {π : Params Ty} {op : KOp}
    {s3 s3' : S3} {s2 : Machine.State} (hR : Repr π.L π.rtok s3 s2) (hw : WF3 s3)
    (hnd : NoDangling s3) (h : OpStep k op s3 s3') {l : Nat} (hl : l < s3.P.length)
    (hlf : isLeaf s3.P l) (hpin : s3.pin l = true ∨ k.Pinned l)
    (hlive : LiveAlloc s2 (π.L l).alloc) :
    LiveAlloc (run s2 (opsOf π op s3 s2)) (π.L l).alloc ∧
      leafAddr (run s2 (opsOf π op s3 s2)) π.L l = leafAddr s2 π.L l := by
  have hwf := hR.adm.wf
  have haddr : leafAddr (run s2 (opsOf π op s3 s2)) π.L l = leafAddr s2 π.L l := by
    simp only [leafAddr]; rw [baseOf_run hwf _ (hlive.mono fun _ _ => trivial)]
  refine ⟨?_, haddr⟩
  have hnod : (∀ o ∈ opsOf π op s3 s2, NoDealloc o) →
      LiveAlloc (run s2 (opsOf π op s3 s2)) (π.L l).alloc :=
    fun hn => live_run _ _ hwf hn hlive
  have hpinned : ¬ (s3.pin l = false ∧ ¬ k.Pinned l) := fun ⟨h1, h2⟩ => by
    rcases hpin with h | h
    · rw [h1] at h; cases h
    · exact h2 h
  cases op with
  | transfer => exact hnod (copyOps_noDealloc _ _ _ _)
  | enter => exact hnod (allocOps_noDealloc _ _ _ _ _ _)
  | read =>
    refine hnod fun o ho => ?_
    obtain ⟨_, -, rfl⟩ := List.mem_map.1 ho
    trivial
  | write => exact hnod (writeOps_noDealloc _ _ _ _ _)
  | writeShared => exact hnod (writeOps_noDealloc _ _ _ _ _)
  | alloc => exact hnod (allocOps_noDealloc _ _ _ _ _ _)
  | store a p =>
    refine hnod fun o ho => ?_
    simp only [opsOf, storeOps] at ho
    split at ho
    · exact writeOps_noDealloc _ _ _ _ _ o ho
    · cases ho
  | free p auth =>
    obtain ⟨hpre, -⟩ := Guarded.ok_iff.1 h
    have hrt := (free_usable hw hnd hpre).1
    obtain ⟨a, ha, hla⟩ := hlive
    refine ⟨_, ?_, hla⟩
    show (s2.dealloc (π.L p).alloc).allocs _ = _
    rw [dealloc_allocs, ite_eq_right fun e => hpinned ?_, ha]
    have hfp := hR.leaf_of_alloc hw hl hlf hrt e
    exact hpre.notPinned l (List.mem_range.2 hl) (.inl hfp)
  | exit =>
    obtain ⟨hpre, -⟩ := Guarded.ok_iff.1 h
    have hF : s3.F ≠ [] := fun e => hpre.hasCaller (by rw [e]; rfl)
    have hpw : (exitRoots s3).Pairwise (fun r r' => (π.L r).alloc ≠ (π.L r').alloc) :=
      ((range_pairwise _).filter _).imp_of_mem fun {r r'} hr hr' hlt =>
        hR.inj r r' (mem_exitRoots.1 hr).1 (mem_exitRoots.1 hr').1 (Nat.ne_of_lt hlt)
    have hlv : ∀ r ∈ exitRoots s3, AllocP s2 (π.L r).alloc
        fun a => a.live = true ∧ a.freeAuth = some (π.rtok r) := fun r hr =>
      (hR.live r (mem_exitRoots.1 hr).1 (exitRoots_dies hw hF hr).1).and
        (hR.tokens r (mem_exitRoots.1 hr).1)
    obtain ⟨-, hkeep, -⟩ := deallocOps_run (Ty := Ty) (C := fun _ _ => True)
      (ObR := ⟨fun _ _ _ => True, fun _ _ _ => True⟩)
      (ObW := ⟨fun _ _ _ _ => True, fun _ _ _ _ => True⟩) (fun _ => trivial) _ s2 hpw hlv
    obtain ⟨a, ha, hla⟩ := hlive
    refine ⟨a, ?_, hla⟩
    change (run s2 (deallocOps (Ty := Ty) π.L π.rtok (exitRoots s3))).allocs _ = _
    rw [hkeep _ fun r hr e => hpinned ?_, ha]
    obtain ⟨hdu, hdn⟩ := exitRoots_dies hw hF hr
    have hfp := hR.leaf_of_alloc hw hl hlf (mem_exitRoots.1 hr).1 e.symm
    exact hpre.notPinned r (List.mem_range.2 (mem_exitRoots.1 hr).1.1) hdu hdn l hfp
  | derive => exact hnod fun _ h => nomatch h
  | split => exact hnod fun _ h => nomatch h
  | release => exact hnod fun _ h => nomatch h
  | depend => exact hnod fun _ h => nomatch h
  | pin => exact hnod fun _ h => nomatch h
  | unpin => exact hnod fun _ h => nomatch h
  | endUse => exact hnod fun _ h => nomatch h

/-! ## Decidable sufficient conditions for `WF3` and `NoDangling` (§49, §54)

Bounded forms of the clauses, checked by evaluation on concrete states of a run. Only the direction
"check implies clause" is proven; it is all a run needs. -/

/-- A property of an optional value read at `some y` (§38). -/
theorem optP_of {α : Type} {o : Option α} {y : α} {P : α → Prop} {d : Prop} (h : o = some y)
    (hp : OptP o P d) : P y := by
  subst h; exact hp

/-- An owner within bounds (§49.3): a frame below `nF` or an existing place. -/
def OwnerOK (s : S3) : Holder → Prop
  | .frame f => f < s.nF
  | .place o => o < s.P.length

/-- Decidability of `OwnerOK` (§49.3). -/
instance (s : S3) (h : Holder) : Decidable (OwnerOK s h) := by
  cases h <;> unfold OwnerOK <;> infer_instance

/-- Same footprint, read as two inclusions of lists (§49.6, §49.7). -/
def SameFp (s : S3) (fp : List Nat) (r : Nat) : Prop :=
  (∀ l ∈ fp, l ∈ footprint s.P r) ∧ ∀ l ∈ footprint s.P r, l ∈ fp

/-- Decidability of `SameFp` (§49.6). -/
instance (s : S3) (fp : List Nat) (r : Nat) : Decidable (SameFp s fp r) := by
  unfold SameFp; infer_instance

/-- Bounded §49.2 (§49). -/
def PlacesCheck (s : S3) : Prop :=
  ∀ q < s.P.length, OptP (s.P[q]?) (fun pl => OptP pl.parent (fun r => OptP (s.P[r]?)
    (fun pr => r < q ∧ pr.owner = pl.owner ∧ s.dead r = s.dead q) False) True) True

/-- Bounded §49.3, first two parts (§49). -/
def OwnersCheck (s : S3) : Prop :=
  ∀ q < s.P.length, OptP (s.P[q]?) (fun pl => OwnerOK s pl.owner) True

/-- Bounded §49.4 (§49). -/
def FootprintsCheck (s : S3) : Prop :=
  ∀ a < s.A.length, OptP (s.A[a]?) (fun x => ∀ l ∈ x.footprint, l < s.P.length ∧ isLeaf s.P l)
    True

/-- Bounded §49.5 (§49). -/
def OriginsCheck (s : S3) : Prop :=
  ∀ b < s.A.length, OptP (s.A[b]?) (fun y => OptP y.origin (fun a => a < b) True) True

/-- Root of the chain of an authority covering a leaf (§49.6). -/
def ChainRoot (s : S3) (l x : Nat) : Prop :=
  OptP (s.A[x]?) (fun z => z.origin = none ∧ ∃ r < s.P.length, RootPlace s.P r ∧ partOf s.P l r ∧
    SameFp s z.footprint r) False

/-- Decidability of `ChainRoot` (§49.6). -/
instance (s : S3) (l x : Nat) : Decidable (ChainRoot s l x) := by
  unfold ChainRoot; infer_instance

/-- Bounded §49.6 `RootChain` (§49). -/
def RootChainCheck (s : S3) : Prop :=
  ∀ a < s.A.length, OptP (s.A[a]?) (fun y => ∀ l ∈ y.footprint, isLeaf s.P l →
    ∃ x ∈ a :: s.ancs a, ChainRoot s l x) True

/-- Root authority of a root place (§49.7). -/
def RootAuthOf (s : S3) (r i : Nat) : Prop :=
  OptP (s.A[i]?) (fun z => z.active = true ∧ z.origin = none ∧ z.mode = .modify ∧
    OptP (s.P[r]?) (fun pr => z.holder = pr.owner) False ∧ SameFp s z.footprint r) False

/-- Decidability of `RootAuthOf` (§49.7). -/
instance (s : S3) (r i : Nat) : Decidable (RootAuthOf s r i) := by
  unfold RootAuthOf; infer_instance

/-- Bounded §49.7 `RootHeld` (§49). -/
def RootHeldCheck (s : S3) : Prop :=
  ∀ r < s.P.length, RootPlace s.P r → s.Usable r → ∃ i < s.A.length, RootAuthOf s r i

/-- Bounded §49.8 (§49). -/
def HoldersCheck (s : S3) : Prop :=
  ∀ a < s.A.length, OptP (s.A[a]?) (fun y => y.active = true → HolderLive s y.holder) True

/-- Bounded `WF3` (§49). -/
def WF3Check (s : S3) : Prop :=
  (s.F ≠ [] ∧ s.F.Nodup ∧ ∀ f ∈ s.F, f < s.nF) ∧ PlacesCheck s ∧ OwnersCheck s ∧
    FootprintsCheck s ∧ OriginsCheck s ∧ RootChainCheck s ∧ RootHeldCheck s ∧ HoldersCheck s

/-- An authority covers no leaf of an unusable place (§54). -/
def CoversUsable (s : S3) (y : Authority) : Prop :=
  ∀ q < s.P.length, ¬ s.Usable q → ∀ l ∈ footprint s.P q, l ∉ y.footprint

/-- Decidability of `CoversUsable` (§54). -/
instance (s : S3) (y : Authority) : Decidable (CoversUsable s y) := by
  unfold CoversUsable; infer_instance

/-- Bounded `NoDangling` (§54). -/
def NoDanglingCheck (s : S3) : Prop :=
  ∀ j < s.A.length, OptP (s.A[j]?) (fun y => y.active = true → CoversUsable s y) True

/-- Decidability of the bounded clauses (§49, §54). -/
instance (s : S3) : Decidable (PlacesCheck s) := by unfold PlacesCheck; infer_instance
/-- Decidability of the bounded clauses (§49). -/
instance (s : S3) : Decidable (OwnersCheck s) := by unfold OwnersCheck; infer_instance
/-- Decidability of the bounded clauses (§49). -/
instance (s : S3) : Decidable (FootprintsCheck s) := by unfold FootprintsCheck; infer_instance
/-- Decidability of the bounded clauses (§49). -/
instance (s : S3) : Decidable (OriginsCheck s) := by unfold OriginsCheck; infer_instance
/-- Decidability of the bounded clauses (§49). -/
instance (s : S3) : Decidable (RootChainCheck s) := by unfold RootChainCheck; infer_instance
/-- Decidability of the bounded clauses (§49). -/
instance (s : S3) : Decidable (RootHeldCheck s) := by unfold RootHeldCheck; infer_instance
/-- Decidability of the bounded clauses (§49). -/
instance (s : S3) : Decidable (HoldersCheck s) := by unfold HoldersCheck; infer_instance
/-- Decidability of the bounded clauses (§49). -/
instance (s : S3) : Decidable (WF3Check s) := by unfold WF3Check; infer_instance
/-- Decidability of the bounded clauses (§54). -/
instance (s : S3) : Decidable (NoDanglingCheck s) := by unfold NoDanglingCheck; infer_instance

/-- The bounded check implies `WF3` (§49). -/
theorem wf3_of_check {s : S3} (h : WF3Check s) : WF3 s := by
  obtain ⟨hF, hPl, hOw, hFp, hOr, hRC, hRH, hHo⟩ := h
  refine ⟨hF, fun q pl r hq hp => ?_, ⟨fun q pl f hq ho => ?_, fun q pl o hq ho => ?_,
    fun q hu => hu.frameOf⟩, fun a x ha => optP_of ha (hFp a (lt_of_getElem? ha)),
    fun b y a hb ho => ?_, ?_, ?_, ?_⟩
  · have h1 := optP_of hq (hPl q (lt_of_getElem? hq))
    have := optP_of hp h1
    cases hr : s.P[r]? with
    | none => rw [hr] at this; exact this.elim
    | some pr => rw [hr] at this; exact ⟨pr, rfl, this⟩
  · have := optP_of hq (hOw q (lt_of_getElem? hq)); rw [ho] at this; exact this
  · have := optP_of hq (hOw q (lt_of_getElem? hq)); rw [ho] at this; exact this
  · have h1 := optP_of hb (hOr b (lt_of_getElem? hb))
    exact optP_of (P := fun a' => a' < b) ho h1
  · intro a y l ha hl hlf
    obtain ⟨x, hx, hc⟩ := optP_of ha (hRC a (lt_of_getElem? ha)) l hl hlf
    unfold ChainRoot at hc
    cases hz : s.A[x]? with
    | none => rw [hz] at hc; exact hc.elim
    | some z =>
      obtain ⟨hzo, r, -, hr, hlr, hf1, hf2⟩ := optP_of hz hc
      exact ⟨x, z, r, List.mem_cons.1 hx, hz, hzo, hr, hlr, fun l' => ⟨hf1 l', hf2 l'⟩⟩
  · intro r hr hu
    obtain ⟨i, -, hi⟩ := hRH r hr.1 hr hu
    unfold RootAuthOf at hi
    cases hz : s.A[i]? with
    | none => rw [hz] at hi; exact hi.elim
    | some z =>
      obtain ⟨za, zo, zm, hh, hf1, hf2⟩ := optP_of hz hi
      cases hpr : s.P[r]? with
      | none => rw [hpr] at hh; exact hh.elim
      | some pr =>
        have h2 : z.holder = pr.owner := by rw [hpr] at hh; exact hh
        exact ⟨i, z, pr, hz, za, zo, zm, rfl, h2, fun l' => ⟨hf1 l', hf2 l'⟩⟩
  · intro a y ha ya
    exact optP_of ha (hHo a (lt_of_getElem? ha)) ya

/-- A place whose footprint is nonempty exists (§40). -/
theorem lt_of_mem_footprint {P : List Place} {q l : Nat} (h : l ∈ footprint P q) :
    q < P.length := by
  obtain ⟨hlP, -, -, hlq⟩ := mem_footprint.1 h
  rcases hlq with rfl | hlq
  · exact hlP
  · exact Nat.lt_trans (chain_lt hlq) hlP

/-- The bounded check implies `NoDangling` (§54). -/
theorem noDangling_of_check {s : S3} (h : NoDanglingCheck s) : NoDangling s := by
  intro j y hy ya q hq l hl hly
  exact optP_of hy (h j (lt_of_getElem? hy)) ya q (lt_of_mem_footprint hl) hq l hl hly

/-- Decidability of `FreeCompatInst` (§70.2, §82.4). -/
instance (C : Nat → Nat → Prop) [DecidableRel C] (rtok : Nat → Nat) (p auth : Nat) :
    Decidable (FreeCompatInst C rtok p auth) := by
  unfold FreeCompatInst; infer_instance

/-! ## Executable runs (§58, §60–§75) -/

/-- The preconditions of the `ok` outcome of a kernel operation (§60–§75; for `alloc`, the static
preconditions and `K.Satisfiable`, §71). -/
def OpPre (k : K) : KOp → S3 → Prop
  | .derive src region m, s => DerivePre s src region m
  | .split src rs, s => SplitPre k s src rs
  | .release a, s => ReleasePre s a
  | .transfer src dst, s => TransferPre k s src dst
  | .depend q x, s => DependPre s q x
  | .enter ps ls, s => EnterPre s ps ls
  | .exit, s => ExitPre k s
  | .read a ls, s => Read3Pre s a ls
  | .write a ls _, s => Write3Pre s a ls
  | .writeShared a ls _, s => WriteSharedPre k s a ls
  | .pin p, s => PinPre s p
  | .unpin p, s => UnpinPre k s p
  | .endUse p, s => EndUsePre k s p
  | .free p auth, s => FreePre k s p auth
  | .alloc pr ow ls, s => AllocStatic k s pr ow ls ∧ k.Satisfiable pr ls s
  | .store a p, s => StorePre s a p

/-- The effect of the `ok` outcome of a kernel operation (§60–§75). -/
def opEff3 : KOp → S3 → S3
  | .derive src region m, s => deriveEff s src region m
  | .split src rs, s => splitEff s src rs
  | .release a, s => releaseEff s a
  | .transfer src dst, s => transferEff s src dst
  | .depend q x, s => dependEff s q x
  | .enter ps ls, s => enterEff s ps ls
  | .exit, s => exitEff s
  | .read _ _, s => s
  | .write _ ls _, s => write3Eff s ls
  | .writeShared _ ls _, s => write3Eff s ls
  | .pin p, s => pinEff s p true
  | .unpin p, s => pinEff s p false
  | .endUse p, s => endUseEff s p
  | .free p _, s => freeEff s p
  | .alloc _ ow ls, s => allocEff s ow ls
  | .store a p, s => storeEff s a p

/-- The preconditions give the `ok` step to the effect (§58). -/
theorem opStep_of_pre {k : K} {op : KOp} {s : S3} (h : OpPre k op s) :
    OpStep k op s (opEff3 op s) := by
  cases op with
  | alloc => exact .ok h.1 h.2
  | _ => exact .ok h

section Runner

variable (k : K) [∀ r r', Decidable (k.DeclaredDisjoint r r')] [DecidablePred k.SharedMutable]
  [DecidablePred k.Pinned] [DecidablePred k.ExternalDone] [DecidablePred k.Deallocable]
  [∀ p a, Decidable (k.FreeCompat p a)] [∀ p ls s, Decidable (k.Satisfiable p ls s)]

/-- Decidability of the preconditions of a kernel operation (§60–§75). -/
instance opPreDec (op : KOp) (s : S3) : Decidable (OpPre k op s) := by
  cases op <;> unfold OpPre <;> infer_instance

variable {Ty : Type} (C : Nat → Nat → Prop) [DecidableRel C] (ObR : Machine.ReadOblSpec Ty)
  (ObW : Machine.WriteOblSpec Ty) [∀ s o, Decidable (Obl ObR ObW s o)] (π : Params Ty)

/-- Decidability of the obligations of a step (§20.3, §82). -/
instance stepOblDec (op : KOp) (s3 : S3) (s2 : Machine.State) :
    Decidable (StepObl k C ObR ObW π op s3 s2) := by
  unfold StepObl; cases op <;> dsimp only <;> infer_instance

/-- One translated step: when the bounded invariant checks, the preconditions and the obligations
hold, the effect of the step and the memory state after its raw operations (§82). -/
def sstep (st : S3 × Machine.State) (op : KOp) : Option (S3 × Machine.State) :=
  if WF3Check st.1 ∧ NoDanglingCheck st.1 ∧ OpPre k op st.1 ∧ StepObl k C ObR ObW π op st.1 st.2
  then some (opEff3 op st.1, run st.2 (opsOf π op st.1 st.2)) else none

/-- A translated run of a list of operations, in order (§82). -/
def srun : S3 × Machine.State → List KOp → Option (S3 × Machine.State)
  | st, [] => some st
  | st, op :: ops => (sstep k C ObR ObW π st op).bind fun st' => srun st' ops

end Runner

/-- A successful translated run extends a `SimRun` (§82 preamble). -/
theorem srun_sound {k : K} [∀ r r', Decidable (k.DeclaredDisjoint r r')]
    [DecidablePred k.SharedMutable] [DecidablePred k.Pinned] [DecidablePred k.ExternalDone]
    [DecidablePred k.Deallocable] [∀ p a, Decidable (k.FreeCompat p a)]
    [∀ p ls s, Decidable (k.Satisfiable p ls s)] {Ty : Type} {C : Nat → Nat → Prop}
    [DecidableRel C] {ObR : Machine.ReadOblSpec Ty} {ObW : Machine.WriteOblSpec Ty}
    [∀ s o, Decidable (Obl ObR ObW s o)] {π : Params Ty} {statics : Statics} :
    ∀ (ops : List KOp) (st st' : S3 × Machine.State),
      SimRun k C ObR ObW statics π st.1 st.2 → srun k C ObR ObW π st ops = some st' →
      SimRun k C ObR ObW statics π st'.1 st'.2
  | [], st, st', h, he => by
    simp only [srun, Option.some.injEq] at he; subst he; exact h
  | op :: ops, st, st', h, he => by
    simp only [srun] at he
    cases hs : sstep k C ObR ObW π st op with
    | none => rw [hs] at he; cases he
    | some st₁ =>
      rw [hs] at he
      simp only [Option.bind_some] at he
      unfold sstep at hs
      split at hs
      · rename_i hc
        simp only [Option.some.injEq] at hs; subst hs
        exact srun_sound ops _ st' (.step h (wf3_of_check hc.1) (noDangling_of_check hc.2.1)
          (opStep_of_pre hc.2.2.1) hc.2.2.2) he
      · cases hs

/-- An option known to be `some` is `some` of its value (§82, runs). -/
theorem some_getD {α : Type} {o : Option α} (d : α) (h : o.isSome = true) :
    o = some (o.getD d) := by
  cases o with
  | none => cases h
  | some x => rfl

/-! ## Concrete parameters and runs (non-vacuity; §82, `formal/DESIGN.md` "Layout interface") -/

namespace Runs

open Ern.MemoryModel.Access.Examples

/-- Decidability of `K0.Satisfiable` (§48; test contract of the kernel examples). -/
instance : ∀ p ls s, Decidable (K0.Satisfiable p ls s) := fun _ _ _ => instDecidableTrue

/-- Root place of `q`: the last element of its parent chain (§40). -/
def rootOf (P : List Place) (q : Nat) : Nat := (chain (parentOf P) q).getLastD q

/-- Number of root places below `r`: the identity of the allocation of the root `r` when every root
place receives one allocation in index order (§9 ¶11, §82.1). -/
def rootRank (P : List Place) (r : Nat) : Nat :=
  ((List.range r).filter fun i => decide (i < P.length ∧ parentOf P i = none)).length

/-- Number of leaves of the root of `l` below `l` (§82.1). -/
def leafRank (P : List Place) (l : Nat) : Nat :=
  ((List.range l).filter fun i => decide (isLeaf P i ∧ rootOf P i = rootOf P l)).length

/-- Test layout for the places `P` (§82.1): a place in the allocation of its root; a leaf of 8
bytes at 8 times its rank among the leaves of its root; leaves of the roots listed in `z` have
size zero (§71.1, zero physical size). -/
def autoL (P : List Place) (z : List Nat) : Layout := fun q =>
  if rootOf P q ∈ z then ⟨rootRank P (rootOf P q), 0, 0⟩
  else ⟨rootRank P (rootOf P q), 8 * leafRank P q, 8⟩

/-- Test geometry (§9 ¶1): 8 bytes per leaf of the root, aligned on 8; size zero for the roots of
`z`. -/
def autoG (P : List Place) (z : List Nat) : Nat → Geom := fun r =>
  if r ∈ z then ⟨0, 0, 8⟩ else ⟨0, 8 * (footprint P r).length, 8⟩

/-- The test geometry has valid alignments (§9 ¶4). -/
theorem autoG_ok (P : List Place) (z : List Nat) : GeomOK (autoG P z) := fun r => by
  simp only [autoG]; split <;> exact ⟨Nat.succ_pos 7, 3, rfl⟩

/-- Test reference encoding (§82.3): 8 bytes, little-endian, each with the provenance. -/
def pe8 : PtrEnc where
  size := 8
  enc addr prov i := ((addr / 256 ^ i % 256).toUInt8, prov)
  decode f := (List.range 8).foldr (fun i acc => acc + (f i).1.toNat * 256 ^ i) 0
  reads f g h := by
    have key : ∀ l : List Nat, (∀ i ∈ l, i < 8) →
        l.foldr (fun i acc => acc + (f i).1.toNat * 256 ^ i) 0 =
          l.foldr (fun i acc => acc + (g i).1.toNat * 256 ^ i) 0 := by
      intro l hl
      induction l with
      | nil => rfl
      | cons a l ih =>
        simp only [List.foldr_cons]
        rw [ih fun i hi => hl i (List.mem_cons_of_mem _ hi), h a (hl a (List.mem_cons_self ..))]
    exact key _ fun i hi => List.mem_range.1 hi

/-- Test obligations of reads (§15 ¶5, §20.3 ¶1): explicit predicates; the decidable part requires
an address aligned on 8 bytes (§15.6), the static part is `True` (sequential runs, §15.7, §18). -/
abbrev obR : Machine.ReadOblSpec Unit := ⟨fun _ ac _ => ac.addr % 8 = 0, fun _ _ _ => True⟩

/-- Test obligations of writes (§16 ¶4, §20.3 ¶1), as `obR`. -/
abbrev obW : Machine.WriteOblSpec Unit := ⟨fun _ ac _ _ => ac.addr % 8 = 0, fun _ _ _ _ => True⟩

/-- Decidability of the test obligations (§20.3 ¶3). -/
instance : ∀ s o, Decidable (Obl obR obW s o) := fun _ o => by
  cases o <;> unfold Obl <;> infer_instance

/-- Test parameters for the final places `P` (§82): layout and geometry above, token `100 + r`
for the root `r`, `topPlacement`, unit types, `pe8`, initial byte `10 l + i` of static leaf `l`. -/
def piOf (P : List Place) (z : List Nat) : Params Unit :=
  ⟨autoL P z, fun r => 100 + r, topPlacement, autoG P z, fun _ => (), pe8,
    fun l i => ((10 * l + i).toUInt8, none)⟩

/-- The test parameters satisfy their obligations, with compatibility by equality (§9 ¶11,
§17.2). -/
theorem piOf_ok (P : List Place) (z : List Nat) : ParamsOK (· = ·) (piOf P z) :=
  ⟨topPlacement_ok, autoG_ok P z, fun _ => rfl⟩

/-- Kernel effects of a list of operations, without checks: computes the final places of a run, on
which the layout parameter is fixed once (§82). -/
def kernelRun : S3 → List KOp → S3
  | s, [] => s
  | s, op :: ops => kernelRun (opEff3 op s) ops

/-- Initial state of a translated run (§47, `repr_init`). -/
def sinit (statics : Statics) (π : Params Unit) : S3 × Machine.State :=
  (S3.init statics, run Machine.State.empty (initOps π.pl π.geom π.rtok π.L π.ty π.ival statics))

/-- Written representation of the runs: byte `i` of leaf `l` is `10 l + i`, no provenance
(§10 ¶4). -/
def wv : Nat → Nat → UInt8 × Option Nat := fun l i => ((10 * l + i).toUInt8, none)

/-- Address decoded from the range of leaf `l` (§82.3). -/
def decodedAt (π : Params Unit) (s2 : Machine.State) (l : Nat) : Nat :=
  π.pe.decode (bytesOf s2 π.L l)

/-- A successful translated run from `S3.init statics` gives the conclusions of `simulation` for
its final states (§82 preamble). -/
theorem sim_of {statics : Statics} {π : Params Unit} {ops : List KOp}
    (hπ : ParamsOK (· = ·) π) (hst : StaticsOK statics)
    (hlay : NewLayout π.L (S3.init statics).P 0 0 π.geom (rootIdx (statics.map (·.1))))
    (hob : OblAlong obR obW (run Machine.State.empty (allocOps (Ty := Unit) π.pl π.geom π.rtok 0
      Machine.State.empty (rootIdx (statics.map (·.1))))) (writeOps (run Machine.State.empty
        (allocOps (Ty := Unit) π.pl π.geom π.rtok 0 Machine.State.empty
          (rootIdx (statics.map (·.1))))) π.L π.ty π.ival (initLeaves statics)))
    (h : (srun K0 (· = ·) obR obW π (sinit statics π) ops).isSome = true) :
    (∃ os, Machine.Exec (· = ·) obR obW os Machine.State.empty
      ((srun K0 (· = ·) obR obW π (sinit statics π) ops).getD (sinit statics π)).2) ∧
    Repr π.L π.rtok ((srun K0 (· = ·) obR obW π (sinit statics π) ops).getD (sinit statics π)).1
      ((srun K0 (· = ·) obR obW π (sinit statics π) ops).getD (sinit statics π)).2 ∧
    Access.Reachable K0 statics
      ((srun K0 (· = ·) obR obW π (sinit statics π) ops).getD (sinit statics π)).1 :=
  simulation hπ (srun_sound ops (sinit statics π) _ (.init hst hlay hob) (some_getD _ h))

/-! ### A run through most kernel operations -/

/-- One static leaf `0`, `Init` (§47). -/
def stD : Statics := [((none, none, 0), true)]

/-- The operations of the run (§60–§75): frame 1 with locals 1, 2, 3; write, pin, unpin of 1;
storage 4 allocated from provider 1 for owner 2; transfer of 1 into 3, end of use of 1, shared
write of 1, dependency of 3 on the root of 1; authority 5 derived from the root of 4, written,
read, stored in 3, released; 4 freed; exit of frame 1. -/
def opsD : List KOp :=
  [.enter [] [(none, 0), (none, 0), (none, 0)], .write 1 [1] wv, .pin 1, .unpin 1,
   .alloc 1 2 [(none, 0)], .transfer 1 3, .endUse 1, .writeShared 1 [1] wv, .depend 3 1,
   .derive 4 [4] .modify, .write 5 [4] wv, .read 5 [4], .store 5 3, .release 5, .free 4 104,
   .exit]

/-- Parameters of the run, fixed once from its final places (§82). -/
def πD : Params Unit := piOf (kernelRun (S3.init stD) opsD).P []

/-- Final kernel and memory states of the run (§82). -/
def finD : S3 × Machine.State :=
  (srun K0 (· = ·) obR obW πD (sinit stD πD) opsD).getD (sinit stD πD)

/-- Every step of the run passes its invariant checks (§49, §54), preconditions (§60–§75) and
obligations (§82). -/
theorem runD_ok : (srun K0 (· = ·) obR obW πD (sinit stD πD) opsD).isSome = true := by decide

/-- Non-vacuity of the refinement (§82, `formal/DESIGN.md` "Layout interface"): the run of 16
kernel steps is translated into an execution of `ok` raw steps from the empty state, `Repr` holds
at its end (so the test layout satisfies `LayoutWF` and the parameters `ParamsOK`), and the final
kernel state is reachable. The allocation of the freed storage 4 and the automatic storage of
locals 1, 2, 3 are dead; the static allocation is live (§70, §73, §82.5). -/
theorem runD_sim :
    ((∃ os, Machine.Exec (· = ·) obR obW os Machine.State.empty finD.2) ∧
      Repr πD.L πD.rtok finD.1 finD.2 ∧ Access.Reachable K0 stD finD.1) ∧
    ParamsOK (· = ·) πD ∧ LayoutWF πD.L finD.1 finD.2 ∧ finD.1.P.length = 5 ∧
    (finD.2.allocs (πD.L 4).alloc).map (·.live) = some false ∧
    (∀ r ∈ [1, 2, 3], (finD.2.allocs (πD.L r).alloc).map (·.live) = some false) ∧
    (finD.2.allocs (πD.L 0).alloc).map (·.live) = some true := by
  have h := sim_of (piOf_ok _ []) (by decide) (by decide) (by decide) runD_ok
  exact ⟨h, piOf_ok _ [], h.2.1.layout, by decide, by decide, by decide, by decide⟩

/-! ### Zero physical size (§71.1, §82.4) -/

/-- A run allocating storage of zero physical size, laid out as a one-leaf shape of size zero
(§71.1): frame 1 with locals 0, 1; storage 2 allocated from provider 0 for owner 1. -/
def opsZ : List KOp :=
  [.enter [] [(none, 0), (none, 0)], .write 0 [0] wv, .alloc 0 1 [(none, 0)], .exit]

/-- Parameters of the run, storage 2 of size zero (§71.1). -/
def πZ : Params Unit := piOf (kernelRun (S3.init []) opsZ).P [2]

/-- Final states of the run (§82). -/
def finZ : S3 × Machine.State := (srun K0 (· = ·) obR obW πZ (sinit [] πZ) opsZ).getD (sinit [] πZ)

/-- Every step of the run passes its checks (§49, §54, §60–§75, §82). -/
theorem runZ_ok : (srun K0 (· = ·) obR obW πZ (sinit [] πZ) opsZ).isSome = true := by decide

/-- The zero-physical-size case (§82.4, §71.1, §9 ¶3): `alloc` of a one-leaf shape is realized by
one creation of an allocation of size zero, `ok`, and the run is in `Repr`. -/
theorem runZ_sim :
    ((∃ os, Machine.Exec (· = ·) obR obW os Machine.State.empty finZ.2) ∧
      Repr πZ.L πZ.rtok finZ.1 finZ.2 ∧ Access.Reachable K0 [] finZ.1) ∧
    (finZ.2.allocs (πZ.L 2).alloc).map (·.size) = some 0 ∧ (πZ.L 2).len = 0 :=
  ⟨sim_of (piOf_ok _ [2]) (by decide) (by decide) (by decide) runZ_ok, by decide, by decide⟩

/-! ### Corpus case H15: references to empty regions (§82.3, empty-region rule) -/

/-- The run of corpus case H15 with the library `issue` replaced by its kernel realization
(§82.3; Part XIV preamble: `split` then `store`): frame 1 with locals 0–4; storage 5 with leaf 6,
owned by 0, allocated from provider 1 (its root authority 5 plays `internal`); `split(5, [[]])`
then `store(6, 2)` (an empty block into leaf 2); `split(3, [[]])` then `store(7, 4)`. -/
def ops15 : List KOp :=
  [.enter [] [(none, 0), (none, 0), (none, 0), (none, 0), (none, 0)], .write 1 [1] wv,
   .alloc 1 0 [(none, 0), (some 5, 0)], .split 5 [[]], .store 6 2, .split 3 [[]], .store 7 4]

/-- Parameters of the run, fixed once from its final places (§82). -/
def π15 : Params Unit := piOf (kernelRun (S3.init []) ops15).P []

/-- Final states of the run (§82). -/
def fin15 : S3 × Machine.State :=
  (srun K0 (· = ·) obR obW π15 (sinit [] π15) ops15).getD (sinit [] π15)

/-- Every step of the run passes its checks (§49, §54, §60–§75, §82). -/
theorem run15_ok : (srun K0 (· = ·) obR obW π15 (sinit [] π15) ops15).isSome = true := by decide

/-- **Corpus case H15** (§82.3, empty-region rule): a reference to an empty region has as
address the base of the allocation of the effective anchor of its authority and as provenance
that allocation. Leaf 2 holds the empty block split from the root of storage 5: it decodes to the
base of the allocation of 5, every byte carries that allocation. Leaf 4 holds the empty region
split from the root of local 3: it decodes to the base of the allocation of 3, with that
provenance. Both bases are nonzero. The run is translated with `Repr`. -/
theorem H15 :
    ((∃ os, Machine.Exec (· = ·) obR obW os Machine.State.empty fin15.2) ∧
      Repr π15.L π15.rtok fin15.1 fin15.2 ∧ Access.Reachable K0 [] fin15.1) ∧
    decodedAt π15 fin15.2 2 = baseOf fin15.2 (π15.L 5).alloc ∧
    (∀ i < 8, (bytesOf fin15.2 π15.L 2 i).2 = some (π15.L 5).alloc) ∧
    baseOf fin15.2 (π15.L 5).alloc ≠ 0 ∧
    decodedAt π15 fin15.2 4 = baseOf fin15.2 (π15.L 3).alloc ∧
    (∀ i < 8, (bytesOf fin15.2 π15.L 4 i).2 = some (π15.L 3).alloc) ∧
    baseOf fin15.2 (π15.L 3).alloc ≠ 0 :=
  ⟨sim_of (piOf_ok _ []) (by decide) (by decide) (by decide) run15_ok, by decide, by decide,
    by decide, by decide, by decide, by decide⟩

/-! ### Corpus case H16: lowest address of a region (§82.3, lowest-address rule) -/

/-- The run of corpus case H16 with `issue` replaced by `split` then `store` (§82.3, Part XIV):
frame 1 with locals 0, 1, 2; storage 3 with leaves 4 (offset 0) and 5 (offset 8), owned by 0;
`split(3, [[5, 4]])` then `store(4, 2)`. -/
def ops16 : List KOp :=
  [.enter [] [(none, 0), (none, 0), (none, 0)], .write 1 [1] wv,
   .alloc 1 0 [(none, 0), (some 3, 0), (some 3, 0)], .split 3 [[5, 4]], .store 4 2]

/-- Parameters of the run, fixed once from its final places (§82). -/
def π16 : Params Unit := piOf (kernelRun (S3.init []) ops16).P []

/-- Final states of the run (§82). -/
def fin16 : S3 × Machine.State :=
  (srun K0 (· = ·) obR obW π16 (sinit [] π16) ops16).getD (sinit [] π16)

/-- Every step of the run passes its checks (§49, §54, §60–§75, §82). -/
theorem run16_ok : (srun K0 (· = ·) obR obW π16 (sinit [] π16) ops16).isSome = true := by decide

/-- **Corpus case H16** (§82.3, lowest-address rule): the reference to the region `[5, 4]`, whose
first listed leaf is not the lowest, has the lowest address among its leaves of nonzero size,
that of leaf 4 (offset 0), not that of the head 5 (offset 8); its provenance is the storage
allocation. The run is translated with `Repr`. -/
theorem H16 :
    ((∃ os, Machine.Exec (· = ·) obR obW os Machine.State.empty fin16.2) ∧
      Repr π16.L π16.rtok fin16.1 fin16.2 ∧ Access.Reachable K0 [] fin16.1) ∧
    (π16.L 4).off = 0 ∧ (π16.L 5).off = 8 ∧
    decodedAt π16 fin16.2 2 = baseOf fin16.2 (π16.L 3).alloc ∧
    decodedAt π16 fin16.2 2 ≠ baseOf fin16.2 (π16.L 3).alloc + 8 ∧
    (∀ i < 8, (bytesOf fin16.2 π16.L 2 i).2 = some (π16.L 3).alloc) :=
  ⟨sim_of (piOf_ok _ []) (by decide) (by decide) (by decide) run16_ok, by decide, by decide,
    by decide, by decide, by decide⟩

end Runs

/-! ## Decidable sufficient conditions for `KInv` and `KAux` (§50–§54, §57) -/

/-- Bounded `I1` for one pair (§50). -/
def I1Pair (s : S3) (a b : Nat) : Prop :=
  a ≠ b → OptP (s.A[a]?) (fun x => OptP (s.A[b]?) (fun y => x.active = true → y.active = true →
    (∃ p ∈ x.footprint, p ∈ y.footprint) → a ∉ s.ancs b → b ∉ s.ancs a →
      x.mode = .observe ∧ y.mode = .observe) True) True

/-- Decidability of `I1Pair` (§50). -/
instance (s : S3) (a b : Nat) : Decidable (I1Pair s a b) := by unfold I1Pair; infer_instance

/-- Bounded `I1` (§50). -/
def I1Check (s : S3) : Prop := ∀ a < s.A.length, ∀ b < s.A.length, I1Pair s a b

/-- The origin of `y` exists, with a mode at least that of `y` and a footprint containing that of
`y` (§51). -/
def OriginOK (s : S3) (y : Authority) : Prop :=
  OptP y.origin (fun a => OptP (s.A[a]?)
    (fun x => y.mode.le x.mode ∧ ∀ p ∈ y.footprint, p ∈ x.footprint) False) True

/-- Decidability of `OriginOK` (§51). -/
instance (s : S3) (y : Authority) : Decidable (OriginOK s y) := by
  unfold OriginOK; infer_instance

/-- Bounded `I2` (§51). -/
def I2Check (s : S3) : Prop := ∀ b < s.A.length, OptP (s.A[b]?) (fun y => OriginOK s y) True

/-- Bounded `I3` (§52). -/
def I3Check (s : S3) : Prop := ∀ q < s.P.length, s.Usable q → ∀ x ∈ s.D q, s.Active x

/-- Bounded `RootHeldConv` for one authority (§40, §49.7). -/
def RootConvOK (s : S3) (z : Authority) : Prop :=
  z.origin = none → ∀ l ∈ z.footprint, ∀ r < s.P.length, RootPlace s.P r → partOf s.P l r →
    OptP (s.P[r]?) (fun pr => z.holder = pr.owner) False

/-- Decidability of `RootConvOK` (§49.7). -/
instance (s : S3) (z : Authority) : Decidable (RootConvOK s z) := by
  unfold RootConvOK; infer_instance

/-- Bounded `RootHeldConv` (§40, §49.7). -/
def RootHeldConvCheck (s : S3) : Prop :=
  ∀ x < s.A.length, OptP (s.A[x]?) (fun z => RootConvOK s z) True

/-- Decidability of the bounded clauses (§50). -/
instance (s : S3) : Decidable (I1Check s) := by unfold I1Check; infer_instance
/-- Decidability of the bounded clauses (§51). -/
instance (s : S3) : Decidable (I2Check s) := by unfold I2Check; infer_instance
/-- Decidability of the bounded clauses (§52). -/
instance (s : S3) : Decidable (I3Check s) := by unfold I3Check; infer_instance
/-- Decidability of the bounded clauses (§49.7). -/
instance (s : S3) : Decidable (RootHeldConvCheck s) := by unfold RootHeldConvCheck; infer_instance

/-- The bounded checks imply `KInv` (§57) and `KAux` (§49.7). -/
theorem kInv_kAux_of_check {s : S3} (hw : WF3Check s) (h1 : I1Check s) (h2 : I2Check s)
    (h3 : I3Check s) (ho : AnchorOrder s) (hnd : NoDanglingCheck s) (hoh : AnchorOrderHeld s)
    (hc : RootHeldConvCheck s) : KInv s ∧ KAux s := by
  refine ⟨kInv_of (wf3_of_check hw) ⟨⟨?_, ?_, ?_, i4_always s⟩, ho, noDangling_of_check hnd⟩ hoh,
    ?_⟩
  · intro a b x y p hab ha hb xa ya hpx hpy hba hab'
    have h := h1 a (lt_of_getElem? ha) b (lt_of_getElem? hb) hab
    rw [ha] at h; simp only [OptP] at h; rw [hb] at h
    exact h xa ya ⟨p, hpx, hpy⟩ hba hab'
  · intro b y a hb hy
    have h := optP_of hb (h2 b (lt_of_getElem? hb))
    unfold OriginOK at h
    rw [hy] at h; simp only [OptP] at h
    cases hx : s.A[a]? with
    | none => rw [hx] at h; exact h.elim
    | some x => rw [hx] at h; exact ⟨x, rfl, h⟩
  · intro q hq x hx
    exact h3 q hq.lt hq x hx
  · intro x z l r hx hzo hl hr hlr
    have h := optP_of hx (hc x (lt_of_getElem? hx)) hzo l hl r hr.1 hr hlr
    cases hpr : s.P[r]? with
    | none => rw [hpr] at h; exact h.elim
    | some pr => rw [hpr] at h; exact ⟨pr, rfl, h⟩

namespace Runs

open Ern.MemoryModel.Access.Examples

/-! ### Pinned leaves and `transfer` (§74, §63.5, §82.6) -/

/-- Two static leaves `0` and `1`, `Init` (§47). -/
def stP : Statics := [((none, none, 0), true), ((none, none, 0), true)]

/-- Storage 2 allocated from provider 1 for owner 0, storage 3 for owner 2; `pin(2)` (§71, §74). -/
def opsP : List KOp := [.alloc 1 0 [(none, 0)], .alloc 1 2 [(none, 0)], .pin 2]

/-- Parameters of the run, fixed once from its final places (§82). -/
def πP : Params Unit := piOf (kernelRun (S3.init stP) opsP).P []

/-- Final states of the run (§82). -/
def finP : S3 × Machine.State :=
  (srun K0 (· = ·) obR obW πP (sinit stP πP) opsP).getD (sinit stP πP)

/-- Every step of the run passes its checks (§49, §54, §60–§75, §82). -/
theorem runP_ok : (srun K0 (· = ·) obR obW πP (sinit stP πP) opsP).isSome = true := by decide

/-- A pinned leaf need not stay usable across an `ok` `transfer` under the reference definitions
(§74 "While it is active, `transfer` ... rejected if they act on leaves it pins"; §63.5 checks the
in-place source leaves only, and `transfer` can close an ownership cycle, §63 against §49.8 and
§54). From a reachable state satisfying `KInv` and `KAux` where leaf 2 is pinned
and usable, `transfer(0, 3)` is accepted and leaf 2 is no longer usable. Its allocation stays live
with the same address (`pinned_address_stable`: no raw operation of `transfer` deallocates), so
`pinned_address_stable` does not rest on the usability of pinned leaves. -/
theorem pinned_not_usable_after_transfer :
    Access.Reachable K0 stP finP.1 ∧ KInv finP.1 ∧ KAux finP.1 ∧
      TransferStep K0 0 3 finP.1 (.ok (transferEff finP.1 0 3)) ∧
      finP.1.pin 2 = true ∧ finP.1.Usable 2 ∧ ¬ (transferEff finP.1 0 3).Usable 2 := by
  have hsim := sim_of (piOf_ok _ []) (by decide) (by decide) (by decide) runP_ok
  exact ⟨hsim.2.2, kInv_kAux_of_check (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) |>.1, kInv_kAux_of_check (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) |>.2,
    .ok (by decide), by decide, by decide, by decide⟩

end Runs

end Ern.MemoryModel.Refinement
