import Ern.MM02
import Ern.MM03

/-!
# Refinement MM-03.3 v0.3 → MM-02 v0.4 (milestone 2, pass 1)

Representation of the abstract states of MM-03.3 (module `Ern.MM03`) by the states of the abstract
machine of MM-02 (module `Ern.MM02`), and refinement of the operations in the scope of the
arbitrage K4 of the task. Both modules are imported unchanged; a lemma they lack is proved here.

The arbitrages K1–K5 of the task are cited as `K1`…`K5`. The rules of the specifications are cited
as `MM-02.x` (MM-02 v0.4) and `MM-03.3 …` (MM-03.3 v0.3 révisée). Out of scope: `transfer`,
`store`, `issue`, concurrency, real `DDSound`, stability of pinned addresses, low-level translation.
-/

namespace Ern.MM23

open Ern.MM03

/-! ## Allocations of the MM-02 state -/

/-- The MM-02 allocation `i` is registered (MM-02.2) and satisfies `p`. -/
def AllocP (s2 : MM02.State) (i : Nat) (p : MM02.Alloc → Prop) : Prop :=
  ∃ a, s2.allocs i = some a ∧ p a

instance (s2 : MM02.State) (i : Nat) (p : MM02.Alloc → Prop) [DecidablePred p] :
    Decidable (AllocP s2 i p) :=
  match h : s2.allocs i with
  | some a =>
    if ha : p a then isTrue ⟨a, h, ha⟩
    else isFalse fun ⟨b, hb, hb'⟩ => by rw [h] at hb; cases hb; exact ha hb'
  | none => isFalse fun ⟨b, hb, _⟩ => by rw [h] at hb; cases hb

/-- The MM-02 allocation `i` is registered and live (MM-02.2). -/
abbrev LiveAlloc (s2 : MM02.State) (i : Nat) : Prop := AllocP s2 i (·.live = true)

/-- The MM-02 allocation `i` is registered and dead (MM-02.2, MM-02.D). -/
abbrev DeadAlloc (s2 : MM02.State) (i : Nat) : Prop := AllocP s2 i (·.live = false)

/-! ## Layout (K1) -/

/-- K1: layout of the leaves. The leaf `l` occupies the byte range `L l` of an MM-02 allocation:
its identity `alloc`, an offset `off` and a size `len` (an MM-02.4 place). The layout fixes no
ABI, no type alignment and no order of fields. It is a parameter of an execution, defined on
every index, present or future. -/
abbrev Layout := Nat → MM02.Place

/-- K1, obligations `LayoutWF` of a layout in an MM-03 state `s3` and an MM-02 state `s2`:
(a) the leaves of one root place are in one allocation; (b) two distinct leaves in one allocation
have disjoint ranges (`RangeDisjoint`, MM-02.2); (c) the range of every leaf lies within its
allocation, which is registered (MM-02.B, spatial containment). (d) No size is bounded below: a
range may be empty, so a shape of one leaf may have size zero. No other hypothesis. -/
structure LayoutWF (L : Layout) (s3 : S3) (s2 : MM02.State) : Prop where
  sameAlloc : ∀ r < s3.P.length, RootPlace s3.P r → ∀ l ∈ footprint s3.P r,
    ∀ l' ∈ footprint s3.P r, (L l).alloc = (L l').alloc
  disjoint : ∀ l < s3.P.length, ∀ l' < s3.P.length, isLeaf s3.P l → isLeaf s3.P l' → l ≠ l' →
    (L l).alloc = (L l').alloc → MM02.RangeDisjoint (L l).off (L l).len (L l').off (L l').len
  within : ∀ l < s3.P.length, isLeaf s3.P l →
    AllocP s2 (L l).alloc fun a => (L l).off + (L l).len ≤ a.size

set_option synthInstance.maxSize 512 in
instance (L : Layout) (s3 : S3) (s2 : MM02.State) : Decidable (LayoutWF L s3 s2) :=
  decidable_of_iff
    ((∀ r < s3.P.length, RootPlace s3.P r → ∀ l ∈ footprint s3.P r,
      ∀ l' ∈ footprint s3.P r, (L l).alloc = (L l').alloc) ∧
     (∀ l < s3.P.length, ∀ l' < s3.P.length, isLeaf s3.P l → isLeaf s3.P l' → l ≠ l' →
      (L l).alloc = (L l').alloc → MM02.RangeDisjoint (L l).off (L l).len (L l').off (L l').len) ∧
     (∀ l < s3.P.length, isLeaf s3.P l →
      AllocP s2 (L l).alloc fun a => (L l).off + (L l).len ≤ a.size))
    ⟨fun ⟨a, b, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨a, b, c⟩⟩

/-! ## Representation relation (K2, K3) -/

/-- K3: the owner `h` of a root is a frame that is no longer on the stack `F`: the root died by
the exit of its frame. -/
def FrameGone (F : Frames) : Holder → Prop
  | .frame f => f ∉ F
  | .place _ => False

instance (F : Frames) (h : Holder) : Decidable (FrameGone F h) := by
  cases h <;> unfold FrameGone <;> infer_instance

/-- K2: deallocation token of the allocation of a root owned by `h`: the token `tok f` proper to
the frame `f` when `h` is the frame `f`; none is fixed for a root owned by a place. -/
def tokOf (tok : Nat → Nat) : Holder → Option Nat
  | .frame f => some (tok f)
  | .place _ => none

/-- K3, relation of representation `Repr` between an MM-03 state `s3` and an MM-02 state `s2`, for
the layout `L` and the frame tokens `tok`:
- `lwf`: `LayoutWF` (K1);
- `inj`: two distinct root places are in distinct allocations (K2: a root corresponds to an
  allocation; a part to a sub-range of the allocation of its root, by `LayoutWF.sameAlloc`);
- `tokens`: the allocation of a root owned by the frame `f` has the token `tok f` (K2);
- `live`: every usable root has its allocation live (K3);
- `init`: every `Init` leaf has all its bytes initialised (K3);
- `freed`: a root dead by `free` has its allocation dead (K3);
- `exited`: a root dead by the exit of its frame has its allocation dead (K3);
- `leaked`: a root owned by a place, not usable and not freed keeps its allocation live (K3: dead
  by `endUse`; K4: owned storage that dies with a frame or with a freed root is not deallocated).
`Repr` does not read the contracts `K`: no clause of K3 depends on them. -/
structure Repr (tok : Nat → Nat) (L : Layout) (s3 : S3) (s2 : MM02.State) : Prop where
  lwf : LayoutWF L s3 s2
  inj : ∀ r < s3.P.length, ∀ r' < s3.P.length, RootPlace s3.P r → RootPlace s3.P r' → r ≠ r' →
    ∀ l ∈ footprint s3.P r, ∀ l' ∈ footprint s3.P r', (L l).alloc ≠ (L l').alloc
  tokens : ∀ r < s3.P.length, RootPlace s3.P r → OptP (s3.P[r]?) (fun pl =>
    OptP (tokOf tok pl.owner) (fun d => ∀ l ∈ footprint s3.P r,
      AllocP s2 (L l).alloc (·.freeAuth = some d)) True) True
  live : ∀ r < s3.P.length, RootPlace s3.P r → s3.Usable r → ∀ l ∈ footprint s3.P r,
    LiveAlloc s2 (L l).alloc
  init : ∀ l < s3.P.length, isLeaf s3.P l → s3.I l = .init →
    AllocP s2 (L l).alloc fun a => a.InitRange (L l).off (L l).len
  freed : ∀ r < s3.P.length, RootPlace s3.P r → s3.freed r = true → ∀ l ∈ footprint s3.P r,
    DeadAlloc s2 (L l).alloc
  exited : ∀ r < s3.P.length, RootPlace s3.P r → OptP (s3.P[r]?) (fun pl => FrameGone s3.F pl.owner)
    False → ∀ l ∈ footprint s3.P r, DeadAlloc s2 (L l).alloc
  leaked : ∀ r < s3.P.length, RootPlace s3.P r → ¬ s3.Usable r → s3.freed r = false →
    OptP (s3.P[r]?) (fun pl => pl.owner.isPlace = true) False → ∀ l ∈ footprint s3.P r,
    LiveAlloc s2 (L l).alloc

set_option synthInstance.maxSize 4096 in
instance (tok : Nat → Nat) (L : Layout) (s3 : S3) (s2 : MM02.State) :
    Decidable (Repr tok L s3 s2) :=
  decidable_of_iff
    (LayoutWF L s3 s2 ∧
     (∀ r < s3.P.length, ∀ r' < s3.P.length, RootPlace s3.P r → RootPlace s3.P r' → r ≠ r' →
      ∀ l ∈ footprint s3.P r, ∀ l' ∈ footprint s3.P r', (L l).alloc ≠ (L l').alloc) ∧
     (∀ r < s3.P.length, RootPlace s3.P r → OptP (s3.P[r]?) (fun pl =>
      OptP (tokOf tok pl.owner) (fun d => ∀ l ∈ footprint s3.P r,
        AllocP s2 (L l).alloc (·.freeAuth = some d)) True) True) ∧
     (∀ r < s3.P.length, RootPlace s3.P r → s3.Usable r → ∀ l ∈ footprint s3.P r,
      LiveAlloc s2 (L l).alloc) ∧
     (∀ l < s3.P.length, isLeaf s3.P l → s3.I l = .init →
      AllocP s2 (L l).alloc fun a => a.InitRange (L l).off (L l).len) ∧
     (∀ r < s3.P.length, RootPlace s3.P r → s3.freed r = true → ∀ l ∈ footprint s3.P r,
      DeadAlloc s2 (L l).alloc) ∧
     (∀ r < s3.P.length, RootPlace s3.P r →
      OptP (s3.P[r]?) (fun pl => FrameGone s3.F pl.owner) False → ∀ l ∈ footprint s3.P r,
      DeadAlloc s2 (L l).alloc) ∧
     (∀ r < s3.P.length, RootPlace s3.P r → ¬ s3.Usable r → s3.freed r = false →
      OptP (s3.P[r]?) (fun pl => pl.owner.isPlace = true) False → ∀ l ∈ footprint s3.P r,
      LiveAlloc s2 (L l).alloc))
    ⟨fun ⟨a, b, c, d, e, f, g, h⟩ => ⟨a, b, c, d, e, f, g, h⟩,
     fun ⟨a, b, c, d, e, f, g, h⟩ => ⟨a, b, c, d, e, f, g, h⟩⟩

/-! ## Sequences of MM-02 operations (MM-02.H, K4, K5) -/

/-- An MM-02 operation with its arguments (MM-02.H): read, write, deallocation, allocation. -/
inductive Op2 where
  | read (ac : MM02.Access)
  | write (ac : MM02.Access) (w : Nat → UInt8 × Option Nat)
  | dealloc (id auth : Nat)
  | alloc (space base size align : Nat) (freeAuth : Option Nat)

/-- Effect of an operation of outcome `ok` (MM-02.H.2): a read leaves the state unchanged. -/
def Op2.eff : Op2 → MM02.State → MM02.State
  | .read _, s => s
  | .write ac w, s => s.write ac w
  | .dealloc id _, s => s.dealloc id
  | .alloc sp b sz al fa, s => s.alloc sp b sz al fa

/-- State reached by a sequence of operations of outcome `ok`. -/
def exec : MM02.State → List Op2 → MM02.State
  | s, [] => s
  | s, o :: os => exec (o.eff s) os

/-- `p s o` holds for each operation `o` of the sequence, in the state `s` where it runs. -/
def Along (p : MM02.State → Op2 → Prop) : MM02.State → List Op2 → Prop
  | _, [] => True
  | s, o :: os => p s o ∧ Along p (o.eff s) os

instance decAlong (p : MM02.State → Op2 → Prop) [h : ∀ s o, Decidable (p s o)] :
    (s : MM02.State) → (os : List Op2) → Decidable (Along p s os)
  | _, [] => isTrue trivial
  | s, o :: os => @instDecidableAnd _ _ (h s o) (decAlong p (o.eff s) os)

/-- The operation `o` has the outcome `ok` in `s` for its relation (MM-02.H.1): `ReadStep`,
`WriteStep`, `DeallocStep` or `AllocStep`. -/
def OpOk (C : Nat → Nat → Prop) (ObR : MM02.ReadOblSpec) (ObW : MM02.WriteOblSpec)
    (s : MM02.State) : Op2 → Prop
  | .read ac => ∃ v, MM02.ReadStep ObR ac s (.ok v)
  | .write ac w => MM02.WriteStep ObW ac w s (.ok (s.write ac w))
  | .dealloc id au => MM02.DeallocStep C id au s (.ok (s.dealloc id))
  | .alloc sp b sz al fa => MM02.AllocStep sp b sz al fa s (.ok (s.alloc sp b sz al fa))

/-- R6 (MM-03.3 §9.2): every operation of the sequence has the outcome `ok` in the state where it
runs, the compatibility `C` and the obligations `ObR`, `ObW` fixed for the execution. -/
abbrev AllOk (C : Nat → Nat → Prop) (ObR : MM02.ReadOblSpec) (ObW : MM02.WriteOblSpec) :
    MM02.State → List Op2 → Prop :=
  Along (OpOk C ObR ObW)

/-- K5: the decidable part `dec` of the obligation of a read or a write (alignment of the access,
validity of the representation; MM-02.B.4, B.6, C.4, C.5), in the state `s` where it runs. -/
def Op2.Dec (ObR : MM02.ReadOblSpec) (ObW : MM02.WriteOblSpec) (s : MM02.State) : Op2 → Prop
  | .read ac => ObR.dec s ac
  | .write ac w => ObW.dec s ac w
  | _ => True

/-- K5: `dec` holds for each read and write of the sequence, in the state where it runs. An
explicit parametric hypothesis, never instantiated by `True` in a theorem. -/
abbrev DecAlong (ObR : MM02.ReadOblSpec) (ObW : MM02.WriteOblSpec) :
    MM02.State → List Op2 → Prop :=
  Along (Op2.Dec ObR ObW)

/-! ## Placement of new allocations (K2) -/

/-- K2: geometry of a new allocation: address space, size, alignment. -/
structure Geom where
  space : Nat
  size : Nat
  align : Nat

/-- K2: `Placement`, the choice of the base address of a new allocation of geometry `g` in the
MM-02 state `s`. -/
abbrev Placement := MM02.State → Geom → Nat

/-- K2: obligation of a placement, `AllocPre` (MM-02.2, création brute: freshness, alignment,
no overlap with a live allocation), in every state with fresh identities (`WF`, MM-02.A), for every
valid alignment. -/
def PlacementOK (pl : Placement) : Prop :=
  ∀ s g, MM02.WF s → 0 < g.align → MM02.Pow2 g.align →
    MM02.AllocPre s g.space (pl s g) g.size g.align

/-- End of the allocation `i` of `s`, `0` if absent. -/
def allocEnd (s : MM02.State) (i : Nat) : Nat := ((s.allocs i).map fun a => a.base + a.size).getD 0

/-- Largest end of the allocations of identity below `n`. -/
def maxEnd (s : MM02.State) : Nat → Nat
  | 0 => 0
  | n + 1 => max (maxEnd s n) (allocEnd s n)

theorem le_maxEnd (s : MM02.State) : ∀ n i, i < n → allocEnd s i ≤ maxEnd s n
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, i, h => by
    simp only [maxEnd]
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
    · exact Nat.le_trans (le_maxEnd s n i h) (Nat.le_max_left _ _)
    · exact Nat.le_max_right _ _

/-- K2: a placement that satisfies its obligation (`topPlacement_ok`): the first multiple of the
alignment above the end of every registered allocation. -/
def topPlacement : Placement := fun s g => g.align * (maxEnd s s.next / g.align + 1)

theorem topPlacement_ok : PlacementOK topPlacement := by
  intro s g hwf h0 h2
  refine ⟨hwf _ (Nat.le_refl _), h0, h2, Nat.mul_mod_right _ _, fun i a ha _ _ => ?_⟩
  have hi : i < s.next := Nat.lt_of_not_le fun hle => by rw [hwf i hle] at ha; cases ha
  have he : a.base + a.size ≤ maxEnd s s.next := by
    have := le_maxEnd s s.next i hi; simpa [allocEnd, ha] using this
  have hb := Nat.lt_mul_div_succ (maxEnd s s.next) h0
  exact MM02.rangeDisjoint_iff.2 (.inl (by simp only [topPlacement]; omega))

/-- K2 ("`K.Satisfiable` implique l'existence d'un placement valide"): in MM-02, whose addresses
are unbounded naturals (MM-02.2), every allocation of valid alignment has a valid placement in a
state with fresh identities, whatever `K.Satisfiable` says. -/
theorem placement_exists {s : MM02.State} (hwf : MM02.WF s) (g : Geom) (h0 : 0 < g.align)
    (h2 : MM02.Pow2 g.align) : ∃ base, MM02.AllocPre s g.space base g.size g.align :=
  ⟨_, topPlacement_ok s g hwf h0 h2⟩

/-! ## Accesses and operations attached to MM-03 steps (K4) -/

/-- K4: the access to the range of leaf `l` in `s2`: address = base of its allocation + offset,
provenance = its allocation (the allocation of its root), length = its size, authority `au`. -/
def leafAcc (s2 : MM02.State) (L : Layout) (au : MM02.Auth) (l : Nat) : MM02.Access :=
  ⟨(((s2.allocs (L l).alloc).map (·.base)).getD 0) + (L l).off, (L l).alloc, (L l).len, au⟩

/-- K4 (`read3`): one read of authority `read` per range read. -/
def readOps (s2 : MM02.State) (L : Layout) (ls : List Nat) : List Op2 :=
  ls.map fun l => .read (leafAcc s2 L .read l)

/-- K4 (`write3`, `writeShared`): one write of authority `write` per range written, of the bytes
`w l` for leaf `l`. -/
def writeOps (s2 : MM02.State) (L : Layout) (w : Nat → Nat → UInt8 × Option Nat) (ls : List Nat) :
    List Op2 :=
  ls.map fun l => .write (leafAcc s2 L .write l) (w l)

/-- K2, K4 (`enterFrame`, `alloc`, static storage): one allocation per root `i` of `roots`, in
order, of geometry `g i`, at the base chosen by `pl` in the current state, with the token `fa`. -/
def allocOps (pl : Placement) (g : Nat → Geom) (fa : Option Nat) :
    MM02.State → List Nat → List Op2
  | _, [] => []
  | s, i :: is => .alloc (g i).space (pl s (g i)) (g i).size (g i).align fa ::
      allocOps pl g fa (s.alloc (g i).space (pl s (g i)) (g i).size (g i).align fa) is

/-! ## Sequences: composition -/

theorem exec_append (s : MM02.State) (os os' : List Op2) :
    exec s (os ++ os') = exec (exec s os) os' := by
  induction os generalizing s with
  | nil => rfl
  | cons o os ih => exact ih _

theorem along_append {p : MM02.State → Op2 → Prop} {s : MM02.State} {os os' : List Op2} :
    Along p s (os ++ os') ↔ Along p s os ∧ Along p (exec s os) os' := by
  induction os generalizing s with
  | nil => simp [Along, exec]
  | cons o os ih => simp only [List.cons_append, Along, exec, ih, and_assoc]

/-! ## Allocations kept by a step of MM-02 -/

/-- `s'` keeps every allocation of `s` with its address space, base, size, alignment, liveness
and token, and every initialised byte of it initialised (MM-02.C: a write only initialises;
MM-02.A: an allocation leaves the others intact). -/
def Dom (s s' : MM02.State) : Prop :=
  ∀ i a, s.allocs i = some a → ∃ a', s'.allocs i = some a' ∧ a'.space = a.space ∧
    a'.base = a.base ∧ a'.size = a.size ∧ a'.align = a.align ∧ a'.live = a.live ∧
    a'.freeAuth = a.freeAuth ∧ ∀ j, a.bytes j ≠ .uninit → a'.bytes j ≠ .uninit

theorem Dom.refl (s : MM02.State) : Dom s s :=
  fun _ a h => ⟨a, h, rfl, rfl, rfl, rfl, rfl, rfl, fun _ h => h⟩

theorem Dom.trans {s s' s'' : MM02.State} (h : Dom s s') (h' : Dom s' s'') : Dom s s'' := by
  intro i a ha
  obtain ⟨a', ha', e1, e2, e3, e4, e5, e6, hb⟩ := h i a ha
  obtain ⟨a'', ha'', f1, f2, f3, f4, f5, f6, hb'⟩ := h' i a' ha'
  exact ⟨a'', ha'', f1.trans e1, f2.trans e2, f3.trans e3, f4.trans e4, f5.trans e5, f6.trans e6,
    fun j hj => hb' j (hb j hj)⟩

theorem write_allocs (s : MM02.State) (ac : MM02.Access) (w : Nat → UInt8 × Option Nat) (i : Nat) :
    (s.write ac w).allocs i = if i = ac.prov then
      (s.allocs i).map (fun a => a.write (ac.addr - a.base) ac.len w) else s.allocs i := rfl

theorem Dom.write (s : MM02.State) (ac : MM02.Access) (w : Nat → UInt8 × Option Nat) :
    Dom s (s.write ac w) := by
  intro i a ha
  rw [write_allocs]
  split
  · refine ⟨a.write (ac.addr - a.base) ac.len w, by rw [ha]; rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      fun j hj => ?_⟩
    simp only [MM02.Alloc.write]
    split
    · exact fun h => by cases h
    · exact hj
  · exact ⟨a, ha, rfl, rfl, rfl, rfl, rfl, rfl, fun _ h => h⟩

theorem Dom.alloc {s : MM02.State} (hwf : MM02.WF s) (space base size align : Nat)
    (fa : Option Nat) : Dom s (s.alloc space base size align fa) := fun _ a ha =>
  ⟨a, (MM02.alloc_fresh hwf space base size align fa ha).2, rfl, rfl, rfl, rfl, rfl, rfl,
    fun _ h => h⟩

theorem AllocP.of_dom {s s' : MM02.State} {i : Nat} {p : MM02.Alloc → Prop} (h : AllocP s i p)
    (hd : Dom s s')
    (hp : ∀ a a' : MM02.Alloc, a'.base = a.base → a'.size = a.size → a'.live = a.live →
      a'.freeAuth = a.freeAuth → (∀ j, a.bytes j ≠ .uninit → a'.bytes j ≠ .uninit) → p a → p a') :
    AllocP s' i p := by
  obtain ⟨a, ha, hpa⟩ := h
  obtain ⟨a', ha', -, e2, e3, -, e5, e6, hb⟩ := hd i a ha
  exact ⟨a', ha', hp a a' e2 e3 e5 e6 hb hpa⟩

theorem AllocP.and {s : MM02.State} {i : Nat} {p q : MM02.Alloc → Prop} (hp : AllocP s i p)
    (hq : AllocP s i q) : AllocP s i fun a => p a ∧ q a := by
  obtain ⟨a, ha, h1⟩ := hp
  obtain ⟨b, hb, h2⟩ := hq
  rw [ha] at hb; cases hb
  exact ⟨a, ha, h1, h2⟩

theorem AllocP.mono {s : MM02.State} {i : Nat} {p q : MM02.Alloc → Prop} (h : AllocP s i p)
    (hpq : ∀ a, p a → q a) : AllocP s i q :=
  let ⟨a, ha, hpa⟩ := h; ⟨a, ha, hpq a hpa⟩

theorem AllocP.lt {s : MM02.State} (hwf : MM02.WF s) {i : Nat} {p : MM02.Alloc → Prop}
    (h : AllocP s i p) : i < s.next :=
  Nat.lt_of_not_le fun hle => by obtain ⟨a, ha, -⟩ := h; rw [hwf i hle] at ha; cases ha

/-! ## Transport of `Repr` -/

theorem OptP.imp {α : Type} {o : Option α} {P Q : α → Prop} {d d' : Prop} (h : OptP o P d)
    (hPQ : ∀ y, P y → Q y) (hd : d → d') : OptP o Q d' := by
  cases o with
  | some y => exact hPQ y h
  | none => exact hd h

/-- `Repr` carries over when the MM-02 state only keeps its allocations (`Dom`) and the MM-03 state
keeps its places, stack, `dead` and `freed` marks, every leaf that becomes `Init` having its range
initialised (K3). -/
theorem Repr.change {tok : Nat → Nat} {L : Layout} {s3 s3' : S3} {s2 s2' : MM02.State}
    (hR : Repr tok L s3 s2) (hd : Dom s2 s2') (hP : s3'.P = s3.P) (hF : s3'.F = s3.F)
    (hdead : s3'.dead = s3.dead) (hfr : s3'.freed = s3.freed)
    (hI : ∀ l < s3.P.length, isLeaf s3.P l → s3'.I l = .init →
      s3.I l = .init ∨ AllocP s2' (L l).alloc fun a => a.InitRange (L l).off (L l).len) :
    Repr tok L s3' s2' := by
  have hU : ∀ q, s3'.Usable q ↔ s3.Usable q := fun q => S3.Usable.congr hP hF hdead
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [hP, hF, hfr, hU]
  · exact hR.lwf.sameAlloc
  · exact hR.lwf.disjoint
  · exact fun l hl hlf => (hR.lwf.within l hl hlf).of_dom hd fun a a' _ e _ _ _ h => e ▸ h
  · exact hR.inj
  · exact fun r hr hrt => OptP.imp (hR.tokens r hr hrt) (fun _ h => OptP.imp h (fun _ h l hl =>
      (h l hl).of_dom hd fun _ _ _ _ _ e _ h => e ▸ h) id) id
  · exact fun r hr hrt hu l hl => (hR.live r hr hrt hu l hl).of_dom hd fun a a' _ _ e _ _ h => e ▸ h
  · intro l hl hlf hi
    rcases hI l hl hlf hi with h | h
    · exact (hR.init l hl hlf h).of_dom hd fun a a' _ _ _ _ hb h i hi => hb _ (h i hi)
    · exact h
  · exact fun r hr hrt hf l hl => (hR.freed r hr hrt hf l hl).of_dom hd fun a a' _ _ e _ _ h => e ▸ h
  · exact fun r hr hrt hg l hl => (hR.exited r hr hrt hg l hl).of_dom hd
      fun a a' _ _ e _ _ h => e ▸ h
  · exact fun r hr hrt hu hf ho l hl => (hR.leaked r hr hrt hu hf ho l hl).of_dom hd
      fun a a' _ _ e _ _ h => e ▸ h

/-! ## Writes (K4: `write3`, `writeShared`; K3: `S3.init`) -/

theorem leafAcc_of {s2 : MM02.State} {L : Layout} {au : MM02.Auth} {l : Nat} {a : MM02.Alloc}
    (h : s2.allocs (L l).alloc = some a) :
    leafAcc s2 L au l = ⟨a.base + (L l).off, (L l).alloc, (L l).len, au⟩ := by
  simp [leafAcc, h]

theorem leafAcc_dom {s2 s2' : MM02.State} (hd : Dom s2 s2') {L : Layout} {au : MM02.Auth} {l : Nat}
    (h : AllocP s2 (L l).alloc fun _ => True) : leafAcc s2' L au l = leafAcc s2 L au l := by
  obtain ⟨a, ha, -⟩ := h
  obtain ⟨a', ha', -, e, -⟩ := hd _ a ha
  rw [leafAcc_of ha, leafAcc_of ha', e]

/-- K4, MM-02.C: the write of the range of a leaf whose allocation is live and contains the range
has the outcome `ok`, under `dec` (K5) and the static part `stat` (K5: concurrency, true in the
sequential fragment). -/
theorem write_leaf_ok {ObW : MM02.WriteOblSpec} {s2 : MM02.State} {L : Layout} {l : Nat}
    {w : Nat → UInt8 × Option Nat} (hstat : ∀ s ac w, ObW.stat s ac w)
    (h : AllocP s2 (L l).alloc fun a => a.live = true ∧ (L l).off + (L l).len ≤ a.size)
    (hdec : ObW.dec s2 (leafAcc s2 L .write l) w) :
    MM02.WriteStep ObW (leafAcc s2 L .write l) w s2 (.ok (s2.write (leafAcc s2 L .write l) w)) := by
  obtain ⟨a, ha, hl, hs⟩ := h
  refine .ok ⟨⟨a, ?_, hl, ?_, .inr rfl⟩, hdec, hstat _ _ _⟩
  · rw [leafAcc_of ha]; exact ha
  · rw [leafAcc_of ha]; exact ⟨Nat.le_add_right _ _, by simp only; omega⟩

/-- MM-02.C: after the write of the range of a leaf, the range is initialised. -/
theorem write_leaf_init {s2 : MM02.State} {L : Layout} {l : Nat} {w : Nat → UInt8 × Option Nat}
    (h : AllocP s2 (L l).alloc fun _ => True) :
    AllocP (s2.write (leafAcc s2 L .write l) w) (L l).alloc
      fun a => a.InitRange (L l).off (L l).len := by
  obtain ⟨a, ha, -⟩ := h
  refine ⟨a.write (L l).off (L l).len w, ?_, fun i hi => ?_⟩
  · rw [write_allocs, leafAcc_of ha]
    simp only [↓reduceIte, ha, Option.map_some, Nat.add_sub_cancel_left]
  · have hr : (L l).off ≤ (L l).off + i ∧ (L l).off + i < (L l).off + (L l).len :=
      ⟨Nat.le_add_right _ _, by omega⟩
    simp only [MM02.Alloc.write, hr, and_self, ↓reduceIte]; exact fun h => by cases h

theorem write3Eff_cons (s : S3) (l : Nat) (ls : List Nat) :
    write3Eff (write3Eff s [l]) ls = write3Eff s (l :: ls) := by
  simp only [write3Eff]; congr 1; funext p
  by_cases h1 : p ∈ ls <;> by_cases h2 : p = l <;> simp [h1, h2]

/-- K4, R2 core: the writes of the ranges of leaves whose allocations are live have the outcome
`ok`, and the states where those leaves are `Init` stay in `Repr`, under `dec` along the
sequence and `stat` (K5). -/
theorem repr_writes {C : Nat → Nat → Prop} {ObR : MM02.ReadOblSpec} {ObW : MM02.WriteOblSpec}
    {tok : Nat → Nat} {L : Layout} {w : Nat → Nat → UInt8 × Option Nat}
    (hstat : ∀ s ac w, ObW.stat s ac w) :
    ∀ (ls : List Nat) (s3 : S3) (s2 : MM02.State), Repr tok L s3 s2 →
      (∀ l ∈ ls, l < s3.P.length ∧ isLeaf s3.P l ∧ LiveAlloc s2 (L l).alloc) →
      DecAlong ObR ObW s2 (writeOps s2 L w ls) →
      AllOk C ObR ObW s2 (writeOps s2 L w ls) ∧
        Repr tok L (write3Eff s3 ls) (exec s2 (writeOps s2 L w ls))
  | [], s3, s2, hR, _, _ => by
    refine ⟨trivial, hR.change (Dom.refl _) rfl rfl rfl rfl fun l _ _ h => .inl ?_⟩
    simpa [write3Eff] using h
  | l :: ls, s3, s2, hR, hls, hdec => by
    obtain ⟨hl, hlf, hlive⟩ := hls l (List.mem_cons_self ..)
    have hw := (hR.lwf.within l hl hlf)
    have hex : AllocP s2 (L l).alloc fun _ => True := hw.mono fun _ _ => trivial
    obtain ⟨s2₁, hs2₁⟩ : ∃ x, x = s2.write (leafAcc s2 L .write l) (w l) := ⟨_, rfl⟩
    have hd₁ : Dom s2 s2₁ := hs2₁ ▸ Dom.write _ _ _
    have hR₁ : Repr tok L (write3Eff s3 [l]) s2₁ := by
      refine hR.change hd₁ rfl rfl rfl rfl fun l' _ _ h => ?_
      simp only [write3Eff, List.mem_singleton] at h
      split at h
      · rename_i e; subst e; exact .inr (hs2₁ ▸ write_leaf_init hex)
      · exact .inl h
    have hops : writeOps s2₁ L w ls = writeOps s2 L w ls := by
      simp only [writeOps, List.map_inj_left]
      intro l' hl'
      obtain ⟨hl'P, hl'f, -⟩ := hls l' (List.mem_cons_of_mem _ hl')
      rw [leafAcc_dom hd₁ ((hR.lwf.within l' hl'P hl'f).mono fun _ _ => trivial)]
    have e : writeOps s2 L w (l :: ls) = .write (leafAcc s2 L .write l) (w l) :: writeOps s2 L w ls :=
      rfl
    rw [e] at hdec ⊢
    have e₁ : Op2.eff (.write (leafAcc s2 L .write l) (w l)) s2 = s2₁ := hs2₁.symm
    have hdec' : DecAlong ObR ObW s2₁ (writeOps s2₁ L w ls) := by rw [hops, ← e₁]; exact hdec.2
    have := repr_writes (C := C) hstat ls (write3Eff s3 [l]) s2₁ hR₁ (fun l' hl' => by
      obtain ⟨h1, h2, h3⟩ := hls l' (List.mem_cons_of_mem _ hl')
      exact ⟨h1, h2, h3.of_dom hd₁ fun _ _ _ _ e _ _ h => e ▸ h⟩) hdec'
    rw [hops, write3Eff_cons] at this
    refine ⟨⟨write_leaf_ok hstat (hlive.and hw) hdec.1, ?_⟩, ?_⟩
    · show AllOk C ObR ObW (Op2.eff _ s2) _; rw [e₁]; exact this.1
    · show Repr tok L _ (exec (Op2.eff _ s2) _); rw [e₁]; exact this.2

/-! ## Allocations (K2, K4: `enterFrame`, `alloc`, static storage) -/

section AllocOps
variable (pl : Placement) (g : Nat → Geom) (fa : Option Nat)

theorem allocOps_next : ∀ (roots : List Nat) (s : MM02.State),
    (exec s (allocOps pl g fa s roots)).next = s.next + roots.length
  | [], _ => rfl
  | _ :: is, s => by
    show (exec (s.alloc _ _ _ _ fa) (allocOps pl g fa _ is)).next = _
    rw [allocOps_next is]; simp only [MM02.State.alloc, List.length_cons]; omega

theorem allocOps_old : ∀ (roots : List Nat) (s : MM02.State) (i : Nat), i < s.next →
    (exec s (allocOps pl g fa s roots)).allocs i = s.allocs i
  | [], _, _, _ => rfl
  | _ :: is, s, i, hi => by
    show (exec (s.alloc _ _ _ _ fa) (allocOps pl g fa _ is)).allocs i = _
    rw [allocOps_old is _ i (by simp only [MM02.State.alloc]; omega)]
    simp [MM02.State.alloc, Nat.ne_of_lt hi]

theorem allocOps_new : ∀ (roots : List Nat) (s : MM02.State) (j i : Nat), roots[j]? = some i →
    ∃ b, (exec s (allocOps pl g fa s roots)).allocs (s.next + j) =
      some ⟨(g i).space, b, (g i).size, (g i).align, true, fun _ => .uninit, fa⟩
  | [], _, _, _, h => by simp at h
  | k :: is, s, 0, i, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h
    refine ⟨pl s (g k), ?_⟩
    show (exec (s.alloc _ _ _ _ fa) (allocOps pl g fa _ is)).allocs _ = _
    rw [allocOps_old pl g fa is _ _ (by simp [MM02.State.alloc])]
    simp [MM02.State.alloc]
  | k :: is, s, j + 1, i, h => by
    simp only [List.getElem?_cons_succ] at h
    obtain ⟨b, hb⟩ := allocOps_new is (s.alloc (g k).space (pl s (g k)) (g k).size (g k).align fa)
      j i h
    refine ⟨b, ?_⟩
    show (exec (s.alloc _ _ _ _ fa) (allocOps pl g fa _ is)).allocs _ = _
    rw [show s.next + (j + 1) = (s.alloc (g k).space (pl s (g k)) (g k).size (g k).align fa).next + j
      by simp only [MM02.State.alloc]; omega]
    exact hb

theorem allocOps_wf : ∀ (roots : List Nat) (s : MM02.State), MM02.WF s →
    MM02.WF (exec s (allocOps pl g fa s roots))
  | [], _, h => h
  | _ :: is, _, h => allocOps_wf is _ (MM02.alloc_wf h _ _ _ _ _)

/-- K2, K4: the allocations of the roots have the outcome `ok` (MM-02.2, création brute) under the
obligation of the placement and valid alignments. -/
theorem allocOps_ok {C : Nat → Nat → Prop} {ObR : MM02.ReadOblSpec} {ObW : MM02.WriteOblSpec}
    {pl : Placement} {g : Nat → Geom} {fa : Option Nat} (hpl : PlacementOK pl) :
    ∀ (roots : List Nat) (s : MM02.State), MM02.WF s →
      (∀ i ∈ roots, 0 < (g i).align ∧ MM02.Pow2 (g i).align) →
      AllOk C ObR ObW s (allocOps pl g fa s roots)
  | [], _, _, _ => trivial
  | i :: is, s, h, hg => by
    obtain ⟨h0, h2⟩ := hg i (List.mem_cons_self ..)
    exact ⟨.ok (hpl s (g i) h h0 h2),
      allocOps_ok hpl is _ (MM02.alloc_wf h _ _ _ _ _) fun i hi => hg i (List.mem_cons_of_mem _ hi)⟩

end AllocOps

theorem AllocP.of_eq {s s' : MM02.State} {i : Nat} {p : MM02.Alloc → Prop} (h : AllocP s i p)
    (he : s'.allocs i = s.allocs i) : AllocP s' i p :=
  let ⟨a, ha, hpa⟩ := h; ⟨a, he.trans ha, hpa⟩

/-! ## Shapes appended to the places (C6 of MM-03) -/

section Shape
variable {P : List Place} {hd : Holder} {ls : List (Option Nat × Option Nat × Nat)}

theorem shape_isLeaf_old (hsh : ShapeOK P.length ls) {l : Nat} (hl : l < P.length) :
    isLeaf (shapeP P hd ls) l ↔ isLeaf P l := by
  constructor
  · intro h r hr; rw [← shape_parentOf_lt hr]; exact h r (by rw [shapeP_len]; omega)
  · intro h r hr e
    by_cases hrn : r < P.length
    · rw [shape_parentOf_lt hrn] at e; exact h r hrn e
    · rw [shapeP_len] at hr
      have hi : r - P.length < ls.length := by omega
      have hp := shape_parentOf_new (P := P) (hd := hd) hi
      rw [show P.length + (r - P.length) = r by omega, e] at hp
      have := (hsh (r - P.length) (List.mem_range.2 hi)).1
      rw [← hp] at this; simp only [OptP] at this; omega

theorem shape_rootPlace_old {r : Nat} (hr : r < P.length) :
    RootPlace (shapeP P hd ls) r ↔ RootPlace P r := by
  simp only [RootPlace, shape_parentOf_lt hr, shapeP_len]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by omega, h2⟩

theorem shape_rootPlace_new {r : Nat} (h : RootPlace (shapeP P hd ls) r) (hr : P.length ≤ r) :
    ∃ i, r = P.length + i ∧ i ∈ rootIdx ls := by
  obtain ⟨hlt, hn⟩ := h
  rw [shapeP_len] at hlt
  have hi : r - P.length < ls.length := by omega
  have hp := shape_parentOf_new (P := P) (hd := hd) hi
  rw [show P.length + (r - P.length) = r by omega, hn] at hp
  exact ⟨r - P.length, by omega, mem_rootIdx hi hp.symm⟩

/-- Every new place is a part of a new root place (MM-03.3.2; C6). -/
theorem shape_part_root (hsh : ShapeOK P.length ls) : ∀ m l, l < m → P.length ≤ l →
    l < (shapeP P hd ls).length → ∃ i ∈ rootIdx ls, partOf (shapeP P hd ls) l (P.length + i)
  | 0, _, h, _, _ => absurd h (Nat.not_lt_zero _)
  | m + 1, l, hlm, hge, hl => by
    rw [shapeP_len] at hl
    have hi : l - P.length < ls.length := by omega
    have hp := shape_parentOf_new (P := P) (hd := hd) hi
    rw [show P.length + (l - P.length) = l by omega] at hp
    cases hb : (ls[l - P.length]?).bind (·.1) with
    | none =>
      refine ⟨l - P.length, mem_rootIdx hi hb, by rw [shapeP_len]; omega, .inl (by omega)⟩
    | some p =>
      have h1 := (hsh (l - P.length) (List.mem_range.2 hi)).1
      rw [hb] at h1; simp only [OptP] at h1
      rw [hb] at hp
      obtain ⟨i, hi', hpi⟩ := shape_part_root hsh m p (by omega) (by omega) (by rw [shapeP_len]; omega)
      refine ⟨i, hi', by rw [shapeP_len]; omega, .inr ?_⟩
      rw [chain_cons hp (by omega)]
      rcases hpi.2 with e | e
      · rw [e]; exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ e

end Shape

/-- K1, K2: layout of the new roots `roots` of the places `P'` appended after `n` old places, in
fresh allocations: the leaves of the `j`-th new root `n + i` are in the allocation `next + j`,
within the size of `g i`; two distinct new leaves of one allocation have disjoint ranges. -/
structure NewLayout (L : Layout) (P' : List Place) (n next : Nat) (g : Nat → Geom)
    (roots : List Nat) : Prop where
  place : ∀ j < roots.length, OptP (roots[j]?) (fun i => ∀ l ∈ footprint P' (n + i),
    (L l).alloc = next + j ∧ (L l).off + (L l).len ≤ (g i).size) True
  disjoint : ∀ l < P'.length, ∀ l' < P'.length, n ≤ l → n ≤ l' → isLeaf P' l → isLeaf P' l' →
    l ≠ l' → (L l).alloc = (L l').alloc →
    MM02.RangeDisjoint (L l).off (L l).len (L l').off (L l').len

set_option synthInstance.maxSize 4096 in
instance (L : Layout) (P' : List Place) (n next : Nat) (g : Nat → Geom) (roots : List Nat) :
    Decidable (NewLayout L P' n next g roots) :=
  decidable_of_iff
    ((∀ j < roots.length, OptP (roots[j]?) (fun i => ∀ l ∈ footprint P' (n + i),
      (L l).alloc = next + j ∧ (L l).off + (L l).len ≤ (g i).size) True) ∧
     (∀ l < P'.length, ∀ l' < P'.length, n ≤ l → n ≤ l' → isLeaf P' l → isLeaf P' l' →
      l ≠ l' → (L l).alloc = (L l').alloc →
      MM02.RangeDisjoint (L l).off (L l).len (L l').off (L l').len))
    ⟨fun ⟨a, b⟩ => ⟨a, b⟩, fun ⟨a, b⟩ => ⟨a, b⟩⟩

theorem NewLayout.at {L : Layout} {P' : List Place} {n next : Nat} {g : Nat → Geom}
    {roots : List Nat} (h : NewLayout L P' n next g roots) {j i : Nat} (hj : roots[j]? = some i)
    {l : Nat} (hl : l ∈ footprint P' (n + i)) :
    (L l).alloc = next + j ∧ (L l).off + (L l).len ≤ (g i).size := by
  have := h.place j (lt_of_getElem? hj); rw [hj] at this; exact this l hl

/-- A usable place is not owned by a frame popped from the stack (MM-03.3.2). -/
theorem not_frameGone_of_usable {s : S3} {q : Nat} {pl : Place} (hu : s.Usable q)
    (hpl : s.P[q]? = some pl) : ¬ FrameGone s.F pl.owner := by
  have := hu.owner_live hpl
  cases ho : pl.owner with
  | frame f => rw [ho] at this; exact fun h => h this
  | place _ => exact fun h => False.elim h

/-- K2, K3: `Repr` carries over when new places, a shape appended after the old ones, receive one
fresh allocation per new root (`allocOps`), laid out by `NewLayout`: the old places keep their
usability, `freed` marks and frame; the new places are usable and not freed; no leaf becomes
`Init`; a new root owned by the frame `f` has the token `tok f`. -/
theorem repr_extend {tok : Nat → Nat} {L : Layout} {s3 s3' : S3} {s2 : MM02.State} {hd : Holder}
    {ls : List (Option Nat × Option Nat × Nat)} {pl : Placement} {g : Nat → Geom}
    {fa : Option Nat} (hR : Repr tok L s3 s2) (hwf : MM02.WF s2)
    (hP : s3'.P = shapeP s3.P hd ls) (hsh : ShapeOK s3.P.length ls)
    (hUold : ∀ q < s3.P.length, s3'.Usable q → s3.Usable q)
    (hUold' : ∀ q < s3.P.length, s3.Usable q → s3'.Usable q)
    (hUnew : ∀ i < ls.length, s3'.Usable (s3.P.length + i))
    (hfr : ∀ q, s3'.freed q = if s3.P.length ≤ q then false else s3.freed q)
    (hI : ∀ l, s3'.I l = .init → l < s3.P.length ∧ s3.I l = .init)
    (hgone : ∀ q < s3.P.length, ∀ pl : Place, s3.P[q]? = some pl → FrameGone s3'.F pl.owner →
      FrameGone s3.F pl.owner)
    (htok : ∀ f, hd = .frame f → fa = some (tok f))
    (hNL : NewLayout L s3'.P s3.P.length s2.next g (rootIdx ls)) :
    Repr tok L s3' (exec s2 (allocOps pl g fa s2 (rootIdx ls))) := by
  -- notations
  have hlen : s3'.P.length = s3.P.length + ls.length := by rw [hP, shapeP_len]
  have hold := allocOps_old pl g fa (rootIdx ls) s2
  have hnew := allocOps_new pl g fa (rootIdx ls) s2
  have hget : ∀ q < s3.P.length, s3'.P[q]? = s3.P[q]? := fun q hq => by rw [hP, shapeP_lt hq]
  have hleaf : ∀ l < s3.P.length, isLeaf s3'.P l ↔ isLeaf s3.P l := fun l hl => by
    rw [hP]; exact shape_isLeaf_old hsh hl
  have hroot : ∀ r < s3.P.length, RootPlace s3'.P r ↔ RootPlace s3.P r := fun r hr => by
    rw [hP]; exact shape_rootPlace_old hr
  have hfp : ∀ r < s3.P.length, ∀ l, l ∈ footprint s3'.P r ↔ l ∈ footprint s3.P r :=
    fun r hr l => by rw [hP]; exact shape_footprint_old hsh hr l
  have hfpge : ∀ i l, l ∈ footprint s3'.P (s3.P.length + i) → s3.P.length ≤ l := fun i l h => by
    rw [hP] at h; exact shape_root_fp_ge h
  -- an old leaf is in an allocation of `s2`
  have hlt : ∀ l < s3.P.length, isLeaf s3.P l → (L l).alloc < s2.next := fun l hl hlf =>
    (hR.lwf.within l hl hlf).lt hwf
  -- a new root place is the `j`-th root of the shape
  have hnr : ∀ r < s3'.P.length, RootPlace s3'.P r → ¬ r < s3.P.length →
      ∃ j i, (rootIdx ls)[j]? = some i ∧ r = s3.P.length + i := fun r _ hr hn => by
    rw [hP] at hr
    obtain ⟨i, e, hi⟩ := shape_rootPlace_new hr (by omega)
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hi
    exact ⟨j, i, hj, e⟩
  -- a new leaf is in the footprint of a new root
  have hnl : ∀ l < s3'.P.length, isLeaf s3'.P l → ¬ l < s3.P.length →
      ∃ j i, (rootIdx ls)[j]? = some i ∧ l ∈ footprint s3'.P (s3.P.length + i) :=
    fun l hl hlf hn => by
      obtain ⟨i, hi, hpart⟩ := shape_part_root (P := s3.P) (hd := hd) hsh (l + 1) l
        (Nat.lt_succ_self l) (by omega) (by rw [← hP]; exact hl)
      obtain ⟨j, hj⟩ := List.getElem?_of_mem hi
      exact ⟨j, i, hj, mem_footprint.2 ⟨hl, hlf, by rw [hP]; exact hpart⟩⟩
  -- the allocation of a leaf of a new root
  have hna : ∀ j i, (rootIdx ls)[j]? = some i → ∀ l ∈ footprint s3'.P (s3.P.length + i),
      (L l).alloc = s2.next + j ∧ (L l).off + (L l).len ≤ (g i).size ∧
      ∃ b, (exec s2 (allocOps pl g fa s2 (rootIdx ls))).allocs (L l).alloc =
        some ⟨(g i).space, b, (g i).size, (g i).align, true, fun _ => .uninit, fa⟩ :=
    fun j i hj l hl => by
      obtain ⟨e, hs⟩ := hNL.at hj hl
      obtain ⟨b, hb⟩ := hnew j i hj
      exact ⟨e, hs, b, by rw [e]; exact hb⟩
  -- the new places are not old
  have hroot_lt : ∀ j i, (rootIdx ls)[j]? = some i → i < ls.length := fun j i hj =>
    (rootIdx_mem hj).1
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- K1 (a)
    intro r hr hrt l hl l' hl'
    by_cases hro : r < s3.P.length
    · exact hR.lwf.sameAlloc r hro ((hroot r hro).1 hrt) l ((hfp r hro l).1 hl) l'
        ((hfp r hro l').1 hl')
    · obtain ⟨j, i, hj, rfl⟩ := hnr r hr hrt hro
      rw [(hna j i hj l hl).1, (hna j i hj l' hl').1]
  · -- K1 (b)
    intro l hl l' hl' hlf hlf' hne he
    by_cases ho : l < s3.P.length <;> by_cases ho' : l' < s3.P.length
    · exact hR.lwf.disjoint l ho l' ho' ((hleaf l ho).1 hlf) ((hleaf l' ho').1 hlf') hne he
    · obtain ⟨j, i, hj, hm⟩ := hnl l' hl' hlf' ho'
      have := hlt l ho ((hleaf l ho).1 hlf); rw [he, (hna j i hj l' hm).1] at this; omega
    · obtain ⟨j, i, hj, hm⟩ := hnl l hl hlf ho
      have := hlt l' ho' ((hleaf l' ho').1 hlf'); rw [← he, (hna j i hj l hm).1] at this; omega
    · exact hNL.disjoint l hl l' hl' (by omega) (by omega) hlf hlf' hne he
  · -- K1 (c)
    intro l hl hlf
    by_cases ho : l < s3.P.length
    · have h := hR.lwf.within l ho ((hleaf l ho).1 hlf)
      exact h.of_eq (hold _ (h.lt hwf))
    · obtain ⟨j, i, hj, hm⟩ := hnl l hl hlf ho
      obtain ⟨-, hs, b, hb⟩ := hna j i hj l hm
      exact ⟨_, hb, hs⟩
  · -- K2: injectivity
    intro r hr r' hr' hrt hrt' hne l hl l' hl'
    by_cases ho : r < s3.P.length <;> by_cases ho' : r' < s3.P.length
    · exact hR.inj r ho r' ho' ((hroot r ho).1 hrt) ((hroot r' ho').1 hrt') hne l
        ((hfp r ho l).1 hl) l' ((hfp r' ho' l').1 hl')
    · obtain ⟨j, i, hj, rfl⟩ := hnr r' hr' hrt' ho'
      have hlf := (mem_footprint.1 ((hfp r ho l).1 hl)).2.1
      have := hlt l (mem_footprint.1 ((hfp r ho l).1 hl)).1 hlf
      rw [(hna j i hj l' hl').1]; omega
    · obtain ⟨j, i, hj, rfl⟩ := hnr r hr hrt ho
      have hlf := (mem_footprint.1 ((hfp r' ho' l').1 hl')).2.1
      have := hlt l' (mem_footprint.1 ((hfp r' ho' l').1 hl')).1 hlf
      rw [(hna j i hj l hl).1]; omega
    · obtain ⟨j, i, hj, rfl⟩ := hnr r hr hrt ho
      obtain ⟨j', i', hj', rfl⟩ := hnr r' hr' hrt' ho'
      rw [(hna j i hj l hl).1, (hna j' i' hj' l' hl').1]
      intro e
      have : j = j' := by omega
      subst this; rw [hj] at hj'; cases hj'; exact hne rfl
  · -- K2: tokens
    intro r hr hrt
    by_cases ho : r < s3.P.length
    · rw [hget r ho]
      exact OptP.imp (hR.tokens r ho ((hroot r ho).1 hrt)) (fun _ h => OptP.imp h
        (fun _ h l hl => by
          have h1 := h l ((hfp r ho l).1 hl)
          exact h1.of_eq (hold _ (h1.lt hwf))) id) id
    · obtain ⟨j, i, hj, rfl⟩ := hnr r hr hrt ho
      rw [hP, shapeP_new (hroot_lt j i hj)]
      show OptP (tokOf tok (shapeOwner ls hd i)) _ True
      cases hso : shapeOwner ls hd i with
      | place _ => trivial
      | frame f =>
        have hhd : hd = .frame f := by
          unfold shapeOwner at hso; split at hso
          · cases hso
          · exact hso
        intro l hl
        obtain ⟨-, -, b, hb⟩ := hna j i hj l (by rw [hP]; exact hl)
        exact ⟨_, hb, htok f hhd⟩
  · -- K3: usable roots
    intro r hr hrt hu l hl
    by_cases ho : r < s3.P.length
    · have h := hR.live r ho ((hroot r ho).1 hrt) (hUold r ho hu) l ((hfp r ho l).1 hl)
      exact h.of_eq (hold _ (h.lt hwf))
    · obtain ⟨j, i, hj, rfl⟩ := hnr r hr hrt ho
      obtain ⟨-, -, b, hb⟩ := hna j i hj l hl
      exact ⟨_, hb, rfl⟩
  · -- K3: `Init` leaves
    intro l hl hlf hi
    obtain ⟨ho, hi'⟩ := hI l hi
    have h := hR.init l ho ((hleaf l ho).1 hlf) hi'
    exact h.of_eq (hold _ (h.lt hwf))
  · -- K3: freed roots
    intro r hr hrt hf l hl
    rw [hfr] at hf
    by_cases ho : r < s3.P.length
    · simp only [show ¬ s3.P.length ≤ r by omega, ↓reduceIte] at hf
      have h := hR.freed r ho ((hroot r ho).1 hrt) hf l ((hfp r ho l).1 hl)
      exact h.of_eq (hold _ (h.lt hwf))
    · simp only [show s3.P.length ≤ r by omega, ↓reduceIte] at hf; cases hf
  · -- K3: roots of an exited frame
    intro r hr hrt hg l hl
    by_cases ho : r < s3.P.length
    · rw [hget r ho] at hg
      have hg' : OptP (s3.P[r]?) (fun pl => FrameGone s3.F pl.owner) False := by
        cases hpl : s3.P[r]? with
        | none => rw [hpl] at hg; exact hg
        | some pl => rw [hpl] at hg; exact hgone r ho pl hpl hg
      have h := hR.exited r ho ((hroot r ho).1 hrt) hg' l ((hfp r ho l).1 hl)
      exact h.of_eq (hold _ (h.lt hwf))
    · obtain ⟨j, i, hj, rfl⟩ := hnr r hr hrt ho
      have hu := hUnew i (hroot_lt j i hj)
      cases hpl : s3'.P[s3.P.length + i]? with
      | none => rw [hpl] at hg; exact hg.elim
      | some pl => rw [hpl] at hg; exact absurd hg (not_frameGone_of_usable hu hpl)
  · -- K3: leaked roots
    intro r hr hrt hu hf ho' l hl
    by_cases ho : r < s3.P.length
    · simp only [hfr, show ¬ s3.P.length ≤ r by omega, ↓reduceIte] at hf
      rw [hget r ho] at ho'
      have h := hR.leaked r ho ((hroot r ho).1 hrt) (fun h => hu (hUold' r ho h)) hf ho' l
        ((hfp r ho l).1 hl)
      exact h.of_eq (hold _ (h.lt hwf))
    · obtain ⟨j, i, hj, rfl⟩ := hnr r hr hrt ho
      exact absurd (hUnew i (hroot_lt j i hj)) hu

/-! ## Initial state (K3) -/

/-- `Repr` holds trivially for a state without places. -/
theorem repr_of_nil {tok : Nat → Nat} {L : Layout} {s3 : S3} {s2 : MM02.State}
    (h : s3.P.length = 0) : Repr tok L s3 s2 :=
  ⟨⟨fun _ hr => absurd hr (by omega), fun _ hr => absurd hr (by omega),
    fun _ hr => absurd hr (by omega)⟩, fun _ hr => absurd hr (by omega),
    fun _ hr => absurd hr (by omega), fun _ hr => absurd hr (by omega),
    fun _ hr => absurd hr (by omega), fun _ hr => absurd hr (by omega),
    fun _ hr => absurd hr (by omega), fun _ hr => absurd hr (by omega)⟩

/-- K3 (initial state): the leaves of the static storage declared `Init` (MM-03.3.9; D1). -/
def initLeaves (statics : Statics) : List Nat :=
  (List.range statics.length).filter fun l =>
    ((statics[l]?).map (·.2)).getD false && decide (isLeaf (S3.init statics).P l)

/-- K3 (initial state): the MM-02 operations from `State.empty`: one allocation per static root
(`AllocStep`), of geometry `g i`, at the placement `pl`, with the token of the base frame 0 (K2);
then one write per leaf declared `Init` (`WriteStep`), of the bytes `w l`. -/
def initOps (pl : Placement) (g : Nat → Geom) (tok : Nat → Nat) (L : Layout)
    (w : Nat → Nat → UInt8 × Option Nat) (statics : Statics) : List Op2 :=
  allocOps pl g (some (tok 0)) MM02.State.empty (rootIdx (statics.map (·.1))) ++
  writeOps (exec MM02.State.empty
    (allocOps pl g (some (tok 0)) MM02.State.empty (rootIdx (statics.map (·.1))))) L w
    (initLeaves statics)

/-- `repr_init` (K3): the initial state `S3.init statics` is in `Repr` with the MM-02 state obtained
from `State.empty` by the allocations of the static roots, then the writes of the leaves declared
`Init`; every operation of that sequence has the outcome `ok`. Hypotheses: a well-formed static
storage (`ShapeOK`); the obligation of the placement (K2); valid alignments; a layout of the
statics in the fresh allocations (`NewLayout`, K1); `dec` along the sequence and `stat` (K5). -/
theorem repr_init {C : Nat → Nat → Prop} {ObR : MM02.ReadOblSpec} {ObW : MM02.WriteOblSpec}
    {statics : Statics} (hsh : ShapeOK 0 (statics.map (·.1))) {pl : Placement}
    (hpl : PlacementOK pl) {g : Nat → Geom}
    (hg : ∀ i ∈ rootIdx (statics.map (·.1)), 0 < (g i).align ∧ MM02.Pow2 (g i).align)
    {tok : Nat → Nat} {L : Layout}
    (hNL : NewLayout L (S3.init statics).P 0 0 g (rootIdx (statics.map (·.1))))
    {w : Nat → Nat → UInt8 × Option Nat} (hstat : ∀ s ac w, ObW.stat s ac w)
    (hdec : DecAlong ObR ObW MM02.State.empty (initOps pl g tok L w statics)) :
    AllOk C ObR ObW MM02.State.empty (initOps pl g tok L w statics) ∧
      Repr tok L (S3.init statics) (exec MM02.State.empty (initOps pl g tok L w statics)) := by
  -- the statics with every leaf `Uninit`
  let st0 : Statics := statics.map fun e => (e.1, false)
  have hmap : st0.map (·.1) = statics.map (·.1) := by simp [st0, List.map_map, Function.comp_def]
  have hP0 : (S3.init st0).P = (S3.init statics).P := by simp only [S3.init, hmap]
  have hsh0 : ShapeOK 0 (st0.map (·.1)) := hmap ▸ hsh
  have hnil : (S3.init ([] : Statics)).P.length = 0 := rfl
  -- allocations
  have hR1 : Repr tok L (S3.init st0)
      (exec MM02.State.empty (allocOps pl g (some (tok 0)) MM02.State.empty
        (rootIdx (statics.map (·.1))))) := by
    refine repr_extend (s3 := S3.init []) (hd := .frame 0) (repr_of_nil hnil)
      (fun _ _ => rfl) ?_ (by rw [hnil]; exact hsh) (fun q hq => absurd hq (by omega))
      (fun q hq => absurd hq (by omega)) ?_ ?_ ?_ (fun q hq => absurd hq (by omega)) ?_ ?_
    · rw [hP0]; rfl
    · intro i hi
      rw [hnil, Nat.zero_add]
      exact init_usable hsh0 (i + 1) i (Nat.lt_succ_self i) (by simpa [st0] using hi)
    · intro q; simp [S3.init]
    · intro l hl
      have : ((st0[l]?).map (·.2)).getD false = false := by
        simp only [st0, List.getElem?_map]; cases statics[l]? <;> rfl
      simp [S3.init, this] at hl
    · intro f e; cases e; rfl
    · rw [hP0, hnil]; exact hNL
  have hok1 : AllOk C ObR ObW MM02.State.empty
      (allocOps pl g (some (tok 0)) MM02.State.empty (rootIdx (statics.map (·.1)))) :=
    allocOps_ok hpl _ _ (fun _ _ => rfl) hg
  -- writes
  have hdec2 := (along_append.1 hdec).2
  have hw := repr_writes (C := C) hstat (initLeaves statics) (S3.init st0) _ hR1 (fun l hl => by
      simp only [initLeaves, List.mem_filter, List.mem_range, Bool.and_eq_true,
        decide_eq_true_eq] at hl
      obtain ⟨hlt, -, hlf⟩ := hl
      have hlP : l < (S3.init st0).P.length := by rw [hP0, init_len]; exact hlt
      rw [← hP0] at hlf
      obtain ⟨r, hr, hlr⟩ := exists_rootPlace (init_wf st0 hsh0).1 (l + 1) l (Nat.lt_succ_self l) hlP
      have hrlt : r < st0.length := by have := hr.1; rwa [init_len] at this
      exact ⟨hlP, hlf, hR1.live r hr.1 hr (init_usable hsh0 (r + 1) r (Nat.lt_succ_self r) hrlt) l
        (mem_footprint.2 ⟨hlP, hlf, hlr⟩)⟩) hdec2
  refine ⟨along_append.2 ⟨hok1, hw.1⟩, ?_⟩
  rw [initOps, exec_append]
  refine hw.2.change (Dom.refl _) hP0.symm rfl rfl rfl fun l hl hlf hi => .inl ?_
  have hflag : ((statics[l]?).map (·.2)).getD false = true := by
    simp only [S3.init] at hi; split at hi
    · assumption
    · cases hi
  have hmem : l ∈ initLeaves statics := by
    simp only [initLeaves, List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨?_, hflag, ?_⟩
    · have := hl; simp only [write3Eff, hP0, init_len] at this; exact this
    · have := hlf; simp only [write3Eff, hP0] at this; exact this
  simp only [write3Eff, hmem, ↓reduceIte]

/-! ## Smoke test -/

namespace Smoke

def st : Statics := [((none, none, 0), true)]
def L : Layout := fun _ => ⟨0, 0, 4⟩
def tk : Nat → Nat := fun f => 100 + f
def g : Nat → Geom := fun _ => ⟨0, 4, 4⟩
def w : Nat → Nat → UInt8 × Option Nat := fun l i => ((l + i).toUInt8, none)
/-- Obligations of the test cases: `dec` asks an access aligned on 4 bytes (K5: a non-trivial
instance); `stat` is true, as K5 fixes for the sequential fragment. -/
def obR : MM02.ReadOblSpec := ⟨fun _ ac => ac.addr % 4 = 0, fun _ _ => True⟩
def obW : MM02.WriteOblSpec := ⟨fun _ ac _ => ac.addr % 4 = 0, fun _ _ _ => True⟩
instance : ∀ s o, Decidable (Op2.Dec obR obW s o) := fun s o => by
  cases o <;> simp only [Op2.Dec, obR, obW] <;> infer_instance
def s2 : MM02.State := exec MM02.State.empty (initOps topPlacement g tk L w st)

example : Repr tk L (S3.init st) s2 :=
  (repr_init (C := fun _ _ => False) (ObR := obR) (ObW := obW) (by decide) topPlacement_ok
    (by decide) (by decide) (fun _ _ _ => trivial) (by decide)).2
example : Repr tk L (S3.init st) s2 := by decide
example : ¬ Repr tk L (S3.init st)
    (exec MM02.State.empty (allocOps topPlacement g (some (tk 0)) MM02.State.empty [0])) := by
  decide

end Smoke

end Ern.MM23
